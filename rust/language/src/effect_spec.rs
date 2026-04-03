use crate::ast::{Choreography, EffectAuthorityClass};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GeneratedEffectBehavior {
    OneShot,
    Stream,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GeneratedSimulationMode {
    Deterministic,
    Adversarial,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneratedSimulationMetadata {
    pub behavior: GeneratedEffectBehavior,
    pub mode: GeneratedSimulationMode,
    pub latency_policy: String,
    pub timeout_policy: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneratedEffectOperation {
    pub interface_name: String,
    pub operation_name: String,
    pub rust_method_name: String,
    pub request_type_name: String,
    pub outcome_type_name: String,
    pub authority_class: EffectAuthorityClass,
    pub input_type: String,
    pub output_type: String,
    pub simulation: GeneratedSimulationMetadata,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneratedEffectFamily {
    pub interface_name: String,
    pub request_enum_name: String,
    pub outcome_enum_name: String,
    pub host_trait_name: String,
    pub simulator_trait_name: String,
    pub scenario_builder_name: String,
    pub operations: Vec<GeneratedEffectOperation>,
}

/// Derive canonical effect-interface families from a parsed choreography.
pub fn generated_effect_families(choreography: &Choreography) -> Vec<GeneratedEffectFamily> {
    choreography
        .effect_interface_declarations()
        .into_iter()
        .map(|effect| {
            let request_enum_name = format!("{}Request", effect.name);
            let outcome_enum_name = format!("{}Outcome", effect.name);
            let host_trait_name = format!("{}ExternalHandler", effect.name);
            let simulator_trait_name = format!("{}SimulatorHandler", effect.name);
            let scenario_builder_name = format!("{}ScenarioBuilder", effect.name);
            let operations = effect
                .operations
                .into_iter()
                .map(|op| {
                    let operation_type_name = to_upper_camel_case(&op.name);
                    GeneratedEffectOperation {
                        interface_name: effect.name.clone(),
                        operation_name: op.name.clone(),
                        rust_method_name: to_snake_case(&op.name),
                        request_type_name: format!("{}{}Request", effect.name, operation_type_name),
                        outcome_type_name: format!("{}{}Outcome", effect.name, operation_type_name),
                        authority_class: op.authority_class,
                        input_type: op.input_type,
                        output_type: op.output_type,
                        simulation: simulation_defaults(op.authority_class),
                    }
                })
                .collect();

            GeneratedEffectFamily {
                interface_name: effect.name,
                request_enum_name,
                outcome_enum_name,
                host_trait_name,
                simulator_trait_name,
                scenario_builder_name,
                operations,
            }
        })
        .collect()
}

/// Generate canonical Rust effect interfaces, manifests, and optional simulator
/// scaffolds from declared effect families.
pub fn generate_effect_interface_scaffold(
    out_dir: &Path,
    families: &[GeneratedEffectFamily],
    with_simulator: bool,
) -> Result<Vec<PathBuf>, String> {
    fs::create_dir_all(out_dir).map_err(|e| {
        format!(
            "failed to create output directory '{}': {e}",
            out_dir.display()
        )
    })?;

    let files = build_effect_family_files(families, with_simulator)?;
    preflight_absent_targets(out_dir, &files)?;
    write_files_transactionally(out_dir, &files)
}

#[derive(Debug, Clone)]
struct GeneratedFile {
    name: &'static str,
    kind: &'static str,
    content: String,
}

fn build_effect_family_files(
    families: &[GeneratedEffectFamily],
    with_simulator: bool,
) -> Result<Vec<GeneratedFile>, String> {
    let mut files = vec![
        GeneratedFile {
            name: "generated_effects.rs",
            kind: "generated effect interface scaffold",
            content: render_generated_effects(families),
        },
        GeneratedFile {
            name: "generated_effect_manifest.json",
            kind: "generated effect manifest",
            content: serde_json::to_string_pretty(families)
                .map_err(|e| format!("encode effect manifest: {e}"))?,
        },
        GeneratedFile {
            name: "README.md",
            kind: "generated effect README",
            content: render_generated_readme(families, with_simulator),
        },
    ];

    if with_simulator {
        files.push(GeneratedFile {
            name: "generated_simulator.rs",
            kind: "generated simulator scaffold",
            content: render_generated_simulator(families),
        });
    }

    Ok(files)
}

fn preflight_absent_targets(out_dir: &Path, files: &[GeneratedFile]) -> Result<(), String> {
    for file in files {
        let path = out_dir.join(file.name);
        if path.exists() {
            return Err(format!(
                "{} already exists at '{}'; use a new output directory or remove existing files",
                file.kind,
                path.display()
            ));
        }
    }
    Ok(())
}

fn write_files_transactionally(
    out_dir: &Path,
    files: &[GeneratedFile],
) -> Result<Vec<PathBuf>, String> {
    let stage_dir = out_dir.join(format!(
        ".effect_scaffold_stage_{}_{}",
        std::process::id(),
        now_nanos()
    ));
    fs::create_dir_all(&stage_dir).map_err(|e| {
        format!(
            "failed to create staging directory '{}': {e}",
            stage_dir.display()
        )
    })?;

    for file in files {
        let stage_path = stage_dir.join(file.name);
        if let Err(err) = fs::write(&stage_path, &file.content) {
            drop(fs::remove_dir_all(&stage_dir));
            return Err(format!(
                "failed to write staging file '{}': {err}",
                stage_path.display()
            ));
        }
    }

    let mut moved = Vec::new();
    for file in files {
        let stage_path = stage_dir.join(file.name);
        let target_path = out_dir.join(file.name);
        if let Err(err) = fs::rename(&stage_path, &target_path) {
            rollback_moved_files(&moved);
            drop(fs::remove_dir_all(&stage_dir));
            return Err(format!(
                "failed to finalize '{}' from staging '{}': {err}",
                target_path.display(),
                stage_path.display()
            ));
        }
        moved.push(target_path);
    }

    if let Err(err) = fs::remove_dir(&stage_dir) {
        return Err(format!(
            "generated files but failed to clean staging directory '{}': {err}",
            stage_dir.display()
        ));
    }

    Ok(moved)
}

fn rollback_moved_files(paths: &[PathBuf]) {
    for path in paths {
        drop(fs::remove_file(path));
    }
}

fn render_generated_effects(families: &[GeneratedEffectFamily]) -> String {
    let mut out = String::from(
        "// @generated by effect-scaffold from Telltale `effect` declarations.\n\
         // This file is the canonical Rust-facing effect boundary for the declared interfaces.\n\n\
         use serde::{Deserialize, Serialize};\n\
         use serde_json::Value;\n\n",
    );

    for family in families {
        out.push_str(&format!(
            "#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]\n\
             pub enum {} {{\n",
            family.request_enum_name
        ));
        for op in &family.operations {
            let variant_name = operation_variant_name(op);
            out.push_str(&format!(
                "    {}({}),\n",
                variant_name, op.request_type_name
            ));
        }
        out.push_str("}\n\n");

        out.push_str(&format!(
            "#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]\n\
             pub enum {} {{\n",
            family.outcome_enum_name
        ));
        for op in &family.operations {
            let variant_name = operation_variant_name(op);
            out.push_str(&format!(
                "    {}({}),\n",
                variant_name, op.outcome_type_name
            ));
        }
        out.push_str("}\n\n");

        for op in &family.operations {
            out.push_str(&render_request_struct(op));
            out.push('\n');
            out.push_str(&render_outcome_enum(op));
            out.push('\n');
        }

        out.push_str(&format!("pub trait {} {{\n", family.host_trait_name));
        for op in &family.operations {
            out.push_str(&format!(
                "    fn {}(&self, request: {}) -> {};\n",
                op.rust_method_name, op.request_type_name, op.outcome_type_name
            ));
        }
        out.push_str("}\n\n");
    }

    out
}

fn render_generated_simulator(families: &[GeneratedEffectFamily]) -> String {
    let mut out = String::from(
        "// @generated by effect-scaffold from Telltale `effect` declarations.\n\
         // This file provides first-class simulator helpers for generated effect families.\n\n\
         use std::collections::BTreeMap;\n\n\
         use serde_json::Value;\n\
         use telltale_simulator::generated::{GeneratedEffectScenario, GeneratedEffectScenarioBuilder, ScenarioEffectResult};\n\n",
    );

    for family in families {
        out.push_str(&format!(
            "#[derive(Debug, Clone, Default)]\n\
pub struct {}State {{\n\
    pub values: BTreeMap<String, Value>,\n\
    pub event_log: Vec<String>,\n\
}}\n\n",
            family.interface_name
        ));

        out.push_str(&format!(
            "#[derive(Debug, Clone, Default)]\n\
pub struct {} {{\n\
    builder: GeneratedEffectScenarioBuilder,\n\
}}\n\n\
impl {} {{\n\
    pub fn new() -> Self {{\n\
        Self::default()\n\
    }}\n\n",
            family.scenario_builder_name, family.scenario_builder_name
        ));
        for op in &family.operations {
            out.push_str(&render_scenario_builder_methods(family, op));
        }
        out.push_str(
            "    pub fn build(self) -> GeneratedEffectScenario {\n        self.builder.build()\n    }\n}\n\n",
        );

        out.push_str(&format!("pub trait {} {{\n", family.simulator_trait_name));
        for op in &family.operations {
            out.push_str(&format!(
                "    fn {}(&mut self, state: &mut {}State, request: Value) -> ScenarioEffectResult<Value>;\n",
                op.rust_method_name, family.interface_name
            ));
        }
        out.push_str("}\n\n");
    }

    out
}

fn render_generated_readme(families: &[GeneratedEffectFamily], with_simulator: bool) -> String {
    let mut out = String::from(
        "# Generated Effect Interfaces\n\n\
         This directory was generated from Telltale `effect` declarations. The DSL is the single\n\
         source of truth for the Rust host boundary, simulator scenario helpers, and exported\n\
         effect-family manifest.\n\n\
         ## Files\n\n\
         - `generated_effects.rs`: canonical request/outcome enums and host-handler traits.\n\
         - `generated_effect_manifest.json`: schema/export manifest for the same effect families.\n",
    );
    if with_simulator {
        out.push_str(
            "- `generated_simulator.rs`: first-class simulator state, traits, and scenario builders.\n",
        );
    }
    out.push_str("\n## Declared effect families\n\n");
    for family in families {
        out.push_str(&format!("- `{}`\n", family.interface_name));
        for op in &family.operations {
            out.push_str(&format!(
                "  - `{}.{}`: `{}` input, `{}` output, `{}` authority, `{}` simulation\n",
                family.interface_name,
                op.operation_name,
                op.input_type,
                op.output_type,
                authority_class_name(op.authority_class),
                simulation_mode_name(op.simulation.mode)
            ));
        }
    }

    out.push_str(
        "\n## Next steps\n\n\
         1. Implement the generated external-handler traits in the host runtime.\n\
         2. Keep simulator scenarios in CI for success, timeout, cancellation, stale late result,\n\
            blocked, and degraded cases.\n\
         3. Treat `generated_effect_manifest.json` as the exported schema surface for this guest runtime.\n",
    );
    out
}

fn render_request_struct(op: &GeneratedEffectOperation) -> String {
    format!(
        "#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]\n\
pub struct {} {{\n\
    pub input: Value,\n\
}}\n\n\
impl {} {{\n\
    pub const INTERFACE_NAME: &'static str = \"{}\";\n\
    pub const OPERATION_NAME: &'static str = \"{}\";\n\
    pub const DSL_INPUT_TYPE: &'static str = \"{}\";\n\
    pub const AUTHORITY_CLASS: &'static str = \"{}\";\n\
}}\n",
        op.request_type_name,
        op.request_type_name,
        op.interface_name,
        op.operation_name,
        op.input_type,
        authority_class_name(op.authority_class),
    )
}

fn render_outcome_enum(op: &GeneratedEffectOperation) -> String {
    format!(
        "#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]\n\
pub enum {} {{\n\
    Return {{ value: Value }},\n\
    Timeout,\n\
    Cancelled,\n\
    StaleLateResult,\n\
    Blocked,\n\
    Degraded {{ detail: String }},\n\
    Error {{ value: Value }},\n\
}}\n\n\
impl {} {{\n\
    pub const DSL_OUTPUT_TYPE: &'static str = \"{}\";\n\
    pub const SIMULATION_MODE: &'static str = \"{}\";\n\
}}\n",
        op.outcome_type_name,
        op.outcome_type_name,
        op.output_type,
        simulation_mode_name(op.simulation.mode),
    )
}

fn render_scenario_builder_methods(
    family: &GeneratedEffectFamily,
    op: &GeneratedEffectOperation,
) -> String {
    let interface = &family.interface_name;
    let operation = &op.operation_name;
    let method = &op.rust_method_name;
    format!(
        "    pub fn {method}_success(mut self, payload: Value) -> Self {{\n\
        self.builder = self.builder.record_return(\"{interface}\", \"{operation}\", payload);\n\
        self\n\
    }}\n\n\
    pub fn {method}_timeout(mut self) -> Self {{\n\
        self.builder = self.builder.record_timeout(\"{interface}\", \"{operation}\");\n\
        self\n\
    }}\n\n\
    pub fn {method}_cancelled(mut self) -> Self {{\n\
        self.builder = self.builder.record_cancelled(\"{interface}\", \"{operation}\");\n\
        self\n\
    }}\n\n\
    pub fn {method}_stale_late_result(mut self) -> Self {{\n\
        self.builder = self.builder.record_stale_late_result(\"{interface}\", \"{operation}\");\n\
        self\n\
    }}\n\n\
    pub fn {method}_blocked(mut self) -> Self {{\n\
        self.builder = self.builder.record_blocked(\"{interface}\", \"{operation}\");\n\
        self\n\
    }}\n\n\
    pub fn {method}_degraded(mut self, detail: impl Into<String>) -> Self {{\n\
        self.builder = self.builder.record_degraded(\"{interface}\", \"{operation}\", detail);\n\
        self\n\
    }}\n\n\
    pub fn {method}_with_delay_ms(mut self, delay_ms: u64) -> Self {{\n\
        self.builder = self.builder.with_delay_ms(delay_ms);\n\
        self\n\
    }}\n\n"
    )
}

fn simulation_defaults(authority_class: EffectAuthorityClass) -> GeneratedSimulationMetadata {
    match authority_class {
        EffectAuthorityClass::Observe => GeneratedSimulationMetadata {
            behavior: GeneratedEffectBehavior::Stream,
            mode: GeneratedSimulationMode::Deterministic,
            latency_policy: "best_effort".to_string(),
            timeout_policy: "not_authoritative".to_string(),
        },
        EffectAuthorityClass::Authoritative => GeneratedSimulationMetadata {
            behavior: GeneratedEffectBehavior::OneShot,
            mode: GeneratedSimulationMode::Deterministic,
            latency_policy: "bounded".to_string(),
            timeout_policy: "required".to_string(),
        },
        EffectAuthorityClass::Command => GeneratedSimulationMetadata {
            behavior: GeneratedEffectBehavior::OneShot,
            mode: GeneratedSimulationMode::Deterministic,
            latency_policy: "immediate".to_string(),
            timeout_policy: "optional".to_string(),
        },
    }
}

fn authority_class_name(class: EffectAuthorityClass) -> &'static str {
    match class {
        EffectAuthorityClass::Authoritative => "authoritative",
        EffectAuthorityClass::Command => "command",
        EffectAuthorityClass::Observe => "observe",
    }
}

fn operation_variant_name(op: &GeneratedEffectOperation) -> String {
    to_upper_camel_case(&op.operation_name)
}

fn simulation_mode_name(mode: GeneratedSimulationMode) -> &'static str {
    match mode {
        GeneratedSimulationMode::Deterministic => "deterministic",
        GeneratedSimulationMode::Adversarial => "adversarial",
    }
}

fn to_snake_case(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    for (idx, ch) in input.chars().enumerate() {
        if ch.is_ascii_uppercase() {
            if idx > 0 {
                out.push('_');
            }
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push(ch);
        }
    }
    out
}

fn to_upper_camel_case(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    let mut uppercase_next = true;
    for ch in input.chars() {
        if ch == '_' || ch == '-' {
            uppercase_next = true;
            continue;
        }
        if uppercase_next {
            out.push(ch.to_ascii_uppercase());
            uppercase_next = false;
        } else {
            out.push(ch);
        }
    }
    out
}

fn now_nanos() -> u128 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |duration| duration.as_nanos())
}

#[cfg(test)]
mod tests {
    use super::{
        generate_effect_interface_scaffold, generated_effect_families, now_nanos,
        render_generated_effects, render_generated_simulator, GeneratedEffectBehavior,
    };
    use crate::compiler::parser::parse_choreography_str;
    use std::env;
    use std::fs;
    use std::path::PathBuf;

    fn sample_dsl() -> &'static str {
        r#"
effect Runtime
  authoritative readChannel : ChannelRef -> Result ReadError ChannelSnapshot
  {
    class : authoritative
    progress : may_block
    region : fragment
    agreement_use : required
    reentrancy : reject_same_fragment
  }
  command acceptInvite : InviteRef -> Result AcceptError MaterializedChannel
  {
    class : best_effort
    progress : immediate
    region : session
    agreement_use : none
    reentrancy : allow
  }
  observe watchPresence : ChannelId -> PresenceView
  {
    class : observational
    progress : immediate
    region : session
    agreement_use : forbidden
    reentrancy : allow
  }

protocol Flow uses Runtime =
  roles Coordinator
  Coordinator -> Coordinator : Ping
"#
    }

    #[test]
    fn generated_effect_families_follow_declared_effect_interfaces() {
        let choreography = parse_choreography_str(sample_dsl()).expect("parse effect surface");
        let families = generated_effect_families(&choreography);
        assert_eq!(families.len(), 1);
        let runtime = &families[0];
        assert_eq!(runtime.interface_name, "Runtime");
        assert_eq!(runtime.host_trait_name, "RuntimeExternalHandler");
        assert_eq!(runtime.simulator_trait_name, "RuntimeSimulatorHandler");
        assert_eq!(runtime.operations.len(), 3);
        assert_eq!(runtime.operations[0].rust_method_name, "read_channel");
        assert_eq!(
            runtime.operations[2].simulation.behavior,
            GeneratedEffectBehavior::Stream
        );
    }

    #[test]
    fn generated_effect_rendering_emits_host_and_simulator_surfaces() {
        let choreography = parse_choreography_str(sample_dsl()).expect("parse choreography");
        let families = generated_effect_families(&choreography);

        let effects = render_generated_effects(&families);
        assert!(effects.contains("pub enum RuntimeRequest"));
        assert!(effects.contains("pub trait RuntimeExternalHandler"));
        assert!(effects.contains("pub struct RuntimeReadChannelRequest"));
        assert!(effects.contains("pub enum RuntimeWatchPresenceOutcome"));

        let simulator = render_generated_simulator(&families);
        assert!(simulator.contains("pub struct RuntimeScenarioBuilder"));
        assert!(simulator.contains("pub trait RuntimeSimulatorHandler"));
        assert!(simulator.contains("read_channel_success"));
    }

    #[test]
    fn scaffold_generation_writes_expected_files() {
        let out_dir = unique_temp_dir("effect_scaffold_ok");
        let choreography = parse_choreography_str(sample_dsl()).expect("parse choreography");
        let generated = generate_effect_interface_scaffold(
            &out_dir,
            &generated_effect_families(&choreography),
            true,
        )
        .expect("generation succeeds");

        assert_eq!(generated.len(), 4);
        assert!(out_dir.join("generated_effects.rs").exists());
        assert!(out_dir.join("generated_effect_manifest.json").exists());
        assert!(out_dir.join("generated_simulator.rs").exists());
        assert!(out_dir.join("README.md").exists());
        let effects = fs::read_to_string(out_dir.join("generated_effects.rs")).expect("read");
        assert!(effects.contains("RuntimeExternalHandler"));
        let simulator =
            fs::read_to_string(out_dir.join("generated_simulator.rs")).expect("read sim");
        assert!(simulator.contains("RuntimeScenarioBuilder"));

        drop(fs::remove_dir_all(out_dir));
    }

    #[test]
    fn preflight_rejects_existing_files_without_partial_writes() {
        let out_dir = unique_temp_dir("effect_scaffold_preflight");
        fs::create_dir_all(&out_dir).expect("create out dir");
        fs::write(
            out_dir.join("generated_effect_manifest.json"),
            "already here",
        )
        .expect("seed existing file");
        let choreography = parse_choreography_str(sample_dsl()).expect("parse choreography");

        let error = generate_effect_interface_scaffold(
            &out_dir,
            &generated_effect_families(&choreography),
            true,
        )
        .expect_err("preflight should fail");
        assert!(error.contains("generated_effect_manifest.json"));
        assert!(!out_dir.join("generated_effects.rs").exists());
        assert!(!out_dir.join("generated_simulator.rs").exists());
        assert!(!out_dir.join("README.md").exists());

        drop(fs::remove_dir_all(out_dir));
    }

    fn unique_temp_dir(prefix: &str) -> PathBuf {
        let mut path = env::temp_dir();
        path.push(format!("{prefix}_{}_{}", std::process::id(), now_nanos()));
        path
    }
}
