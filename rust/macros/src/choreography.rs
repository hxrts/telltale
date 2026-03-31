//! Telltale protocol definition macro implementation.
//!
//! Parsing is delegated to the shared Telltale frontend. This proc-macro emits
//! a protocol module that always contains the canonical spec/effect surfaces
//! and, when projection succeeds, a derived `sessions` module.

use proc_macro::{Delimiter, TokenStream as MacroTokenStream, TokenTree as MacroTokenTree};
use proc_macro2::{Delimiter as TokenDelimiter, Group, Ident, Span, TokenStream, TokenTree};
use quote::{format_ident, quote, ToTokens};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use syn::{Error, LitStr, Result};
use telltale_language::ast::{
    AgreementProfileDeclaration, AuthorityBindingMode, AuthorityExpr, Branch,
    ChildEffectAggregationPolicy, Choreography, EffectInterfaceDeclaration,
    EffectOperationDeclaration, LocalType, MessageType, OperationDeclaration, Protocol, Role,
    TypeDeclaration,
};

struct ParsedMacroChoreography {
    choreography: Choreography,
    source: String,
}

/// Main entry point for the tell! macro.
///
/// This macro is intentionally outside the current formal-verification claim.
/// It is treated as a public frontend convenience surface whose generated
/// output is checked by compiler-pipeline, Lean-correspondence, and macro-UI
/// gates rather than by a mechanized macro-expansion proof.
pub fn tell(input: MacroTokenStream) -> Result<TokenStream> {
    let parsed = parse_macro_choreography(input)?;
    parsed
        .choreography
        .validate()
        .map_err(|err| Error::new(Span::call_site(), err.to_string()))?;

    let generated = generate_protocol_module(&parsed.choreography, &parsed.source)?;
    Ok(generated)
}

fn parse_macro_choreography(input: MacroTokenStream) -> Result<ParsedMacroChoreography> {
    if let Ok(lit_str) = syn::parse::<LitStr>(input.clone()) {
        return Err(Error::new(
            lit_str.span(),
            "string-literal tell input was removed; use the canonical indentation-based token DSL directly",
        ));
    }

    let source = macro_source_text(input)
        .map(normalize_macro_indentation)
        .ok_or_else(|| {
            Error::new(
                Span::call_site(),
                "failed to recover original choreography source from macro input",
            )
        })?;

    let choreography = telltale_language::parse_choreography_str(&source).map_err(|err| {
        Error::new(
            Span::call_site(),
            format!(
                "Choreography parse error: {err}\n\
                 Macro token input is parsed from original source text.\n\
                 Use the canonical indentation-based DSL surface in token form."
            ),
        )
    })?;

    Ok(ParsedMacroChoreography {
        choreography,
        source,
    })
}

fn normalize_macro_indentation(source: String) -> String {
    const TOP_LEVEL_HEADERS: &[&str] = &[
        "module ",
        "import ",
        "protocol ",
        "proof_bundle ",
        "profile ",
        "agreement_profile ",
        "role_set ",
        "topology ",
        "type ",
        "effect ",
        "fragment ",
        "operation ",
        "guest runtime ",
    ];

    let mut normalized = String::new();
    for line in source.lines() {
        let trimmed = line.trim_start();
        if TOP_LEVEL_HEADERS
            .iter()
            .any(|prefix| trimmed.starts_with(prefix))
        {
            normalized.push_str(trimmed);
        } else {
            normalized.push_str(line);
        }
        normalized.push('\n');
    }

    if !source.ends_with('\n') {
        normalized.pop();
    }
    normalized
}

fn macro_source_text(input: MacroTokenStream) -> Option<String> {
    #[derive(Clone, Copy)]
    struct Location {
        line: usize,
        column: usize,
    }

    #[allow(clippy::incompatible_msrv)]
    fn location_of(span: proc_macro::Span) -> (Location, Location) {
        let start = span.start();
        let end = span.end();
        (
            Location {
                line: start.line(),
                column: start.column(),
            },
            Location {
                line: end.line(),
                column: end.column(),
            },
        )
    }

    fn append_gap(out: &mut String, previous_end: Location, next_start: Location) {
        if next_start.line > previous_end.line {
            for _ in previous_end.line..next_start.line {
                out.push('\n');
            }
            for _ in 0..next_start.column {
                out.push(' ');
            }
        } else if next_start.column > previous_end.column {
            for _ in previous_end.column..next_start.column {
                out.push(' ');
            }
        }
    }

    fn append_stream(
        out: &mut String,
        previous_end: &mut Option<Location>,
        stream: MacroTokenStream,
    ) -> Option<()> {
        for token in stream {
            match token {
                MacroTokenTree::Group(group) => {
                    let (open_start, _) = location_of(group.span_open());
                    let (_, close_end) = location_of(group.span_close());
                    if let Some(prev) = previous_end.as_ref() {
                        append_gap(out, *prev, open_start);
                    }
                    out.push_str(&group.to_string());
                    *previous_end = Some(close_end);
                }
                MacroTokenTree::Ident(ident) => {
                    let (start, end) = location_of(ident.span());
                    if let Some(prev) = previous_end.as_ref() {
                        append_gap(out, *prev, start);
                    }
                    out.push_str(&ident.to_string());
                    *previous_end = Some(end);
                }
                MacroTokenTree::Punct(punct) => {
                    let (start, end) = location_of(punct.span());
                    if let Some(prev) = previous_end.as_ref() {
                        append_gap(out, *prev, start);
                    }
                    out.push(punct.as_char());
                    *previous_end = Some(end);
                }
                MacroTokenTree::Literal(literal) => {
                    let (start, end) = location_of(literal.span());
                    if let Some(prev) = previous_end.as_ref() {
                        append_gap(out, *prev, start);
                    }
                    out.push_str(&literal.to_string());
                    *previous_end = Some(end);
                }
            }
        }
        Some(())
    }

    fn strip_group_source(source: &str, delimiter: Delimiter) -> String {
        let trimmed = source.trim();
        match delimiter {
            Delimiter::Parenthesis | Delimiter::Brace | Delimiter::Bracket
                if trimmed.len() >= 2 =>
            {
                trimmed[1..trimmed.len() - 1].to_string()
            }
            _ => trimmed.to_string(),
        }
    }

    let mut tokens = input.clone().into_iter();
    if let Some(MacroTokenTree::Group(group)) = tokens.next() {
        let single_group = tokens.next().is_none();
        if single_group {
            if let Some(source) = group.span().source_text() {
                return Some(strip_group_source(&source, group.delimiter()));
            }
        }
        if single_group && group.delimiter() == Delimiter::Brace {
            return macro_source_text(group.stream());
        }
    }

    let mut out = String::new();
    let mut previous_end = None;
    append_stream(&mut out, &mut previous_end, input)?;
    Some(out)
}

fn project_local_types(choreography: &Choreography) -> Result<Vec<(Role, LocalType)>> {
    let mut local_types = Vec::new();
    for role in &choreography.roles {
        let local_type = telltale_language::project(choreography, role)
            .map_err(|err| Error::new(Span::call_site(), err.to_string()))?;
        local_types.push((role.clone(), local_type));
    }
    Ok(local_types)
}

fn generate_protocol_module(choreography: &Choreography, source: &str) -> Result<TokenStream> {
    let protocol_ident = format_ident!("{}", choreography.name);
    let protocol_impl_ident = format_ident!(
        "__tell_protocol_{}",
        to_snake_identifier(&choreography.name.to_string())
    );
    let choreography_source = LitStr::new(source, Span::call_site());
    let qualified_name = LitStr::new(&choreography.qualified_name(), Span::call_site());
    let language_tier_status = choreography.language_tier_status();
    let protocol_machine_executable = language_tier_status.protocol_machine_executable;
    let proof_only = language_tier_status.proof_only;
    let strongest_tier = LitStr::new(
        match language_tier_status.strongest_tier {
            telltale_language::ast::LanguageTier::FullSpec => "full_spec",
            telltale_language::ast::LanguageTier::SessionProjectable => "session_projectable",
            telltale_language::ast::LanguageTier::ProtocolMachineExecutable => {
                "protocol_machine_executable"
            }
            telltale_language::ast::LanguageTier::ProofOnly => "proof_only",
        },
        Span::call_site(),
    );
    let tier_diagnostic = LitStr::new(&language_tier_status.diagnostic, Span::call_site());
    let theorem_packs = choreography
        .required_theorem_packs()
        .into_iter()
        .map(|name| LitStr::new(&name, Span::call_site()))
        .collect::<Vec<_>>();
    let execution_profiles = choreography
        .protocol_execution_profiles()
        .into_iter()
        .map(|name| LitStr::new(&name, Span::call_site()))
        .collect::<Vec<_>>();
    let agreement_profile_names = choreography
        .agreement_profile_declarations()
        .into_iter()
        .map(|profile| LitStr::new(&profile.name, Span::call_site()))
        .collect::<Vec<_>>();
    let finalization_profile_names = choreography
        .agreement_profile_declarations()
        .into_iter()
        .filter(|profile| profile.finalized_at != "none")
        .map(|profile| LitStr::new(&profile.name, Span::call_site()))
        .collect::<Vec<_>>();
    let parity_critical_operations = choreography
        .operation_declarations()
        .iter()
        .map(|operation| LitStr::new(&operation.name, Span::call_site()))
        .collect::<Vec<_>>();
    let agreement_bound_operations = choreography
        .operation_declarations()
        .iter()
        .filter(|operation| operation.agreement.is_some())
        .map(|operation| LitStr::new(&operation.name, Span::call_site()))
        .collect::<Vec<_>>();
    let type_decls = generate_type_declarations(choreography)?;
    let effects_module = generate_effects_module(choreography)?;
    let authority_module = generate_authority_module(choreography)?;
    let commitments_module = generate_commitments_module(choreography)?;
    let agreements_module = generate_agreements_module(choreography)?;
    let deadlock_fragment = LitStr::new(
        "closed + contractive projected local types whose full unfold exposes send/recv",
        Span::call_site(),
    );
    let (
        projectable,
        projection_error,
        sessions_module,
        deadlock_automation_eligible,
        deadlock_automation_roles,
        deadlock_automation_diagnostic,
    ) = match project_local_types(choreography) {
        Ok(local_types) => {
            let mut eligible_roles = Vec::new();
            let mut ineligible_roles = Vec::new();
            for (role, local_type) in &local_types {
                match telltale_language::ast::convert::local_to_local_r(local_type) {
                    Ok(local_r) => {
                        if local_r.regular_practical_fragment() {
                            eligible_roles
                                .push(LitStr::new(&role.name().to_string(), Span::call_site()));
                        } else {
                            ineligible_roles.push(role.name().to_string());
                        }
                    }
                    Err(err) => {
                        ineligible_roles
                            .push(format!("{} (conversion failed: {err})", role.name()));
                    }
                }
            }
            let automation_eligible = ineligible_roles.is_empty();
            let automation_eligible = quote!(#automation_eligible);
            let automation_diagnostic = if ineligible_roles.is_empty() {
                quote!(None)
            } else {
                let reason = LitStr::new(
                    &format!(
                        "automatic deadlock-fragment discharge unavailable for roles: {}",
                        ineligible_roles.join(", ")
                    ),
                    Span::call_site(),
                );
                quote!(Some(#reason))
            };
            (
                quote!(true),
                quote!(None),
                Some(generate_sessions_module(choreography, &local_types)?),
                automation_eligible,
                eligible_roles,
                automation_diagnostic,
            )
        }
        Err(err) => {
            let message = syn::LitStr::new(&err.to_string(), Span::call_site());
            (
                quote!(false),
                quote!(Some(#message)),
                None,
                quote!(false),
                Vec::new(),
                quote!(Some("automatic deadlock-fragment discharge unavailable because session projection failed")),
            )
        }
    };

    let sessions_module = sessions_module.unwrap_or_else(TokenStream::new);
    let spec_body = quote! {
        #[allow(dead_code)]
        pub const SOURCE: &str = #choreography_source;

        #[allow(dead_code)]
        pub const QUALIFIED_NAME: &str = #qualified_name;

        pub mod proof_status {
            #[allow(dead_code)]
            pub const FULL_SPEC_LEGAL: bool = true;

            #[allow(dead_code)]
            pub const STRONGEST_TIER: &str = #strongest_tier;

            #[allow(dead_code)]
            pub const SESSION_PROJECTABLE: bool = #projectable;

            #[allow(dead_code)]
            pub const PROTOCOL_MACHINE_EXECUTABLE: bool = #protocol_machine_executable;

            #[allow(dead_code)]
            pub const PROOF_ONLY: bool = #proof_only;

            #[allow(dead_code)]
            pub const DIAGNOSTIC: &str = #tier_diagnostic;

            #[allow(dead_code)]
            pub const SESSION_PROJECTION_ERROR: Option<&str> = #projection_error;

            #[allow(dead_code)]
            pub const DEADLOCK_AUTOMATION_FRAGMENT: &str = #deadlock_fragment;

            #[allow(dead_code)]
            pub const DEADLOCK_AUTOMATION_ELIGIBLE: bool = #deadlock_automation_eligible;

            #[allow(dead_code)]
            pub const DEADLOCK_AUTOMATION_ROLES: &[&str] = &[#(#deadlock_automation_roles),*];

            #[allow(dead_code)]
            pub const DEADLOCK_AUTOMATION_DIAGNOSTIC: Option<&str> =
                #deadlock_automation_diagnostic;

            #[allow(dead_code)]
            pub const REQUIRED_THEOREM_PACKS: &[&str] = &[#(#theorem_packs),*];

            #[allow(dead_code)]
            pub const EXECUTION_PROFILES: &[&str] = &[#(#execution_profiles),*];

            #[allow(dead_code)]
            pub const AGREEMENT_PROFILE_NAMES: &[&str] = &[#(#agreement_profile_names),*];

            #[allow(dead_code)]
            pub const FINALIZATION_PROFILE_NAMES: &[&str] = &[#(#finalization_profile_names),*];

            #[allow(dead_code)]
            pub const PARITY_CRITICAL_OPERATIONS: &[&str] = &[#(#parity_critical_operations),*];

            #[allow(dead_code)]
            pub const AGREEMENT_BOUND_OPERATIONS: &[&str] = &[#(#agreement_bound_operations),*];

            #[allow(dead_code)]
            pub fn agreement_profile(
                name: &str,
            ) -> Option<&'static super::agreements::AgreementProfileMetadata> {
                super::agreements::profile(name)
            }

            #[allow(dead_code)]
            pub fn agreement_operation(
                name: &str,
            ) -> Option<&'static super::agreements::OperationAgreementMetadata> {
                super::agreements::operation(name)
            }

            #[allow(dead_code)]
            pub fn commitment_operation(
                name: &str,
            ) -> Option<&'static super::commitments::CommitmentMetadata> {
                super::commitments::operation(name)
            }
        }

        #type_decls

        #effects_module

        #authority_module

        #commitments_module

        #agreements_module

        #sessions_module
    };

    Ok(match &choreography.namespace {
        Some(namespace) => {
            let ns_ident = format_ident!("{}", namespace);
            quote! {
                pub mod #ns_ident {
                    #[doc(hidden)]
                    pub mod #protocol_impl_ident {
                        #![allow(dead_code, unused_imports, unused_variables, missing_docs)]
                        use ::telltale::serde as serde;
                        #spec_body
                    }

                    pub use #protocol_impl_ident as #protocol_ident;
                }
            }
        }
        None => quote! {
            #[doc(hidden)]
            pub mod #protocol_impl_ident {
                #![allow(dead_code, unused_imports, unused_variables, missing_docs)]
                use ::telltale::serde as serde;
                #spec_body
            }

            pub use #protocol_impl_ident as #protocol_ident;
        },
    })
}

#[derive(Clone, Debug)]
enum DslTypeExpr {
    Path(Vec<String>),
    Result(Box<DslTypeExpr>, Box<DslTypeExpr>),
    Maybe(Box<DslTypeExpr>),
    Unit,
    Record(Vec<DslRecordField>),
}

#[derive(Clone, Debug)]
struct DslRecordField {
    name: String,
    ty: DslTypeExpr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TypeToken {
    Ident(String),
    LBrace,
    RBrace,
    Colon,
    Comma,
}

fn generate_type_declarations(choreography: &Choreography) -> Result<TokenStream> {
    let declarations = choreography
        .type_declarations()
        .iter()
        .map(generate_type_declaration)
        .collect::<Result<Vec<_>>>()?;
    Ok(quote! { #(#declarations)* })
}

fn generate_type_declaration(type_decl: &TypeDeclaration) -> Result<TokenStream> {
    let name = format_ident!("{}", type_decl.name);
    if type_decl.is_alias {
        let alias_of = type_decl.alias_of.as_deref().ok_or_else(|| {
            Error::new(
                Span::call_site(),
                format!(
                    "type alias `{}` is missing a right-hand side",
                    type_decl.name
                ),
            )
        })?;
        let parsed = parse_dsl_type_expr(alias_of)?;
        match parsed {
            DslTypeExpr::Record(fields) => {
                let fields = fields
                    .iter()
                    .map(generate_record_field)
                    .collect::<Result<Vec<_>>>()?;
                Ok(quote! {
                    #[derive(Clone, Debug, PartialEq, ::telltale::serde::Serialize, ::telltale::serde::Deserialize)]
                    #[serde(crate = "::telltale::serde")]
                    pub struct #name {
                        #(#fields),*
                    }
                })
            }
            other => {
                let ty = lower_dsl_type_expr(&other, false)?;
                Ok(quote! {
                    pub type #name = #ty;
                })
            }
        }
    } else {
        let variants = type_decl
            .constructors
            .iter()
            .map(|constructor| {
                let variant = format_ident!("{}", constructor.name);
                if let Some(payload_type) = constructor.payload_type.as_deref() {
                    let payload = lower_dsl_type_expr(&parse_dsl_type_expr(payload_type)?, false)?;
                    Ok(quote!(#variant(#payload)))
                } else {
                    Ok(quote!(#variant))
                }
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(quote! {
            #[derive(Clone, Debug, PartialEq, ::telltale::serde::Serialize, ::telltale::serde::Deserialize)]
            #[serde(crate = "::telltale::serde")]
            pub enum #name {
                #(#variants),*
            }

            impl ::std::fmt::Display for #name {
                fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
                    write!(f, "{self:?}")
                }
            }

            impl ::std::error::Error for #name {}
        })
    }
}

fn generate_record_field(field: &DslRecordField) -> Result<TokenStream> {
    let rust_name = to_snake_identifier(&field.name);
    let field_ident = format_ident!("{}", rust_name);
    let field_ty = lower_dsl_type_expr(&field.ty, false)?;
    let rename_attr = if rust_name != field.name {
        let original = &field.name;
        quote!(#[serde(rename = #original)])
    } else {
        TokenStream::new()
    };
    Ok(quote! {
        #rename_attr
        pub #field_ident: #field_ty
    })
}

fn generate_effects_module(choreography: &Choreography) -> Result<TokenStream> {
    let used_effects = choreography
        .protocol_uses()
        .into_iter()
        .collect::<BTreeSet<_>>();
    let type_exports = choreography
        .type_declarations()
        .iter()
        .map(|decl| format_ident!("{}", decl.name))
        .collect::<Vec<_>>();
    let effect_surfaces = choreography
        .effect_interface_declarations()
        .iter()
        .map(|effect| generate_effect_surface(effect, used_effects.contains(effect.name.as_str())))
        .collect::<Result<Vec<_>>>()?;

    let type_exports = if type_exports.is_empty() {
        TokenStream::new()
    } else {
        quote!(pub use super::{#(#type_exports),*};)
    };

    Ok(quote! {
        pub mod effects {
            pub use ::telltale::dsl::{AuditEvent, PresenceView, Role, Session};
            pub use ::telltale::dsl::semantic::{
                EffectAdmissibility,
                EffectAgreementUse,
                EffectAuthorityClass,
                EffectHandlerDomain,
                EffectInterfaceMetadata,
                EffectReentrancyPolicy,
                EffectRegionScope,
                EffectRetryShape,
                EffectSemanticClass,
                EffectTimeoutPolicy,
                EffectTotality,
            };

            #[derive(Clone, Debug, PartialEq, Eq)]
            pub struct EffectOperationMetadata {
                pub interface_name: &'static str,
                pub operation_name: &'static str,
                pub authority_class: EffectAuthorityClass,
                pub semantic_class: EffectSemanticClass,
                pub agreement_use: EffectAgreementUse,
                pub region_scope: EffectRegionScope,
                pub admissibility: EffectAdmissibility,
                pub totality: EffectTotality,
                pub timeout_policy: EffectTimeoutPolicy,
                pub retry_shape: EffectRetryShape,
                pub reentrancy_policy: EffectReentrancyPolicy,
                pub handler_domain: EffectHandlerDomain,
            }

            impl EffectOperationMetadata {
                #[must_use]
                pub fn runtime_metadata(&self) -> EffectInterfaceMetadata {
                    EffectInterfaceMetadata {
                        interface_name: self.interface_name.to_string(),
                        operation_name: self.operation_name.to_string(),
                        authority_class: self.authority_class,
                        semantic_class: self.semantic_class,
                        agreement_use: self.agreement_use,
                        region_scope: self.region_scope,
                        admissibility: self.admissibility,
                        totality: self.totality,
                        timeout_policy: self.timeout_policy.clone(),
                        retry_shape: self.retry_shape.clone(),
                        reentrancy_policy: self.reentrancy_policy,
                        handler_domain: self.handler_domain,
                    }
                }

                #[must_use]
                pub fn architecturally_legal(&self) -> bool {
                    self.runtime_metadata().architecturally_legal()
                }
            }

            #[derive(Clone, Debug, PartialEq, Eq)]
            pub struct EffectInterfaceSurfaceMetadata {
                pub interface_name: &'static str,
                pub operations: &'static [EffectOperationMetadata],
            }

            impl EffectInterfaceSurfaceMetadata {
                #[must_use]
                pub fn operation(&self, name: &str) -> Option<&'static EffectOperationMetadata> {
                    self.operations.iter().find(|entry| entry.operation_name == name)
                }

                #[must_use]
                pub fn runtime_metadata(&self) -> ::std::vec::Vec<EffectInterfaceMetadata> {
                    self.operations
                        .iter()
                        .map(EffectOperationMetadata::runtime_metadata)
                        .collect()
                }

                #[must_use]
                pub fn runtime_legal(&self) -> bool {
                    self.operations.iter().all(EffectOperationMetadata::architecturally_legal)
                }
            }

            #type_exports
            #(#effect_surfaces)*
        }
    })
}

fn generate_effect_surface(
    effect: &EffectInterfaceDeclaration,
    is_used: bool,
) -> Result<TokenStream> {
    let trait_name = format_ident!("{}", effect.name);
    let metadata_module_name = format_ident!("{}", to_snake_identifier(&effect.name));
    let request_name = format_ident!("{}Request", effect.name);
    let outcome_name = format_ident!("{}Outcome", effect.name);
    let request_variants = effect
        .operations
        .iter()
        .map(generate_effect_request_variant)
        .collect::<Result<Vec<_>>>()?;
    let outcome_variants = effect
        .operations
        .iter()
        .map(generate_effect_outcome_variant)
        .collect::<Result<Vec<_>>>()?;
    let methods = effect
        .operations
        .iter()
        .map(generate_effect_method_signature)
        .collect::<Result<Vec<_>>>()?;
    let handle_arms = effect
        .operations
        .iter()
        .map(|op| generate_effect_handle_arm(op, &request_name, &outcome_name))
        .collect::<Result<Vec<_>>>()?;
    let metadata_entries = effect
        .operations
        .iter()
        .map(|op| generate_effect_operation_metadata_entry(effect, op, is_used))
        .collect::<Result<Vec<_>>>()?;
    let operation_lookup_entries = effect
        .operations
        .iter()
        .map(generate_effect_operation_lookup_entry)
        .collect::<Vec<_>>();
    let request_metadata_arms = effect
        .operations
        .iter()
        .map(|op| generate_effect_request_metadata_arm(op, &request_name))
        .collect::<Vec<_>>();
    let interface_name = LitStr::new(&effect.name, Span::call_site());

    Ok(quote! {
        pub mod #metadata_module_name {
            use super::*;

            #(#metadata_entries)*

            pub const OPERATIONS: &[EffectOperationMetadata] = &[#(#operation_lookup_entries),*];

            pub const INTERFACE: EffectInterfaceSurfaceMetadata = EffectInterfaceSurfaceMetadata {
                interface_name: #interface_name,
                operations: OPERATIONS,
            };

            #[must_use]
            pub fn metadata() -> &'static EffectInterfaceSurfaceMetadata {
                &INTERFACE
            }

            #[must_use]
            pub fn operation(name: &str) -> Option<&'static EffectOperationMetadata> {
                INTERFACE.operation(name)
            }

            #[must_use]
            pub fn request_metadata(request: &#request_name) -> &'static EffectOperationMetadata {
                match request {
                    #(#request_metadata_arms),*
                }
            }
        }

        #[derive(Clone, Debug, PartialEq, ::telltale::serde::Serialize, ::telltale::serde::Deserialize)]
        #[serde(crate = "::telltale::serde")]
        pub enum #request_name {
            #(#request_variants),*
        }

        #[derive(Clone, Debug, PartialEq, ::telltale::serde::Serialize, ::telltale::serde::Deserialize)]
        #[serde(crate = "::telltale::serde")]
        pub enum #outcome_name {
            #(#outcome_variants),*
        }

        pub trait #trait_name {
            #(#methods)*

            fn handle(&mut self, request: #request_name) -> #outcome_name {
                match request {
                    #(#handle_arms),*
                }
            }
        }
    })
}

#[derive(Default)]
struct AuthoritySurfaceCollector {
    authoritative_reads: BTreeMap<String, (String, String)>,
    observed_reads: BTreeMap<String, (String, String)>,
    publications: BTreeMap<String, String>,
    materializations: BTreeMap<String, String>,
    receipts: BTreeMap<String, (String, String, String)>,
    handoffs: BTreeMap<String, (String, String)>,
}

fn generate_authority_module(choreography: &Choreography) -> Result<TokenStream> {
    let mut collector = AuthoritySurfaceCollector::default();
    collect_authority_surfaces(&choreography.protocol, &mut collector);

    let authoritative_reads = collector
        .authoritative_reads
        .iter()
        .map(|(binding_name, (effect_interface, effect_operation))| {
            let binding_name = LitStr::new(binding_name, Span::call_site());
            let effect_interface = LitStr::new(effect_interface, Span::call_site());
            let effect_operation = LitStr::new(effect_operation, Span::call_site());
            quote! {
                AuthorityReadMetadata {
                    binding_name: #binding_name,
                    effect_interface: #effect_interface,
                    effect_operation: #effect_operation,
                    capability_class: ProtocolCriticalCapabilityClass::Evidence,
                    read_class: FinalizationReadClass::AuthoritativeOnly,
                }
            }
        })
        .collect::<Vec<_>>();
    let observed_reads = collector
        .observed_reads
        .iter()
        .map(|(binding_name, (effect_interface, effect_operation))| {
            let binding_name = LitStr::new(binding_name, Span::call_site());
            let effect_interface = LitStr::new(effect_interface, Span::call_site());
            let effect_operation = LitStr::new(effect_operation, Span::call_site());
            quote! {
                AuthorityReadMetadata {
                    binding_name: #binding_name,
                    effect_interface: #effect_interface,
                    effect_operation: #effect_operation,
                    capability_class: ProtocolCriticalCapabilityClass::Evidence,
                    read_class: FinalizationReadClass::ObservedOnly,
                }
            }
        })
        .collect::<Vec<_>>();
    let publications = collector
        .publications
        .iter()
        .map(|(publication_name, witness_name)| {
            let publication_name = LitStr::new(publication_name, Span::call_site());
            let witness_name = LitStr::new(witness_name, Span::call_site());
            quote! {
                PublicationMetadata {
                    publication_name: #publication_name,
                    witness_name: #witness_name,
                    capability_class: ProtocolCriticalCapabilityClass::Evidence,
                    finalization_stage: FinalizationStage::Authoritative,
                }
            }
        })
        .collect::<Vec<_>>();
    let materializations = collector
        .materializations
        .iter()
        .map(|(proof_name, publication_name)| {
            let proof_name = LitStr::new(proof_name, Span::call_site());
            let publication_name = LitStr::new(publication_name, Span::call_site());
            quote! {
                MaterializationMetadata {
                    proof_name: #proof_name,
                    publication_name: #publication_name,
                    capability_class: ProtocolCriticalCapabilityClass::Evidence,
                }
            }
        })
        .collect::<Vec<_>>();
    let canonical_handles = collector
        .materializations
        .iter()
        .map(|(proof_name, publication_name)| {
            let proof_name = LitStr::new(proof_name, Span::call_site());
            let publication_name = LitStr::new(publication_name, Span::call_site());
            quote! {
                CanonicalHandleMetadata {
                    proof_name: #proof_name,
                    publication_name: #publication_name,
                    handle_kind: CanonicalHandleKind::Materialization,
                    capability_class: ProtocolCriticalCapabilityClass::Evidence,
                }
            }
        })
        .collect::<Vec<_>>();
    let receipts = collector
        .receipts
        .iter()
        .map(|(binding_name, (subject, from_role, to_role))| {
            let binding_name = LitStr::new(binding_name, Span::call_site());
            let subject = LitStr::new(subject, Span::call_site());
            let from_role = LitStr::new(from_role, Span::call_site());
            let to_role = LitStr::new(to_role, Span::call_site());
            quote! {
                ReceiptMetadata {
                    binding_name: #binding_name,
                    subject: #subject,
                    from_role: #from_role,
                    to_role: #to_role,
                    capability_class: ProtocolCriticalCapabilityClass::Transition,
                }
            }
        })
        .collect::<Vec<_>>();
    let handoffs = collector
        .handoffs
        .iter()
        .map(|(operation_name, (target_role, receipt_name))| {
            let operation_name = LitStr::new(operation_name, Span::call_site());
            let target_role = LitStr::new(target_role, Span::call_site());
            let receipt_name = LitStr::new(receipt_name, Span::call_site());
            quote! {
                HandoffMetadata {
                    operation_name: #operation_name,
                    target_role: #target_role,
                    receipt_name: #receipt_name,
                    capability_class: ProtocolCriticalCapabilityClass::Transition,
                }
            }
        })
        .collect::<Vec<_>>();

    Ok(quote! {
        pub mod authority {
            pub use ::telltale::dsl::semantic::{
                AuthoritativeRead,
                AuthoritativeReadKind,
                AuthoritativeReadLifecycle,
                CanonicalHandle,
                CanonicalHandleKind,
                DelegationStatus,
                FinalizationReadClass,
                FinalizationStage,
                MaterializationProof,
                ObservedRead,
                OutstandingEffectStatus,
                OwnershipScope,
                ProtocolCriticalCapabilityClass,
                PublicationEvent,
                PublicationObserverClass,
                PublicationStatus,
                SemanticHandoff,
            };

            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub struct AuthorityReadMetadata {
                pub binding_name: &'static str,
                pub effect_interface: &'static str,
                pub effect_operation: &'static str,
                pub capability_class: ProtocolCriticalCapabilityClass,
                pub read_class: FinalizationReadClass,
            }

            impl AuthorityReadMetadata {
                #[must_use]
                pub fn authoritative_read(
                    &self,
                    read_id: impl Into<::std::string::String>,
                ) -> AuthoritativeRead {
                    AuthoritativeRead {
                        read_id: read_id.into(),
                        session: None,
                        owner_id: None,
                        kind: AuthoritativeReadKind::Readiness,
                        lifecycle: AuthoritativeReadLifecycle::Issued,
                        predicate_ref: ::std::option::Option::Some(format!(
                            "{}.{}",
                            self.effect_interface, self.effect_operation
                        )),
                        witness_id: None,
                        generation: None,
                        reason: None,
                    }
                }

                #[must_use]
                pub fn observed_read(
                    &self,
                    read_id: impl Into<::std::string::String>,
                    effect_id: u64,
                    handler_identity: impl Into<::std::string::String>,
                ) -> ObservedRead {
                    ObservedRead {
                        read_id: read_id.into(),
                        session: None,
                        effect_id,
                        effect_interface: ::std::option::Option::Some(
                            self.effect_interface.to_string(),
                        ),
                        effect_operation: ::std::option::Option::Some(
                            self.effect_operation.to_string(),
                        ),
                        handler_identity: handler_identity.into(),
                        status: OutstandingEffectStatus::Pending,
                    }
                }
            }

            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub struct PublicationMetadata {
                pub publication_name: &'static str,
                pub witness_name: &'static str,
                pub capability_class: ProtocolCriticalCapabilityClass,
                pub finalization_stage: FinalizationStage,
            }

            impl PublicationMetadata {
                #[must_use]
                pub fn publication_event(
                    &self,
                    publication_id: impl Into<::std::string::String>,
                    operation_id: impl Into<::std::string::String>,
                ) -> PublicationEvent {
                    PublicationEvent {
                        publication_id: publication_id.into(),
                        session: None,
                        operation_id: operation_id.into(),
                        owner_id: None,
                        publication: self.publication_name.to_string(),
                        observer_class: PublicationObserverClass::Canonical,
                        status: PublicationStatus::Published,
                        proof_ref: None,
                        handle_ref: None,
                        reason: None,
                    }
                }
            }

            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub struct MaterializationMetadata {
                pub proof_name: &'static str,
                pub publication_name: &'static str,
                pub capability_class: ProtocolCriticalCapabilityClass,
            }

            impl MaterializationMetadata {
                #[must_use]
                pub fn materialization_proof(
                    &self,
                    proof_id: impl Into<::std::string::String>,
                    predicate_ref: impl Into<::std::string::String>,
                    output_digest: impl Into<::std::string::String>,
                ) -> MaterializationProof {
                    MaterializationProof {
                        proof_id: proof_id.into(),
                        session: None,
                        predicate_ref: predicate_ref.into(),
                        witness_ref: ::std::option::Option::Some(self.publication_name.to_string()),
                        output_digest: output_digest.into(),
                        passed: true,
                    }
                }

                #[must_use]
                pub fn canonical_handle_metadata(&self) -> CanonicalHandleMetadata {
                    CanonicalHandleMetadata {
                        proof_name: self.proof_name,
                        publication_name: self.publication_name,
                        handle_kind: CanonicalHandleKind::Materialization,
                        capability_class: ProtocolCriticalCapabilityClass::Evidence,
                    }
                }

                #[must_use]
                pub fn canonical_handle(
                    &self,
                    handle_id: impl Into<::std::string::String>,
                    proof: &MaterializationProof,
                ) -> CanonicalHandle {
                    self.canonical_handle_metadata()
                        .canonical_handle(handle_id, proof)
                }
            }

            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub struct CanonicalHandleMetadata {
                pub proof_name: &'static str,
                pub publication_name: &'static str,
                pub handle_kind: CanonicalHandleKind,
                pub capability_class: ProtocolCriticalCapabilityClass,
            }

            impl CanonicalHandleMetadata {
                #[must_use]
                pub fn canonical_handle(
                    &self,
                    handle_id: impl Into<::std::string::String>,
                    proof: &MaterializationProof,
                ) -> CanonicalHandle {
                    CanonicalHandle {
                        handle_id: handle_id.into(),
                        session: None,
                        owner_id: None,
                        kind: self.handle_kind,
                        proof_ref: ::std::option::Option::Some(proof.proof_id.clone()),
                    }
                }
            }

            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub struct ReceiptMetadata {
                pub binding_name: &'static str,
                pub subject: &'static str,
                pub from_role: &'static str,
                pub to_role: &'static str,
                pub capability_class: ProtocolCriticalCapabilityClass,
            }

            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub struct HandoffMetadata {
                pub operation_name: &'static str,
                pub target_role: &'static str,
                pub receipt_name: &'static str,
                pub capability_class: ProtocolCriticalCapabilityClass,
            }

            impl HandoffMetadata {
                #[must_use]
                pub fn semantic_handoff(
                    &self,
                    handoff_id: u64,
                    session: usize,
                    from_coro: usize,
                    to_coro: usize,
                ) -> SemanticHandoff {
                    SemanticHandoff {
                        handoff_id,
                        session,
                        from_coro,
                        to_coro,
                        revoked_owner_id: ::std::string::String::new(),
                        activated_owner_id: self.target_role.to_string(),
                        scope: OwnershipScope::Session,
                        status: DelegationStatus::Committed,
                        tick: 0,
                        reason: ::std::option::Option::Some(self.receipt_name.to_string()),
                    }
                }
            }

            #[allow(dead_code)]
            pub const AUTHORITATIVE_READS: &[AuthorityReadMetadata] = &[#(#authoritative_reads),*];
            #[allow(dead_code)]
            pub const OBSERVED_READS: &[AuthorityReadMetadata] = &[#(#observed_reads),*];
            #[allow(dead_code)]
            pub const PUBLICATIONS: &[PublicationMetadata] = &[#(#publications),*];
            #[allow(dead_code)]
            pub const MATERIALIZATIONS: &[MaterializationMetadata] = &[#(#materializations),*];
            #[allow(dead_code)]
            pub const CANONICAL_HANDLES: &[CanonicalHandleMetadata] = &[#(#canonical_handles),*];
            #[allow(dead_code)]
            pub const RECEIPTS: &[ReceiptMetadata] = &[#(#receipts),*];
            #[allow(dead_code)]
            pub const HANDOFFS: &[HandoffMetadata] = &[#(#handoffs),*];

            #[must_use]
            pub fn authoritative_binding(name: &str) -> Option<&'static AuthorityReadMetadata> {
                AUTHORITATIVE_READS.iter().find(|entry| entry.binding_name == name)
            }

            #[must_use]
            pub fn observed_binding(name: &str) -> Option<&'static AuthorityReadMetadata> {
                OBSERVED_READS.iter().find(|entry| entry.binding_name == name)
            }

            #[must_use]
            pub fn publication(name: &str) -> Option<&'static PublicationMetadata> {
                PUBLICATIONS.iter().find(|entry| entry.publication_name == name)
            }

            #[must_use]
            pub fn materialization(name: &str) -> Option<&'static MaterializationMetadata> {
                MATERIALIZATIONS.iter().find(|entry| entry.proof_name == name)
            }

            #[must_use]
            pub fn canonical_handle(name: &str) -> Option<&'static CanonicalHandleMetadata> {
                CANONICAL_HANDLES.iter().find(|entry| entry.proof_name == name)
            }

            #[must_use]
            pub fn receipt(name: &str) -> Option<&'static ReceiptMetadata> {
                RECEIPTS.iter().find(|entry| entry.binding_name == name)
            }

            #[must_use]
            pub fn handoff(operation: &str) -> Option<&'static HandoffMetadata> {
                HANDOFFS.iter().find(|entry| entry.operation_name == operation)
            }
        }
    })
}

fn collect_authority_surfaces(protocol: &Protocol, collector: &mut AuthoritySurfaceCollector) {
    match protocol {
        Protocol::Begin { continuation, .. }
        | Protocol::Await { continuation, .. }
        | Protocol::Resolve { continuation, .. }
        | Protocol::Invalidate { continuation, .. }
        | Protocol::Publish { continuation, .. }
        | Protocol::Extension { continuation, .. }
        | Protocol::DependentWork { continuation, .. } => {
            collect_authority_surfaces(continuation, collector);
        }
        Protocol::Let {
            name,
            mode,
            expr,
            continuation,
            ..
        } => {
            match (mode, expr) {
                (
                    AuthorityBindingMode::Authoritative,
                    AuthorityExpr::Check {
                        effect, operation, ..
                    },
                ) => {
                    collector
                        .authoritative_reads
                        .insert(name.clone(), (effect.clone(), operation.clone()));
                }
                (
                    AuthorityBindingMode::Observe,
                    AuthorityExpr::Observe {
                        effect, operation, ..
                    },
                ) => {
                    collector
                        .observed_reads
                        .insert(name.clone(), (effect.clone(), operation.clone()));
                }
                (AuthorityBindingMode::Plain, AuthorityExpr::Transfer { subject, from, to }) => {
                    collector.receipts.insert(
                        name.clone(),
                        (
                            subject.trim().to_string(),
                            from.trim().to_string(),
                            to.trim().to_string(),
                        ),
                    );
                }
                _ => {}
            }
            collect_authority_surfaces(continuation, collector);
        }
        Protocol::PublishAuthority {
            witness,
            publication_name,
            continuation,
        } => {
            collector
                .publications
                .insert(publication_name.clone(), witness.clone());
            collect_authority_surfaces(continuation, collector);
        }
        Protocol::Materialize {
            proof,
            publication,
            continuation,
        } => {
            collector
                .materializations
                .insert(proof.clone(), publication.clone());
            collect_authority_surfaces(continuation, collector);
        }
        Protocol::Handoff {
            operation,
            target,
            receipt,
            continuation,
        } => {
            collector.handoffs.insert(
                operation.clone(),
                (target.name().to_string(), receipt.clone()),
            );
            collect_authority_surfaces(continuation, collector);
        }
        Protocol::Send { continuation, .. } | Protocol::Broadcast { continuation, .. } => {
            collect_authority_surfaces(continuation, collector);
        }
        Protocol::Choice { branches, .. } => {
            for branch in branches {
                collect_authority_surfaces(&branch.protocol, collector);
            }
        }
        Protocol::Case { branches, .. } => {
            for branch in branches {
                collect_authority_surfaces(&branch.protocol, collector);
            }
        }
        Protocol::Timeout {
            body,
            on_timeout,
            on_cancel,
            ..
        } => {
            collect_authority_surfaces(body, collector);
            collect_authority_surfaces(on_timeout, collector);
            if let Some(on_cancel) = on_cancel {
                collect_authority_surfaces(on_cancel, collector);
            }
        }
        Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => {
            collect_authority_surfaces(body, collector);
        }
        Protocol::Parallel { protocols } => {
            for protocol in protocols {
                collect_authority_surfaces(protocol, collector);
            }
        }
        Protocol::Var(_) | Protocol::End => {}
    }
}

fn generate_commitments_module(choreography: &Choreography) -> Result<TokenStream> {
    let entries = choreography
        .operation_declarations()
        .iter()
        .map(generate_commitment_metadata)
        .collect::<Result<Vec<_>>>()?;

    Ok(quote! {
        pub mod commitments {
            pub use ::telltale::dsl::semantic::{
                OperationInstance,
                OperationPhase,
                ProgressContract,
                ProgressState,
            };

            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub struct ProgressMetadata {
                pub contract_name: &'static str,
                pub requires_profile: Option<&'static str>,
                pub within_window: Option<&'static str>,
                pub on_timeout: Option<&'static str>,
                pub on_stall: Option<&'static str>,
            }

            impl ProgressMetadata {
                #[must_use]
                pub const fn is_bounded(&self) -> bool {
                    self.within_window.is_some()
                }
            }

            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub struct CommitmentMetadata {
                pub operation_name: &'static str,
                pub owner_role: &'static str,
                pub region: Option<&'static str>,
                pub progress: ProgressMetadata,
            }

            impl CommitmentMetadata {
                #[must_use]
                pub fn operation_instance(
                    &self,
                    operation_id: impl Into<::std::string::String>,
                ) -> OperationInstance {
                    OperationInstance {
                        operation_id: operation_id.into(),
                        session: None,
                        owner_id: None,
                        kind: self.operation_name.to_string(),
                        phase: OperationPhase::Pending,
                        handler_identity: None,
                        effect_ids: ::std::vec::Vec::new(),
                        dependent_operation_ids: ::std::vec::Vec::new(),
                        terminal_publication: None,
                        budget_ticks: None,
                        requires_proof: true,
                    }
                }

                #[must_use]
                pub fn progress_contract(
                    &self,
                    operation_id: impl Into<::std::string::String>,
                ) -> ProgressContract {
                    ProgressContract {
                        operation_id: operation_id.into(),
                        session: None,
                        state: ProgressState::Pending,
                        last_ordering_key: None,
                        bounded: self.progress.is_bounded(),
                        budget_ticks: None,
                        last_progress_tick: None,
                        escalated_at_tick: None,
                        reason: None,
                    }
                }
            }

            #[allow(dead_code)]
            pub const OPERATIONS: &[CommitmentMetadata] = &[#(#entries),*];

            #[must_use]
            pub fn operation(name: &str) -> Option<&'static CommitmentMetadata> {
                OPERATIONS.iter().find(|entry| entry.operation_name == name)
            }
        }
    })
}

fn generate_commitment_metadata(operation: &OperationDeclaration) -> Result<TokenStream> {
    let Some(progress) = operation.progress_contract.as_ref() else {
        return Err(Error::new(
            Span::call_site(),
            format!(
                "operation `{}` is missing explicit progress metadata",
                operation.name
            ),
        ));
    };

    let operation_name = LitStr::new(&operation.name, Span::call_site());
    let owner_role = LitStr::new(&operation.owner_role, Span::call_site());
    let region = operation.within.as_deref().map_or_else(
        || quote!(::std::option::Option::None),
        |value| {
            let value = LitStr::new(value, Span::call_site());
            quote!(::std::option::Option::Some(#value))
        },
    );
    let contract_name = LitStr::new(&progress.contract_name, Span::call_site());
    let requires_profile = progress.requires_profile.as_deref().map_or_else(
        || quote!(::std::option::Option::None),
        |value| {
            let value = LitStr::new(value, Span::call_site());
            quote!(::std::option::Option::Some(#value))
        },
    );
    let within_window = progress.within_window.as_deref().map_or_else(
        || quote!(::std::option::Option::None),
        |value| {
            let value = LitStr::new(value, Span::call_site());
            quote!(::std::option::Option::Some(#value))
        },
    );
    let on_timeout = progress.on_timeout.as_deref().map_or_else(
        || quote!(::std::option::Option::None),
        |value| {
            let value = LitStr::new(value, Span::call_site());
            quote!(::std::option::Option::Some(#value))
        },
    );
    let on_stall = progress.on_stall.as_deref().map_or_else(
        || quote!(::std::option::Option::None),
        |value| {
            let value = LitStr::new(value, Span::call_site());
            quote!(::std::option::Option::Some(#value))
        },
    );

    Ok(quote! {
        CommitmentMetadata {
            operation_name: #operation_name,
            owner_role: #owner_role,
            region: #region,
            progress: ProgressMetadata {
                contract_name: #contract_name,
                requires_profile: #requires_profile,
                within_window: #within_window,
                on_timeout: #on_timeout,
                on_stall: #on_stall,
            },
        }
    })
}

fn generate_agreements_module(choreography: &Choreography) -> Result<TokenStream> {
    let profile_entries = choreography
        .agreement_profile_declarations()
        .iter()
        .map(generate_agreement_profile_metadata)
        .collect::<Result<Vec<_>>>()?;
    let operation_entries = choreography
        .operation_declarations()
        .iter()
        .filter(|operation| operation.agreement.is_some())
        .map(|operation| generate_operation_agreement_metadata(choreography, operation))
        .collect::<Result<Vec<_>>>()?;

    Ok(quote! {
        pub mod agreements {
            pub use ::telltale::dsl::semantic::{
                AgreementContract,
                AgreementEvidenceKind,
                AgreementLevel,
                AgreementProfile,
                AgreementRule,
                EffectCompositionPolicy,
                OperationVisibility,
                PrestateBinding,
            };

            #[derive(Clone, Copy, Debug, PartialEq, Eq)]
            pub struct AgreementProfileMetadata {
                pub profile_name: &'static str,
                pub visibility: OperationVisibility,
                pub rule_name: &'static str,
                pub usable_at: AgreementLevel,
                pub finalized_at: AgreementLevel,
                pub required_evidence_kind: AgreementEvidenceKind,
            }

            impl AgreementProfileMetadata {
                #[must_use]
                pub fn agreement_rule(&self) -> AgreementRule {
                    match self.rule_name {
                        "no_agreement" => AgreementRule::NoAgreement,
                        "any_participant" => AgreementRule::AnyParticipant,
                        "unanimous" => AgreementRule::Unanimous,
                        other => AgreementRule::Named {
                            rule_name: other.to_string(),
                        },
                    }
                }

                #[must_use]
                pub fn agreement_profile(&self) -> AgreementProfile {
                    AgreementProfile {
                        profile_name: self.profile_name.to_string(),
                        visibility: self.visibility,
                        rule: self.agreement_rule(),
                        usable_at: self.usable_at,
                        finalized_at: self.finalized_at,
                        required_evidence_kind: self.required_evidence_kind,
                    }
                }
            }

            #[derive(Clone, Debug, PartialEq, Eq)]
            pub struct OperationAgreementMetadata {
                pub operation_name: &'static str,
                pub profile_name: &'static str,
                pub prestate: Option<&'static str>,
                pub child_effect_aggregation: Option<EffectCompositionPolicy>,
                pub visibility: OperationVisibility,
                pub rule_name: &'static str,
                pub usable_at: AgreementLevel,
                pub finalized_at: AgreementLevel,
                pub required_evidence_kind: AgreementEvidenceKind,
            }

            impl OperationAgreementMetadata {
                #[must_use]
                pub fn agreement_rule(&self) -> AgreementRule {
                    match self.rule_name {
                        "no_agreement" => AgreementRule::NoAgreement,
                        "any_participant" => AgreementRule::AnyParticipant,
                        "unanimous" => AgreementRule::Unanimous,
                        other => AgreementRule::Named {
                            rule_name: other.to_string(),
                        },
                    }
                }

                #[must_use]
                pub fn agreement_contract(
                    &self,
                    operation_id: impl Into<::std::string::String>,
                ) -> AgreementContract {
                    AgreementContract {
                        contract_name: format!("agreement:{}", self.operation_name),
                        operation_id: operation_id.into(),
                        session: None,
                        owner_id: None,
                        profile_name: Some(self.profile_name.to_string()),
                        visibility: self.visibility,
                        rule: self.agreement_rule(),
                        usable_at: self.usable_at,
                        finalized_at: self.finalized_at,
                        required_evidence_kind: self.required_evidence_kind,
                    }
                }

                #[must_use]
                pub fn prestate_binding(
                    &self,
                    operation_id: impl Into<::std::string::String>,
                    state_digest: impl Into<::std::string::String>,
                ) -> Option<PrestateBinding> {
                    self.prestate.map(|prestate| {
                        let operation_id = operation_id.into();
                        PrestateBinding {
                            binding_id: format!("prestate:{operation_id}"),
                            operation_id,
                            session: None,
                            state_digest: state_digest.into(),
                            epoch_ref: Some(prestate.to_string()),
                            participant_digest: None,
                        }
                    })
                }
            }

            #[allow(dead_code)]
            pub const PROFILES: &[AgreementProfileMetadata] = &[#(#profile_entries),*];

            #[allow(dead_code)]
            pub const OPERATIONS: &[OperationAgreementMetadata] = &[#(#operation_entries),*];

            #[must_use]
            pub fn profile(name: &str) -> Option<&'static AgreementProfileMetadata> {
                PROFILES.iter().find(|entry| entry.profile_name == name)
            }

            #[must_use]
            pub fn operation(name: &str) -> Option<&'static OperationAgreementMetadata> {
                OPERATIONS.iter().find(|entry| entry.operation_name == name)
            }
        }
    })
}

fn generate_agreement_profile_metadata(
    profile: &AgreementProfileDeclaration,
) -> Result<TokenStream> {
    let profile_name = LitStr::new(&profile.name, Span::call_site());
    let visibility = lower_operation_visibility(&profile.visibility)?;
    let rule_name = LitStr::new(&profile.rule, Span::call_site());
    let usable_at = lower_agreement_level(&profile.usable_at)?;
    let finalized_at = lower_agreement_level(&profile.finalized_at)?;
    let required_evidence_kind = lower_agreement_evidence_kind(&profile.evidence)?;

    Ok(quote! {
        AgreementProfileMetadata {
            profile_name: #profile_name,
            visibility: #visibility,
            rule_name: #rule_name,
            usable_at: #usable_at,
            finalized_at: #finalized_at,
            required_evidence_kind: #required_evidence_kind,
        }
    })
}

fn generate_operation_agreement_metadata(
    choreography: &Choreography,
    operation: &OperationDeclaration,
) -> Result<TokenStream> {
    let attachment = operation.agreement.as_ref().ok_or_else(|| {
        Error::new(
            Span::call_site(),
            format!(
                "operation `{}` is missing a named agreement attachment",
                operation.name
            ),
        )
    })?;
    let operation_name = LitStr::new(&operation.name, Span::call_site());
    let profile_name = LitStr::new(&attachment.profile_name, Span::call_site());
    let prestate = attachment.prestate.as_deref().map_or_else(
        || quote!(::std::option::Option::None),
        |value| {
            let value = LitStr::new(value, Span::call_site());
            quote!(::std::option::Option::Some(#value))
        },
    );
    let child_effect_aggregation = operation
        .child_effect_aggregation
        .as_ref()
        .map(|aggregation| lower_child_effect_aggregation_policy(&aggregation.policy))
        .transpose()?
        .map_or_else(
            || quote!(::std::option::Option::None),
            |value| quote!(::std::option::Option::Some(#value)),
        );

    let profile_decl = choreography_profile_for_operation(
        choreography,
        operation,
        attachment.profile_name.as_str(),
    )?;
    let visibility = lower_operation_visibility(&profile_decl.visibility)?;
    let rule_name = LitStr::new(&profile_decl.rule, Span::call_site());
    let usable_at = lower_agreement_level(&profile_decl.usable_at)?;
    let finalized_at = lower_agreement_level(&profile_decl.finalized_at)?;
    let required_evidence_kind = lower_agreement_evidence_kind(&profile_decl.evidence)?;

    Ok(quote! {
        OperationAgreementMetadata {
            operation_name: #operation_name,
            profile_name: #profile_name,
            prestate: #prestate,
            child_effect_aggregation: #child_effect_aggregation,
            visibility: #visibility,
            rule_name: #rule_name,
            usable_at: #usable_at,
            finalized_at: #finalized_at,
            required_evidence_kind: #required_evidence_kind,
        }
    })
}

fn choreography_profile_for_operation(
    choreography: &Choreography,
    operation: &OperationDeclaration,
    profile_name: &str,
) -> Result<AgreementProfileDeclaration> {
    choreography
        .agreement_profile_declarations()
        .iter()
        .find(|profile| profile.name == profile_name)
        .cloned()
        .ok_or_else(|| {
            Error::new(
                Span::call_site(),
                format!(
                    "operation `{}` references unknown agreement profile `{profile_name}`",
                    operation.name
                ),
            )
        })
}

fn lower_operation_visibility(value: &str) -> Result<TokenStream> {
    match value {
        "immediate" => Ok(quote!(OperationVisibility::Immediate)),
        "pending" => Ok(quote!(OperationVisibility::Pending)),
        "blocked_until_finalized" => Ok(quote!(OperationVisibility::BlockedUntilFinalized)),
        other => Err(Error::new(
            Span::call_site(),
            format!(
                "unsupported agreement visibility `{other}`; use `immediate`, `pending`, or `blocked_until_finalized`"
            ),
        )),
    }
}

fn lower_agreement_level(value: &str) -> Result<TokenStream> {
    match value {
        "none" => Ok(quote!(AgreementLevel::None)),
        "provisional" => Ok(quote!(AgreementLevel::Provisional)),
        "soft_safe" => Ok(quote!(AgreementLevel::SoftSafe)),
        "finalized" => Ok(quote!(AgreementLevel::Finalized)),
        other => Err(Error::new(
            Span::call_site(),
            format!(
                "unsupported agreement level `{other}`; use `none`, `provisional`, `soft_safe`, or `finalized`"
            ),
        )),
    }
}

fn lower_agreement_evidence_kind(value: &str) -> Result<TokenStream> {
    match value {
        "witness" => Ok(quote!(AgreementEvidenceKind::Witness)),
        "certificate" => Ok(quote!(AgreementEvidenceKind::Certificate)),
        "commit_fact" => Ok(quote!(AgreementEvidenceKind::CommitFact)),
        "publication" => Ok(quote!(AgreementEvidenceKind::Publication)),
        "materialization" => Ok(quote!(AgreementEvidenceKind::Materialization)),
        other => Err(Error::new(
            Span::call_site(),
            format!(
                "unsupported agreement evidence kind `{other}`; use `witness`, `certificate`, `commit_fact`, `publication`, or `materialization`"
            ),
        )),
    }
}

fn lower_child_effect_aggregation_policy(
    policy: &ChildEffectAggregationPolicy,
) -> Result<TokenStream> {
    Ok(match policy {
        ChildEffectAggregationPolicy::All => quote!(EffectCompositionPolicy::All),
        ChildEffectAggregationPolicy::First => quote!(EffectCompositionPolicy::First),
        ChildEffectAggregationPolicy::Threshold { required_successes } => {
            let required_successes = *required_successes;
            quote!(EffectCompositionPolicy::Threshold {
                required_successes: #required_successes
            })
        }
    })
}

fn lower_effect_authority_class(
    value: telltale_language::ast::EffectAuthorityClass,
) -> TokenStream {
    match value {
        telltale_language::ast::EffectAuthorityClass::Authoritative => {
            quote!(EffectAuthorityClass::Authoritative)
        }
        telltale_language::ast::EffectAuthorityClass::Command => {
            quote!(EffectAuthorityClass::Command)
        }
        telltale_language::ast::EffectAuthorityClass::Observe => {
            quote!(EffectAuthorityClass::Observe)
        }
    }
}

fn lower_effect_semantic_class(value: &str) -> Result<TokenStream> {
    match value {
        "authoritative" => Ok(quote!(EffectSemanticClass::Authoritative)),
        "observational" => Ok(quote!(EffectSemanticClass::Observational)),
        "best_effort" => Ok(quote!(EffectSemanticClass::BestEffort)),
        other => Err(Error::new(
            Span::call_site(),
            format!(
                "unsupported effect semantic class `{other}`; use `authoritative`, `observational`, or `best_effort`"
            ),
        )),
    }
}

fn lower_effect_agreement_use(value: &str) -> Result<TokenStream> {
    match value {
        "required" => Ok(quote!(EffectAgreementUse::Required)),
        "none" => Ok(quote!(EffectAgreementUse::None)),
        "forbidden" => Ok(quote!(EffectAgreementUse::Forbidden)),
        other => Err(Error::new(
            Span::call_site(),
            format!(
                "unsupported effect agreement_use `{other}`; use `required`, `none`, or `forbidden`"
            ),
        )),
    }
}

fn lower_effect_region_scope(value: &str) -> Result<TokenStream> {
    match value {
        "session" => Ok(quote!(EffectRegionScope::Session)),
        "fragment" => Ok(quote!(EffectRegionScope::Fragment)),
        "global" => Ok(quote!(EffectRegionScope::Global)),
        other => Err(Error::new(
            Span::call_site(),
            format!("unsupported effect region `{other}`; use `session`, `fragment`, or `global`"),
        )),
    }
}

fn lower_effect_admissibility(is_used: bool) -> TokenStream {
    if is_used {
        quote!(EffectAdmissibility::DeclaredUseOnly)
    } else {
        quote!(EffectAdmissibility::InternalOnly)
    }
}

fn lower_effect_totality(value: &str) -> Result<TokenStream> {
    match value {
        "immediate" => Ok(quote!(EffectTotality::Immediate)),
        "may_block" => Ok(quote!(EffectTotality::MayBlock)),
        other => Err(Error::new(
            Span::call_site(),
            format!("unsupported effect progress `{other}`; use `immediate` or `may_block`"),
        )),
    }
}

fn lower_effect_timeout_policy(value: &str) -> Result<TokenStream> {
    match value {
        "immediate" => Ok(quote!(EffectTimeoutPolicy::None)),
        "may_block" => Ok(quote!(EffectTimeoutPolicy::Required { budget_ticks: None })),
        other => Err(Error::new(
            Span::call_site(),
            format!("unsupported effect progress `{other}`; use `immediate` or `may_block`"),
        )),
    }
}

fn lower_effect_retry_shape() -> TokenStream {
    quote!(EffectRetryShape::Forbidden)
}

fn lower_effect_reentrancy_policy(value: &str) -> Result<TokenStream> {
    match value {
        "allow" => Ok(quote!(EffectReentrancyPolicy::Allow)),
        "reject_same_operation" => Ok(quote!(EffectReentrancyPolicy::RejectSameOperation)),
        "reject_same_fragment" => Ok(quote!(EffectReentrancyPolicy::RejectSameFragment)),
        other => Err(Error::new(
            Span::call_site(),
            format!(
                "unsupported effect reentrancy `{other}`; use `allow`, `reject_same_operation`, or `reject_same_fragment`"
            ),
        )),
    }
}

fn lower_effect_handler_domain(is_used: bool) -> TokenStream {
    if is_used {
        quote!(EffectHandlerDomain::External)
    } else {
        quote!(EffectHandlerDomain::Internal)
    }
}

fn generate_effect_request_variant(op: &EffectOperationDeclaration) -> Result<TokenStream> {
    let variant = format_ident!("{}", to_upper_camel_identifier(&op.name));
    let input = lower_dsl_type_expr(&parse_dsl_type_expr(&op.input_type)?, false)?;
    Ok(quote!(#variant(#input)))
}

fn generate_effect_outcome_variant(op: &EffectOperationDeclaration) -> Result<TokenStream> {
    let variant = format_ident!("{}", to_upper_camel_identifier(&op.name));
    let output = lower_dsl_type_expr(&parse_dsl_type_expr(&op.output_type)?, false)?;
    Ok(quote!(#variant(#output)))
}

fn generate_effect_method_signature(op: &EffectOperationDeclaration) -> Result<TokenStream> {
    let method = format_ident!("{}", to_snake_identifier(&op.name));
    let input = lower_dsl_type_expr(&parse_dsl_type_expr(&op.input_type)?, false)?;
    let output = lower_dsl_type_expr(&parse_dsl_type_expr(&op.output_type)?, false)?;
    Ok(quote! {
        fn #method(&mut self, input: #input) -> #output;
    })
}

fn generate_effect_handle_arm(
    op: &EffectOperationDeclaration,
    request_name: &Ident,
    outcome_name: &Ident,
) -> Result<TokenStream> {
    let variant = format_ident!("{}", to_upper_camel_identifier(&op.name));
    let method = format_ident!("{}", to_snake_identifier(&op.name));
    Ok(quote! {
        #request_name::#variant(input) => #outcome_name::#variant(self.#method(input))
    })
}

fn generate_effect_operation_metadata_entry(
    effect: &EffectInterfaceDeclaration,
    op: &EffectOperationDeclaration,
    is_used: bool,
) -> Result<TokenStream> {
    let const_name = format_ident!("{}", to_upper_snake_identifier(&op.name));
    let interface_name = LitStr::new(&effect.name, Span::call_site());
    let operation_name = LitStr::new(&op.name, Span::call_site());
    let authority_class = lower_effect_authority_class(op.authority_class);
    let semantic_class = lower_effect_semantic_class(&op.semantic_class)?;
    let agreement_use = lower_effect_agreement_use(&op.agreement_use)?;
    let region_scope = lower_effect_region_scope(&op.region)?;
    let admissibility = lower_effect_admissibility(is_used);
    let totality = lower_effect_totality(&op.progress)?;
    let timeout_policy = lower_effect_timeout_policy(&op.progress)?;
    let retry_shape = lower_effect_retry_shape();
    let reentrancy_policy = lower_effect_reentrancy_policy(&op.reentrancy)?;
    let handler_domain = lower_effect_handler_domain(is_used);
    Ok(quote! {
        pub const #const_name: EffectOperationMetadata = EffectOperationMetadata {
            interface_name: #interface_name,
            operation_name: #operation_name,
            authority_class: #authority_class,
            semantic_class: #semantic_class,
            agreement_use: #agreement_use,
            region_scope: #region_scope,
            admissibility: #admissibility,
            totality: #totality,
            timeout_policy: #timeout_policy,
            retry_shape: #retry_shape,
            reentrancy_policy: #reentrancy_policy,
            handler_domain: #handler_domain,
        };
    })
}

fn generate_effect_operation_lookup_entry(op: &EffectOperationDeclaration) -> TokenStream {
    let const_name = format_ident!("{}", to_upper_snake_identifier(&op.name));
    quote!(#const_name)
}

fn generate_effect_request_metadata_arm(
    op: &EffectOperationDeclaration,
    request_name: &Ident,
) -> TokenStream {
    let variant = format_ident!("{}", to_upper_camel_identifier(&op.name));
    let const_name = format_ident!("{}", to_upper_snake_identifier(&op.name));
    quote!(#request_name::#variant(_) => &#const_name)
}

fn lower_dsl_type_expr(ty: &DslTypeExpr, allow_inline_record: bool) -> Result<TokenStream> {
    match ty {
        DslTypeExpr::Path(path) => Ok(lower_dsl_type_path(path)),
        DslTypeExpr::Result(error_ty, ok_ty) => {
            let error_ty = lower_dsl_type_expr(error_ty, false)?;
            let ok_ty = lower_dsl_type_expr(ok_ty, false)?;
            Ok(quote!(::std::result::Result<#ok_ty, #error_ty>))
        }
        DslTypeExpr::Maybe(inner) => {
            let inner = lower_dsl_type_expr(inner, false)?;
            Ok(quote!(::std::option::Option<#inner>))
        }
        DslTypeExpr::Unit => Ok(quote!(())),
        DslTypeExpr::Record(_) if !allow_inline_record => Err(Error::new(
            Span::call_site(),
            "anonymous record types must be declared with `type alias` before they can be used in Rust surfaces",
        )),
        DslTypeExpr::Record(fields) => {
            let fields = fields
                .iter()
                .map(|field| {
                    let name = format_ident!("{}", to_snake_identifier(&field.name));
                    let ty = lower_dsl_type_expr(&field.ty, false)?;
                    Ok(quote!(#name: #ty))
                })
                .collect::<Result<Vec<_>>>()?;
            Ok(quote!({ #(#fields),* }))
        }
    }
}

fn lower_dsl_type_path(path: &[String]) -> TokenStream {
    let joined = path.join(".");
    match joined.as_str() {
        "Int" => quote!(i64),
        "Bool" => quote!(bool),
        "String" => quote!(::std::string::String),
        "Role" => quote!(::telltale::dsl::Role),
        "Session" => quote!(::telltale::dsl::Session),
        "PresenceView" => quote!(::telltale::dsl::PresenceView),
        "AuditEvent" => quote!(::telltale::dsl::AuditEvent),
        _ => {
            let segments = path
                .iter()
                .map(|segment| format_ident!("{}", segment))
                .collect::<Vec<_>>();
            let first = &segments[0];
            let rest = &segments[1..];
            quote!(#first #( :: #rest )*)
        }
    }
}

fn parse_dsl_type_expr(input: &str) -> Result<DslTypeExpr> {
    let tokens = tokenize_dsl_type(input)?;
    let mut cursor = TypeCursor { tokens, index: 0 };
    let expr = cursor.parse_type_expr()?;
    if cursor.peek().is_some() {
        return Err(Error::new(
            Span::call_site(),
            format!("unexpected trailing tokens in DSL type `{input}`"),
        ));
    }
    Ok(expr)
}

fn tokenize_dsl_type(input: &str) -> Result<Vec<TypeToken>> {
    let chars: Vec<char> = input.chars().collect();
    let mut index = 0;
    let mut tokens = Vec::new();
    while index < chars.len() {
        match chars[index] {
            '{' => {
                tokens.push(TypeToken::LBrace);
                index += 1;
            }
            '}' => {
                tokens.push(TypeToken::RBrace);
                index += 1;
            }
            ':' => {
                tokens.push(TypeToken::Colon);
                index += 1;
            }
            ',' => {
                tokens.push(TypeToken::Comma);
                index += 1;
            }
            ch if ch.is_whitespace() => {
                index += 1;
            }
            ch if ch.is_ascii_alphabetic() => {
                let start = index;
                index += 1;
                while index < chars.len()
                    && (chars[index].is_ascii_alphanumeric()
                        || chars[index] == '_'
                        || chars[index] == '.')
                {
                    index += 1;
                }
                tokens.push(TypeToken::Ident(chars[start..index].iter().collect()));
            }
            other => {
                return Err(Error::new(
                    Span::call_site(),
                    format!("unsupported token `{other}` in DSL type `{input}`"),
                ))
            }
        }
    }
    Ok(tokens)
}

struct TypeCursor {
    tokens: Vec<TypeToken>,
    index: usize,
}

impl TypeCursor {
    fn peek(&self) -> Option<&TypeToken> {
        self.tokens.get(self.index)
    }

    fn next(&mut self) -> Option<TypeToken> {
        let token = self.tokens.get(self.index).cloned();
        if token.is_some() {
            self.index += 1;
        }
        token
    }

    fn parse_type_expr(&mut self) -> Result<DslTypeExpr> {
        match self.next() {
            Some(TypeToken::LBrace) => self.parse_record(),
            Some(TypeToken::Ident(name)) if name == "Result" => {
                let error_ty = self.parse_type_expr()?;
                let ok_ty = self.parse_type_expr()?;
                Ok(DslTypeExpr::Result(Box::new(error_ty), Box::new(ok_ty)))
            }
            Some(TypeToken::Ident(name)) if name == "Maybe" => {
                let inner = self.parse_type_expr()?;
                Ok(DslTypeExpr::Maybe(Box::new(inner)))
            }
            Some(TypeToken::Ident(name)) if name == "Unit" => Ok(DslTypeExpr::Unit),
            Some(TypeToken::Ident(path)) => Ok(DslTypeExpr::Path(
                path.split('.').map(str::to_string).collect(),
            )),
            Some(other) => Err(Error::new(
                Span::call_site(),
                format!("unexpected token {:?} in DSL type", other),
            )),
            None => Err(Error::new(
                Span::call_site(),
                "unexpected end of DSL type expression",
            )),
        }
    }

    fn parse_record(&mut self) -> Result<DslTypeExpr> {
        let mut fields = Vec::new();
        loop {
            match self.peek() {
                Some(TypeToken::RBrace) => {
                    self.next();
                    break;
                }
                Some(TypeToken::Ident(_)) => {
                    let field_name = match self.next() {
                        Some(TypeToken::Ident(name)) => name,
                        _ => unreachable!(),
                    };
                    match self.next() {
                        Some(TypeToken::Colon) => {}
                        other => {
                            return Err(Error::new(
                                Span::call_site(),
                                format!(
                                    "expected `:` after record field `{field_name}`, got {other:?}"
                                ),
                            ))
                        }
                    }
                    let field_ty = self.parse_type_expr()?;
                    fields.push(DslRecordField {
                        name: field_name,
                        ty: field_ty,
                    });
                    if matches!(self.peek(), Some(TypeToken::Comma)) {
                        self.next();
                    }
                }
                other => {
                    return Err(Error::new(
                        Span::call_site(),
                        format!("unexpected token {:?} in record type", other),
                    ))
                }
            }
        }
        Ok(DslTypeExpr::Record(fields))
    }
}

fn generate_sessions_module(
    choreography: &Choreography,
    local_types: &[(Role, LocalType)],
) -> Result<TokenStream> {
    let role_structs = generate_role_structs(&choreography.roles);
    let helper_types = generate_helper_types(&choreography.protocol)?;
    let session_types = generate_session_types(local_types)?;
    let setup_fn = generate_setup_function(&choreography.name);

    Ok(quote! {
        pub mod sessions {
            use ::telltale::Role;

            #role_structs
            #helper_types
            #session_types
            #setup_fn
        }
    })
}

fn generate_role_structs(roles: &[Role]) -> TokenStream {
    let role_names: Vec<_> = roles.iter().map(|role| role.name()).collect();

    let role_structs = roles.iter().enumerate().map(|(index, role)| {
        let role_name = role.name();
        let route_fields: Vec<_> = roles
            .iter()
            .enumerate()
            .filter_map(|(other_index, other_role)| {
                if index == other_index {
                    None
                } else {
                    let other_name = other_role.name();
                    Some(quote! { #[route(#other_name)] pub Channel })
                }
            })
            .collect();

        if route_fields.is_empty() {
            quote! {
                #[derive(::telltale::Role)]
                #[message(Label)]
                #[allow(dead_code)]
                pub struct #role_name;
            }
        } else {
            quote! {
                #[derive(::telltale::Role)]
                #[message(Label)]
                #[allow(dead_code)]
                pub struct #role_name(#(#route_fields),*);
            }
        }
    });
    let public_role_names: Vec<_> = role_names
        .iter()
        .map(|role_name| quote!(pub #role_name))
        .collect();

    quote! {
        type Channel = ::telltale::channel::Bidirectional<
            ::telltale::futures::channel::mpsc::UnboundedSender<Label>,
            ::telltale::futures::channel::mpsc::UnboundedReceiver<Label>,
        >;

        #(#role_structs)*

        #[derive(::telltale::Roles)]
        #[allow(dead_code)]
        pub struct Roles(#(#public_role_names),*);
    }
}

#[derive(Clone)]
enum LabelSurface {
    Message {
        name: Ident,
        payload: Option<TokenStream>,
    },
    Choice {
        name: Ident,
    },
}

fn generate_helper_types(protocol: &Protocol) -> Result<TokenStream> {
    let mut labels = BTreeMap::<String, LabelSurface>::new();
    collect_label_surfaces(protocol, &mut labels)?;

    let mut label_variants = Vec::new();
    let mut helper_types = Vec::new();

    for surface in labels.into_values() {
        match surface {
            LabelSurface::Message { name, payload } => {
                if let Some(payload) = payload {
                    let public_payload = public_tuple_payload(&payload)?;
                    helper_types.push(quote! {
                        #[derive(Clone, Debug)]
                        #[allow(dead_code)]
                        pub struct #name #public_payload;
                    });
                } else {
                    helper_types.push(quote! {
                        #[derive(Clone, Debug)]
                        #[allow(dead_code)]
                        pub struct #name;
                    });
                }
                label_variants.push(quote! { #name(#name) });
            }
            LabelSurface::Choice { name } => {
                helper_types.push(quote! {
                    #[derive(Clone, Debug)]
                    #[allow(dead_code)]
                    pub struct #name;
                });
                label_variants.push(quote! { #name(#name) });
            }
        }
    }

    Ok(quote! {
        #(#helper_types)*

        #[derive(::telltale::Message)]
        #[allow(dead_code)]
        pub enum Label {
            #(#label_variants),*
        }
    })
}

fn public_tuple_payload(payload: &TokenStream) -> Result<TokenStream> {
    let mut tokens = payload.clone().into_iter();
    let Some(TokenTree::Group(group)) = tokens.next() else {
        return Err(Error::new(
            Span::call_site(),
            "message payload did not parse as a tuple payload group",
        ));
    };
    if tokens.next().is_some() || group.delimiter() != TokenDelimiter::Parenthesis {
        return Err(Error::new(
            Span::call_site(),
            "message payload did not parse as a parenthesized tuple payload",
        ));
    }

    let inner = group.stream();
    let mut public_group = Group::new(TokenDelimiter::Parenthesis, quote!(pub #inner));
    public_group.set_span(group.span());
    Ok(TokenStream::from(TokenTree::Group(public_group)))
}

fn to_snake_identifier(input: &str) -> String {
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

fn to_upper_camel_identifier(input: &str) -> String {
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

fn to_upper_snake_identifier(input: &str) -> String {
    to_snake_identifier(input).to_ascii_uppercase()
}

fn collect_label_surfaces(
    protocol: &Protocol,
    labels: &mut BTreeMap<String, LabelSurface>,
) -> Result<()> {
    match protocol {
        Protocol::Begin { continuation, .. }
        | Protocol::Await { continuation, .. }
        | Protocol::Resolve { continuation, .. }
        | Protocol::Invalidate { continuation, .. } => {
            collect_label_surfaces(continuation, labels)?;
        }
        Protocol::Send {
            message,
            continuation,
            ..
        } => {
            insert_message_surface(labels, message)?;
            collect_label_surfaces(continuation, labels)?;
        }
        Protocol::Broadcast {
            message,
            continuation,
            ..
        } => {
            insert_message_surface(labels, message)?;
            collect_label_surfaces(continuation, labels)?;
        }
        Protocol::Choice { branches, .. } => {
            collect_choice_surfaces(branches, labels)?;
        }
        Protocol::Case { branches, .. } => {
            for branch in branches {
                collect_label_surfaces(&branch.protocol, labels)?;
            }
        }
        Protocol::Timeout {
            body,
            on_timeout,
            on_cancel,
            ..
        } => {
            collect_label_surfaces(body, labels)?;
            collect_label_surfaces(on_timeout, labels)?;
            if let Some(on_cancel) = on_cancel {
                collect_label_surfaces(on_cancel, labels)?;
            }
        }
        Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => {
            collect_label_surfaces(body, labels)?;
        }
        Protocol::Parallel { protocols } => {
            for protocol in protocols {
                collect_label_surfaces(protocol, labels)?;
            }
        }
        Protocol::Let { continuation, .. }
        | Protocol::Publish { continuation, .. }
        | Protocol::PublishAuthority { continuation, .. }
        | Protocol::Materialize { continuation, .. }
        | Protocol::DependentWork { continuation, .. }
        | Protocol::Extension { continuation, .. } => {
            collect_label_surfaces(continuation, labels)?;
        }
        Protocol::Handoff { continuation, .. } => {
            collect_label_surfaces(continuation, labels)?;
        }
        Protocol::Var(_) | Protocol::End => {}
    }

    Ok(())
}

fn collect_choice_surfaces(
    branches: &[Branch],
    labels: &mut BTreeMap<String, LabelSurface>,
) -> Result<()> {
    for branch in branches {
        let key = branch.label.to_string();
        match labels.get(&key) {
            // When a message with the same name already exists, the choice
            // label reuses the message struct (the payload carries the label).
            Some(LabelSurface::Message { .. }) => {}
            Some(LabelSurface::Choice { .. }) | None => {
                labels.entry(key).or_insert_with(|| LabelSurface::Choice {
                    name: branch.label.clone(),
                });
            }
        }
        collect_label_surfaces(&branch.protocol, labels)?;
    }

    Ok(())
}

fn insert_message_surface(
    labels: &mut BTreeMap<String, LabelSurface>,
    message: &MessageType,
) -> Result<()> {
    let key = message.name.to_string();
    let payload = message.payload.clone();
    match labels.get(&key) {
        Some(LabelSurface::Message {
            payload: existing_payload,
            ..
        }) => {
            let existing = existing_payload
                .as_ref()
                .map(ToString::to_string)
                .unwrap_or_else(|| "<none>".to_string());
            let next = payload
                .as_ref()
                .map(ToString::to_string)
                .unwrap_or_else(|| "<none>".to_string());
            if existing != next {
                return Err(Error::new(
                    message.name.span(),
                    format!(
                        "message '{}' is used with conflicting payload types in the same protocol",
                        key
                    ),
                ));
            }
        }
        Some(LabelSurface::Choice { .. }) => {
            // Promote the choice label to a message — the payload-carrying
            // message struct doubles as the choice dispatch label.
            labels.insert(
                key,
                LabelSurface::Message {
                    name: message.name.clone(),
                    payload,
                },
            );
        }
        None => {
            labels.insert(
                key,
                LabelSurface::Message {
                    name: message.name.clone(),
                    payload,
                },
            );
        }
    }

    Ok(())
}

fn generate_session_types(local_types: &[(Role, LocalType)]) -> Result<TokenStream> {
    let mut output = TokenStream::new();

    for (role, local_type) in local_types {
        let mut state = ChoiceCodegenState::new(role.name().clone());
        let session_body = state.render_local_type(local_type)?;
        let session_name = format_ident!("{}Session", role.name());
        let choice_defs = state.choice_defs;

        output.extend(quote! {
            #(#choice_defs)*

            #[::telltale::session]
            pub type #session_name = #session_body;
        });
    }

    Ok(output)
}

struct ChoiceCodegenState {
    role_name: Ident,
    next_choice_id: usize,
    choice_defs: Vec<TokenStream>,
    /// Maps `rec` labels to the session-type token streams they produce.
    /// Populated when entering a `Rec` node so that inner `Var`
    /// references resolve to e.g. `Select<Peer, Enum>` or
    /// `Branch<Peer, Enum>`.
    rec_labels: HashMap<String, TokenStream>,
}

impl ChoiceCodegenState {
    fn new(role_name: Ident) -> Self {
        Self {
            role_name,
            next_choice_id: 0,
            choice_defs: Vec::new(),
            rec_labels: HashMap::new(),
        }
    }

    fn render_local_type(&mut self, local_type: &LocalType) -> Result<TokenStream> {
        match local_type {
            LocalType::Send {
                to,
                message,
                continuation,
            } => {
                let continuation = self.render_local_type(continuation)?;
                let to_name = to.name();
                let message_name = &message.name;
                Ok(quote! { ::telltale::Send<#to_name, #message_name, #continuation> })
            }
            LocalType::Receive {
                from,
                message,
                continuation,
            } => {
                let continuation = self.render_local_type(continuation)?;
                let from_name = from.name();
                let message_name = &message.name;
                Ok(quote! { ::telltale::Receive<#from_name, #message_name, #continuation> })
            }
            LocalType::Select { to, branches } => {
                let enum_name = self.push_choice_enum(branches)?;
                let to_name = to.name();
                Ok(quote! { ::telltale::Select<#to_name, #enum_name> })
            }
            LocalType::Branch { from, branches } => {
                let enum_name = self.push_choice_enum(branches)?;
                let from_name = from.name();
                Ok(quote! { ::telltale::Branch<#from_name, #enum_name> })
            }
            LocalType::End => Ok(quote! { ::telltale::End }),
            LocalType::Rec { label, body } => {
                // Pre-register the session type that the body will
                // produce, so that inner `Var` references resolve to
                // `Select<Peer, Enum>` or `Branch<Peer, Enum>` rather
                // than a bare enum name.
                let predicted_id = self.next_choice_id + 1;
                let predicted_name = format_ident!("{}Choice{}", self.role_name, predicted_id);
                let predicted_tokens = match body.as_ref() {
                    LocalType::Select { to, .. } => {
                        let to_name = to.name();
                        quote! { ::telltale::Select<#to_name, #predicted_name> }
                    }
                    LocalType::Branch { from, .. } => {
                        let from_name = from.name();
                        quote! { ::telltale::Branch<#from_name, #predicted_name> }
                    }
                    _ => predicted_name.to_token_stream(),
                };
                self.rec_labels.insert(label.to_string(), predicted_tokens);
                self.render_local_type(body)
            }
            LocalType::Var(label) => {
                if let Some(tokens) = self.rec_labels.get(&label.to_string()) {
                    Ok(tokens.clone())
                } else {
                    Ok(label.to_token_stream())
                }
            }
            LocalType::Loop { body, .. } => {
                // Bounded/unbounded loops lower to their body. The runtime
                // controls iteration; the session type describes one pass.
                self.render_local_type(body)
            }
            LocalType::LocalChoice { branches } => {
                // Local decisions without communication still need a choice
                // enum so the implementation can branch.  We generate a
                // `Select`-style enum without a partner role; the runtime
                // dispatcher uses it structurally.
                let enum_name = self.push_choice_enum(branches)?;
                Ok(quote! { ::telltale::Select<Self, #enum_name> })
            }
            LocalType::Timeout { body, .. } => {
                // Timeout is a runtime concern. The session type for the
                // happy path is the body; timeout/cancel paths are handled
                // by the handler at runtime.
                self.render_local_type(body)
            }
        }
    }

    fn push_choice_enum(&mut self, branches: &[(Ident, LocalType)]) -> Result<Ident> {
        self.next_choice_id += 1;
        let enum_name = format_ident!("{}Choice{}", self.role_name, self.next_choice_id);
        let variants: Vec<_> = branches
            .iter()
            .map(|(label, local_type)| {
                let continuation = self.render_local_type(local_type)?;
                Ok(quote! { #label(#label, #continuation) })
            })
            .collect::<Result<Vec<_>>>()?;

        self.choice_defs.push(quote! {
            #[::telltale::session]
            pub enum #enum_name {
                #(#variants),*
            }
        });

        Ok(enum_name)
    }
}

fn generate_setup_function(protocol_name: &Ident) -> TokenStream {
    quote! {
        #[doc = concat!("Setup function for the ", stringify!(#protocol_name), " protocol.")]
        pub fn setup() -> Roles {
            Roles::default()
        }
    }
}
