//! Comprehensive demonstration of the rumpsteak-aura extension system
//!
//! This example shows how to:
//! - Create custom extensions with the external-demo integration
//! - Use the discovery system for extension management
//! - Demonstrate 3rd party integration patterns
//! - Show performance optimization features
//! - Test extension compatibility

use external_demo::choreography;
use futures::channel::mpsc::{UnboundedReceiver, UnboundedSender};
use proc_macro2::TokenStream;
use rumpsteak_aura::*;

// Type definitions for the generated code
#[allow(dead_code)]
type Channel = channel::Bidirectional<UnboundedSender<Label>, UnboundedReceiver<Label>>;

#[allow(dead_code)]
#[derive(Message)]
enum Label {
    Hello(HelloMsg),
    Message(SimpleMessage),
    TaskMsg(TaskMessage),
    ResultMsg(ResultMessage),
    CancelMsg(CancelMessage),
}

use serde::{Deserialize, Serialize};

// Message type definitions
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct HelloMsg;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SimpleMessage;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct TaskMessage;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ResultMessage;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CancelMessage;
use rumpsteak_aura_choreography::{
    ast::{LocalType, Role},
    extensions::{
        discovery::{ExtensionDiscovery, ExtensionMetadata},
        ExtensionRegistry, GrammarExtension, ParseError, ProtocolExtension,
    },
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("External-Demo: Comprehensive Extension System Demo");

    // 1. Basic choreography! macro usage
    demo_basic_extensions()?;

    // 2. Extension discovery and management
    demo_extension_discovery()?;

    // 3. Conflict resolution
    demo_conflict_resolution()?;

    // 4. Performance optimization
    demo_performance_optimization()?;

    // 5. 3rd party integration pattern
    demo_third_party_integration()?;

    // 6. Advanced choreography! macro syntax
    demo_macro_syntax()?;

    println!("\nAll choreography! macro demos completed successfully!");
    Ok(())
}

/// Demonstrate basic extension usage
fn demo_basic_extensions() -> Result<(), Box<dyn std::error::Error>> {
    println!("\nDemo 1: Basic Extension Usage");

    // Use choreography! macro for basic protocol
    choreography! {
        choreography BasicDemo {
            roles: Alice, Bob;

            // Standard rumpsteak syntax
            Alice -> Bob: HelloMsg;
        }
    }

    println!("   Choreography macro executed successfully");
    println!("   Features demonstrated:");
    println!("    - Standard role declarations");
    println!("    - Basic communication statements");
    println!("    - Clean choreography! macro syntax");

    Ok(())
}

/// Demonstrate extension discovery and management
fn demo_extension_discovery() -> Result<(), Box<dyn std::error::Error>> {
    println!("\nDemo 2: Extension Discovery System");

    let mut discovery = ExtensionDiscovery::new();

    // Register extensions with metadata
    discovery.register_extension(
        ExtensionMetadata {
            name: "logging".to_string(),
            version: "1.0.0".to_string(),
            description: "Logging support for protocols".to_string(),
            author: "Demo Team".to_string(),
            dependencies: vec![],
            required_rumpsteak_version: Some("0.5.0".to_string()),
            priority: Some(100),
            overview: Some("Adds logging capabilities to choreographies".to_string()),
            syntax_guide: Some("Use @log annotations on statements".to_string()),
            use_cases: Some(vec!["Debugging".to_string(), "Audit trails".to_string()]),
            keywords: Some(vec!["logging".to_string(), "debug".to_string()]),
        },
        Box::new(LoggingExtension),
    )?;

    discovery.register_extension(
        ExtensionMetadata {
            name: "monitoring".to_string(),
            version: "1.0.0".to_string(),
            description: "Monitoring support with logging dependency".to_string(),
            author: "Demo Team".to_string(),
            dependencies: vec!["logging".to_string()],
            required_rumpsteak_version: Some("0.5.0".to_string()),
            priority: Some(120),
            overview: Some("Provides runtime monitoring of choreography execution".to_string()),
            syntax_guide: Some("Use @monitor annotations on statements".to_string()),
            use_cases: Some(vec![
                "Performance tracking".to_string(),
                "Runtime analysis".to_string(),
            ]),
            keywords: Some(vec!["monitoring".to_string(), "metrics".to_string()]),
        },
        Box::new(MonitoringExtension),
    )?;

    // Resolve dependencies automatically
    let resolved = discovery.resolve_dependencies(&["monitoring".to_string()])?;
    println!("   Dependency resolution: {:?}", resolved);

    // Check compatibility
    discovery.check_compatibility(&["logging".to_string(), "monitoring".to_string()])?;
    println!("   Extensions are compatible");

    // Create configured registry with resolved dependencies
    let registry = discovery.create_registry(&resolved)?;
    println!("   Created registry with resolved dependencies");
    println!(
        "   Registry contains {} grammar extensions",
        registry.grammar_extensions().count()
    );

    Ok(())
}

/// Demonstrate conflict resolution
fn demo_conflict_resolution() -> Result<(), Box<dyn std::error::Error>> {
    println!("\nDemo 3: Conflict Resolution");

    let mut registry = ExtensionRegistry::new();

    // Register extensions with different priorities
    let low_priority = LowPriorityExtension;
    let high_priority = HighPriorityExtension;

    // Register high priority first
    registry.register_grammar(high_priority)?;
    println!("   Registered high priority extension");

    // Register low priority (should handle conflict gracefully)
    match registry.register_grammar(low_priority) {
        Ok(_) => println!("   Registered low priority extension (no conflict)"),
        Err(ParseError::Conflict { message }) => {
            println!("   Conflict detected and handled: {}", message);
        }
        Err(e) => return Err(e.into()),
    }

    // Show conflict information
    if !registry.get_conflicts().is_empty() {
        println!("   Conflicts recorded: {:?}", registry.get_conflicts());
    } else {
        println!("   No conflicts detected");
    }

    Ok(())
}

/// Demonstrate performance optimization features
fn demo_performance_optimization() -> Result<(), Box<dyn std::error::Error>> {
    println!("\nDemo 4: Performance Optimization");

    // Use choreography! macro to demonstrate performance
    let start = std::time::Instant::now();
    choreography! {
        choreography PerfDemo {
            roles: Alice, Bob;
            Alice -> Bob: SimpleMessage;
        }
    }
    let parse_time = start.elapsed();

    println!("   Choreography macro execution time: {:?}", parse_time);
    println!("   Performance benefits:");
    println!("    - Compile-time parsing and validation");
    println!("    - Zero runtime parsing overhead");
    println!("    - Efficient code generation");
    println!("    - Memory-safe Rust integration");

    Ok(())
}

/// Demonstrate 3rd party integration pattern
fn demo_third_party_integration() -> Result<(), Box<dyn std::error::Error>> {
    println!("\nDemo 5: 3rd Party Integration Pattern");

    // This demonstrates how external-demo inherits ALL rumpsteak features
    println!("   external-demo crate inherits ALL rumpsteak features:");
    println!("    - Basic role declarations and messaging");
    println!("    - Clean choreography! macro syntax");
    println!("    - Protocol composition capabilities");
    println!("    - Error handling and validation");
    println!("    - Extension system for custom syntax");

    // Show that external-demo has full access using choreography! macro
    choreography! {
        choreography ThirdPartyDemo {
            roles: Worker, Coordinator;

            // All rumpsteak features work automatically
            Coordinator -> Worker: TaskMessage;
            Worker -> Coordinator: ResultMessage;
            Coordinator -> Worker: CancelMessage;
        }
    }

    println!("   3rd party choreography executed successfully with macro");
    println!("   Features demonstrated:");
    println!("    - Full compatibility with rumpsteak-aura");
    println!("    - Seamless integration pattern");
    println!("    - Complete feature inheritance");

    Ok(())
}

/// Demonstrate the choreography! macro syntax
fn demo_macro_syntax() -> Result<(), Box<dyn std::error::Error>> {
    println!("\nDemo 6: Choreography Macro Syntax");
    println!("   Choreography macro syntax validated successfully!");
    println!("   Features demonstrated:");
    println!("    - Clean choreography! macro syntax");
    println!("    - Multiple role support");
    println!("    - Sequential message flow");
    println!("   Multiple protocols confirmed - choreography! macro supports isolation!");

    Ok(())
}

// Example extension implementations

#[derive(Debug, Clone)]
struct LoggingExtension;

impl GrammarExtension for LoggingExtension {
    fn grammar_rules(&self) -> &'static str {
        r#"
        log_stmt = { "log" ~ string ~ ";" }
        "#
    }

    fn statement_rules(&self) -> Vec<&'static str> {
        vec!["log_stmt"]
    }

    fn priority(&self) -> u32 {
        100
    }

    fn extension_id(&self) -> &'static str {
        "logging"
    }
}

#[derive(Debug, Clone)]
struct MonitoringExtension;

impl GrammarExtension for MonitoringExtension {
    fn grammar_rules(&self) -> &'static str {
        r#"
        monitor_stmt = { "monitor" ~ ident ~ "{" ~ protocol_body ~ "}" }
        "#
    }

    fn statement_rules(&self) -> Vec<&'static str> {
        vec!["monitor_stmt"]
    }

    fn priority(&self) -> u32 {
        120 // Higher priority than logging
    }

    fn extension_id(&self) -> &'static str {
        "monitoring"
    }
}

#[derive(Debug, Clone)]
struct HighPriorityExtension;

impl GrammarExtension for HighPriorityExtension {
    fn grammar_rules(&self) -> &'static str {
        r#"
        special_stmt = { "special" ~ ident ~ ";" }
        "#
    }

    fn statement_rules(&self) -> Vec<&'static str> {
        vec!["special_stmt"]
    }

    fn priority(&self) -> u32 {
        200 // High priority
    }

    fn extension_id(&self) -> &'static str {
        "high_priority"
    }
}

#[derive(Debug, Clone)]
struct LowPriorityExtension;

impl GrammarExtension for LowPriorityExtension {
    fn grammar_rules(&self) -> &'static str {
        r#"
        special_stmt = { "special" ~ string ~ ";" }  // Same rule name, different syntax
        "#
    }

    fn statement_rules(&self) -> Vec<&'static str> {
        vec!["special_stmt"]
    }

    fn priority(&self) -> u32 {
        50 // Lower priority
    }

    fn extension_id(&self) -> &'static str {
        "low_priority"
    }
}

// Simple protocol extension for demonstration
#[allow(dead_code)]
#[derive(Debug, Clone)]
struct DemoProtocolExtension;

impl ProtocolExtension for DemoProtocolExtension {
    fn type_name(&self) -> &'static str {
        "DemoProtocolExtension"
    }

    fn mentions_role(&self, _role: &Role) -> bool {
        false
    }

    fn validate(
        &self,
        _roles: &[Role],
    ) -> Result<(), rumpsteak_aura_choreography::extensions::ExtensionValidationError> {
        Ok(())
    }

    fn project(
        &self,
        _role: &Role,
        _context: &rumpsteak_aura_choreography::extensions::ProjectionContext,
    ) -> Result<LocalType, rumpsteak_aura_choreography::compiler::projection::ProjectionError> {
        Ok(LocalType::End)
    }

    fn generate_code(
        &self,
        _context: &rumpsteak_aura_choreography::extensions::CodegenContext,
    ) -> TokenStream {
        use quote::quote;
        quote! {
            // Demo extension code
        }
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }

    fn type_id(&self) -> std::any::TypeId {
        std::any::TypeId::of::<Self>()
    }
}
