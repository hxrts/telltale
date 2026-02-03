# DSL Extensions Part 2: Syntax Extensions

This guide explains how to extend the choreography DSL syntax. Runtime effects are covered in [DSL Extensions Part 1: Runtime Effect System](16_effect_extensions.md).

## Overview

Syntax extensions add new grammar rules and statement parsers to the DSL. The system is built around `GrammarExtension`, `StatementParser`, and `ProtocolExtension`.

## GrammarExtension

Grammar extensions provide Pest rules and a list of statement rules they handle.

```rust
pub trait GrammarExtension: Send + Sync + Debug {
    fn grammar_rules(&self) -> &'static str;
    fn statement_rules(&self) -> Vec<&'static str>;
    fn priority(&self) -> u32 { 100 }
    fn extension_id(&self) -> &'static str;
}
```

The `priority` value resolves conflicts when multiple extensions define the same rule. Higher priority wins and conflicts are recorded by the registry.

## StatementParser and ProtocolExtension

Statement parsers translate matched rules into protocol extensions.

```rust
pub trait StatementParser: Send + Sync + Debug {
    fn can_parse(&self, rule_name: &str) -> bool;
    fn supported_rules(&self) -> Vec<String>;
    fn parse_statement(
        &self,
        rule_name: &str,
        content: &str,
        context: &ParseContext,
    ) -> Result<Box<dyn ProtocolExtension>, ParseError>;
}
```

`ProtocolExtension` instances participate in validation, projection, and code generation.

```rust
pub trait ProtocolExtension: Send + Sync + Debug {
    fn type_name(&self) -> &'static str;
    fn mentions_role(&self, role: &Role) -> bool;
    fn validate(&self, roles: &[Role]) -> Result<(), ExtensionValidationError>;
    fn project(&self, role: &Role, ctx: &ProjectionContext) -> Result<LocalType, ProjectionError>;
    fn generate_code(&self, ctx: &CodegenContext) -> proc_macro2::TokenStream;
}
```

Use these traits to attach new DSL constructs to projection and codegen.

## ExtensionRegistry

The `ExtensionRegistry` stores grammar extensions and statement parsers.

```rust
let mut registry = ExtensionRegistry::new();
registry.register_grammar(MyGrammarExtension)?;
registry.register_parser(MyStatementParser, "my_parser".to_string());
```

The registry tracks rule conflicts and supports dependency checks. Use `get_detailed_conflicts` for human readable conflict reports.

## GrammarComposer

`GrammarComposer` combines the base grammar with registered extension rules and caches the result.

```rust
let mut composer = GrammarComposer::new();
composer.register_extension(MyGrammarExtension);
let grammar = composer.compose()?;
```

The cache avoids recomposing the grammar when the extension set has not changed.

## ExtensionParser

`ExtensionParser` wires the grammar composer into the parsing pipeline.

```rust
let mut parser = ExtensionParser::new();
parser.register_extension(MyGrammarExtension, MyStatementParser);
let choreography = parser.parse_with_extensions(source)?;
```

`parse_with_extensions` currently runs the standard parser and does not dispatch extension statements. This means extension grammar rules are composed, but statement parsing is a no op until the dispatch path is completed.

## Extension Discovery

The `extensions::discovery` module provides metadata and dependency management.

```rust
let mut discovery = ExtensionDiscovery::new();
discovery.add_search_path("./extensions");
let registry = discovery.create_registry(&["timeout".to_string()])?;
```

Discovery assembles an `ExtensionRegistry` in dependency order and performs basic validation.

## Built In Timeout Extension

The `extensions::timeout` module contains a sample grammar extension, parser, and protocol extension. It is intended as a reference implementation and currently uses simplified parsing logic.

See [Extension Guide](18_extension_guide.md) for a full workflow and [Choreographic DSL](04_choreographic_dsl.md) for the base grammar.
