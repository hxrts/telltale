#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

//! Integration tests for the extension system

use std::any::{Any, TypeId};
use std::sync::{Arc, Mutex};
use telltale_language::compiler::projection::ProjectionError;
use telltale_language::extensions::{
    CodegenContext, ExtensionValidationError, GrammarExtension, ParseContext, ParseError,
    ProjectionContext, ProtocolExtension, StatementParser,
};
use telltale_runtime::ast::{LocalType, Protocol, Role};
use telltale_runtime::effects::*;
use telltale_runtime::RoleName;
use telltale_runtime::{
    parse_and_generate_with_extensions, parse_choreography_with_extensions, ExtensionParserBuilder,
};

// Simple test extension
#[derive(Clone, Debug)]
struct TestExtension {
    value: u32,
}

impl ExtensionEffect<TestRole> for TestExtension {
    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn type_name(&self) -> &'static str {
        "TestExtension"
    }

    fn participating_roles(&self) -> Vec<TestRole> {
        vec![]
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn ExtensionEffect<TestRole>> {
        Box::new(self.clone())
    }
}

#[derive(Debug)]
struct TestStatementGrammarExtension;

impl GrammarExtension for TestStatementGrammarExtension {
    fn grammar_rules(&self) -> &'static str {
        r#"
test_ext_stmt = { "test_ext" ~ integer }
"#
    }

    fn statement_rules(&self) -> Vec<&'static str> {
        vec!["test_ext_stmt"]
    }

    fn extension_id(&self) -> &'static str {
        "test_statement"
    }
}

#[derive(Debug)]
struct TestStatementParser;

impl StatementParser for TestStatementParser {
    fn can_parse(&self, rule_name: &str) -> bool {
        rule_name == "test_ext_stmt"
    }

    fn supported_rules(&self) -> Vec<String> {
        vec!["test_ext_stmt".to_string()]
    }

    fn parse_statement(
        &self,
        rule_name: &str,
        content: &str,
        _context: &ParseContext,
    ) -> Result<Box<dyn ProtocolExtension>, ParseError> {
        if rule_name != "test_ext_stmt" {
            return Err(ParseError::InvalidSyntax {
                details: format!("unexpected rule {rule_name}"),
            });
        }
        let value = content
            .split_whitespace()
            .nth(1)
            .ok_or_else(|| ParseError::InvalidSyntax {
                details: "missing test_ext integer payload".to_string(),
            })?
            .parse::<u32>()
            .map_err(|_| ParseError::InvalidSyntax {
                details: "invalid test_ext integer payload".to_string(),
            })?;
        Ok(Box::new(TestStatementProtocol { value }))
    }
}

#[derive(Debug, Clone)]
struct TestStatementProtocol {
    value: u32,
}

impl ProtocolExtension for TestStatementProtocol {
    fn type_name(&self) -> &'static str {
        "TestStatementProtocol"
    }

    fn mentions_role(&self, _role: &Role) -> bool {
        true
    }

    fn validate(&self, _roles: &[Role]) -> Result<(), ExtensionValidationError> {
        Ok(())
    }

    fn project(
        &self,
        _role: &Role,
        _context: &ProjectionContext,
    ) -> Result<LocalType, ProjectionError> {
        Ok(LocalType::End)
    }

    fn generate_code(&self, _context: &CodegenContext) -> proc_macro2::TokenStream {
        let value = self.value;
        quote::quote! {
            .ext(TestExtension { value: #value })
        }
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }

    fn clone_box(&self) -> Box<dyn ProtocolExtension> {
        Box::new(self.clone())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum TestRole {
    Alice,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum TestLabel {
    Default,
}

impl LabelId for TestLabel {
    fn as_str(&self) -> &'static str {
        match self {
            TestLabel::Default => "default",
        }
    }

    fn from_str(label: &str) -> Option<Self> {
        match label {
            "default" => Some(TestLabel::Default),
            _ => None,
        }
    }
}

impl RoleId for TestRole {
    type Label = TestLabel;

    fn role_name(&self) -> RoleName {
        match self {
            TestRole::Alice => RoleName::from_static("Alice"),
        }
    }
}

// Test handler with extension support
struct TestHandler {
    registry: ExtensionRegistry<(), TestRole>,
    executed_extensions: Arc<Mutex<Vec<u32>>>,
}

impl TestHandler {
    fn new(_role: TestRole) -> Self {
        let executed_extensions = Arc::new(Mutex::new(Vec::new()));
        Self {
            registry: registered_test_registry(executed_extensions.clone()),
            executed_extensions,
        }
    }

    fn without_extensions(_role: TestRole) -> Self {
        Self {
            registry: ExtensionRegistry::new(),
            executed_extensions: Arc::new(Mutex::new(Vec::new())),
        }
    }

    fn executed_values(&self) -> Vec<u32> {
        self.executed_extensions.lock().unwrap().clone()
    }
}

fn registered_test_registry(
    executed_extensions: Arc<Mutex<Vec<u32>>>,
) -> ExtensionRegistry<(), TestRole> {
    let mut registry = ExtensionRegistry::new();
    let executed = executed_extensions.clone();
    registry
        .register::<TestExtension, _>(move |_ep, ext| {
            let executed = executed.clone();
            Box::pin(async move {
                let test_ext = ext
                    .as_any()
                    .downcast_ref::<TestExtension>()
                    .ok_or_else(|| ExtensionError::TypeMismatch {
                        expected: "TestExtension",
                        actual: ext.type_name(),
                    })?;

                executed.lock().unwrap().push(test_ext.value);
                Ok(())
            })
        })
        .expect("register test extension");
    registry
}

fn lower_test_statement_protocol(protocol: &Protocol) -> Program<TestRole, ()> {
    match protocol {
        Protocol::Extension {
            extension,
            continuation,
            ..
        } => {
            let statement_ext = extension
                .as_any()
                .downcast_ref::<TestStatementProtocol>()
                .expect("expected TestStatementProtocol extension");
            Program::new()
                .ext(TestExtension {
                    value: statement_ext.value,
                })
                .end()
                .then(lower_test_statement_protocol(continuation))
        }
        Protocol::End => Program::new().end(),
        other => panic!("unsupported protocol shape in test lowerer: {other:?}"),
    }
}

#[async_trait::async_trait]
impl ExtensibleHandler for TestHandler {
    fn extension_registry(&self) -> &ExtensionRegistry<Self::Endpoint, Self::Role> {
        &self.registry
    }
}

#[async_trait::async_trait]
impl ChoreoHandler for TestHandler {
    type Role = TestRole;
    type Endpoint = ();

    async fn send<M: serde::Serialize + Send + Sync>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _to: Self::Role,
        _msg: &M,
    ) -> ChoreoResult<()> {
        Ok(())
    }

    async fn recv<M: serde::de::DeserializeOwned + Send>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _from: Self::Role,
    ) -> ChoreoResult<M> {
        Err(ChoreographyError::Transport("recv not implemented".into()))
    }

    async fn choose(
        &mut self,
        _ep: &mut Self::Endpoint,
        _who: Self::Role,
        _label: TestLabel,
    ) -> ChoreoResult<()> {
        Ok(())
    }

    async fn offer(
        &mut self,
        _ep: &mut Self::Endpoint,
        _from: Self::Role,
    ) -> ChoreoResult<TestLabel> {
        Ok(TestLabel::Default)
    }

    async fn with_timeout<F, T>(
        &mut self,
        _ep: &mut Self::Endpoint,
        _at: Self::Role,
        _dur: std::time::Duration,
        body: F,
    ) -> ChoreoResult<T>
    where
        F: std::future::Future<Output = ChoreoResult<T>> + Send,
    {
        body.await
    }
}

#[tokio::test]
async fn test_extension_execution() {
    let mut handler = TestHandler::new(TestRole::Alice);
    let mut endpoint = ();

    let program: Program<TestRole, ()> = Program::new()
        .ext(TestExtension { value: 1 })
        .ext(TestExtension { value: 2 })
        .ext(TestExtension { value: 3 })
        .end();

    let result = interpret_extensible(&mut handler, &mut endpoint, program)
        .await
        .unwrap();

    assert_eq!(result.final_state, InterpreterState::Completed);

    let executed = handler.executed_values();
    assert_eq!(executed, vec![1, 2, 3]);
}

#[tokio::test]
async fn test_extension_type_safety() {
    let handler = TestHandler::new(TestRole::Alice);

    // Verify the handler is registered for TestExtension
    assert!(handler.registry.is_registered::<TestExtension>());
}

#[test]
fn test_extension_in_program() {
    let program: Program<TestRole, ()> = Program::new().ext(TestExtension { value: 42 }).end();

    assert_eq!(program.len(), 2); // extension + end

    // Verify we can extract the extension
    if let Some(ext) = program.effects()[0].as_extension::<TestExtension>() {
        assert_eq!(ext.value, 42);
    } else {
        panic!("Expected TestExtension");
    }
}

#[test]
fn test_extension_type_checking() {
    let effect = Effect::<TestRole, ()>::ext(TestExtension { value: 100 });

    // Correct type check
    assert!(effect.is_extension::<TestExtension>());

    // Wrong type check
    #[derive(Clone, Debug)]
    struct OtherExtension;
    impl ExtensionEffect<TestRole> for OtherExtension {
        fn type_id(&self) -> TypeId {
            TypeId::of::<Self>()
        }
        fn type_name(&self) -> &'static str {
            "OtherExtension"
        }
        fn participating_roles(&self) -> Vec<TestRole> {
            vec![]
        }
        fn as_any(&self) -> &dyn Any {
            self
        }
        fn as_any_mut(&mut self) -> &mut dyn Any {
            self
        }
        fn clone_box(&self) -> Box<dyn ExtensionEffect<TestRole>> {
            Box::new(self.clone())
        }
    }

    assert!(!effect.is_extension::<OtherExtension>());
}

#[tokio::test]
async fn test_unregistered_extension_fails_closed_without_side_effects() {
    let mut handler = TestHandler::without_extensions(TestRole::Alice);
    let mut endpoint = ();
    let program: Program<TestRole, ()> = Program::new().ext(TestExtension { value: 99 }).end();

    let result = interpret_extensible(&mut handler, &mut endpoint, program)
        .await
        .expect("interpreter should surface extension failure as failed state");

    match result.final_state {
        InterpreterState::Failed(message) => {
            assert!(message.contains("Extension handler not registered"));
        }
        other => panic!("expected failed state, got {other:?}"),
    }
    assert!(
        handler.executed_values().is_empty(),
        "unregistered extension must not mutate semantic state out of band"
    );
}

#[test]
fn extension_pipeline_generates_code_for_standard_protocols_with_registered_extensions() {
    let registry = telltale_runtime::ExtensionRegistry::with_builtin_extensions();
    let tokens = parse_and_generate_with_extensions(
        r#"
protocol Ping =
  roles A, B
  A -> B : Msg
"#,
        &registry,
    )
    .expect("registered extensions should not break standard parse/codegen");

    let code = tokens.to_string();
    assert!(code.contains("Ping"));
    assert!(code.contains("A"));
    assert!(code.contains("B"));
}

#[tokio::test]
async fn extension_statement_dispatch_executes_through_parser_lowering_and_runtime() {
    let mut parser = ExtensionParserBuilder::new()
        .with_extension(TestStatementGrammarExtension, TestStatementParser)
        .expect("register test statement extension")
        .build();

    assert!(parser.can_handle_statement("test_ext_stmt"));
    let stats = parser.extension_stats();
    assert_eq!(stats.grammar_extensions, 1);
    assert_eq!(stats.statement_parsers, 1);

    let source = r#"
protocol ExtFlow =
  roles Alice
  test_ext 41
"#;

    let choreography = parser
        .parse_with_extensions(source)
        .expect("extension parser should dispatch registered statements");
    match &choreography.protocol {
        Protocol::Extension { extension, .. } => {
            let ext = extension
                .as_any()
                .downcast_ref::<TestStatementProtocol>()
                .expect("expected parsed test statement extension");
            assert_eq!(ext.value, 41);
        }
        other => panic!("expected extension protocol, got {other:?}"),
    }

    let mut registry = telltale_runtime::ExtensionRegistry::new();
    registry
        .register_grammar(TestStatementGrammarExtension)
        .unwrap();
    registry.register_parser(TestStatementParser, "test_statement".to_string());
    let (parsed, extensions) = parse_choreography_with_extensions(source, &registry)
        .expect("public parse API should preserve extensions");
    assert_eq!(extensions.len(), 1);

    let generated = parse_and_generate_with_extensions(source, &registry)
        .expect("codegen should lower extension statement");
    let generated_code = generated.to_string();
    assert!(
        generated_code.contains("TestExtension") && generated_code.contains("value : 41"),
        "generated extension lowering should include the runtime effect payload: {generated_code}"
    );

    let mut handler = TestHandler::new(TestRole::Alice);
    let mut endpoint = ();
    let program = lower_test_statement_protocol(&parsed.protocol);
    let result = interpret_extensible(&mut handler, &mut endpoint, program)
        .await
        .expect("parsed extension program should execute");

    assert_eq!(result.final_state, InterpreterState::Completed);
    assert_eq!(handler.executed_values(), vec![41]);
}

#[tokio::test]
async fn extension_statement_dispatch_fails_with_stable_diagnostics_without_handler() {
    let mut registry = telltale_runtime::ExtensionRegistry::new();
    registry
        .register_grammar(TestStatementGrammarExtension)
        .unwrap();
    registry.register_parser(TestStatementParser, "test_statement".to_string());
    let (parsed, _extensions) = parse_choreography_with_extensions(
        r#"
protocol ExtFlow =
  roles Alice
  test_ext 99
"#,
        &registry,
    )
    .expect("extension statement should parse");

    let mut handler = TestHandler::without_extensions(TestRole::Alice);
    let mut endpoint = ();
    let program = lower_test_statement_protocol(&parsed.protocol);
    let result = interpret_extensible(&mut handler, &mut endpoint, program)
        .await
        .expect("interpreter should surface extension dispatch failure as failed state");

    match result.final_state {
        InterpreterState::Failed(message) => {
            assert!(message.contains("Extension handler not registered"));
            assert!(message.contains("TestExtension"));
        }
        other => panic!("expected failed state, got {other:?}"),
    }
}

#[test]
fn malformed_extension_statement_rejects_with_stable_parse_diagnostic() {
    let mut parser = ExtensionParserBuilder::new()
        .with_extension(TestStatementGrammarExtension, TestStatementParser)
        .expect("register test statement extension")
        .build();

    let err = parser
        .parse_with_extensions(
            r#"
protocol ExtFlow =
  roles Alice
  test_ext nope
"#,
        )
        .expect_err("malformed extension payload should fail during statement parsing");
    let message = err.to_string();
    assert!(
        message.contains("invalid test_ext integer payload"),
        "unexpected malformed-extension diagnostic: {message}"
    );
}
