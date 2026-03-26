#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]

//! Integration tests for the extension system

use std::any::{Any, TypeId};
use std::sync::{Arc, Mutex};
use telltale_language::extensions::timeout::{TimeoutGrammarExtension, TimeoutStatementParser};
use telltale_runtime::effects::*;
use telltale_runtime::RoleName;
use telltale_runtime::{parse_and_generate_with_extensions, ExtensionParserBuilder};

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

#[test]
fn timeout_extension_statement_dispatch_remains_fail_closed_until_runtime_support_exists() {
    let mut parser = ExtensionParserBuilder::new()
        .with_extension(TimeoutGrammarExtension, TimeoutStatementParser)
        .expect("register timeout extension")
        .build();

    assert!(parser.can_handle_statement("timeout_stmt"));
    let stats = parser.extension_stats();
    assert_eq!(stats.grammar_extensions, 1);
    assert_eq!(
        stats.statement_parsers, 0,
        "statement parser registration remains reserved until dispatch support lands"
    );

    let standard = parser
        .parse_with_extensions(
            r#"
protocol Ping =
  roles A, B
  A -> B : Msg
"#,
        )
        .expect("registered extensions should preserve standard parsing");
    assert_eq!(standard.roles.len(), 2);

    let err = parser
        .parse_with_extensions(
            r#"
protocol Timed =
  roles A, B
  timeout 10ms A {
    A -> B : Msg
  }
"#,
        )
        .expect_err("timeout statement dispatch should fail closed until implemented");
    let message = err.to_string();
    assert!(
        message.contains("Standard parsing failed")
            || message.contains("Unknown extension statement"),
        "unexpected extension failure mode: {message}"
    );
}
