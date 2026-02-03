# API Reference

## Core AST Types

### Choreography

```rust
pub struct Choreography {
    pub name: Ident,
    pub namespace: Option<String>,
    pub roles: Vec<Role>,
    pub protocol: Protocol,
    pub attrs: HashMap<String, String>,
}
```

Represents a complete choreographic protocol specification.
Name identifies the protocol.
Namespace provides optional module scoping.
Roles list all participants.
Protocol contains the interaction tree.
Attrs hold annotations like optimize or verify.

Methods:

```rust
pub fn qualified_name(&self) -> String
pub fn validate(&self) -> Result<(), ValidationError>
pub fn get_attributes(&self) -> &HashMap<String, String>
pub fn get_attributes_mut(&mut self) -> &mut HashMap<String, String>
pub fn get_attribute(&self, key: &str) -> Option<&String>
pub fn set_attribute(&mut self, key: String, value: String)
pub fn remove_attribute(&mut self, key: &str) -> Option<String>
pub fn has_attribute(&self, key: &str) -> bool
pub fn get_attribute_as<T>(&self, key: &str) -> Option<T>
pub fn get_attribute_as_bool(&self, key: &str) -> Option<bool>
pub fn clear_attributes(&mut self)
pub fn attribute_count(&self) -> usize
pub fn attribute_keys(&self) -> Vec<&String>
pub fn validate_required_attributes(&self, required_keys: &[&str]) -> Result<(), Vec<String>>
pub fn find_nodes_with_annotation(&self, key: &str) -> Vec<&Protocol>
pub fn find_nodes_with_annotation_value(&self, key: &str, value: &str) -> Vec<&Protocol>
pub fn total_annotation_count(&self) -> usize
```

These methods manage choreography attributes and validation. They also provide annotation queries across the protocol tree.

### Protocol

```rust
pub enum Protocol {
    Send {
        from: Role,
        to: Role,
        message: MessageType,
        continuation: Box<Protocol>,
        annotations: HashMap<String, String>,
        from_annotations: HashMap<String, String>,
        to_annotations: HashMap<String, String>,
    },
    Broadcast {
        from: Role,
        to_all: Vec<Role>,
        message: MessageType,
        continuation: Box<Protocol>,
        annotations: HashMap<String, String>,
        from_annotations: HashMap<String, String>,
    },
    Choice {
        role: Role,
        branches: Vec<Branch>,
        annotations: HashMap<String, String>,
    },
    Loop {
        condition: Option<Condition>,
        body: Box<Protocol>,
    },
    Parallel {
        protocols: Vec<Protocol>,
    },
    Rec {
        label: Ident,
        body: Box<Protocol>,
    },
    Var(Ident),
    Extension {
        extension: Box<dyn ProtocolExtension>,
        continuation: Box<Protocol>,
        annotations: HashMap<String, String>,
    },
    End,
}
```

Protocol represents the global choreography as a tree.
Send describes point-to-point message transmission.
Broadcast sends messages to multiple roles.
Choice represents branching with labeled branches.
Loop contains iteration with optional conditions.
Parallel holds concurrent protocol execution.
Rec defines recursion points.
Var references recursive labels.
Extension represents custom protocol statements.
End terminates the protocol.

Methods:

```rust
pub fn mentions_role(&self, role: &Role) -> bool
pub fn validate(&self, roles: &[Role]) -> Result<(), ValidationError>
pub fn get_annotations(&self) -> &HashMap<String, String>
pub fn get_annotation(&self, key: &str) -> Option<&String>
pub fn get_annotations_mut(&mut self) -> Option<&mut HashMap<String, String>>
pub fn has_annotation(&self, key: &str) -> bool
pub fn set_annotation(&mut self, key: String, value: String) -> bool
pub fn get_annotation_as<T>(&self, key: &str) -> Option<T>
pub fn get_annotation_as_bool(&self, key: &str) -> Option<bool>
pub fn get_annotations_with_prefix(&self, prefix: &str) -> HashMap<String, String>
pub fn collect_nodes_with_annotation(&self, key: &str, nodes: &mut Vec<&Protocol>)
pub fn collect_nodes_with_annotation_value(
    &self,
    key: &str,
    value: &str,
    nodes: &mut Vec<&Protocol>,
)
pub fn deep_annotation_count(&self) -> usize
```

These methods manage statement annotations and query annotation usage. They are used by validation and tooling passes.

### Branch

```rust
pub struct Branch {
    pub label: Ident,
    pub guard: Option<TokenStream>,
    pub protocol: Protocol,
}
```

Branch in a choice construct.
Label identifies the branch.
Guard provides optional conditional expression.
Protocol contains the branch continuation.

### Condition

```rust
pub enum Condition {
    RoleDecides(Role),
    Count(usize),
    Custom(TokenStream),
    Fuel(usize),
    YieldAfter(usize),
    YieldWhen(String),
}
```

Loop condition specification.
RoleDecides means a role controls iteration. Note: `loop decide by Role` is desugared
to a choice+recursion pattern at parse time, so `RoleDecides` is rarely seen in the AST
after parsing. See the DSL documentation for details.
Count specifies fixed iterations.
Custom contains arbitrary Rust expressions.
Fuel limits the number of iterations.
YieldAfter yields control after a number of steps.
YieldWhen yields control on a matching label or condition.

### LocalType

```rust
pub enum LocalType {
    Send {
        to: Role,
        message: MessageType,
        continuation: Box<LocalType>,
    },
    Receive {
        from: Role,
        message: MessageType,
        continuation: Box<LocalType>,
    },
    Select {
        to: Role,
        branches: Vec<(Ident, LocalType)>,
    },
    Branch {
        from: Role,
        branches: Vec<(Ident, LocalType)>,
    },
    LocalChoice {
        branches: Vec<(Ident, LocalType)>,
    },
    Loop {
        condition: Option<Condition>,
        body: Box<LocalType>,
    },
    Rec {
        label: Ident,
        body: Box<LocalType>,
    },
    Var(Ident),
    Timeout {
        duration: Duration,
        body: Box<LocalType>,
    },
    End,
}
```

LocalType is the projected session type for a single role.
Send and Receive represent communication actions.
Select makes a choice and notifies others.
Branch receives a choice from another role.
LocalChoice is internal branching without communication.
Loop, Rec, Var handle iteration and recursion.
Timeout wraps a local type with a duration.
End terminates the session.

Methods:

```rust
pub fn is_well_formed(&self) -> bool
```

This checks recursive structure for well formedness. It is used in validation and tests.

### Role

```rust
pub struct Role { /* private fields */ }
```

Role identifies a protocol participant.
Name is the role identifier.
Param specifies role count (Static, Symbolic, or Runtime).
Index specifies role instance (Concrete, Symbolic, Wildcard, or Range).
Array_size stores a computed size for code generation.

Methods:

```rust
pub fn new(name: Ident) -> RoleValidationResult<Self>
pub fn with_param(name: Ident, param: RoleParam) -> RoleValidationResult<Self>
pub fn with_index(name: Ident, index: RoleIndex) -> RoleValidationResult<Self>
pub fn with_param_and_index(
    name: Ident,
    param: RoleParam,
    index: RoleIndex,
) -> RoleValidationResult<Self>
pub fn parameterized(name: Ident, param: TokenStream) -> RoleValidationResult<Self>
pub fn array(name: Ident, size: usize) -> RoleValidationResult<Self>
pub fn name(&self) -> &Ident
pub fn param(&self) -> Option<&RoleParam>
pub fn index(&self) -> Option<&RoleIndex>
pub fn array_size(&self) -> Option<&TokenStream>
pub fn is_indexed(&self) -> bool
pub fn is_parameterized(&self) -> bool
pub fn is_array(&self) -> bool
pub fn is_dynamic(&self) -> bool
pub fn is_symbolic(&self) -> bool
pub fn is_wildcard(&self) -> bool
pub fn is_range(&self) -> bool
pub fn get_param(&self) -> Option<&RoleParam>
pub fn get_index(&self) -> Option<&RoleIndex>
pub fn matches_family(&self, family: &Role) -> bool
pub fn validate(&self) -> RoleValidationResult<()>
pub fn safe_static(name: Ident, count: u32) -> RoleValidationResult<Self>
pub fn safe_indexed(name: Ident, index: u32) -> RoleValidationResult<Self>
pub fn safe_range(name: Ident, start: u32, end: u32) -> RoleValidationResult<Self>
```

These methods construct and validate roles. Constructors return `RoleValidationResult` when bounds checks fail. They also inspect role parameters and indices.

### RoleParam

```rust
pub enum RoleParam {
    Static(u32),
    Symbolic(String),
    Runtime,
}
```

Role parameter for dynamic role counts.
Static specifies a compile-time count.
Symbolic uses a named parameter.
Runtime indicates count determined at runtime.

### RoleIndex

```rust
pub enum RoleIndex {
    Concrete(u32),
    Symbolic(String),
    Wildcard,
    Range(RoleRange),
}
```

Role index for referencing specific instances.
Concrete specifies a fixed index.
Symbolic uses a named variable.
Wildcard matches all instances.
Range specifies a range of indices.

### MessageType

```rust
pub struct MessageType {
    pub name: Ident,
    pub type_annotation: Option<TokenStream>,
    pub payload: Option<TokenStream>,
}
```

MessageType describes a protocol message.
Name is the message identifier.
Type_annotation contains optional Rust type annotations.
Payload specifies the message data type.

Methods:

```rust
pub fn to_ident(&self) -> Ident
```

This method converts the message type name to an identifier. It is used during code generation.

## Parser API

### parse_choreography_str

```rust
pub fn parse_choreography_str(input: &str) -> Result<Choreography, ParseError>
```

Parses a choreography from a string.
Returns ParseError if syntax is invalid or roles are undefined.

### parse_choreography_file

```rust
pub fn parse_choreography_file(path: &Path) -> Result<Choreography, ParseError>
```

Parses a choreography from a file.
Reads the file content and delegates to parse_choreography_str.

### parse_choreography

```rust
pub fn parse_choreography(input: TokenStream) -> Result<Choreography, ParseError>
```

Parses a choreography from a proc macro token stream.
Used internally by the choreography macro.

### ParseError

```rust
pub enum ParseError {
    Pest(Box<pest::error::Error<Rule>>),
    Layout { span: ErrorSpan, message: String },
    Syntax { span: ErrorSpan, message: String },
    UndefinedRole { role: String, span: ErrorSpan },
    DuplicateRole { role: String, span: ErrorSpan },
    EmptyChoreography,
    InvalidMessage { message: String, span: ErrorSpan },
    InvalidCondition { message: String, span: ErrorSpan },
    UndefinedProtocol { protocol: String, span: ErrorSpan },
    DuplicateProtocol { protocol: String, span: ErrorSpan },
    GrammarComposition(GrammarCompositionError),
}
```

ParseError describes parsing failures.
Each variant includes error context and location information.
ErrorSpan provides formatted error messages with source snippets.

## Projection API

### project

```rust
pub fn project(choreography: &Choreography, role: &Role) -> Result<LocalType, ProjectionError>
```

Projects a global choreography to a local session type for one role.
Returns ProjectionError if projection fails due to conflicts or invalid patterns.

### ProjectionError

```rust
pub enum ProjectionError {
    NonParticipantChoice,
    UnsupportedParallel(String),
    InconsistentParallel,
    UnboundVariable(String),
    DynamicRoleProjection { role: String },
    UnboundSymbolic { param: String },
    RangeProjection,
    WildcardProjection,
}
```

ProjectionError indicates projection failures.
NonParticipantChoice means a role is not involved in a choice.
UnsupportedParallel indicates parallel composition is not supported for the role.
InconsistentParallel means conflicting parallel branches.
UnboundVariable indicates a recursive variable is not in scope.
DynamicRoleProjection means runtime roles cannot be projected statically.
UnboundSymbolic indicates a symbolic parameter is not bound.
RangeProjection and WildcardProjection indicate unsupported index types.

## Code Generation API

### generate_session_type

```rust
pub fn generate_session_type(
    choreography: &Choreography,
    role: &Role,
) -> Result<TokenStream, ProjectionError>
```

Generates Telltale session type for a specific role.
Projects the choreography to a local type and converts to Rust type definitions.

### generate_choreography_code

```rust
pub fn generate_choreography_code(choreography: &Choreography) -> TokenStream
```

Generates complete choreography code including roles, messages, and session types.

### generate_effects_protocol

```rust
pub fn generate_effects_protocol(choreography: &Choreography) -> TokenStream
```

Generates effect-based protocol implementations.
Creates effect programs that handlers can interpret at runtime.

### generate_role_implementations

```rust
pub fn generate_role_implementations(choreography: &Choreography) -> TokenStream
```

Generates trait implementations for role types.

### generate_helpers

```rust
pub fn generate_helpers(choreography: &Choreography) -> TokenStream
```

Generates helper functions for protocol execution.

## Effect System API

### Program

```rust
pub struct Program<R: RoleId, M> {
    pub effects: Vec<Effect<R, M>>,
}
```

Program is a sequence of effects representing a protocol.
Effects lists the operations to execute.

Builder methods:

```rust
pub fn new() -> Self
pub fn send(self, to: R, msg: M) -> Self
pub fn recv<T: 'static>(self, from: R) -> Self
pub fn choose(self, at: R, label: Label) -> Self
pub fn offer(self, from: R) -> Self
pub fn with_timeout(self, at: R, dur: Duration, body: Program<R, M>) -> Self
pub fn parallel(self, programs: Vec<Program<R, M>>) -> Self
pub fn branch(self, choosing_role: R, branches: Vec<(Label, Program<R, M>)>) -> Self
pub fn loop_n(self, iterations: usize, body: Program<R, M>) -> Self
pub fn loop_inf(self, body: Program<R, M>) -> Self
pub fn ext<E: ExtensionEffect + 'static>(self, extension: E) -> Self
pub fn end(self) -> Self
pub fn then(self, other: Program<R, M>) -> Self
```

Analysis methods:

```rust
pub fn roles_involved(&self) -> HashSet<R>
pub fn send_count(&self) -> usize
pub fn recv_count(&self) -> usize
pub fn has_timeouts(&self) -> bool
pub fn has_parallel(&self) -> bool
pub fn validate(&self) -> Result<(), ProgramError>
pub fn is_empty(&self) -> bool
pub fn len(&self) -> usize
```

These methods inspect program structure and validate the sequence. They are used by analysis and debugging tools.

### Effect

```rust
pub enum Effect<R: RoleId, M> {
    Send { to: R, msg: M },
    Recv { from: R, msg_type: &'static str },
    Choose { at: R, label: Label },
    Offer { from: R },
    Branch {
        choosing_role: R,
        branches: Vec<(Label, Program<R, M>)>,
    },
    Loop {
        iterations: Option<usize>,
        body: Box<Program<R, M>>,
    },
    Timeout {
        at: R,
        dur: Duration,
        body: Box<Program<R, M>>,
    },
    Parallel {
        programs: Vec<Program<R, M>>,
    },
    Extension(Box<dyn ExtensionEffect>),
    End,
}
```

Effect represents a single choreographic operation.
Send transmits a message to another role.
Recv receives a message with type information.
Choose makes an internal choice and broadcasts the label.
Offer waits for an external choice from another role.
Branch represents conditional execution based on choice.
Loop executes body multiple times or infinitely.
Timeout wraps a sub-program with time limit.
Parallel executes multiple programs concurrently.
Extension provides domain-specific effects.
End terminates the program.

Methods:

```rust
pub fn ext<E: ExtensionEffect + 'static>(extension: E) -> Self
pub fn is_extension<E: ExtensionEffect + 'static>(&self) -> bool
pub fn as_extension<E: ExtensionEffect + 'static>(&self) -> Option<&E>
pub fn as_extension_mut<E: ExtensionEffect + 'static>(&mut self) -> Option<&mut E>
pub fn extension_type_id(&self) -> Option<TypeId>
```

These helpers inspect and extract extension payloads. They are used by interpreters and middleware.

### interpret

```rust
pub async fn interpret<H, R, M>(
    handler: &mut H,
    endpoint: &mut H::Endpoint,
    program: Program<R, M>,
) -> Result<InterpretResult<M>>
where
    H: ChoreoHandler<Role = R> + Send,
    R: RoleId,
    M: ProgramMessage + Serialize + DeserializeOwned + 'static,
```

Interprets a program using a handler.
Executes each effect by calling handler methods.
Returns InterpretResult with received messages and execution status.

### interpret_extensible

```rust
pub async fn interpret_extensible<H, R, M>(
    handler: &mut H,
    endpoint: &mut <H as ExtensibleHandler>::Endpoint,
    program: Program<R, M>,
) -> Result<InterpretResult<M>>
where
    H: ChoreoHandler<Role = R, Endpoint = <H as ExtensibleHandler>::Endpoint>
        + ExtensibleHandler
        + Send,
    R: RoleId,
    M: ProgramMessage + Serialize + DeserializeOwned + 'static,
```

Interprets a program using an extensible handler.
Supports handlers that dispatch extension effects to registered handlers.

### InterpretResult

```rust
pub struct InterpretResult<M> {
    pub received_values: Vec<M>,
    pub final_state: InterpreterState,
}
```

InterpretResult contains execution results.
Received_values holds messages from recv operations.
Final_state indicates execution outcome.

### InterpreterState

```rust
pub enum InterpreterState {
    Completed,
    Timeout,
    Failed(String),
}
```

State of the program interpreter.
Completed means successful execution.
Timeout indicates operation exceeded duration.
Failed contains error description.

### ChoreoHandler

```rust
#[async_trait]
pub trait ChoreoHandler: Send {
    type Role: RoleId;
    type Endpoint: Endpoint;

    async fn send<M: Serialize + Send + Sync>(
        &mut self,
        ep: &mut Self::Endpoint,
        to: Self::Role,
        msg: &M,
    ) -> ChoreoResult<()>;

    async fn recv<M: DeserializeOwned + Send>(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<M>;

    async fn choose(
        &mut self,
        ep: &mut Self::Endpoint,
        who: Self::Role,
        label: <Self::Role as RoleId>::Label,
    ) -> ChoreoResult<()>;

    async fn offer(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> ChoreoResult<<Self::Role as RoleId>::Label>;

    async fn with_timeout<F, T>(
        &mut self,
        ep: &mut Self::Endpoint,
        at: Self::Role,
        dur: Duration,
        body: F,
    ) -> ChoreoResult<T>
    where
        F: std::future::Future<Output = ChoreoResult<T>> + Send;

    async fn broadcast<M: Serialize + Send + Sync>(
        &mut self,
        ep: &mut Self::Endpoint,
        recipients: &[Self::Role],
        msg: &M,
    ) -> ChoreoResult<()>;
}
```

ChoreoHandler trait defines the handler interface.
Implement this trait to create custom transport handlers.
Uses async_trait for object safety.

### ChoreographicAdapter

```rust
#[async_trait]
pub trait ChoreographicAdapter: Send {
    type Error: std::error::Error + Send + Sync + From<ChoreographyError> + 'static;
    type Role: RoleId;

    async fn send<M: Message>(&mut self, to: Self::Role, msg: M) -> Result<(), Self::Error>;
    async fn recv<M: Message>(&mut self, from: Self::Role) -> Result<M, Self::Error>;

    async fn provide_message<M: Message>(&mut self, to: Self::Role) -> Result<M, Self::Error>;
    async fn select_branch<L: LabelId>(&mut self, labels: &[L]) -> Result<L, Self::Error>;

    async fn broadcast<M: Message + Clone>(
        &mut self,
        to: &[Self::Role],
        msg: M,
    ) -> Result<(), Self::Error>;

    async fn collect<M: Message>(&mut self, from: &[Self::Role]) -> Result<Vec<M>, Self::Error>;

    async fn choose(
        &mut self,
        to: Self::Role,
        label: <Self::Role as RoleId>::Label,
    ) -> Result<(), Self::Error>;

    async fn offer(
        &mut self,
        from: Self::Role,
    ) -> Result<<Self::Role as RoleId>::Label, Self::Error>;
}
```

ChoreographicAdapter drives generated runners directly.
Implement `provide_message` and `select_branch` to supply runtime data and decisions.
Default implementations return errors to avoid placeholder behavior.

### ExtensionEffect

```rust
pub trait ExtensionEffect: Send + Sync + std::fmt::Debug {
    fn type_id(&self) -> TypeId;
    fn type_name(&self) -> &'static str;
    fn participating_role_ids(&self) -> Vec<Box<dyn Any>>;
    fn as_any(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;
    fn clone_box(&self) -> Box<dyn ExtensionEffect>;
}
```

ExtensionEffect enables domain-specific protocol extensions.
Type_id provides unique identification.
Type_name returns human-readable name.
Participating_role_ids specifies which roles are involved (empty means all roles).
As_any and as_any_mut enable downcasting.
Clone_box enables cloning trait objects.

### ChoreographyError

```rust
pub enum ChoreographyError {
    Transport(String),
    Serialization(String),
    ChannelSendFailed { channel_type: &'static str, reason: String },
    ChannelClosed { channel_type: &'static str, operation: &'static str },
    NoPeerChannel { peer: String },
    LabelSerializationFailed { operation: &'static str, reason: String },
    MessageSerializationFailed {
        operation: &'static str,
        type_name: &'static str,
        reason: String
    },
    Timeout(Duration),
    ProtocolViolation(String),
    UnknownRole(String),
    ProtocolContext {
        protocol: &'static str,
        role: &'static str,
        phase: &'static str,
        inner: Box<ChoreographyError>
    },
    RoleContext { role: &'static str, index: Option<u32>, inner: Box<ChoreographyError> },
    MessageContext {
        operation: &'static str,
        message_type: &'static str,
        direction: &'static str,
        other_role: &'static str,
        inner: Box<ChoreographyError>
    },
    ChoiceError { role: &'static str, details: String },
    WithContext { context: String, inner: Box<ChoreographyError> },
    InvalidChoice { expected: Vec<String>, actual: String },
    ExecutionError(String),
}
```

ChoreographyError describes execution failures.
Transport covers network and channel errors.
Serialization handles encoding and decoding issues.
Timeout indicates operation exceeded duration.
ProtocolViolation means session type mismatch.
UnknownRole indicates referenced role not found.

### LabelId

```rust
pub trait LabelId: Copy + Eq + std::hash::Hash + Debug + Send + Sync + 'static {
    fn as_str(&self) -> &'static str;
    fn from_str(label: &str) -> Option<Self>;
}
```

LabelId identifies branches in choice protocols.
Implementations map stable identifiers to protocol branch names.

### RoleId

```rust
pub trait RoleId: Copy + Eq + std::hash::Hash + Debug + Send + Sync + 'static {
    type Label: LabelId;
    fn role_name(&self) -> RoleName;
    fn role_index(&self) -> Option<u32>;
}
```

RoleId trait for role identifiers.
Automatically implemented for types meeting the bounds.

## Handler APIs

### InMemoryHandler

```rust
pub struct InMemoryHandler<R: RoleId>
```

In-memory handler for testing using futures channels.
Simulates message passing without network communication.
WASM-compatible.

Constructor:

```rust
pub fn new(role: R) -> Self
pub fn with_channels(
    role: R,
    channels: Arc<Mutex<HashMap<(R, R), MessageChannelPair>>>,
    choice_channels: Arc<Mutex<HashMap<(R, R), ChoiceChannelPair>>>,
) -> Self
```

The new constructor creates an isolated handler.
With_channels shares channels between handlers for coordinated testing.

### TelltaleHandler

```rust
pub struct TelltaleHandler<R: RoleId>
```

Handler for Telltale session-typed channels.
Provides unified abstraction over bidirectional channels and dynamic sessions.

Constructor:

```rust
pub fn new() -> Self
```

Requires TelltaleEndpoint for connection management.
See [Using Telltale Handlers](08_telltale_handler.md) for complete usage.

### TelltaleEndpoint

```rust
pub struct TelltaleEndpoint<R: RoleId>
```

Endpoint managing per-peer channels and sessions.
Tracks session metadata and connection state.

### SimpleChannel

```rust
pub struct SimpleChannel
```

Simple bidirectional channel for backward compatibility.

Methods:

```rust
pub fn pair() -> (Self, Self)
pub async fn send(&mut self, msg: Vec<u8>) -> Result<(), String>
pub async fn recv(&mut self) -> Result<Vec<u8>, String>
```

These methods create a channel pair and move raw bytes. They are used by the Telltale handler implementation.

### RecordingHandler

```rust
pub struct RecordingHandler<R: RoleId>
```

Recording handler for testing that captures all effects.
Does not produce actual values.
Use for protocol structure verification.

Constructor:

```rust
pub fn new(role: R) -> Self
```

Methods:

```rust
pub fn events(&self) -> Vec<RecordedEvent<R>>
pub fn clear(&self)
```

Returns the list of recorded operations.

### RecordedEvent

```rust
pub enum RecordedEvent<R: RoleId> {
    Send { from: R, to: R, msg_type: String },
    Recv { from: R, to: R, msg_type: String },
    Choose { at: R, label: Label },
    Offer { from: R, to: R },
}
```

Represents a recorded choreographic operation.

## Extension System API

### ExtensibleHandler

```rust
pub trait ExtensibleHandler {
    type Endpoint: Endpoint;
    fn extension_registry(&self) -> &ExtensionRegistry<Self::Endpoint>;
}
```

ExtensibleHandler enables extension effect dispatch.
Handlers implementing this trait can process domain-specific extensions.

### ExtensionRegistry

```rust
pub struct ExtensionRegistry<EP: Endpoint>
```

Registry mapping extension types to handlers.

Methods:

```rust
pub fn new() -> Self
pub fn register<E, F>(&mut self, handler: F)
where
    E: ExtensionEffect + 'static,
    F: Fn(&mut EP, &dyn ExtensionEffect) -> BoxFuture<'static, Result<()>>
        + Send
        + Sync
        + 'static,
pub fn is_registered<E: ExtensionEffect + 'static>(&self) -> bool
pub fn handle(
    &self,
    ep: &mut EP,
    ext: &dyn ExtensionEffect,
) -> Option<BoxFuture<'static, Result<()>>>
```

These methods register and invoke extension handlers. They are used by extensible interpreters.

### ExtensionError

```rust
pub enum ExtensionError {
    UnknownExtension { type_name: String },
    TypeMismatch { expected: &'static str, actual: &'static str },
    ExecutionFailed(String),
}
```

Errors during extension processing.

## Runtime API

### spawn

```rust
pub fn spawn<F>(future: F)
where F: Future<Output = ()> + Send + 'static
```

Spawns a task on the platform runtime.
Uses tokio on native targets.
Uses wasm-bindgen-futures on WASM.

### spawn_local

```rust
pub fn spawn_local<F>(future: F)
where F: Future<Output = ()> + 'static
```

Spawns a local task without Send bound.
Useful for WASM where Send is not required.

## Macro API

### choreography!

```rust
choreography!(r#"
protocol ProtocolName =
  roles Role1, Role2
  Role1 -> Role2 : Message
"#);
```

Procedural macro for choreographies defined in the DSL.
Parses the DSL and generates role types, message types, and session types.
The macro requires a string literal input.

Example:

```rust
choreography!(r#"
protocol TwoPhaseCommit =
  roles Coordinator, Participant
  Coordinator -> Participant : Prepare
  Participant -> Coordinator : Vote
"#);
```

This example defines a two party commit protocol. The macro expands into generated role and session types.

## Theory API

### project

```rust
pub fn project(g: &GlobalType, role: &str) -> Result<LocalTypeR, ProjectionError>
```

Projects a global type to a local type for a given role. Uses merge internally to combine branches when the role is not involved in a choice.

### merge

```rust
pub fn merge(t1: &LocalTypeR, t2: &LocalTypeR) -> Result<LocalTypeR, MergeError>
```

Merges two local types. Send merge requires identical label sets. Receive merge unions label sets. Returns an error if the types have incompatible structure.

### can_merge

```rust
pub fn can_merge(t1: &LocalTypeR, t2: &LocalTypeR) -> bool
```

Checks if two local types can be merged without error.

### MergeError

```rust
pub enum MergeError {
    EndMismatch(LocalTypeR),
    PartnerMismatch { expected: String, found: String },
    DirectionMismatch,
    IncompatibleContinuations { label: String },
    RecursiveVariableMismatch { expected: String, found: String },
    VariableMismatch { expected: String, found: String },
    IncompatibleTypes,
    SendLabelMismatch { left: String, right: String },
    SendBranchCountMismatch { left: usize, right: usize },
}
```

MergeError indicates why two local types cannot be merged. The `SendLabelMismatch` and `SendBranchCountMismatch` variants are specific to send merge which requires identical labels.

### sync_subtype

```rust
pub fn sync_subtype(sub: &LocalTypeR, sup: &LocalTypeR) -> bool
```

Checks synchronous subtyping between two local types. Uses tree-based algorithm.

### async_subtype

```rust
pub fn async_subtype(sub: &LocalTypeR, sup: &LocalTypeR) -> bool
```

Checks asynchronous subtyping between two local types. Uses SISO decomposition.

### dual

```rust
pub fn dual(lt: &LocalTypeR) -> LocalTypeR
```

Computes the dual of a local type. Swaps send and receive operations.

## Content Addressing API

### ContentId

```rust
pub struct ContentId<H: Hasher = Sha256Hasher> {
    hash: H::Digest,
}
```

Content identifier wrapping a cryptographic hash. Parameterized by hasher type with SHA-256 as default.

Methods:

```rust
pub fn from_bytes(data: &[u8]) -> Self
pub fn from_hash(hash: impl AsRef<[u8]>) -> Result<Self, ContentIdError>
pub fn as_bytes(&self) -> &[u8]
pub fn to_hex(&self) -> String
pub fn algorithm(&self) -> &'static str
```

These methods construct and inspect content identifiers. Use `from_bytes` when hashing raw canonical bytes.

### Hasher

```rust
pub trait Hasher: Clone + Default + PartialEq + Send + Sync + 'static {
    type Digest: AsRef<[u8]> + Clone + PartialEq + Eq + Hash + Send + Sync + 'static;
    const HASH_SIZE: usize;
    fn digest(data: &[u8]) -> Self::Digest;
    fn algorithm_name() -> &'static str;
}
```

Hasher trait for swappable hash algorithms. The default implementation is `Sha256Hasher`.

### Contentable

```rust
pub trait Contentable {
    fn to_bytes(&self) -> Result<Vec<u8>, ContentableError>;
    fn from_bytes(bytes: &[u8]) -> Result<Self, ContentableError>;
}
```

Trait for types that support content addressing. Implementations exist for `GlobalType`, `LocalTypeR`, `Label`, and `PayloadSort`.

### ContentStore

```rust
pub struct ContentStore<K: Contentable, V, H: Hasher = Sha256Hasher>
```

Content-addressed storage with deduplication.

Methods:

```rust
pub fn new() -> Self
pub fn with_capacity(capacity: usize) -> Self
pub fn get(&self, key: &K) -> Result<Option<&V>, ContentableError>
pub fn insert(&mut self, key: &K, value: V) -> Result<Option<V>, ContentableError>
pub fn get_or_insert_with<F>(&mut self, key: &K, f: F) -> Result<&V, ContentableError>
pub fn contains(&self, key: &K) -> Result<bool, ContentableError>
pub fn remove(&mut self, key: &K) -> Result<Option<V>, ContentableError>
pub fn clear(&mut self)
pub fn len(&self) -> usize
pub fn is_empty(&self) -> bool
pub fn metrics(&self) -> CacheMetrics
pub fn reset_metrics(&self)
```

These methods provide lookup, insertion, and cache metrics. Key-based operations return `ContentableError` when serialization fails. The store uses content IDs derived from `Contentable` keys.

## Topology API

### Location

```rust
pub enum Location {
    Local,
    Remote(TopologyEndpoint),
    Colocated(RoleName),
}
```

Location specifies where a role executes. Local is in-process. Remote specifies a network endpoint. Colocated references another role.

### TopologyConstraint

```rust
pub enum TopologyConstraint {
    Colocated(RoleName, RoleName),
    Separated(RoleName, RoleName),
    Pinned(RoleName, Location),
    Region(RoleName, Region),
}
```

Constraints on role placement. Colocated requires same node. Separated requires different nodes. Pinned fixes a location. Region specifies geographic constraints.

### Topology

```rust
pub struct Topology {
    mode: Option<TopologyMode>,
    locations: BTreeMap<RoleName, Location>,
    constraints: Vec<TopologyConstraint>,
}
```

Maps roles to locations with optional constraints.

Methods:

```rust
pub fn builder() -> TopologyBuilder
pub fn new() -> Topology
pub fn local_mode() -> Topology
pub fn with_role(self, role: RoleName, location: Location) -> Topology
pub fn with_constraint(self, constraint: TopologyConstraint) -> Topology
pub fn get_location(&self, role: &RoleName) -> Result<Location, TopologyError>
pub fn validate(&self, choreo_roles: &[RoleName]) -> TopologyValidation
pub fn load(path: impl AsRef<Path>) -> Result<ParsedTopology, TopologyLoadError>
pub fn parse(content: &str) -> Result<ParsedTopology, TopologyLoadError>
```

These methods create and validate topology data. `get_location` returns `TopologyError` when a role is not present. The load and parse helpers return `ParsedTopology` metadata.

### TopologyBuilder

```rust
pub struct TopologyBuilder { ... }
```

Builder for constructing topologies.

Methods:

```rust
pub fn new() -> Self
pub fn mode(self, mode: TopologyMode) -> Self
pub fn local_role(self, role: RoleName) -> Self
pub fn remote_role(self, role: RoleName, endpoint: TopologyEndpoint) -> Self
pub fn colocated_role(self, role: RoleName, peer: RoleName) -> Self
pub fn role(self, role: RoleName, location: Location) -> Self
pub fn colocated(self, r1: RoleName, r2: RoleName) -> Self
pub fn separated(self, r1: RoleName, r2: RoleName) -> Self
pub fn pinned(self, role: RoleName, location: Location) -> Self
pub fn region(self, role: RoleName, region: Region) -> Self
pub fn build(self) -> Topology
```

These methods add locations and constraints to a topology builder. Call `build` to produce a `Topology`.

### TopologyHandler

```rust
pub struct TopologyHandler { ... }
```

Topology-aware handler for protocol execution.

Methods:

```rust
pub fn new(topology: Topology, role: RoleName) -> Self
pub fn from_parsed(parsed: ParsedTopology, role: RoleName) -> Self
pub async fn initialize(&self) -> TransportResult<()>
pub async fn send(&self, to_role: &RoleName, message: Vec<u8>) -> TransportResult<()>
pub async fn recv(&self, from_role: &RoleName) -> TransportResult<Vec<u8>>
pub fn get_location(&self, role: &RoleName) -> Result<Location, TopologyError>
pub fn is_connected(&self, role: &RoleName) -> Result<bool, TopologyError>
pub async fn close(&self) -> TransportResult<()>
```

These methods manage topology aware transports. Initialize before sending messages when eager setup is required.

### TopologyHandlerBuilder

```rust
pub struct TopologyHandlerBuilder { ... }
```

Builder for `TopologyHandler`.

Methods:

```rust
pub fn new(topology: Topology) -> Self
pub fn with_role(self, role: RoleName) -> Self
pub fn build(self) -> Result<TopologyHandler, TopologyHandlerBuildError>
```

### TopologyHandlerBuildError

```rust
pub enum TopologyHandlerBuildError {
    MissingRole,
}
```

Returned when required builder configuration is absent.

### TransportMessage

```rust
pub trait TransportMessage: Send + Sync + 'static {
    fn to_bytes(&self) -> Vec<u8>;
    fn from_bytes(bytes: &[u8]) -> Result<Self, TransportMessageError>
    where
        Self: Sized;
}
```

### TransportMessageError

```rust
pub enum TransportMessageError {
    Deserialization(String),
}
```

## Resource Heap API

### ResourceId

```rust
pub struct ResourceId { /* private fields */ }
```

Unique identifier for heap-allocated resources. Derived from content hash and allocation counter.

Methods:

```rust
pub fn new(hash: [u8; 32], counter: u64) -> Self
pub fn from_resource(resource: &Resource, counter: u64) -> Self
pub fn hash(&self) -> [u8; 32]
pub fn counter(&self) -> u64
pub fn to_short_hex(&self) -> String
```

### Resource

```rust
pub enum Resource {
    Channel(ChannelState),
    Message(Message),
    Session { role: String, type_hash: u64 },
    Value { tag: String, data: Vec<u8> },
}
```

Resource kinds that can be allocated on the heap.

### Heap

```rust
pub struct Heap {
    resources: BTreeMap<ResourceId, Resource>,
    nullifiers: BTreeSet<ResourceId>,
    counter: u64,
}
```

Deterministic heap with nullifier-based consumption tracking.

Methods:

```rust
pub fn new() -> Self
pub fn size(&self) -> usize
pub fn nullified_count(&self) -> usize
pub fn contains(&self, rid: &ResourceId) -> bool
pub fn alloc(&self, resource: Resource) -> (ResourceId, Heap)
pub fn consume(&self, rid: &ResourceId) -> Result<Heap, HeapError>
pub fn read(&self, rid: &ResourceId) -> Result<&Resource, HeapError>
pub fn is_consumed(&self, rid: &ResourceId) -> bool
pub fn is_active(&self, rid: &ResourceId) -> bool
pub fn active_resources(&self) -> impl Iterator<Item = (&ResourceId, &Resource)>
pub fn consumed_ids(&self) -> impl Iterator<Item = &ResourceId>
pub fn alloc_session(&self, role: &str, type_hash: u64) -> (ResourceId, Heap)
```

These methods allocate and consume heap resources. The iterator helpers expose active and consumed IDs for commitment generation.

### HeapError

```rust
pub enum HeapError {
    NotFound(ResourceId),
    AlreadyConsumed(ResourceId),
    AlreadyExists(ResourceId),
    TypeMismatch { expected: String, got: String },
    Other(String),
}
```

Errors from heap operations. NotFound indicates missing resource. AlreadyConsumed indicates double-consumption attempt. TypeMismatch and Other capture additional failure cases.

## Analysis API

### analyze

```rust
pub fn analyze(choreography: &Choreography) -> AnalysisResult
```

Analyzes choreography for properties and potential issues.
Returns warnings and communication graph.

### AnalysisResult

```rust
pub struct AnalysisResult {
    pub warnings: Vec<AnalysisWarning>,
    pub communication_graph: CommunicationGraph,
    pub participation: HashMap<Role, ParticipationInfo>,
}
```

Results of choreography analysis.

### generate_dot_graph

```rust
pub fn generate_dot_graph(choreography: &Choreography) -> String
```

Generates GraphViz DOT representation of the choreography.
Useful for visualization and documentation.
