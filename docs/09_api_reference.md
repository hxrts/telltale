# API Reference

## Core Types

### Choreography

```rust
pub struct Choreography {
    pub name: Ident,
    pub roles: Vec<Role>,
    pub protocol: Protocol,
    pub attrs: HashMap<String, String>,
}
```

Represents a complete choreography. The name identifies the protocol. Roles list all participants. Protocol contains the interaction tree. Attrs hold annotations like optimize or verify.

### Protocol

```rust
pub enum Protocol {
    Send { from: Role, to: Role, message: MessageType, continuation: Box<Protocol> },
    Choice { role: Role, branches: Vec<(Label, Protocol)> },
    Loop { condition: Option<Condition>, body: Box<Protocol> },
    Parallel { protocols: Vec<Protocol> },
    Rec { name: Ident, body: Box<Protocol> },
    Var(Ident),
    End,
}
```

Protocol represents the global choreography as a tree. Send describes message transmission. Choice represents branching. Loop contains iteration. Parallel holds concurrent branches. Rec defines recursion points. Var references recursion. End terminates the protocol.

### LocalType

```rust
pub enum LocalType {
    Send { to: Role, message: MessageType, continuation: Box<LocalType> },
    Receive { from: Role, message: MessageType, continuation: Box<LocalType> },
    Select { to: Role, branches: Vec<(Label, LocalType)> },
    Branch { from: Role, branches: Vec<(Label, LocalType)> },
    LocalChoice { branches: Vec<(Label, LocalType)> },
    Loop { condition: Option<Condition>, body: Box<LocalType> },
    Rec { label: String, body: Box<LocalType> },
    Var(String),
    End,
}
```

LocalType is the projected view for a single role. Send and Receive represent communication. Select makes a choice. Branch receives a choice. LocalChoice is internal branching. Loop, Rec, Var handle iteration. End terminates.

### Role

```rust
pub struct Role {
    pub name: Ident,
    pub index: Option<usize>,
    pub param: Option<TokenStream>,
    pub array_size: Option<TokenStream>,
}
```

Role identifies a participant. Name is the role identifier. Index holds concrete indices for indexed roles (e.g., `Worker[0]`). Param contains symbolic parameter expressions (e.g., `N` in `Worker[N]`). Array_size specifies the size of parameterized role arrays.

### MessageType

```rust
pub struct MessageType {
    pub name: Ident,
    pub payload: Option<Vec<Field>>,
    pub type_annotation: Option<TokenStream>,
}
```

MessageType describes a message. Name is the message identifier. Payload lists fields. Type_annotation contains optional Rust type annotations like `<String>` or `<Vec<i32>>`.

## Parser API

### parse_choreography_str

```rust
pub fn parse_choreography_str(input: &str) -> Result<Choreography, ParseError>
```

Parses a choreography from a string. Returns ParseError if syntax is invalid or roles are undefined.

### parse_choreography_file

```rust
pub fn parse_choreography_file(path: &Path) -> Result<Choreography, ParseError>
```

Parses a choreography from a file. Reads the file and delegates to parse_choreography_str.

### ParseError

```rust
pub enum ParseError {
    UndefinedRole(String),
    DuplicateRole(String),
    UndefinedProtocol(String),
    DuplicateProtocol(String),
    Syntax { location: String, message: String },
    InvalidCondition(String),
    InvalidMessage(String),
    Pest(Box<pest::error::Error<Rule>>),
}
```

ParseError describes parsing failures. Each variant includes context about the error location and cause.

## Projection API

### project

```rust
pub fn project(choreography: &Choreography, role: &Role) -> Result<LocalType, ProjectionError>
```

Projects a global choreography to a local type for one role. Returns ProjectionError if projection fails due to conflicts or invalid patterns.

### ProjectionError

```rust
pub enum ProjectionError {
    InconsistentParallel(String),
    UndefinedRole(String),
    InvalidChoice(String),
    InvalidLoop(String),
    RecursionError(String),
}
```

ProjectionError indicates projection failures. InconsistentParallel means conflicting parallel branches. Other variants describe specific issues.

## Code Generation API

### generate_session_types

```rust
pub fn generate_session_types(choreography: &Choreography) -> TokenStream
```

Generates Rumpsteak session types from a choreography. Projects to local types and converts to Rust type definitions.

### generate_effects_protocol

```rust
pub fn generate_effects_protocol(choreography: &Choreography) -> TokenStream
```

Generates effect-based protocol implementations. Creates effect programs that handlers can interpret.

## Effect System API

### Program

```rust
pub struct Program<R, M> {
    pub effects: Vec<Effect<R, M>>,
}
```

Program is a sequence of effects representing a protocol. Effects lists the operations to execute.

Methods:

```rust
pub fn new() -> Self
pub fn send(self, to: R, msg: M) -> Self
pub fn recv<T>(self, from: R) -> Self
pub fn choose(self, who: R, label: Label) -> Self
pub fn offer(self, from: R) -> Self
pub fn with_timeout(self, at: R, dur: Duration, body: Program<R, M>) -> Self
pub fn parallel(self, programs: Vec<Program<R, M>>) -> Self
pub fn end(self) -> Self
```

Builder methods chain to construct programs.

### Effect

```rust
pub enum Effect<R, M> {
    Send { to: R, msg: M },
    Recv { from: R },
    Choose { who: R, label: Label },
    Offer { from: R },
    WithTimeout { at: R, dur: Duration, body: Box<Program<R, M>> },
    Parallel { programs: Vec<Program<R, M>> },
    End,
}
```

Effect represents a single operation. Send, Recv, Choose, Offer are basic actions. WithTimeout wraps a sub-program. Parallel executes branches. End terminates.

### interpret

```rust
pub async fn interpret<H, R, M>(
    handler: &mut H,
    endpoint: &mut H::Endpoint,
    program: Program<R, M>,
) -> Result<InterpretResult<M>>
where
    H: ChoreoHandler<Role = R>,
    R: RoleId,
    M: ProgramMessage + Serialize + DeserializeOwned + 'static,
```

Interprets a program using a handler. Executes each effect by calling handler methods. Returns InterpretResult with received messages and status.

### InterpretResult

```rust
pub struct InterpretResult<M> {
    pub received_values: Vec<M>,
    pub final_state: InterpreterState,
}
```

InterpretResult contains execution results. Received_values holds messages from recv operations. Final_state indicates Completed, Failed, or Timeout.

### ChoreoHandler

```rust
pub trait ChoreoHandler {
    type Role: RoleId;
    type Endpoint;
    
    async fn send<M: Serialize + Send + Sync>(
        &mut self, ep: &mut Self::Endpoint, to: Self::Role, msg: &M
    ) -> Result<()>;
    
    async fn recv<M: DeserializeOwned + Send>(
        &mut self, ep: &mut Self::Endpoint, from: Self::Role
    ) -> Result<M>;
    
    async fn choose(
        &mut self, ep: &mut Self::Endpoint, who: Self::Role, label: Label
    ) -> Result<()>;
    
    async fn offer(
        &mut self, ep: &mut Self::Endpoint, from: Self::Role
    ) -> Result<Label>;
}
```

ChoreoHandler trait defines handler interface. Implement this trait to create custom handlers.

### ChoreographyError

```rust
pub enum ChoreographyError {
    Transport(String),
    Serialization(String),
    Timeout(Duration),
    ProtocolViolation(String),
    Other(String),
}
```

ChoreographyError describes execution failures. Transport covers network errors. Serialization handles encoding issues. Timeout indicates operation exceeded duration. ProtocolViolation means session type mismatch.

## Handler APIs

### InMemoryHandler

```rust
pub struct InMemoryHandler<R: RoleId>
```

Constructor:

```rust
pub fn new(role: R) -> Self
pub fn with_channels(
    role: R,
    channels: Arc<Mutex<HashMap<(R, R), MessageChannelPair>>>,
    choice_channels: Arc<Mutex<HashMap<(R, R), ChoiceChannelPair>>>,
) -> Self
```

The new constructor creates an isolated handler. With_channels shares channels between handlers for coordinated testing.

### RumpsteakHandler

```rust
pub struct RumpsteakHandler<R, M>
```

Constructor:

```rust
pub fn new() -> Self
```

Requires RumpsteakEndpoint for connection management. See [Using Rumpsteak Handlers](06_rumpsteak_handler.md) for complete API.

### RecordingHandler

```rust
pub struct RecordingHandler<R: RoleId>
```

Constructor:

```rust
pub fn new(role: R) -> Self
```

Methods:

```rust
pub fn events(&self) -> &[RecordedEvent<R>]
```

Returns the list of recorded operations.

## Runtime API

### spawn

```rust
pub fn spawn<F>(future: F)
where F: Future<Output = ()> + Send + 'static
```

Spawns a task on the platform runtime. Uses tokio on native targets. Uses wasm-bindgen-futures on WASM.

### spawn_local

```rust
pub fn spawn_local<F>(future: F)
where F: Future<Output = ()> + 'static
```

Spawns a local task without Send bound. Useful for WASM where Send is not required.

## Macro API

### choreography!

```rust
choreography! {
    ProtocolName {
        roles: Role1, Role2
        Role1 -> Role2: Message
    }
}
```

Procedural macro for inline choreographies. Parses the DSL and generates role types, message types, and session types.

Supports both inline syntax and string literals.

