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
pub fn get_attribute(&self, key: &str) -> Option<&String>
pub fn set_attribute(&mut self, key: String, value: String)
pub fn has_attribute(&self, key: &str) -> bool
pub fn find_nodes_with_annotation(&self, key: &str) -> Vec<&Protocol>
```

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
End terminates the protocol.

Methods:

```rust
pub fn mentions_role(&self, role: &Role) -> bool
pub fn validate(&self, roles: &[Role]) -> Result<(), ValidationError>
pub fn get_annotations(&self) -> &HashMap<String, String>
pub fn get_annotation(&self, key: &str) -> Option<&String>
pub fn has_annotation(&self, key: &str) -> bool
pub fn set_annotation(&mut self, key: String, value: String) -> bool
pub fn collect_nodes_with_annotation(&self, key: &str, nodes: &mut Vec<&Protocol>)
```

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
}
```

Loop condition specification.
RoleDecides means a role controls iteration.
Count specifies fixed iterations.
Custom contains arbitrary Rust expressions.

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
    End,
}
```

LocalType is the projected session type for a single role.
Send and Receive represent communication actions.
Select makes a choice and notifies others.
Branch receives a choice from another role.
LocalChoice is internal branching without communication.
Loop, Rec, Var handle iteration and recursion.
End terminates the session.

Methods:

```rust
pub fn is_well_formed(&self) -> bool
```

### Role

```rust
pub struct Role {
    pub name: Ident,
    pub param: Option<RoleParam>,
    pub index: Option<RoleIndex>,
    pub legacy_index: Option<usize>,
    pub legacy_param: Option<TokenStream>,
    pub array_size: Option<TokenStream>,
}
```

Role identifies a protocol participant.
Name is the role identifier.
Param specifies role count (Static, Symbolic, or Runtime).
Index specifies role instance (Concrete, Symbolic, Wildcard, or Range).
Legacy fields maintain backward compatibility.

Methods:

```rust
pub fn new(name: Ident) -> Self
pub fn with_param(name: Ident, param: RoleParam) -> Self
pub fn with_index(name: Ident, index: RoleIndex) -> Self
pub fn is_indexed(&self) -> bool
pub fn is_parameterized(&self) -> bool
pub fn is_array(&self) -> bool
pub fn is_dynamic(&self) -> bool
pub fn matches_family(&self, family: &Role) -> bool
pub fn validate(&self) -> RoleValidationResult<()>
pub fn safe_static(name: Ident, count: u32) -> RoleValidationResult<Self>
```

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
    Syntax { span: ErrorSpan, message: String },
    UndefinedRole { role: String, span: ErrorSpan },
    DuplicateRole { role: String, span: ErrorSpan },
    InvalidMessage { message: String, span: ErrorSpan },
    InvalidCondition { condition: String, span: ErrorSpan },
    InvalidAnnotation { annotation: String, span: ErrorSpan },
    RoleValidation { error: RoleValidationError, span: ErrorSpan },
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

Generates Rumpsteak session type for a specific role.
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
    ) -> Result<()>;

    async fn recv<M: DeserializeOwned + Send>(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> Result<M>;

    async fn choose(
        &mut self,
        ep: &mut Self::Endpoint,
        who: Self::Role,
        label: Label,
    ) -> Result<()>;

    async fn offer(
        &mut self,
        ep: &mut Self::Endpoint,
        from: Self::Role,
    ) -> Result<Label>;

    async fn with_timeout<F, T>(
        &mut self,
        ep: &mut Self::Endpoint,
        at: Self::Role,
        dur: Duration,
        body: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>> + Send;

    async fn broadcast<M: Serialize + Send + Sync>(
        &mut self,
        ep: &mut Self::Endpoint,
        recipients: &[Self::Role],
        msg: &M,
    ) -> Result<()>;
}
```

ChoreoHandler trait defines the handler interface.
Implement this trait to create custom transport handlers.
Uses async_trait for object safety.

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
    Timeout(Duration),
    ProtocolViolation(String),
    UnknownRole(String),
}
```

ChoreographyError describes execution failures.
Transport covers network and channel errors.
Serialization handles encoding and decoding issues.
Timeout indicates operation exceeded duration.
ProtocolViolation means session type mismatch.
UnknownRole indicates referenced role not found.

### Label

```rust
pub struct Label(pub &'static str);
```

Label identifies branches in choice protocols.
Contains a static string matching protocol branch names.

### RoleId

```rust
pub trait RoleId: Copy + Eq + std::hash::Hash + Debug + Send + Sync + 'static {}
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

### RumpsteakHandler

```rust
pub struct RumpsteakHandler<R: RoleId>
```

Handler for Rumpsteak session-typed channels.
Provides unified abstraction over bidirectional channels and dynamic sessions.

Constructor:

```rust
pub fn new() -> Self
```

Requires RumpsteakEndpoint for connection management.
See [Using Rumpsteak Handlers](07_rumpsteak_handler.md) for complete usage.

### RumpsteakEndpoint

```rust
pub struct RumpsteakEndpoint<R: RoleId>
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
choreography! {
    ProtocolName {
        roles: Role1, Role2
        Role1 -> Role2: Message
    }
}
```

Procedural macro for inline choreographies.
Parses the DSL and generates role types, message types, and session types.
Supports both inline syntax and string literals.

Example:

```rust
choreography! {
    TwoPhaseCommit {
        roles: Coordinator, Participant
        
        Coordinator -> Participant: Prepare
        Participant -> Coordinator: Vote
        choice Coordinator {
            Commit => Coordinator -> Participant: Commit,
            Abort => Coordinator -> Participant: Abort
        }
    }
}
```

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
    hash: Vec<u8>,
}
```

Content identifier wrapping a cryptographic hash. Parameterized by hasher type with SHA-256 as default.

Methods:

```rust
pub fn new<T: Contentable>(value: &T) -> Self
pub fn as_bytes(&self) -> &[u8]
```

### Hasher

```rust
pub trait Hasher: Clone + Default {
    const HASH_SIZE: usize;
    fn hash(data: &[u8]) -> Vec<u8>;
}
```

Hasher trait for swappable hash algorithms. Implementations include `Sha256Hasher`, `Blake3Hasher`, and `PoseidonHasher`.

### Contentable

```rust
pub trait Contentable {
    fn to_cbor(&self) -> Vec<u8>;
    fn from_cbor(data: &[u8]) -> Result<Self, ContentError>;
}
```

Trait for types that support content addressing. Implementations exist for `GlobalType`, `LocalTypeR`, `Label`, and `PayloadSort`.

### ContentStore

```rust
pub struct ContentStore<T: Contentable> {
    store: BTreeMap<ContentId, T>,
}
```

Content-addressed storage with deduplication.

Methods:

```rust
pub fn new() -> Self
pub fn insert(&mut self, value: T) -> ContentId
pub fn get(&self, cid: &ContentId) -> Option<&T>
pub fn contains(&self, cid: &ContentId) -> bool
```

## Topology API

### Location

```rust
pub enum Location {
    Local,
    Remote { endpoint: String },
    Colocated { peer: String },
}
```

Location specifies where a role executes. Local is in-process. Remote specifies a network endpoint. Colocated references another role.

### TopologyConstraint

```rust
pub enum TopologyConstraint {
    Colocated(String, String),
    Separated(String, String),
    Pinned(String, Location),
    Region(String, String),
}
```

Constraints on role placement. Colocated requires same node. Separated requires different nodes. Pinned fixes a location. Region specifies geographic constraints.

### Topology

```rust
pub struct Topology {
    locations: BTreeMap<String, Location>,
    constraints: Vec<TopologyConstraint>,
}
```

Maps roles to locations with optional constraints.

Methods:

```rust
pub fn builder() -> TopologyBuilder
pub fn load(path: &str) -> Result<Topology, TopologyError>
pub fn location(&self, role: &str) -> Option<&Location>
pub fn validate(&self, choreo: &Choreography) -> Result<(), TopologyError>
```

### TopologyBuilder

```rust
pub struct TopologyBuilder { ... }
```

Builder for constructing topologies.

Methods:

```rust
pub fn role(self, name: &str, endpoint: &str) -> Self
pub fn constraint(self, constraint: TopologyConstraint) -> Self
pub fn build(self) -> Topology
```

### ProtocolHandler

```rust
pub struct ProtocolHandler<R: RoleId> { ... }
```

Topology-aware handler for protocol execution.

Methods:

```rust
pub fn as_role(role: &str) -> ProtocolHandlerBuilder
pub fn from_topology(topology: Topology, role: &str) -> Self
```

## Resource Heap API

### ResourceId

```rust
pub struct ResourceId {
    id: ContentId,
}
```

Unique identifier for heap-allocated resources. Derived from content hash.

### Resource

```rust
pub enum Resource {
    Channel(ChannelState),
    Message(Message),
    Session(LocalTypeR),
}
```

Resource kinds that can be allocated on the heap.

### Heap

```rust
pub struct Heap {
    resources: BTreeMap<ResourceId, Resource>,
    nullifiers: BTreeSet<ResourceId>,
}
```

Deterministic heap with nullifier-based consumption tracking.

Methods:

```rust
pub fn new() -> Self
pub fn alloc(&self, resource: Resource) -> (ResourceId, Heap)
pub fn consume(&self, rid: &ResourceId) -> Result<Heap, HeapError>
pub fn read(&self, rid: &ResourceId) -> Result<&Resource, HeapError>
pub fn is_consumed(&self, rid: &ResourceId) -> bool
pub fn merkle_root(&self) -> [u8; 32]
pub fn prove_inclusion(&self, rid: &ResourceId) -> InclusionProof
```

### HeapError

```rust
pub enum HeapError {
    NotFound(ResourceId),
    AlreadyConsumed(ResourceId),
    InvalidProof,
}
```

Errors from heap operations. NotFound indicates missing resource. AlreadyConsumed indicates double-consumption attempt.

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
