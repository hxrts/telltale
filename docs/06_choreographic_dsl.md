# Choreographic DSL

## Overview

The parser translates the layout-sensitive Telltale DSL into the internal AST
(`Choreography` and `Protocol`). The DSL is direct style. Statements are
newline separated. Indentation defines blocks. Records keep braces, but
structural blocks do not.

The parser lives in `rust/language/src/compiler/parser/`. It uses Pest plus a
layout preprocessor. The canonical source-file extension for Telltale source
files is `.tell`.

The preferred surface style mixes MPST operators with a small functional-language layout:

- keep `->`, `->*`, `|`, `rec`, and `continue` for protocol structure
- reserve `=>` for branch/result bodies
- use indentation to make control flow visually obvious
- keep braces for record/data layout instead of general structural blocks
- format standalone records and effect-semantics records as multiline brace blocks with `key : value` fields
- use sender records like `Role { priority : high }`
- use `Message of module.Type` with dotted paths instead of Rust-style `::`

### Scope

The DSL describes protocol structure, role-local communication obligations, and protocol-critical authority checks. It does not model arbitrary host state or general application ownership. Session and fragment ownership boundaries are still derived at runtime from composition and link metadata when available. Protocol-visible authority queries and evidence flow are part of the language surface.

The current DSL includes an authority-oriented surface for protocol-critical
host queries and typed local branching:

- top-level `type` and `type alias` declarations
- nominal `effect` interface declarations
- protocol-level `uses` declarations
- `authoritative let` / `observe let` bindings for effect queries
- `let` bindings for linear transfer receipts
- `case ... of` over `Result`/`Maybe`-style constructors
- `timeout ... on timeout ... on cancel ...`
- evidence guards of the form `when check Effect.op(...) yields witness`

These forms participate in explicit language tiers:

- full spec: the DSL can express the construct and the semantic object model
  justifies it
- session projectable: the construct admits MPST/session projection
- protocol-machine executable: the construct is executable through the
  protocol-machine path even when it is not session projectable
- proof only: the construct parses, but lacks the metadata required for
  executable lowering

The generated Rust surface exposes this status through
`Protocol::proof_status`.

## DSL Syntax

```rust
use telltale::tell;

tell! {
  protocol PingPong =
    roles Alice, Bob
    Alice -> Bob : Ping
    Bob -> Alice : Pong
}
```

`tell!` is the canonical public DSL entrypoint. String-literal macro input and
legacy brace-based structural syntax are rejected. The canonical surface is
token-form, indentation-based, and proof-directed.

When a protocol projects cleanly to sessions, the generated module exposes
`Protocol::sessions`. Every generated protocol also exposes
`Protocol::proof_status`, which reports the strongest supported tier and any
projection blocker.

### Namespaces

Namespaces are expressed via a module declaration (rather than attributes) in
source files:

```tell
module threshold_ceremony exposing (ThresholdProtocol)

protocol ThresholdProtocol =
  roles Coordinator, Signers[*]
  Coordinator -> Signers[*] : Request
```

Multiple modules can coexist in separate files. Inside `tell!` you typically
omit the module header and define one protocol-oriented spec directly in Rust.

The parser recognizes `import` declarations for completeness. Import resolution is not currently applied during compilation.

### Supported Constructs

#### 1) Send Statement

```tell
Buyer { priority : high }
  -> Seller : Request of shop.Order

Seller
  -> Buyer : Quote of shop.Price
```

The send statement transfers a message from one role to another. Sender metadata is written as a record attached to the sender term. Typed message attachment is written as `Message of module.Type`.

#### 2) Broadcast Statement

```tell
Leader ->* : Announcement
```

Broadcast sends a message to all other roles.

#### 3) Choice Statement (explicit decider)

```tell
choice Client at
  | Buy when (balance > price) =>
      Client
        -> Server : Purchase of shop.Order
  | Cancel =>
      Client
        -> Server : Cancel
```

The deciding role (`Client`) selects a branch. Guards are optional. Guard expressions are parsed through a typed predicate IR and must be boolean-like. Valid examples include `ready`, `balance > price`, and `is_open()`.

#### 4) Loop Statement

```tell
loop decide by Client
  Client -> Server : Request
  Server -> Client : Response
```

This loop continues while the deciding role chooses to continue. The `decide by` form is
desugared to a choice+recursion pattern at parse time. The first message in the loop body
serves as the "continue" signal - when the deciding role sends it, the loop continues.
A synthetic `Done` message is added as the termination signal.

The example above desugars to:

```tell
rec RoleDecidesLoop
  choice Client at
    | Request =>
      Client -> Server : Request
      Server -> Client : Response
      continue RoleDecidesLoop
    | Done =>
      Client -> Server : Done
```

Requirement: The first statement in a `loop decide by Role` body must be a send from
the deciding role. This ensures the decision to continue is fused with the first message,
saving a round trip compared to sending a separate "continue" signal.

This desugaring converts the `RoleDecides` loop into standard multiparty session type
constructs (choice + recursion), enabling formal verification in Lean and compatibility
with standard MPST projection algorithms.

```tell
loop repeat 5
  A -> B : Ping
  B -> A : Pong
```

This loop repeats a fixed number of times. The compiler records the iteration count in the AST.

```tell
loop while "has_more_data"
  A -> B : Data
```

This loop parses the string content through the same typed predicate IR used by guards. The parser rejects non-boolean predicates such as `"count + 1"` before building the AST.

```tell
loop forever
  A -> B : Tick
```

This loop has no exit condition. Use it for persistent background protocols.

#### 5) Parallel Statement

```tell
par
  | A -> B : Msg1
    B
      -> A : Ack
  | C -> D : Msg2
```

Parallel composition is expressed by `par` with leading `|` branches. A solitary branch is a parse error.

#### 6) Recursion and Calls

```tell
rec Loop
  A -> B : Tick
  continue Loop
```

This defines a recursive label `Loop` and uses `continue Loop` to jump back, modeling unbounded recursion.

```tell
call Handshake
```

This calls another protocol that is in scope. The call target must be defined in the same file or `where` block.

The `continue` keyword is for recursive back-references within a `rec` block. The `call` keyword is for invoking sub-protocols defined in `where` blocks.

#### 7) Protocol Composition (`where` block)

Define and reuse local protocol fragments inside a `where` block.

```tell
protocol Main =
  roles A, B, C
  call Handshake
  call DataTransfer
  A -> C : Done
where
  protocol Handshake =
    A -> B : Hello
    B -> A : Hi
  protocol DataTransfer =
    A -> B : Data
    B -> A : Ack
```

Local protocols can call each other and can be used within choices, loops, and branches.

#### 8) Message Types and Payloads

The preferred typed message form is `Message of module.Type`. Dotted paths are preferred in DSL surface syntax.

```tell
A
  -> B : Request of api.Request
B
  -> A : Response of api.Response

A
  -> B : Msg { data : String, count : Int }
B
  -> A : Result(i : Int, ok : Bool)
```

This sequence demonstrates payload and result handling patterns with mixed message shapes.

#### 9) Dynamic Role Count Support

Dynamic role counts are supported via wildcard and symbolic parameters.

```tell
protocol ThresholdProtocol =
  roles Coordinator, Signers[*]
  Coordinator -> Signers[*] : Request
  Signers[0..threshold] -> Coordinator : Response
```

This example uses a wildcard role family. It also uses a symbolic bound in the role index.

```tell
protocol ConsensusProtocol =
  roles Leader, Followers[N]
  Leader -> Followers[*] : Proposal
  Followers[i] -> Leader : Vote
```

The consensus protocol above demonstrates a symbolic role count (`N`) with an index variable (`i`) iterating over the follower set.

#### 10) Profiles, Progress, And Proof Status

Profiles and explicit progress attachment are part of the proof-backed surface.

```rust
use telltale::tell;

tell! {
  profile Replay fairness strong

  agreement_profile MembershipSoftSafe
    visibility pending
    rule threshold_participants
    usable_at provisional
    finalized_at finalized
    evidence commit_fact

  operation MembershipCheck at Coordinator progress MembershipProgress requires Replay within bounded agreement MembershipSoftSafe compose first_success =
    publish MembershipQueued

  protocol Membership under Replay =
    roles Coordinator, Member
    Coordinator -> Member : Invite
}

assert_eq!(Membership::proof_status::STRONGEST_TIER, "session_projectable");
assert!(Membership::proof_status::PROTOCOL_MACHINE_EXECUTABLE);
```

Profiles, theorem-pack requirements, and language-tier diagnostics are surfaced
as generated metadata because they are part of the verified model, not an
afterthought layered on top.

For effect interfaces, the canonical Rust import is `use Protocol::effects`.
Traits, request/outcome enums, effect-domain data, and per-operation semantic
metadata all live under that one boundary. Interface metadata is exposed under
snake-case effect modules such as `Protocol::effects::runtime`.

This example mixes a named count with index variables. It enables parameterized protocols.

```tell
protocol PartialBroadcast =
  roles Broadcaster, Receivers[*]
  Broadcaster -> Receivers[0..count] : Message
  Receivers[0..threshold] -> Broadcaster : Ack
```

This example shows bounded ranges for role indices. It models partial broadcasts and threshold acknowledgments.

#### 10) Timing Patterns

Timing patterns provide constructs for building time-aware protocols. All patterns desugar to standard MPST constructs (choice, recursion) and remain verifiable in Lean.

##### Timed Choice

A protocol-visible timeout branches the protocol on deadline expiry:

```tell
protocol TimedRequest =
  roles Client, Server
  timeout 5s Client at
    Server -> Client : Response
  on timeout =>
    Client -> Server : Cancel
```

Use `timeout duration Role at` when deadline expiry is a protocol-visible
outcome. The runtime enforces the deadline. Projection currently rejects
this form until the authority-sensitive lowering rules are complete.

Durations support: `ms` (milliseconds), `s` (seconds), `m` (minutes), `h` (hours).

##### Liveness Pattern

The old `heartbeat` surface is removed from the proof-backed DSL. Model
connection liveness with explicit protocol-visible timeouts plus ordinary
messages:

```tell
protocol Liveness =
  roles Alice, Bob
  Alice -> Bob : Ping
  timeout 1s Bob at
    Bob -> Alice : Pong
  on timeout =>
    Bob -> Alice : Disconnect
```

This keeps liveness handling inside the current verified surface. If you only
need an operational transport hint rather than a protocol branch, use
`runtime_timeout` sender metadata instead.

##### Runtime Timeout Metadata

Record metadata can carry transport-level timeout hints:

```tell
protocol TimedOps =
  roles Client, Server
  Client { runtime_timeout : 5s }
    -> Server : Request
  Server -> Client : Response
```

Unlike `timeout ... on timeout ...`, this metadata does not change the session
type. It is a hint to the transport layer and is not verified in Lean. Use it
for operational timeouts when you do not want the protocol to branch on
timeout.

#### 11) Proof Bundles and Semantic Statements

`proof_bundle` declarations define capability sets. `protocol ... requires ...`
selects the bundles required by a protocol.

```tell
proof_bundle DelegationBase version "1.0.0" issuer "did:example:issuer" constraint "fresh_nonce" requires [delegation, guard_tokens]
proof_bundle KnowledgeBase requires [knowledge_flow]

protocol TransferFlow requires DelegationBase, KnowledgeBase =
  roles Coordinator, Worker
  let receipt = transfer Session from Coordinator to Worker
  publish receipt as DelegationRecorded
  materialize delegationProof from DelegationRecorded
  handoff acceptInvite to Worker with receipt
  Coordinator -> Worker : Commit
```

The parser stores bundle declarations and required bundle names in typed choreography metadata. Bundle records include optional `version`, `issuer`, and repeated `constraint` fields.

Validation fails on duplicate bundles and missing required bundles. If
`requires` is omitted and bundle coverage is unambiguous, the parser can infer
required bundles from the semantic statements that remain in the DSL surface.

Legacy protocol-machine-core statements such as `acquire`, `fork`, `join`,
`delegate`, and `tag` are removed from the proof-backed DSL and are rejected
fail closed. Keep those instructions in the runtime model rather than in
choreography source.

The accepted DSL still includes protocol-visible semantic statements such as
`publish`, `materialize`, `handoff`, `dependent work`, `begin`, `await`, and
`resolve`.

#### 12) Authority and Failure Surface

The authority/failure additions keep the language expression-oriented and
Elm/PureScript-like while making protocol-critical host decisions explicit.

##### Nominal Effect Interfaces and `uses`

```tell
effect Runtime
  authoritative ready : Session -> Result CommitError ReadyWitness
  {
    class : authoritative
    progress : may_block
    region : fragment
    agreement_use : required
    reentrancy : reject_same_fragment
  }
  observe watchPresence : Session -> PresenceView
  {
    class : observational
    progress : immediate
    region : session
    agreement_use : forbidden
    reentrancy : allow
  }
  command cancel : Session -> Result CancelError CancelReceipt
  {
    class : best_effort
    progress : immediate
    region : session
    agreement_use : required
    reentrancy : allow
  }

effect Audit
  command record : AuditEvent -> Unit
  {
    class : best_effort
    progress : immediate
    region : session
    agreement_use : forbidden
    reentrancy : allow
  }

protocol CommitFlow uses Runtime, Audit =
  roles Coordinator, Worker
  authoritative let readiness = check Runtime.ready(session)
  Coordinator -> Worker : Commit
```

Effects are nominal declarations. `uses` makes protocol dependencies explicit.
Only declared effects named in `uses` may be referenced by `check`.

##### `Result` and `Maybe` with `case/of`

```tell
authoritative let readiness = check Runtime.ready(session) in
  case readiness of
    | Ok(witness) =>
        Coordinator -> Worker : Commit(witness)
    | Err(TimedOut) =>
        Coordinator -> Worker : Cancel
```

`Result` and `Maybe` are first-class sum-style forms for protocol-visible
authority checks. Exhaustiveness is required for `Ok`/`Err` and
`Just`/`Nothing`.

##### Custom Unions and Type Aliases

```tell
type CommitError =
  | TimedOut
  | Cancelled
  | InvalidWitness

type alias ReadyWitness =
  { epoch : Int, issuedBy : Role }
```

Use custom unions for typed failure surfaces and aliases for structured
evidence payloads.

##### Evidence Binding with `let`

```tell
observe let presence = observe Runtime.watchPresence(session)
authoritative let readiness = check Runtime.ready(session)
let receipt = transfer Session from Coordinator to Worker
handoff acceptInvite to Worker with receipt
```

Authority queries use explicit `observe let` or `authoritative let` bindings.
Linear transfer receipts still use ordinary `let`.

##### Typed Timeout and Cancellation Blocks

```tell
timeout 5s Coordinator at
  Worker -> Coordinator : Ready(readyWitness)
on timeout =>
  Coordinator -> Worker : Cancel
on cancel =>
  Coordinator -> Worker : Cancelled
```

Use `timeout ... on timeout ... on cancel ...` when timeout and cancellation are
protocol-visible outcomes rather than ambient runtime metadata.

##### Evidence Guards

```tell
choice Coordinator at
  | Commit when check Runtime.ready(session) yields witness =>
      Coordinator -> Worker : Commit(witness)
  | Abort =>
      Coordinator -> Worker : Abort
```

Evidence guards are the concise path for “take this branch only if a typed
authoritative query succeeds and binds evidence”.

##### Linear Single-Use Bindings

```tell
let receipt = transfer Session from Coordinator to Worker
handoff acceptInvite to Worker with receipt
```

Bindings produced by transfer-like authority operations are linear. The
compiler rejects duplicate use and implicit discard.

##### Scoped Bindings with `let ... in`

```tell
authoritative let readiness = check Runtime.ready(session) in
  case readiness of
    | Ok(witness) =>
        Coordinator -> Worker : Commit(witness)
    | Err(reason) =>
        Coordinator -> Worker : Abort(reason)
```

`let ... in` introduces an indented statement block. Use it to keep authority
logic readable without pushing protocol-critical branching back into untyped
host code.

##### No Implicit Default Branches

```tell
authoritative let readiness = check Runtime.ready(session) in
  case readiness of
    | Ok(witness) =>
        Coordinator -> Worker : Commit(witness)
    | Err(TimedOut) =>
        Coordinator -> Worker : Cancel
```

Protocol-critical authority flows do not allow implicit wildcard/default
masking for `Result` and `Maybe`. Missing cases are validation errors.

##### Typed External Query Surface

```tell
authoritative let readiness = check Runtime.ready(session)
```

`check Effect.op(...)` is the canonical language-level form for typed host
queries, and it must be bound with `authoritative let`. Observation-only
queries use `observe let value = observe Effect.op(...)`. These user-facing
forms lower to the same typed runtime/effect boundary used by the host bridge.

##### Choosing Between Timeout Metadata and Timeout Branching

Use `runtime_timeout : 5s` sender metadata for operational transport hints that
do not change the protocol. Use `timeout ... on timeout ... on cancel ...` when
the timeout result must be explicit in the protocol and replay/audit surface.

This lowering preserves statement order and continuation structure. Projection skips extension-local behavior for now and continues projecting the remaining protocol.

#### 13) Child-Effect Aggregation

`compose ...` is a secondary child-effect aggregation clause on an operation.
It does not define distributed agreement by itself. Agreement lives in named
agreement profiles. Child-effect aggregation only says how sibling child
effects roll up underneath that parent agreement.

```tell
agreement_profile PendingPublication
  visibility pending
  rule threshold_participants
  usable_at provisional
  finalized_at finalized
  evidence publication

operation syncMembership(channel : ChannelId) at Worker progress MembershipProgress requires Replay within bounded agreement PendingPublication prestate ChannelMembership compose threshold_success(2) =
  publish SyncQueued(channel)
```

The `compose threshold_success(2)` clause attaches a child-effect rollup policy to the operation without overriding the parent agreement profile.

##### Reusable Domain Agreement Profiles

Domain systems should define their own agreement vocabulary as named profiles
over Telltale's generic core instead of expecting core built-ins such as
`quorum` or `fallback` to carry all the meaning.

```tell
agreement_profile ContactCeremonySoftSafe
  visibility pending
  rule aura_soft_safe
  usable_at soft_safe
  finalized_at finalized
  evidence commit_fact

operation addContact(contactId : String) at Coordinator progress ContactProgress requires Replay within bounded agreement ContactCeremonySoftSafe prestate ContactContext compose threshold_success(3) =
  publish ContactQueued(contactId)
```

This keeps Telltale generic:

- `visibility`, `usable_at`, `finalized_at`, and `evidence` are the core
  semantic vocabulary
- `ContactCeremonySoftSafe` and `aura_soft_safe` are domain-defined names
- `compose ...` only describes child-effect rollup below the agreement
  contract, not the agreement contract itself

The generated Rust surface preserves those domain names through
`Protocol::agreements` and `Protocol::proof_status`, so downstream host code
can keep a natural domain vocabulary without forking the core language model.

#### 14) Role Sets and Topologies

Role sets and topologies are declared at the top level and stored as typed metadata.

```tell
role_set Signers = Alice, Bob, Carol
role_set Quorum = subset(Signers, 0..2)
cluster LocalCluster = Signers, Quorum
ring RingNet = Alice, Bob, Carol
mesh FullMesh = Alice, Bob, Carol
```

These declarations do not change core protocol semantics. They provide structured topology context for tooling and simulation setup.

#### 15) Lowering Diagnostics

Use `choreo-fmt --explain-lowering` to inspect canonical lowering output.

```bash
choreo-fmt --explain-lowering protocol.tell
```

The report includes proof-bundle metadata, inferred requirements, lowered protocol shape, and lint suggestions.

#### 16) String-based Protocol Definition

```rust
use telltale_runtime::compiler::parser::parse_choreography_str;

let protocol = r#"
protocol PingPong =
  roles Alice, Bob
  Alice -> Bob : Ping
  Bob -> Alice : Pong
"#;

let choreography = parse_choreography_str(protocol)?;
```

This parses a string into a `Choreography` AST. It is the entry point for runtime parsing.

Namespaced protocols are expressed with a module header.

```rust
let protocol = r#"
module secure_messaging exposing (EncryptedProtocol)

protocol EncryptedProtocol =
  roles Sender, Receiver
  Sender -> Receiver : SecureMessage
"#;

let choreography = parse_choreography_str(protocol)?;
```

The parser builds the AST for projection, validation, and code generation.

## Implementation Details

### Parser Stack

- Layout preprocessor converts indentation into explicit block delimiters.
- Pest grammar parses the canonical indentation-based syntax after layout normalization.
- Parser module constructs the AST and runs validation.

### Parse Pipeline

1. Preprocess layout (indentation -> `{}`/`()`).
2. Parse with Pest grammar.
3. Build statements and normalize `par` branches into `Parallel`.
4. Resolve `call` references and lower protocol-machine-core statements to `Protocol::Extension`.
5. Build `Choreography` and attach typed proof-bundle metadata.
6. Run semantic checks with `choreography.validate()` when required by your integration.

## API

### Primary Functions

`parse_choreography_str` parses a DSL string into a `Choreography` AST.

```rust
use telltale_runtime::compiler::parser::parse_choreography_str;

let choreo = parse_choreography_str(r#"
protocol Example =
  roles A, B
  A -> B : Hello
"#)?;
```

This example parses a DSL string into a `Choreography`. It uses `parse_choreography_str` directly.

`parse_choreography_file` parses a DSL file from disk.
It expects the canonical `.tell` source extension.

```rust
use std::path::Path;
use telltale_runtime::compiler::parser::parse_choreography_file;

let choreo = parse_choreography_file(Path::new("protocol.tell"))?;
```

This example parses a file path into a `Choreography`. The file must contain a valid DSL definition.

`parse_dsl` is an alias for `parse_choreography_str`.

### Error Handling

```rust
match parse_choreography_str(input) {
    Ok(choreo) => { /* use choreography */ }
    Err(ParseError::UndefinedRole { role, .. }) => {
        eprintln!("Role '{}' used but not declared", role);
    }
    Err(ParseError::DuplicateRole { role, .. }) => {
        eprintln!("Role '{}' declared multiple times", role);
    }
    Err(ParseError::Syntax { span, message }) => {
        eprintln!("Syntax error at {}:{}: {}", span.line, span.column, message);
    }
    Err(e) => {
        eprintln!("Parse error: {}", e);
    }
}
```

This pattern matches common parse errors. It formats diagnostics with the reported context.

## Grammar Details

### Tokens and Keywords

- Identifiers: `[a-zA-Z][a-zA-Z0-9_]*`
- Integers: `[0-9]+`
- Strings: `"..."` (used in `loop while`)
- Keywords: `protocol`, `roles`, `case`, `of`, `choice`, `at`, `loop`,
  `decide`, `by`, `repeat`, `while`, `forever`, `par`, `rec`, `continue`, `call`, `where`,
  `module`, `import`, `exposing`, `proof_bundle`, `requires`, `acquire`, `release`,
  `fork`, `join`, `abort`, `transfer`, `delegate`, `tag`, `check`, `using`, `into`, `as`, `to`, `from`, `with`, `bundle`,
  `version`, `issuer`, `constraint`,
  `role_set`, `subset`, `cluster`, `ring`, `mesh`,
  `let`, `in`, `type`, `alias`, `effect`, `uses`, `timeout`, `on`, `cancel`,
  `when`, `yields`, `heartbeat`, `every`, `on_missing`, `body`,
  `observe`, `authoritative`, `command`, `Ok`, `Err`, `Just`, `Nothing`, `Result`, `Maybe`, `Unit`,
  `publish`, `handoff`, `dependent`, `work`, `required`, `for`,
  `fragment`, `operation`, `within`, `guest`, `runtime`, `entry`
- Operators: `->`, `->*`, `<->`, `:`, `=>`, `=`, `..`, `{}`, `()`, `[]`, `,`, `|`

### Comments

Single-line comments use `--`. Multi-line comments use `{- ... -}`.

```
-- This is a single-line comment

{- This is a
   multi-line comment -}
```

These comments are ignored by the parser. They use the same syntax as Haskell and PureScript.

### Whitespace and Layout

Indentation defines blocks. Use `{}` to force an empty block or to opt out of layout. Parenthesized blocks must be non-empty.

## Validation

The parser validates role declarations and parallel branch structure. `choreography.validate()` also validates proof-bundle declarations, required bundle references, and protocol-machine-core capability coverage.

## Error Messages

Example undefined role error:

```
Undefined role 'Charlie'
  --> input:5:14
    |
  5 |     Alice -> Charlie : Hello
                   ^^^^^^^
```

This error indicates a role that was not declared in `roles`. The location points to the undefined identifier.

Example duplicate role error:

```
Duplicate role declaration 'Alice'
  --> input:3:33
    |
  3 |     roles Alice, Bob, Charlie, Alice
                                      ^^^^^
```

This error indicates that a role name appears more than once. The location points to the duplicate entry.

## Examples

### Simple Two-Party Protocol

```tell
protocol PingPong =
  roles Alice, Bob
  Alice
    -> Bob : Ping
  Bob
    -> Alice : Pong
```

This example shows a simple two role protocol. It uses a single send and reply.

### Protocol with Choice

```tell
protocol Negotiation =
  roles Buyer, Seller

  Buyer
    -> Seller : Offer

  choice Seller at
    | Accept =>
        Seller
          -> Buyer : Accept
    | Reject =>
        Seller
          -> Buyer : Reject
```

This example shows an explicit choice decided by `Seller`. Each branch starts with a send from the deciding role.

### Complex E-Commerce Protocol

```tell
protocol ECommerce =
  roles Buyer, Seller, Shipper

  Buyer
    -> Seller : Inquiry of commerce.Inquiry
  Seller
    -> Buyer : Quote of commerce.Quote

  choice Buyer at
    | Order =>
        Buyer
          -> Seller : Order of commerce.Order
        Seller
          -> Shipper : ShipRequest of logistics.ShipRequest
        Shipper
          -> Buyer : Tracking of logistics.Tracking

        loop decide by Buyer
          Buyer
            -> Shipper : StatusCheck
          Shipper
            -> Buyer : StatusUpdate

        Shipper
          -> Buyer : Delivered
        Buyer
          -> Seller : Confirmation
    | Cancel =>
        Buyer
          -> Seller : Cancel
```

This example combines choice and looping. It models a longer interaction with a buyer controlled loop.

### Parallel Example

```tell
protocol ParallelDemo =
  roles A, B, C, D
  par
    | A -> B : Msg1
    | C -> D : Msg2
```

This example uses `par` with leading `|` branches. Each branch defines a parallel sub protocol.

## Integration

### With Projection

```rust
use telltale_runtime::compiler::{parser, projection};

let choreo = parser::parse_choreography_str(input)?;

for role in &choreo.roles {
    let local_type = projection::project(&choreo, role)?;
    println!("Local type for {}: {:?}", role.name(), local_type);
}
```

This projects the global protocol to a local type for each role. The result can be used for type driven code generation.

### With Code Generation

```rust
use telltale_runtime::compiler::{parser, projection, codegen};

let choreo = parser::parse_choreography_str(input)?;
let mut local_types = Vec::new();

for role in &choreo.roles {
    let local_type = projection::project(&choreo, role)?;
    local_types.push((role.clone(), local_type));
}

let code = codegen::generate_choreography_code(
    &choreo.name.to_string(),
    &choreo.roles,
    &local_types,
);
```

This generates Rust code for the choreography. The generated code includes session types and role APIs.

## Testing

Run parser tests with:

```bash
cargo test --package telltale-runtime parser
```

This runs the parser test suite for the choreography crate. It exercises grammar and layout handling.
