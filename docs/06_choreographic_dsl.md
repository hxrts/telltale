# Choreographic DSL

## Overview

The parser translates a layout-sensitive DSL into the internal AST (`Choreography` and `Protocol`). The DSL is direct style. Statements are newline separated. Indentation defines blocks.

Empty blocks must use `{}`. The DSL does not use an explicit `end` keyword. A protocol ends when its block ends.

The preferred surface style mixes MPST operators with a small functional-language layout:

- keep `->`, `->*`, `|`, `rec`, and `continue` for protocol structure
- use indentation to make control flow visually obvious
- use sender records like `Role { priority = high }`
- use `Message of module.Type` with dotted paths instead of Rust-style `::`

The parser module is located in `rust/choreography/src/compiler/parser/`. It provides an implementation of the choreography DSL parser using Pest plus a layout preprocessor.

## DSL Syntax

```rust
choreography!(r#"
protocol PingPong =
  roles Alice, Bob
  Alice -> Bob : Ping
  Bob -> Alice : Pong
"#);
```

This form passes the DSL as a string literal.

```rust
choreography! {
  protocol PingPong = {
    roles Alice, Bob;
    Alice -> Bob : Ping;
    Bob -> Alice : Pong;
  }
}
```

This form passes the DSL as normal macro tokens. Semicolons are treated as statement separators. Composite operators are normalized for DSL parsing.

### Namespaces

Namespaces are expressed via a module declaration (rather than attributes).

```rust
let protocol = r#"
module threshold_ceremony exposing (ThresholdProtocol)

protocol ThresholdProtocol =
  roles Coordinator, Signers[*]
  Coordinator -> Signers[*] : Request
"#;
```

Multiple modules can coexist in separate files. Inside the `choreography!` macro you typically omit the module header. String-based parsing supports module headers.

The parser recognizes `import` declarations for completeness. Import resolution is not currently applied during compilation.

### Supported Constructs

#### 1) Send Statement

```choreo
Buyer { priority = high }
  -> Seller : Request of shop.Order

Seller
  -> Buyer : Quote of shop.Price
```

The send statement transfers a message from one role to another. Sender metadata is written as a record attached to the sender term. Typed message attachment is written as `Message of module.Type`.

#### 2) Broadcast Statement

```choreo
Leader ->* : Announcement
```

Broadcast sends a message to all other roles.

#### 3) Choice Statement (explicit decider)

```choreo
choice at Client
  | Buy when (balance > price) ->
      Client
        -> Server : Purchase of shop.Order
  | Cancel ->
      Client
        -> Server : Cancel
```

The deciding role (`Client`) selects a branch. Guards are optional. Guard expressions are parsed through a typed predicate IR and must be boolean-like. Valid examples include `ready`, `balance > price`, and `is_open()`.

#### 4) Loop Statement

```choreo
loop decide by Client
  Client -> Server : Request
  Server -> Client : Response
```

This loop continues while the deciding role chooses to continue. The `decide by` form is
desugared to a choice+recursion pattern at parse time. The first message in the loop body
serves as the "continue" signal - when the deciding role sends it, the loop continues.
A synthetic `Done` message is added as the termination signal.

The example above desugars to:

```choreo
rec RoleDecidesLoop
  choice at Client
    Request ->
      Client -> Server : Request
      Server -> Client : Response
      continue RoleDecidesLoop
    Done ->
      Client -> Server : Done
```

Requirement: The first statement in a `loop decide by Role` body must be a send from
the deciding role. This ensures the decision to continue is fused with the first message,
saving a round trip compared to sending a separate "continue" signal.

This desugaring converts the `RoleDecides` loop into standard multiparty session type
constructs (choice + recursion), enabling formal verification in Lean and compatibility
with standard MPST projection algorithms.

```choreo
loop repeat 5
  A -> B : Ping
  B -> A : Pong
```

This loop repeats a fixed number of times. The compiler records the iteration count in the AST.

```choreo
loop while "has_more_data"
  A -> B : Data
```

This loop parses the string content through the same typed predicate IR used by guards. The parser rejects non-boolean predicates such as `"count + 1"` before building the AST.

```choreo
loop forever
  A -> B : Tick
```

This loop has no exit condition. Use it for persistent background protocols.

#### 5) Parallel Statement

```choreo
par
  | A
      -> B : Msg1
    B
      -> A : Ack
  | C
      -> D : Msg2
```

Parallel composition is expressed by `par` with leading `|` branches. A solitary branch is a parse error.

#### 6) Recursion and Calls

```choreo
rec Loop
  A -> B : Tick
  continue Loop
```

This defines a recursive label `Loop` and uses `continue Loop` to jump back, modeling unbounded recursion.

```choreo
call Handshake
```

This calls another protocol that is in scope. The call target must be defined in the same file or `where` block.

The `continue` keyword is for recursive back-references within a `rec` block. The `call` keyword is for invoking sub-protocols defined in `where` blocks.

#### 7) Protocol Composition (`where` block)

Define and reuse local protocol fragments inside a `where` block.

```choreo
protocol Main = {
  roles A, B, C
  call Handshake
  call DataTransfer
  A -> C : Done
}
where {
  protocol Handshake = {
    A -> B : Hello
    B -> A : Hi
  }
  protocol DataTransfer = {
    A -> B : Data
    B -> A : Ack
  }
}
```

Local protocols can call each other and can be used within choices, loops, and branches.

#### 8) Message Types and Payloads

The preferred typed message form is `Message of module.Type`. Dotted paths are preferred in DSL surface syntax.

```choreo
A
  -> B : Request of api.Request
B
  -> A : Response of api.Response

A
  -> B : Msg { data : String, count : Int }
B
  -> A : Result(i : Int, ok : Bool)
```

#### 9) Dynamic Role Count Support

Dynamic role counts are supported via wildcard and symbolic parameters.

```choreo
protocol ThresholdProtocol =
  roles Coordinator, Signers[*]
  Coordinator -> Signers[*] : Request
  Signers[0..threshold] -> Coordinator : Response
```

This example uses a wildcard role family. It also uses a symbolic bound in the role index.

```choreo
protocol ConsensusProtocol =
  roles Leader, Followers[N]
  Leader -> Followers[*] : Proposal
  Followers[i] -> Leader : Vote
```

This example mixes a named count with index variables. It enables parameterized protocols.

```choreo
protocol PartialBroadcast =
  roles Broadcaster, Receivers[*]
  Broadcaster -> Receivers[0..count] : Message
  Receivers[0..threshold] -> Broadcaster : Ack
```

This example shows bounded ranges for role indices. It models partial broadcasts and threshold acknowledgments.

#### 10) Timing Patterns

Timing patterns provide constructs for building time-aware protocols. All patterns desugar to standard MPST constructs (choice, recursion) and remain verifiable in Lean.

##### Timed Choice

A timed choice races an operation against a timeout deadline:

```choreo
protocol TimedRequest =
{
  roles Client, Server
  Client -> Server : Request
  timed_choice at Client(5s) {
    | OnTime -> {
      Server -> Client : Response
    }
    | TimedOut -> {
      Client -> Server : Cancel
    }
  }
}
```

This desugars to a standard `Choice` with a `TimedChoice { duration }` annotation. The timeout is enforced at runtime by the effect interpreter.

Durations support: `ms` (milliseconds), `s` (seconds), `m` (minutes), `h` (hours).

##### Heartbeat Pattern

The heartbeat pattern models connection liveness detection:

```choreo
protocol Liveness =
  roles Alice, Bob
  heartbeat Alice -> Bob every 1s on_missing(3) {
    Bob -> Alice : Disconnect
  } body {
    Alice -> Bob : Ping
    Bob -> Alice : Pong
  }
```

This desugars to a recursive choice:

```choreo
rec HeartbeatLoop
  Alice -> Bob : Heartbeat
  choice at Bob
    Alive ->
      // body
      Alice -> Bob : Ping
      Bob -> Alice : Pong
      continue HeartbeatLoop
    Dead ->
      // on_missing
      Bob -> Alice : Disconnect
```

The `on_missing(3)` parameter indicates how many missed heartbeats before declaring the sender dead. The runtime uses this for timeout calculations.

##### Runtime Timeout Metadata

Record metadata can carry transport-level timeout hints:

```choreo
protocol TimedOps =
  roles Client, Server
  Client { runtime_timeout = 5s }
    -> Server : Request
  Server -> Client : Response
```

Unlike `timed_choice`, this metadata does not change the session type. It is a hint to the transport layer and is not verified in Lean. Use it for operational timeouts when you do not want the protocol to branch on timeout.

#### 11) Proof Bundles and VM-Core Statements

`proof_bundle` declarations define capability sets. `protocol ... requires ...` selects the bundles required by a protocol.

```choreo
proof_bundle DelegationBase version "1.0.0" issuer "did:example:issuer" constraint "fresh_nonce" requires [delegation, guard_tokens]
proof_bundle KnowledgeBase requires [knowledge_flow]

protocol TransferFlow requires DelegationBase, KnowledgeBase = {
  roles A, B
  acquire guard as token
  transfer token to B with bundle DelegationBase
  tag obligation as obligation_tag
  check obligation for B into witness
  A -> B : Commit
}
```

The parser stores bundle declarations and required bundle names in typed choreography metadata. Bundle records include optional `version`, `issuer`, and repeated `constraint` fields.

Validation fails on duplicate bundles, missing required bundles, or missing capability coverage for VM-core statements. If `requires` is omitted and bundle coverage is unambiguous, the parser infers required bundles from VM-core capability demand.

VM-core statements lower to `Protocol::Extension` nodes with annotations. The annotation keys are `vm_core_op`, `required_capability`, and `vm_core_operands`.

```choreo
protocol SpeculativeFlow requires SpecBundle =
  roles A, B
  fork ghost0
  A -> B : Try
  join
```

This lowering preserves statement order and continuation structure. Projection skips extension-local behavior for now and continues projecting the remaining protocol.

#### 12) First-Class Combinators

The DSL includes first-class combinators for common patterns.

```choreo
protocol Combinators =
  roles A, B
  handshake A <-> B : Hello
  quorum_collect A -> B min 2 : Vote
  retry 3 {
    A -> B : Ping
  }
```

`handshake` lowers to a two-message exchange (`Hello` and `HelloAck`). `retry` lowers to a bounded loop. `quorum_collect` lowers to a protocol extension node with combinator annotations.

#### 13) Role Sets and Topologies

Role sets and topologies are declared at the top level and stored as typed metadata.

```choreo
role_set Signers = Alice, Bob, Carol
role_set Quorum = subset(Signers, 0..2)
cluster LocalCluster = Signers, Quorum
ring RingNet = Alice, Bob, Carol
mesh FullMesh = Alice, Bob, Carol
```

These declarations do not change core protocol semantics. They provide structured topology context for tooling and simulation setup.

#### 14) Lowering Diagnostics

Use `choreo-fmt --explain-lowering` to inspect canonical lowering output.

```bash
choreo-fmt --explain-lowering protocol.choreo
```

The report includes proof-bundle metadata, inferred requirements, lowered protocol shape, and lint suggestions.

#### 15) String-based Protocol Definition

```rust
use telltale_choreography::compiler::parser::parse_choreography_str;

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
- Pest grammar parses the canonical brace based syntax.
- Parser module constructs the AST and runs validation.

### Parse Pipeline

1. Preprocess layout (indentation -> `{}`/`()`).
2. Parse with Pest grammar.
3. Build statements and normalize `par` branches into `Parallel`.
4. Resolve `call` references and lower VM-core statements to `Protocol::Extension`.
5. Build `Choreography` and attach typed proof-bundle metadata.
6. Run semantic checks with `choreography.validate()` when required by your integration.

## API

### Primary Functions

`parse_choreography_str` parses a DSL string into a `Choreography` AST.

```rust
use telltale_choreography::compiler::parser::parse_choreography_str;

let choreo = parse_choreography_str(r#"
protocol Example =
  roles A, B
  A -> B : Hello
"#)?;
```

This example parses a DSL string into a `Choreography`. It uses `parse_choreography_str` directly.

`parse_choreography_file` parses a DSL file from disk.

```rust
use std::path::Path;
use telltale_choreography::compiler::parser::parse_choreography_file;

let choreo = parse_choreography_file(Path::new("protocol.choreo"))?;
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
- Keywords: `protocol`, `roles`, `case`, `choose`, `of`, `choice`, `at`, `loop`,
  `decide`, `by`, `repeat`, `while`, `forever`, `branch`, `par`, `rec`, `call`, `where`,
  `module`, `import`, `exposing`, `proof_bundle`, `requires`, `acquire`, `release`,
  `fork`, `join`, `abort`, `transfer`, `delegate`, `tag`, `check`, `using`, `into`,
  `version`, `issuer`, `constraint`, `handshake`, `retry`, `quorum_collect`, `min`,
  `role_set`, `subset`, `cluster`, `ring`, `mesh`
- Operators: `->`, `->*`, `:`, `{}`, `()`, `,`, `|`

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

The parser validates role declarations and parallel branch structure. `choreography.validate()` also validates proof-bundle declarations, required bundle references, and VM-core capability coverage.

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

```choreo
protocol PingPong =
  roles Alice, Bob
  Alice
    -> Bob : Ping
  Bob
    -> Alice : Pong
```

This example shows a simple two role protocol. It uses a single send and reply.

### Protocol with Choice

```choreo
protocol Negotiation =
  roles Buyer, Seller

  Buyer
    -> Seller : Offer

  choice at Seller
    | Accept ->
        Seller
          -> Buyer : Accept
    | Reject ->
        Seller
          -> Buyer : Reject
```

This example shows an explicit choice decided by `Seller`. Each branch starts with a send from the deciding role.

### Complex E-Commerce Protocol

```choreo
protocol ECommerce =
  roles Buyer, Seller, Shipper

  Buyer
    -> Seller : Inquiry of commerce.Inquiry
  Seller
    -> Buyer : Quote of commerce.Quote

  choice at Buyer
    | Order ->
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
    | Cancel ->
        Buyer
          -> Seller : Cancel
```

This example combines choice and looping. It models a longer interaction with a buyer controlled loop.

### Parallel Example

```choreo
protocol ParallelDemo =
  roles A, B, C, D
  par
    | A
        -> B : Msg1
    | C
        -> D : Msg2
```

This example uses `par` with leading `|` branches. Each branch defines a parallel sub protocol.

## Integration

### With Projection

```rust
use telltale_choreography::compiler::{parser, projection};

let choreo = parser::parse_choreography_str(input)?;

for role in &choreo.roles {
    let local_type = projection::project(&choreo, role)?;
    println!("Local type for {}: {:?}", role.name, local_type);
}
```

This projects the global protocol to a local type for each role. The result can be used for type driven code generation.

### With Code Generation

```rust
use telltale_choreography::compiler::{parser, projection, codegen};

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
cargo test --package telltale-choreography parser
```

This runs the parser test suite for the choreography crate. It exercises grammar and layout handling.
