# Choreographic DSL

## Overview

The parser translates protocol specifications from a layout-sensitive, PureScript or Elm inspired DSL into the internal AST (`Choreography` + `Protocol`). The DSL is direct style. Statements are newline separated. Indentation defines blocks.

Empty blocks must use `{}`. The DSL does not use an explicit `end` keyword. A protocol ends when its block ends.

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

This example shows role declarations and message passing with the macro. The macro expects a string literal that contains the DSL.

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

Multiple modules can coexist in separate files. Inside the `choreography!` macro you typically omit the module header, but it is supported in string-based parsing.

### Supported Constructs

#### 1) Send Statement

```rust
Role1 -> Role2 : MessageName
Role1 -> Role2 : MessageWithPayload { data : String, count : Int }
```

The send statement transfers a message from one role to another.

#### 2) Broadcast Statement

```rust
Leader ->* : Announcement
```

Broadcast sends a message to all other roles.

#### 3) Choice Statement (explicit decider)

```rust
case choose Client of
  Buy when (balance > price) ->
    Client -> Server : Purchase
  Cancel ->
    Client -> Server : Cancel
```

The deciding role (`Client`) selects a branch. Guards are optional.

Alias syntax (sugar):

```rust
choice at Client
  Buy ->
    Client -> Server : Purchase
  Cancel ->
    Client -> Server : Cancel
```

This is equivalent to the `case choose` form. It is a lighter syntax for the same choice structure.

#### 4) Loop Statement

```rust
loop decide by Client
  Client -> Server : Request
  Server -> Client : Response
```

This loop continues while the deciding role chooses to continue. The `decide by` form is
desugared to a choice+recursion pattern at parse time. The first message in the loop body
serves as the "continue" signal - when the deciding role sends it, the loop continues.
A synthetic `Done` message is added as the termination signal.

The example above desugars to:

```rust
rec RoleDecidesLoop
  choice at Client
    Request ->
      Client -> Server : Request
      Server -> Client : Response
      continue RoleDecidesLoop
    Done ->
      Client -> Server : Done
```

**Requirement**: The first statement in a `loop decide by Role` body must be a send from
the deciding role. This ensures the decision to continue is fused with the first message,
saving a round trip compared to sending a separate "continue" signal.

This desugaring converts the `RoleDecides` loop into standard multiparty session type
constructs (choice + recursion), enabling formal verification in Lean and compatibility
with standard MPST projection algorithms.

```rust
loop repeat 5
  A -> B : Ping
  B -> A : Pong
```

This loop repeats a fixed number of times. The compiler records the iteration count in the AST.

```rust
loop while "has_more_data"
  A -> B : Data
```

This loop uses a custom condition token. The condition is preserved for tooling and extension passes.

```rust
loop forever
  A -> B : Tick
```

This loop has no exit condition. Use it for persistent background protocols.

#### 5) Parallel Statement (branch adjacency)

Parallel composition is expressed by adjacent `branch` blocks at the same indentation level.

```rust
branch
  A -> B : Msg1
  B -> A : Ack
branch
  C -> D : Msg2
```

A solitary `branch` is a parse error. Use `{}` for an empty branch if needed.

#### 6) Recursion and Calls

```rust
rec Loop
  A -> B : Tick
  continue Loop
```

This defines a recursive label `Loop` and uses `continue Loop` to jump back, modeling unbounded recursion.

```rust
call Handshake
```

This calls another protocol that is in scope. The call target must be defined in the same file or `where` block.

The `continue` keyword is for recursive back-references within a `rec` block. The `call` keyword is for invoking sub-protocols defined in `where` blocks.

#### 7) Protocol Composition (`where` block)

Define and reuse local protocol fragments inside a `where` block.

```rust
protocol Main =
  roles A, B, C
  call Handshake
  call DataTransfer
  A -> C : Done
  where
    protocol Handshake =
      roles A, B
      A -> B : Hello
      B -> A : Hi

    protocol DataTransfer =
      roles A, B
      A -> B : Data
      B -> A : Ack
```

Local protocols can call each other and can be used within choices, loops, and branches.

#### 8) Message Types and Payloads

Message types support generic parameters. Payloads may be written with `{}` or `()`.

```rust
A -> B : Request<String>
B -> A : Response<i32>

A -> B : Data<String, i32, bool>

A -> B : Msg { data : String, count : Int }
B -> A : Result(i : Int, ok : Bool)
```

This section shows generic parameters and payload shapes. Both `{}` and `()` forms are accepted.

#### 9) Dynamic Role Count Support

Dynamic role counts are supported via wildcard and symbolic parameters.

```rust
protocol ThresholdProtocol =
  roles Coordinator, Signers[*]
  Coordinator -> Signers[*] : Request
  Signers[0..threshold] -> Coordinator : Response
```

This example uses a wildcard role family. It also uses a symbolic bound in the role index.

```rust
protocol ConsensusProtocol =
  roles Leader, Followers[N]
  Leader -> Followers[*] : Proposal
  Followers[i] -> Leader : Vote
```

This example mixes a named count with index variables. It enables parameterized protocols.

```rust
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

```rust
protocol TimedRequest =
  roles Client, Server
  Client -> Server : Request
  timed_choice at Client(5s)
    OnTime ->
      Server -> Client : Response
    TimedOut ->
      Client -> Server : Cancel
```

This desugars to a standard `Choice` with a `TimedChoice { duration }` annotation. The timeout is enforced at runtime by the effect interpreter.

Durations support: `ms` (milliseconds), `s` (seconds), `m` (minutes), `h` (hours).

##### Heartbeat Pattern

The heartbeat pattern models connection liveness detection:

```rust
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

```rust
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

##### Runtime Timeout Annotation

The `@runtime_timeout` annotation provides transport-level timeout hints:

```rust
protocol TimedOps =
  roles Client, Server
  @runtime_timeout(5s) Client -> Server : Request
  Server -> Client : Response
```

Unlike `timed_choice`, this annotation does **not** change the session type. It is purely a hint to the transport layer and is not verified in Lean. Use it for operational timeouts when you don't want the protocol to branch on timeout.

#### 11) String-based Protocol Definition

```rust
use rumpsteak_aura_choreography::compiler::parser::parse_choreography_str;

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
3. Build statements and normalize branch adjacency to `Parallel`.
4. Validate roles and resolve `call` references.
5. Build `Choreography`/`Protocol` AST.

## API

### Primary Functions

`parse_choreography_str` parses a DSL string into a `Choreography` AST.

```rust
use rumpsteak_aura_choreography::compiler::parser::parse_choreography_str;

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
use rumpsteak_aura_choreography::compiler::parser::parse_choreography_file;

let choreo = parse_choreography_file(Path::new("protocol.choreo"))?;
```

This example parses a file path into a `Choreography`. The file must contain a valid DSL definition.

`parse_dsl` is an alias for `parse_choreography_str`.

### Error Handling

```rust
match parse_choreography_str(input) {
    Ok(choreo) => { /* use choreography */ }
    Err(ParseError::UndefinedRole(role)) => {
        eprintln!("Role '{}' used but not declared", role);
    }
    Err(ParseError::DuplicateRole(role)) => {
        eprintln!("Role '{}' declared multiple times", role);
    }
    Err(ParseError::Syntax { location, message }) => {
        eprintln!("Syntax error at {}: {}", location, message);
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
  `decide`, `by`, `repeat`, `while`, `forever`, `branch`, `rec`, `call`, `where`,
  `module`, `import`, `exposing`
- Operators: `->`, `->*`, `:`, `{}`, `()`, `,`, `|`

### Comments

Single-line comments use `--`. Multi-line comments use `{- ... -}`.

```
-- This is a single-line comment

{- This is a
   multi-line comment -}
```

### Whitespace and Layout

Indentation defines blocks. Use `{}` to force an empty block or to opt out of layout. Parenthesized blocks must be non-empty.

## Validation

The parser validates that roles are declared, declared roles are unique, and `branch` blocks appear in parallel adjacency. Additional semantic validation is performed by `choreography.validate()`.

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

```rust
protocol PingPong =
  roles Alice, Bob
  Alice -> Bob : Ping
  Bob -> Alice : Pong
```

This example shows a simple two role protocol. It uses a single send and reply.

### Protocol with Choice

```rust
protocol Negotiation =
  roles Buyer, Seller

  Buyer -> Seller : Offer

  case choose Seller of
    Accept ->
      Seller -> Buyer : Accept
    Reject ->
      Seller -> Buyer : Reject
```

This example shows an explicit choice decided by `Seller`. Each branch starts with a send from the deciding role.

### Complex E-Commerce Protocol

```rust
protocol ECommerce =
  roles Buyer, Seller, Shipper

  Buyer -> Seller : Inquiry
  Seller -> Buyer : Quote

  case choose Buyer of
    Order ->
      Buyer -> Seller : Order
      Seller -> Shipper : ShipRequest
      Shipper -> Buyer : Tracking

      loop decide by Buyer
        Buyer -> Shipper : StatusCheck
        Shipper -> Buyer : StatusUpdate

      Shipper -> Buyer : Delivered
      Buyer -> Seller : Confirmation
    Cancel ->
      Buyer -> Seller : Cancel
```

This example combines choice and looping. It models a longer interaction with a buyer controlled loop.

### Parallel Example

```rust
protocol ParallelDemo =
  roles A, B, C, D
  branch
    A -> B : Msg1
  branch
    C -> D : Msg2
```

This example uses adjacent `branch` blocks. Each branch defines a parallel sub protocol.

## Integration

### With Projection

```rust
use rumpsteak_aura_choreography::compiler::{parser, projection};

let choreo = parser::parse_choreography_str(input)?;

for role in &choreo.roles {
    let local_type = projection::project(&choreo, role)?;
    println!("Local type for {}: {:?}", role.name, local_type);
}
```

This projects the global protocol to a local type for each role. The result can be used for type driven code generation.

### With Code Generation

```rust
use rumpsteak_aura_choreography::compiler::{parser, projection, codegen};

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
cargo test --package rumpsteak-aura-choreography parser
```

This runs the parser test suite for the choreography crate. It exercises grammar and layout handling.
