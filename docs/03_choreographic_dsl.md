# Choreographic DSL

## Current Status

The parser module is located in `rust/choreography/src/compiler/parser.rs`. It provides an implementation of the choreography DSL parser using Pest plus a layout preprocessor.

## Overview

The parser translates protocol specifications from a layout‑sensitive, PureScript/Elm‑inspired DSL into the internal AST (`Choreography` + `Protocol`). The DSL is **direct style**: statements are newline‑separated and indentation defines blocks.

## DSL Syntax

```rust
choreography! {
    protocol PingPong =
      roles Alice, Bob
      Alice -> Bob : Ping
      Bob -> Alice : Pong
}
```

This example shows role declarations and message passing.

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

Multiple modules can coexist in separate files. Inside the `choreography!` macro you typically omit the module header, but it is supported in string‑based parsing.

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

#### 4) Loop Statement

```rust
loop decide by Client
  Client -> Server : Request
  Server -> Client : Response
```

```rust
loop repeat 5
  A -> B : Ping
  B -> A : Pong
```

```rust
loop while "has_more_data"
  A -> B : Data
```

```rust
loop forever
  A -> B : Tick
```

#### 5) Parallel Statement (branch adjacency)

Parallel composition is expressed by **adjacent** `branch` blocks at the same indentation level.

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
  call Loop
```

```rust
call Handshake
```

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

#### 9) Dynamic Role Count Support

Dynamic role counts are supported via wildcard and symbolic parameters.

```rust
protocol ThresholdProtocol =
  roles Coordinator, Signers[*]
  Coordinator -> Signers[*] : Request
  Signers[0..threshold] -> Coordinator : Response
```

```rust
protocol ConsensusProtocol =
  roles Leader, Followers[N]
  Leader -> Followers[*] : Proposal
  Followers[i] -> Leader : Vote
```

```rust
protocol PartialBroadcast =
  roles Broadcaster, Receivers[*]
  Broadcaster -> Receivers[0..count] : Message
  Receivers[0..threshold] -> Broadcaster : Ack
```

#### 10) String‑based Protocol Definition

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

- **Layout preprocessor** converts indentation into explicit block delimiters.
- **Pest grammar** parses the canonical (brace‑based) syntax.
- **Parser module** constructs the AST and runs validation.

### Parse Pipeline

1. Preprocess layout (indentation → `{}`/`()`).
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

`parse_choreography_file` parses a DSL file from disk.

```rust
use std::path::Path;
use rumpsteak_aura_choreography::compiler::parser::parse_choreography_file;

let choreo = parse_choreography_file(Path::new("protocol.choreo"))?;
```

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

Single‑line comments use `//`. Multi‑line comments use `/* ... */`.

### Whitespace and Layout

Indentation defines blocks. Use `{}` to force an empty block or to opt out of layout. Parenthesized blocks must be non‑empty.

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

Example duplicate role error:

```
Duplicate role declaration 'Alice'
  --> input:3:33
    |
  3 |     roles Alice, Bob, Charlie, Alice
                                      ^^^^^
```

## Examples

### Simple Two‑Party Protocol

```rust
protocol PingPong =
  roles Alice, Bob
  Alice -> Bob : Ping
  Bob -> Alice : Pong
```

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

### Complex E‑Commerce Protocol

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

### Parallel Example

```rust
protocol ParallelDemo =
  roles A, B, C, D
  branch
    A -> B : Msg1
  branch
    C -> D : Msg2
```

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

## Testing

Run parser tests with:

```bash
cargo test --package rumpsteak-aura-choreography parser
```
