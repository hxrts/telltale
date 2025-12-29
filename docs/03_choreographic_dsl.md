# Choreographic DSL

## Current Status

The parser module is located in `rust/choreography/src/compiler/parser.rs`. It provides an implementation of a choreographic DSL parser. The parser uses the Pest parser generator.

## Overview

The parser translates choreographic protocol specifications from a high-level DSL. The output is the internal AST representation including `Choreography` and `Protocol` types.

## DSL Syntax

The choreographic DSL follows this syntax.

```rust
choreography! {
    MyProtocol {
        roles: Alice, Bob, Carol

        Alice -> Bob: Greeting
        Bob -> Alice: Response

        choice Alice {
            continue: {
                Alice -> Carol: Data
            }
            stop: {
                Alice -> Bob: Done
            }
        }
    }
}
```

This example shows role declarations, message passing, and choice constructs.

### Namespaces

Choreographies can be namespaced to avoid conflicts. Multiple protocols in the same crate can use different namespaces.

```rust
choreography! {
    #[namespace = "threshold_ceremony"]
    ThresholdProtocol {
        roles: Coordinator, Signers[*]
        Coordinator -> Signers[*]: Request
    }
}
```

This generates the protocol within a `threshold_ceremony` module.

Multiple choreographies with different namespaces can coexist in the same crate.

```rust
choreography! {
    #[namespace = "consensus"]
    ConsensusProtocol {
        roles: Leader, Followers[N]
        // protocol body
    }
}

choreography! {
    #[namespace = "recovery"]
    RecoveryProtocol {
        roles: Requester, Guardians[*]
        // protocol body
    }
}
```

Each choreography is defined independently with its own namespace.

### Supported Constructs

#### 1. Send Statement

```rust
Role1 -> Role2: MessageName
Role1 -> Role2: MessageWithPayload(data: String, count: i32)
```

The send statement transfers a message from one role to another.

#### 2. Broadcast Statement

```rust
Leader ->* : Announcement
```

The broadcast statement sends a message to all other roles.

#### 3. Choice Statement

Basic choice syntax allows a role to select between alternatives.

```rust
choice DeciderRole {
    option1: {
        // protocol statements
    }
    option2: {
        // protocol statements
    }
}
```

The deciding role selects one branch.

Guards can be added to choice branches.

```rust
choice Client {
    buy when (balance > price): {
        Client -> Server: Purchase
    }
    cancel: {
        Client -> Server: Cancel
    }
}
```

Guards are optional conditions attached to choice branches. The guard expression is any valid Rust boolean expression.

#### 4. Loop Statement

Loops can have a fixed count.

```rust
loop (count: 5) {
    A -> B: Request
    B -> A: Response
}
```

This executes the body 5 times.

Loops can use role decision.

```rust
loop (decides: Client) {
    Client -> Server: Request
    Server -> Client: Response
}
```

The Client role decides when to exit the loop.

Loops can use custom conditions.

```rust
loop (custom: "has_more_data") {
    A -> B: Data
}
```

Custom conditions are evaluated at runtime.

Loops can be infinite.

```rust
loop {
    A -> B: Tick
}
```

Infinite loops continue until explicitly broken.

#### 5. Parallel Statement

```rust
parallel {
    A -> B: Msg1
|
    C -> D: Msg2
}
```

Parallel composition executes multiple protocols concurrently.

#### 6. Recursive Protocol

```rust
rec LoopLabel {
    A -> B: Data
}
```

Recursive protocols enable unbounded repetition with labeled recursion points.

#### 7. Protocol Composition

Define and reuse protocol fragments.

```rust
choreography! {
    Main {
        roles: A, B, C

        protocol Handshake {
            A -> B: Hello
            B -> A: Hi
        }

        protocol DataTransfer {
            A -> B: Data
            B -> A: Ack
        }

        call Handshake
        call DataTransfer
        A -> C: Done
    }
}
```

Protocol definitions are defined before the main protocol body. They are inlined at call sites with no runtime overhead. Protocols can be called multiple times. Nesting is supported where protocols can call other protocols. Protocols can be used within choice branches and loops.

#### 8. Enhanced Annotations

Annotations provide meta-information for optimization and verification. The system supports statement-level and role-specific annotations.

Statement-level annotations attach metadata to protocol actions.

```rust
[@cost = 100, @priority = "high"]
A -> B: ImportantMessage

[@timeout = 5000, @retry = 3]
B -> C: RetriableMessage
```

These annotations specify cost and timeout values.

Role-specific annotations attach metadata to individual roles.

```rust
Coordinator[@cost = 200] -> Worker[*]: BroadcastMessage
Worker[i][@priority = "low"] -> Coordinator: Response
```

The coordinator role has a cost annotation.

Multiple annotation types can be combined.

```rust
[@critical, @audit_log = "true"]
Client -> Server: AuthRequest

Server[@timeout = 1000] -> Database[@cost = 50]: Query

[@buffered, @compress = "gzip"]
Database -> Server: QueryResult
```

Annotations are accessible through the generated code. Runtime systems can use them for optimization, monitoring, and policy enforcement.

Supported annotation keys include `@cost` for execution cost. Use `@priority` for priority levels. The `@timeout` key specifies timeout in milliseconds. The `@retry` key sets retry count. Mark critical operations with `@critical`. Enable buffering with `@buffered`. Use `@audit_log` for audit logging. The `@compress` key specifies compression type.

#### 9. Type Annotations for Messages

Messages can include explicit type annotations. This specifies the types of data being transmitted.

Simple types use single type parameters.

```rust
A -> B: Request<String>
B -> A: Response<i32>
```

The request carries a String. The response carries an i32.

Multiple types can be specified.

```rust
A -> B: Data<String, i32, bool>
```

This message carries three typed values.

Generic types are supported.

```rust
A -> B: Container<Vec<String>>
B -> A: Result<i32, Error>
```

Nested generics work with arbitrary depth.

Path types can be used for fully qualified types.

```rust
A -> B: Data<std::string::String>
B -> A: Result<std::vec::Vec<i32>>
```

These use the full module path.

Type annotations can be combined with payloads.

```rust
A -> B: Request<String>(data)
B -> A: Response<i32>(result)
```

Type annotations are optional. Messages without types are valid. Annotations are stored as `TokenStream` in the AST. This provides flexibility for code generation.

#### 10. Dynamic Role Count Support

The system supports dynamic role parameterization. Participant counts can be determined at runtime. This enables threshold protocols, consensus algorithms, and scenarios with variable participants.

Runtime-determined role counts use the wildcard syntax.

```rust
choreography! {
    ThresholdProtocol {
        roles: Coordinator, Signers[*]

        Coordinator -> Signers[*]: Request
        Signers[0..threshold] -> Coordinator: Response
    }
}
```

The number of signers is determined at runtime.

Symbolic parameters provide compile-time flexibility.

```rust
choreography! {
    ConsensusProtocol {
        roles: Leader, Followers[N]

        Leader -> Followers[*]: Proposal
        Followers[i] -> Leader: Vote
    }
}
```

The parameter N is resolved during code generation.

Range-based role selection targets subsets of roles.

```rust
choreography! {
    PartialBroadcast {
        roles: Broadcaster, Receivers[*]

        Broadcaster -> Receivers[0..count]: Message
        Receivers[0..threshold] -> Broadcaster: Ack
    }
}
```

Only roles in the specified range participate.

Static arrays use fixed counts.

```rust
choreography! {
    StaticWorkers {
        roles: Master, Worker[3]

        Master -> Worker[0]: Task1
        Master -> Worker[1]: Task2
        Worker[0] -> Master: Result1
    }
}
```

This creates exactly 3 worker roles.

Dynamic role features include runtime role counts using `Worker[*]`. Symbolic parameters use `Worker[N]`. Range expressions use `Worker[0..threshold]`. Wildcard references use `Worker[*]`. Security constraints prevent overflow with a maximum of 10,000 roles. Comprehensive runtime validation ensures safety.

Runtime binding example shows how to use dynamic roles.

```rust
use rumpsteak_aura_choreography::compiler::{parse_choreography_str, codegen::generate_choreography_code_with_dynamic_roles};

let dsl = r#"
choreography Threshold {
    roles: Coordinator, Signers[*];
    Coordinator -> Signers[*]: Request;
}
"#;

let choreo = parse_choreography_str(dsl)?;
let code = generate_choreography_code_with_dynamic_roles(&choreo, &local_types);

let mut runtime = ThresholdRuntime::new();
runtime.bind_role_count("Signers", 5)?;
runtime.map_signers_instances(vec!["alice", "bob", "charlie", "dave", "eve"])?;
```

The generated code includes runtime support for role binding.

#### 11. String-based Protocol Definition

The current implementation uses `parse_choreography_str` to parse protocols. Protocols are defined as string literals. The parser supports namespaces, annotations, and dynamic roles.

Basic usage parses a simple protocol.

```rust
use rumpsteak_aura_choreography::compiler::parser::parse_choreography_str;

let protocol = r#"
    choreography PingPong {
        roles: Alice, Bob;

        Alice -> Bob: Ping;
        Bob -> Alice: Pong;
    }
"#;

let choreography = parse_choreography_str(protocol)?;
```

This creates a PingPong choreography.

Namespaced protocols avoid conflicts.

```rust
let protocol = r#"
    #[namespace = "secure_messaging"]
    choreography EncryptedProtocol {
        roles: Sender, Receiver;

        [@encrypt = "aes256"]
        Sender -> Receiver: SecureMessage;
    }
"#;

let choreography = parse_choreography_str(protocol)?;
```

The namespace isolates this protocol.

Dynamic roles with annotations enable complex protocols.

```rust
let protocol = r#"
    #[namespace = "consensus"]
    choreography ByzantineFaultTolerant {
        roles: Leader, Replicas[*];

        [@phase = "prepare", @timeout = 5000]
        Leader -> Replicas[*]: Prepare;

        Replicas[0..quorum] -> Leader: PrepareOk;
    }
"#;

let choreography = parse_choreography_str(protocol)?;
```

This defines a consensus protocol with timeout annotations.

The parser processes choreographic protocol specifications from strings. It builds AST representation for further processing. Full protocol syntax is supported including annotations and dynamic roles. Detailed error reporting provides span information. Runtime protocol generation and analysis are enabled.

Generated AST can be used for protocol projection to local types. Code generation for session types is supported. Runtime analysis and validation are possible. Dynamic role binding and management are enabled.

## Implementation Details

### Parser Stack

The Pest Grammar is defined in `choreography.pest`. It provides formal grammar definition using PEG syntax. It handles lexing and initial parsing. Comments, whitespace, and various token types are supported.

The Parser Module is in `parser.rs`. It processes Pest parse tree into AST. It validates role declarations. Protocol AST is constructed from statements. Comprehensive error handling is provided.

Error Types include `ParseError` variants. Syntax errors include location information. Undefined role errors are reported. Duplicate role declarations are caught. Invalid message or condition formats are detected.

### Parse Pipeline

The parse pipeline transforms input through several stages.

Input String is parsed by Pest Grammar. This produces a Parse Tree of Pest Pairs. Statement AST Construction builds intermediate structures. Role Validation checks all roles are declared. Protocol AST Generation creates the final tree. The Choreography Object is returned.

## API

### Primary Functions

The function `parse_choreography_str` parses a choreographic DSL string into a Choreography AST.

```rust
use rumpsteak_aura_choreography::compiler::parser::parse_choreography_str;

let choreo = parse_choreography_str(r#"
choreography Example {
    roles: A, B
    A -> B: Hello
}
"#)?;
```

This creates a choreography from a string literal.

The function `parse_choreography_file` parses a choreographic DSL from a file.

```rust
use std::path::Path;
use rumpsteak_aura_choreography::compiler::parser::parse_choreography_file;

let choreo = parse_choreography_file(Path::new("protocol.choreo"))?;
```

This reads and parses a file.

The function `parse_dsl` is an alias for `parse_choreography_str`. It provides compatibility with older code.

### Error Handling

The parser provides detailed error messages.

```rust
match parse_choreography_str(input) {
    Ok(choreo) => {
        // Use choreography
    }
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

Error handling catches different error types.

## Grammar Details

### Tokens

Identifiers match `[a-zA-Z][a-zA-Z0-9_]*`. Integers match `[0-9]+`. Strings match `"..."` for custom conditions.

Keywords include `choreography`, `roles`, `choice`, `loop`, `parallel`, and `rec`. Additional keywords are `count`, `decides`, and `custom`.

Operators include `->` for send. The `->*` operator indicates broadcast. Other operators are `:`, `,`, `{`, `}`, `(`, `)`, and `|`.

### Comments

Single-line comments use `//`. Multi-line comments use `/* comment */`.

### Whitespace

Whitespace includes spaces, tabs, and newlines. It is ignored and can be used freely for formatting.

## Validation

The parser performs validations during parsing.

Role Declaration validation ensures all used roles are declared in the `roles:` section. Role Uniqueness validation prevents roles from being declared multiple times. Syntax Correctness validation ensures all statements follow the grammar. Non-Empty Roles validation requires at least one role declaration.

Additional semantic validation is performed by the `choreography.validate()` method after parsing.

## Error Messages

The parser provides Rust-style error messages with precise span information.

Features include line and column numbers for exact error location. Code snippets show the problematic line. Visual indicators underline the specific error location. Contextual messages provide clear explanations.

Example error output shows undefined role.

```
Undefined role 'Charlie'
  --> input:5:14
    |
  5 |     Alice -> Charlie: Hello
                   ^^^^^^^
```

This indicates where Charlie is used but not declared.

Example error for duplicate role.

```
Duplicate role declaration 'Alice'
  --> input:3:33
    |
  3 |     roles: Alice, Bob, Charlie, Alice
                                      ^^^^^
```

This shows Alice declared twice.

Error types include `ParseError::UndefinedRole` for roles used but not declared. `ParseError::DuplicateRole` handles roles declared more than once. `ParseError::UndefinedProtocol` catches protocols called but not defined. `ParseError::DuplicateProtocol` detects protocols defined multiple times. `ParseError::Syntax` reports grammar or syntax violations. `ParseError::InvalidCondition` handles loop condition problems. `ParseError::InvalidMessage` reports message format issues. `ParseError::Pest` captures low-level parsing errors.

See `rust/choreography/examples/error_demo.rs` for more examples.

## Examples

### Simple Two-Party Protocol

```rust
choreography! {
    PingPong {
        roles: Alice, Bob

        Alice -> Bob: Ping
        Bob -> Alice: Pong
    }
}
```

This creates a simple ping-pong protocol.

### Protocol with Choice

```rust
choreography! {
    Negotiation {
        roles: Buyer, Seller

        Buyer -> Seller: Offer

        choice Seller {
            accept: {
                Seller -> Buyer: Accept
            }
            reject: {
                Seller -> Buyer: Reject
            }
        }
    }
}
```

The seller chooses to accept or reject.

### Complex E-Commerce Protocol

```rust
choreography! {
    ECommerce {
        roles: Buyer, Seller, Shipper

        Buyer -> Seller: Inquiry
        Seller -> Buyer: Quote

        choice Buyer {
            order: {
                Buyer -> Seller: Order
                Seller -> Shipper: ShipRequest
                Shipper -> Buyer: Tracking

                loop (decides: Buyer) {
                    Buyer -> Shipper: StatusCheck
                    Shipper -> Buyer: StatusUpdate
                }

                Shipper -> Buyer: Delivered
                Buyer -> Seller: Confirmation
            }
            cancel: {
                Buyer -> Seller: Cancel
            }
        }
    }
}
```

This protocol includes choice, loops, and multiple roles.

## Integration

### With Projection

Parse and project to local types.

```rust
use rumpsteak_aura_choreography::compiler::{parser, projection};

let choreo = parser::parse_choreography_str(input)?;

for role in &choreo.roles {
    let local_type = projection::project(&choreo, role)?;
    println!("Local type for {}: {:?}", role.name, local_type);
}
```

Each role gets its own local type.

### With Code Generation

Parse and generate Rumpsteak session types.

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

This generates session types from the choreography.

## Testing

The parser includes comprehensive test coverage.

Basic parsing tests cover simple protocols with sends. Choice construct tests include 2-way, 3-way, and nested choices. Loop construct tests cover all condition types. Parallel composition tests handle multiple concurrent branches. Error case tests validate undefined roles, duplicate roles, and syntax errors. Edge case tests check empty protocols, whitespace variations, and comments. Integration tests verify interaction with projection and validation.

Run tests with this command.

```bash
cargo test --package rumpsteak-aura-choreography parser
```

This executes all parser tests.
