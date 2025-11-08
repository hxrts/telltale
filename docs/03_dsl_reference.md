
# Choreographic DSL Parser Architecture

## Current Status

The parser module (`choreography/src/compiler/parser.rs`) provides an implementation of a choreographic DSL parser using the Pest parser generator.


## Overview

The parser translates choreographic protocol specifications from a high-level DSL into the internal AST representation (`Choreography`, `Protocol`, etc.).

## Choreographic DSL Syntax

The choreographic DSL follows this syntax:

```rust
choreography MyProtocol {
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
```

### Supported Constructs

#### 1. Send Statement
```rust
Role1 -> Role2: MessageName
Role1 -> Role2: MessageWithPayload(data: String, count: i32)
```

#### 2. Broadcast Statement
```rust
Leader ->* : Announcement
```

#### 3. Choice Statement

Basic choice:
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

With guards:
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

Guards are optional conditions that can be attached to choice branches. The guard expression is any valid Rust boolean expression.

#### 4. Loop Statement

With count:
```rust
loop (count: 5) {
    A -> B: Request
    B -> A: Response
}
```

With role decision:
```rust
loop (decides: Client) {
    Client -> Server: Request
    Server -> Client: Response
}
```

With custom condition:
```rust
loop (custom: "has_more_data") {
    A -> B: Data
}
```

Without condition (infinite):
```rust
loop {
    A -> B: Tick
}
```

#### 5. Parallel Statement
```rust
parallel {
    A -> B: Msg1
|
    C -> D: Msg2
}
```

#### 6. Recursive Protocol
```rust
rec LoopLabel {
    A -> B: Data
}
```

#### 7. Protocol Composition (Sub-protocols)

Define and reuse protocol fragments

```rust
choreography Main {
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
```

Protocol definitions are:
- Defined before the main protocol body
- Inlined at call sites (no runtime overhead)
- Can be called multiple times
- Can be nested (protocols can call other protocols)
- Can be used within choice branches, loops, etc.

#### 8. Annotations

Annotations provide hints for optimization, verification, and other meta-information about choreographies and statements.

**Choreography-level annotations:**
```rust
@optimize
choreography Simple {
    roles: A, B
    A -> B: Msg
}
```

**With arguments:**
```rust
@optimize(inline, buffer_size=1024)
choreography Optimized {
    roles: A, B
    A -> B: Msg
}
```

**Multiple annotations:**
```rust
@optimize(inline)
@verify(deadlock_free)
@parallel
choreography Production {
    roles: A, B, C
    A -> B: Start
    B -> C: Forward
}
```

**Statement-level annotations:**
```rust
choreography Annotated {
    roles: A, B
    
    @critical
    A -> B: ImportantMsg
    
    @buffered(size=10)
    B -> A: Response
}
```

Annotations are stored in the `Choreography.attrs` HashMap as key-value pairs:
- Simple annotations (`@optimize`) map to `"true"`
- Annotations with arguments (`@optimize(inline, buffer_size=1024)`) map to `"inline,buffer_size=1024"`

**Common annotation types:**
- `@optimize` - Performance optimization hints (inline, buffer_size, etc.)
- `@verify` - Verification properties (deadlock_free, liveness, etc.)
- `@parallel` - Enable parallel execution
- `@critical` - Mark critical sections
- `@buffered` - Buffering configuration

#### 9. Type Annotations for Messages

Messages can include explicit type annotations to specify the types of data being transmitted.

**Simple types:**
```rust
choreography TypedMessages {
    roles: A, B
    
    A -> B: Request<String>
    B -> A: Response<i32>
}
```

**Multiple types:**
```rust
A -> B: Data<String, i32, bool>
```

**Generic types:**
```rust
A -> B: Container<Vec<String>>
B -> A: Result<i32, Error>
```

**Path types:**
```rust
A -> B: Data<std::string::String>
B -> A: Result<std::vec::Vec<i32>>
```

**Type annotations with payloads:**
```rust
A -> B: Request<String>(data)
B -> A: Response<i32>(result)
```

Type annotations are:
- Optional - messages without types are still valid
- Stored as `TokenStream` in the AST for flexibility
- Can be nested generics with arbitrary depth
- Support standard Rust type syntax including paths

#### 10. Parameterized Roles

**Status: ✅ Fully Implemented**

Roles can be parameterized to represent role arrays or families of participants. The system supports concrete array sizes, concrete indices, and symbolic parameters.

**Concrete array with indexed access:**
```rust
choreography WorkerPool {
    roles: Master, Worker[3]
    
    Master -> Worker[0]: Task
    Worker[0] -> Master: Result
}
```

**Multiple indexed workers:**
```rust
choreography MultipleWorkers {
    roles: Coordinator, Worker[5]
    
    Coordinator -> Worker[0]: Init
    Coordinator -> Worker[1]: Init
    Coordinator -> Worker[2]: Init
    Worker[0] -> Coordinator: Done
}
```

**Symbolic parameters:**
```rust
choreography SymbolicParam {
    roles: Leader, Follower[N]
    
    Leader -> Follower[i]: Command
    Follower[i] -> Leader: Ack
}
```

**Features:**
- ✅ Concrete array sizes (e.g., `Worker[3]` declares an array of 3 workers)
- ✅ Concrete indices (e.g., `Worker[0]`, `Worker[1]`)
- ✅ Symbolic parameters (e.g., `Worker[N]` where N is a parameter)
- ✅ Symbolic indices (e.g., `Worker[i]` in protocol statements)
- ✅ Full validation with role family matching
- ✅ Projection to local types for each role
- ✅ Multiple independent role families

**Example Usage:**
```rust
use rumpsteak_choreography::compiler::{parse_dsl, project};

let dsl = r#"
choreography Test {
    roles: Coordinator, Worker[3]
    
    Coordinator -> Worker[0]: Task
    Worker[0] -> Coordinator: Result
}
"#;

let choreo = parse_dsl(dsl)?;
choreo.validate()?;

for role in &choreo.roles {
    let local_type = project(&choreo, role)?;
    // Use local_type for code generation
}
```

#### 11. Macro Support for Inline Protocols

The `choreography!` procedural macro enables embedding choreographic protocols directly in Rust code.

**Basic usage:**
```rust
use rumpsteak_macros::choreography;

choreography! {
    PingPong {
        roles: Alice, Bob
        
        Alice -> Bob: Ping
        Bob -> Alice: Pong
    }
}
```

**String literal syntax (DSL integration):**
```rust
choreography! {
    r#"
    choreography Example {
        roles: A, B, C
        
        A -> B: Request
        B -> C: Forward
        C -> A: Response
    }
    "#
}
```

The macro:
- Parses choreographic protocol specifications
- Generates role structs and message types
- Creates session types for each role
- Provides setup functions for instantiation
- Supports both inline and string literal syntaxes
- Enables compile-time validation of protocols

**Generated code includes:**
- Role type definitions implementing the `Role` trait
- Message type definitions implementing the `Message` trait
- Session type definitions for type-safe communication
- Setup function for creating protocol instances

This allows protocols to be defined inline and used with full type safety and compile-time checking.

## Implementation Details

### Parser Stack

1. **Pest Grammar** (`choreography.pest`)
   - Formal grammar definition using PEG syntax
   - Handles lexing and initial parsing
   - Supports comments, whitespace, and various token types

2. **Parser Module** (`parser.rs`)
   - Processes Pest parse tree into AST
   - Validates role declarations
   - Constructs Protocol AST from statements
   - Comprehensive error handling

3. **Error Types** (`ParseError`)
   - Syntax errors with location information
   - Undefined role errors
   - Duplicate role declarations
   - Invalid message or condition formats

### Parse Pipeline

```
Input String
    ↓
Pest Grammar Parsing
    ↓
Parse Tree (Pest Pairs)
    ↓
Statement AST Construction
    ↓
Role Validation
    ↓
Protocol AST Generation
    ↓
Choreography Object
```

## API

### Primary Functions

#### `parse_choreography_str(input: &str) -> Result<Choreography, ParseError>`
Parse a choreographic DSL string into a Choreography AST.

```rust
use rumpsteak_choreography::compiler::parser::parse_choreography_str;

let choreo = parse_choreography_str(r#"
choreography Example {
    roles: A, B
    A -> B: Hello
}
"#)?;
```

#### `parse_choreography_file(path: &Path) -> Result<Choreography, ParseError>`
Parse a choreographic DSL from a file.

```rust
use std::path::Path;
use rumpsteak_choreography::compiler::parser::parse_choreography_file;

let choreo = parse_choreography_file(Path::new("protocol.choreo"))?;
```

#### `parse_dsl(input: &str) -> Result<Choreography, ParseError>`
Alias for `parse_choreography_str` for compatibility.

### Error Handling

The parser provides detailed error messages:

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

## Grammar Details

### Tokens

- Identifiers: `[a-zA-Z][a-zA-Z0-9_]*`
- Integers: `[0-9]+`
- Strings: `"..."` (for custom conditions)
- Keywords: `choreography`, `roles`, `choice`, `loop`, `parallel`, `rec`, `count`, `decides`, `custom`
- Operators: `->` (send), `->*` (broadcast), `:`, `,`, `{`, `}`, `(`, `)`, `|`

### Comments

- Single-line: `// comment`
- Multi-line: `/* comment */`

### Whitespace

Whitespace (spaces, tabs, newlines) is ignored and can be used freely for formatting.

## Validation

The parser performs the following validations:

1. Role Declaration: All used roles must be declared in the `roles:` section
2. Role Uniqueness: Roles cannot be declared multiple times
3. Syntax Correctness: All statements must follow the grammar
4. Non-Empty Roles: At least one role must be declared

Additional semantic validation is performed by the `choreography.validate()` method after parsing.

## Error Messages

The parser now provides Rust-style error messages with precise span information.

### Features

- **Line and column numbers**: Exact location of errors
- **Code snippets**: Shows the problematic line
- **Visual indicators**: Underlines the specific error location
- **Contextual messages**: Clear explanation of what went wrong

### Example Error Output

```
Undefined role 'Charlie'
  --> input:5:14
    |
  5 |     Alice -> Charlie: Hello
                   ^^^^^^^
```

```
Duplicate role declaration 'Alice'
  --> input:3:33
    |
  3 |     roles: Alice, Bob, Charlie, Alice
                                      ^^^^^
```

### Error Types

- `ParseError::UndefinedRole`: Role used but not declared
- `ParseError::DuplicateRole`: Role declared more than once
- `ParseError::UndefinedProtocol`: Protocol called but not defined
- `ParseError::DuplicateProtocol`: Protocol defined multiple times
- `ParseError::Syntax`: Grammar or syntax violations
- `ParseError::InvalidCondition`: Loop condition problems
- `ParseError::InvalidMessage`: Message format issues
- `ParseError::Pest`: Low-level parsing errors

See `choreography/examples/error_demo.rs` for more examples.

## Examples

### Simple Two-Party Protocol

```rust
let input = r#"
choreography PingPong {
    roles: Alice, Bob
    
    Alice -> Bob: Ping
    Bob -> Alice: Pong
}
"#;

let choreo = parse_choreography_str(input)?;
assert_eq!(choreo.roles.len(), 2);
```

### Protocol with Choice

```rust
let input = r#"
choreography Negotiation {
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
"#;

let choreo = parse_choreography_str(input)?;
```

### Complex E-Commerce Protocol

```rust
let input = r#"
choreography ECommerce {
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
"#;

let choreo = parse_choreography_str(input)?;
```

## Integration

### With Projection

Parse and project to local types:

```rust
use rumpsteak_choreography::compiler::{parser, projection};

let choreo = parser::parse_choreography_str(input)?;

for role in &choreo.roles {
    let local_type = projection::project(&choreo, role)?;
    println!("Local type for {}: {:?}", role.name, local_type);
}
```

### With Code Generation

Parse and generate Rumpsteak session types:

```rust
use rumpsteak_choreography::compiler::{parser, projection, codegen};

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

The parser includes comprehensive test coverage:

- **Basic parsing**: Simple protocols with sends
- **Choice constructs**: 2-way, 3-way, and nested choices
- **Loop constructs**: All condition types
- **Parallel composition**: Multiple concurrent branches
- **Error cases**: Undefined roles, duplicate roles, syntax errors
- **Edge cases**: Empty protocols, whitespace variations, comments
- **Integration**: With projection and validation

Run tests with:
```bash
cargo test --package rumpsteak-choreography parser
```
