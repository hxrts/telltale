//! Asynchronous Subtyping Example
//!
//! This example demonstrates the SISO (Single Input, Single Output) tree
//! decomposition approach to asynchronous subtyping, based on the paper:
//! "Precise Subtyping for Asynchronous Multiparty Sessions" (POPL 2021)
//!
//! Key concepts:
//! - Synchronous subtyping: covariant outputs, contravariant inputs
//! - Asynchronous subtyping: allows safe message reordering
//! - SISO decomposition: decomposes types into analyzable segments
//!
//! Run with: cargo run --example async_subtyping

use rumpsteak_theory::{
    async_subtype, orphan_free, siso_decompose, sync_subtype, InputTree, OutputTree,
};
use rumpsteak_types::{Label, LocalTypeR};

#[allow(clippy::too_many_lines)]
fn main() {
    println!("=== Asynchronous Subtyping Example ===\n");

    // Example 1: Simple synchronous subtyping
    println!("1. Synchronous Subtyping");
    println!("------------------------");

    let t1 = LocalTypeR::send("B", Label::new("hello"), LocalTypeR::End);
    let t2 = LocalTypeR::send("B", Label::new("hello"), LocalTypeR::End);

    println!("T1: Send hello to B, then End");
    println!("T2: Send hello to B, then End");
    println!("sync_subtype(T1, T2) = {:?}", sync_subtype(&t1, &t2));
    println!();

    // Example 2: Subtyping with different continuations
    println!("2. Subtyping with Continuations");
    println!("-------------------------------");

    let sub = LocalTypeR::send(
        "B",
        Label::new("msg"),
        LocalTypeR::send("B", Label::new("extra"), LocalTypeR::End),
    );

    let sup = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);

    println!("Sub: Send msg, then send extra, then End");
    println!("Sup: Send msg, then End");
    println!("sync_subtype(Sub, Sup) = {:?}", sync_subtype(&sub, &sup));
    println!();

    // Example 3: Choice subtyping (width subtyping)
    println!("3. Choice Width Subtyping");
    println!("-------------------------");

    // Subtype has more choices
    let sub_choice = LocalTypeR::Send {
        partner: "B".to_string(),
        branches: vec![
            (Label::new("option1"), LocalTypeR::End),
            (Label::new("option2"), LocalTypeR::End),
            (Label::new("option3"), LocalTypeR::End),
        ],
    };

    let sup_choice = LocalTypeR::Send {
        partner: "B".to_string(),
        branches: vec![
            (Label::new("option1"), LocalTypeR::End),
            (Label::new("option2"), LocalTypeR::End),
        ],
    };

    println!("Sub: Can send option1, option2, or option3");
    println!("Sup: Can send option1 or option2");
    println!(
        "sync_subtype(Sub, Sup) = {:?}",
        sync_subtype(&sub_choice, &sup_choice)
    );
    println!();

    // Example 4: SISO Decomposition
    println!("4. SISO Decomposition");
    println!("---------------------");

    let complex = LocalTypeR::send(
        "B",
        Label::new("req"),
        LocalTypeR::recv(
            "B",
            Label::new("resp"),
            LocalTypeR::send("B", Label::new("ack"), LocalTypeR::End),
        ),
    );

    println!("Complex type: Send req -> Recv resp -> Send ack -> End");
    match siso_decompose(&complex) {
        Ok(segments) => {
            println!("SISO segments: {} segment(s)", segments.len());
            for (i, seg) in segments.iter().enumerate() {
                println!(
                    "  Segment {}: input={:?}, output={:?}",
                    i + 1,
                    seg.input,
                    seg.output
                );
            }
        }
        Err(e) => println!("SISO decomposition failed: {}", e),
    }
    println!();

    // Example 5: Asynchronous subtyping
    println!("5. Asynchronous Subtyping");
    println!("-------------------------");

    // In async subtyping, message reordering can be safe
    // if there are no dependencies

    let async_sub = LocalTypeR::send(
        "B",
        Label::new("msg1"),
        LocalTypeR::send("C", Label::new("msg2"), LocalTypeR::End),
    );

    let async_sup = LocalTypeR::send(
        "C",
        Label::new("msg2"),
        LocalTypeR::send("B", Label::new("msg1"), LocalTypeR::End),
    );

    println!("Sub: Send msg1 to B, then msg2 to C");
    println!("Sup: Send msg2 to C, then msg1 to B");
    println!("(Different ordering, independent messages)");
    println!(
        "async_subtype(Sub, Sup) = {:?}",
        async_subtype(&async_sub, &async_sup)
    );
    println!();

    // Example 6: Orphan-free check
    println!("6. Orphan-Free Check");
    println!("--------------------");

    let orphan_free_type = LocalTypeR::send(
        "B",
        Label::new("req"),
        LocalTypeR::recv("B", Label::new("resp"), LocalTypeR::End),
    );

    println!("Type: Send req to B, recv resp from B");
    println!("orphan_free(type) = {}", orphan_free(&orphan_free_type));
    println!();

    // Example 7: Input and Output Trees
    println!("7. Input/Output Tree Concepts");
    println!("-----------------------------");

    let recv_only = LocalTypeR::recv(
        "A",
        Label::new("input1"),
        LocalTypeR::recv("A", Label::new("input2"), LocalTypeR::End),
    );

    let send_only = LocalTypeR::send(
        "B",
        Label::new("output1"),
        LocalTypeR::send("B", Label::new("output2"), LocalTypeR::End),
    );

    println!("Receive-only type: Recv input1 -> Recv input2 -> End");
    match siso_decompose(&recv_only) {
        Ok(segments) => {
            for seg in &segments {
                if let InputTree::Recv { partner, branches } = &seg.input {
                    println!(
                        "  Input tree: receives from {} with {} branch(es)",
                        partner,
                        branches.len()
                    );
                }
            }
        }
        Err(e) => println!("  Decomposition error: {}", e),
    }

    println!("Send-only type: Send output1 -> Send output2 -> End");
    match siso_decompose(&send_only) {
        Ok(segments) => {
            for seg in &segments {
                if let OutputTree::Send { partner, branches } = &seg.output {
                    println!(
                        "  Output tree: sends to {} with {} branch(es)",
                        partner,
                        branches.len()
                    );
                }
            }
        }
        Err(e) => println!("  Decomposition error: {}", e),
    }
    println!();

    // Example 8: Recursive type subtyping
    println!("8. Recursive Type Subtyping");
    println!("---------------------------");

    let rec1 = LocalTypeR::mu(
        "loop",
        LocalTypeR::send("B", Label::new("ping"), LocalTypeR::var("loop")),
    );

    let rec2 = LocalTypeR::mu(
        "loop",
        LocalTypeR::send("B", Label::new("ping"), LocalTypeR::var("loop")),
    );

    println!("Rec1: μloop. Send ping -> loop");
    println!("Rec2: μloop. Send ping -> loop");
    println!(
        "sync_subtype(Rec1, Rec2) = {:?}",
        sync_subtype(&rec1, &rec2)
    );
    println!();

    println!("=== Asynchronous Subtyping Demo Complete ===");
}
