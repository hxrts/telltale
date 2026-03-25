//! Asynchronous subtyping example driven from canonical `tell!` protocols.
//!
//! This is a theory-facing example: `tell!` remains the source of truth for the
//! protocol surface, and the example projects the relevant local views into
//! `LocalTypeR` before running the subtyping algorithms.

use anyhow::{anyhow, Result};
use telltale::tell;
use telltale_parser::{ast::convert::local_to_local_r, parse_choreography_str, project};
use telltale_theory::subtyping::{
    async_subtype, orphan_free, siso_decompose, sync_subtype, InputTree, OutputTree,
};
use telltale_types::LocalTypeR;

tell! {
    -- // Simple send from A to B used for equality and recursion examples.
    protocol Hello =
      roles A, B
      A -> B : Hello
}

tell! {
    -- // A sends one message and then an extra continuation message.
    protocol HelloExtra =
      roles A, B
      A -> B : Msg
      A -> B : Extra
}

tell! {
    -- // A chooses among three options sent to B.
    protocol ChoiceWidthSub =
      roles A, B
      choice A at
        | Option1 =>
          A -> B : Option1
        | Option2 =>
          A -> B : Option2
        | Option3 =>
          A -> B : Option3
}

tell! {
    -- // A chooses among two options sent to B.
    protocol ChoiceWidthSup =
      roles A, B
      choice A at
        | Option1 =>
          A -> B : Option1
        | Option2 =>
          A -> B : Option2
}

tell! {
    -- // A sends a request, receives a response, then acknowledges it.
    protocol RequestResponseAck =
      roles A, B
      A -> B : Req
      B -> A : Resp
      A -> B : Ack
}

tell! {
    -- // A sends to B and then to C.
    protocol OrderedSendSub =
      roles A, B, C
      A -> B : Msg1
      A -> C : Msg2
}

tell! {
    -- // A sends to C and then to B.
    protocol OrderedSendSup =
      roles A, B, C
      A -> C : Msg2
      A -> B : Msg1
}

tell! {
    -- // B sends two consecutive inputs to A.
    protocol ReceiveOnly =
      roles A, B
      B -> A : Input1
      B -> A : Input2
}

tell! {
    -- // A sends two consecutive outputs to B.
    protocol SendOnly =
      roles A, B
      A -> B : Output1
      A -> B : Output2
}

tell! {
    -- // Recursive ping loop from A to B with an explicit stop branch.
    protocol RecursivePing =
      roles A, B
      rec loop
        choice A at
          | Continue =>
            A -> B : Ping
            continue loop
          | Stop =>
            A -> B : Stop
}

fn local_view(source: &str, role_name: &str) -> Result<LocalTypeR> {
    let choreography = parse_choreography_str(source)?;
    let role = choreography
        .roles
        .iter()
        .find(|role| role.name() == role_name)
        .ok_or_else(|| anyhow!("role {role_name} not found in choreography"))?;
    let local = project(&choreography, role)?;
    Ok(local_to_local_r(&local)?)
}

#[allow(clippy::too_many_lines)]
fn main() -> Result<()> {
    println!("=== Asynchronous Subtyping Example ===\n");

    println!("1. Synchronous Subtyping");
    println!("------------------------");
    let t1 = local_view(Hello::SOURCE, "A")?;
    let t2 = local_view(Hello::SOURCE, "A")?;
    println!("T1: Send hello to B, then End");
    println!("T2: Send hello to B, then End");
    println!("sync_subtype(T1, T2) = {:?}", sync_subtype(&t1, &t2));
    println!();

    println!("2. Subtyping with Continuations");
    println!("-------------------------------");
    let sub = local_view(HelloExtra::SOURCE, "A")?;
    let sup = local_view(Hello::SOURCE, "A")?;
    println!("Sub: Send msg, then send extra, then End");
    println!("Sup: Send msg, then End");
    println!("sync_subtype(Sub, Sup) = {:?}", sync_subtype(&sub, &sup));
    println!();

    println!("3. Choice Width Subtyping");
    println!("-------------------------");
    let sub_choice = local_view(ChoiceWidthSub::SOURCE, "A")?;
    let sup_choice = local_view(ChoiceWidthSup::SOURCE, "A")?;
    println!("Sub: Can send option1, option2, or option3");
    println!("Sup: Can send option1 or option2");
    println!(
        "sync_subtype(Sub, Sup) = {:?}",
        sync_subtype(&sub_choice, &sup_choice)
    );
    println!();

    println!("4. SISO Decomposition");
    println!("---------------------");
    let complex = local_view(RequestResponseAck::SOURCE, "A")?;
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
        Err(error) => println!("SISO decomposition failed: {error}"),
    }
    println!();

    println!("5. Asynchronous Subtyping");
    println!("-------------------------");
    let async_sub = local_view(OrderedSendSub::SOURCE, "A")?;
    let async_sup = local_view(OrderedSendSup::SOURCE, "A")?;
    println!("Sub: Send msg1 to B, then msg2 to C");
    println!("Sup: Send msg2 to C, then msg1 to B");
    println!("(Different ordering, independent messages)");
    println!(
        "async_subtype(Sub, Sup) = {:?}",
        async_subtype(&async_sub, &async_sup)
    );
    println!();

    println!("6. Orphan-Free Check");
    println!("--------------------");
    let orphan_free_type = local_view(RequestResponseAck::SOURCE, "A")?;
    println!("Type: Send req to B, recv resp from B");
    println!("orphan_free(type) = {}", orphan_free(&orphan_free_type));
    println!();

    println!("7. Input/Output Tree Concepts");
    println!("-----------------------------");
    let recv_only = local_view(ReceiveOnly::SOURCE, "A")?;
    let send_only = local_view(SendOnly::SOURCE, "A")?;

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
        Err(error) => println!("  Decomposition error: {error}"),
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
        Err(error) => println!("  Decomposition error: {error}"),
    }
    println!();

    println!("8. Recursive Type Subtyping");
    println!("---------------------------");
    let rec1 = local_view(RecursivePing::SOURCE, "A")?;
    let rec2 = local_view(RecursivePing::SOURCE, "A")?;
    println!("Rec1: μloop. Select Continue/Stop; Continue sends ping and loops");
    println!("Rec2: μloop. Select Continue/Stop; Continue sends ping and loops");
    println!(
        "sync_subtype(Rec1, Rec2) = {:?}",
        sync_subtype(&rec1, &rec2)
    );
    println!();

    println!("=== Asynchronous Subtyping Demo Complete ===");
    Ok(())
}
