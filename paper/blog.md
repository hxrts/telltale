# Developing Theory Outside Your Expertise with AI and Formal Verification

I recently completed a series of papers on multiparty session types. This is a subfield of programming language theory concerned with proving distributed protocols correct at compile time. I came to this problem from a background in distributed systems and statistical mechanics, but I have no formal training in type theory.

This post describes the methodology I used to make theoretical contributions in a new field. The approach combines AI tools for exploration and exposition with formal verification in Lean4 for correctness. Neither alone would have been sufficient.

## The Challenge

Entering an established research field as an outsider carries risks. You might reinvent known results. You might miss relevant prior work. You might make subtle errors that experts would catch immediately. The norms, conventions, notation, and proof styles are unfamiliar.

There is also an opportunity. Outsiders can find structural parallels that insiders overlook. A fresh perspective can identify gaps that have become invisible through habituation.

The question is how to capture the upside while mitigating the risks.

## Problem Selection

Not every problem is suitable for this kind of approach. I wanted to work on multiparty session types foremost because I found the idea compelling, but also because it seemed ammenable to making theoretical headway.

The community is small. There are perhaps a few dozen active researchers, this means there is room for contribution. It also means the experts are accessible and the literature is tractable.

Session types are a branch of type theory, meaning problems are amenable to machine verification using proof assistants. This provides hard guardrails on correctness that do not depend on my expertise.

Recent work had revealed vulnerabilities. A 2025 paper found flaws in foundational proofs from 2016. This indicated that even experts struggle with the complexity of asynchronous buffered semantics. It also meant the field was actively revisiting its foundations.

The problem was adjacent to my expertise. Distributed systems are what session types describe. Physics provided mathematical tools I could apply, so I wasn't starting from zero.

## Guardrails with Lean4

LLMs have a tendency to generate plausible mathematics that is subtly wrong, and although the accuracy of AI systems has gotten *much* better in the last several months, they are far from perfect. They skip steps that do not actually follow. They confidently assert non-theorems. This is dangerous when working in an unfamiliar domain where you cannot easily spot errors.

Proof assistants like Lean4 provide guardrails. Either the proof compiles or it does not. This inverts the trust model. I do not need to fully understand every intermediate step if the proof checks. The compiler becomes the arbiter of correctness.

Lean4 specifically was important because it has the ergonomics of a programming language. Earlier proof assistants have steep learning curves and unfamiliar syntax. Lean4 feels like writing functional code. This made it accessible to someone without formal verification training. It also made AI assistance more effective, since the models have seen more code than proof scripts.

The workflow becomes iterative. AI proposes proof strategies and fills in details. Lean accepts or rejects them. When Lean rejects, AI helps interpret the error messages and suggests fixes. This cycle continues until the proof compiles.

That said, Lean has escape hatches that bypass verification. The `sorry` tactic admits any goal without proof. The `axiom` command introduces unproven assumptions. The `unsafe` and `partial` keywords disable termination checking. AI will happily suggest these to make errors disappear. You must be disciplined. Treat them as technical debt. Eliminate them before claiming results.

## The Representation Problem

Formal verification guarantees your proofs are correct. But correct about what?

The hard problem is not the proof. It is the model. Your formalization must faithfully represent the real system. In distributed systems this means asking hard questions. Do your message semantics match real networks? Do your failure modes capture real crashes? Does your timing model reflect actual asynchrony?

Lean cannot help here. It checks internal consistency. It cannot check external fidelity. This is where domain expertise becomes essential. You need to know what matters to model and what is safe to abstract away.

The physics analogies helped with this. If the formalization has the same structure as a well-understood physical system, that provides evidence the model is sensible. It is not proof. But it is a sanity check that pure formalism cannot provide.

## Finding Analogies

I deliberately looked for connections to physics. This was not an accident or a late discovery. It was part of the methodology from the start.

The reason is practical. I could reason confidently about Lyapunov functions, gauge symmetry, and coarse-graining. These are tools I learned in statistical mechanics. I could not reason as confidently about session type metatheory. By finding structural parallels, I could leverage familiar mathematics to guide my intuition.

I asked AI to help identify similarities between session type semantics and statistical mechanics. Some suggestions were spurious. Others revealed genuine structural parallels. The Lyapunov function connecting buffer depths to termination bounds was real. The gauge symmetry interpretation of role identity was substantive.

These analogies serve multiple purposes. They provided intuition during development. They help readers evaluate AI-assisted results by connecting to familiar territory. They make claims more accessible through cross-domain vocabulary.

## Workflow

I used several AI systems throughout the project. These included Aristotle, ChatGPT 5.2/5.3, and Claude Opus 4.5/4.6. Each had different strengths.

I used LLMs to perform literature searches and help identify gaps. It helped with Lean proof scaffolding and error interpretation. It served as a sanity check for my analogies and interpretations.

What worked well was iterative refinement with Lean as ground truth. AI would propose a proof strategy. Lean would reject parts of it. AI would diagnose the errors. Iterate until the proof compiled.

## The Results

The work addresses a gap in session type theory. Prior work establishes that well-typed protocols are safe, meaning they do not get stuck or deadlock. But the proofs require global reasoning that becomes complex with asynchronous buffered communication. Additionally, results are typically qualitative. You know the protocol terminates, but not how long it takes.

The first paper introduces a local invariant called *Coherence*. Instead of re-deriving global properties at each step, Coherence captures what must hold at each communication edge. The invariant is preserved by every valid step. This makes preservation proofs modular and reusable. For type theory, this provides a cleaner proof architecture. And for distributed systems, it means the safety guarantees compose naturally as you add participants or channels.

The second paper adds quantitative bounds. A Lyapunov function on the protocol state decreases with every productive step. This yields concrete bounds on how many steps until termination. The paper also provides a uniform schema for decidability results. Questions like "can this protocol tolerate these failures" become algorithmically decidable. For type theory, this connects session types to stability analysis from dynamical systems. For distributed systems, it means you can answer capacity planning questions at compile time.

The third paper addresses reconfiguration. Protocols change at runtime through delegation and linking. The paper proves that projection commutes with these operations. If you reconfigure first and then project, you get the same result as projecting first and then reconfiguring. It also proves that Coherence is minimal. Any invariant that guarantees safe delegation must imply Coherence. For type theory, this provides a canonical choice of invariant. For distributed systems, it means dynamic topologies preserve the same safety guarantees as static ones.

Alongside the proofs, we built a Rust implementation and deterministic simulator. The implementation provides a practical artifact that practitioners can work with directly. The simulator allows testing protocol behavior under controlled conditions before deployment. This bridges the gap between formal results and engineering practice.

## Lessons

Several lessons emerged from this project.

Pick problems where formal verification is feasible. The proof assistant is your safety net. Without it, you are relying on your own ability to spot errors in an unfamiliar domain. That is a losing proposition.

Look for isomorphisms to domains you know well. Cross-domain intuition is valuable. It guides exploration. It provides sanity checks. It helps you communicate results.

Use AI for breadth and tools for depth. AI is excellent at exploring large spaces quickly. It can survey literature, suggest approaches, and generate drafts. But it cannot be trusted for correctness. Verify everything that matters with tools or domain experts.

Learn the field's conventions. Notation and proof style matter. They affect how your work is received. AI can help you learn conventions quickly by explaining examples from the literature.

Small fields are welcoming. Researchers in small communities are often happy to see new contributors. They are accessible. They will answer questions. They will point you to relevant work.

## Conclusion

The combination was essential. Domain expertise from distributed systems and physics. AI for breadth, speed, and exposition. Lean for correctness guarantees. None alone would have been sufficient.

This approach is reproducible. The tools are available. The methodology is straightforward.
