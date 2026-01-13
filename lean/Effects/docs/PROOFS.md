Here are the properties that actually matter for *this* system (async buffers + shadow traces `D` + coherence + freshness supply). I’d group them into five “must prove” pillars, then a few “nice-to-have” ones.

## 1) Type safety for asynchronous communication (the core)

**(a) Preservation / Subject reduction**
If `WTConfig (S,G,D,C)` and `C → C'`, then there exist updated environments `(S',G',D')` such that `WTConfig (S',G',D',C')`.
This is the main theorem that forces you to prove:

* enqueue updates `B` and `D` consistently,
* dequeue updates `B` and `D` consistently,
* session endpoints in `G` advance consistently,
* coherence is maintained.

**(b) Protocol fidelity (no mismatched dequeue)**
A sharper corollary of preservation: if a `recv` step dequeues a value `v` from buffer edge `e`, then `v` has the type predicted by the *current* local/session state (as tracked by `D` and `G`).
This is the “real asynchrony” replacement for classic “communication safety”.

## 2) Queue invariants (the thing that makes async provable)

**(a) BuffersTyped invariance**
If `BuffersTyped(G,D,B)` holds, then after:

* send/enqueue: it still holds (enqueue lemma),
* recv/dequeue: it still holds (dequeue lemma).

This is your mechanical backbone: most of the async proof is just queue typing preservation.

**(b) Coherence invariance**
If `Coherent(G,D)` holds, then it holds after each protocol step:

* `Coherent_send_preserved`
* `Coherent_recv_preserved`
* (and later) `Coherent_select/branch_preserved` for labeled choice
* `Coherent_newChan_preserved` for fresh sessions/endpoints

This is the “global consistency” condition that replaces simple binary duality.

## 3) Freshness and allocation (no nominal pain, but must be proved)

**(a) Supply invariant preservation**
If `SupplyInv(nextId, store, bufs, G, D)` holds, then it continues to hold after every step.
This is what guarantees **fresh channel allocation is sound** without side conditions sprinkled everywhere.

**(b) Fresh allocation lemma**
From `SupplyInv(n, …)` you get: no endpoint with id `n` exists anywhere, so allocating id `n` is fresh.
Then show the post-state satisfies `SupplyInv(n+1, …)`.

If you move to MPST, this becomes “fresh session id”.

## 4) Linearity / non-aliasing (otherwise the whole story collapses)

You need one of these (depending on how you represent the runtime store):

**(a) Static linearity is enforced**
Your `Split` judgment (for `par`) ensures linear resources aren’t duplicated across threads.

**(b) Runtime non-aliasing invariant is preserved**
A theorem like: if the store is well-formed w.r.t. linear vars (no two linear vars point to the same endpoint), then it stays so after steps.
This is what eliminates the annoying “some other variable points to the same endpoint” case you kept having to assume away.

In the “finished” system, (b) should be a *derived invariant* from (a) + typing, not an extra assumption.

## 5) Progress / non-stuckness (must be honest in async)

For real asynchrony, you usually prove a *conditional* progress theorem:

**(a) Local progress (non-stuckness due to typing)**
If `WTConfig` holds, then the configuration is either:

* terminated, or
* can take a step, or
* is blocked only on a `recv` whose corresponding buffer is empty (i.e., not blocked due to protocol mismatch).

This is the right “progress” notion for async semantics without hidden fairness.

**(b) Conditional communication progress / liveness (optional but valuable)**
Under explicit assumptions (fair scheduler / eventual delivery / no permanent starvation), blocked receives eventually become enabled.
This is where you’d state and prove a theorem that depends on a scheduler model; it shouldn’t be silently baked into the calculus.

---

# Nice-to-have properties (but not essential to close the core problem)

* **Determinism (or confluence) of the local computation layer**: often false with concurrency, but you can prove determinism for expression evaluation if you separate it.
* **Session completion**: if all processes terminate, then all session types are `end` and all buffers empty (a “clean shutdown” theorem).
* **Compatibility / substitutability**: if you add subtyping, prove that replacing a component with a subtype preserves well-typedness.
* **Decidability of typechecking**: mostly engineering, but important if you want this to be more than a proof artifact.

---

## If you extend to MPST, the list stays the same — only coherence changes

You still prove: preservation + buffer-typing invariance + coherence invariance + freshness + linearity + (conditional) progress.
The difference is that `Coherent(G,D)` is now quantified over **roles and directed edges** and/or mediated by a global type projection.

If you want, I can rewrite these as crisp Lean-friendly theorem statements in the style of your `WTConfigN_L` and `Step` relations, including exactly what side conditions you need to avoid the “self-channel in messages” corner cases.
