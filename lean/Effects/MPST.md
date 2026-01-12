To go from your binary async session core to **multiparty session types (MPST)**, you keep the same “real asynchrony” spine (explicit buffers + type-level shadow buffers + coherence), but you change what a “channel” *is* and what coherence means.

## 1) Replace binary endpoints with session + role

Binary:

* `Endpoint = ChanId × Polarity`
  MPST:
* `Endpoint = SessionId × Role`
* `Role` is a finite identifier (`Nat`/`String`), and a session has a *set of roles*.

Runtime values become `Value.chan (sid, r)` (an endpoint capability for role `r` in session `sid`).

Typing environment becomes:

* `G : (sid, role) ↦ LocalType` (a **local** session type for each role in each session)

You don’t have to store global types, instead maintain a **consistency/coherence invariant** relating the locals and queues (more on that below).

## 2) Buffers become “directed mailboxes”

In MPST, messages have sender and receiver roles. So your runtime buffers should be keyed by a **directed edge**:

* simplest: `Buf : (sid, fromRole, toRole) ↦ List Value`  (FIFO per pair)
* more actor-like: `Buf : (sid, toRole) ↦ List (fromRole × Value)` (single mailbox per receiver; ordering policy becomes important)

Your type-level shadow buffers `D` mirror this:

* `D : (sid, from, to) ↦ List ValType` (or include labels/branches)

Then the operational rules generalize cleanly:

* send by role `p` to role `q`: enqueue into `(sid,p,q)` and advance `G(sid,p)`
* recv by role `q` from role `p`: dequeue from `(sid,p,q)` and advance `G(sid,q)`

## 3) Local types replace binary duality

Binary duality was “send vs recv”. MPST uses **local types** such as:

* `!q(T).L` (send `T` to role `q`, continue as `L`)
* `?p(T).L` (receive `T` from role `p`, continue)
* plus labeled choice (selection/branching): `⊕q{ℓᵢ: Lᵢ}` and `&p{ℓᵢ: Lᵢ}`

So your local-step typing rules look like:

* if `G(sid,p) = !q(T).L` then `send` is allowed; update `G(sid,p) := L` and append `T` to `D(sid,p,q)`
* if `G(sid,q) = ?p(T).L` and `D(sid,p,q) = T :: ts` then `recv` is allowed; update `G(sid,q) := L` and pop `D(sid,p,q) := ts`

This is exactly your binary pattern, just indexed by `(sid,p,q)` and using local types.

## 4) Coherence generalizes from “dual” to “global consistency”

Your binary `Coherent(G,D)` said: after “consuming” queued types, the two endpoint session types are dual.

MPST coherence becomes: for every session `sid` and every directed edge `(p→q)`:

* the sender local type at `(sid,p)` is consistent with the trace `D(sid,p,q)` it has produced, and
* the receiver local type at `(sid,q)` is consistent with `D(sid,p,q)` it must consume, and
* **all roles agree on the same global conversation shape.**

There are two workable ways to state this invariant:

### Option A: global type + projection

Maintain `GT(sid)` and require:

* `G(sid,r) = proj(GT(sid), r)` for all roles `r`
* plus “queue traces match pending actions” (your `Consume` idea becomes “consume receives along an edge”)
  This is the cleanest spec-side story.

### Option B: no global type, just local compatibility + queue traces

Define a multiparty “consume” relation that advances locals given queued traces on all edges, and require that the resulting locals are **jointly compatible** (no role expects to receive from p while p’s local can never send to it, etc.). This is closer to what you’ve already mechanized: coherence is a *semantic invariant* over `(G,D)`.

Either way, your proof pattern stays the same: each step locally updates `(G,D,B)` and you prove it preserves `Coherent`.

## 5) Freshness becomes “fresh session id + role set”

Your supply invariant generalizes nicely:

* `nextSid` is fresh, and **all session ids appearing anywhere are < nextSid**
* `newSession sid roles GT` allocates:

  * store bindings for each role endpoint `(sid,r)`
  * empty buffers for each directed pair `(sid,p,q)` (or empty mailbox `(sid,q)`)

This is the MPST version of your breakthrough freshness handling: no nominal gymnastics, just a monotone “all ids < nextSid”.

## 6) What the preservation proof looks like in MPST

Almost identical to what you’ve built, with two extra moving parts:

1. **Queue typing lemmas** now quantify over directed edges:

   * enqueue preserves `BuffersTyped` for `(sid,p,q)`
   * dequeue preserves it for `(sid,p,q)`

2. **Coherence lemmas** now come in more cases:

   * send/recv on value messages (your current ones)
   * plus selection/branch labels (enqueue label, receiver branches on label)
   * plus any ordering policy if you use merged mailboxes (`(sid,q)`)

Everything else is the same “invariant threading” structure:

* `WTConfig(sid, G, D, store, bufs)` is preserved by each `Step`
* “stuckness” becomes: a recv is blocked only because its corresponding buffer edge is empty (or scheduling), not because of type mismatch.

## 7) Ordering discipline

* **Single mailbox per receiver**: more realistic for actors, which requires:

  * tags `(fromRole, payload)` in buffers
  * and a more complex `Consume`/coherence story that allows interleaving from different senders.

---

If you want a concrete “what would it look like” translation into your Lean skeleton, the minimal diffs are:

* replace `Endpoint` with `(SessionId × Role)`
* replace `Buffers : Endpoint ↦ List Value` with `Buffers : (SessionId × Role × Role) ↦ List Value`
* replace `D : Endpoint ↦ List ValType` with `D : (SessionId × Role × Role) ↦ List ValType`
* replace binary `SType` with MPST local types (send/recv to specific roles, plus choice)
* rewrite `Coherent` to quantify over sessions and directed edges (or store `GT` and require projection)

That’s it structurally—the hard part is just choice/labels and (if you want it) merged mailbox ordering.
