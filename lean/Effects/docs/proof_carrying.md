We want “proof-carrying runtime + verified monitor” to be cleanly supported (and provable). We should tweak the type system so that **the monitor’s checks are exactly the same judgments your metatheory already proves preserve**. Concretely, that means shifting from “processes hold channels” to “processes hold *capabilities* issued by the monitor”, and making the protocol state and effect obligations *explicitly representable and decidable* at runtime.

## 1) Replace raw channel values with linear capability tokens

Right now you model channels as `Value.chan endpoint`. For a monitored system you want:

* `Tok(e, S)` (or `Tok(sid, role, L)` in MPST): a **linear** token that entitles the holder to act on endpoint `e` currently at local type/state `S`.
* The monitor consumes `Tok(e, send T U)` and returns a fresh `Tok(e, U)` after an accepted send; similarly for recv.

Type-system adjustment:

* Make “having an endpoint” *not* a normal value type. Instead:

  * either add a separate class of **linear capabilities** (like an affine/linear capability context),
  * or keep `ValType.chan` but ensure channel values are *never duplicable* and are only constructible by monitor actions.

This single change eliminates 80% of the aliasing pain and turns “untrusted node can’t misuse endpoint” into “node can’t forge/duplicate tokens”.

## 2) Make runtime steps carry *checkable* protocol witnesses

Your typing rules already know the next action is `send T U` / `recv T U`. The monitor needs to check that quickly.

So adjust your operational interface so that each boundary action includes:

* endpoint identifier `e` (or `(sid, role)` / `(sid,p,q)`),
* current local type/state hash or index (optional but practical),
* payload plus a runtime tag/validator for its `ValType`,
* and the token `Tok(e, S)` itself.

Type-system side: define a “monitor transition judgment” that mirrors your typing evolution:

* `MonStep(G,D,B, Tok(e,S), action) = (G',D',B', Tok(e,S'))`
  and then prove it preserves the same invariants as your static system.

## 3) Strengthen “value typing” so the monitor can decide it

For the monitor to check “payload has type T”, `HasTypeVal` must be decidable on runtime values. That usually means:

* stick to a runtime-representable universe of value types (bool/int/unit/ref/token),
* for channels-as-values, treat them as **tokens** (ownership transfer), not raw endpoints,
* avoid exotic dependent value types unless you also ship runtime evidence.

In Lean terms: make `HasTypeVal` computably checkable (or at least reducible to decidable checks + token validity).

## 4) Make coherence and queue typing *explicit monitor state*

Your big breakthrough objects `D` (shadow queue traces) and `Coherent(G,D)` should become part of the monitor’s trusted state, not a proof artifact.

Type-system adjustment:

* define `WTMon(G,D,B,Supply,Lin)` as the monitor invariant (basically your `WTConfig` minus untrusted process internals),
* define `MonitorStep` rules for send/recv/newSession/select/branch,
* prove `WTMon → WTMon` for each rule.

That gives you the key theorem: “if the monitor accepts a step, invariants never break”.

## 5) Add an explicit “no self-token in messages / controlled delegation” rule

The monitor story forces you to be precise about endpoint delegation (sending endpoints/tokens as messages):

* If you allow it, model it explicitly as **token transfer**:

  * send carries `Tok(e2,S2)` as payload,
  * monitor consumes that token from sender and mints a corresponding token for receiver.
* If you don’t allow it, add a typing restriction that forbids channel/tokens as payload types.

Either way, you should bake in the invariant you kept informally using:

* “messages in queues never contain the very same token/endpoint that is being stepped”.
  With tokens, this becomes straightforward: tokens can’t be serialized without the monitor’s involvement.

## 6) Recast effects as *monitor-visible obligations* (or ban boundary-unsafe effects)

For “composable effects” under monitoring, you need a clear separation:

* **Local effects** (pure computation, local state) can remain untrusted and outside the monitor.
* **Boundary-relevant effects** (cancellation, exceptions that abort mid-protocol, timeouts, transactional rollback) must be reflected in the monitor state as obligations.

Practical adjustment options:

* Add a small effect layer to local types: e.g. “this recv is cancellable” or “this send is compensatable”.
* Or restrict effects at the boundary: e.g. “no abort between receiving a token and consuming it”.
* Or require explicit compensating protocol messages (a typed cancellation branch), so the monitor can enforce that any abort follows a protocol path.

The goal is: every “effectful deviation” that could strand peers is either **impossible** or **represented as a protocol action** the monitor can check.

## 7) Add a decidable “link” judgment for runtime composition

To let two untrusted nodes connect safely, you want a judgment like:

* `LinkOK(G1,D1, TokA …, G2,D2, TokB …)` iff merged `G,D` are coherent and ownership is disjoint.

Type-system adjustment:

* define a *boundary typing* / interface type:

  * what tokens a component exports,
  * what local types they are at,
  * what shadow traces apply to shared buffers,
* and prove a linking theorem: if `LinkOK` then the merged monitor state satisfies `WTMon`.

This makes “runtime composition” a monitor-checked, decidable rule rather than a meta-level assumption.

## 8) MPST-specific adjustment: buffers keyed by directed edges and labeled choices

For multiparty you’ll want the monitor state to be keyed by `(sid,p→q)` (or mailbox-per-receiver with tags), and local types to include `⊕`/`&` labels. Then:

* send enqueues `(label, value)` or `(label)` for pure choice,
* recv checks label membership and advances the local type accordingly,
* `D` stores traces of labels + types per edge.

This keeps all monitor checks local and decidable.
