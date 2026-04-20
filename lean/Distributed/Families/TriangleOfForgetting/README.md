This directory contains the Lean 4 formalization of the Triangle of Forgetting.

As described in the accompanying [blog post](https://weboftru.st/post/triangle-of-forgetting), it formalizes the result
that monotone merge, temporal secrecy, and dynamic membership cannot be jointly
guaranteed in an asynchronous distributed setting. Here temporal secrecy is
formalized as the combined demand of forward secrecy and post-compromise
security.

- `Core.lean`: the abstract theorem family and main impossibility results.
- `GenericCausalState.lean`: a reusable causal-state wrapper for CRDT-style
  instantiations.
- `Example.lean`: a concrete worked example built on the generic wrapper.
- `API.lean`: the certified protocol-facing wrapper used by theorem packs.
