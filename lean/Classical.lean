import Classical.Transport.API
import Classical.Families.SpectralGapTermination


/-! # Classical Theorem Transport Layer

This module is the entry point for transported classical theorems from physics
and queueing theory, adapted for session-typed protocol verification.

## Purpose

Many properties of distributed protocols (liveness, throughput, tail bounds)
have analogues in classical applied mathematics. This layer exposes them as
**honest conditional interfaces (Option B)**: each named classical theorem
(Little's law, MaxWeight optimality, sub-Gaussian tails, LDP/mixing envelopes,
spectral-gap termination, Cheeger) is an *assumed input* carried by a
`*Witness`/`*Input` field and is **not proved** here. Lemmas only derive
elementary consequences from those inputs. The heavy-traffic, mean-field and
functional-CLT families contain only elementary identities (the functional-CLT
input is a degenerate constant path); no limit theorem is proved.

## Theorem Families

| Family                 | Classical Origin (not proved) | Protocol Application             |
|-----------------------|---------------------------|-------------------------------------|
| Foster-Lyapunov-Harris | Markov chain stability     | Liveness via progress measures      |
| MaxWeight Backpressure | Network scheduling         | Throughput-optimal processing       |
| Large Deviations       | Rare event asymptotics     | SLA tail bounds                     |
| Heavy Traffic          | Near-capacity queue limits | Buffer sizing under load            |
| Mixing Times           | Markov chain convergence   | Equilibration rates                 |
| Fluid Limits           | Deterministic flow models  | Aggregate buffer dynamics           |
| Concentration          | Sub-Gaussian tails         | Observable deviation bounds         |
| Little's Law           | L = λW identity            | Latency/throughput relationships    |
| Functional CLT         | Donsker's theorem          | Path-level trajectory analysis      |
| Propagation of Chaos   | Mean-field limits          | Multi-session scalability           |

## Usage

Import this module to access the stable `Classical.Transport` API:

```lean
import Classical

-- Conditional lemmas over assumed inputs
example := Classical.Transport.foster_conclusion_of_input
example := Classical.Transport.littles_law_wait_time_of_input
```

## See Also

- `Classical.Transport.Context` for transport context definitions
- `Classical.Transport.Contracts` for Input/Conclusion contracts
- `Classical.Transport.Theorems` for transported theorem statements
- Individual family modules under `Classical.Families.*` for background results
-/
