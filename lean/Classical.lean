import Classical.Transport

/-!
# Classical Theorem Transport Layer

This module is the entry point for transported classical theorems from physics
and queueing theory, adapted for session-typed protocol verification.

## Purpose

Many properties of distributed protocols (liveness, throughput, tail bounds)
have analogues in classical applied mathematics. Rather than reproving these
from scratch, the transport layer instantiates well-known results with
protocol-specific definitions.

## Theorem Families

| Family                 | Classical Origin           | Protocol Application                |
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

-- Use transported theorems
#check Classical.Transport.transported_fosterLyapunov
#check Classical.Transport.transported_littlesLaw
```

## See Also

- `Classical.Transport.API` for Input/Conclusion type definitions
- `Classical.Transport.Results` for the transported theorem statements
- Individual theorem modules for mathematical background and proofs
-/
