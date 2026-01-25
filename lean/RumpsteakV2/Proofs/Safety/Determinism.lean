/-! # RumpsteakV2.Proofs.Safety.Determinism

Determinism for V2 protocol semantics.

## Overview

Determinism states that given the same action, a configuration transitions
to a unique next configuration. This is crucial for:
- Predictable protocol execution
- Testing and simulation
- Reasoning about protocol behavior

## Forms of Determinism

1. **Global Type Determinism**: `step g g₁ act` and `step g g₂ act` implies `g₁ = g₂`
2. **Environment Determinism**: `EnvConfigStep e e₁ act` and `EnvConfigStep e e₂ act` implies `e₁ = e₂`
3. **Configuration Determinism**: combining both for full system

## Non-determinism Sources

The protocol itself is deterministic given an action. Non-determinism arises from:
- Action selection (which branch is chosen)
- Environment scheduling (which message is delivered)

These are resolved by the action parameter—once an action is fixed, the result is deterministic.

## Expose

The following definitions form the semantic interface for proofs:

- `GlobalStepDet`: global step determinism
- `EnvStepDet`: environment step determinism
- `ConfigStepDet`: configuration step determinism
- `Claims`: bundle of determinism properties

## Dependencies

This module uses placeholder definitions until Project.lean builds.
-/

import RumpsteakV2.Proofs.Safety.Determinism.Part1
import RumpsteakV2.Proofs.Safety.Determinism.Part2
