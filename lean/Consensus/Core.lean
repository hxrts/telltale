import Consensus.Types
import Consensus.Classifier
import Consensus.Hypotheses
import Consensus.ClassicalValidation
import Consensus.Certified
import Consensus.Api
import Consensus.FLP.Hypotheses
import Consensus.FLP.Api
import Consensus.CAP.Hypotheses
import Consensus.CAP.Api

set_option autoImplicit false

/-! # Consensus.Core

Facade module for consensus validation:
- model types (`Consensus.Types`)
- space classification (`Consensus.Classifier`)
- hypothesis validation (`Consensus.Hypotheses`)
- classical-property eligibility (`Consensus.ClassicalValidation`)
- certified classical wrappers (`Consensus.Certified`)
-/
