import Runtime.ProtocolMachine.Model.TypeClasses
import Runtime.ProtocolMachine.Composition

set_option autoImplicit false

universe u

/-! # Bundled protocol machine Domain Dictionary

`ProtocolMachineDomain` bundles the full executable protocol machine domain interface stack (models + bridges)
into one typeclass so executable modules do not repeat long constraint lists.
-/

class ProtocolMachineDomain (ι γ π ε ν : Type u) where
  identityModel : IdentityModel ι
  guardLayer : GuardLayer γ
  persistenceModel : PersistenceModel π
  effectRuntime : EffectRuntime ε
  verificationModel : VerificationModel ν
  authTree : AuthTree ν
  accumulatedSet : AccumulatedSet ν
  identityGuardBridge : IdentityGuardBridge ι γ
  effectGuardBridge : EffectGuardBridge ε γ
  persistenceEffectBridge : PersistenceEffectBridge π ε
  identityPersistenceBridge : IdentityPersistenceBridge ι π
  identityVerificationBridge : IdentityVerificationBridge ι ν

attribute [instance] ProtocolMachineDomain.identityModel
attribute [instance] ProtocolMachineDomain.guardLayer
attribute [instance] ProtocolMachineDomain.persistenceModel
attribute [instance] ProtocolMachineDomain.effectRuntime
attribute [instance] ProtocolMachineDomain.verificationModel
attribute [instance] ProtocolMachineDomain.authTree
attribute [instance] ProtocolMachineDomain.accumulatedSet
attribute [instance] ProtocolMachineDomain.identityGuardBridge
attribute [instance] ProtocolMachineDomain.effectGuardBridge
attribute [instance] ProtocolMachineDomain.persistenceEffectBridge
attribute [instance] ProtocolMachineDomain.identityPersistenceBridge
attribute [instance] ProtocolMachineDomain.identityVerificationBridge

instance instVMDomainOfPieces (ι γ π ε ν : Type u)
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectRuntime ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] : ProtocolMachineDomain ι γ π ε ν where
  identityModel := inferInstance
  guardLayer := inferInstance
  persistenceModel := inferInstance
  effectRuntime := inferInstance
  verificationModel := inferInstance
  authTree := inferInstance
  accumulatedSet := inferInstance
  identityGuardBridge := inferInstance
  effectGuardBridge := inferInstance
  persistenceEffectBridge := inferInstance
  identityPersistenceBridge := inferInstance
  identityVerificationBridge := inferInstance
