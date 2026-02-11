import Runtime.VM.Model.TypeClasses
import Runtime.VM.Composition.DomainComposition

set_option autoImplicit false

universe u

/-! # Bundled VM Domain Dictionary

`VMDomain` bundles the full executable VM domain interface stack (models + bridges)
into one typeclass so executable modules do not repeat long constraint lists.
-/

class VMDomain (ι γ π ε ν : Type u) where
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

attribute [instance] VMDomain.identityModel
attribute [instance] VMDomain.guardLayer
attribute [instance] VMDomain.persistenceModel
attribute [instance] VMDomain.effectRuntime
attribute [instance] VMDomain.verificationModel
attribute [instance] VMDomain.authTree
attribute [instance] VMDomain.accumulatedSet
attribute [instance] VMDomain.identityGuardBridge
attribute [instance] VMDomain.effectGuardBridge
attribute [instance] VMDomain.persistenceEffectBridge
attribute [instance] VMDomain.identityPersistenceBridge
attribute [instance] VMDomain.identityVerificationBridge

instance instVMDomainOfPieces (ι γ π ε ν : Type u)
    [IdentityModel ι] [GuardLayer γ] [PersistenceModel π] [EffectRuntime ε]
    [VerificationModel ν] [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν] : VMDomain ι γ π ε ν where
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
