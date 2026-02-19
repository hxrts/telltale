import Runtime.VM.Runtime.Runner

/-! # Threaded Runner Extension

Extended round semantics that can execute multiple scheduler picks per round.
The canonical runner in `Runner.lean` remains the reference semantics.
-/

set_option autoImplicit false

universe u

/-- One footprint atom used for wave-level disjointness checks. -/
abbrev FootprintAtom := SessionId × Role

/-- Deduplicate roles while preserving order. -/
private def dedupRoles (roles : List Role) : List Role :=
  roles.foldl (fun acc r => if r ∈ acc then acc else acc ++ [r]) []

/-- Deduplicate footprint atoms while preserving order. -/
private def dedupFootprintAtoms (atoms : List FootprintAtom) : List FootprintAtom :=
  atoms.foldl (fun acc a => if a ∈ acc then acc else acc ++ [a]) []

/-- Compile-time footprint summary for a role from program metadata. -/
private def roleFootprintSummary {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]
    (prog : Program γ ε) (role : Role) : List Role :=
  match prog.metadata.footprintSummary.find? (fun p => p.1 = role) with
  | some (_, roles) => roles
  | none => []

private def buildOwnershipIndex {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : Std.HashMap OwnershipKey LaneId :=
  st.coroutines.toList.foldl
    (fun acc c =>
      let lane := laneOf st.sched c.id
      c.ownedEndpoints.foldl (fun acc' ep => acc'.insert (ep.sid, ep.role) lane) acc)
    {}

private def normalizeThreadedState {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : VMState ι γ π ε ν :=
  let sched' := syncLaneViews st.sched
  let st' := { st with sched := sched' }
  let ownership := buildOwnershipIndex st'
  { st' with sched := { st'.sched with ownershipIndex := ownership } }

/-- Endpoint footprint carried by one coroutine. -/
def coroFootprintAtoms {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cid : CoroutineId) : List FootprintAtom :=
  match st.coroutines[cid]? with
  | none => []
  | some c =>
      let staticRolesFor : Role → List Role :=
        match st.programs[c.programId]? with
        | some prog => fun role => dedupRoles (role :: roleFootprintSummary prog role)
        | none => fun role => [role]
      let atoms := c.ownedEndpoints.foldl
        (fun acc ep =>
          acc ++ (staticRolesFor ep.role).map (fun role => (ep.sid, role)))
        []
      dedupFootprintAtoms atoms

/-- Primary session id for a coroutine when one endpoint is available. -/
def coroPrimarySession? {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cid : CoroutineId) : Option SessionId :=
  match st.coroutines[cid]? with
  | none => none
  | some c => c.ownedEndpoints.head?.map (fun ep => ep.sid)

/-- Two footprints are disjoint when no atom occurs in both lists. -/
def waveFootprintDisjoint (left right : List FootprintAtom) : Prop :=
  (∀ atom, atom ∈ left → atom ∉ right) ∧
  (∀ atom, atom ∈ right → atom ∉ left)

/-- Admissible wave contract for threaded scheduling.

Each picked coroutine must be ready and runnable. Picks are unique. Picks in the
same wave are lane-disjoint, session-disjoint, and footprint-disjoint.
-/
def waveAdmissible {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (picked : List CoroutineId) : Prop :=
  List.Nodup picked ∧
  (∀ cid, cid ∈ picked → cid ∈ st.sched.readyQueue ∧ isRunnable st cid = true) ∧
  (∀ c1 c2,
      c1 ∈ picked → c2 ∈ picked → c1 ≠ c2 →
      laneOf st.sched c1 ≠ laneOf st.sched c2) ∧
  (∀ c1 c2,
      c1 ∈ picked → c2 ∈ picked → c1 ≠ c2 →
      match coroPrimarySession? st c1, coroPrimarySession? st c2 with
      | some sid1, some sid2 => sid1 ≠ sid2
      | _, _ => True) ∧
  (∀ c1 c2,
      c1 ∈ picked → c2 ∈ picked → c1 ≠ c2 →
      waveFootprintDisjoint (coroFootprintAtoms st c1) (coroFootprintAtoms st c2))

private def waveSessionDisjointB {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (left right : CoroutineId) : Bool :=
  match coroPrimarySession? st left, coroPrimarySession? st right with
  | some sidL, some sidR => sidL ≠ sidR
  | _, _ => true

private def waveFootprintDisjointB (left right : List FootprintAtom) : Bool :=
  !(left.any (fun atom => atom ∈ right))

private def compatibleWithWave {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (eligible : CoroutineId → CoroutineId → Bool)
    (picked : List CoroutineId) (cid : CoroutineId) : Bool :=
  (isRunnable st cid) &&
    picked.all (fun other =>
      let fpCid := coroFootprintAtoms st cid
      let fpOther := coroFootprintAtoms st other
      let fpDisjoint := waveFootprintDisjointB fpCid fpOther &&
        waveFootprintDisjointB fpOther fpCid
      (laneOf st.sched cid ≠ laneOf st.sched other) &&
      eligible cid other && eligible other cid &&
      (waveSessionDisjointB st cid other || fpDisjoint) &&
      fpDisjoint)

private def planWavePass {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (eligible : CoroutineId → CoroutineId → Bool)
    (remaining : List CoroutineId) :
    List CoroutineId × List CoroutineId :=
  let rec go (pending wave deferred : List CoroutineId) :=
    match pending with
    | [] => (wave.reverse, deferred.reverse)
    | cid :: rest =>
        if compatibleWithWave st eligible wave cid then
          go rest (cid :: wave) deferred
        else
          go rest wave (cid :: deferred)
  go remaining [] []

/-- Deterministic phase-1 planner with proof-guided eligibility.
Partitions the normalized ready queue into admissible waves using stable order. -/
def planDeterministicWavesEligible {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (eligible : CoroutineId → CoroutineId → Bool) :
    List (List CoroutineId) :=
  let st' := normalizeThreadedState st
  let rec loop (remaining : List CoroutineId) (waves : List (List CoroutineId)) (fuel : Nat) :
      List (List CoroutineId) :=
    match fuel with
    | 0 => waves.reverse
    | fuel' + 1 =>
        if remaining.isEmpty then
          waves.reverse
        else
          let (wave, deferred) := planWavePass st' eligible remaining
          if wave.isEmpty then
            waves.reverse
          else
            loop deferred (wave :: waves) fuel'
  loop st'.sched.readyQueue [] st'.sched.readyQueue.length

/-- Deterministic phase-1 planner: all runnable pairs are eligible. -/
def planDeterministicWaves {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) : List (List CoroutineId) :=
  planDeterministicWavesEligible st (fun _ _ => true)

private def chunkWave (width : Nat) (wave : List CoroutineId) : List (List CoroutineId) :=
  let rec go (remaining : List CoroutineId) (acc : List (List CoroutineId)) (fuel : Nat) :
      List (List CoroutineId) :=
    match fuel with
    | 0 => acc.reverse
    | fuel' + 1 =>
        if remaining.isEmpty then
          acc.reverse
        else
          let batch := remaining.take width
          let rest := remaining.drop width
          go rest (batch :: acc) fuel'
  if width = 0 then [] else go wave [] wave.length

private def removeWaveFromReady (ready : SchedQueue) (wave : List CoroutineId) : SchedQueue :=
  wave.foldl (fun q cid => removeFirst cid q) ready

private def executeWave {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (wave : List CoroutineId) : VMState ι γ π ε ν :=
  let st0 := normalizeThreadedState st
  let sched0 := st0.sched
  let ready0 := removeWaveFromReady sched0.readyQueue wave
  let sched1 := syncLaneViews
    { sched0 with readyQueue := ready0, stepCount := sched0.stepCount + wave.length }
  let st1 := { st0 with sched := sched1 }
  let st2 := wave.foldl (fun stAcc cid =>
      if isRunnable stAcc cid then
        let (st', res) := execInstr stAcc cid
        let sched' := updateAfterStep st'.sched cid res.status
        { st' with sched := sched' }
      else
        stAcc) st1
  normalizeThreadedState st2

def executePlannedWaves {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (waves : List (List CoroutineId)) : VMState ι γ π ε ν :=
  waves.foldl executeWave st

/-- Certificate artifact for a deterministic wave plan. -/
structure WaveCertificate where
  waves : List (List CoroutineId)
  plannerStep : Nat := 0
  deriving Repr

/-- Reusable threaded round planning artifact. -/
structure ThreadedRoundPlan where
  certificate : WaveCertificate
  deriving Repr

private def waveReadyRunnableB {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (wave : List CoroutineId) : Bool :=
  wave.all (fun cid => cid ∈ st.sched.readyQueue && isRunnable st cid)

private def wavePairwiseB {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (wave : List CoroutineId) : Bool :=
  let rec go (seen remaining : List CoroutineId) :=
    match remaining with
    | [] => true
    | cid :: rest =>
        compatibleWithWave st (fun _ _ => true) seen cid && go (cid :: seen) rest
  go [] wave

private def noDupB (xs : List CoroutineId) : Bool :=
  let rec go (seen remaining : List CoroutineId) :=
    match remaining with
    | [] => true
    | x :: rest =>
        if x ∈ seen then false else go (x :: seen) rest
  go [] xs

/-- Boolean checker for one wave against `waveAdmissible`-style obligations. -/
def checkWaveAdmissible {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (wave : List CoroutineId) : Bool :=
  waveReadyRunnableB st wave && wavePairwiseB st wave

/-- Wave-certificate checker for `waveAdmissible` obligations. -/
def checkWaveCertificate {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (cert : WaveCertificate) : Bool :=
  let picks := cert.waves.foldl (fun acc wave => acc ++ wave) []
  noDupB picks && cert.waves.all (checkWaveAdmissible st)

/-- Build a deterministic certificate for a threaded round width. -/
def plannedWaveCertificate {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (n : Nat) (st : VMState ι γ π ε ν) : WaveCertificate :=
  let planned := planDeterministicWaves st
  let bounded := planned.foldr (fun wave acc => chunkWave n wave ++ acc) []
  { waves := bounded, plannerStep := st.sched.stepCount }

/-- Build a threaded round plan from deterministic planner output. -/
def planThreadedRound {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (n : Nat) (st : VMState ι γ π ε ν) : ThreadedRoundPlan :=
  { certificate := plannedWaveCertificate n st }

/-- Validate one threaded round plan certificate. -/
def checkThreadedRoundPlan {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (plan : ThreadedRoundPlan) : Bool :=
  checkWaveCertificate st plan.certificate

/-- Execute one validated threaded plan with canonical fallback. -/
def executeThreadedRoundPlan {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (st : VMState ι γ π ε ν) (plan : ThreadedRoundPlan) : VMState ι γ π ε ν :=
  if checkThreadedRoundPlan st plan then
    executePlannedWaves st plan.certificate.waves
  else
    schedRoundOne st

/-- Execute a certified threaded round; fallback to canonical one-step on
certificate failure. -/
def executeCertifiedRound {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (n : Nat) (st : VMState ι γ π ε ν) : VMState ι γ π ε ν :=
  executeThreadedRoundPlan st (planThreadedRound n st)

/-- Threaded phase-2 executor over deterministic preplanned waves. -/
def schedRoundThreaded {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (n : Nat) (st : VMState ι γ π ε ν) : VMState ι γ π ε ν :=
  if n = 0 then
    st
  else if n = 1 then
    schedRoundOne st
  else
    executeCertifiedRound n st

/-- Threaded fuel-bounded runner: same outer control as canonical runner, but
rounds may execute more than one scheduler step. -/
def runScheduledThreaded {ι γ π ε ν : Type u} [IdentityModel ι] [GuardLayer γ]
    [PersistenceModel π] [EffectRuntime ε] [VerificationModel ν]
    [AuthTree ν] [AccumulatedSet ν]
    [IdentityGuardBridge ι γ] [EffectGuardBridge ε γ]
    [PersistenceEffectBridge π ε] [IdentityPersistenceBridge ι π]
    [IdentityVerificationBridge ι ν]
    (fuel : Nat) (concurrency : Nat) (st : VMState ι γ π ε ν) : VMState ι γ π ε ν :=
  match fuel with
  | 0 => st
  | fuel' + 1 =>
      let st' := { st with clock := st.clock + 1 }
      let st'' := tryUnblockReceivers st'
      let st''' := schedRoundThreaded concurrency st''
      if allTerminal st''' then
        st'''
      else if st'''.sched.stepCount = st''.sched.stepCount then
        st'''
      else
        runScheduledThreaded fuel' concurrency st'''
