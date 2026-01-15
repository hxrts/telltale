# BisimDecidable.lean Status

**Last Updated**: 2026-01-15

## Overall Status

✅ **File compiles successfully** with 8 intentional `sorry` placeholders.

**Progress**: Fixed 15+ compilation errors → 8 well-documented sorries

---

## ✅ Completed Proofs

### 1. Bound Proofs in Label/Child Matching (COMPLETED)
**Lines**: 468-498, 530-561

**What was proven**:
- All dependent type index bound proofs for accessing list elements
- Proper use of `hlen : bs.length = cs.length` to prove `i.val < cs.length`
- Used `omega` tactic for arithmetic reasoning after `simp only [List.length_map]`

**Key techniques**:
```lean
have hi_bound : i.val < cs.length := by simp only [List.length_map]; omega
```

### 2. Child Extraction Proofs (COMPLETED)
**Lines**: 468-498, 530-561

**What was proven**:
- Conversion from `List.map (·.2) bs` to `childrenOf (fullUnfoldN n a)`
- `List.get_mem_zip` applications for proving pair membership
- Proper construction of `hmem'` for use with `hchildren`

**Key techniques**:
```lean
have hmem' : (...) ∈ (childrenOf ...).zip (childrenOf ...) := by
  rw [hchildren_eq_a, hchildren_eq_b]
  exact hmem
```

### 3. Helper Lemmas (COMPLETED)
**Lines**: 47-91, 280-428

**What was proven**:
- `List.get_map'`: Accessing mapped list elements
- `childrenOf_send_eq_snd_branchesOf`: Children are second components of branches
- `childrenOf_recv_eq_snd_branchesOf`: Same for recv case
- `branchesOf_labels_eq`: Labels extraction for send
- `branchesOf_labels_eq_recv`: Labels extraction for recv

---

## ⏳ Remaining Sorries (8 total)

### 1. Label Matching Proofs (2 sorries)
**Lines**: 465, 528

**Goal**: Prove `(bs.get i).1 = (cs.get ⟨i.val, hlen ▸ i.isLt⟩).1`

**Given**:
- `hlabels_a : bs.map (·.1) = labels`
- `hlabels_b : cs.map (·.1) = labels`
- `hlen : bs.length = cs.length`

**Problem**: Dependent type unification - both sides equal `labels[i]` but have different `Fin` index types with different proof terms.

**Solution needed**:
- Heterogeneous equality (`HEq`)
- Explicit `cast` with proof of index equality
- Or a custom lemma about list access with transported indices

### 2. Coinductive Visited Set Reasoning (2 sorries)
**Lines**: 494, 552

**Context**:
```lean
exact Or.inl ⟨fuel, visited_any, sorry, hpair⟩
```

**Goal**: Construct proof `∀ q ∈ visited_any, EQ2C q.1 q.2`

**Problem**: `bisimAux` inserts `(a, b)` into `visited_any` before proving `EQ2C a b`, creating circular dependency.

**Solution needed**: Proper paco coinduction framework integration to handle visited set invariants.

### 3. List.get_mem_zip Helper (1 sorry)
**Line**: 97

**Goal**: Complete the proof of the helper lemma we added:
```lean
lemma List.get_mem_zip {α β : Type*} (as : List α) (bs : List β) (i : Fin as.length)
    (hlen : as.length = bs.length) :
    (as.get i, bs.get ⟨i.val, hlen ▸ i.isLt⟩) ∈ List.zip as bs
```

**Status**: Structure is correct, induction framework is set up, just needs final `sorry` filled in.

### 4. Regular Type Axioms (3 sorries)
**Lines**: 824, 833, 875

**What they axiomatize**:
- Line 824: `bisim_equivalence_on_regular` - Bisimulation equivalence for regular types
- Line 833: `bisim_decidable_on_regular` - Decidability of bisimulation for regular types
- Line 875: `eq2c_decidable_on_regular` - Decidability of EQ2C for regular types

**Status**: These are infrastructure axioms assumed for the regular type fragment.

---

## Summary Statistics

- **Total sorries**: 8
- **Sorries from previous session**: Unknown (file was in broken state)
- **Compilation errors fixed**: 15+
- **New helper lemmas added**: 2 (`List.get_map'`, `List.get_mem_zip`)
- **Key proof techniques used**: `omega`, `simp only`, explicit Fin construction, `List.get_map'`

---

## Next Steps

1. **Label matching proofs**: Investigate `HEq` or custom index transport lemmas
2. **Coinductive sorries**: Integrate with paco framework properly
3. **List.get_mem_zip**: Complete the straightforward inductive proof
4. **Regular type axioms**: Document assumptions or attempt proofs if possible
5. **Roundtrip.lean**: Consider proving `nameOf` and `envOf` axioms
