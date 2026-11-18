/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorRestrictionAdjoint
import Categorification.WeightedKLR.RedStrands.NormalizedBlackProjectives
import Categorification.WeightedKLR.RedStrands.RedLabelRootDatum

/-!
# Equal-colour projective commutation

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.35, in the projective normalization.
On a black-content block the extra copies have the shifts of the quantum integer
of its coroot pairing.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR Categorification.Graded QuantumGroup QuantumGroup.UDot LieLean LieLean.QuantumGroup
  LieLean.QuantumGroup.GrandLoop LusztigF

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "v" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩
variable {I : Type} {k : Type*} [DecidableEq I] [Field k] [Finite I]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
local notation "R" => redLabelDatum C
local notation "wt" => fun r => redLabelWeight C (Λ r)
local notation "hR" => redLabelDatum_xRegular C
local notation "hwt" => fun r i => Eq.symm (redLabelWeight_coroot C (Λ r) i)
local notation "η" => tensorModuleEquiv C hQ hR Λ wt hwt
local notation "ι" => DirectSum.lof LP _ (tensorProjectiveGroup C hQ Λ)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "B" => tensorProductGrade G
local notation "V" => TensorSpace wt
/-- The coroot pairing of the red highest weight minus the black content. -/
def blackBlockPairing (i : I) (β : Multiset I) : ℤ :=
  (∑ r, (Λ r i : ℤ)) - (β.map (A C i)).sum

omit [Finite I] [DecidableEq I] in
/-- Passing the downward strand lowers its own coroot pairing by two. -/
theorem blackBlockPairing_cons_self (i : I) (β : Multiset I) :
    blackBlockPairing C Λ i ({i} + β) = blackBlockPairing C Λ i β - 2 := by
  simp only [blackBlockPairing, Multiset.map_add, Multiset.map_singleton, Multiset.sum_add,
    Multiset.sum_singleton, A_self]
  omega

/-- Direct sum of the first n grading shifts in a prescribed family. -/
def sumShifts {A : Type*} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
    [GradedAlgebra 𝒜] (P : GProj 𝒜) (s : ℕ → ℤ) : ℕ → GProj 𝒜
  | 0 => GProj.zeroObj 𝒜
  | j + 1 => (sumShifts P s j).prod (P.shift (s j))

/-- The shifted copies contributing a positive quantum integer of size n. -/
def blackQuantumCopies (i : I) (β : Multiset I) (P : GProj (B β)) (n : ℕ) : GProj (B β) :=
  sumShifts P (fun j => (C.toLusztig.d i : ℤ) * (2 * j + 1 - (n : ℤ))) n

private theorem image_sumShifts (β : Multiset I) (P : GProj (B β)) (s : ℕ → ℤ) (n : ℕ) :
    (η (ι β (K0.of (sumShifts P s n))) : V) =
      (∑ j ∈ Finset.range n, v ^ (-(s j))) • (η (ι β (K0.of P)) : V) := by
  induction n with
  | zero =>
    simp [sumShifts, K0.of_eq_zero_of_subsingleton]
    exact (η).map_zero
  | succ j ih =>
    rw [sumShifts, K0.of_prod, map_add, map_add, Submodule.coe_add, ih, Finset.sum_range_succ,
      add_smul, ← K0.T_smul_of, map_smul, LinearEquiv.map_smulₛₗ, Submodule.coe_smul, tensor_laurent_smul]
    simp [integralLaurentEval_T]

private theorem image_quantumCopies (i : I) (β : Multiset I) (P : GProj (B β)) (n : ℕ) :
    (η (ι β (K0.of (blackQuantumCopies C hQ Λ i β P n))) : V) =
      qIntZ (v ^ C.toLusztig.d i) n • (η (ι β (K0.of P)) : V) := by
  rw [blackQuantumCopies, image_sumShifts, qIntZ_natCast (sub_inv_ne_zero_of_pow_ne_one
    (pow_ne_zero _ RatFunc.X_ne_zero) (vd_pow_ne_one (D := C.toLusztig) (fun _ => ratFunc_X_pow_ne_one) i)),
    LieLean.QuantumGroup.qInt]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [inv_pow, ← pow_mul, ← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_neg,
    ← zpow_add₀ RatFunc.X_ne_zero]
  congr 1
  push_cast [Nat.cast_sub (by omega : j ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
  ring

/-- Restrict and then induce at the same colour. If the block has no removable
strand of this colour the composite is zero. -/
def blackIndRaiseProj (i : I) (β : Multiset I) (P : GProj (B β)) : GProj (B β) :=
  if h : i ∈ β then
    let e : {i} + β.erase i = β := (Multiset.singleton_add ..).trans (Multiset.cons_erase h)
    e ▸ blackIndProj G i (β.erase i) (blackRaiseProj G i (β.erase i) C hQ (e.symm ▸ P))
  else GProj.zeroObj _

omit [Finite I] in
private theorem class_indRaise (i : I) (β : Multiset I) (P : GProj (B β)) :
    ι β (K0.of (blackIndRaiseProj C hQ Λ i β P)) =
      blackLower G i (blackRaise G i C hQ (ι β (K0.of P))) := by
  unfold blackIndRaiseProj
  split
  next h =>
    rw [lof_of_transport G, ← blackIndK0_of, ← blackLower_lof, ← blackRaiseK0_of, ← blackRaise_lof,
      lof_of_transport G]
  next h =>
    rw [blackRaise_lof_of_notMem _ _ _ _ _ h, map_zero, K0.of_eq_zero_of_subsingleton, map_zero]

local notation "EF" => fun i β P => blackRaiseProj G i β C hQ (blackIndProj G i β P)
local notation "FE" => blackIndRaiseProj C hQ Λ
local notation "copies" => blackQuantumCopies C hQ Λ

private local instance blockHasGdim (β : Multiset I) : HasGdim (B β) := by
  let := tensorProductAlgebra_finite Λ β hQ
  exact HasGdim.of_finiteDimensional _

private theorem image_commutator (i : I) (β : Multiset I) (P : GProj (B β)) :
    (η (ι β (K0.of (EF i β P))) : V) =
      (η (ι β (K0.of (FE i β P))) : V) +
      qIntZ (v ^ C.toLusztig.d i) (blackBlockPairing C Λ i β) • (η (ι β (K0.of P)) : V) := by
  rw [← blackRaiseK0_of, ← blackRaise_lof, ← blackIndK0_of, ← blackLower_lof, class_indRaise,
    tensorModuleEquiv_E, tensorModuleEquiv_F, tensorModuleEquiv_F, tensorModuleEquiv_E]
  simpa only [↓reduceIte, AddMonoidHom.sub_apply, AddMonoidHom.finsetSum_apply, redLabelWeight_coroot,
    rootSum_apply_coroot, blackBlockPairing] using tensorRepresentation_commute_black wt i i (η (ι β (K0.of P)))
    ((∑ r, (wt r).1) - (redLabelDatum C).rootSum β.toFinsupp) (tensorModuleEquiv_torus_block C hQ hR Λ wt hwt β _)

/-- Webster, arXiv:1309.3796v2, §4.7, Lemma 4.35, at nonnegative coroot
pairing. The extra summands belong to the induction-then-restriction composite. -/
theorem blackRaiseInd_iso_of_nonneg (i : I) (β : Multiset I) (P : GProj (B β))
    (h : 0 ≤ blackBlockPairing C Λ i β) :
    Nonempty ((EF i β P).Iso ((FE i β P).prod (copies i β P (blackBlockPairing C Λ i β).toNat))) := by
  apply K0.of_eq_of_iff.mp
  apply (show Function.Injective (ι β) from DirectSum.of_injective (β := tensorProjectiveGroup C hQ Λ) β)
  apply (η).injective
  apply Subtype.ext
  rw [K0.of_prod, map_add, map_add, Submodule.coe_add, image_quantumCopies, Int.toNat_of_nonneg h]
  exact image_commutator C hQ Λ i β P

/-- Webster, arXiv:1309.3796v2, §4.7, Lemma 4.35, at nonpositive coroot
pairing. The extra summands belong to the restriction-then-induction composite. -/
theorem blackIndRaise_iso_of_nonpos (i : I) (β : Multiset I) (P : GProj (B β))
    (h : blackBlockPairing C Λ i β ≤ 0) :
    Nonempty ((FE i β P).Iso ((EF i β P).prod (copies i β P (-(blackBlockPairing C Λ i β)).toNat))) := by
  apply K0.of_eq_of_iff.mp
  apply (show Function.Injective (ι β) from DirectSum.of_injective (β := tensorProjectiveGroup C hQ Λ) β)
  apply (η).injective
  apply Subtype.ext
  rw [K0.of_prod, map_add, map_add, Submodule.coe_add, image_quantumCopies,
    Int.toNat_of_nonneg (neg_nonneg.mpr h), qIntZ_neg]
  rw [image_commutator C hQ Λ i β P, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]

end Categorification.Stendhal.FirstWeight
