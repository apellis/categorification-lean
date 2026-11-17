/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.VacuumK0

/-!
# Webster's categorification for an empty sequence of highest weights

B. Webster, arXiv:1309.3796v2, Definitions 4.3 and 4.6 and Theorem 4.38.
With no red strands every nonempty word is violated. The empty block therefore
accounts for the entire Grothendieck group.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR Categorification.Graded
open scoped DirectSum

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k)

private abbrev emptyWeights (J : Type*) : Fin 0 → J →₀ ℕ := Fin.elim0

local notation "Λ₀" => emptyWeights I

omit [DecidableEq I] in
private theorem ordered_noRed {ν : Multiset I} (s : Seq (stendhalWeight 0 ν)) : IsRedOrdered s :=
  fun _ _ r => r.elim0

omit [DecidableEq I] in
private theorem violated_noRed {ν : Multiset I} (hν : ν ≠ 0) (s : Seq (stendhalWeight 0 ν)) :
    IsViolated s := by
  have h : 0 < Multiset.card (stendhalWeight 0 ν) := by
    simpa [stendhalWeight] using Multiset.card_pos.mpr hν
  refine ⟨h, ?_⟩
  cases s.lbl ⟨0, h⟩ with
  | inl _ => rfl
  | inr r => exact r.elim0

/-- With no red strands the nonzero black weights give the zero algebra
(Webster, arXiv:1309.3796v2, Definitions 4.3 and 4.6). -/
theorem subsingleton_emptyTensorAlgebra {ν : Multiset I} (hν : ν ≠ 0) :
    Subsingleton (TensorProductAlgebra k Q Λ₀ ν) := by
  classical
  let J := StendhalAlgebra.violatedIdeal k Q Λ₀ ν
  have hsum : ∑ s, StendhalAlgebra.e (Q := Q) (Λ := Λ₀) s (ordered_noRed s) =
      (1 : StendhalAlgebra k Q Λ₀ ν) := by
    apply KLR.Corner.ext
    rw [KLR.Corner.val_sum, KLR.Corner.val_one]
    change _ = StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν
    unfold StendhalAlgebraAllOrders.redOrderedIdem
    simp [ordered_noRed, StendhalAlgebra.e]
  have hmem : 1 ∈ J := by
    rw [← hsum]
    exact sum_mem fun s _ => TwoSidedIdeal.subset_span
      ⟨s, ordered_noRed s, violated_noRed hν s, rfl⟩
  apply subsingleton_of_zero_eq_one
  exact (J.ringCon.eq.2 ((J.mem_iff 1).1 hmem)).symm

section Field

variable {k : Type*} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (G : KLR.GradingDatum (stendhalQ Q (emptyWeights I)))

local notation "R" => LaurentPolynomial ℤ
local notation "K" => fun ν : Multiset I => K0 (tensorProductGrade G ν)

private theorem emptyTensorK0_eq_zero {ν : Multiset I} (hν : ν ≠ 0) (x : K ν) : x = 0 := by
  let := subsingleton_emptyTensorAlgebra Q hν
  induction x using K0.induction_on with
  | of P =>
    let : Subsingleton P.carrier := ⟨fun x y =>
      (Module.eq_zero_of_zero_eq_one (x := x)
        (Subsingleton.elim (0 : TensorProductAlgebra k Q (emptyWeights I) ν) 1)).trans
      (Module.eq_zero_of_zero_eq_one (x := y)
        (Subsingleton.elim (0 : TensorProductAlgebra k Q (emptyWeights I) ν) 1)).symm⟩
    exact K0.of_eq_zero_of_subsingleton P
  | zero => rfl
  | add x y hx hy => simp [hx, hy]
  | neg x hx => simp [hx]

/-- **Webster, arXiv:1309.3796v2, Theorem 4.38**, for the empty tuple.
The sole surviving summand is the top-weight line, identified with the empty
tensor product over the Laurent polynomials. -/
def emptyTensorK0Equiv : (⨁ ν : Multiset I, K ν) ≃ₗ[R] R := by
  classical
  let c := DirectSum.component R (Multiset I) K 0
  have hc : Function.Bijective c := by
    constructor
    · intro x y h
      ext ν
      by_cases hν : ν = 0
      · subst ν
        exact h
      · exact (emptyTensorK0_eq_zero Q G hν (x ν)).trans
          (emptyTensorK0_eq_zero Q G hν (y ν)).symm
    · intro z
      exact ⟨DirectSum.lof R _ K 0 z, DirectSum.component.lof_self _ _ _⟩
  exact (LinearEquiv.ofBijective c hc).trans (tensorProductVacuumK0Equiv G)

end Field

end Categorification.Stendhal
