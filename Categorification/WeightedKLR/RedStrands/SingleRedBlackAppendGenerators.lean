/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleRedBlackInductionIdealMul
import Categorification.WeightedKLR.RedStrands.BlackMixedSquare
import Categorification.WeightedKLR.RedStrands.BlackNewStrandProjection

set_option backward.isDefEq.respectTransparency false

/-!
# The black-strand map on the dots and crossings, one red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6 and
Theorem 4.20, one red strand. Adding a black strand on the right sends `insertRed z` to
`insertRed (cL z)` (`SingleRed.appendBlack_insertRed`); in particular an old dot or crossing
stays at its position, cut by `appendBlack 1`. On the projectives `e(𝐢 i) T^λ_β` the cut is
invisible (`SingleRed.idemRightMul_appendBlackOpOfEq_insertRed`).
-/

noncomputable section

namespace Categorification.Stendhal.SingleRed

open CategoryTheory MulOpposite KLR KLRAlgebra KLRAlgebra.AbsentColour InductionAlong
  QuantumGroup

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (Λ : Fin 1 → I →₀ ℕ)

/-- **Adding a black strand on the right commutes with inserting the red strand on the left**
(Webster, arXiv:1309.3796v3, §4.6, Theorem 4.20): `appendBlack (insertRed z) = insertRed (cL z)`.
-/
theorem appendBlack_insertRed (i : I) (ν : Multiset I) (z : KLRAlgebra k Q ν) :
    appendBlack Q Λ i ν (insertRed Q Λ ν z) = insertRed Q Λ ({i} + ν) (cL Q i ν z) := by
  have h := appendBlack_cyclotomicEquiv i ν Q Λ
    (CycKLR.mk k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ 0 j) ν z)
  change appendBlack Q Λ i ν (cyclotomicProjection Q Λ ν _) =
    cyclotomicProjection Q Λ ({i} + ν) _ at h
  rwa [AbsentColour.cyclotomicLast_mk, cyclotomicProjection, CycKLR.lift_mk, cyclotomicProjection,
    CycKLR.lift_mk] at h

/-- The last strand of the content `{i} + μ`. -/
def lastPos (i : I) (μ : Multiset I) : Fin (Multiset.card (({i} : Multiset I) + μ)) :=
  ⟨Multiset.card μ, by simp⟩

/-- **The dot on the appended strand** is the dot `x_last` on the last black strand, cut by
`appendBlack 1` (Webster, arXiv:1309.3796v3, §4.6, one red strand). -/
theorem appendedDot_eq_insertRed (i : I) (μ : Multiset I) :
    appendedDot Q Λ i μ =
      insertRed Q Λ ({i} + μ) (KLRAlgebra.x (lastPos i μ)) * appendBlack Q Λ i μ 1 := by
  rw [appendedDot_eq, affineTensorProjection_x, insertRed_x]
  congr 1
  refine congrArg (TensorProductAlgebra.mk Q Λ _) (Subtype.ext ?_)
  change _ * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ _ = StendhalAlgebraAllOrders.x _
  rw [redOrderedIdem_eq_one, mul_one]
  congr 1
  apply Fin.ext
  simp [lastPos, blackPos, stendhalWeight]

omit [DecidableEq I] [Field k] in
/-- A right multiplication from `T e` does not see a left factor `u` with `e u = e`. -/
theorem idemRightMul_mul_left_of_mul_eq {T : Type} [Ring T] {e f u : T} (heu : e * u = e)
    (c : T) (hf : IsIdempotentElem f) : idemRightMul e f (u * c) hf = idemRightMul e f c hf := by
  ext ⟨x, hx⟩
  have hx' : x * e = x := hx
  have hxu : x * u = x := by
    conv_lhs => rw [← hx']
    rw [mul_assoc, heu, hx']
  change x * (u * c) * f = x * c * f
  rw [← mul_assoc, hxu]

/-- The cut `appendBlack 1` fixes the projective `e(𝐬 i) T^λ_β`. -/
theorem redFirstIdem_appendSeq_mul_appendBlack_one (i : I) {μ β : Multiset I}
    (h : ({i} : Multiset I) + μ = β) (s : Seq μ) :
    redFirstIdem Q Λ β (appendSeq i h s) * castOp Q Λ h (op (appendBlack Q Λ i μ 1)) =
      redFirstIdem Q Λ β (appendSeq i h s) := by
  subst h
  rw [← appendBlackOpOfEq_redFirstIdem, appendBlackOpOfEq_apply]
  change appendBlackOp Q Λ i μ _ * op (appendBlack Q Λ i μ 1) = appendBlackOp Q Λ i μ _
  rw [← op_unop (redFirstIdem Q Λ μ s), appendBlackOp_op, ← op_mul, ← map_mul, one_mul]

/-- **The dot on the appended strand**, as a right multiplication on `e(𝐬 i) T^λ_β`, is the dot
on the last black strand (Webster, arXiv:1309.3796v3, §4.6, one red strand). -/
theorem idemRightMul_castOp_appendedDot (i : I) {μ β : Multiset I}
    (h : ({i} : Multiset I) + μ = β) (s : Seq μ) :
    idemRightMul (redFirstIdem Q Λ β (appendSeq i h s)) (redFirstIdem Q Λ β (appendSeq i h s))
        (castOp Q Λ h (op (appendedDot Q Λ i μ))) (redFirstIdem_isIdempotentElem Q Λ β _) =
      idemRightMul (redFirstIdem Q Λ β (appendSeq i h s)) (redFirstIdem Q Λ β (appendSeq i h s))
        (op (insertRed Q Λ β (KLRAlgebra.x ⟨Multiset.card μ, by rw [← h]; simp⟩)))
        (redFirstIdem_isIdempotentElem Q Λ β _) := by
  have hcut := redFirstIdem_appendSeq_mul_appendBlack_one Q Λ i h s
  subst h
  change idemRightMul _ _ (op (appendedDot Q Λ i μ)) _ = _
  rw [appendedDot_eq_insertRed, op_mul]
  exact idemRightMul_mul_left_of_mul_eq hcut _ _

/-- **An old dot**, as a right multiplication on `e(𝐬 i) T^λ_β`, under the black-strand map
stays a dot at the same position (Webster, arXiv:1309.3796v3, §4.6, one red strand). -/
theorem idemRightMul_appendBlackOpOfEq_insertRed_x (i : I) {μ β : Multiset I}
    (h : ({i} : Multiset I) + μ = β) (s s' : Seq μ) (b : Fin (Multiset.card μ)) :
    idemRightMul (redFirstIdem Q Λ β (appendSeq i h s)) (redFirstIdem Q Λ β (appendSeq i h s'))
        (appendBlackOpOfEq Q Λ i h (op (insertRed Q Λ μ (KLRAlgebra.x b))))
        (redFirstIdem_isIdempotentElem Q Λ β _) =
      idemRightMul (redFirstIdem Q Λ β (appendSeq i h s)) (redFirstIdem Q Λ β (appendSeq i h s'))
        (op (insertRed Q Λ β (KLRAlgebra.x ⟨b.val, by rw [← h]; simp⟩)))
        (redFirstIdem_isIdempotentElem Q Λ β _) := by
  have hcut := redFirstIdem_appendSeq_mul_appendBlack_one Q Λ i h s
  subst h
  have h1 : insertRed Q Λ ({i} + μ) (cL Q i μ 1) = appendBlack Q Λ i μ 1 := by
    rw [← appendBlack_insertRed, map_one]
  rw [appendBlackOpOfEq_apply]
  change idemRightMul _ _ (appendBlackOp Q Λ i μ (op _)) _ = _
  rw [appendBlackOp_op, appendBlack_insertRed, cL_x, map_mul, h1, op_mul]
  refine (idemRightMul_mul_left_of_mul_eq hcut _ _).trans ?_
  congr 4

end Categorification.Stendhal.SingleRed
