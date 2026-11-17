/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackInduction

/-!
# Black induction of a principal projective

Webster, arXiv:1309.3796v2, §4.6 after Theorem 4.31. Right black-strand induction
sends a homogeneous principal projective to the one cut out by appending its idempotent.
-/
noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra Categorification.Graded MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I k : Type*} {ℓ : ℕ} [DecidableEq I] [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  (G : GradingDatum (stendhalQ Q Λ)) (i : I) (ν : Multiset I)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "src" => tensorProductGrade G ν
local notation "dst" => tensorProductGrade G νᵢ
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "T'" => TensorProductAlgebra k Q Λ νᵢ
local notation "φ" => appendBlack Q Λ i ν
local notation "Mc" => InductionAlong.Corner (φ : T →ₙ+* T')
private local instance : IsScalarTower k T' Mc where
  smul_assoc c a z := Subtype.ext (smul_mul_assoc c a z.val)

private local instance : IsScalarTower k Tᵐᵒᵖ Mc where
  smul_assoc c r z := Subtype.ext (by
    change z.val * φ (c • r.unop) = c • (z.val * φ r.unop)
    rw [map_smul, mul_smul_comm])

private def indMul (e : T) : BalancedTensor k T' T Mc (leftIdeal e) →ₗ[T'] T' :=
  (lIdeal (φ 1)).subtype.comp <|
    (BalancedTensor.rid k T' T Mc).toLinearMap.comp (BalancedTensor.mapRight (leftIdeal e).subtype)

private theorem indMul_tmul (e : T) (b : Mc) (x : leftIdeal e) :
    indMul (Q := Q) (Λ := Λ) i ν e (BalancedTensor.tmul b x) = b.val * φ x.val := rfl

private def indPrincipalEquiv {e : T} (he : IsIdempotentElem e) :
    BalancedTensor k T' T Mc (leftIdeal e) ≃ₗ[T'] leftIdeal (φ e) := by
  let p : leftIdeal e := ⟨e, he.eq⟩
  let f := (indMul (Q := Q) (Λ := Λ) i ν e).codRestrict (leftIdeal (φ e)) fun t => by
    induction t using BalancedTensor.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul b x =>
      change (b.val * φ x.val) * φ e = b.val * φ x.val
      rw [mul_assoc, ← map_mul, mem_leftIdeal.mp x.2]
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  have inc (z : leftIdeal (φ e)) : z.val ∈ lIdeal (φ 1) := by
    change z.val * φ 1 = z.val
    conv_lhs => rw [← mem_leftIdeal.mp z.property, mul_assoc, ← map_mul, mul_one]
    exact z.property
  let g : leftIdeal (φ e) →ₗ[T'] BalancedTensor k T' T Mc (leftIdeal e) :=
    { toFun := fun b => BalancedTensor.tmul (⟨b.val, inc b⟩ : Mc) p
      map_add' := fun x y => BalancedTensor.add_tmul (⟨x.val, inc x⟩ : Mc) (⟨y.val, inc y⟩ : Mc) p
      map_smul' := fun c x => BalancedTensor.smul_tmul' c (⟨x.val, inc x⟩ : Mc) p }
  apply LinearEquiv.ofLinearMap f g
  · ext x
    exact x.property
  · apply BalancedTensor.extB
    intro b x
    change BalancedTensor.tmul (op x.val • b) p = BalancedTensor.tmul b x
    rw [BalancedTensor.op_smul_tmul]
    exact congrArg (BalancedTensor.tmul b) (Subtype.ext (mem_leftIdeal.mp x.property))

/-- Right black-strand induction sends a degree-zero principal projective to the one at the
appended idempotent (Webster, arXiv:1309.3796v2, Lemma 4.37). -/
theorem blackIndK0_ofIdempotent {e : T} (he : IsIdempotentElem e) (he0 : e ∈ src 0) :
    blackIndK0 G i ν (K0.of (GProj.ofIdempotent e he he0)) =
      K0.of (GProj.ofIdempotent (𝒜 := dst) (appendBlack Q Λ i ν e) (he.map (φ)) (appendBlack_mem_grade Q Λ i ν G he0)) := by
  rw [blackIndK0_of]
  apply K0.of_eq_of_iso
  refine GradedEquiv.ofPreserves (indPrincipalEquiv (Q := Q) (Λ := Λ) i ν he) ?_
  intro d y hy
  change indMul (Q := Q) (Λ := Λ) i ν e y ∈ dst d
  apply balancedGrading_map_mem dst ((indMul (Q := Q) (Λ := Λ) i ν e).restrictScalars k) _ hy
  intro a b z x hz hx
  rw [LinearMap.restrictScalars_apply, indMul_tmul]
  exact SetLike.GradedMul.mul_mem (A := dst) hz (appendBlack_mem_grade Q Λ i ν G hx)

end Categorification.Stendhal
