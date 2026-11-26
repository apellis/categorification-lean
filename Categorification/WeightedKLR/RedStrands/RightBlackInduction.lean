/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleFunctors
import Categorification.WeightedKLR.RedStrands.BlackRestrictionProjective
import Categorification.WeightedKLR.RedStrands.RightBoundaryProjectives
import Categorification.Algebra.Graded.TensorHomDuality
import Categorification.Algebra.Graded.G0

/-!
# Graded right black induction

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §4.6, the
functor `Fᵢ M = M ⊗_{T^λ_ν} e' T^λ_{ν+i}` on right modules, after Theorem 4.31. Right modules are
left modules over the opposite algebras, and `Fᵢ` is induction along `appendBlackOp`
(`blackF`). Here it is made graded: the corner `e' T^λ_{ν+i}` carries the grading of the
opposite algebra, and `Fᵢ N` carries the balanced tensor product grading
(`rightBlackInd`, for finite-dimensional graded modules).

On the right sequence projective `e(s) T^λ_ν`, `Fᵢ` gives the right sequence projective of the
loading with the black strand appended (`rightBlackIndSequenceIso`), the right-module form of
the principal-projective case of Lemma 4.37. Cutting `Fᵢ N` by a loading idempotent `e(t)` gives
`N ⊗ e' T^λ_{ν+i} e(t)`; when the corner is projective (Theorem 4.31, `projective_blackRes_regular`)
this is `HOM(X_t, N)` for the dual `X_t` of the cut corner (`cornerCutDual`,
`gdimPoly_rightBlackInd_cut`).

## Main definitions and results

* `rightBlackInd N` : the graded module `Fᵢ N`.
* `rightBlackIndSequenceIso` : `Fᵢ (e(s) T^λ_ν) ≅ e(s i) T^λ_{ν+i}`.
* `cornerCutDual t` : the dual of the cut corner `e' T^λ_{ν+i} e(t)`, a graded projective.
* `gdimPoly_rightBlackInd_cut` : `gdim (Fᵢ N) e(t) = gdim HOM(cornerCutDual t, N)`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR Categorification.Graded DirectSum MulOpposite InductionAlong BalancedTensor
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  (G : GradingDatum (stendhalQ Q Λ)) (i : I) (ν : Multiset I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "T'" => TensorProductAlgebra k Q Λ νᵢ
local notation "src" => oppositeGrade (tensorProductGrade G ν)
local notation "dst" => oppositeGrade (tensorProductGrade G νᵢ)
local notation "φ" => appendBlackOp Q Λ i ν
local notation "Mc" => Corner (appendBlackOp Q Λ i ν)
local notation "cornerGr" => Graded.submodule dst (lIdeal (appendBlackOp Q Λ i ν 1))

theorem appendBlackOp_smul (c : k) (x : Tᵐᵒᵖ) : φ (c • x) = c • φ x :=
  congrArg op (map_smul (appendBlack Q Λ i ν) c x.unop)

theorem appendBlackOp_mem_grade {d : ℤ} {x : Tᵐᵒᵖ} (hx : x ∈ src d) : φ x ∈ dst d :=
  appendBlack_mem_grade Q Λ i ν G hx

private local instance : IsScalarTower k T'ᵐᵒᵖ Mc where
  smul_assoc c a z := Subtype.ext (smul_mul_assoc c a z.val)

private local instance : IsScalarTower k Tᵐᵒᵖᵐᵒᵖ Mc where
  smul_assoc c r z := Subtype.ext (by
    change z.val * φ (c • r.unop) = c • (z.val * φ r.unop)
    rw [appendBlackOp_smul, mul_smul_comm])

/-- The corner `e' T^λ_{ν+i}`, read in the opposite algebra, as a graded projective. -/
private def cornerProj : GProj dst :=
  GProj.ofIdempotent (φ 1) (unit_mul_unit φ) (appendBlackOp_mem_grade G i ν SetLike.GradedOne.one_mem)

private local instance : DirectSum.Decomposition cornerGr := (cornerProj G i ν).decomposition

private local instance : SetLike.GradedSMul (oppositeGrade src) cornerGr where
  smul_mem {l d} r z hr hz := by
    change z.val * φ r.unop ∈ dst (l + d)
    rw [show l + d = d + l from add_comm l d]
    exact SetLike.GradedMul.mul_mem (A := dst) hz (appendBlackOp_mem_grade G i ν hr)

private local instance : SetLike.GradedSMul dst cornerGr := (cornerProj G i ν).gradedSMul

/-- The grading of `e' T^λ_{ν+i} ⊗ N` is a decomposition. -/
@[instance_reducible] private def rightBlackIndDecomposition (N : GFin src) :
    Decomposition (balancedGrading T'ᵐᵒᵖ Tᵐᵒᵖ cornerGr N.grading) :=
  balancedDecomposition (B := T'ᵐᵒᵖ) (ℳ := cornerGr) (𝒩 := N.grading) src
    (op_smul_mem_of_mem src cornerGr)

private theorem rightBlackIndGradedSMul (N : GFin src) :
    SetLike.GradedSMul dst (balancedGrading T'ᵐᵒᵖ Tᵐᵒᵖ cornerGr N.grading) :=
  gradedSMul_balanced (B := T'ᵐᵒᵖ) (A := Tᵐᵒᵖ) (ℳ := cornerGr) (𝒩 := N.grading) dst

/-! ### Principal projectives -/

/-- Multiplication `e' T^λ_{ν+i} ⊗ (e T^λ_ν) → T^λ_{ν+i}`, read in the opposite algebras. -/
private def rightIndMul (e : Tᵐᵒᵖ) :
    BalancedTensor k T'ᵐᵒᵖ Tᵐᵒᵖ Mc (leftIdeal e) →ₗ[T'ᵐᵒᵖ] T'ᵐᵒᵖ :=
  (lIdeal (φ 1)).subtype.comp <|
    (BalancedTensor.rid k T'ᵐᵒᵖ Tᵐᵒᵖ Mc).toLinearMap.comp
      (BalancedTensor.mapRight (leftIdeal e).subtype)

private theorem rightIndMul_tmul (e : Tᵐᵒᵖ) (b : Mc) (x : leftIdeal e) :
    rightIndMul (Q := Q) (Λ := Λ) i ν e (BalancedTensor.tmul b x) = b.val * φ x.val := rfl

/-- `e' T^λ_{ν+i} ⊗ (e T^λ_ν) ≅ φ(e) T^λ_{ν+i}`, in the opposite algebras. -/
private def rightIndPrincipalEquiv {e : Tᵐᵒᵖ} (he : IsIdempotentElem e) :
    BalancedTensor k T'ᵐᵒᵖ Tᵐᵒᵖ Mc (leftIdeal e) ≃ₗ[T'ᵐᵒᵖ] leftIdeal (φ e) := by
  let p : leftIdeal e := ⟨e, he.eq⟩
  let f := (rightIndMul (Q := Q) (Λ := Λ) i ν e).codRestrict (leftIdeal (φ e)) fun t => by
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
  let g : leftIdeal (φ e) →ₗ[T'ᵐᵒᵖ] BalancedTensor k T'ᵐᵒᵖ Tᵐᵒᵖ Mc (leftIdeal e) :=
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

variable [Module.Finite k (TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν))ᵐᵒᵖ]

private theorem finite_corner : Module.Finite k Mc :=
  Module.Finite.of_injective ((lIdeal (φ 1)).subtype.restrictScalars k) Subtype.val_injective

variable {G i ν} in
private theorem finite_rightBlackInd (N : GFin src) :
    Module.Finite k (BalancedTensor k T'ᵐᵒᵖ Tᵐᵒᵖ Mc N.carrier) := by
  have := finite_corner (Q := Q) (Λ := Λ) i ν
  have : Module.Finite k (Mc ⊗[k] N.carrier) := Module.Finite.tensorProduct k _ _
  exact Module.Finite.of_surjective
    (((BalancedTensor.mk k T'ᵐᵒᵖ Tᵐᵒᵖ Mc N.carrier).restrictScalars k :
      Mc ⊗[k] N.carrier →ₗ[k] BalancedTensor k T'ᵐᵒᵖ Tᵐᵒᵖ Mc N.carrier))
    (BalancedTensor.mk_surjective (k := k) (B := T'ᵐᵒᵖ) (A := Tᵐᵒᵖ) (M := Mc) (N := N.carrier))

/-- **Webster's `Fᵢ` on graded right modules** (arXiv:1309.3796v2, §4.6, after Theorem 4.31):
`N ↦ N ⊗_{T^λ_ν} e' T^λ_{ν+i}`, written as `e' T^λ_{ν+i} ⊗ N` over the opposite algebras, with the
balanced tensor product grading. -/
def rightBlackInd (N : GFin src) : GFin dst where
  carrier := BalancedTensor k T'ᵐᵒᵖ Tᵐᵒᵖ Mc N.carrier
  grading := balancedGrading T'ᵐᵒᵖ Tᵐᵒᵖ cornerGr N.grading
  decomposition := rightBlackIndDecomposition G i ν N
  gradedSMul := rightBlackIndGradedSMul G i ν N
  finiteDimensional := finite_rightBlackInd N

variable [Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]

/-- **Right black induction of a principal projective** (Webster, arXiv:1309.3796v2, §4.6 and
Lemma 4.37, for right modules): `Fᵢ (e T^λ_ν) ≅ φ(e) T^λ_{ν+i}` as graded modules. -/
def rightBlackIndPrincipalIso {e : Tᵐᵒᵖ} (he : IsIdempotentElem e) (he0 : e ∈ src 0) :
    (rightBlackInd G i ν (GProj.ofIdempotent e he he0).toGFin).Iso
      (GProj.ofIdempotent (φ e) (he.map φ) (appendBlackOp_mem_grade G i ν he0)).toGFin :=
  GradedEquiv.ofPreserves (rightIndPrincipalEquiv (Q := Q) (Λ := Λ) i ν he) fun d y hy => by
    change rightIndMul (Q := Q) (Λ := Λ) i ν e y ∈ dst d
    apply balancedGrading_map_mem dst ((rightIndMul (Q := Q) (Λ := Λ) i ν e).restrictScalars k) _ hy
    intro a b z x hz hx
    rw [LinearMap.restrictScalars_apply, rightIndMul_tmul]
    exact SetLike.GradedMul.mul_mem (A := dst) hz (appendBlackOp_mem_grade G i ν hx)

end Categorification.Stendhal
