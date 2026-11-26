/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.BalancedInduction
import Categorification.Algebra.Graded.Idempotent
import Categorification.Algebra.Graded.ProjectiveCharacter

/-!
# Tensoring with a cyclic projective `A e`

For an idempotent `e` of a ring `A` and a right `A`-module `M`, `m ⊗ a ↦ m a` is an isomorphism
`M ⊗_A A e ≅ M e` (`idealRid`). It is degree preserving for gradings, so for `e` of degree zero
`gdim (M ⊗_A A e) = gdim (M e)` (`gdimPoly_balancedGrading_leftIdeal`). In particular, for a
graded bimodule `M` the functor `N ↦ M ⊗_A N` sends the cyclic projective `A e` to `M e`, as in
the computation of the braiding functors of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v2, §6.1, on projective modules.

## Main definitions and results

* `idealRid he` : `M ⊗_A A e ≃ M e`.
* `gdimPoly_balancedGrading_leftIdeal` : `gdim (M ⊗_A A e) = gdim (M e)`.
-/

noncomputable section

namespace Categorification.Graded

open DirectSum MulOpposite BalancedTensor

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Algebra k B] {A : Type*} [Ring A]
  [Algebra k A]
  {M : Type*} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M] [Module Aᵐᵒᵖ M]
  [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]

theorem op_smul_mem_idemSubspace_of_mem_leftIdeal {e a : A} (ha : a ∈ leftIdeal e) (m : M) :
    op a • m ∈ idemSubspace k M (op e) := by
  rw [mem_idemSubspace, smul_smul, ← op_mul, mem_leftIdeal.1 ha]

variable (k B M) in
/-- The balanced bilinear map `(m, a) ↦ m a` on `M × A e`. -/
def idealRidBil (e : A) : M →ₗ[k] leftIdeal e →ₗ[k] idemSubspace k M (op e) where
  toFun m :=
    { toFun a := ⟨op (a : A) • m, op_smul_mem_idemSubspace_of_mem_leftIdeal a.2 m⟩
      map_add' a a' := Subtype.ext (by
        change op ((a : A) + a') • m = op (a : A) • m + op (a' : A) • m
        rw [op_add, add_smul])
      map_smul' c a := Subtype.ext (by
        change op (c • (a : A)) • m = c • (op (a : A) • m)
        rw [op_smul, smul_assoc]) }
  map_add' m m' := LinearMap.ext fun a => Subtype.ext (smul_add (op (a : A)) m m')
  map_smul' c m := LinearMap.ext fun a => Subtype.ext (smul_comm (op (a : A)) c m)

theorem idealRidBil_balanced {e : A} (m : M) (a : A) (n : leftIdeal e) :
    idealRidBil k M e (op a • m) n = idealRidBil k M e m (a • n) :=
  Subtype.ext (by
    change op (n : A) • op a • m = op ((a • n : leftIdeal e) : A) • m
    rw [smul_smul, ← op_mul]
    rfl)

variable (B) in
/-- **`M ⊗_A A e ≅ M e`**, `m ⊗ a ↦ m a`, for an idempotent `e`. -/
def idealRid {e : A} (he : IsIdempotentElem e) :
    BalancedTensor k B A M (leftIdeal e) ≃ₗ[k] idemSubspace k M (op e) :=
  LinearEquiv.ofLinearMap
    (lift (idealRidBil k M e) idealRidBil_balanced)
    { toFun m := tmul (m : M) (⟨e, by rw [mem_leftIdeal, he.eq]⟩ : leftIdeal e)
      map_add' m m' := add_tmul _ _ _
      map_smul' c m := smul_tmul c _ _ }
    (LinearMap.ext fun m => Subtype.ext m.2)
    (ext fun m a => by
      change tmul (op (a : A) • m) _ = tmul m a
      rw [op_smul_tmul]
      congr 1
      exact Subtype.ext (mem_leftIdeal.1 a.2))

@[simp] theorem idealRid_tmul {e : A} (he : IsIdempotentElem e) (m : M) (a : leftIdeal e) :
    (idealRid B he (tmul m a : BalancedTensor k B A M (leftIdeal e)) : M) = op (a : A) • m := by
  change ((lift (idealRidBil k M e) idealRidBil_balanced (tmul m a) : idemSubspace k M (op e)) : M) = _
  rw [lift_tmul]
  rfl

section Graded

variable {M : Type*} [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]
  (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul (oppositeGrade 𝒜) ℳ]

/-- **`gdim (M ⊗_A A e) = gdim (M e)`** for an idempotent `e` of degree zero. -/
theorem gdimPoly_balancedGrading_leftIdeal {e : A} (he : IsIdempotentElem e)
    (he0 : e ∈ 𝒜 0) :
    letI := submoduleDecomposition 𝒜 (leftIdeal_isHomogeneous he0)
    letI := balancedDecomposition (B := k) (ℳ := ℳ)
      (𝒩 := Graded.submodule 𝒜 (leftIdeal e)) 𝒜 (op_smul_mem_of_mem 𝒜 ℳ)
    gdimPoly (balancedGrading k A ℳ (Graded.submodule 𝒜 (leftIdeal e))) =
      gdimPoly (idem ℳ (op e)) := by
  let := submoduleDecomposition 𝒜 (leftIdeal_isHomogeneous he0)
  let := balancedDecomposition (B := k) (ℳ := ℳ)
    (𝒩 := Graded.submodule 𝒜 (leftIdeal e)) 𝒜 (op_smul_mem_of_mem 𝒜 ℳ)
  let := idemDecomposition ℳ (show op e ∈ oppositeGrade 𝒜 0 from he0)
  refine gdimPoly_congr (GradedEquiv.ofPreserves (A := k) (idealRid k he) fun d x hx => ?_)
  refine balancedGrading_map_mem (fun d => idem ℳ (op e) d) ((idealRid k he).toLinearMap)
    (fun i j m a hm ha => ?_) hx
  change op (a : A) • m ∈ ℳ (i + j)
  exact op_smul_mem_of_mem 𝒜 ℳ hm ha

end Graded

section Induce

universe u

variable {k : Type*} [Field k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] (ℬ : ℤ → Submodule k B) [GradedAlgebra ℬ]
  {M : Type u} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul ℬ ℳ]
  [SetLike.GradedSMul (oppositeGrade 𝒜) ℳ] [Module.Finite k M] [Module.Finite k A]
  [Module.Finite k B]

/-- **`gdim HOM(B e', M ⊗_A A e) = gdim e' M e`** for idempotents `e`, `e'` of degree zero. -/
theorem projectiveHomPolynomial_induce_ofIdempotent {e : A} (he : IsIdempotentElem e)
    (he0 : e ∈ 𝒜 0) {e' : B} (he' : IsIdempotentElem e') (he0' : e' ∈ ℬ 0) :
    letI := idemDecomposition ℳ he0'
    projectiveHomPolynomial ℬ (GFin.induce 𝒜 ℬ ℳ (GProj.ofIdempotent e he he0).toGFin)
        (K0.of (GProj.ofIdempotent e' he' he0')) =
      gdimPoly (idem (idem ℳ e') (op e)) := by
  let := idemDecomposition ℳ he0'
  refine (projectiveHomPolynomial_ofIdempotent ℬ _ he' he0').trans ?_
  refine (gdimPoly_idem_balancedGrading 𝒜 ℳ (GProj.ofIdempotent e he he0).grading he'
    he0').trans ?_
  exact gdimPoly_balancedGrading_leftIdeal 𝒜 (idem ℳ e') he he0

end Induce

end Categorification.Graded
