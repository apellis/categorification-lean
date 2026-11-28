/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapGradedHead
import Categorification.Algebra.Graded.G0
import Categorification.Algebra.Graded.RightTwist

/-!
# The head of a projective modulo a trace as a finite-dimensional graded module

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Lemma 7.3. Webster's `L_λ` is the quotient `e A ⧸ trace` of the right projective `e A` of an
idempotent `e` of degree `0` by the images of the cut projectives `c_j A`
(`Stendhal.coevaluationHead`). With the grading `headGrade` of `CupCapGradedHead`, this file
bundles it as an object of `GFin` over the opposite grading (finite-dimensional graded right
`A`-modules), the input of the class functional `classFunctional`:

* `headGradeSubmodule`: the degree components as `k`-subspaces.
* `headGFin`: the bundled finite-dimensional graded right module, for `A` finite over `k`.
* `cut_smul_head_eq_zero`: the cut idempotents kill the head: `v c_j = 0`.
-/

noncomputable section

namespace Categorification.Stendhal

open DirectSum MulOpposite Categorification.Graded

section HeadModule

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜] {e : A} (he0 : e ∈ 𝒜 0) {J : Type u} (cut : J → A)
  (hcut : ∀ j, cut j ∈ 𝒜 0)

set_option hygiene false in
local notation "𝐇" => rIdeal e ⧸ coevaluationTrace (e := e) cut

/-- The degree components of the head `e A ⧸ trace` as `k`-subspaces (`headGrade`). -/
def headGradeSubmodule (q : ℤ) : Submodule k (𝐇) where
  __ := headGrade 𝒜 he0 cut hcut q
  smul_mem' c v hv := by
    have h := op_smul_mem_headGrade 𝒜 he0 cut hcut (SetLike.algebraMap_mem_graded 𝒜 c) hv
    rw [add_zero] at h
    have hc : c • v = op (algebraMap k A c) • v := by
      rw [← algebraMap_smul (A := Aᵐᵒᵖ) c v]
      rfl
    rw [hc]
    exact h

theorem isInternal_headGradeSubmodule : IsInternal (headGradeSubmodule 𝒜 he0 cut hcut) :=
  isInternal_headGrade 𝒜 he0 cut hcut

noncomputable instance headGradeSubmoduleDecomposition :
    Decomposition (headGradeSubmodule 𝒜 he0 cut hcut) :=
  (isInternal_headGradeSubmodule 𝒜 he0 cut hcut).chooseDecomposition _

instance headGradeSubmodule_gradedSMul :
    SetLike.GradedSMul (oppositeGrade 𝒜) (headGradeSubmodule 𝒜 he0 cut hcut) where
  smul_mem {r p a v} ha hv := by
    have h := op_smul_mem_headGrade 𝒜 he0 cut hcut (a := a.unop) ha hv
    rw [op_unop, add_comm] at h
    exact h

omit [GradedAlgebra 𝒜] in
variable {cut} in
/-- The surjection `A → e A ⧸ trace`, `a ↦ [e a]`, as a `k`-linear map. -/
def headQuotientMap (he : IsIdempotentElem e) : A →ₗ[k] (𝐇) where
  toFun a := Submodule.Quotient.mk ⟨e * a, by
    change e * (e * a) = e * a
    rw [← mul_assoc, he.eq]⟩
  map_add' a b := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    exact Subtype.ext (mul_add e a b)
  map_smul' c a := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (mul_smul_comm c e a)

omit [GradedAlgebra 𝒜] in
theorem headQuotientMap_surjective (he : IsIdempotentElem e) :
    Function.Surjective (headQuotientMap (k := k) (cut := cut) he) := by
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    refine ⟨x.val, ?_⟩
    change Submodule.Quotient.mk _ = _
    congr 1
    exact Subtype.ext x.2

omit [GradedAlgebra 𝒜] in
theorem finite_head (he : IsIdempotentElem e) [Module.Finite k A] : Module.Finite k (𝐇) :=
  Module.Finite.of_surjective _ (headQuotientMap_surjective (k := k) cut he)

/-- **The head `e A ⧸ trace` as a finite-dimensional graded right module** (Webster's `L_λ`
of Lemma 7.3, with the grading `headGrade`). -/
def headGFin (he : IsIdempotentElem e) [Module.Finite k A] : GFin (oppositeGrade 𝒜) :=
  { toGMod := GMod.of (𝐇) (headGradeSubmodule 𝒜 he0 cut hcut)
    finiteDimensional := finite_head (k := k) cut he }

/-- **The cut idempotents kill the head**: `v c_j = 0` in `e A ⧸ trace`. -/
theorem cut_smul_head_eq_zero (hc : ∀ j, IsIdempotentElem (cut j)) (j : J) (v : 𝐇) :
    op (cut j) • v = 0 := by
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine Submodule.subset_span ⟨j, ?_⟩
    change x.val * cut j * cut j = x.val * cut j
    rw [mul_assoc, (hc j).eq]

end HeadModule

end Categorification.Stendhal
