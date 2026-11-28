/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapGrading
import Categorification.WeightedKLR.Rigidity.CoevaluationTrace

/-!
# The grading of the head of a projective modulo a trace

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Lemma 7.3, and §7.3, Definition 7.15: Webster's coefficient module `L_μ` is the quotient of the
projective `e T` (for the wrap idempotent `e`) by the images of the cut projectives `c_j T`
(`Stendhal.coevaluationHead`, `Stendhal.coevaluationTrace`). Webster's modules are graded; we
make the grading of this quotient explicit.

For a graded algebra `A`, an idempotent `e` of degree zero and idempotents `c_j` of degree zero,
the right ideal `e A` is graded by the components of its elements, the trace of the `c_j` is a
graded submodule, and the quotient `e A ⧸ trace` is a graded right `A`-module
(`isInternal_headGrade`, `op_smul_mem_headGrade`). This is the grading of `L_μ`; with it `L_μ`
satisfies the hypothesis `CupCap.IsGradedCoeff` of the grading of the cap bimodule.

## Main definitions

* `rIdealProj`, `headProj`: the degree projections of `e A` and of `e A ⧸ trace`.
* `headGrade`: the grading of `e A ⧸ trace`.

## Main results

* `rIdealProj_mem_coevaluationTrace`: the trace is a graded submodule.
* `isInternal_headGrade`, `op_smul_mem_headGrade`.
-/

noncomputable section

namespace Categorification.Stendhal

open DirectSum MulOpposite

section GradedHead

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜] {e : A} (he0 : e ∈ 𝒜 0) {J : Type*} (cut : J → A)
  (hcut : ∀ j, cut j ∈ 𝒜 0)

/-- The degree `q` component of an element of the right ideal `e A`, for `e` of degree zero. -/
def rIdealProj (q : ℤ) : rIdeal e →+ rIdeal e where
  toFun x := ⟨decompose 𝒜 (x : A) q, by
    rw [mem_rIdeal, ← coe_decompose_mul_of_left_mem_zero 𝒜 he0, x.2]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem coe_rIdealProj (q : ℤ) (x : rIdeal e) :
    (rIdealProj 𝒜 he0 q x : A) = decompose 𝒜 (x : A) q := rfl

theorem rIdealProj_smul (q : ℤ) {r : ℤ} {a : A} (ha : a ∈ 𝒜 r) (x : rIdeal e) :
    rIdealProj 𝒜 he0 q (op a • x) = op a • rIdealProj 𝒜 he0 (q - r) x := by
  apply Subtype.ext
  have h := coe_decompose_mul_add_of_right_mem 𝒜 (a := (x : A)) (i := q - r) ha
  rw [sub_add_cancel] at h
  exact h

theorem rIdealProj_rIdealProj (q q' : ℤ) (x : rIdeal e) :
    rIdealProj 𝒜 he0 q (rIdealProj 𝒜 he0 q' x) =
      if q = q' then rIdealProj 𝒜 he0 q' x else 0 := by
  by_cases h : q = q'
  · subst h
    rw [ite_eq_left rfl]
    exact Subtype.ext (decompose_of_mem_same 𝒜 (SetLike.coe_mem (decompose 𝒜 (x : A) q)))
  · rw [ite_eq_right h]
    exact Subtype.ext
      (decompose_of_mem_ne 𝒜 (SetLike.coe_mem (decompose 𝒜 (x : A) q')) (Ne.symm h))

include hcut in
/-- **The trace of degree-zero idempotents is a graded submodule.** -/
theorem rIdealProj_mem_coevaluationTrace {x : rIdeal e} (hx : x ∈ coevaluationTrace cut)
    (q : ℤ) : rIdealProj 𝒜 he0 q x ∈ coevaluationTrace cut := by
  induction hx using Submodule.span_induction generalizing q with
  | mem x hx =>
    obtain ⟨j, hj⟩ := hx
    refine Submodule.subset_span ⟨j, ?_⟩
    rw [coe_rIdealProj, ← coe_decompose_mul_of_right_mem_zero 𝒜 (hcut j), hj]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem (hx q) (hy q)
  | smul c x _ hx =>
    induction c using MulOpposite.rec' with
    | h a =>
    induction a using Decomposition.inductionOn 𝒜 with
    | zero => rw [op_zero, zero_smul, map_zero]; exact zero_mem _
    | @homogeneous r a =>
      rw [rIdealProj_smul 𝒜 he0 q a.2]
      exact Submodule.smul_mem _ _ (hx _)
    | add a b ha hb => rw [op_add, add_smul, map_add]; exact add_mem ha hb

theorem mem_iSup_rIdealProj_range (x : rIdeal e) :
    x ∈ ⨆ q, (rIdealProj 𝒜 he0 q).range := by
  classical
  have hx : x = ∑ q ∈ (decompose 𝒜 (x : A)).support, rIdealProj 𝒜 he0 q x := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact (sum_support_decompose 𝒜 (x : A)).symm
  rw [hx]
  exact sum_mem fun q _ => AddSubgroup.mem_iSup_of_mem q ⟨x, rfl⟩

set_option hygiene false in
local notation "𝐇" => rIdeal e ⧸ coevaluationTrace (e := e) cut

/-- The degree `q` projection of the quotient `e A ⧸ trace`. -/
def headProj (q : ℤ) : (𝐇) →+ (𝐇) :=
  QuotientAddGroup.lift (coevaluationTrace (e := e) cut).toAddSubgroup
    ((coevaluationTrace (e := e) cut).mkQ.toAddMonoidHom.comp (rIdealProj 𝒜 he0 q))
    fun _ hz => (Submodule.Quotient.mk_eq_zero _).2
      (rIdealProj_mem_coevaluationTrace 𝒜 he0 cut hcut hz q)

theorem headProj_mk (q : ℤ) (x : rIdeal e) :
    headProj 𝒜 he0 cut hcut q (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (rIdealProj 𝒜 he0 q x) := rfl

theorem headProj_headProj (q q' : ℤ) (v : 𝐇) :
    headProj 𝒜 he0 cut hcut q (headProj 𝒜 he0 cut hcut q' v) =
      if q = q' then headProj 𝒜 he0 cut hcut q' v else 0 := by
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    rw [headProj_mk, headProj_mk, rIdealProj_rIdealProj]
    split_ifs
    · rfl
    · exact Submodule.Quotient.mk_zero _

theorem headProj_smul (q : ℤ) {r : ℤ} {a : A} (ha : a ∈ 𝒜 r) (v : 𝐇) :
    headProj 𝒜 he0 cut hcut q (op a • v) = op a • headProj 𝒜 he0 cut hcut (q - r) v := by
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, headProj_mk, headProj_mk, rIdealProj_smul 𝒜 he0 q ha,
      Submodule.Quotient.mk_smul]

theorem mem_iSup_headProj_range (v : 𝐇) : v ∈ ⨆ q, (headProj 𝒜 he0 cut hcut q).range := by
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    have h := AddSubgroup.map_le_iff_le_comap.2 (iSup_le fun q => ?_ :
      (⨆ q, (rIdealProj 𝒜 he0 q).range) ≤ (⨆ q, (headProj 𝒜 he0 cut hcut q).range).comap
        (coevaluationTrace (e := e) cut).mkQ.toAddMonoidHom)
    · exact h ⟨x, mem_iSup_rIdealProj_range 𝒜 he0 x, rfl⟩
    · rintro _ ⟨y, rfl⟩
      exact AddSubgroup.mem_iSup_of_mem q ⟨Submodule.Quotient.mk y, rfl⟩

/-- **The grading of the head** `e A ⧸ trace`: the classes of the homogeneous elements of
`e A`. -/
def headGrade (q : ℤ) : AddSubgroup (𝐇) := (headProj 𝒜 he0 cut hcut q).range

theorem isInternal_headGrade : IsInternal (headGrade 𝒜 he0 cut hcut) :=
  CupCap.isInternal_range_of_projections _ (headProj_headProj 𝒜 he0 cut hcut)
    (mem_iSup_headProj_range 𝒜 he0 cut hcut)

noncomputable instance headDecomposition : Decomposition (headGrade 𝒜 he0 cut hcut) :=
  (isInternal_headGrade 𝒜 he0 cut hcut).chooseDecomposition _

theorem mem_headGrade_iff {q : ℤ} {v : 𝐇} :
    v ∈ headGrade 𝒜 he0 cut hcut q ↔ headProj 𝒜 he0 cut hcut q v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [headProj_headProj, ite_eq_left rfl]
  · exact fun h => ⟨v, h⟩

theorem mk_mem_headGrade {q : ℤ} {x : rIdeal e} (hx : (x : A) ∈ 𝒜 q) :
    (Submodule.Quotient.mk x : 𝐇) ∈ headGrade 𝒜 he0 cut hcut q := by
  rw [mem_headGrade_iff, headProj_mk]
  exact congrArg _ (Subtype.ext (decompose_of_mem_same _ hx))

/-- **The head is a graded right module.** -/
theorem op_smul_mem_headGrade {p r : ℤ} {a : A} (ha : a ∈ 𝒜 r) {v : 𝐇}
    (hv : v ∈ headGrade 𝒜 he0 cut hcut p) : op a • v ∈ headGrade 𝒜 he0 cut hcut (p + r) := by
  rw [mem_headGrade_iff] at hv ⊢
  rw [headProj_smul 𝒜 he0 cut hcut _ ha, add_sub_cancel_right, hv]

end GradedHead

end Categorification.Stendhal
