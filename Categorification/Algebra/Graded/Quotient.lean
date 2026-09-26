/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Module

/-!
# Quotient gradings

If `M = ⨁_d ℳ d` is a graded module and `W ⊆ M` is a homogeneous subspace (closed under taking
homogeneous components), then `M / W` is graded by the images `(ℳ d).map W.mkQ`
(`Graded.quotGrading`, `Graded.isInternal_quotGrading`). This is used for the grading of the
coinvariant algebra `L_m = k[x_1, …, x_m] / (Sym⁺)` of Khovanov–Lauda I (arXiv:0803.4121v2,
§2.2).
-/

namespace Categorification.Graded

open DirectSum

variable {ι k M : Type*} [CommRing k] [AddCommGroup M] [Module k M]
  (ℳ : ι → Submodule k M) (W : Submodule k M)

/-- The grading of `M / W` by the images of the `ℳ d`. -/
def quotGrading : ι → Submodule k (M ⧸ W) := fun d => (ℳ d).map W.mkQ

theorem mem_quotGrading {d : ι} {x : M ⧸ W} :
    x ∈ quotGrading ℳ W d ↔ ∃ y ∈ ℳ d, W.mkQ y = x := Submodule.mem_map

theorem mk_mem_quotGrading {d : ι} {y : M} (hy : y ∈ ℳ d) :
    (Submodule.Quotient.mk y : M ⧸ W) ∈ quotGrading ℳ W d :=
  ⟨y, hy, rfl⟩

variable [DecidableEq ι] [Decomposition ℳ]

/-- An element of `⨆_{j ≠ d} ℳ j` has zero component in degree `d`. -/
theorem decompose_eq_zero_of_mem_iSup_ne {d : ι} {z : M} (hz : z ∈ ⨆ (j) (_ : j ≠ d), ℳ j) :
    (decompose ℳ z d : M) = 0 := by
  rw [iSup_subtype'] at hz
  refine Submodule.iSup_induction _ (motive := fun z => (decompose ℳ z d : M) = 0) hz ?_ ?_ ?_
  · intro j z hz
    exact decompose_of_mem_ne ℳ hz j.2
  · simp
  · intro x y hx hy
    rw [decompose_add, add_apply, Submodule.coe_add, hx, hy, add_zero]

/-- **The quotient of a graded module by a homogeneous subspace is graded.** -/
theorem isInternal_quotGrading (hW : ∀ d, ∀ x ∈ W, (decompose ℳ x d : M) ∈ W) :
    IsInternal (quotGrading ℳ W) := by
  have hint := Decomposition.isInternal ℳ
  refine isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_def]
    intro d
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := hx
    have hx'' : W.mkQ y ∈ (⨆ (j) (_ : j ≠ d), ℳ j).map W.mkQ := by
      rw [Submodule.map_iSup]
      simpa only [Submodule.map_iSup] using hx'
    obtain ⟨z, hz, hzy⟩ := hx''
    have hyz : y - z ∈ W := by
      rw [← Submodule.Quotient.eq]
      exact hzy.symm
    have := hW d _ hyz
    rw [decompose_sub, sub_apply, Submodule.coe_sub, decompose_of_mem_same ℳ hy,
      decompose_eq_zero_of_mem_iSup_ne ℳ hz, sub_zero] at this
    exact (Submodule.Quotient.mk_eq_zero W).2 this
  · show ⨆ d, (ℳ d).map W.mkQ = ⊤
    rw [← Submodule.map_iSup, hint.submodule_iSup_eq_top, Submodule.map_top,
      Submodule.range_mkQ]

/-- The graded structure of `M / W` for a homogeneous `W`. -/
noncomputable def quotDecomposition (hW : ∀ d, ∀ x ∈ W, (decompose ℳ x d : M) ∈ W) :
    Decomposition (quotGrading ℳ W) :=
  (isInternal_quotGrading ℳ W hW).chooseDecomposition

end Categorification.Graded
