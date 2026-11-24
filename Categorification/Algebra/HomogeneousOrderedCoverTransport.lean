/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.OrderedProjectiveResolution
import Categorification.Algebra.DiagramBigrading

/-!
# Transport of homogeneous ordered covers

A homogeneous ring equivalence identifies the internal grading on a standard after
restriction of scalars and preserves homogeneity of its ordered-cover quotient.
-/

noncomputable section

namespace Categorification.ModuleFiltration

open CategoryTheory DG
open scoped DG.DegreeZero

universe u w

variable {A B : Type u} [Ring A] [Ring B] [InternalGrading A] [InternalGrading B]
  {Label : Type w} {S : Label → ModuleCat.{u} A}
  {e : Label → A} {above : Label → Label → Prop}
  (data : OrderedStandardCovers S e above) (σ : A ≃+* B)

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- An additive bijection that preserves each component of an internal
grading also reflects each component. -/
theorem addEquiv_mem_grade_iff
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (G : ℤ → AddSubgroup M) (H : ℤ → AddSubgroup N)
    [DirectSum.Decomposition G] [DirectSum.Decomposition H]
    (f : M ≃+ N) (hf : ∀ j {x : M}, x ∈ G j → f x ∈ H j)
    (j : ℤ) (x : M) : f x ∈ H j ↔ x ∈ G j := by
  refine ⟨?_, hf j⟩
  intro hx
  let _ : DGAddCommGroup M := {
    grading := G
    d := 0
    d_mem' := fun _ => zero_mem _
    d_d' := fun _ => rfl }
  let _ : DGAddCommGroup N := {
    grading := H
    d := 0
    d_mem' := fun _ => zero_mem _
    d_d' := fun _ => rfl }
  have hmap : ((DirectSum.decompose H (f x) j).val : N) =
      f (DirectSum.decompose G x j).val :=
    coe_decompose_map_of_map_mem f.toAddMonoidHom (fun h => hf _ h) x j
  rw [DirectSum.decompose_of_mem_same _ hx] at hmap
  rw [f.injective hmap]
  exact (DirectSum.decompose G x j).property

/-- Homogeneity of a ring equivalence implies homogeneity of its inverse. -/
theorem ringEquiv_symm_mem_weight
    (hσ : ∀ j {a : A}, a ∈ wgrading j → σ a ∈ wgrading j)
    {j : ℤ} {b : B} (hb : b ∈ wgrading j) : σ.symm b ∈ wgrading j := by
  apply (addEquiv_mem_grade_iff (wgrading (M := A)) (wgrading (M := B))
    σ.toAddEquiv hσ j (σ.symm b)).mp
  change σ (σ.symm b) ∈ wgrading j
  simpa only [RingEquiv.apply_symm_apply] using hb

/-- The restricted standard inherits its homogeneous additive subgroups from
the original standard. -/
abbrev transportedStandardGrading (c : Label) (G : ℤ → AddSubgroup (S c)) :
    ℤ → AddSubgroup ((ModuleCat.restrictScalars σ.symm.toRingHom).obj (S c)) :=
  G

/-- Restricting scalars along a homogeneous equivalence preserves the
homogeneity of the scalar action. -/
theorem transportedStandardGrading_smul (c : Label) (G : ℤ → AddSubgroup (S c))
    (hσ : ∀ {j : ℤ} {b : B}, b ∈ wgrading j → σ.symm b ∈ wgrading j)
    (hG : ∀ {i j : ℤ} {a : A} {x : S c}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
    {i j : ℤ} {b : B} {x : (ModuleCat.restrictScalars σ.symm.toRingHom).obj (S c)}
    (hb : b ∈ wgrading i) (hx : x ∈ transportedStandardGrading σ c G j) :
    b • x ∈ transportedStandardGrading σ c G (i+j) :=
  hG (hσ hb) hx

/-- Transporting an ordered cover along a homogeneous ring equivalence
preserves the weight of its augmentation map. -/
theorem OrderedStandardCovers.transport_quotient_mem_weight (c : Label)
    (G : ℤ → AddSubgroup (S c))
    (hσ : ∀ {j : ℤ} {b : B}, b ∈ wgrading j → σ.symm b ∈ wgrading j)
    (hG : ∀ {j : ℤ} {x : lIdeal (e c)}, x.val ∈ wgrading j → data.quotient c x ∈ G j)
    {j : ℤ} {x : lIdeal (σ (e c))} (hx : x.val ∈ wgrading j) :
    (data.transport σ).quotient c x ∈ transportedStandardGrading σ c G j := by
  let y : lIdeal (e c) := ⟨σ.symm x.val, by
    change σ.symm x.val * e c = σ.symm x.val
    have h := congrArg σ.symm x.property
    simpa only [map_mul, RingEquiv.symm_apply_apply] using h⟩
  change data.quotient c y ∈ G j
  exact hG (hσ hx)

end Categorification.ModuleFiltration
