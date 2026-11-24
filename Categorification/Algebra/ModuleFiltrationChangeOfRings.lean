/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ModuleFiltration
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Scalar restriction and relabelling for filtrations

Restriction of scalars preserves the exact sequences defining a filtration.
The layer labels can also be transported along a family of linear equivalences.
-/

namespace Categorification.ModuleFiltration.HasFiltration

open CategoryTheory
universe u v w w' u'

variable {A : Type u} [Ring A] {B : Type u'} [Ring B] {ι : Type w} {ι' : Type w'}
variable {L : ι → ModuleCat.{v} A}

/-- Restriction of scalars preserves the successive subquotients of a filtration. -/
theorem restrictScalars (f : B →+* A) {m : List ι} {Y : ModuleCat.{v} A}
    (h : HasFiltration L m Y) :
    HasFiltration (fun c => (ModuleCat.restrictScalars f).obj (L c)) m
      ((ModuleCat.restrictScalars f).obj Y) := by
  let F := ModuleCat.restrictScalars.{v} f
  induction h with
  | zero hY => exact .zero hY
  | cons q p m c hq hqp hp _ he ih =>
    refine .cons (F.map (ModuleCat.ofHom q)).hom (F.map (ModuleCat.ofHom p)).hom m c
      hq hqp hp ih ?_
    obtain ⟨e⟩ := he
    exact ⟨(F.mapIso e.toModuleIso).toLinearEquiv⟩

/-- Relabel a filtration by identifying every old layer with the corresponding new layer. -/
theorem mapLabels (f : ι → ι') (L' : ι' → ModuleCat.{v} A)
    (e : ∀ c, Nonempty (L c ≃ₗ[A] L' (f c))) {m : List ι} {Y : ModuleCat.{v} A}
    (h : HasFiltration L m Y) : HasFiltration L' (m.map f) Y := by
  induction h with
  | zero hY => exact .zero hY
  | cons p q m c hp hpq hq _ he ih =>
    refine .cons p q (m.map f) (f c) hp hpq hq ih ?_
    obtain ⟨d⟩ := he
    obtain ⟨e'⟩ := e c
    exact ⟨d.trans e'⟩

end Categorification.ModuleFiltration.HasFiltration
