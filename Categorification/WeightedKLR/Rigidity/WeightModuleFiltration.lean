/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.WeightModuleExactTriangle
import DG.Category.Abelian
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Finite filtrations of dg weight modules

Localization sends a finite filtration by short exact sequences to iterated
extensions of its localized layers.
This is used in the standard-filtration reduction in Webster, arXiv:1309.3796v2, Lemma 6.11.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits DG

universe u v w z

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  {ι : Type*}

/-- A finite filtration with successive quotients isomorphic to the specified layers,
listed from the bottom of the filtration to the top. -/
inductive WeightModuleFiltration (L : ι → CatModule.{w} C) :
    List ι → CatModule.{w} C → Prop
  | nil {M} : IsZero M → WeightModuleFiltration L [] M
  | append {layers} (i : ι) (S : ShortComplex (CatModule.{w} C)) (hS : S.ShortExact) :
      WeightModuleFiltration L layers S.X₁ → Nonempty (S.X₃ ≅ L i) →
      WeightModuleFiltration L (layers ++ [i]) S.X₂

namespace WeightModuleFiltration

variable [CatModule.HasDerivedCategory.{z,w} C]

local notation "Q" => CatModule.DerivedCategory.Q (C := C)

/-- The localization of a filtered object belongs to the iterated extension of any
isomorphism-closed property containing zero objects and all the localized layers. -/
theorem extensionProductIter {L : ι → CatModule.{w} C} {layers : List ι} {M : CatModule.{w} C}
    (h : WeightModuleFiltration L layers M)
    (P : ObjectProperty (CatModule.DerivedCategory.{z,w} C)) [P.IsClosedUnderIsomorphisms]
    (hzero : ∀ X, IsZero X → P X) (hL : ∀ i ∈ layers, P ((Q).obj (L i))) :
    P.extensionProductIter layers.length ((Q).obj M) := by
  induction h with
  | nil hM =>
    exact hzero _ ((Q).map_isZero hM)
  | @append layers i S hS _ hl ih =>
    obtain ⟨e⟩ := hl
    have hpt := (CatModule.shortExact_iff S).mp hS
    obtain ⟨δ, hδ⟩ := Stendhal.FundamentalCorner.exists_distinguished_weightTriangle_of_exact
      S.f S.g S.zero (fun X => (hpt X).1) (fun X => (hpt X).2.1) (fun X => (hpt X).2.2)
    rw [List.length_append, List.length_singleton, ObjectProperty.extensionProductIter_succ']
    exact ⟨_, _, (Q).map S.f, (Q).map S.g, δ, hδ,
      ih (fun j hj => hL j (List.mem_append_left _ hj)),
      P.prop_of_iso ((Q).mapIso e).symm (hL i (by simp))⟩

end WeightModuleFiltration

end Categorification
