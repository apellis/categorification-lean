/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# The zigzags of a bicategorical adjunction, with the coherence isomorphisms explicit

`leftZigzag_eq`, `rightZigzag_eq`: Mathlib's `leftZigzag η ε` and `rightZigzag η ε` (defined with
`⊗≫`) as plain composites with one associator.
-/

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

/-- The left zigzag with the coherence isomorphism made explicit. -/
theorem leftZigzag_eq {C : Type*} [Bicategory C] {a b : C}
    {f : a ⟶ b} {g : b ⟶ a} (unit : 𝟙 a ⟶ f ≫ g) (counit : g ≫ f ⟶ 𝟙 b) :
    leftZigzag unit counit = unit ▷ f ≫ (α_ f g f).hom ≫ f ◁ counit := by
  simp [bicategoricalComp]

/-- The right zigzag with the coherence isomorphism made explicit. -/
theorem rightZigzag_eq {C : Type*} [Bicategory C] {a b : C}
    {f : a ⟶ b} {g : b ⟶ a} (unit : 𝟙 a ⟶ f ≫ g) (counit : g ≫ f ⟶ 𝟙 b) :
    rightZigzag unit counit = g ◁ unit ≫ (α_ g f g).inv ≫ counit ▷ g := by
  simp [bicategoricalComp]

end Categorification.TwoRep
