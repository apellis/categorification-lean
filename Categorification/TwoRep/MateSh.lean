/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CisBubRight
import Categorification.TwoRep.LemAprime

/-!
# Mates of shifted 2-morphisms: preliminaries

For an adjunction `u ⊣ v` in a graded bicategory, the *mate* of a shifted endomorphism
`f : u ⟶ u⟨d⟩` is the shifted endomorphism of `v` obtained by "sliding `f` around the unit and
counit":

`v → v ≫ 𝟙 → v ≫ (u ≫ v) → (v ≫ u) ≫ v → (v ≫ u⟨d⟩) ≫ v → (v ≫ u)⟨d⟩ ≫ v → 𝟙⟨d⟩ ≫ v → v⟨d⟩`.

This is how dots and crossings on downward strands `F` are obtained from those on `E`
(Cautis–Lauda arXiv:1111.1431v3, §4 (cyclicity)). This file contains the unshifted adjunction
bijections and the shift-coherence mixins that the shifted mate calculus will need. No shifted
adjunction `u⟨d⟩ ⊣ v⟨-d⟩` is to be constructed.

## Main definitions and results

* `GradedBicategory.ShiftUnitor`: compatibility of the whiskering shift isomorphisms with the
  left and right unitors (sign-free);
* `GradedBicategory.ShiftAssocMid`: compatibility of the whiskering shift isomorphisms with the
  associator, mixed form (companion of `ShiftAssoc` in `LemAprime.lean` and `ShiftAssocRight` in
  `CisBubRight.lean`);
* `Θ₀ adj : (v ≫ u ⟶ y) → (v ⟶ y ≫ v)` ("close up with the unit") and
  `Ξ₀ adj : (v ⟶ y ≫ v) → (v ≫ u ⟶ y)` ("compose with the counit"), the ordinary (unshifted)
  adjunction bijections;
* `Ξ₀_Θ₀`, `Θ₀_Ξ₀`: they are mutually inverse (from the triangle identities);
* `Θ₀_comp`: naturality of `Θ₀` in `y`.

## Further shifted constructions

`GradedHomAdjunction.lean` now proves the shifted bijections `Θsh`, `Ξsh` and their inverse
identities for a given adjunction, using the actual finite-sum graded-Hom bicategory.
Its `shiftedEndEquiv` specializes them to
`ShiftedHom (v ≫ u) (𝟙 b) d ≃ ShiftedHom v v d`.

`ShiftedMates.lean` now constructs `εsh` and `mateSh`, identifies the latter with ordinary
conjugate mates in the graded-Hom bicategory, and proves `mateSh_comp`, `mateSh_mk₀_id`,
additivity, injectivity and scalar compatibility under explicit linearity hypotheses.
Still to formalize: compatibility with composite adjunctions
`mateSh_comp_shWhiskerLeft` (needs `ShiftAssoc`) and
`mateSh_comp_shWhiskerRight` (needs `ShiftAssocMid`).

## E-dots versus F-dots in CL's bottom half (motivation)

CL state the bottom half of §3 (Remark 3.11, `eq:main2`, and the lemmas "proved in the same
way") with the *E-dot*, i.e. the dot on the `E` strand of `E F 1_n` and `F E 1_n`. The literal
mirror of their proof of Lemma 3.6 (`LemXind.lean`) for `n ≤ 0` does not go through with E-dots:
the "no `E`-summand" step uses `Hom(E1_{n-2}, EFE1_{n-2}) = 0` in the relevant degree, but
`E F E 1_{n-2} = E (F E 1_{n-2}) ⊇ E 1_{n-2}⟨-n+2⟩` (from `eq:main2` at `n-2`), which is nonzero
for `n ≤ 1`. See `DotEntriesNeg.lean` for the precise statement. The mirror argument is expected
to prove the corresponding statement for the **F-dot**, the mate of the E-dot under
`E ⊣ F⟨n+1⟩`; E-dots and F-dots are related only through the cyclicity of §4. The mate calculus
above is the planned basis for that F-dot route.
-/
noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]

/-- **Compatibility of the whiskering shift isomorphisms with the unitors**:
`𝟙 ≫ g⟨n⟩ ≅ (𝟙 ≫ g)⟨n⟩ ≅ g⟨n⟩` is the left unitor of `g⟨n⟩`, and symmetrically on the right. -/
class GradedBicategory.ShiftUnitor (B : Type u) [Bicategory.{w, v} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] :
    Prop where
  leftUnitor_shift : ∀ {a b : B} (g : a ⟶ b) (n : ℤ),
    (whiskerLeftShiftIso (𝟙 a) g n).hom ≫ ((λ_ g).hom)⟦n⟧' = (λ_ (g⟦n⟧)).hom
  rightUnitor_shift : ∀ {a b : B} (f : a ⟶ b) (n : ℤ),
    (whiskerRightShiftIso f (𝟙 b) n).hom ≫ ((ρ_ f).hom)⟦n⟧' = (ρ_ (f⟦n⟧)).hom

/-- **Compatibility of the whiskering shift isomorphisms with the associator, mixed form**:
the two identifications `f ≫ g⟨n⟩ ≫ h ≅ (f ≫ g ≫ h)⟨n⟩` (shifting the right whiskering first, or
the left whiskering first) agree. Companion of `ShiftAssoc` (`LemAprime.lean`) and
`ShiftAssocRight` (`CisBubRight.lean`). -/
class GradedBicategory.ShiftAssocMid (B : Type u) [Bicategory.{w, v} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] :
    Prop where
  assoc_shift_mid : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (n : ℤ),
    (α_ f (g⟦n⟧) h).hom ≫ (f ◁ (whiskerRightShiftIso g h n).hom) ≫
        (whiskerLeftShiftIso f (g ≫ h) n).hom =
      ((whiskerLeftShiftIso f g n).hom ▷ h) ≫ (whiskerRightShiftIso (f ≫ g) h n).hom ≫
        ((α_ f g h).hom)⟦n⟧'

/-! ## The unshifted adjunction bijections -/

section Plain

omit [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]

variable {a b : B} {u : a ⟶ b} {v : b ⟶ a} (adj : u ⊣ v) {y : b ⟶ b}

/-- "Close up with the unit": `φ : v ≫ u ⟶ y` gives `v ⟶ y ≫ v`. -/
def Θ₀ (φ : v ≫ u ⟶ y) : v ⟶ y ≫ v :=
  (ρ_ v).inv ≫ (v ◁ adj.unit) ≫ (α_ v u v).inv ≫ (φ ▷ v)

/-- "Compose with the counit": `ψ : v ⟶ y ≫ v` gives `v ≫ u ⟶ y`. -/
def Ξ₀ (ψ : v ⟶ y ≫ v) : v ≫ u ⟶ y :=
  (ψ ▷ u) ≫ (α_ y v u).hom ≫ (y ◁ adj.counit) ≫ (ρ_ y).hom

theorem Ξ₀_Θ₀ (φ : v ≫ u ⟶ y) : Ξ₀ adj (Θ₀ adj φ) = φ := by
  dsimp only [Ξ₀, Θ₀]
  calc _ = 𝟙 _ ⊗≫ v ◁ adj.unit ▷ u ⊗≫ (φ ▷ (v ≫ u) ≫ y ◁ adj.counit) ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ v ◁ adj.unit ▷ u ⊗≫ ((v ≫ u) ◁ adj.counit ≫ φ ▷ 𝟙 b) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ v ◁ leftZigzag adj.unit adj.counit ⊗≫ φ ⊗≫ 𝟙 _ := by
        dsimp only [leftZigzag]; bicategory
    _ = φ := by
        rw [adj.left_triangle]; bicategory

theorem Θ₀_Ξ₀ (ψ : v ⟶ y ≫ v) : Θ₀ adj (Ξ₀ adj ψ) = ψ := by
  dsimp only [Ξ₀, Θ₀]
  calc _ = 𝟙 _ ⊗≫ (v ◁ adj.unit ≫ ψ ▷ (u ≫ v)) ⊗≫ y ◁ adj.counit ▷ v ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ (ψ ▷ 𝟙 a ≫ (y ≫ v) ◁ adj.unit) ⊗≫ y ◁ adj.counit ▷ v ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ ψ ⊗≫ y ◁ rightZigzag adj.unit adj.counit ⊗≫ 𝟙 _ := by
        dsimp only [rightZigzag]; bicategory
    _ = ψ := by
        rw [adj.right_triangle]; bicategory

theorem Θ₀_comp (φ : v ≫ u ⟶ y) {y' : b ⟶ b} (z : y ⟶ y') :
    Θ₀ adj (φ ≫ z) = Θ₀ adj φ ≫ (z ▷ v) := by
  simp only [Θ₀, comp_whiskerRight, Category.assoc]

end Plain

end Categorification.TwoRep
