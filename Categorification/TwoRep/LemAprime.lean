/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.LemXind

/-!
# CL Lemma 3.8: the two cup-and-crossing maps `E 1_m → E E F 1_m ⟨-m-1⟩` are nonzero

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Lemma 3.8 (`lem:A'`): for `m ≥ n` the two maps
`E 1_m → E E F 1_m ⟨-m-1⟩` — the cup on the left of the strand followed by the up-down crossing
(the inclusion `F E 1_m ⊆ E F 1_m`), and the cup on the right of the strand followed by the
crossing of the two upward strands — are nonzero multiples of the unique such map (Corollary 3.3).

Indexing: `1_m` at the object `r + 1`, `E 1_m = E (r + 1)`, `E E F 1_m = F r ≫ (E r ≫ E (r + 1))`
(`FW r`), `e : EFDecomp r` (cup at the weight `m`: `ι e 0`), `e₂ : EFDecomp (r + 1)` (cup at the
weight `m + 2`: `ι e₂ 0`); the crossing of the two upward strands is `cross r` on `E r ≫ E (r + 1)`.

* `lemAprimeLeft e e₂ = ιa e e₂ 0 : E 1_m 1_{m+2}⟨m+1⟩ → E E F 1_m` (cup on the left, then the
  inclusion `F E 1_m ⊆ E F 1_m` whiskered by `E 1_m`); it is a split monomorphism
  (`ιa_comp_πa`), hence nonzero (`lemAprimeLeft_ne_zero`): "the composition of two inclusions".
* `lemAprimeRight e = ιb e 0 ≫ (F r ◁ cross r) : 1_m⟨m-1⟩ E 1_m → E E F 1_m ⟨-2⟩` (cup on the
  right, then the crossing); `lemAprimeRight_ne_zero`: CL's proof — add a dot on the strand `E 1_m`
  above the crossing and slide it down with the nilHecke relation `τ x_R = x_L τ - r`; the term
  `x_L τ` is the dot on `E 1_m` *below* the cup followed by (the shift of) the original map, and the
  other term is `r` times the cup on the right of the strand, a split monomorphism. Moving the
  dot below the cup uses the shifted interchange law (`ShiftInterchange`) and the compatibility
  of the whiskering shift isomorphisms with the associator, the further mixin
  `GradedBicategory.ShiftAssoc` introduced here (sign-free, as for `ShiftInterchange`).

Corollary 3.3 (`cor2`) says the space `Hom(E 1_m, E E F 1_m ⟨-m-1⟩)` is one-dimensional, so the
two maps are nonzero multiples of any generator; this file only proves the nonvanishing.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]

/-- **Compatibility of the whiskering shift isomorphisms with the associator**: the two
identifications `(f ≫ g) ≫ h⟨n⟩ ≅ (f ≫ (g ≫ h))⟨n⟩` (through `f ≫ (g ≫ h⟨n⟩)` or through
`((f ≫ g) ≫ h)⟨n⟩`) agree. Like `ShiftInterchange`, this holds in any graded 2-category in which the
shift is a degree shift. -/
class GradedBicategory.ShiftAssoc (B : Type u) [Bicategory.{w, v} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] :
    Prop where
  assoc_shift : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (n : ℤ),
    (α_ f g (h⟦n⟧)).hom ≫ (f ◁ (whiskerLeftShiftIso g h n).hom) ≫
        (whiskerLeftShiftIso f (g ≫ h) n).hom =
      (whiskerLeftShiftIso (f ≫ g) h n).hom ≫ ((α_ f g h).hom)⟦n⟧'

/-- Naturality of `f ≫ g⟨n⟩ ≅ (f ≫ g)⟨n⟩` in `g` (no coherence needed). -/
theorem whiskerLeftShiftIso_natural_right {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (θ : g ⟶ g')
    (n : ℤ) : (whiskerLeftShiftIso f g n).inv ≫ (f ◁ θ⟦n⟧') =
      (f ◁ θ)⟦n⟧' ≫ (whiskerLeftShiftIso f g' n).inv := by
  have := ((precomp c f).commShiftIso n).hom.naturality θ
  simp only [Functor.comp_map] at this
  change (f ◁ θ⟦n⟧') ≫ (whiskerLeftShiftIso f g' n).hom =
    (whiskerLeftShiftIso f g n).hom ≫ (f ◁ θ)⟦n⟧' at this
  rw [Iso.inv_comp_eq, ← Category.assoc, ← this, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem whiskerLeft_sub' {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η θ : g ⟶ h) :
    f ◁ (η - θ) = f ◁ η - f ◁ θ :=
  (precomp c f).map_sub

namespace StrongSl2

variable {k : Type*} [Field k] [∀ a b : B, Linear k (a ⟶ b)] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  {S : StrongSl2 k B} {r : ℤ} (e : S.EFDecomp r) (e₂ : S.EFDecomp (r + 1))

omit [GradedBicategory.IsLinear B k] in
theorem ιFE_comp_πFE : ιFE e ≫ πFE e = 𝟙 _ := by simp [ιFE, πFE]

omit [GradedBicategory.IsLinear B k] in
/-- `ιa` is a split monomorphism. -/
theorem ιa_comp_πa {j : ℕ} (hj : j < (S.wt (r + 1 + 1)).toNat) :
    ιa e e₂ j ≫ πa e e₂ j = 𝟙 _ := by
  simp only [ιa, πa, Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
    ιFE_comp_πFE, Bicategory.id_whiskerRight, Category.id_comp, Iso.inv_hom_id_assoc,
    ← Bicategory.whiskerLeft_comp, ι_π_self e₂ hj, Bicategory.whiskerLeft_id]

omit [GradedBicategory.IsLinear B k] in
/-- `ιb` is a split monomorphism. -/
theorem ιb_comp_πb {j : ℕ} (hj : j < (S.wt (r + 1)).toNat) : ιb e j ≫ πb e j = 𝟙 _ := by
  simp only [ιb, πb, Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight, ι_π_self e hj,
    Bicategory.id_whiskerRight]

/-- **The left map of CL Lemma 3.8**: the cup `1_{m+2}⟨m+1⟩ → E F 1_{m+2}` on the left of the
strand `E 1_m`, followed by the inclusion `F E 1_m ⊆ E F 1_m` whiskered by `E 1_m`:
`E 1_m 1_{m+2}⟨m+1⟩ → E E F 1_m`. -/
abbrev lemAprimeLeft : S.Asum r 0 ⟶ S.FW r := ιa e e₂ 0

/-- **The right map of CL Lemma 3.8**: the cup `1_m⟨m-1⟩ → E F 1_m` on the right of the strand
`E 1_m`, followed by the crossing of the two upward strands: `1_m⟨m-1⟩ E 1_m → E E F 1_m ⟨-2⟩`. -/
def lemAprimeRight : S.Bsum r 0 ⟶ S.F r ≫ (S.E r ≫ S.E (r + 1))⟦(-2 : ℤ)⟧ :=
  ιb e 0 ≫ (S.F r ◁ (S.cross r : S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦(-2 : ℤ)⟧))

omit [GradedBicategory.IsLinear B k] in
/-- **CL Lemma 3.8, left map**: it is nonzero ("the composition of two inclusions"), as soon as
`E 1_m ≠ 0` and `m + 2 > 0`. -/
theorem lemAprimeLeft_ne_zero (hm : 0 < (S.wt (r + 1 + 1)).toNat) (hE : ¬ IsZero (S.E (r + 1))) :
    lemAprimeLeft e e₂ ≠ 0 := by
  intro h0
  have hid : (𝟙 (S.Asum r 0) : _ ⟶ _) = 0 := by
    rw [← ιa_comp_πa e e₂ hm, lemAprimeLeft] at *
    rw [h0, zero_comp]
  have hz : IsZero (S.Asum r 0) := (IsZero.iff_id_eq_zero _).2 hid
  exact hE (((shiftFunctor _ (-(1 * ((((S.wt (r + 1 + 1)).toNat : ℕ) : ℤ) - 1 -
    2 * ((0 : ℕ) : ℤ))))).map_isZero (hz.of_iso (S.AsumIso r 0).symm)).of_iso
    ((shiftFunctorCompIsoId _ _ _ (by ring)).app _).symm)

section Right

variable [GradedBicategory.ShiftInterchange B] [GradedBicategory.ShiftAssoc B]

omit [GradedBicategory.IsLinear B k] in
/-- The dotted cup on the right, followed by the crossing and the dot slid down, is a shift of the
original map: `(cup ▷ E⟨2⟩) ≫ (F ◁ (E ≫ E⟨2⟩ ≅ (E E)⟨2⟩)) ≫ (F ◁ τ⟨2⟩)` is
`(1_m⟨m-1⟩ ≫ E⟨2⟩ ≅ (1_m⟨m-1⟩ E)⟨2⟩) ≫ ((cup ▷ E) ≫ (F ◁ τ))⟨2⟩` up to the shift isomorphism. -/
theorem ιb₂_comp_shift {X : S.obj r ⟶ S.obj (r + 1 + 1)} (τ : S.E r ≫ S.E (r + 1) ⟶ X) :
    ιb₂ e 0 ≫ (S.F r ◁ (whiskerLeftShiftIso (S.E r) (S.E (r + 1)) 2).hom) ≫
        (S.F r ◁ τ⟦(2 : ℤ)⟧') =
      (whiskerLeftShiftIso (S.oneShift r 0) (S.E (r + 1)) 2).hom ≫
        (ιb e 0 ≫ (S.F r ◁ τ))⟦(2 : ℤ)⟧' ≫ (whiskerLeftShiftIso (S.F r) X 2).inv := by
  have hN := GradedBicategory.ShiftInterchange.whiskerLeftShiftIso_natural (ι e 0) (S.E (r + 1)) 2
  have hA := GradedBicategory.ShiftAssoc.assoc_shift (S.F r) (S.E r) (S.E (r + 1)) 2
  have hnat := whiskerLeftShiftIso_natural_right (S.F r) τ 2
  simp only [ιb₂, ιb, Functor.map_comp, Category.assoc]
  rw [← hnat]
  conv_lhs => rw [← Iso.hom_inv_id_assoc (whiskerLeftShiftIso (S.F r) (S.E r ≫ S.E (r + 1)) 2)
    (S.F r ◁ τ⟦(2 : ℤ)⟧')]
  rw [reassoc_of% hA, ← reassoc_of% hN]

/-- **CL Lemma 3.8, right map**: the cup on the right of the strand followed by the crossing is
nonzero, as soon as `E 1_m ≠ 0` and `m > 0`. -/
theorem lemAprimeRight_ne_zero (hm : 0 < (S.wt (r + 1)).toNat) (hE : ¬ IsZero (S.E (r + 1))) :
    lemAprimeRight e ≠ 0 := by
  intro hR
  set N := S.nh r with hN
  -- the nilHecke relation `τ x_R = x_L τ - r` as an identity of plain 2-morphisms
  obtain ⟨Z, hZ⟩ : ∃ Z : (S.E r ≫ S.E (r + 1))⟦(0 : ℤ)⟧ ⟶ S.E r ≫ S.E (r + 1),
      Z = (shiftFunctorZero _ ℤ).hom.app (S.E r ≫ S.E (r + 1)) := ⟨_, rfl⟩
  have hrel : (S.cross r : S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦(-2 : ℤ)⟧) ≫
      ((N.xR : S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦(2 : ℤ)⟧)⟦(-2 : ℤ)⟧' ≫
        (shiftFunctorAdd' _ (2 : ℤ) (-2) 0 (by norm_num)).inv.app _ ≫ Z) =
      ((S.E r ◁ (S.dot (r + 1) : S.E (r + 1) ⟶ (S.E (r + 1))⟦(2 : ℤ)⟧)) ≫
        (whiskerLeftShiftIso (S.E r) (S.E (r + 1)) 2).hom) ≫
        ((S.cross r : S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦(-2 : ℤ)⟧)⟦(2 : ℤ)⟧' ≫
          (shiftFunctorAdd' _ (-2 : ℤ) 2 0 (by norm_num)).inv.app _ ≫ Z) -
      (S.rQ : k) • 𝟙 (S.E r ≫ S.E (r + 1)) := by
    have h1 : N.τ.comp N.xR (by norm_num : (2 : ℤ) + -2 = 0) =
        N.xL.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0) - (N.r : k) • NH2.one := by
      rw [NH2.xL_comp_τ]; abel
    have h2 : (N.τ.comp N.xR (by norm_num : (2 : ℤ) + -2 = 0) :
        S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦(0 : ℤ)⟧) ≫ Z =
        ((N.xL.comp N.τ (by norm_num : (-2 : ℤ) + 2 = 0) :
          S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦(0 : ℤ)⟧) -
          (N.r : k) • (NH2.one : S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦(0 : ℤ)⟧)) ≫ Z := by
      rw [h1]
    rw [Preadditive.sub_comp, Linear.smul_comp] at h2
    simp only [ShiftedHom.comp, NH2.one, ShiftedHom.mk₀, Category.assoc, Category.id_comp] at h2
    have h3 : (shiftFunctorZero' (S.obj r ⟶ S.obj (r + 1 + 1)) (0 : ℤ) rfl).inv.app
        (S.E r ≫ S.E (r + 1)) ≫ Z = 𝟙 _ := by
      rw [hZ]
      simp [shiftFunctorZero']
    rw [h3] at h2
    have hxL : (N.xL : S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦(2 : ℤ)⟧) =
        (S.E r ◁ (S.dot (r + 1) : S.E (r + 1) ⟶ (S.E (r + 1))⟦(2 : ℤ)⟧)) ≫
          (whiskerLeftShiftIso (S.E r) (S.E (r + 1)) 2).hom := shWhiskerLeft_eq _ _
    rw [← hxL]
    exact h2
  -- compose the vanishing map with the slid dot
  have h0 : ιb e 0 ≫ (S.F r ◁ ((S.cross r : S.E r ≫ S.E (r + 1) ⟶
      (S.E r ≫ S.E (r + 1))⟦(-2 : ℤ)⟧) ≫
      ((N.xR : S.E r ≫ S.E (r + 1) ⟶ (S.E r ≫ S.E (r + 1))⟦(2 : ℤ)⟧)⟦(-2 : ℤ)⟧' ≫
        (shiftFunctorAdd' _ (2 : ℤ) (-2) 0 (by norm_num)).inv.app _ ≫ Z))) = 0 := by
    rw [Bicategory.whiskerLeft_comp, ← Category.assoc]
    change lemAprimeRight e ≫ _ = 0
    rw [hR, zero_comp]
  rw [hrel, whiskerLeft_sub', whiskerLeft_smul, Bicategory.whiskerLeft_id, Preadditive.comp_sub,
    Linear.comp_smul, Category.comp_id, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_comp,
    Bicategory.whiskerLeft_comp, ← Φ₀] at h0
  simp only [Category.assoc] at h0
  rw [← Category.assoc (ιb e 0) (S.Φ₀ r), ιb_comp_Φ₀] at h0
  simp only [Category.assoc] at h0
  rw [reassoc_of% (ιb₂_comp_shift e (S.cross r)), ← lemAprimeRight, hR, Functor.map_zero,
    zero_comp, comp_zero, comp_zero, zero_sub, neg_eq_zero] at h0
  -- so `r • cup = 0`, hence the cup vanishes, hence `E 1_m = 0`
  have hι : ιb e 0 = 0 := by
    have := congrArg (fun φ => ((S.rQ⁻¹ : kˣ) : k) • φ) h0
    simpa [smul_smul] using this
  have hid : (𝟙 (S.Bsum r 0) : _ ⟶ _) = 0 := by rw [← ιb_comp_πb e hm, hι, zero_comp]
  have hz : IsZero (S.Bsum r 0) := (IsZero.iff_id_eq_zero _).2 hid
  exact hE (((shiftFunctor _ (-(1 * ((((S.wt (r + 1)).toNat : ℕ) : ℤ) - 1 -
    2 * ((0 : ℕ) : ℤ))))).map_isZero (hz.of_iso (S.BsumIso r 0).symm)).of_iso
    ((shiftFunctorCompIsoId _ _ _ (by ring)).app _).symm)

end Right

end StrongSl2

end Categorification.TwoRep
