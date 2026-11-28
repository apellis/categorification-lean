/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceCyclicTwo
import Categorification.WeightedKLR.Rigidity.CupCapProp721TraceCyclicMat
import Categorification.Diagrams.KLR.MatEndNatEmbSigma

/-!
# Symmetry of the two-step trace along composable matrix maps against a cyclic 2-morphism

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 4.31,
as used in §7.3, proof of Proposition 7.21, for the crossing on `𝔉_i²`. Let `F₁ : C₀ ⥤ C₁`,
`F₂ : C₁ ⥤ C₂` be composable additive functors with matrix maps `φ₁`, `φ₂`
(`KLR.Diagram.MatEnd.mapEmbOp`), and let `Res_{φ₁} ⊣ Ind_{φ₁}`, `Res_{φ₂} ⊣ Ind_{φ₂}` be the
adjunctions `KLR.Diagram.MatEnd.resIndAdjunction` built from biadjunctions `F₁' ⊣⊢ E₁`,
`F₂' ⊣⊢ E₂` on completed additive envelopes. The two-step trace of their composite
(`CupCap.resIndTrace₂`) closes a diagram on the right by the nested cup and cap: it is the unit
of the composite adjunction `F₁' F₂' ⊣ E₂ E₁`, then `E₁ E₂` of the diagram, then the counit of
`E₂ E₁ ⊣ F₁' F₂'` (`CupCap.unit_map_close_nested`).

If a natural endomorphism `θ` of `F₁ ⋙ F₂` is cyclic for the composite adjunctions, the two-step
trace is symmetric against its diagonal matrix `c = natEmb θ`:
`τ₁₂(c w) = τ₁₂(w φ₂(φ₁(1)) c φ₂(1))` (`KLR.Diagram.MatEnd.resIndTrace₂_cyclic`). This is the
hypothesis of `CupCap.conjugateEquiv_resAct₂_eq_of_trace`. The diagram slides past `c` on the
left by the corner calculus of the composite generator (`karoubiGen_comp`), and on the right by
the generator condition of Rouquier's crossing (`karoubiSect_corner_sigmaElt`).

## Main results

* `CupCap.unit_map_close_nested`: two nested closings are one closing along the composite
  adjunctions.
* `KLR.Diagram.MatEnd.resIndTrace₂_cyclic`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Idempotents MulOpposite Categorification.InductionAlong

namespace Categorification.Stendhal.CupCap

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] {L₁ : C₀ ⥤ C₁}
  {R₁ : C₁ ⥤ C₀} {L₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁} (a₁ : L₁ ⊣ R₁) (a₁' : R₁ ⊣ L₁) (a₂ : L₂ ⊣ R₂)
  (a₂' : R₂ ⊣ L₂)

/-- **Nested closings are closings along the composite adjunctions**: closing
`s ≫ (closing of V) ≫ g` with `L₁ ⊣ R₁`, `R₁ ⊣ L₁` is closing `L₂ s ≫ V ≫ L₂ g` with the
composites `L₁ L₂ ⊣ R₂ R₁` and `R₂ R₁ ⊣ L₁ L₂`. -/
theorem unit_map_close_nested (x : C₀) (y : C₁) (s : L₁.obj x ⟶ y) (g : y ⟶ L₁.obj x)
    (V : L₂.obj y ⟶ L₂.obj y) :
    a₁.unit.app x ≫ R₁.map (s ≫ (a₂.unit.app y ≫ R₂.map V ≫ a₂'.counit.app y) ≫ g) ≫
        a₁'.counit.app x =
      (a₁.comp a₂).unit.app x ≫ (R₂ ⋙ R₁).map (L₂.map s ≫ V ≫ L₂.map g) ≫
        (a₂'.comp a₁').counit.app x := by
  have hin : s ≫ (a₂.unit.app y ≫ R₂.map V ≫ a₂'.counit.app y) ≫ g =
      a₂.unit.app (L₁.obj x) ≫ R₂.map (L₂.map s ≫ V ≫ L₂.map g) ≫ a₂'.counit.app (L₁.obj x) := by
    have h1 := a₂.unit.naturality s
    have h2 := a₂'.counit.naturality g
    simp only [Functor.id_map, Functor.comp_map] at h1 h2
    simp only [Functor.map_comp, Category.assoc]
    rw [h2, ← reassoc_of% h1]
  rw [hin, Adjunction.comp_unit_app, Adjunction.comp_counit_app]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

end Categorification.Stendhal.CupCap

namespace Categorification.KLR.Diagram.MatEnd

open Categorification.Stendhal.CupCap

attribute [local instance] HomTensor.bimodule

section One

variable {C : Type} [Category.{0} C] [Preadditive C] {D : Type} [Category.{0} D]
  [Preadditive D] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  {X : ι → C} {Y : κ → D} (F : C ⥤ D) [F.Additive] {e : ι → κ}
  (he : Function.Injective e) (h : ∀ i, F.obj (X i) = Y (e i))
  {E : Karoubi (Mat_ D) ⥤ Karoubi (Mat_ C)} [E.Additive] (adj : mapKaroubi F.mapMat_ ⊣ E)
  (adj' : E ⊣ mapKaroubi F.mapMat_)
  {J : Type} [Fintype J]
  (π : J → (E.obj ((toKaroubi _).obj (familySum Y)) ⟶ (toKaroubi _).obj (familySum X)))
  (ι' : J → ((toKaroubi _).obj (familySum X) ⟶ E.obj ((toKaroubi _).obj (familySum Y))))
  (hπ : ∑ j, π j ≫ ι' j = 𝟙 _)

/-- **The trace of `resIndAdjunction` as an endomorphism of the completed sum**: under
`karoubiMatrixOp`, the trace at `z` is the closing morphism `resIndClose z`. -/
theorem karoubiMatrixOp_resIndTrace (z : Corner (mapEmbOp F he h))
    (hz : mapEmbOp F he h 1 * z.1 = z.1) :
    (karoubiMatrixOp X (resIndTrace (resIndAdjunction F he h adj adj' π ι' hπ) z hz)).unop =
      resIndClose F he h adj adj' z := by
  rw [resIndTrace_eq]
  change (karoubiMatrixOp X ((karoubiMatrixOp X).symm (op (resIndClose F he h adj adj' z)) *
    1)).unop = _
  rw [mul_one, RingEquiv.apply_symm_apply]
  rfl

end One

section Two

variable {C₀ C₁ C₂ : Type} [Category.{0} C₀] [Preadditive C₀] [Category.{0} C₁] [Preadditive C₁]
  [Category.{0} C₂] [Preadditive C₂]
  {ι₀ ι₁ ι₂ : Type} [Fintype ι₀] [DecidableEq ι₀] [Fintype ι₁] [DecidableEq ι₁]
  [Fintype ι₂] [DecidableEq ι₂] {X₀ : ι₀ → C₀} {X₁ : ι₁ → C₁} {X₂ : ι₂ → C₂}
  (F₁ : C₀ ⥤ C₁) (F₂ : C₁ ⥤ C₂) [F₁.Additive] [F₂.Additive] {e₁ : ι₀ → ι₁} {e₂ : ι₁ → ι₂}
  (he₁ : Function.Injective e₁) (h₁ : ∀ i, F₁.obj (X₀ i) = X₁ (e₁ i))
  (he₂ : Function.Injective e₂) (h₂ : ∀ j, F₂.obj (X₁ j) = X₂ (e₂ j))
  {E₁ : Karoubi (Mat_ C₁) ⥤ Karoubi (Mat_ C₀)} [E₁.Additive]
  (a₁ : mapKaroubi F₁.mapMat_ ⊣ E₁) (a₁' : E₁ ⊣ mapKaroubi F₁.mapMat_)
  {J₁ : Type} [Fintype J₁]
  (π₁ : J₁ → (E₁.obj ((toKaroubi _).obj (familySum X₁)) ⟶ (toKaroubi _).obj (familySum X₀)))
  (ι₁ : J₁ → ((toKaroubi _).obj (familySum X₀) ⟶ E₁.obj ((toKaroubi _).obj (familySum X₁))))
  (hπ₁ : ∑ j, π₁ j ≫ ι₁ j = 𝟙 _)
  {E₂ : Karoubi (Mat_ C₂) ⥤ Karoubi (Mat_ C₁)} [E₂.Additive]
  (a₂ : mapKaroubi F₂.mapMat_ ⊣ E₂) (a₂' : E₂ ⊣ mapKaroubi F₂.mapMat_)
  {J₂ : Type} [Fintype J₂]
  (π₂ : J₂ → (E₂.obj ((toKaroubi _).obj (familySum X₂)) ⟶ (toKaroubi _).obj (familySum X₁)))
  (ι₂ : J₂ → ((toKaroubi _).obj (familySum X₁) ⟶ E₂.obj ((toKaroubi _).obj (familySum X₂))))
  (hπ₂ : ∑ j, π₂ j ≫ ι₂ j = 𝟙 _)

set_option hygiene false in
local notation "K₀" => (toKaroubi _).obj (familySum X₀)
set_option hygiene false in
local notation "K₁" => (toKaroubi _).obj (familySum X₁)
set_option hygiene false in
local notation "K₂" => (toKaroubi _).obj (familySum X₂)
set_option hygiene false in
local notation "L₁" => mapKaroubi F₁.mapMat_
set_option hygiene false in
local notation "L₂" => mapKaroubi F₂.mapMat_

/-- The diagram closed by the two-step trace at `w`:
`F₂'(sect₁) ≫ sect₂ ≫ w ≫ F₂'(gen₁)`, an endomorphism of `F₂' F₁' G_{X₀}`. -/
abbrev twoStepDiagram (w : Corner (mapEmbOp F₂ he₂ h₂)) :
    (L₂).obj ((L₁).obj K₀) ⟶ (L₂).obj ((L₁).obj K₀) :=
  (L₂).map (karoubiSect F₁ h₁) ≫ (karoubiSect F₂ h₂ ≫ karoubiCorner F₂ he₂ h₂ w) ≫
    (L₂).map (karoubiGen F₁ he₁ h₁)

set_option hygiene false in
local notation "M₁" => resIndAdjunction F₁ he₁ h₁ a₁ a₁' π₁ ι₁ hπ₁
set_option hygiene false in
local notation "M₂" => resIndAdjunction F₂ he₂ h₂ a₂ a₂' π₂ ι₂ hπ₂

/-- **The two-step trace closes the two-step diagram with the nested cup and cap** (Webster,
arXiv:1309.3796v3, Theorem 4.31): under `karoubiMatrixOp`, the trace `τ₁₂(w)` is the unit of
`F₁' F₂' ⊣ E₂ E₁`, then `E₁ E₂` of `twoStepDiagram w`, then the counit of `E₂ E₁ ⊣ F₁' F₂'`. -/
theorem karoubiMatrixOp_resIndTrace₂ (w : Corner (mapEmbOp F₂ he₂ h₂))
    (hw : mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ 1) * w.1 = w.1) :
    (karoubiMatrixOp X₀ (resIndTrace₂ (M₁) (M₂) w hw)).unop =
      (a₁.comp a₂).unit.app K₀ ≫ (E₂ ⋙ E₁).map (twoStepDiagram F₁ F₂ he₁ h₁ he₂ h₂ w) ≫
        (a₂'.comp a₁').counit.app K₀ := by
  unfold resIndTrace₂
  rw [karoubiMatrixOp_resIndTrace F₁ he₁ h₁ a₁ a₁' π₁ ι₁ hπ₁ _
      (trace_smul_unitGen_fixed (M₂) w hw),
    resIndClose_eq_unit F₁ he₁ h₁ a₁ a₁' _ (trace_smul_unitGen_fixed (M₂) w hw),
    karoubiCorner_smul, karoubiMatrixOpY_eq,
    karoubiMatrixOp_resIndTrace F₂ he₂ h₂ a₂ a₂' π₂ ι₂ hπ₂ w (fixed_of_fixed₂ hw),
    resIndClose_eq_unit F₂ he₂ h₂ a₂ a₂' w (fixed_of_fixed₂ hw)]
  exact unit_map_close_nested a₁ a₁' a₂ a₂' K₀ K₁ _ _ _

variable (θ : F₁ ⋙ F₂ ⟶ F₁ ⋙ F₂)

set_option hygiene false in
local notation "c" => op (natEmb (F₁ ⋙ F₂) (compEq F₁ F₂ h₁ h₂) θ)

/-- The completed `θ` as an endomorphism of `F₁' ⋙ F₂'`. -/
abbrev compCompletion : (L₁) ⋙ (L₂) ⟶ (L₁) ⋙ (L₂) :=
  completionMap₂ θ

/-- `θ` slides through the composite generator: `c ≫ gen = gen ≫ θ`. -/
theorem natEmb_comp_karoubiGen :
    (karoubiMatrixOpY X₂ (c)).unop ≫ karoubiGen F₂ he₂ h₂ ≫ (L₂).map (karoubiGen F₁ he₁ h₁) =
      (karoubiGen F₂ he₂ h₂ ≫ (L₂).map (karoubiGen F₁ he₁ h₁)) ≫
        (compCompletion F₁ F₂ θ).app K₀ := by
  rw [← karoubiGen_comp F₁ F₂ he₁ h₁ he₂ h₂]
  have hgen : (c) • unitGen (mapEmbOp (F₁ ⋙ F₂) (he₂.comp he₁) (compEq F₁ F₂ h₁ h₂)) =
      cornerMul (intertwines_natEmb (F₁ ⋙ F₂) (he₂.comp he₁) (compEq F₁ F₂ h₁ h₂) θ)
        (unitGen (mapEmbOp (F₁ ⋙ F₂) (he₂.comp he₁) (compEq F₁ F₂ h₁ h₂))) :=
    Subtype.ext (natEmb_commute (F₁ ⋙ F₂) (he₂.comp he₁) (compEq F₁ F₂ h₁ h₂) θ 1)
  rw [← karoubiCorner_smul, hgen, karoubiCorner_cornerMul_natEmb]

/-- The composite section followed by the composite generator is the identity. -/
theorem compSect_compGen {Z : Karoubi (Mat_ C₂)}
    (k : (L₂).obj ((L₁).obj K₀) ⟶ Z) :
    (L₂).map (karoubiSect F₁ h₁) ≫ karoubiSect F₂ h₂ ≫ karoubiGen F₂ he₂ h₂ ≫
        (L₂).map (karoubiGen F₁ he₁ h₁) ≫ k = k := by
  rw [← Category.assoc (karoubiSect F₂ h₂), karoubiSect_gen, Category.id_comp,
    ← Functor.map_comp_assoc, karoubiSect_gen, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The composite generator followed by the composite section is the projector of
`φ₂(φ₁(1))`. -/
theorem compGen_compSect :
    karoubiGen F₂ he₂ h₂ ≫ (L₂).map (karoubiGen F₁ he₁ h₁) ≫
        (L₂).map (karoubiSect F₁ h₁) ≫ karoubiSect F₂ h₂ =
      (karoubiMatrixOpY X₂ (mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ 1))).unop := by
  rw [← Category.assoc ((L₂).map _), ← Functor.map_comp,
    karoubiGen_sect F₁ he₁ h₁, karoubiMatrixOpY_eq (X₁ := X₁), ← Category.assoc,
    karoubiGen_map F₂ he₂ h₂, Category.assoc, karoubiGen_sect F₂ he₂ h₂]
  change ((karoubiMatrixOpY X₂ (mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ 1))) *
    (karoubiMatrixOpY X₂ (mapEmbOp F₂ he₂ h₂ 1))).unop = _
  rw [← map_mul, ← map_mul, mul_one]

/-- `c` slides into the corner morphism of `w` as `θ`. -/
theorem karoubiCorner_natEmb_smul (w : Corner (mapEmbOp F₂ he₂ h₂))
    (hw : mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ 1) * w.1 = w.1) :
    karoubiCorner F₂ he₂ h₂ ((c) • w) =
      karoubiGen F₂ he₂ h₂ ≫ (L₂).map (karoubiGen F₁ he₁ h₁) ≫
        (compCompletion F₁ F₂ θ).app K₀ ≫ (L₂).map (karoubiSect F₁ h₁) ≫ karoubiSect F₂ h₂ ≫
          karoubiCorner F₂ he₂ h₂ w := by
  have hwf : karoubiCorner F₂ he₂ h₂ w =
      (karoubiMatrixOpY X₂ (mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ 1))).unop ≫
        karoubiCorner F₂ he₂ h₂ w := by
    rw [← karoubiCorner_smul]
    exact congrArg _ (Subtype.ext hw.symm)
  rw [karoubiCorner_smul]
  conv_lhs => rw [hwf, ← compGen_compSect F₁ F₂ he₁ h₁ he₂ h₂]
  have hn := natEmb_comp_karoubiGen F₁ F₂ he₁ h₁ he₂ h₂ θ
  simp only [Category.assoc] at hn ⊢
  rw [reassoc_of% hn]

/-- **The left slide**: `twoStepDiagram (c w) = θ ≫ twoStepDiagram w` for `φ₂(φ₁(1)) w = w`. -/
theorem twoStepDiagram_smul (w : Corner (mapEmbOp F₂ he₂ h₂))
    (hw : mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ 1) * w.1 = w.1) :
    twoStepDiagram F₁ F₂ he₁ h₁ he₂ h₂ ((c) • w) =
      (compCompletion F₁ F₂ θ).app K₀ ≫ twoStepDiagram F₁ F₂ he₁ h₁ he₂ h₂ w := by
  unfold twoStepDiagram
  rw [karoubiCorner_natEmb_smul F₁ F₂ he₁ h₁ he₂ h₂ θ w hw]
  simp only [Category.assoc]
  rw [compSect_compGen]

/-- **The right slide**: `twoStepDiagram (w φ₂(φ₁(1)) c φ₂(1)) = twoStepDiagram w ≫ θ`. -/
theorem twoStepDiagram_twoStepRightElem (w : Corner (mapEmbOp F₂ he₂ h₂)) :
    twoStepDiagram F₁ F₂ he₁ h₁ he₂ h₂
        (Corner.twoStepRightElem (c) w (unitGen (mapEmbOp F₁ he₁ h₁))) =
      twoStepDiagram F₁ F₂ he₁ h₁ he₂ h₂ w ≫ (compCompletion F₁ F₂ θ).app K₀ := by
  set σ := sigmaElt (mapEmbOp F₁ he₁ h₁) (mapEmbOp F₂ he₂ h₂) (c)
    (unitGen (mapEmbOp F₁ he₁ h₁))
  have hσfix : (karoubiMatrixOpY X₂ (mapEmbOp F₂ he₂ h₂ 1)).unop ≫ karoubiCorner F₂ he₂ h₂ σ =
      karoubiCorner F₂ he₂ h₂ σ := by
    rw [← karoubiCorner_smul]
    refine congrArg _ (Subtype.ext ?_)
    change mapEmbOp F₂ he₂ h₂ 1 * (mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ 1) *
      ((c) * mapEmbOp F₂ he₂ h₂ 1)) = _
    rw [← mul_assoc, ← map_mul, one_mul]
    rfl
  have hw1 : (karoubiMatrixOpY X₂ w.1).unop ≫ karoubiGen F₂ he₂ h₂ =
      karoubiCorner F₂ he₂ h₂ w := by
    rw [← karoubiCorner_smul]
    exact congrArg _ (Subtype.ext w.2)
  have hσ : karoubiCorner F₂ he₂ h₂ σ =
      karoubiGen F₂ he₂ h₂ ≫ (L₂).map (karoubiGen F₁ he₁ h₁) ≫
        (compCompletion F₁ F₂ θ).app K₀ ≫ (L₂).map (karoubiSect F₁ h₁) := by
    rw [← hσfix, ← karoubiGen_sect F₂ he₂ h₂, Category.assoc,
      karoubiSect_corner_sigmaElt F₁ F₂ he₁ h₁ he₂ h₂ θ]
  have he : Corner.twoStepRightElem (c) w (unitGen (mapEmbOp F₁ he₁ h₁)) = w.1 • σ := rfl
  unfold twoStepDiagram
  rw [he, karoubiCorner_smul, hσ]
  simp only [Category.assoc]
  rw [reassoc_of% hw1, ← Functor.map_comp, karoubiSect_gen, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

/-- **The two-step trace along composable matrix maps is symmetric against a cyclic
2-morphism** (Webster, arXiv:1309.3796v3, Theorem 4.31, with the action of the 2-morphisms by
attachment at the right): if `θ : F₁ ⋙ F₂ ⟶ F₁ ⋙ F₂` is cyclic for the composite completed
adjunctions `F₁' F₂' ⊣ E₂ E₁` and `E₂ E₁ ⊣ F₁' F₂'`, then
`τ₁₂(c w) = τ₁₂(w φ₂(φ₁(1)) c φ₂(1))` for `c = natEmb θ` and every `w ∈ A₂ φ₂(1)` with
`φ₂(φ₁(1)) w = w`. -/
theorem resIndTrace₂_cyclic
    (hθ : conjugateEquiv (a₂'.comp a₁') (a₂'.comp a₁')
        (conjugateEquiv (a₁.comp a₂) (a₁.comp a₂) (compCompletion F₁ F₂ θ)) =
      compCompletion F₁ F₂ θ)
    (w : Corner (mapEmbOp F₂ he₂ h₂))
    (hw : mapEmbOp F₂ he₂ h₂ (mapEmbOp F₁ he₁ h₁ 1) * w.1 = w.1) :
    resIndTrace₂ (M₁) (M₂) ((c) • w)
        (smul_fixed₂ (natEmb_comp_commute F₁ F₂ he₁ h₁ he₂ h₂ θ) w hw) =
      resIndTrace₂ (M₁) (M₂)
        (Corner.twoStepRightElem (c) w (unitGen (mapEmbOp F₁ he₁ h₁)))
        (twoStepRightElem_fixed₂ w hw) := by
  apply (karoubiMatrixOp X₀).injective
  apply MulOpposite.unop_injective
  rw [karoubiMatrixOp_resIndTrace₂, karoubiMatrixOp_resIndTrace₂,
    twoStepDiagram_smul F₁ F₂ he₁ h₁ he₂ h₂ θ w hw, twoStepDiagram_twoStepRightElem]
  exact unit_map_counit_comm_of_cyclic (a₁.comp a₂) (a₂'.comp a₁') _ hθ K₀ _

end Two

end Categorification.KLR.Diagram.MatEnd
