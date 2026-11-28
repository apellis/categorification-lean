/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721DerivedPaste

/-!
# Commuting squares transported along comparison functors

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21. The isomorphisms `𝕂 ∘ 𝔈_i ≅ 𝔈_i ∘ 𝕂` and `𝕂 ∘ 𝔉_i ≅ 𝔉_i ∘ 𝕂` between
functors on derived categories of dg modules are obtained from the corresponding isomorphisms of
derived functors of exact functors on Mathlib's derived categories of modules, through the fully
faithful comparison functors. This file isolates that transport in a generic form.

Given functors `Φ_a : 𝒟_a ⥤ D_a` (the comparisons), functors `X, K, K', Y` on the `𝒟` side and
`X^, K^, K'^, Y^` on the `D` side with comparison isomorphisms `X ⋙ Φ ≅ Φ ⋙ X^` (and so on), an
isomorphism `e : K' ⋙ Y ≅ X ⋙ K` is *conjugate* to `e^ : X^ ⋙ K^ ≅ K'^ ⋙ Y^`
(`CupCap.IsComparisonSquare`) when its image under `Φ` is the composite of the comparison
isomorphisms with `e^⁻¹`. A natural transformation `α : X ⟶ X'` is conjugate to `α^ : X^ ⟶ X'^`
(`CupCap.IsComparisonConj`) in the same sense; `CupCap.comparisonConj` constructs it when `Φ` is
fully faithful. Then a 2-morphism identity for `e^` gives one for `e`
(`CupCap.IsComparisonSquare.whisker`), and conjugacy is compatible with pasting
(`CupCap.IsComparisonSquare.paste`) and with changing `X^`, `Y^` along isomorphisms.

## Main definitions and results

* `CupCap.IsComparisonSquare`, `CupCap.IsComparisonConj`, `CupCap.comparisonConj`.
* `CupCap.IsComparisonSquare.whisker`: transport of the 2-morphism identity.
* `CupCap.IsComparisonSquare.paste`, `CupCap.IsComparisonSquare.changeX`,
  `CupCap.IsComparisonSquare.changeY`.
-/

open CategoryTheory

noncomputable section

namespace Categorification.Stendhal.CupCap

section Conj

variable {𝒟₁ 𝒟₂ D₁ D₂ : Type*} [Category* 𝒟₁] [Category* 𝒟₂] [Category* D₁] [Category* D₂]
  {Φ₁ : 𝒟₁ ⥤ D₁} {Φ₂ : 𝒟₂ ⥤ D₂} {X X' : 𝒟₁ ⥤ 𝒟₂} {Xh Xh' : D₁ ⥤ D₂}

/-- `α : X ⟶ X'` is **conjugate** to `αh : Xh ⟶ Xh'` along the comparison isomorphisms
`cX : X ⋙ Φ₂ ≅ Φ₁ ⋙ Xh` and `cX'`: `Φ₂ (α x) = cX x ≫ αh (Φ₁ x) ≫ cX'⁻¹ x`. -/
def IsComparisonConj (cX : X ⋙ Φ₂ ≅ Φ₁ ⋙ Xh) (cX' : X' ⋙ Φ₂ ≅ Φ₁ ⋙ Xh') (αh : Xh ⟶ Xh')
    (α : X ⟶ X') : Prop :=
  ∀ x, Φ₂.map (α.app x) = cX.hom.app x ≫ αh.app (Φ₁.obj x) ≫ cX'.inv.app x

/-- **The conjugate of `αh` along fully faithful comparisons.** -/
def comparisonConj (hΦ : Φ₂.FullyFaithful) (cX : X ⋙ Φ₂ ≅ Φ₁ ⋙ Xh)
    (cX' : X' ⋙ Φ₂ ≅ Φ₁ ⋙ Xh') (αh : Xh ⟶ Xh') : X ⟶ X' :=
  (hΦ.whiskeringRight 𝒟₁).preimage (cX.hom ≫ Functor.whiskerLeft Φ₁ αh ≫ cX'.inv)

theorem isComparisonConj_comparisonConj (hΦ : Φ₂.FullyFaithful) (cX : X ⋙ Φ₂ ≅ Φ₁ ⋙ Xh)
    (cX' : X' ⋙ Φ₂ ≅ Φ₁ ⋙ Xh') (αh : Xh ⟶ Xh') :
    IsComparisonConj cX cX' αh (comparisonConj hΦ cX cX' αh) := fun x => by
  have := congrArg (fun t => NatTrans.app t x)
    ((hΦ.whiskeringRight 𝒟₁).map_preimage (cX.hom ≫ Functor.whiskerLeft Φ₁ αh ≫ cX'.inv))
  refine this.trans ?_
  simp

/-- **Changing both sides of a conjugacy along isomorphisms** `γ : Xh ≅ Xh₂`, `γ' : Xh' ≅ Xh₂'`
with `γ ≫ αh₂ = αh ≫ γ'`. -/
theorem IsComparisonConj.trans_whiskerLeft {Xh₂ Xh₂' : D₁ ⥤ D₂} {cX : X ⋙ Φ₂ ≅ Φ₁ ⋙ Xh}
    {cX' : X' ⋙ Φ₂ ≅ Φ₁ ⋙ Xh'} {αh : Xh ⟶ Xh'} {α : X ⟶ X'}
    (hα : IsComparisonConj cX cX' αh α) (γ : Xh ≅ Xh₂) (γ' : Xh' ≅ Xh₂') {αh₂ : Xh₂ ⟶ Xh₂'}
    (h : γ.hom ≫ αh₂ = αh ≫ γ'.hom) :
    IsComparisonConj (cX ≪≫ Functor.isoWhiskerLeft Φ₁ γ) (cX' ≪≫ Functor.isoWhiskerLeft Φ₁ γ')
      αh₂ α := fun x => by
  have h' := congrArg (fun t => NatTrans.app t (Φ₁.obj x)) h
  simp only [NatTrans.comp_app] at h'
  simp only [hα x, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.assoc, reassoc_of% h',
    Iso.hom_inv_id_app_assoc]

end Conj

section Square

variable {𝒟₁ 𝒟₂ 𝒟₃ 𝒟₄ D₁ D₂ D₃ D₄ : Type*} [Category* 𝒟₁] [Category* 𝒟₂] [Category* 𝒟₃]
  [Category* 𝒟₄] [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄]
  {Φ₁ : 𝒟₁ ⥤ D₁} {Φ₂ : 𝒟₂ ⥤ D₂} {Φ₃ : 𝒟₃ ⥤ D₃} {Φ₄ : 𝒟₄ ⥤ D₄}
  {X X' : 𝒟₁ ⥤ 𝒟₂} {K : 𝒟₂ ⥤ 𝒟₃} {K' : 𝒟₁ ⥤ 𝒟₄} {Y Y' : 𝒟₄ ⥤ 𝒟₃}
  {Xh Xh' : D₁ ⥤ D₂} {Kh : D₂ ⥤ D₃} {K'h : D₁ ⥤ D₄} {Yh Yh' : D₄ ⥤ D₃}

/-- `e : K' ⋙ Y ≅ X ⋙ K` is **conjugate** to `eh : Xh ⋙ Kh ≅ K'h ⋙ Yh` along the comparison
isomorphisms: `Φ₃ (e x) = cY ≫ Yh (cK' x) ≫ eh⁻¹ (Φ₁ x) ≫ Kh (cX⁻¹ x) ≫ cK⁻¹`. -/
def IsComparisonSquare (cX : X ⋙ Φ₂ ≅ Φ₁ ⋙ Xh) (cK : K ⋙ Φ₃ ≅ Φ₂ ⋙ Kh)
    (cK' : K' ⋙ Φ₄ ≅ Φ₁ ⋙ K'h) (cY : Y ⋙ Φ₃ ≅ Φ₄ ⋙ Yh) (eh : Xh ⋙ Kh ≅ K'h ⋙ Yh)
    (e : K' ⋙ Y ≅ X ⋙ K) : Prop :=
  ∀ x, Φ₃.map (e.hom.app x) = cY.hom.app (K'.obj x) ≫ Yh.map (cK'.hom.app x) ≫
    eh.inv.app (Φ₁.obj x) ≫ Kh.map (cX.inv.app x) ≫ cK.inv.app (X.obj x)

/-- **A 2-morphism identity passes along comparisons**: if `e`, `e'` are conjugate to `eh`, `eh'`
and `α`, `β` to `αh`, `βh`, then `(Kh ∘ αh) ≫ eh' = eh ≫ (βh ∘ K'h)` implies
`(β ∘ K') ≫ e' = e ≫ (K ∘ α)`. -/
theorem IsComparisonSquare.whisker [Φ₃.Faithful] {cX : X ⋙ Φ₂ ≅ Φ₁ ⋙ Xh}
    {cX' : X' ⋙ Φ₂ ≅ Φ₁ ⋙ Xh'} {cK : K ⋙ Φ₃ ≅ Φ₂ ⋙ Kh} {cK' : K' ⋙ Φ₄ ≅ Φ₁ ⋙ K'h}
    {cY : Y ⋙ Φ₃ ≅ Φ₄ ⋙ Yh} {cY' : Y' ⋙ Φ₃ ≅ Φ₄ ⋙ Yh'} {eh : Xh ⋙ Kh ≅ K'h ⋙ Yh}
    {eh' : Xh' ⋙ Kh ≅ K'h ⋙ Yh'} {e : K' ⋙ Y ≅ X ⋙ K} {e' : K' ⋙ Y' ≅ X' ⋙ K}
    {αh : Xh ⟶ Xh'} {βh : Yh ⟶ Yh'} {α : X ⟶ X'} {β : Y ⟶ Y'}
    (he : IsComparisonSquare cX cK cK' cY eh e) (he' : IsComparisonSquare cX' cK cK' cY' eh' e')
    (hα : IsComparisonConj cX cX' αh α) (hβ : IsComparisonConj cY cY' βh β)
    (h : Functor.whiskerRight αh Kh ≫ eh'.hom = eh.hom ≫ Functor.whiskerLeft K'h βh) :
    Functor.whiskerLeft K' β ≫ e'.hom = e.hom ≫ Functor.whiskerRight α K := by
  have key : ∀ y, eh.inv.app y ≫ Kh.map (αh.app y) = βh.app (K'h.obj y) ≫ eh'.inv.app y :=
    fun y => by
      have := congrArg (fun t => NatTrans.app t y) h
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at this
      rw [← cancel_mono (eh'.hom.app y), Category.assoc, this, Iso.inv_hom_id_app_assoc,
        Category.assoc, Iso.inv_hom_id_app]
      exact (Category.comp_id _).symm
  ext x
  apply Φ₃.map_injective
  have hK := cK.inv.naturality (α.app x)
  simp only [Functor.comp_map] at hK
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, hβ (K'.obj x), he' x, he x, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← hK, hα x]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Kh.map_comp_assoc (cX.inv.app x), Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% (key (Φ₁.obj x)), ← βh.naturality_assoc]
  rfl

/-- **Changing `Yh` along an isomorphism** `γ : Yh ≅ Yh'` keeps conjugacy, with the comparison
`cY ≫ γ` and the square `eh ≫ (γ ∘ K'h)`. -/
theorem IsComparisonSquare.changeY {cX : X ⋙ Φ₂ ≅ Φ₁ ⋙ Xh} {cK : K ⋙ Φ₃ ≅ Φ₂ ⋙ Kh}
    {cK' : K' ⋙ Φ₄ ≅ Φ₁ ⋙ K'h} {cY : Y ⋙ Φ₃ ≅ Φ₄ ⋙ Yh} {eh : Xh ⋙ Kh ≅ K'h ⋙ Yh}
    {e : K' ⋙ Y ≅ X ⋙ K} (he : IsComparisonSquare cX cK cK' cY eh e) (γ : Yh ≅ Yh')
    {eh' : Xh ⋙ Kh ≅ K'h ⋙ Yh'} (hγ : eh'.hom = eh.hom ≫ Functor.whiskerLeft K'h γ.hom) :
    IsComparisonSquare cX cK cK' (cY ≪≫ Functor.isoWhiskerLeft Φ₄ γ) eh' e := fun x => by
  obtain rfl : eh' = eh ≪≫ Functor.isoWhiskerLeft K'h γ := Iso.ext hγ
  rw [he x]
  simp only [Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Category.assoc]
  rw [← γ.hom.naturality_assoc]
  erw [Iso.hom_inv_id_app_assoc]

/-- **Changing `Xh` along an isomorphism** `γ : Xh ≅ Xh'` keeps conjugacy, with the comparison
`cX ≫ γ` and the square `(Kh ∘ γ⁻¹) ≫ eh`. -/
theorem IsComparisonSquare.changeX {cX : X ⋙ Φ₂ ≅ Φ₁ ⋙ Xh} {cK : K ⋙ Φ₃ ≅ Φ₂ ⋙ Kh}
    {cK' : K' ⋙ Φ₄ ≅ Φ₁ ⋙ K'h} {cY : Y ⋙ Φ₃ ≅ Φ₄ ⋙ Yh} {eh : Xh ⋙ Kh ≅ K'h ⋙ Yh}
    {e : K' ⋙ Y ≅ X ⋙ K} (he : IsComparisonSquare cX cK cK' cY eh e) (γ : Xh ≅ Xh')
    {eh' : Xh' ⋙ Kh ≅ K'h ⋙ Yh} (hγ : eh'.hom = Functor.whiskerRight γ.inv Kh ≫ eh.hom) :
    IsComparisonSquare (cX ≪≫ Functor.isoWhiskerLeft Φ₁ γ) cK cK' cY eh' e := fun x => by
  obtain rfl : eh' = Functor.isoWhiskerRight γ.symm Kh ≪≫ eh := Iso.ext hγ
  rw [he x]
  simp only [Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv,
    Iso.symm_inv, Functor.whiskerRight_app, Category.assoc, Functor.map_comp]
  rw [← Kh.map_comp_assoc (γ.hom.app (Φ₁.obj x)), Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

end Square

section Paste

variable {𝒟₁ 𝒟₂ 𝒟₃ 𝒟₄ 𝒟₅ 𝒟₆ D₁ D₂ D₃ D₄ D₅ D₆ : Type*} [Category* 𝒟₁] [Category* 𝒟₂]
  [Category* 𝒟₃] [Category* 𝒟₄] [Category* 𝒟₅] [Category* 𝒟₆] [Category* D₁] [Category* D₂]
  [Category* D₃] [Category* D₄] [Category* D₅] [Category* D₆]
  {Φ₁ : 𝒟₁ ⥤ D₁} {Φ₂ : 𝒟₂ ⥤ D₂} {Φ₃ : 𝒟₃ ⥤ D₃} {Φ₄ : 𝒟₄ ⥤ D₄} {Φ₅ : 𝒟₅ ⥤ D₅}
  {Φ₆ : 𝒟₆ ⥤ D₆}
  {X₁ : 𝒟₂ ⥤ 𝒟₃} {X₂ : 𝒟₁ ⥤ 𝒟₂} {K : 𝒟₃ ⥤ 𝒟₄} {K₁ : 𝒟₂ ⥤ 𝒟₅} {K₂ : 𝒟₁ ⥤ 𝒟₆}
  {Y₁ : 𝒟₅ ⥤ 𝒟₄} {Y₂ : 𝒟₆ ⥤ 𝒟₅}
  {X₁h : D₂ ⥤ D₃} {X₂h : D₁ ⥤ D₂} {Kh : D₃ ⥤ D₄} {K₁h : D₂ ⥤ D₅} {K₂h : D₁ ⥤ D₆}
  {Y₁h : D₅ ⥤ D₄} {Y₂h : D₆ ⥤ D₅}

theorem squarePaste_inv_app {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄] [Category* C₅] [Category* C₆] {X₁ : C₂ ⥤ C₃} {X₂ : C₁ ⥤ C₂}
    {K : C₃ ⥤ C₄} {K₁ : C₂ ⥤ C₅} {K₂ : C₁ ⥤ C₆} {Y₁ : C₅ ⥤ C₄} {Y₂ : C₆ ⥤ C₅}
    (e₁ : X₁ ⋙ K ≅ K₁ ⋙ Y₁) (e₂ : X₂ ⋙ K₁ ≅ K₂ ⋙ Y₂) (x : C₁) :
    (squarePaste e₁ e₂).inv.app x = Y₁.map (e₂.inv.app x) ≫ e₁.inv.app (X₂.obj x) := by
  simp [squarePaste]

/-- **Conjugacy is compatible with pasting**: the pasting of conjugate squares is conjugate to
the pasting, with the pasted comparison isomorphisms of the composites `X₂ ⋙ X₁`, `Y₂ ⋙ Y₁`. -/
theorem IsComparisonSquare.paste {cX₁ : X₁ ⋙ Φ₃ ≅ Φ₂ ⋙ X₁h} {cX₂ : X₂ ⋙ Φ₂ ≅ Φ₁ ⋙ X₂h}
    {cK : K ⋙ Φ₄ ≅ Φ₃ ⋙ Kh} {cK₁ : K₁ ⋙ Φ₅ ≅ Φ₂ ⋙ K₁h} {cK₂ : K₂ ⋙ Φ₆ ≅ Φ₁ ⋙ K₂h}
    {cY₁ : Y₁ ⋙ Φ₄ ≅ Φ₅ ⋙ Y₁h} {cY₂ : Y₂ ⋙ Φ₅ ≅ Φ₆ ⋙ Y₂h} {eh₁ : X₁h ⋙ Kh ≅ K₁h ⋙ Y₁h}
    {eh₂ : X₂h ⋙ K₁h ≅ K₂h ⋙ Y₂h} {e₁ : K₁ ⋙ Y₁ ≅ X₁ ⋙ K} {e₂ : K₂ ⋙ Y₂ ≅ X₂ ⋙ K₁}
    (he₁ : IsComparisonSquare cX₁ cK cK₁ cY₁ eh₁ e₁)
    (he₂ : IsComparisonSquare cX₂ cK₁ cK₂ cY₂ eh₂ e₂) :
    IsComparisonSquare (squarePaste cX₁ cX₂) cK cK₂ (squarePaste cY₁ cY₂) (squarePaste eh₁ eh₂)
      (squarePaste e₁.symm e₂.symm).symm := fun x => by
  have hY := cY₁.inv.naturality (e₂.hom.app x)
  simp only [Functor.comp_map] at hY
  simp only [Iso.symm_hom, squarePaste_inv_app, squarePaste_hom_app, Iso.symm_inv,
    Functor.map_comp, Functor.comp_map, Category.assoc]
  rw [← cancel_epi (cY₁.inv.app (Y₂.obj (K₂.obj x))), Iso.inv_hom_id_app_assoc, ← reassoc_of% hY,
    he₂ x, he₁ (X₂.obj x)]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Y₁h.map_comp_assoc (cK₁.inv.app (X₂.obj x)), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have hN := eh₁.inv.naturality (cX₂.inv.app x)
  simp only [Functor.comp_map] at hN
  rw [reassoc_of% hN]
  rfl

end Paste

end Categorification.Stendhal.CupCap
