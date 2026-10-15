/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.SumInvPointwise
import Categorification.TwoRep.RouqLocTransport

/-!
# Mates of squares of functors

The mate of a square `τ : G ⋙ L₂ ⟶ L₁ ⋙ H` along adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂`, written with
the unit of `L₂ ⊣ R₂` and the counit of `L₁ ⊣ R₁` (`mateNat`). This is the form of Brundan's
mixed sideways crossing `E_i F_j → F_j E_i` (arXiv:1501.00350v1, (1.7);
`TwoRep.RouqFamily.mixedSigma`). In `LinearCat k` and `AdditiveCat` the bicategorical mate is
`mateNat` of the underlying natural transformations (`LinearCat.mate_hom`,
`AdditiveCat.mate_hom`), and `mateNat` is compatible with maps of the 1-cells that intertwine
the unit, the counit and the square (`mateNat_conj`).
-/

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

section Functor

variable {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒟]
  {L₁ L₁' : 𝒜 ⥤ ℬ} {R₁ R₁' : ℬ ⥤ 𝒜} {G G' : 𝒜 ⥤ 𝒞} {L₂ L₂' : 𝒞 ⥤ 𝒟} {R₂ R₂' : 𝒟 ⥤ 𝒞}
  {H H' : ℬ ⥤ 𝒟}

/-- The mate of a square of functors `τ : G ⋙ L₂ ⟶ L₁ ⋙ H` along the units of `L₂ ⊣ R₂` and
the counit of `L₁ ⊣ R₁`. -/
def mateNat (η₂ : 𝟭 𝒞 ⟶ L₂ ⋙ R₂) (τ : G ⋙ L₂ ⟶ L₁ ⋙ H) (ε₁ : R₁ ⋙ L₁ ⟶ 𝟭 ℬ) :
    R₁ ⋙ G ⟶ H ⋙ R₂ :=
  Functor.whiskerLeft (R₁ ⋙ G) η₂ ≫ Functor.whiskerRight (Functor.whiskerLeft R₁ τ) R₂ ≫
    Functor.whiskerRight ε₁ (H ⋙ R₂)

@[simp] theorem mateNat_app (η₂ : 𝟭 𝒞 ⟶ L₂ ⋙ R₂) (τ : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (ε₁ : R₁ ⋙ L₁ ⟶ 𝟭 ℬ) (Y : ℬ) :
    (mateNat η₂ τ ε₁).app Y = η₂.app (G.obj (R₁.obj Y)) ≫ R₂.map (τ.app (R₁.obj Y)) ≫
      R₂.map (H.map (ε₁.app Y)) := rfl

/-- The mate is compatible with maps of the 1-cells that intertwine the unit, the counit and the
square. -/
theorem mateNat_conj (η₂ : 𝟭 𝒞 ⟶ L₂ ⋙ R₂) (τ : G ⋙ L₂ ⟶ L₁ ⋙ H) (ε₁ : R₁ ⋙ L₁ ⟶ 𝟭 ℬ)
    (η₂' : 𝟭 𝒞 ⟶ L₂' ⋙ R₂') (τ' : G' ⋙ L₂' ⟶ L₁' ⋙ H') (ε₁' : R₁' ⋙ L₁' ⟶ 𝟭 ℬ)
    (e₁ : L₁' ⟶ L₁) (r₁ : R₁' ⟶ R₁) (g : G' ⟶ G) (e₂ : L₂' ⟶ L₂) (r₂ : R₂' ⟶ R₂) (h : H' ⟶ H)
    (hη : η₂' ≫ (Functor.whiskerRight e₂ R₂' ≫ Functor.whiskerLeft L₂ r₂) = η₂)
    (hκ : (Functor.whiskerRight r₁ L₁' ≫ Functor.whiskerLeft R₁ e₁) ≫ ε₁ = ε₁')
    (hτ : τ' ≫ (Functor.whiskerRight e₁ H' ≫ Functor.whiskerLeft L₁ h) =
      (Functor.whiskerRight g L₂' ≫ Functor.whiskerLeft G e₂) ≫ τ) :
    mateNat η₂' τ' ε₁' ≫ (Functor.whiskerRight h R₂' ≫ Functor.whiskerLeft H r₂) =
      (Functor.whiskerRight r₁ G' ≫ Functor.whiskerLeft R₁ g) ≫ mateNat η₂ τ ε₁ := by
  subst hη hκ
  ext Y
  have hτY := NatTrans.congr_app hτ (R₁'.obj Y)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, mateNat_app, Functor.id_obj, Functor.map_comp,
    Category.assoc] at hτY ⊢
  -- move `h` and `e₁` past the counit
  have a1 : H'.map (L₁'.map (r₁.app Y)) ≫ H'.map (e₁.app (R₁.obj Y)) ≫
      H'.map (ε₁.app Y) ≫ h.app Y =
      H'.map (e₁.app (R₁'.obj Y)) ≫ h.app (L₁.obj (R₁'.obj Y)) ≫ H.map (L₁.map (r₁.app Y)) ≫
        H.map (ε₁.app Y) := by
    have n1 := h.naturality (ε₁.app Y)
    have n2 := h.naturality (L₁.map (r₁.app Y))
    have n3 := e₁.naturality (r₁.app Y)
    simp only [Functor.id_obj, Functor.comp_obj] at n1 n2 n3
    rw [n1, ← H'.map_comp_assoc, n3, H'.map_comp_assoc, reassoc_of% n2]
  have a1' := congrArg R₂'.map a1
  have hτ' := congrArg R₂'.map hτY
  have nτ := congrArg R₂'.map (τ.naturality (r₁.app Y))
  have ne := congrArg R₂'.map (e₂.naturality (G.map (r₁.app Y)))
  have ng := congrArg R₂'.map (congrArg L₂'.map (g.naturality (r₁.app Y)))
  have nη1 := η₂'.naturality (G'.map (r₁.app Y))
  have nη2 := η₂'.naturality (g.app (R₁.obj Y))
  have nr1 := r₂.naturality (τ.app (R₁.obj Y))
  have nr2 := r₂.naturality (H.map (ε₁.app Y))
  simp only [Functor.map_comp, Functor.comp_map, Functor.comp_obj, Functor.id_obj,
    Functor.id_map] at a1' hτ' nτ ne ng nη1 nη2 nr1 nr2
  rw [reassoc_of% a1', reassoc_of% hτ', ← reassoc_of% nτ, ← reassoc_of% ne, ← reassoc_of% ng,
    ← reassoc_of% nη1, ← reassoc_of% nη2, nr2, reassoc_of% nr1]

/-- **Invertibility of mates transfers along isomorphisms of the 1-cells** that intertwine the
unit, the counit and the square. -/
theorem isIso_mateNat_of_conj (η₂ : 𝟭 𝒞 ⟶ L₂ ⋙ R₂) (τ : G ⋙ L₂ ⟶ L₁ ⋙ H)
    (ε₁ : R₁ ⋙ L₁ ⟶ 𝟭 ℬ) (η₂' : 𝟭 𝒞 ⟶ L₂' ⋙ R₂') (τ' : G' ⋙ L₂' ⟶ L₁' ⋙ H')
    (ε₁' : R₁' ⋙ L₁' ⟶ 𝟭 ℬ) (e₁ : L₁' ≅ L₁) (r₁ : R₁' ≅ R₁) (g : G' ≅ G) (e₂ : L₂' ≅ L₂)
    (r₂ : R₂' ≅ R₂) (h : H' ≅ H)
    (hη : η₂' ≫ (Functor.whiskerRight e₂.hom R₂' ≫ Functor.whiskerLeft L₂ r₂.hom) = η₂)
    (hκ : (Functor.whiskerRight r₁.hom L₁' ≫ Functor.whiskerLeft R₁ e₁.hom) ≫ ε₁ = ε₁')
    (hτ : τ' ≫ (Functor.whiskerRight e₁.hom H' ≫ Functor.whiskerLeft L₁ h.hom) =
      (Functor.whiskerRight g.hom L₂' ≫ Functor.whiskerLeft G e₂.hom) ≫ τ)
    [IsIso (mateNat η₂ τ ε₁)] : IsIso (mateNat η₂' τ' ε₁') := by
  have e := mateNat_conj η₂ τ ε₁ η₂' τ' ε₁' e₁.hom r₁.hom g.hom e₂.hom r₂.hom h.hom hη hκ hτ
  have e' : mateNat η₂' τ' ε₁' =
      ((Functor.isoWhiskerRight r₁ G' ≪≫ Functor.isoWhiskerLeft R₁ g).hom ≫
        mateNat η₂ τ ε₁) ≫ (Functor.isoWhiskerRight h R₂' ≪≫ Functor.isoWhiskerLeft H r₂).inv := by
    rw [Iso.eq_comp_inv]
    exact e
  rw [e']
  infer_instance

end Functor

section Bicat

universe w v u

variable {𝔅 : Type u} [Bicategory.{w, v} 𝔅] {a b c d : 𝔅} {l₁ : a ⟶ b} {r₁ : b ⟶ a}
  {g : a ⟶ c} {l₂ : c ⟶ d} {r₂ : d ⟶ c} {h : b ⟶ d}

/-- The mate with all associators and unitors written out. -/
theorem mateEquiv_eq (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (τ : g ≫ l₂ ⟶ l₁ ≫ h) :
    mateEquiv adj₁ adj₂ τ = (ρ_ (r₁ ≫ g)).inv ≫ (r₁ ≫ g) ◁ adj₂.unit ≫
      (α_ r₁ g (l₂ ≫ r₂)).hom ≫ r₁ ◁ (α_ g l₂ r₂).inv ≫ r₁ ◁ τ ▷ r₂ ≫
      r₁ ◁ (α_ l₁ h r₂).hom ≫ (α_ r₁ l₁ (h ≫ r₂)).inv ≫ adj₁.counit ▷ (h ≫ r₂) ≫
      (λ_ (h ≫ r₂)).hom := by
  rw [mateEquiv_apply']
  bicategory

end Bicat

namespace LinearCat

universe w v u

variable {k : Type w} [CommRing k] {A B C D : LinearCat.{w, v, u} k} {l₁ : A ⟶ B} {r₁ : B ⟶ A}
  {g : A ⟶ C} {l₂ : C ⟶ D} {r₂ : D ⟶ C} {h : B ⟶ D}

/-- The mate in `LinearCat k` is the mate of natural transformations. -/
theorem mate_hom (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (τ : g ≫ l₂ ⟶ l₁ ≫ h) :
    (mateEquiv adj₁ adj₂ τ).hom = mateNat adj₂.unit.hom τ.hom adj₁.counit.hom := by
  rw [mateEquiv_eq]
  ext X
  change 𝟙 _ ≫ adj₂.unit.hom.app (g.obj.obj (r₁.obj.obj X)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
      r₂.obj.map (τ.hom.app (r₁.obj.obj X)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
      r₂.obj.map (h.obj.map (adj₁.counit.hom.app X)) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  rfl

end LinearCat

namespace AdditiveCat

universe v u

variable {A B C D : AdditiveCat.{v, u}} {l₁ : A ⟶ B} {r₁ : B ⟶ A}
  {g : A ⟶ C} {l₂ : C ⟶ D} {r₂ : D ⟶ C} {h : B ⟶ D}

/-- The mate in `AdditiveCat` is the mate of natural transformations. -/
theorem mate_hom (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂) (τ : g ≫ l₂ ⟶ l₁ ≫ h) :
    (mateEquiv adj₁ adj₂ τ).hom = mateNat adj₂.unit.hom τ.hom adj₁.counit.hom := by
  rw [mateEquiv_eq]
  ext X
  change 𝟙 _ ≫ adj₂.unit.hom.app (g.obj.obj (r₁.obj.obj X)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
      r₂.obj.map (τ.hom.app (r₁.obj.obj X)) ≫ 𝟙 _ ≫ 𝟙 _ ≫
      r₂.obj.map (h.obj.map (adj₁.counit.hom.app X)) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  rfl

end AdditiveCat

end Categorification.TwoRep
