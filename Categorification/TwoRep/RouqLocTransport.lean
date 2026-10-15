/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.AdditiveCat
import Categorification.TwoRep.RouqBoundaryAdjunction

/-!
# Transporting Rouquier data along isomorphisms of 1-cells

Brundan's local Rouquier data (`RouqLoc`, arXiv:1501.00350v1, Definition 1.1, one colour)
and the boundary coefficients (`RouqBoundary.Coefficients`) only depend on the 1-cells up
to isomorphism. In `AdditiveCat`, where 1-cells are additive functors, this file transports
them along natural isomorphisms `e : E' ≅ E` and `r : R' ≅ R` of the underlying functors,
provided the units, counits, dots and crossings correspond.

* `SumInvTo.conj`, `SumInvFrom.conj` : conjugating an explicit inverse of a map into (out
  of) a direct sum by isomorphisms, in any preadditive category.
* `AdditiveCat.RouqLoc.transport`, `RouqBoundary.Coefficients.transport`.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory

section Conj
variable {D : Type*} [Category D] [Preadditive D]

/-- Conjugate an explicit inverse of `(f, g 0, …, g (n-1))` by isomorphisms. -/
def SumInvTo.conj {X Y Z X' Y' Z' : D} {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)} {n : ℕ}
    (S : SumInvTo f g n) (eX : X' ≅ X) (eY : Y ≅ Y') (eZ : Z ≅ Z') {f₂ : X' ⟶ Y'}
    {g₂ : ℕ → (X' ⟶ Z')} (hf : f₂ = eX.hom ≫ f ≫ eY.hom)
    (hg : ∀ m, g₂ m = eX.hom ≫ g m ≫ eZ.hom) : SumInvTo f₂ g₂ n where
  f' := eY.inv ≫ S.f' ≫ eX.inv
  g' m := eZ.inv ≫ S.g' m ≫ eX.inv
  total := by
    have h := congrArg (fun t => eX.hom ≫ t ≫ eX.inv) S.total
    simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
      Preadditive.comp_sum, Category.assoc, Category.id_comp, Iso.hom_inv_id] at h
    simp only [hf, hg, Category.assoc, Iso.hom_inv_id_assoc]
    exact h
  ff := by
    simp only [hf, Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% S.ff, Iso.inv_hom_id]
  fg m hm := by
    simp only [hg, Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% S.fg m hm, Limits.zero_comp, Limits.comp_zero]
  gf m hm := by
    simp only [hf, Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% S.gf m hm, Limits.zero_comp, Limits.comp_zero]
  gg m m' hm hm' := by
    simp only [hg, Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% S.gg m m' hm hm']
    split_ifs <;> simp

/-- Conjugate an explicit inverse of `(f, g 0, …, g (n-1))` out of a direct sum. -/
def SumInvFrom.conj {X Y Z X' Y' Z' : D} {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)} {n : ℕ}
    (S : SumInvFrom f g n) (eX : X ≅ X') (eY : Y' ≅ Y) (eZ : Z' ≅ Z) {f₂ : Y' ⟶ X'}
    {g₂ : ℕ → (Z' ⟶ X')} (hf : f₂ = eY.hom ≫ f ≫ eX.hom)
    (hg : ∀ m, g₂ m = eZ.hom ≫ g m ≫ eX.hom) : SumInvFrom f₂ g₂ n where
  f' := eX.inv ≫ S.f' ≫ eY.inv
  g' m := eX.inv ≫ S.g' m ≫ eZ.inv
  total := by
    have h := congrArg (fun t => eX.inv ≫ t ≫ eX.hom) S.total
    simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
      Preadditive.comp_sum, Category.assoc, Category.id_comp, Iso.inv_hom_id] at h
    simp only [hf, hg, Category.assoc, Iso.inv_hom_id_assoc]
    exact h
  ff := by
    simp only [hf, Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% S.ff, Iso.hom_inv_id]
  fg m hm := by
    simp only [hf, Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% S.fg m hm, Limits.zero_comp, Limits.comp_zero]
  gf m hm := by
    simp only [hg, Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% S.gf m hm, Limits.zero_comp, Limits.comp_zero]
  gg m m' hm hm' := by
    simp only [hg, Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% S.gg m m' hm hm']
    split_ifs <;> simp

end Conj

theorem powComp_conj {D : Type*} [Category D] {X X' : D} (e : X' ≅ X) {x' : X' ⟶ X'}
    {x : X ⟶ X} (hx : x' ≫ e.hom = e.hom ≫ x) (n : ℕ) :
    powComp x' n ≫ e.hom = e.hom ≫ powComp x n := by
  induction n with
  | zero => simp
  | succ n hn => rw [powComp_succ, powComp_succ, Category.assoc, hx, ← Category.assoc, hn,
      Category.assoc]

section Functor

variable {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
  {E₁ E₁' : 𝒜 ⥤ ℬ} {R₁ R₁' : ℬ ⥤ 𝒜} {E₂ E₂' : ℬ ⥤ 𝒞} {R₂ R₂' : 𝒞 ⥤ ℬ}

/-- The rightward crossing of natural transformations (the form of `AdditiveCat.sigma_hom`)
is compatible with maps of the 1-cells that intertwine the units, counits and crossings. -/
theorem sigmaFunctor_conj (η : 𝟭 ℬ ⟶ E₂ ⋙ R₂) (τ : E₁ ⋙ E₂ ⟶ E₁ ⋙ E₂) (κ : R₁ ⋙ E₁ ⟶ 𝟭 ℬ)
    (η' : 𝟭 ℬ ⟶ E₂' ⋙ R₂') (τ' : E₁' ⋙ E₂' ⟶ E₁' ⋙ E₂') (κ' : R₁' ⋙ E₁' ⟶ 𝟭 ℬ)
    (e₁ : E₁' ⟶ E₁) (e₂ : E₂' ⟶ E₂) (r₁ : R₁' ⟶ R₁) (r₂ : R₂' ⟶ R₂)
    (hη : η' ≫ (Functor.whiskerRight e₂ R₂' ≫ Functor.whiskerLeft E₂ r₂) = η)
    (hκ : (Functor.whiskerRight r₁ E₁' ≫ Functor.whiskerLeft R₁ e₁) ≫ κ = κ')
    (hτ : τ' ≫ (Functor.whiskerRight e₁ E₂' ≫ Functor.whiskerLeft E₁ e₂) =
      (Functor.whiskerRight e₁ E₂' ≫ Functor.whiskerLeft E₁ e₂) ≫ τ) :
    (Functor.whiskerLeft (R₁' ⋙ E₁') η' ≫
        Functor.whiskerRight (Functor.whiskerLeft R₁' τ') R₂' ≫
          Functor.whiskerRight κ' (E₂' ⋙ R₂')) ≫
        (Functor.whiskerRight e₂ R₂' ≫ Functor.whiskerLeft E₂ r₂) =
      (Functor.whiskerRight r₁ E₁' ≫ Functor.whiskerLeft R₁ e₁) ≫
        (Functor.whiskerLeft (R₁ ⋙ E₁) η ≫
          Functor.whiskerRight (Functor.whiskerLeft R₁ τ) R₂ ≫
            Functor.whiskerRight κ (E₂ ⋙ R₂)) := by
  subst hκ hη
  ext Y
  have hτW := NatTrans.congr_app hτ (R₁'.obj Y)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.map_comp, Category.assoc] at hτW ⊢
  have core : τ'.app (R₁'.obj Y) ≫ E₂'.map (E₁'.map (r₁.app Y)) ≫ E₂'.map (e₁.app (R₁.obj Y)) ≫
      e₂.app (E₁.obj (R₁.obj Y)) =
      E₂'.map (E₁'.map (r₁.app Y)) ≫ E₂'.map (e₁.app (R₁.obj Y)) ≫ e₂.app (E₁.obj (R₁.obj Y)) ≫ τ.app (R₁.obj Y) := by
    have a : E₂'.map (E₁'.map (r₁.app Y)) ≫ E₂'.map (e₁.app (R₁.obj Y)) =
        E₂'.map (e₁.app (R₁'.obj Y)) ≫ E₂'.map (E₁.map (r₁.app Y)) := by
      rw [← E₂'.map_comp, ← E₂'.map_comp, e₁.naturality]
    have b := e₂.naturality (E₁.map (r₁.app Y))
    have c := τ.naturality (r₁.app Y)
    simp only [Functor.comp_obj, Functor.comp_map] at b c
    simp only [reassoc_of% a, reassoc_of% b, b, reassoc_of% hτW, c]
  have b' : R₂'.map (E₂'.map (κ.app Y)) ≫ R₂'.map (e₂.app Y) =
      R₂'.map (e₂.app (E₁.obj (R₁.obj Y))) ≫ R₂'.map (E₂.map (κ.app Y)) := by
    rw [← R₂'.map_comp, ← R₂'.map_comp]; exact congrArg R₂'.map (e₂.naturality (κ.app Y))
  have c := r₂.naturality (E₂.map (κ.app Y))
  have d := r₂.naturality (τ.app (R₁.obj Y))
  have n1 := η'.naturality (E₁'.map (r₁.app Y) ≫ e₁.app (R₁.obj Y))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
    Functor.map_comp, Category.assoc] at c d n1
  rw [reassoc_of% b', c, ← reassoc_of% d, reassoc_of% n1]
  simp only [← R₂'.map_comp_assoc]
  rw [core]

end Functor

section Bicat

universe w v u

variable {𝔅 : Type u} [Bicategory.{w, v} 𝔅] [∀ a b : 𝔅, Preadditive (a ⟶ b)]
  {a b c : 𝔅} {E₁ E₁' : a ⟶ b} {R₁ R₁' : b ⟶ a} {E₂ E₂' : b ⟶ c} {R₂ R₂' : c ⟶ b}

omit [∀ a b : 𝔅, Preadditive (a ⟶ b)] in
theorem capD_conj (e₁ : E₁' ⟶ E₁) (r₁ : R₁' ⟶ R₁) {κ : R₁ ≫ E₁ ⟶ 𝟙 b}
    {κ' : R₁' ≫ E₁' ⟶ 𝟙 b} (hκ : (r₁ ▷ E₁' ≫ R₁ ◁ e₁) ≫ κ = κ') {p : E₁ ⟶ E₁}
    {p' : E₁' ⟶ E₁'} (hp : p' ≫ e₁ = e₁ ≫ p) :
    R₁' ◁ p' ≫ κ' = (r₁ ▷ E₁' ≫ R₁ ◁ e₁) ≫ R₁ ◁ p ≫ κ := by
  rw [← hκ, Category.assoc, ← Category.assoc (R₁' ◁ p'), whisker_exchange, Category.assoc,
    ← whiskerLeft_comp_assoc, hp, whiskerLeft_comp_assoc]
  simp only [Category.assoc]

omit [∀ a b : 𝔅, Preadditive (a ⟶ b)] in
theorem cupD_conj (e₂ : E₂' ⟶ E₂) (r₂ : R₂' ⟶ R₂) {η : 𝟙 b ⟶ E₂ ≫ R₂}
    {η' : 𝟙 b ⟶ E₂' ≫ R₂'} (hη : η' ≫ (e₂ ▷ R₂' ≫ E₂ ◁ r₂) = η) {p : E₂ ⟶ E₂}
    {p' : E₂' ⟶ E₂'} (hp : p' ≫ e₂ = e₂ ≫ p) :
    (η' ≫ p' ▷ R₂') ≫ (e₂ ▷ R₂' ≫ E₂ ◁ r₂) = η ≫ p ▷ R₂ := by
  rw [← hη, Category.assoc, ← comp_whiskerRight_assoc, hp, comp_whiskerRight_assoc,
    ← whisker_exchange]
  simp only [Category.assoc]

theorem slide_conj (e₁ : E₁' ⟶ E₁) (e₂ : E₂' ⟶ E₂) {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
    {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {x₁' : E₁' ⟶ E₁'} {x₂' : E₂' ⟶ E₂'}
    {τ' : E₁' ≫ E₂' ⟶ E₁' ≫ E₂'} (hx₁ : x₁' ≫ e₁ = e₁ ≫ x₁) (hx₂ : x₂' ≫ e₂ = e₂ ≫ x₂)
    (hτ : τ' ≫ (e₁ ▷ E₂' ≫ E₁ ◁ e₂) = (e₁ ▷ E₂' ≫ E₁ ◁ e₂) ≫ τ) :
    (E₁' ◁ x₂' ≫ τ' - τ' ≫ x₁' ▷ E₂') ≫ (e₁ ▷ E₂' ≫ E₁ ◁ e₂) =
        (e₁ ▷ E₂' ≫ E₁ ◁ e₂) ≫ (E₁ ◁ x₂ ≫ τ - τ ≫ x₁ ▷ E₂) ∧
      (τ' ≫ E₁' ◁ x₂' - x₁' ▷ E₂' ≫ τ') ≫ (e₁ ▷ E₂' ≫ E₁ ◁ e₂) =
        (e₁ ▷ E₂' ≫ E₁ ◁ e₂) ≫ (τ ≫ E₁ ◁ x₂ - x₁ ▷ E₂ ≫ τ) := by
  have hl : E₁' ◁ x₂' ≫ (e₁ ▷ E₂' ≫ E₁ ◁ e₂) = (e₁ ▷ E₂' ≫ E₁ ◁ e₂) ≫ E₁ ◁ x₂ := by
    rw [← Category.assoc, whisker_exchange, Category.assoc, ← whiskerLeft_comp, hx₂,
      whiskerLeft_comp]
    simp only [Category.assoc]
  have hr : x₁' ▷ E₂' ≫ (e₁ ▷ E₂' ≫ E₁ ◁ e₂) = (e₁ ▷ E₂' ≫ E₁ ◁ e₂) ≫ x₁ ▷ E₂ := by
    rw [← comp_whiskerRight_assoc, hx₁, comp_whiskerRight_assoc, ← whisker_exchange]
    simp only [Category.assoc]
  generalize e₁ ▷ E₂' ≫ E₁ ◁ e₂ = φ at hl hr hτ ⊢
  have hc : ∀ {s t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {s' t' : E₁' ≫ E₂' ⟶ E₁' ≫ E₂'},
      s' ≫ φ = φ ≫ s → t' ≫ φ = φ ≫ t → (s' ≫ t') ≫ φ = φ ≫ (s ≫ t) := by
    intro s t s' t' h₁ h₂
    rw [Category.assoc, h₂, reassoc_of% h₁]
  constructor
  · rw [Preadditive.sub_comp, Preadditive.comp_sub, hc hl hτ, hc hτ hr]
  · rw [Preadditive.sub_comp, Preadditive.comp_sub, hc hτ hl, hc hr hτ]

/-- The boundary coefficients transported along isomorphisms of the 1-cells. -/
def RouqBoundary.Coefficients.transport [AdditiveWhiskering 𝔅] {E E' : a ⟶ b}
    {R R' : b ⟶ a} {A : E ⊣ R} {A' : E' ⊣ R'} {x : E ⟶ E} {x' : E' ⟶ E'} {n : ℕ}
    (D : RouqBoundary.Coefficients A x n) (e : E' ≅ E) (r : R' ≅ R)
    (hη : A'.unit ≫ (e.hom ▷ R' ≫ E ◁ r.hom) = A.unit) (hx : x' ≫ e.hom = e.hom ≫ x) :
    RouqBoundary.Coefficients A' x' n :=
  let ψ : E' ≫ R' ≅ E ≫ R := whiskerRightIso e R' ≪≫ whiskerLeftIso E r
  have hc (j : ℕ) : RouqBoundary.cupD A' x' j = RouqBoundary.cupD A x j ≫ ψ.inv := by
    rw [Iso.eq_comp_inv]
    exact cupD_conj e.hom r.hom hη (powComp_conj e hx j)
  { coeff := fun j => ψ.hom ≫ D.coeff j
    total := by
      have hs : ∑ j ∈ Finset.range n, D.coeff j ≫ RouqBoundary.cupD A x j ≫ ψ.inv =
          (∑ j ∈ Finset.range n, D.coeff j ≫ RouqBoundary.cupD A x j) ≫ ψ.inv := by
        rw [Preadditive.sum_comp]; simp only [Category.assoc]
      simp only [hc, Category.assoc]
      rw [← Preadditive.comp_sum, hs, D.total, Category.id_comp, Iso.hom_inv_id]
    entry := fun j l hj hl => by
      rw [hc, Category.assoc, Iso.inv_hom_id_assoc]
      exact D.entry j l hj hl }

end Bicat

namespace AdditiveCat

universe v u

variable {A B C : AdditiveCat.{v, u}}
  {E₁ E₁' : A ⟶ B} {R₁ R₁' : B ⟶ A} {E₂ E₂' : B ⟶ C} {R₂ R₂' : C ⟶ B}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {adj₁' : E₁' ⊣ R₁'} {adj₂' : E₂' ⊣ R₂'}

theorem sigma_conj (e₁ : E₁' ⟶ E₁) (e₂ : E₂' ⟶ E₂) (r₁ : R₁' ⟶ R₁) (r₂ : R₂' ⟶ R₂)
    {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {τ' : E₁' ≫ E₂' ⟶ E₁' ≫ E₂'}
    (hη : adj₂'.unit ≫ (e₂ ▷ R₂' ≫ E₂ ◁ r₂) = adj₂.unit)
    (hκ : (r₁ ▷ E₁' ≫ R₁ ◁ e₁) ≫ adj₁.counit = adj₁'.counit)
    (hτ : τ' ≫ (e₁ ▷ E₂' ≫ E₁ ◁ e₂) = (e₁ ▷ E₂' ≫ E₁ ◁ e₂) ≫ τ) :
    RightwardCrossing.sigma adj₂'.unit τ' adj₁'.counit ≫ (e₂ ▷ R₂' ≫ E₂ ◁ r₂) =
      (r₁ ▷ E₁' ≫ R₁ ◁ e₁) ≫ RightwardCrossing.sigma adj₂.unit τ adj₁.counit := by
  apply ObjectProperty.hom_ext
  have h := sigmaFunctor_conj adj₂.unit.hom τ.hom adj₁.counit.hom adj₂'.unit.hom τ'.hom
    adj₁'.counit.hom e₁.hom e₂.hom r₁.hom r₂.hom (congrArg (fun t => t.hom) hη)
    (congrArg (fun t => t.hom) hκ) (congrArg (fun t => t.hom) hτ)
  exact (congrArg (· ≫ (e₂ ▷ R₂' ≫ E₂ ◁ r₂).hom) (sigma_hom adj₂'.unit τ' adj₁'.counit)).trans
    (h.trans (congrArg ((r₁ ▷ E₁' ≫ R₁ ◁ e₁).hom ≫ ·)
      (sigma_hom adj₂.unit τ adj₁.counit).symm))

/-- **Transport of Rouquier's data at one weight** along isomorphisms `e₁ : E₁' ≅ E₁`,
`e₂ : E₂' ≅ E₂`, `r₁ : R₁' ≅ R₁`, `r₂ : R₂' ≅ R₂` that intertwine the unit of `adj₂`, the
counit of `adj₁`, the dots and the crossing. -/
def RouqLoc.transport {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}
    {x₁' : E₁' ⟶ E₁'} {x₂' : E₂' ⟶ E₂'} {τ' : E₁' ≫ E₂' ⟶ E₁' ≫ E₂'} {h : ℤ}
    (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) (e₁ : E₁' ≅ E₁) (e₂ : E₂' ≅ E₂) (r₁ : R₁' ≅ R₁)
    (r₂ : R₂' ≅ R₂) (hη : adj₂'.unit ≫ (e₂.hom ▷ R₂' ≫ E₂ ◁ r₂.hom) = adj₂.unit)
    (hκ : (r₁.hom ▷ E₁' ≫ R₁ ◁ e₁.hom) ≫ adj₁.counit = adj₁'.counit)
    (hx₁ : x₁' ≫ e₁.hom = e₁.hom ≫ x₁) (hx₂ : x₂' ≫ e₂.hom = e₂.hom ≫ x₂)
    (hτ : τ' ≫ (e₁.hom ▷ E₂' ≫ E₁ ◁ e₂.hom) = (e₁.hom ▷ E₂' ≫ E₁ ◁ e₂.hom) ≫ τ) :
    RouqLoc adj₁' adj₂' x₁' x₂' τ' h :=
  let φ : E₁' ≫ E₂' ≅ E₁ ≫ E₂ := whiskerRightIso e₁ E₂' ≪≫ whiskerLeftIso E₁ e₂
  let ψ₁ : R₁' ≫ E₁' ≅ R₁ ≫ E₁ := whiskerRightIso r₁ E₁' ≪≫ whiskerLeftIso R₁ e₁
  let ψ₂ : E₂' ≫ R₂' ≅ E₂ ≫ R₂ := whiskerRightIso e₂ R₂' ≪≫ whiskerLeftIso E₂ r₂
  have hs := slide_conj e₁.hom e₂.hom hx₁ hx₂ hτ
  have hσ := sigma_conj e₁.hom e₂.hom r₁.hom r₂.hom hη hκ hτ
  { slide_left := by
      rw [← cancel_mono φ.hom, Category.id_comp]
      simp only [φ, Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom]
      rw [hs.1, L.slide_left, Category.comp_id]
    slide_right := by
      rw [← cancel_mono φ.hom, Category.id_comp]
      simp only [φ, Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom]
      rw [hs.2, L.slide_right, Category.comp_id]
    invPos := fun hh => (L.invPos hh).conj ψ₁ ψ₂.symm (Iso.refl _)
      (by rw [Iso.symm_hom, ← Category.assoc, Iso.eq_comp_inv]; exact hσ)
      (fun m => by
        rw [Iso.refl_hom, Category.comp_id]
        exact capD_conj e₁.hom r₁.hom hκ (powComp_conj e₁ hx₁ m))
    invNeg := fun hh => (L.invNeg hh).conj ψ₂.symm ψ₁ (Iso.refl _)
      (by rw [Iso.symm_hom, ← Category.assoc, Iso.eq_comp_inv]; exact hσ)
      (fun m => by
        rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, Iso.eq_comp_inv]
        exact cupD_conj e₂.hom r₂.hom hη (powComp_conj e₂ hx₂ m)) }

end AdditiveCat

end Categorification.TwoRep
