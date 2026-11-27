/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterpAdmissible

/-!
# Sliding a cup or a cap through a strand, in normal form

Webster, arXiv:1309.3796v3, §4.5, proof of Theorem 4.25: the red/down crossings are the mates of
the red/up crossings, so a black cup or cap passes through a red strand. In the interpretation of
diagrams by generator images, a cup next to a strand followed by a crossing is a composite of two
whiskered generator images conjugated by images of free 2-morphisms. This file proves the equality
of the two composites of a cup (`cup_key`) and of a cap (`cap_key`) on either side of a strand,
as soon as the generator images, read through free isomorphisms, satisfy the corresponding mate
equation in the target bicategory.
-/

set_option backward.isDefEq.respectTransparency false

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams

variable {S : Signature} {C : Type*} [Bicategory C] (M : Model S C)

section Mates

variable {B : Type*} [Bicategory B] {c d e f : B} {g : c ⟶ e} {h : d ⟶ f} {l₁ : c ⟶ d}
  {r₁ : d ⟶ c} {l₂ : e ⟶ f} {r₂ : f ⟶ e} (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)

/-- **The unit form of the mate equation**: a cup on the left of `g` followed by `γ` equals a cup
on the right followed by the mate of `γ`. -/
theorem mateEquiv_unit (γ : g ≫ l₂ ⟶ l₁ ≫ h) :
    (ρ_ g).inv ≫ g ◁ adj₂.unit ≫ (α_ _ _ _).inv ≫ γ ▷ r₂ ≫ (α_ _ _ _).hom =
      (λ_ g).inv ≫ adj₁.unit ▷ g ≫ (α_ _ _ _).hom ≫ l₁ ◁ mateEquiv adj₁ adj₂ γ := by
  have h := (mateEquiv_eq_iff adj₁ adj₂ γ (mateEquiv adj₁ adj₂ γ)).mp rfl
  rw [Adjunction.homEquiv₁_symm_apply, Adjunction.homEquiv₂_apply] at h
  simpa only [Category.assoc] using h.symm

/-- **The counit form of the mate equation**: the mate of `γ` followed by a cap on the right of
`h` equals `γ` followed by a cap on the left. -/
theorem mateEquiv_counit (γ : g ≫ l₂ ⟶ l₁ ≫ h) :
    (α_ _ _ _).inv ≫ mateEquiv adj₁ adj₂ γ ▷ l₂ ≫ (α_ _ _ _).hom ≫ h ◁ adj₂.counit ≫
        (ρ_ h).hom =
      r₁ ◁ γ ≫ (α_ _ _ _).inv ≫ adj₁.counit ▷ h ≫ (λ_ h).hom := by
  rw [mateEquiv_apply']
  calc _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ adj₂.unit ▷ l₂ ⊗≫ r₁ ◁ γ ▷ r₂ ▷ l₂ ⊗≫
          ((adj₁.counit ▷ h) ▷ (r₂ ≫ l₂) ≫ (𝟙 _ ≫ h) ◁ adj₂.counit) ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ adj₂.unit ▷ l₂ ⊗≫ r₁ ◁ γ ▷ r₂ ▷ l₂ ⊗≫
          (((r₁ ≫ l₁) ≫ h) ◁ adj₂.counit ≫ (adj₁.counit ▷ h) ▷ 𝟙 _) ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ adj₂.unit ▷ l₂ ⊗≫
          r₁ ◁ (γ ▷ (r₂ ≫ l₂) ≫ (l₁ ≫ h) ◁ adj₂.counit) ⊗≫ adj₁.counit ▷ h ⊗≫ 𝟙 _ := by
        bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ adj₂.unit ▷ l₂ ⊗≫
          r₁ ◁ ((g ≫ l₂) ◁ adj₂.counit ≫ γ ▷ 𝟙 _) ⊗≫ adj₁.counit ▷ h ⊗≫ 𝟙 _ := by
        rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ leftZigzag adj₂.unit adj₂.counit ⊗≫ r₁ ◁ γ ⊗≫
          adj₁.counit ▷ h ⊗≫ 𝟙 _ := by
        bicategory
    _ = _ := by
        rw [adj₂.left_triangle]
        bicategory

end Mates

section Pair

/-- **The image of a two-layer chain** as two layer images between transports of free
1-morphisms, each transport going from the word reached so far to the boundary word of the next
layer. -/
theorem admissibleChain_pair (G : GenImg M) {s t : S.Region} {a b : Obj S} (L₁ L₂ : Layer S)
    (h : Chain a [L₁, L₂] b) (ha : Cond s t a) (hb : Cond s t b) :
    admissibleChain G a [L₁, L₂] b h ha hb =
      M.lift.map₂ (eqToHom (fw_eq (congrArg Obj.word h.2.1.symm) ha.1 ha.2.1
          (h.2.1 ▸ ha).1 (h.2.1 ▸ ha).2.1)) ≫
        coreC G h.1 (h.2.1 ▸ ha) ≫
        M.lift.map₂ (eqToHom (fw_eq (congrArg Obj.word h.2.2.2.1.symm)
          ((h.2.1 ▸ ha).cod h.1).1 ((h.2.1 ▸ ha).cod h.1).2.1
          (h.2.2.2.1 ▸ (h.2.1 ▸ ha).cod h.1).1 (h.2.2.2.1 ▸ (h.2.1 ▸ ha).cod h.1).2.1)) ≫
        coreC G h.2.2.1 (h.2.2.2.1 ▸ (h.2.1 ▸ ha).cod h.1) ≫
        M.lift.map₂ (eqToHom (fw_eq (congrArg Obj.word h.2.2.2.2)
          ((h.2.2.2.1 ▸ (h.2.1 ▸ ha).cod h.1).cod h.2.2.1).1
          ((h.2.2.2.1 ▸ (h.2.1 ▸ ha).cod h.1).cod h.2.2.1).2.1 hb.1 hb.2.1)) := by
  simp only [admissibleChain]
  rw [eqToHom_lift _ _, eqToHom_lift _ _, eqToHom_lift _ _]

end Pair

section Key

variable {a₀ a₁ a₂ a₃ : FB S}

/-- A 2-morphism between images of free 1-morphisms, read through free isomorphisms. -/
theorem conj_free {a b : FB S} {f f' g g' : a ⟶ b} (σ : f ≅ f') (τ : g ≅ g')
    (k : M.lift.map f ⟶ M.lift.map g) :
    k = M.lift.map₂ σ.hom ≫ (M.lift.map₂ σ.inv ≫ k ≫ M.lift.map₂ τ.hom) ≫
      M.lift.map₂ τ.inv := by
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp, Iso.hom_inv_id, PrelaxFunctor.map₂_id,
    Category.comp_id]
  rw [← PrelaxFunctor.map₂_comp_assoc, Iso.hom_inv_id, PrelaxFunctor.map₂_id, Category.id_comp]

/-- The normal form of `cup_key`, with arbitrary free 2-morphisms between the two steps. -/
theorem cup_nf {x : a₀ ⟶ a₁} {dn : a₁ ⟶ a₂} {up : a₂ ⟶ a₁} {dn' : a₀ ⟶ a₃} {x' : a₃ ⟶ a₂}
    {up' : a₃ ⟶ a₀} {P Q : a₀ ⟶ a₁}
    (F₀ : P ⟶ x ≫ (𝟙 a₁ ≫ 𝟙 a₁)) (F₁ : x ≫ ((dn ≫ up) ≫ 𝟙 a₁) ⟶ 𝟙 a₀ ≫ ((x ≫ dn) ≫ up))
    (F₂ : 𝟙 a₀ ≫ ((dn' ≫ x') ≫ up) ⟶ Q)
    (G₀ : P ⟶ 𝟙 a₀ ≫ (𝟙 a₀ ≫ x)) (G₁ : 𝟙 a₀ ≫ ((dn' ≫ up') ≫ x) ⟶ dn' ≫ ((up' ≫ x) ≫ 𝟙 a₁))
    (G₂ : dn' ≫ ((x' ≫ up) ≫ 𝟙 a₁) ⟶ Q)
    (η₁ : 𝟙 _ ⟶ M.lift.map dn ≫ M.lift.map up)
    (γ : M.lift.map x ≫ M.lift.map dn ⟶ M.lift.map dn' ≫ M.lift.map x')
    (η₃ : 𝟙 _ ⟶ M.lift.map dn' ≫ M.lift.map up')
    (β : M.lift.map up' ≫ M.lift.map x ⟶ M.lift.map x' ≫ M.lift.map up)
    (hmate : (ρ_ _).inv ≫ M.lift.map x ◁ η₁ ≫ (α_ _ _ _).inv ≫ γ ▷ M.lift.map up ≫
        (α_ _ _ _).hom =
      (λ_ _).inv ≫ η₃ ▷ M.lift.map x ≫ (α_ _ _ _).hom ≫ M.lift.map dn' ◁ β) :
    M.lift.map₂ F₀ ≫ midK M x (𝟙 a₁) (x := 𝟙 a₁) (y := dn ≫ up) η₁ ≫ M.lift.map₂ F₁ ≫
        midK M (𝟙 a₀) up (x := x ≫ dn) (y := dn' ≫ x') γ ≫ M.lift.map₂ F₂ =
      M.lift.map₂ G₀ ≫ midK M (𝟙 a₀) x (x := 𝟙 a₀) (y := dn' ≫ up') η₃ ≫ M.lift.map₂ G₁ ≫
        midK M dn' (𝟙 a₁) (x := up' ≫ x) (y := x' ≫ up) β ≫ M.lift.map₂ G₂ := by
  let N₀ : x ⟶ x ≫ (𝟙 a₁ ≫ 𝟙 a₁) := (ρ_ x).inv ≫ x ◁ (λ_ _).inv
  let N₀' : x ⟶ 𝟙 a₀ ≫ (𝟙 a₀ ≫ x) := (λ_ x).inv ≫ 𝟙 a₀ ◁ (λ_ x).inv
  let N₂ : 𝟙 a₀ ≫ ((dn' ≫ x') ≫ up) ⟶ dn' ≫ (x' ≫ up) := (λ_ _).hom ≫ (α_ _ _ _).hom
  let N₂' : dn' ≫ ((x' ≫ up) ≫ 𝟙 a₁) ⟶ dn' ≫ (x' ≫ up) := dn' ◁ (ρ_ _).hom
  let θ : P ⟶ x := F₀ ≫ x ◁ (λ_ _).hom ≫ (ρ_ x).hom
  let θ' : dn' ≫ (x' ≫ up) ⟶ Q := (α_ _ _ _).inv ≫ (λ_ _).inv ≫ F₂
  have e₀ : M.lift.map₂ F₀ = M.lift.map₂ θ ≫ M.lift.map₂ N₀ := by
    rw [← PrelaxFunctor.map₂_comp]; exact lift_map₂_eq M _ _
  have e₀' : M.lift.map₂ G₀ = M.lift.map₂ θ ≫ M.lift.map₂ N₀' := by
    rw [← PrelaxFunctor.map₂_comp]; exact lift_map₂_eq M _ _
  have e₂ : M.lift.map₂ F₂ = M.lift.map₂ N₂ ≫ M.lift.map₂ θ' := by
    rw [← PrelaxFunctor.map₂_comp]; exact lift_map₂_eq M _ _
  have e₂' : M.lift.map₂ G₂ = M.lift.map₂ N₂' ≫ M.lift.map₂ θ' := by
    rw [← PrelaxFunctor.map₂_comp]; exact lift_map₂_eq M _ _
  have e₁ : M.lift.map₂ F₁ = M.lift.map₂ (x ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv) :=
    lift_map₂_eq M _ _
  have e₁' : M.lift.map₂ G₁ =
      M.lift.map₂ ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ dn' ◁ (ρ_ _).inv) :=
    lift_map₂_eq M _ _
  have key : M.lift.map₂ N₀ ≫ midK M x (𝟙 a₁) (x := 𝟙 a₁) (y := dn ≫ up) η₁ ≫
        M.lift.map₂ (x ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv) ≫
        midK M (𝟙 a₀) up (x := x ≫ dn) (y := dn' ≫ x') γ ≫ M.lift.map₂ N₂ =
      M.lift.map₂ N₀' ≫ midK M (𝟙 a₀) x (x := 𝟙 a₀) (y := dn' ≫ up') η₃ ≫
        M.lift.map₂ ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ dn' ◁ (ρ_ _).inv) ≫
        midK M dn' (𝟙 a₁) (x := up' ≫ x) (y := x' ≫ up) β ≫ M.lift.map₂ N₂' := by
    simp only [N₀, N₀', N₂, N₂', midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft,
      lift_map₂_associator_hom, lift_map₂_associator_inv, lift_map₂_leftUnitor_hom,
      lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_hom, lift_map₂_rightUnitor_inv,
      lift_map_comp]
    calc _ = 𝟙 _ ⊗≫ ((ρ_ _).inv ≫ M.lift.map x ◁ η₁ ≫ (α_ _ _ _).inv ≫ γ ▷ M.lift.map up ≫
          (α_ _ _ _).hom) ⊗≫ 𝟙 _ := by bicategory
      _ = 𝟙 _ ⊗≫ ((λ_ _).inv ≫ η₃ ▷ M.lift.map x ≫ (α_ _ _ _).hom ≫ M.lift.map dn' ◁ β) ⊗≫
          𝟙 _ := by rw [hmate]
      _ = _ := by bicategory
  rw [e₀, e₀', e₁, e₁', e₂, e₂']
  simp only [Category.assoc]
  rw [reassoc_of% key]

/-- **A cup passes through a strand.** The left side places a cup `η₁` (from `𝟙 a₁` to `dn ≫ up`)
to the left of the strand `x`, then crosses `x` with `dn` by `γ`; the right side places a cup `η₃`
(from `𝟙 a₀` to `dn' ≫ up'`) to the right of `x`, then crosses `up'` with `x` by `β`. The two
composites agree if `γ` and `β` satisfy the unit form of the mate equation. -/
theorem cup_key {x : a₀ ⟶ a₁} {dn : a₁ ⟶ a₂} {up : a₂ ⟶ a₁} {dn' : a₀ ⟶ a₃} {x' : a₃ ⟶ a₂}
    {up' : a₃ ⟶ a₀}
    {p₁ : a₀ ⟶ a₁} {q₁ d₁ c₁ : a₁ ⟶ a₁} {p₂ : a₀ ⟶ a₀} {q₂ : a₂ ⟶ a₁} {d₂ c₂ : a₀ ⟶ a₂}
    {p₃ d₃ c₃ : a₀ ⟶ a₀} {q₃ : a₀ ⟶ a₁} {p₄ : a₀ ⟶ a₃} {q₄ : a₁ ⟶ a₁} {d₄ c₄ : a₃ ⟶ a₁}
    (σp₁ : p₁ ≅ x) (σq₁ : q₁ ≅ 𝟙 a₁) (σd₁ : d₁ ≅ 𝟙 a₁) (σc₁ : c₁ ≅ dn ≫ up)
    (σp₂ : p₂ ≅ 𝟙 a₀) (σq₂ : q₂ ≅ up) (σd₂ : d₂ ≅ x ≫ dn) (σc₂ : c₂ ≅ dn' ≫ x')
    (σp₃ : p₃ ≅ 𝟙 a₀) (σq₃ : q₃ ≅ x) (σd₃ : d₃ ≅ 𝟙 a₀) (σc₃ : c₃ ≅ dn' ≫ up')
    (σp₄ : p₄ ≅ dn') (σq₄ : q₄ ≅ 𝟙 a₁) (σd₄ : d₄ ≅ up' ≫ x) (σc₄ : c₄ ≅ x' ≫ up)
    (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁) (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (g₃ : M.lift.map d₃ ⟶ M.lift.map c₃) (g₄ : M.lift.map d₄ ⟶ M.lift.map c₄)
    (hmate : (ρ_ _).inv ≫ M.lift.map x ◁
        (M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom : 𝟙 _ ⟶ M.lift.map dn ≫ M.lift.map up) ≫
        (α_ _ _ _).inv ≫
        (M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom :
          M.lift.map x ≫ M.lift.map dn ⟶ M.lift.map dn' ≫ M.lift.map x') ▷ M.lift.map up ≫
        (α_ _ _ _).hom =
      (λ_ _).inv ≫
        (M.lift.map₂ σd₃.inv ≫ g₃ ≫ M.lift.map₂ σc₃.hom :
          𝟙 _ ⟶ M.lift.map dn' ≫ M.lift.map up') ▷ M.lift.map x ≫ (α_ _ _ _).hom ≫
        M.lift.map dn' ◁ (M.lift.map₂ σd₄.inv ≫ g₄ ≫ M.lift.map₂ σc₄.hom :
          M.lift.map up' ≫ M.lift.map x ⟶ M.lift.map x' ≫ M.lift.map up))
    {P P₁ Q₁ P₂ Q₂ P₃ Q₃ P₄ Q₄ Q : a₀ ⟶ a₁}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ Q)
    (E₃ : P ⟶ P₃) (A₃ : P₃ ⟶ p₃ ≫ (d₃ ≫ q₃)) (B₃ : p₃ ≫ (c₃ ≫ q₃) ⟶ Q₃) (E₄ : Q₃ ⟶ P₄)
    (A₄ : P₄ ⟶ p₄ ≫ (d₄ ≫ q₄)) (B₄ : p₄ ≫ (c₄ ≫ q₄) ⟶ Q₄) (E₅ : Q₄ ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ =
      M.lift.map₂ E₃ ≫ (M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₄ ≫
        (M.lift.map₂ A₄ ≫ midK M p₄ q₄ g₄ ≫ M.lift.map₂ B₄) ≫ M.lift.map₂ E₅ := by
  obtain ⟨η₁, rfl⟩ : ∃ η, g₁ = M.lift.map₂ σd₁.hom ≫ η ≫ M.lift.map₂ σc₁.inv :=
    ⟨_, conj_free M σd₁ σc₁ g₁⟩
  obtain ⟨η₂, rfl⟩ : ∃ η, g₂ = M.lift.map₂ σd₂.hom ≫ η ≫ M.lift.map₂ σc₂.inv :=
    ⟨_, conj_free M σd₂ σc₂ g₂⟩
  obtain ⟨η₃, rfl⟩ : ∃ η, g₃ = M.lift.map₂ σd₃.hom ≫ η ≫ M.lift.map₂ σc₃.inv :=
    ⟨_, conj_free M σd₃ σc₃ g₃⟩
  obtain ⟨η₄, rfl⟩ : ∃ η, g₄ = M.lift.map₂ σd₄.hom ≫ η ≫ M.lift.map₂ σc₄.inv :=
    ⟨_, conj_free M σd₄ σc₄ g₄⟩
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp,
    Iso.inv_hom_id, PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id] at hmate
  rw [mid_comp M, mid_comp M, mid_comp M, mid_comp M,
    mid_conj M σp₁ σq₁, mid_conj M σp₂ σq₂, mid_conj M σp₃ σq₃, mid_conj M σp₄ σq₄]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  exact cup_nf M _ _ _ _ _ _ _ _ _ _ hmate

/-- `cup_key` for layers whose splitting regions and pieces agree with the canonical ones only up
to equality: the regions are equal, the pieces and the generator images are heterogeneously
equal to the canonical ones. -/
theorem cup_key_heq {x : a₀ ⟶ a₁} {dn : a₁ ⟶ a₂} {up : a₂ ⟶ a₁} {dn' : a₀ ⟶ a₃}
    {x' : a₃ ⟶ a₂} {up' : a₃ ⟶ a₀}
    {n₁ m₁ n₂ m₂ n₃ m₃ n₄ m₄ : FB S}
    {p₁ : a₀ ⟶ n₁} {q₁ : m₁ ⟶ a₁} {d₁ c₁ : n₁ ⟶ m₁} {p₂ : a₀ ⟶ n₂} {q₂ : m₂ ⟶ a₁}
    {d₂ c₂ : n₂ ⟶ m₂} {p₃ : a₀ ⟶ n₃} {q₃ : m₃ ⟶ a₁} {d₃ c₃ : n₃ ⟶ m₃} {p₄ : a₀ ⟶ n₄}
    {q₄ : m₄ ⟶ a₁} {d₄ c₄ : n₄ ⟶ m₄}
    (hn₁ : n₁ = a₁) (hm₁ : m₁ = a₁) (hn₂ : n₂ = a₀) (hm₂ : m₂ = a₂)
    (hn₃ : n₃ = a₀) (hm₃ : m₃ = a₀) (hn₄ : n₄ = a₃) (hm₄ : m₄ = a₁)
    (hp₁ : p₁ ≍ x) (hq₁ : q₁ ≍ 𝟙 a₁) (hd₁ : d₁ ≍ 𝟙 a₁) (hc₁ : c₁ ≍ dn ≫ up)
    (hp₂ : p₂ ≍ 𝟙 a₀) (hq₂ : q₂ ≍ up) (hd₂ : d₂ ≍ x ≫ dn) (hc₂ : c₂ ≍ dn' ≫ x')
    (hp₃ : p₃ ≍ 𝟙 a₀) (hq₃ : q₃ ≍ x) (hd₃ : d₃ ≍ 𝟙 a₀) (hc₃ : c₃ ≍ dn' ≫ up')
    (hp₄ : p₄ ≍ dn') (hq₄ : q₄ ≍ 𝟙 a₁) (hd₄ : d₄ ≍ up' ≫ x) (hc₄ : c₄ ≍ x' ≫ up)
    (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁) (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (g₃ : M.lift.map d₃ ⟶ M.lift.map c₃) (g₄ : M.lift.map d₄ ⟶ M.lift.map c₄)
    (γ₁ : 𝟙 (M.obj a₁) ⟶ M.lift.map dn ≫ M.lift.map up)
    (γ₂ : M.lift.map x ≫ M.lift.map dn ⟶ M.lift.map dn' ≫ M.lift.map x')
    (γ₃ : 𝟙 (M.obj a₀) ⟶ M.lift.map dn' ≫ M.lift.map up')
    (γ₄ : M.lift.map up' ≫ M.lift.map x ⟶ M.lift.map x' ≫ M.lift.map up)
    (hg₁ : g₁ ≍ γ₁) (hg₂ : g₂ ≍ γ₂) (hg₃ : g₃ ≍ γ₃) (hg₄ : g₄ ≍ γ₄)
    (hmate : (ρ_ _).inv ≫ M.lift.map x ◁ γ₁ ≫ (α_ _ _ _).inv ≫ γ₂ ▷ M.lift.map up ≫
        (α_ _ _ _).hom = (λ_ _).inv ≫ γ₃ ▷ M.lift.map x ≫ (α_ _ _ _).hom ≫
        M.lift.map dn' ◁ γ₄)
    {P P₁ Q₁ P₂ Q₂ P₃ Q₃ P₄ Q₄ Q : a₀ ⟶ a₁}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ Q)
    (E₃ : P ⟶ P₃) (A₃ : P₃ ⟶ p₃ ≫ (d₃ ≫ q₃)) (B₃ : p₃ ≫ (c₃ ≫ q₃) ⟶ Q₃) (E₄ : Q₃ ⟶ P₄)
    (A₄ : P₄ ⟶ p₄ ≫ (d₄ ≫ q₄)) (B₄ : p₄ ≫ (c₄ ≫ q₄) ⟶ Q₄) (E₅ : Q₄ ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ =
      M.lift.map₂ E₃ ≫ (M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₄ ≫
        (M.lift.map₂ A₄ ≫ midK M p₄ q₄ g₄ ≫ M.lift.map₂ B₄) ≫ M.lift.map₂ E₅ := by
  subst hn₁ hm₁ hn₂ hm₂ hn₃ hm₃ hn₄ hm₄
  obtain rfl := eq_of_heq hp₁; obtain rfl := eq_of_heq hq₁; obtain rfl := eq_of_heq hd₁
  obtain rfl := eq_of_heq hc₁; obtain rfl := eq_of_heq hp₂; obtain rfl := eq_of_heq hq₂
  obtain rfl := eq_of_heq hd₂; obtain rfl := eq_of_heq hc₂; obtain rfl := eq_of_heq hp₃
  obtain rfl := eq_of_heq hq₃; obtain rfl := eq_of_heq hd₃; obtain rfl := eq_of_heq hc₃
  obtain rfl := eq_of_heq hp₄; obtain rfl := eq_of_heq hq₄; obtain rfl := eq_of_heq hd₄
  obtain rfl := eq_of_heq hc₄
  obtain rfl := eq_of_heq hg₁; obtain rfl := eq_of_heq hg₂; obtain rfl := eq_of_heq hg₃
  obtain rfl := eq_of_heq hg₄
  refine cup_key M (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) g₁ g₂ g₃ g₄ ?_ _ _ _ _ _ _ _ _ _ _ _ _
    _ _
  simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.comp_id]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]
  exact hmate

/-- The normal form of `cap_key`, with arbitrary free 2-morphisms between the two steps. -/
theorem cap_nf {x : a₀ ⟶ a₁} {up : a₁ ⟶ a₂} {dn : a₂ ⟶ a₁} {x' : a₃ ⟶ a₂} {up' : a₀ ⟶ a₃}
    {dn' : a₃ ⟶ a₀} {P Q : a₀ ⟶ a₁}
    (F₀ : P ⟶ 𝟙 a₀ ≫ ((up' ≫ x') ≫ dn)) (F₁ : 𝟙 a₀ ≫ ((x ≫ up) ≫ dn) ⟶ x ≫ ((up ≫ dn) ≫ 𝟙 a₁))
    (F₂ : x ≫ (𝟙 a₁ ≫ 𝟙 a₁) ⟶ Q)
    (G₀ : P ⟶ up' ≫ ((x' ≫ dn) ≫ 𝟙 a₁)) (G₁ : up' ≫ ((dn' ≫ x) ≫ 𝟙 a₁) ⟶ 𝟙 a₀ ≫ ((up' ≫ dn') ≫ x))
    (G₂ : 𝟙 a₀ ≫ (𝟙 a₀ ≫ x) ⟶ Q)
    (β : M.lift.map up' ≫ M.lift.map x' ⟶ M.lift.map x ≫ M.lift.map up)
    (ε₁ : M.lift.map up ≫ M.lift.map dn ⟶ 𝟙 _)
    (γ : M.lift.map x' ≫ M.lift.map dn ⟶ M.lift.map dn' ≫ M.lift.map x)
    (ε₂ : M.lift.map up' ≫ M.lift.map dn' ⟶ 𝟙 _)
    (hmate : (α_ _ _ _).inv ≫ β ▷ M.lift.map dn ≫ (α_ _ _ _).hom ≫ M.lift.map x ◁ ε₁ ≫
        (ρ_ _).hom =
      M.lift.map up' ◁ γ ≫ (α_ _ _ _).inv ≫ ε₂ ▷ M.lift.map x ≫ (λ_ _).hom) :
    M.lift.map₂ F₀ ≫ midK M (𝟙 a₀) dn (x := up' ≫ x') (y := x ≫ up) β ≫ M.lift.map₂ F₁ ≫
        midK M x (𝟙 a₁) (x := up ≫ dn) (y := 𝟙 a₁) ε₁ ≫ M.lift.map₂ F₂ =
      M.lift.map₂ G₀ ≫ midK M up' (𝟙 a₁) (x := x' ≫ dn) (y := dn' ≫ x) γ ≫ M.lift.map₂ G₁ ≫
        midK M (𝟙 a₀) x (x := up' ≫ dn') (y := 𝟙 a₀) ε₂ ≫ M.lift.map₂ G₂ := by
  let N₀ : up' ≫ (x' ≫ dn) ⟶ 𝟙 a₀ ≫ ((up' ≫ x') ≫ dn) := (α_ _ _ _).inv ≫ (λ_ _).inv
  let N₀' : up' ≫ (x' ≫ dn) ⟶ up' ≫ ((x' ≫ dn) ≫ 𝟙 a₁) := up' ◁ (ρ_ _).inv
  let N₂ : x ≫ (𝟙 a₁ ≫ 𝟙 a₁) ⟶ x := x ◁ (λ_ _).hom ≫ (ρ_ x).hom
  let N₂' : 𝟙 a₀ ≫ (𝟙 a₀ ≫ x) ⟶ x := 𝟙 a₀ ◁ (λ_ x).hom ≫ (λ_ x).hom
  let θ : P ⟶ up' ≫ (x' ≫ dn) := F₀ ≫ (λ_ _).hom ≫ (α_ _ _ _).hom
  let θ' : x ⟶ Q := (ρ_ x).inv ≫ x ◁ (λ_ _).inv ≫ F₂
  have e₀ : M.lift.map₂ F₀ = M.lift.map₂ θ ≫ M.lift.map₂ N₀ := by
    rw [← PrelaxFunctor.map₂_comp]; exact lift_map₂_eq M _ _
  have e₀' : M.lift.map₂ G₀ = M.lift.map₂ θ ≫ M.lift.map₂ N₀' := by
    rw [← PrelaxFunctor.map₂_comp]; exact lift_map₂_eq M _ _
  have e₂ : M.lift.map₂ F₂ = M.lift.map₂ N₂ ≫ M.lift.map₂ θ' := by
    rw [← PrelaxFunctor.map₂_comp]; exact lift_map₂_eq M _ _
  have e₂' : M.lift.map₂ G₂ = M.lift.map₂ N₂' ≫ M.lift.map₂ θ' := by
    rw [← PrelaxFunctor.map₂_comp]; exact lift_map₂_eq M _ _
  have e₁ : M.lift.map₂ F₁ = M.lift.map₂ ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ x ◁ (ρ_ _).inv) :=
    lift_map₂_eq M _ _
  have e₁' : M.lift.map₂ G₁ =
      M.lift.map₂ (up' ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv) :=
    lift_map₂_eq M _ _
  have key : M.lift.map₂ N₀ ≫ midK M (𝟙 a₀) dn (x := up' ≫ x') (y := x ≫ up) β ≫
        M.lift.map₂ ((λ_ _).hom ≫ (α_ _ _ _).hom ≫ x ◁ (ρ_ _).inv) ≫
        midK M x (𝟙 a₁) (x := up ≫ dn) (y := 𝟙 a₁) ε₁ ≫ M.lift.map₂ N₂ =
      M.lift.map₂ N₀' ≫ midK M up' (𝟙 a₁) (x := x' ≫ dn) (y := dn' ≫ x) γ ≫
        M.lift.map₂ (up' ◁ (ρ_ _).hom ≫ (α_ _ _ _).inv ≫ (λ_ _).inv) ≫
        midK M (𝟙 a₀) x (x := up' ≫ dn') (y := 𝟙 a₀) ε₂ ≫ M.lift.map₂ N₂' := by
    simp only [N₀, N₀', N₂, N₂', midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft,
      lift_map₂_associator_hom, lift_map₂_associator_inv, lift_map₂_leftUnitor_hom,
      lift_map₂_leftUnitor_inv, lift_map₂_rightUnitor_hom, lift_map₂_rightUnitor_inv,
      lift_map_comp]
    calc _ = 𝟙 _ ⊗≫ ((α_ _ _ _).inv ≫ β ▷ M.lift.map dn ≫ (α_ _ _ _).hom ≫
          M.lift.map x ◁ ε₁ ≫ (ρ_ _).hom) ⊗≫ 𝟙 _ := by bicategory
      _ = 𝟙 _ ⊗≫ (M.lift.map up' ◁ γ ≫ (α_ _ _ _).inv ≫ ε₂ ▷ M.lift.map x ≫ (λ_ _).hom) ⊗≫
          𝟙 _ := by rw [hmate]
      _ = _ := by bicategory
  rw [e₀, e₀', e₁, e₁', e₂, e₂']
  simp only [Category.assoc]
  rw [reassoc_of% key]

/-- **A cap passes through a strand.** The left side crosses the strand `x'` with `up'` by `β`
and then closes `up ≫ dn` by the cap `ε₁` to the right of `x`; the right side crosses `dn` with
`x'` by `γ` and then closes `up' ≫ dn'` by the cap `ε₂` to the left of `x`. The two composites
agree if `β` and `γ` satisfy the counit form of the mate equation. -/
theorem cap_key {x : a₀ ⟶ a₁} {up : a₁ ⟶ a₂} {dn : a₂ ⟶ a₁} {x' : a₃ ⟶ a₂} {up' : a₀ ⟶ a₃}
    {dn' : a₃ ⟶ a₀}
    {p₁ : a₀ ⟶ a₀} {q₁ : a₂ ⟶ a₁} {d₁ c₁ : a₀ ⟶ a₂} {p₂ : a₀ ⟶ a₁} {q₂ d₂ c₂ : a₁ ⟶ a₁}
    {p₃ : a₀ ⟶ a₃} {q₃ : a₁ ⟶ a₁} {d₃ c₃ : a₃ ⟶ a₁} {p₄ d₄ c₄ : a₀ ⟶ a₀} {q₄ : a₀ ⟶ a₁}
    (σp₁ : p₁ ≅ 𝟙 a₀) (σq₁ : q₁ ≅ dn) (σd₁ : d₁ ≅ up' ≫ x') (σc₁ : c₁ ≅ x ≫ up)
    (σp₂ : p₂ ≅ x) (σq₂ : q₂ ≅ 𝟙 a₁) (σd₂ : d₂ ≅ up ≫ dn) (σc₂ : c₂ ≅ 𝟙 a₁)
    (σp₃ : p₃ ≅ up') (σq₃ : q₃ ≅ 𝟙 a₁) (σd₃ : d₃ ≅ x' ≫ dn) (σc₃ : c₃ ≅ dn' ≫ x)
    (σp₄ : p₄ ≅ 𝟙 a₀) (σq₄ : q₄ ≅ x) (σd₄ : d₄ ≅ up' ≫ dn') (σc₄ : c₄ ≅ 𝟙 a₀)
    (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁) (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (g₃ : M.lift.map d₃ ⟶ M.lift.map c₃) (g₄ : M.lift.map d₄ ⟶ M.lift.map c₄)
    (hmate : (α_ _ _ _).inv ≫
        (M.lift.map₂ σd₁.inv ≫ g₁ ≫ M.lift.map₂ σc₁.hom :
          M.lift.map up' ≫ M.lift.map x' ⟶ M.lift.map x ≫ M.lift.map up) ▷ M.lift.map dn ≫
        (α_ _ _ _).hom ≫ M.lift.map x ◁
        (M.lift.map₂ σd₂.inv ≫ g₂ ≫ M.lift.map₂ σc₂.hom :
          M.lift.map up ≫ M.lift.map dn ⟶ 𝟙 _) ≫ (ρ_ _).hom =
      M.lift.map up' ◁ (M.lift.map₂ σd₃.inv ≫ g₃ ≫ M.lift.map₂ σc₃.hom :
          M.lift.map x' ≫ M.lift.map dn ⟶ M.lift.map dn' ≫ M.lift.map x) ≫ (α_ _ _ _).inv ≫
        (M.lift.map₂ σd₄.inv ≫ g₄ ≫ M.lift.map₂ σc₄.hom :
          M.lift.map up' ≫ M.lift.map dn' ⟶ 𝟙 _) ▷ M.lift.map x ≫ (λ_ _).hom)
    {P P₁ Q₁ P₂ Q₂ P₃ Q₃ P₄ Q₄ Q : a₀ ⟶ a₁}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ Q)
    (E₃ : P ⟶ P₃) (A₃ : P₃ ⟶ p₃ ≫ (d₃ ≫ q₃)) (B₃ : p₃ ≫ (c₃ ≫ q₃) ⟶ Q₃) (E₄ : Q₃ ⟶ P₄)
    (A₄ : P₄ ⟶ p₄ ≫ (d₄ ≫ q₄)) (B₄ : p₄ ≫ (c₄ ≫ q₄) ⟶ Q₄) (E₅ : Q₄ ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ =
      M.lift.map₂ E₃ ≫ (M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₄ ≫
        (M.lift.map₂ A₄ ≫ midK M p₄ q₄ g₄ ≫ M.lift.map₂ B₄) ≫ M.lift.map₂ E₅ := by
  obtain ⟨η₁, rfl⟩ : ∃ η, g₁ = M.lift.map₂ σd₁.hom ≫ η ≫ M.lift.map₂ σc₁.inv :=
    ⟨_, conj_free M σd₁ σc₁ g₁⟩
  obtain ⟨η₂, rfl⟩ : ∃ η, g₂ = M.lift.map₂ σd₂.hom ≫ η ≫ M.lift.map₂ σc₂.inv :=
    ⟨_, conj_free M σd₂ σc₂ g₂⟩
  obtain ⟨η₃, rfl⟩ : ∃ η, g₃ = M.lift.map₂ σd₃.hom ≫ η ≫ M.lift.map₂ σc₃.inv :=
    ⟨_, conj_free M σd₃ σc₃ g₃⟩
  obtain ⟨η₄, rfl⟩ : ∃ η, g₄ = M.lift.map₂ σd₄.hom ≫ η ≫ M.lift.map₂ σc₄.inv :=
    ⟨_, conj_free M σd₄ σc₄ g₄⟩
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp,
    Iso.inv_hom_id, PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id] at hmate
  rw [mid_comp M, mid_comp M, mid_comp M, mid_comp M,
    mid_conj M σp₁ σq₁, mid_conj M σp₂ σq₂, mid_conj M σp₃ σq₃, mid_conj M σp₄ σq₄]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  exact cap_nf M _ _ _ _ _ _ _ _ _ _ hmate

/-- `cap_key` for layers whose splitting regions and pieces agree with the canonical ones only up
to equality, as in `cup_key_heq`. -/
theorem cap_key_heq {x : a₀ ⟶ a₁} {up : a₁ ⟶ a₂} {dn : a₂ ⟶ a₁} {x' : a₃ ⟶ a₂}
    {up' : a₀ ⟶ a₃} {dn' : a₃ ⟶ a₀}
    {n₁ m₁ n₂ m₂ n₃ m₃ n₄ m₄ : FB S}
    {p₁ : a₀ ⟶ n₁} {q₁ : m₁ ⟶ a₁} {d₁ c₁ : n₁ ⟶ m₁} {p₂ : a₀ ⟶ n₂} {q₂ : m₂ ⟶ a₁}
    {d₂ c₂ : n₂ ⟶ m₂} {p₃ : a₀ ⟶ n₃} {q₃ : m₃ ⟶ a₁} {d₃ c₃ : n₃ ⟶ m₃} {p₄ : a₀ ⟶ n₄}
    {q₄ : m₄ ⟶ a₁} {d₄ c₄ : n₄ ⟶ m₄}
    (hn₁ : n₁ = a₀) (hm₁ : m₁ = a₂) (hn₂ : n₂ = a₁) (hm₂ : m₂ = a₁)
    (hn₃ : n₃ = a₃) (hm₃ : m₃ = a₁) (hn₄ : n₄ = a₀) (hm₄ : m₄ = a₀)
    (hp₁ : p₁ ≍ 𝟙 a₀) (hq₁ : q₁ ≍ dn) (hd₁ : d₁ ≍ up' ≫ x') (hc₁ : c₁ ≍ x ≫ up)
    (hp₂ : p₂ ≍ x) (hq₂ : q₂ ≍ 𝟙 a₁) (hd₂ : d₂ ≍ up ≫ dn) (hc₂ : c₂ ≍ 𝟙 a₁)
    (hp₃ : p₃ ≍ up') (hq₃ : q₃ ≍ 𝟙 a₁) (hd₃ : d₃ ≍ x' ≫ dn) (hc₃ : c₃ ≍ dn' ≫ x)
    (hp₄ : p₄ ≍ 𝟙 a₀) (hq₄ : q₄ ≍ x) (hd₄ : d₄ ≍ up' ≫ dn') (hc₄ : c₄ ≍ 𝟙 a₀)
    (g₁ : M.lift.map d₁ ⟶ M.lift.map c₁) (g₂ : M.lift.map d₂ ⟶ M.lift.map c₂)
    (g₃ : M.lift.map d₃ ⟶ M.lift.map c₃) (g₄ : M.lift.map d₄ ⟶ M.lift.map c₄)
    (γ₁ : M.lift.map up' ≫ M.lift.map x' ⟶ M.lift.map x ≫ M.lift.map up)
    (γ₂ : M.lift.map up ≫ M.lift.map dn ⟶ 𝟙 (M.obj a₁))
    (γ₃ : M.lift.map x' ≫ M.lift.map dn ⟶ M.lift.map dn' ≫ M.lift.map x)
    (γ₄ : M.lift.map up' ≫ M.lift.map dn' ⟶ 𝟙 (M.obj a₀))
    (hg₁ : g₁ ≍ γ₁) (hg₂ : g₂ ≍ γ₂) (hg₃ : g₃ ≍ γ₃) (hg₄ : g₄ ≍ γ₄)
    (hmate : (α_ _ _ _).inv ≫ γ₁ ▷ M.lift.map dn ≫ (α_ _ _ _).hom ≫ M.lift.map x ◁ γ₂ ≫
        (ρ_ _).hom = M.lift.map up' ◁ γ₃ ≫ (α_ _ _ _).inv ≫ γ₄ ▷ M.lift.map x ≫ (λ_ _).hom)
    {P P₁ Q₁ P₂ Q₂ P₃ Q₃ P₄ Q₄ Q : a₀ ⟶ a₁}
    (E₀ : P ⟶ P₁) (A₁ : P₁ ⟶ p₁ ≫ (d₁ ≫ q₁)) (B₁ : p₁ ≫ (c₁ ≫ q₁) ⟶ Q₁) (E₁ : Q₁ ⟶ P₂)
    (A₂ : P₂ ⟶ p₂ ≫ (d₂ ≫ q₂)) (B₂ : p₂ ≫ (c₂ ≫ q₂) ⟶ Q₂) (E₂ : Q₂ ⟶ Q)
    (E₃ : P ⟶ P₃) (A₃ : P₃ ⟶ p₃ ≫ (d₃ ≫ q₃)) (B₃ : p₃ ≫ (c₃ ≫ q₃) ⟶ Q₃) (E₄ : Q₃ ⟶ P₄)
    (A₄ : P₄ ⟶ p₄ ≫ (d₄ ≫ q₄)) (B₄ : p₄ ≫ (c₄ ≫ q₄) ⟶ Q₄) (E₅ : Q₄ ⟶ Q) :
    M.lift.map₂ E₀ ≫ (M.lift.map₂ A₁ ≫ midK M p₁ q₁ g₁ ≫ M.lift.map₂ B₁) ≫ M.lift.map₂ E₁ ≫
        (M.lift.map₂ A₂ ≫ midK M p₂ q₂ g₂ ≫ M.lift.map₂ B₂) ≫ M.lift.map₂ E₂ =
      M.lift.map₂ E₃ ≫ (M.lift.map₂ A₃ ≫ midK M p₃ q₃ g₃ ≫ M.lift.map₂ B₃) ≫ M.lift.map₂ E₄ ≫
        (M.lift.map₂ A₄ ≫ midK M p₄ q₄ g₄ ≫ M.lift.map₂ B₄) ≫ M.lift.map₂ E₅ := by
  subst hn₁ hm₁ hn₂ hm₂ hn₃ hm₃ hn₄ hm₄
  obtain rfl := eq_of_heq hp₁; obtain rfl := eq_of_heq hq₁; obtain rfl := eq_of_heq hd₁
  obtain rfl := eq_of_heq hc₁; obtain rfl := eq_of_heq hp₂; obtain rfl := eq_of_heq hq₂
  obtain rfl := eq_of_heq hd₂; obtain rfl := eq_of_heq hc₂; obtain rfl := eq_of_heq hp₃
  obtain rfl := eq_of_heq hq₃; obtain rfl := eq_of_heq hd₃; obtain rfl := eq_of_heq hc₃
  obtain rfl := eq_of_heq hp₄; obtain rfl := eq_of_heq hq₄; obtain rfl := eq_of_heq hd₄
  obtain rfl := eq_of_heq hc₄
  obtain rfl := eq_of_heq hg₁; obtain rfl := eq_of_heq hg₂; obtain rfl := eq_of_heq hg₃
  obtain rfl := eq_of_heq hg₄
  refine cap_key M (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) g₁ g₂ g₃ g₄ ?_ _ _ _ _ _ _ _ _ _ _ _ _
    _ _
  simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.comp_id]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]
  exact hmate

end Key

end Categorification.Diagrams.BicatInterp
