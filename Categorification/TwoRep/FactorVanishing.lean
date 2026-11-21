/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.LinearCat
import Mathlib.LinearAlgebra.Span.Defs

/-!
# 2-morphisms factoring through a 1-morphism that kills an object

For a pseudofunctor `F` into `LinearCat k`, an object `C` of `F(a)` and a 1-morphism
`e : a ⟶ b` with `F(e)(C) = 0`, every 2-morphism `u ⟶ v` that factors through a composite
`e ≫ w` acts on `C` by zero. This is the step in the proof of B. Webster, *Knot invariants and
higher representation theory*, arXiv:1309.3796v2, Cor. 3.27, showing that the strongly
equivariant functor `𝒰(λ) → 𝒞` determined by a highest weight object `C` (with `E_i C = 0`)
kills the ideal of 2-morphisms factoring through `E_i 1_λ` (Prop. 3.25).

* `factorIdeal K f g`: for a property `K` of 1-morphisms out of `a`, the span of the
  2-morphisms `f ⟶ g` that factor through a composite `e ≫ w` with `K e`;
* `comp_mem_factorIdeal`, `mem_factorIdeal_comp`: the factor ideal is a two-sided ideal for
  vertical composition;
* `map₂_app_eq_zero_of_mem_factorIdeal`: if every such `e` kills `C` and `F` is additive and
  `k`-linear on 2-morphisms at `C`, every element of the ideal acts on `C` by zero.
-/

open CategoryTheory CategoryTheory.Limits

namespace Categorification.TwoRep

universe w v u w₁ v₁ u₁

variable {k : Type w} [CommRing k] {B : Type u₁} [Bicategory.{w₁, v₁} B]

/-- The object `F(e ≫ w)(C)` is zero when `F(e)(C)` is. -/
theorem isZero_map_comp_obj (F : Pseudofunctor B (LinearCat.{w, v, u} k)) {a b c : B}
    (e : a ⟶ b) (w' : b ⟶ c) (C : F.obj a) (hC : IsZero ((F.map e).obj.obj C)) :
    IsZero ((F.map (e ≫ w')).obj.obj C) :=
  (Functor.map_isZero (F.map w').obj hC).of_iso
    ((ObjectProperty.ι _).mapIso (F.mapComp e w') |>.app C)

/-- **A 2-morphism factoring through `e ≫ w` acts by zero on an object killed by `e`.** -/
theorem map₂_app_eq_zero_of_factor (F : Pseudofunctor B (LinearCat.{w, v, u} k)) {a b c : B}
    {e : a ⟶ b} {w' : b ⟶ c} {f g : a ⟶ c} (α : f ⟶ e ≫ w') (β : e ≫ w' ⟶ g)
    (C : F.obj a)
    (hC : IsZero ((F.map e).obj.obj C)) : (F.map₂ (α ≫ β)).hom.app C = 0 := by
  rw [F.map₂_comp]
  change (F.map₂ α).hom.app C ≫ (F.map₂ β).hom.app C = 0
  rw [(isZero_map_comp_obj F e w' C hC).eq_zero_of_tgt ((F.map₂ α).hom.app C), zero_comp]

section Ideal

variable [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]

/-- **The ideal of 2-morphisms factoring through `K`**: for a property `K` of 1-morphisms out of
`a`, the span of the 2-morphisms `f ⟶ g` of the form `α ≫ β` with `α : f ⟶ e ≫ w`,
`β : e ≫ w ⟶ g` and `K e`. -/
def factorIdeal {a c : B} (K : ∀ ⦃b : B⦄, (a ⟶ b) → Prop) (f g : a ⟶ c) :
    Submodule k (f ⟶ g) :=
  Submodule.span k {φ | ∃ (b : B) (e : a ⟶ b) (w' : b ⟶ c) (α : f ⟶ e ≫ w')
    (β : e ≫ w' ⟶ g), K e ∧ α ≫ β = φ}

/-- The factor ideal is closed under precomposition. -/
theorem comp_mem_factorIdeal {a c : B} {K : ∀ ⦃b : B⦄, (a ⟶ b) → Prop} {f' f g : a ⟶ c}
    (γ : f' ⟶ f) {φ : f ⟶ g} (hφ : φ ∈ factorIdeal (k := k) K f g) :
    γ ≫ φ ∈ factorIdeal (k := k) K f' g := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨b, e, w', α, β, he, rfl⟩ := h
    exact Submodule.subset_span ⟨b, e, w', γ ≫ α, β, he, Category.assoc _ _ _⟩
  | zero => rw [Limits.comp_zero]; exact zero_mem _
  | add φ ψ _ _ hφ hψ => rw [Preadditive.comp_add]; exact add_mem hφ hψ
  | smul r φ _ hφ => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hφ

/-- The factor ideal is closed under postcomposition. -/
theorem mem_factorIdeal_comp {a c : B} {K : ∀ ⦃b : B⦄, (a ⟶ b) → Prop} {f g g' : a ⟶ c}
    {φ : f ⟶ g} (hφ : φ ∈ factorIdeal (k := k) K f g) (δ : g ⟶ g') :
    φ ≫ δ ∈ factorIdeal (k := k) K f g' := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨b, e, w', α, β, he, rfl⟩ := h
    exact Submodule.subset_span ⟨b, e, w', α, β ≫ δ, he, (Category.assoc _ _ _).symm⟩
  | zero => rw [Limits.zero_comp]; exact zero_mem _
  | add φ ψ _ _ hφ hψ => rw [Preadditive.add_comp]; exact add_mem hφ hψ
  | smul r φ _ hφ => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hφ

/-- **Every element of the factor ideal acts by zero on an object killed by `K`**, for a
pseudofunctor additive and `k`-linear on 2-morphisms at `C`. -/
theorem map₂_app_eq_zero_of_mem_factorIdeal (F : Pseudofunctor B (LinearCat.{w, v, u} k))
    {a c : B} (K : ∀ ⦃b : B⦄, (a ⟶ b) → Prop) {f g : a ⟶ c} (C : F.obj a)
    (hK : ∀ ⦃b : B⦄ (e : a ⟶ b), K e → IsZero ((F.map e).obj.obj C))
    (hadd : ∀ φ ψ : f ⟶ g,
      (F.map₂ (φ + ψ)).hom.app C = (F.map₂ φ).hom.app C + (F.map₂ ψ).hom.app C)
    (hsmul : ∀ (r : k) (φ : f ⟶ g),
      (F.map₂ (r • φ)).hom.app C = r • (F.map₂ φ).hom.app C)
    {φ : f ⟶ g} (hφ : φ ∈ factorIdeal (k := k) K f g) : (F.map₂ φ).hom.app C = 0 := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨b, e, w', α, β, he, rfl⟩ := h
    exact map₂_app_eq_zero_of_factor F α β C (hK e he)
  | zero =>
    have := hsmul 0 0
    rwa [zero_smul, zero_smul] at this
  | add φ ψ _ _ hφ hψ => rw [hadd, hφ, hψ, add_zero]
  | smul r φ _ hφ => rw [hsmul, hφ, smul_zero]

end Ideal

end Categorification.TwoRep
