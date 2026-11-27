/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensorExact
import Categorification.Algebra.BalancedTensorRightExact

/-!
# Injectivity of a tensored inclusion from a projective presentation

Let `0 → K → P → D → 0` be a short exact sequence of right `A`-modules and let
`F₂ → F₁ → F₀ → N → 0` be a complex of left `A`-modules, exact at `F₀` and `N`, with `F₀` and
`F₁` projective. If `D ⊗_A F₂ → D ⊗_A F₁ → D ⊗_A F₀` is exact at `D ⊗_A F₁`, then
`K ⊗_A N → P ⊗_A N` is injective (`mapLeftBimodule_injective_of_presentation`).

This is the connecting-map argument of the long exact sequence of
`0 → K ⊗ F → P ⊗ F → D ⊗ F → 0`: its degree-one homology `H₁(D ⊗ F)` surjects onto the kernel of
`H₀(K ⊗ F) = K ⊗ N → H₀(P ⊗ F) = P ⊗ N`. Only the presentation `F₁ → F₀ → N → 0` is used to
compute `H₀`; exactness of `F` at `F₁` is not needed.

It is the final step of the proof of the injectivity in B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Lemma 6.9 (v2: Lemma 6.8), at (6.21), for the
presentation of a column of the braiding bimodule by the cube of loading projectives. The
argument replaces the printed one, which gives only surjectivity.

## Main results

* `BalancedTensor.mapLeftBimodule_injective_of_presentation`.
-/

noncomputable section

namespace Categorification.BalancedTensor

open MulOpposite

variable {k : Type*} [CommRing k] {A : Type*} [Ring A] [Algebra k A]
  {K : Type*} [AddCommGroup K] [Module k K] [Module Aᵐᵒᵖ K] [SMulCommClass k Aᵐᵒᵖ K]
  [IsScalarTower k Aᵐᵒᵖ K]
  {P : Type*} [AddCommGroup P] [Module k P] [Module Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P]
  [IsScalarTower k Aᵐᵒᵖ P]
  {D : Type*} [AddCommGroup D] [Module k D] [Module Aᵐᵒᵖ D] [SMulCommClass k Aᵐᵒᵖ D]
  [IsScalarTower k Aᵐᵒᵖ D]
  {F₂ : Type*} [AddCommGroup F₂] [Module k F₂] [Module A F₂] [IsScalarTower k A F₂]
  {F₁ : Type*} [AddCommGroup F₁] [Module k F₁] [Module A F₁] [IsScalarTower k A F₁]
  {F₀ : Type*} [AddCommGroup F₀] [Module k F₀] [Module A F₀] [IsScalarTower k A F₀]
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

omit [IsScalarTower k Aᵐᵒᵖ K] [IsScalarTower k Aᵐᵒᵖ P] [IsScalarTower k Aᵐᵒᵖ D] in
/-- `M ⊗_A -` sends a zero composite to a zero composite. -/
theorem mapRight_comp_eq_zero {M : Type*} [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
    [SMulCommClass k Aᵐᵒᵖ M] {d₂ : F₂ →ₗ[A] F₁} {d₁ : F₁ →ₗ[A] F₀} (hd : d₁.comp d₂ = 0)
    (x : BalancedTensor k k A M F₂) :
    mapRight (k := k) (B := k) d₁ (mapRight (k := k) (B := k) d₂ x) = 0 := by
  rw [← LinearMap.comp_apply, ← mapRight_comp, hd]
  induction x using induction_on with
  | zero => simp
  | tmul m n => simp [mapRight_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

/-- **Injectivity from a presentation.** For a short exact sequence `0 → K → P → D → 0` of right
`A`-modules and a complex `F₂ → F₁ → F₀ → N → 0` exact at `F₀` and `N`, with `F₀`, `F₁`
projective, if `D ⊗ F₂ → D ⊗ F₁ → D ⊗ F₀` is exact at `D ⊗ F₁`, then `K ⊗_A N → P ⊗_A N` is
injective. -/
theorem mapLeftBimodule_injective_of_presentation
    [Module.Projective A F₀] [Module.Projective A F₁]
    {f : K →ₗ[k] P} (hf : IsBimoduleHom (A := A) f) {g : P →ₗ[k] D} (hg : IsBimoduleHom (A := A) g)
    (hfi : Function.Injective f) (hfg : Function.Exact f g) (hgs : Function.Surjective g)
    {d₂ : F₂ →ₗ[A] F₁} {d₁ : F₁ →ₗ[A] F₀} {ε : F₀ →ₗ[A] N}
    (hd : d₁.comp d₂ = 0) (hε : Function.Exact d₁ ε) (hεs : Function.Surjective ε)
    (hH : ∀ x : BalancedTensor k k A D F₁, mapRight (k := k) (B := k) d₁ x = 0 →
      ∃ y, mapRight (k := k) (B := k) d₂ y = x) :
    Function.Injective (mapLeftBimodule k N f hf) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  -- Lift `z` along the surjection `K ⊗ F₀ → K ⊗ N`.
  obtain ⟨k₀, rfl⟩ := mapRight_surjective (k := k) (B := k) (M := K) hεs z
  -- Its image in `P ⊗ F₀` dies in `P ⊗ N`, so it comes from `P ⊗ F₁`.
  have hP : mapRight (k := k) (B := k) ε (mapLeftBimodule k F₀ f hf k₀) = 0 := by
    rw [← mapLeftBimodule_mapRight]; exact hz
  obtain ⟨p₁, hp₁⟩ := ((mapRight_exact (k := k) (B := k) (M := P) d₁ ε hε hεs) _).1 hP
  -- The image of `p₁` in `D ⊗ F₁` is a cycle, hence a boundary.
  have hfg₀ := mapLeftBimodule_exact (k := k) (B := k) (N := F₀) hf hg hfg
  have hcyc : mapRight (k := k) (B := k) d₁ (mapLeftBimodule k F₁ g hg p₁) = 0 := by
    rw [← mapLeftBimodule_mapRight, hp₁]
    exact hfg₀.apply_apply_eq_zero k₀
  obtain ⟨δ, hδ⟩ := hH _ hcyc
  obtain ⟨p₂, rfl⟩ := mapLeftBimodule_surjective (k := k) (B := k) (N := F₂) hg hgs δ
  -- `p₁ - d₂ p₂` lies in the image of `K ⊗ F₁`.
  have hfg₁ := mapLeftBimodule_exact (k := k) (B := k) (N := F₁) hf hg hfg
  have hq : mapLeftBimodule k F₁ g hg (p₁ - mapRight (k := k) (B := k) d₂ p₂) = 0 := by
    rw [map_sub, mapLeftBimodule_mapRight, hδ, sub_self]
  obtain ⟨k₁, hk₁⟩ := (hfg₁ _).1 hq
  -- Then `k₀ = d₁ k₁` by injectivity of `K ⊗ F₀ → P ⊗ F₀`.
  have hk₀ : mapRight (k := k) (B := k) d₁ k₁ = k₀ := by
    apply mapLeftBimodule_injective (k := k) (B := k) (N := F₀) hf hfi
    rw [mapLeftBimodule_mapRight, hk₁, map_sub, mapRight_comp_eq_zero hd, sub_zero, hp₁]
  rw [← hk₀]
  exact (mapRight_exact (k := k) (B := k) (M := K) d₁ ε hε hεs).apply_apply_eq_zero k₁

end Categorification.BalancedTensor
