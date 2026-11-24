/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Finite filtrations with prescribed subquotients

A module `Y` *has a filtration by* a family of modules `L : ι → ModuleCat A` with list of
labels `m` if there is a finite chain of submodules `0 = Y₀ ⊆ Y₁ ⊆ ⋯ ⊆ Yₙ = Y` whose successive
quotients are isomorphic to the modules `L c`, `c ∈ m`, each label counted with its multiplicity.
This is the notion used for standard filtrations, e.g. in Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v2, Proposition 5.20 and Corollary 5.21.

We encode it inductively by the top step: `Y` has a filtration with labels `c :: m` if it is an
extension `0 → X → Y → Z → 0` of a module `Z ≅ L c` by a module `X` with a filtration with labels
`m`; the zero module has the empty filtration.

## Main definitions

* `ModuleFiltration.HasFiltration L m Y`.

## Main results

* `HasFiltration.of_equiv`: filtrations are transported along isomorphisms.
* `HasFiltration.single`: a module isomorphic to `L c` has the filtration `[c]`.
* `HasFiltration.extension`: an extension of two filtered modules is filtered, with the sum of
  the label lists (the labels of the quotient first).
* `HasFiltration.bind`: refining each subquotient by a filtration of it.
-/

universe u v w w'

namespace Categorification.ModuleFiltration

variable {A : Type u} [Ring A] {ι : Type w}

/-- `Y` has a finite filtration whose successive subquotients are the modules `L c`, `c ∈ m`. -/
inductive HasFiltration (L : ι → ModuleCat.{v} A) : List ι → ModuleCat.{v} A → Prop
  | zero {Y : ModuleCat.{v} A} : Subsingleton Y → HasFiltration L [] Y
  | cons {X Y Z : ModuleCat.{v} A} (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (m : List ι) (c : ι) :
      Function.Injective f → Function.Exact f g → Function.Surjective g →
      HasFiltration L m X → Nonempty (Z ≃ₗ[A] L c) → HasFiltration L (c :: m) Y

namespace HasFiltration

variable {L : ι → ModuleCat.{v} A}

/-- Filtrations are transported along isomorphisms. -/
theorem of_equiv {m : List ι} {Y Y' : ModuleCat.{v} A} (h : HasFiltration L m Y)
    (e : Y ≃ₗ[A] Y') : HasFiltration L m Y' := by
  cases h with
  | zero hY => exact .zero (e.symm.injective.subsingleton)
  | cons f g m c hf hfg hg hX hZ =>
    refine .cons (e.toLinearMap ∘ₗ f) (g ∘ₗ e.symm.toLinearMap) m c
      (e.injective.comp hf) ?_ (hg.comp e.symm.surjective) hX hZ
    intro y
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Set.mem_range]
    rw [hfg (e.symm y)]
    constructor
    · rintro ⟨x, hx⟩; exact ⟨x, by rw [hx, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨x, hx⟩; exact ⟨x, by rw [← hx, LinearEquiv.symm_apply_apply]⟩

/-- The zero module (here: `PUnit`) as a module category object. -/
abbrev zeroObj : ModuleCat.{v} A := ModuleCat.of A PUnit.{v + 1}

/-- A module isomorphic to `L c` has the filtration with the single label `c`. -/
theorem single {c : ι} {Y : ModuleCat.{v} A} (e : Y ≃ₗ[A] L c) : HasFiltration L [c] Y := by
  have h := HasFiltration.cons (L := L) (X := zeroObj) (Y := Y) (Z := Y) 0 LinearMap.id [] c
    (fun a b _ => Subsingleton.elim a b) ?_ (fun y => ⟨y, rfl⟩) (.zero inferInstance) ⟨e⟩
  · exact h
  · intro y
    simp only [LinearMap.id_coe, id_eq, LinearMap.zero_apply, Set.mem_range]
    constructor
    · intro hy; exact ⟨PUnit.unit, hy.symm⟩
    · rintro ⟨_, hx⟩; exact hx.symm

/-- The kernel of a linear map, as a module category object. -/
abbrev kerObj {Y Z : ModuleCat.{v} A} (g : Y →ₗ[A] Z) : ModuleCat.{v} A :=
  ModuleCat.of A (LinearMap.ker g)

/-- An extension `0 → X → Y → Z → 0` of filtered modules is filtered. -/
theorem extension {m m' : List ι} {Z : ModuleCat.{v} A} (hZ : HasFiltration L m' Z) :
    ∀ {X Y : ModuleCat.{v} A} (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z), Function.Injective f →
      Function.Exact f g → Function.Surjective g → HasFiltration L m X →
      HasFiltration L (m' ++ m) Y := by
  induction hZ with
  | zero hZ =>
    intro X Y f g hf hfg _ hX
    have hs : Function.Surjective f := fun y => (hfg y).1 (Subsingleton.elim _ _)
    simpa using hX.of_equiv (LinearEquiv.ofBijective f ⟨hf, hs⟩)
  | @cons Z₁ Z W f' g' m₁ c hf' hfg' hg' _ hW ih =>
    intro X Y f g hf hfg hg hX
    -- the preimage `Y₁ = ker (g' ∘ g)` of `Z₁`
    let K : Submodule A Y := LinearMap.ker (g' ∘ₗ g)
    have hKsub : ∀ y : K, g y ∈ LinearMap.range f' := fun y => (hfg' (g y)).1 y.2
    let e₁ := LinearEquiv.ofInjective f' hf'
    let p : K →ₗ[A] Z₁ :=
      e₁.symm.toLinearMap ∘ₗ ((g.comp K.subtype).codRestrict (LinearMap.range f') hKsub)
    have hp : ∀ y : K, f' (p y) = g y := fun y => by
      have := congrArg Subtype.val (e₁.apply_symm_apply ⟨g y, hKsub y⟩)
      exact this
    let i : X →ₗ[A] K := LinearMap.codRestrict K f (fun x => by
      show g' (g (f x)) = 0
      rw [show g (f x) = 0 from (hfg (f x)).2 ⟨x, rfl⟩, map_zero])
    have hfst := ih (X := X) (Y := kerObj (g' ∘ₗ g)) i p ?_ ?_ ?_ hX
    · have hY := HasFiltration.cons (L := L) (X := kerObj (g' ∘ₗ g)) (Y := Y) (Z := W)
        K.subtype (g' ∘ₗ g) (m₁ ++ m) c Subtype.val_injective ?_ (hg'.comp hg) hfst hW
      · simpa using hY
      · intro y
        simp only [Submodule.coe_subtype, Set.mem_range]
        exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨z, hz⟩ => hz ▸ z.2⟩
    · intro a b hab
      exact hf (congrArg Subtype.val hab)
    · intro y
      constructor
      · intro hy
        have : g y = 0 := by rw [← hp y, hy, map_zero]
        obtain ⟨x, hx⟩ := (hfg y).1 this
        exact ⟨x, Subtype.ext hx⟩
      · rintro ⟨x, rfl⟩
        apply hf'
        rw [hp, map_zero]
        exact (hfg (f x)).2 ⟨x, rfl⟩
    · intro z
      obtain ⟨y, hy⟩ := hg (f' z)
      have hyK : y ∈ K := by
        show g' (g y) = 0
        rw [hy]; exact (hfg' _).2 ⟨z, rfl⟩
      exact ⟨⟨y, hyK⟩, hf' (by rw [hp]; exact hy)⟩

/-- Refining a filtration: if every subquotient `L c` has a filtration by `L'` with labels
`M c`, then `Y` has a filtration by `L'` with labels `m.flatMap M`. -/
theorem bind {ι' : Type w'} {L' : ι' → ModuleCat.{v} A} {M : ι → List ι'}
    (hL : ∀ c, HasFiltration L' (M c) (L c)) {m : List ι} {Y : ModuleCat.{v} A}
    (h : HasFiltration L m Y) : HasFiltration L' (m.flatMap M) Y := by
  induction h with
  | zero hY => simpa using HasFiltration.zero (L := L') hY
  | cons f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    have := ((hL c).of_equiv e.symm).extension f g hf hfg hg ih
    simpa using this

/-- A filtration of a module with labels in `m` is also one for a family agreeing on `m`. -/
theorem mono {L' : ι → ModuleCat.{v} A}
    (hL : ∀ c, Nonempty (L c ≃ₗ[A] L' c)) {m : List ι} {Y : ModuleCat.{v} A}
    (h : HasFiltration L m Y) : HasFiltration L' m Y := by
  induction h with
  | zero hY => exact .zero hY
  | cons f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    exact .cons f g m c hf hfg hg ih ⟨e.trans (hL c).some⟩

/-- Restricting scalars carries a finite filtration to the restricted subquotients,
with the same labels. -/
theorem restrictScalars {R : Type*} [Ring R] (φ : R →+* A) {m : List ι}
    {Y : ModuleCat.{v} A} (h : HasFiltration L m Y) :
    HasFiltration (fun c => (ModuleCat.restrictScalars φ).obj (L c)) m
      ((ModuleCat.restrictScalars φ).obj Y) := by
  induction h with
  | zero hY => exact .zero hY
  | cons f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    let F := ModuleCat.restrictScalars.{v} φ
    exact .cons (F.map (ModuleCat.ofHom f)).hom (F.map (ModuleCat.ofHom g)).hom m c
      hf hfg hg ih ⟨LinearEquiv.ofBijective (F.map (ModuleCat.ofHom e.toLinearMap)).hom e.bijective⟩

end HasFiltration

end Categorification.ModuleFiltration
