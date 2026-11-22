/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ModuleFiltration

/-!
# Exact functors preserve filtrations

An operation on modules that sends injections to injections, surjections to surjections and short
exact sequences to sequences exact in the middle sends a module with a
filtration by `L` to a module with a filtration by its values on `L`, with the same labels. This
is the step of Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
proof of Proposition 5.20, where a standard filtration of a tensor factor is transported through
exterior tensor product and standardization. Zero modules go to zero modules automatically: the
identity of a zero module is injective, surjective and exact at its middle term.

## Main results

* `HasFiltration.map`.
* `HasFiltration.relabel`: a filtration by `L ∘ f` is one by `L` with the labels mapped by `f`.
* `HasFiltration.exists_refine`: refining each subquotient by some filtration of it.
-/

universe u u' v v' w

namespace Categorification.ModuleFiltration

variable {A : Type u} [Ring A] {B : Type u'} [Ring B] {ι : Type w}

namespace HasFiltration

/-- An exact operation on modules preserves filtrations, with the same labels. -/
theorem map (F : ModuleCat.{v} A → ModuleCat.{v'} B)
    (Fm : ∀ {X Y : ModuleCat.{v} A}, (X →ₗ[A] Y) → (F X →ₗ[B] F Y))
    (hinj : ∀ {X Y : ModuleCat.{v} A} (f : X →ₗ[A] Y), Function.Injective f →
      Function.Injective (Fm f))
    (hsurj : ∀ {X Y : ModuleCat.{v} A} (f : X →ₗ[A] Y), Function.Surjective f →
      Function.Surjective (Fm f))
    (hex : ∀ {X Y Z : ModuleCat.{v} A} (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z),
      Function.Injective f → Function.Exact f g → Function.Surjective g →
      Function.Exact (Fm f) (Fm g))
    {L : ι → ModuleCat.{v} A} {m : List ι} {Y : ModuleCat.{v} A}
    (h : HasFiltration L m Y) : HasFiltration (fun c => F (L c)) m (F Y) := by
  induction h with
  | @zero Y₀ hY =>
    refine .zero ⟨fun a b => ?_⟩
    let i : Y₀ →ₗ[A] Y₀ := LinearMap.id
    have hi : Function.Injective i := fun _ _ h => h
    have hi' : Function.Surjective i := fun y => ⟨y, rfl⟩
    have hid : Function.Exact i i := fun y =>
      ⟨fun _ => ⟨y, rfl⟩, fun _ => @Subsingleton.elim _ hY (i y) 0⟩
    have hF := hex i i hi hid hi'
    have h0 : ∀ z : F Y₀, z = 0 := fun z => by
      obtain ⟨y, rfl⟩ := hsurj i hi' z
      exact hinj i hi (by rw [(hF _).2 ⟨y, rfl⟩, map_zero])
    rw [h0 a, h0 b]
  | cons f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    exact .cons (Fm f) (Fm g) m c (hinj f hf) (hex f g hf hfg hg) (hsurj g hg) ih
      ⟨LinearEquiv.ofBijective (Fm e.toLinearMap)
        ⟨hinj _ e.injective, hsurj _ e.surjective⟩⟩

/-- A filtration by `L ∘ f` is a filtration by `L`, with the labels mapped by `f`. -/
theorem relabel {ι' : Type*} {L : ι' → ModuleCat.{v} A} (f : ι → ι') {m : List ι}
    {Y : ModuleCat.{v} A} (h : HasFiltration (fun c => L (f c)) m Y) :
    HasFiltration L (m.map f) Y := by
  induction h with
  | zero hY => exact .zero hY
  | cons f' g m c hf hfg hg _ hZ ih => exact .cons f' g _ (f c) hf hfg hg ih hZ

/-- Refining a filtration: if every subquotient `L c` with `c ∈ m` has some filtration by `L'`,
then so has `Y`. -/
theorem exists_refine {ι' : Type*} {L : ι → ModuleCat.{v} A} {L' : ι' → ModuleCat.{v} A}
    {m : List ι} {Y : ModuleCat.{v} A} (h : HasFiltration L m Y)
    (hL : ∀ c ∈ m, ∃ l, HasFiltration L' l (L c)) : ∃ l, HasFiltration L' l Y := by
  induction h with
  | zero hY => exact ⟨[], .zero hY⟩
  | cons f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    obtain ⟨l₁, h₁⟩ := hL c List.mem_cons_self
    obtain ⟨l₂, h₂⟩ := ih fun d hd => hL d (List.mem_cons_of_mem _ hd)
    exact ⟨l₁ ++ l₂, (h₁.of_equiv e.symm).extension f g hf hfg hg h₂⟩

end HasFiltration

end Categorification.ModuleFiltration
