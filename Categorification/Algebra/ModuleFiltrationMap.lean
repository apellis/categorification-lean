/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ModuleFiltration

/-!
# Exact functors preserve filtrations

An operation on modules that sends injections to injections, surjections to surjections, short
exact sequences to short exact sequences and zero modules to zero modules sends a module with a
filtration by `L` to a module with a filtration by its values on `L`, with the same labels. This
is the step of Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
proof of Proposition 5.21, where a standard filtration of a tensor factor is transported through
exterior tensor product and standardization.

## Main results

* `HasFiltration.map`.
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
    (hzero : ∀ {X : ModuleCat.{v} A}, Subsingleton X → Subsingleton (F X))
    {L : ι → ModuleCat.{v} A} {m : List ι} {Y : ModuleCat.{v} A}
    (h : HasFiltration L m Y) : HasFiltration (fun c => F (L c)) m (F Y) := by
  induction h with
  | zero hY => exact .zero (hzero hY)
  | cons f g m c hf hfg hg _ hZ ih =>
    obtain ⟨e⟩ := hZ
    exact .cons (Fm f) (Fm g) m c (hinj f hf) (hex f g hf hfg hg) (hsurj g hg) ih
      ⟨LinearEquiv.ofBijective (Fm e.toLinearMap)
        ⟨hinj _ e.injective, hsurj _ e.surjective⟩⟩

end HasFiltration

end Categorification.ModuleFiltration
