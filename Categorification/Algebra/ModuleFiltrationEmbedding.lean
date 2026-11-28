/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ModuleFiltration

/-!
# Submodules of filtered modules

If `Y` has a finite filtration with subquotients `L c`, every nonzero submodule of `Y` has a
nonzero submodule embedding into one of the `L c` (`HasFiltration.exists_injective_of_ne_bot`):
meet it with the steps of the filtration and take the first step it meets nontrivially. This is
the step "a module with a standard stratification has a submodule which is standard" of
B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 5.30, (1) ⇒ (2).
-/

universe u v w

namespace Categorification.ModuleFiltration

variable {A : Type u} [Ring A] {ι : Type w} {L : ι → ModuleCat.{v} A}

/-- **A nonzero submodule of a filtered module meets a subquotient**: it has a nonzero submodule
embedding into some `L c`, `c` a label of the filtration. -/
theorem HasFiltration.exists_injective_of_ne_bot {m : List ι} {Y : ModuleCat.{v} A}
    (hY : HasFiltration L m Y) (K : Submodule A Y) (hK : K ≠ ⊥) :
    ∃ c ∈ m, ∃ K' : Submodule A Y, K' ≤ K ∧ K' ≠ ⊥ ∧
      ∃ φ : K' →ₗ[A] L c, Function.Injective φ := by
  induction hY with
  | zero hY =>
    exact (hK (Submodule.eq_bot_of_subsingleton)).elim
  | @cons X Y Z f g m c hf hfg hg hX hZ ih =>
    obtain ⟨e⟩ := hZ
    by_cases hKf : K ⊓ LinearMap.range f = ⊥
    · refine ⟨c, List.mem_cons_self, K, le_rfl, hK, e.toLinearMap ∘ₗ g ∘ₗ K.subtype, ?_⟩
      refine e.injective.comp ((injective_iff_map_eq_zero _).2 fun y hy => ?_)
      obtain ⟨x, hx⟩ := (hfg y).1 hy
      have hy' : (y : Y) ∈ K ⊓ LinearMap.range f := ⟨y.2, x, hx⟩
      rw [hKf, Submodule.mem_bot] at hy'
      exact Subtype.ext hy'
    · let K₀ : Submodule A X := (K ⊓ LinearMap.range f).comap f
      have hK₀ : K₀ ≠ ⊥ := by
        intro h
        apply hKf
        rw [eq_bot_iff]
        rintro y ⟨hyK, x, rfl⟩
        have : x ∈ K₀ := ⟨hyK, x, rfl⟩
        rw [h, Submodule.mem_bot] at this
        rw [this, map_zero, Submodule.mem_bot]
      obtain ⟨c', hc', K', hK'K₀, hK', φ, hφ⟩ := ih K₀ hK₀
      have hle : K'.map f ≤ K := by
        rintro _ ⟨x, hx, rfl⟩
        exact (hK'K₀ hx).1
      have hne : K'.map f ≠ ⊥ := by
        intro h
        apply hK'
        rw [eq_bot_iff]
        intro x hx
        have : f x ∈ K'.map f := ⟨x, hx, rfl⟩
        rw [h, Submodule.mem_bot] at this
        rw [Submodule.mem_bot]
        exact hf (by rw [this, map_zero])
      let ε := Submodule.equivMapOfInjective f hf K'
      exact ⟨c', List.mem_cons_of_mem c hc', K'.map f, hle, hne, φ ∘ₗ ε.symm.toLinearMap,
        hφ.comp ε.symm.injective⟩

end Categorification.ModuleFiltration
