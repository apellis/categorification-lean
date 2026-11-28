/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorSyzygyChain

/-!
# Syzygy chains from chains of short exact sequences

A resolution `0 → M_N → ⋯ → M_0 → X → 0` is often produced as a chain of short exact
sequences `0 → K_{n+1} → M_n → K_n → 0` with `K_0 ≅ X`, given up to isomorphism
(`(S (n + 1)).X₃ ≅ (S n).X₁`), and `M_n = 0` for `n > N`. This is the form of Webster,
arXiv:1309.3796v3, §7.1, Proposition 7.8, used in §7.3 (proof of Proposition 7.22). This file
turns such a chain into a `ModuleSyzygyChain`, the input of the dévissage of `X ⊗ᴸ Y`.

## Main definitions

* `ModuleSyzygyChain.ofShortComplexes`: the syzygy chain with terms `(S n).X₂` and syzygies
  `(S n).X₃`.

## Main results

* `ModuleSyzygyChain.exists_of_shortComplexes`: the same, from isomorphisms given as
  `Nonempty`.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits

namespace ModuleSyzygyChain

variable {B : Type} [Ring B]

/-- **A chain of short exact sequences as a syzygy chain**: the terms are `(S n).X₂`, the
syzygies `(S n).X₃`, and the inclusion of `(S (n + 1)).X₃` into `(S n).X₂` goes through
`(S (n + 1)).X₃ ≅ (S n).X₁`. -/
def ofShortComplexes (S : ℕ → ShortComplex (ModuleCat.{0} B))
    (e : ∀ n, (S (n + 1)).X₃ ≅ (S n).X₁) (hS : ∀ n, (S n).ShortExact) (N : ℕ)
    (hz : ∀ n, N < n → IsZero (S n).X₂) : ModuleSyzygyChain B where
  length := N
  term n := (S n).X₂
  syz n := (S n).X₃
  ι n := ((e n).hom ≫ (S n).f).hom
  π n := (S n).g.hom
  injective n _ := by
    have := (hS n).mono_f
    have h₁ : Function.Injective (S n).f.hom :=
      (ModuleCat.mono_iff_injective (S n).f).mp inferInstance
    have h₂ : Function.Injective (e n).hom.hom :=
      (ModuleCat.mono_iff_injective (e n).hom).mp inferInstance
    rw [ModuleCat.hom_comp]
    exact h₁.comp h₂
  exact n _ := by
    have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS n).exact
    rw [ModuleCat.hom_comp]
    have hsurj : Function.Surjective (e n).hom.hom :=
      (ModuleCat.epi_iff_surjective (e n).hom).mp inferInstance
    intro y
    refine (hex y).trans ⟨fun ⟨x, hx⟩ => ?_, fun ⟨x, hx⟩ => ⟨(e n).hom.hom x, hx⟩⟩
    obtain ⟨z, rfl⟩ := hsurj x
    exact ⟨z, hx⟩
  surjective n _ := by
    have := (hS n).epi_g
    exact (ModuleCat.epi_iff_surjective (S n).g).mp inferInstance
  subsingleton_syz := by
    have := (hS (N + 1)).epi_g
    have hsurj : Function.Surjective (S (N + 1)).g.hom :=
      (ModuleCat.epi_iff_surjective (S (N + 1)).g).mp inferInstance
    have : Subsingleton (S (N + 1)).X₂ :=
      ModuleCat.isZero_iff_subsingleton.mp (hz (N + 1) (Nat.lt_succ_self N))
    exact hsurj.subsingleton

/-- **Syzygy chains from chains of short exact sequences** (the form of Webster,
arXiv:1309.3796v3, Proposition 7.8): a chain of short exact sequences with `(S 0).X₃ ≅ X`,
`(S (n + 1)).X₃ ≅ (S n).X₁` and `(S n).X₂ = 0` for `n > N` gives a syzygy chain of length `N`
resolving `X`, with terms `(S n).X₂`. -/
theorem exists_of_shortComplexes (S : ℕ → ShortComplex (ModuleCat.{0} B))
    {X : ModuleCat.{0} B} (h0 : Nonempty ((S 0).X₃ ≅ X))
    (hs : ∀ n, Nonempty ((S (n + 1)).X₃ ≅ (S n).X₁)) (hS : ∀ n, (S n).ShortExact) (N : ℕ)
    (hz : ∀ n, N < n → IsZero (S n).X₂) :
    ∃ c : ModuleSyzygyChain B, c.length = N ∧ (∀ n, c.term n = (S n).X₂) ∧
      Nonempty (c.syz 0 ≅ X) :=
  ⟨ofShortComplexes S (fun n => (hs n).some) hS N hz, rfl, fun _ => rfl, h0⟩

end ModuleSyzygyChain

end Categorification
