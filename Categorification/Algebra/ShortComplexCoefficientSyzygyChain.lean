/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ShortComplexSyzygyChain
import Categorification.Algebra.DerivedTensorCoefficientAcyclicCover

/-!
# Coefficient syzygy chains from chains of short exact sequences of right modules

The coefficient analogue of `ModuleSyzygyChain.ofShortComplexes`: a resolution
`0 → M_N → ⋯ → M_0 → X → 0` of a right `B`-module, given as a chain of short exact sequences
`0 → K_{n+1} → M_n → K_n → 0` in `ModuleCat Bᵐᵒᵖ` with `K_0 ≅ X` (`(S (n + 1)).X₃ ≅ (S n).X₁`)
and `M_n = 0` for `n > N`, is a `CoefficientSyzygyChain ℤ B` (the coefficient of
`− ⊗ᴸ_B Y` over `ℤ`, `CoefficientModule.ofRight`). This is the form of Webster,
arXiv:1309.3796v3, §7.1, Proposition 7.8 for the reflected left module of §7.3 (proof of
Proposition 7.22), the first input of the dévissage
`nonempty_linearEquiv_derivedTensorHomology_of_syzygyChains`.

## Main definitions

* `CoefficientSyzygyChain.ofRightShortComplexes`: the chain with terms `(S n).X₂` and
  syzygies `(S n).X₃`.

## Main results

* `CoefficientSyzygyChain.exists_of_rightShortComplexes`: the same, from isomorphisms given as
  `Nonempty`, with `c.syz 0` the resolved module itself.
* `coefficientOfRightHomologyEquiv`, `coefficientOfRightHomologyEquivOfEq`: the derived tensor
  cohomology of `CoefficientModule.ofRight N` is that of `N`.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits

namespace CoefficientSyzygyChain

variable {B : Type} [Ring B]

/-- **A chain of short exact sequences of right modules as a coefficient syzygy chain** over
`ℤ`: the terms are `(S n).X₂`, the syzygies `(S n).X₃`, and the inclusion of `(S (n + 1)).X₃`
into `(S n).X₂` goes through `(S (n + 1)).X₃ ≅ (S n).X₁`. -/
def ofRightShortComplexes (S : ℕ → ShortComplex (ModuleCat.{0} Bᵐᵒᵖ))
    (e : ∀ n, (S (n + 1)).X₃ ≅ (S n).X₁) (hS : ∀ n, (S n).ShortExact) (N : ℕ)
    (hz : ∀ n, N < n → IsZero (S n).X₂) : CoefficientSyzygyChain ℤ B where
  length := N
  term n := CoefficientModule.ofRight (S n).X₂
  syz n := CoefficientModule.ofRight (S n).X₃
  ι n := ((e n).hom ≫ (S n).f).hom.toAddMonoidHom.toIntLinearMap
  π n := (S n).g.hom.toAddMonoidHom.toIntLinearMap
  ι_op n b m := ((e n).hom ≫ (S n).f).hom.map_smul (MulOpposite.op b) m
  π_op n b m := (S n).g.hom.map_smul (MulOpposite.op b) m
  injective n _ := by
    have := (hS n).mono_f
    have h₁ : Function.Injective (S n).f.hom :=
      (ModuleCat.mono_iff_injective (S n).f).mp inferInstance
    have h₂ : Function.Injective (e n).hom.hom :=
      (ModuleCat.mono_iff_injective (e n).hom).mp inferInstance
    change Function.Injective ((e n).hom ≫ (S n).f).hom
    rw [ModuleCat.hom_comp]
    exact h₁.comp h₂
  exact n _ := by
    have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS n).exact
    change Function.Exact ((e n).hom ≫ (S n).f).hom (S n).g.hom
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

/-- **Coefficient syzygy chains from chains of short exact sequences of right modules** (the
form of Webster, arXiv:1309.3796v3, Proposition 7.8, for a reflected module): a chain with
`(S 0).X₃ ≅ X`, `(S (n + 1)).X₃ ≅ (S n).X₁` and `(S n).X₂ = 0` for `n > N` gives a coefficient
syzygy chain over `ℤ` of length `N` resolving `X` itself (`c.syz 0` is `X`, not only isomorphic
to it), with terms `(S n).X₂`. -/
theorem exists_of_rightShortComplexes (S : ℕ → ShortComplex (ModuleCat.{0} Bᵐᵒᵖ))
    {X : ModuleCat.{0} Bᵐᵒᵖ} (h0 : Nonempty ((S 0).X₃ ≅ X))
    (hs : ∀ n, Nonempty ((S (n + 1)).X₃ ≅ (S n).X₁)) (hS : ∀ n, (S n).ShortExact) (N : ℕ)
    (hz : ∀ n, N < n → IsZero (S n).X₂) :
    ∃ c : CoefficientSyzygyChain ℤ B, c.length = N ∧
      (∀ n, c.term n = CoefficientModule.ofRight (S n).X₂) ∧
      c.syz 0 = CoefficientModule.ofRight X := by
  obtain ⟨e₀⟩ := h0
  let S₀ : ShortComplex (ModuleCat.{0} Bᵐᵒᵖ) := ShortComplex.mk (S 0).f ((S 0).g ≫ e₀.hom)
    (by rw [← Category.assoc, (S 0).zero, zero_comp])
  have hS₀ : S₀.ShortExact := ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := S 0) (S₂ := S₀) (Iso.refl _) (Iso.refl _) e₀
      (by simp [S₀]) (by simp [S₀])) (hS 0)
  let S' : ℕ → ShortComplex (ModuleCat.{0} Bᵐᵒᵖ) := fun n =>
    match n with
    | 0 => S₀
    | m + 1 => S (m + 1)
  let e' : ∀ n, (S' (n + 1)).X₃ ≅ (S' n).X₁ := fun n =>
    match n with
    | 0 => (hs 0).some
    | m + 1 => (hs (m + 1)).some
  have hS' : ∀ n, (S' n).ShortExact := fun n =>
    match n with
    | 0 => hS₀
    | m + 1 => hS (m + 1)
  have hz' : ∀ n, N < n → IsZero (S' n).X₂ := fun n =>
    match n with
    | 0 => fun h => absurd h (Nat.not_lt_zero N)
    | m + 1 => hz (m + 1)
  refine ⟨ofRightShortComplexes S' e' hS' N hz', rfl, fun n => ?_, rfl⟩
  match n with
  | 0 => rfl
  | m + 1 => rfl

end CoefficientSyzygyChain

section Bridge

open DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w

variable {B : Type} [Ring B] [HasDerivedCategory.{w, 0} ℤ] [HasDerivedCategory.{w, 0} B]

/-- The derived tensor cohomology with the coefficient `CoefficientModule.ofRight N`, for its
bundled `ℤ`-module structure (the form produced by the dévissage over a general ring `k` at
`k = ℤ`), is that with `N` itself. -/
def coefficientOfRightHomologyEquiv (N : ModuleCat.{0} Bᵐᵒᵖ) (Y : DerivedCategory.{w, 0} B)
    (n : ℤ) :
    (homologyFunctor (A := ℤ) ℤ n).obj
        ((@derivedTensor.{w, 0} ℤ B Int.instCommRing.toRing _ (CoefficientModule.ofRight N) _
          (CoefficientModule.ofRight N).isModule _
          (CoefficientModule.ofRight N).isSMulCommClass _ _).obj Y) ≃ₗ[ℤ]
      (homologyFunctor (A := ℤ) ℤ n).obj ((derivedTensor.{w} ℤ B N).obj Y) :=
  LinearEquiv.refl ℤ _

/-- `coefficientOfRightHomologyEquiv` for a coefficient equal to `CoefficientModule.ofRight N`
(as the terms of `CoefficientSyzygyChain.exists_of_rightShortComplexes` are). -/
def coefficientOfRightHomologyEquivOfEq {c : CoefficientModule ℤ B} {N : ModuleCat.{0} Bᵐᵒᵖ}
    (h : c = CoefficientModule.ofRight N) (Y : DerivedCategory.{w, 0} B) (n : ℤ) :
    (homologyFunctor (A := ℤ) ℤ n).obj
        ((@derivedTensor.{w, 0} ℤ B Int.instCommRing.toRing _ c _ c.isModule _
          c.isSMulCommClass _ _).obj Y) ≃ₗ[ℤ]
      (homologyFunctor (A := ℤ) ℤ n).obj ((derivedTensor.{w} ℤ B N).obj Y) := by
  subst h
  exact coefficientOfRightHomologyEquiv N Y n

end Bridge

end Categorification
