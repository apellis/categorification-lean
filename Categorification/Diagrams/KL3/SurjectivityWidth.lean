/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Surjectivity

/-!
# Surjectivity of `γ`: the induction on the width (KL III, proof of Theorem 1.1)

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.8.4
(TeX `\subsubsection{Idempotents in $\UcatD$}`), *Proof of Theorem 1.1*:

> We show that `[P]` is in the image of `γ : _𝒜 U̇ → K₀(U̇)` by induction on the length of `P`.
> Let `P` have length `m`. Then `P` is a direct summand of `E_{ν,-ν'} 1_λ {t}` […]
> `[P] ∈ [E_{ν,-ν'} 1_λ, e_{r,r'}] + γ(_𝒜 U̇)`.

This file isolates the formal part of this induction. An indecomposable `Z` of `U̇(λ, ρ)` is
**low** of level `m` (`IsLow m Z`) if it is a direct summand of `E_w 1_λ {n}` for a signed
sequence `w` of length `< m`; its *width* is the least `m` with `IsLow (m + 1) Z`. The *top*
step of KL III's argument is the hypothesis `TopHyp`: an indecomposable direct summand `Z` of a
sorted `E_{+a} E_{-b} 1_λ {n}` which is not low of level `|a| + |b|` has class in the image of
`γ` plus the span of the classes of the indecomposables of smaller width. Under this hypothesis
every indecomposable has class in the image of `γ` (induction on the width, using Lemma 3.38 in
the form `exists_retract_sorted_of_retract`), so `γ` is surjective.

## Main results

* `gammaImg lam ρ`: the image of `γ`, the `ℤ[q, q⁻¹]`-span of the classes `[E_d 1_λ]`;
  `gammaUA'_surjective_iff`: `γ` is surjective iff `gammaImg lam ρ = ⊤`.
* `IsLow`, `lowSpanU`, `TopHyp`.
* `cl_mem_gammaImg_of_topHyp`, `gammaUA'_surjective_of_topHyp`: **KL III Theorem 1.1
  (surjectivity of `γ`), conditional on `TopHyp`**.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits StringDiagrams QuantumGroup UDot Presentation
  GradedBicat KrullSchmidtCat

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [Field k]

section Width

attribute [local instance] KLR.KLGamma.vAlgebra

variable [DecidableEq I]

variable (RD k) in
/-- **The image of `γ`** in `K₀(U̇(λ, ρ))`: the `ℤ[q, q⁻¹]`-span of the classes `[E_d 1_λ]`
of the products of divided powers `E_d 1_λ` (the range of `dpCComb`). -/
abbrev gammaImg (lam ρ : X) : Submodule (LaurentPolynomial ℤ) (K0Kar RD k ρ lam) :=
  LinearMap.range (dpCComb (RD := RD) (k := k) lam ρ)

theorem dpC_mem_gammaImg {lam ρ : X} (d : List (Bool × I × ℕ)) (h : wt RD lam (dpWord d) = ρ) :
    dpC RD k d lam ρ h ∈ gammaImg RD k lam ρ :=
  ⟨Finsupp.single ⟨d, h⟩ 1, by rw [dpCComb, Finsupp.linearCombination_single, one_smul]⟩

variable (RD k) in
/-- An object of `U̇(λ, ρ)` is **low of level `m`** if it is a direct summand (retract) of some
`E_w 1_λ {n}` with `|w| < m`. -/
def IsLow {ρ lam : X} (m : ℕ) (Z : UKar RD k ρ lam) : Prop :=
  ∃ (w : List (Letter I)) (h : wt RD lam w = ρ) (n : ℤ), w.length < m ∧
    ∃ (f : Z ⟶ nfObj RD k ρ lam w h n) (g : nfObj RD k ρ lam w h n ⟶ Z), f ≫ g = 𝟙 Z

omit [DecidableEq I] in
theorem IsLow.mono {ρ lam : X} {m m' : ℕ} (hm : m ≤ m') {Z : UKar RD k ρ lam} (h : IsLow RD k m Z) :
    IsLow RD k m' Z := by
  obtain ⟨w, hw, n, hl, f, g, hfg⟩ := h
  exact ⟨w, hw, n, by omega, f, g, hfg⟩

variable (RD k) in
/-- The span of the classes of the indecomposables which are low of level `m`. -/
def lowSpanU (ρ lam : X) (m : ℕ) : Submodule (LaurentPolynomial ℤ) (K0Kar RD k ρ lam) :=
  Submodule.span (LaurentPolynomial ℤ)
    {x | ∃ Z : UKar RD k ρ lam, IsIndec Z ∧ IsLow RD k m Z ∧ x = K0U.cl Z}

variable (RD k) in
/-- **The top step of KL III's proof of Theorem 1.1**: every indecomposable direct summand `Z` of
a sorted `E_{+a} E_{-b} 1_λ {n}` which is not low of level `|a| + |b|` (i.e. of width
`|a| + |b|`) has class in `gammaImg + lowSpanU (|a| + |b|)`. -/
def TopHyp (ρ lam : X) : Prop :=
  ∀ (a b : List I) (hab : wt RD lam (ups a ++ dns b) = ρ) (n : ℤ) (Z : UKar RD k ρ lam),
    IsIndec Z → (∃ (f : Z ⟶ nfObj RD k ρ lam (ups a ++ dns b) hab n)
      (g : nfObj RD k ρ lam (ups a ++ dns b) hab n ⟶ Z), f ≫ g = 𝟙 Z) →
    ¬ IsLow RD k (a.length + b.length) Z →
    K0U.cl Z ∈ gammaImg RD k lam ρ ⊔ lowSpanU RD k ρ lam (a.length + b.length)

variable [Finite I] (hSL : SimplyLaced C)
include hSL

/-- **Induction on the width**: under `TopHyp`, the class of every indecomposable which is low of
level `m` lies in the image of `γ`. -/
theorem cl_mem_gammaImg_of_isLow {ρ lam : X} (hT : TopHyp RD k ρ lam) :
    ∀ (m : ℕ) (Z : UKar RD k ρ lam), IsIndec Z → IsLow RD k m Z → K0U.cl Z ∈ gammaImg RD k lam ρ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro Z hZ hlow
    obtain ⟨w, hw, n, hlt, f, g, hfg⟩ := hlow
    obtain ⟨a, b, hab, n', hle, -, f', g', h'⟩ := exists_retract_sorted_of_retract hSL hZ f g hfg
    by_cases hl : IsLow RD k (a.length + b.length) Z
    · exact ih _ (by omega) Z hZ hl
    · have htop := hT a b hab n' Z hZ ⟨f', g', h'⟩ hl
      have hlowle : lowSpanU RD k ρ lam (a.length + b.length) ≤ gammaImg RD k lam ρ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨Q, hQ, hQl, rfl⟩
        exact ih _ (by omega) Q hQ hQl
      exact (sup_le le_rfl hlowle) htop

/-- Under `TopHyp`, **the class of every indecomposable 1-morphism of `U̇(λ, ρ)` lies in the image
of `γ`**. -/
theorem cl_mem_gammaImg_of_topHyp {ρ lam : X} (hT : TopHyp RD k ρ lam) {Z : UKar RD k ρ lam}
    (hZ : IsIndec Z) : K0U.cl Z ∈ gammaImg RD k lam ρ := by
  obtain ⟨w, h, n, f, g, hfg⟩ := exists_retract_nfObj hSL hZ
  exact cl_mem_gammaImg_of_isLow hSL hT (w.length + 1) Z hZ ⟨w, h, n, by omega, f, g, hfg⟩

/-- Under `TopHyp`, `gammaImg = ⊤`. -/
theorem gammaImg_eq_top_of_topHyp {ρ lam : X} (hT : TopHyp RD k ρ lam) :
    gammaImg RD k lam ρ = ⊤ := by
  rw [eq_top_iff, ← (indecBasisU (k := k) hSL ρ lam).span_eq, Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  rw [indecBasisU_apply]
  exact cl_mem_gammaImg_of_topHyp hSL hT b.isIndec_rep

/-- `γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` is surjective iff its image `gammaImg` is everything. -/
theorem gammaUA'_surjective_iff (lam ρ : X) :
    Function.Surjective (gammaUA' (RD := RD) (k := k) hSL lam ρ) ↔ gammaImg RD k lam ρ = ⊤ := by
  constructor
  · intro hs
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨⟨y, f, rfl⟩, hy⟩ := hs x
    rw [gammaUA'_apply] at hy
    exact ⟨f, hy⟩
  · intro htop x
    obtain ⟨f, hf⟩ := (eq_top_iff.1 htop) (Submodule.mem_top (x := x))
    exact ⟨⟨dpComb lam ρ f, LinearMap.mem_range_self _ _⟩, by rw [gammaUA'_apply]; exact hf⟩

/-- **KL III Theorem 1.1 (surjectivity of `γ`), conditional on the top step `TopHyp`.** -/
theorem gammaUA'_surjective_of_topHyp {lam ρ : X} (hT : TopHyp RD k ρ lam) :
    Function.Surjective (gammaUA' (RD := RD) (k := k) hSL lam ρ) :=
  (gammaUA'_surjective_iff hSL lam ρ).2 (gammaImg_eq_top_of_topHyp hSL hT)

end Width

end Categorification.KL3.Diagram
