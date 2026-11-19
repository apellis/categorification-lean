/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLRedNegligibleIdeal
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverRedDotAction

/-!
# Centrality of the coloured dot sums in the cover

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. Over a field, a family of Rouquier
parameters factors as `Q a b = P b a · P a b(v, u)` with nonzero factors
(`exists_factor_of_isRouquierQ`): choose an order on the colours and put the whole polynomial
on one side of each pair. The faithful polynomial representation then makes each coloured dot
sum central in the KLR algebra, so the hypothesis `CoverDotCentral` holds for every family of
Rouquier parameters (`coverDotCentral`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open QuantumGroup KLR MvPolynomial

universe u v

/-- Over a field, Rouquier parameters factor as `Q a b = P b a · P a b(v, u)` off the diagonal,
with nonzero factors. -/
theorem exists_factor_of_isRouquierQ {J : Type u} {k : Type v} [Field k] {D : CartanDatum J}
    {S : J → J → MvPolynomial (Fin 2) k} (hS : IsRouquierQ D S) :
    ∃ P : J → J → MvPolynomial (Fin 2) k,
      (∀ a b, a ≠ b → S a b = P b a * rename ![1, 0] (P a b)) ∧ ∀ a b, a ≠ b → P a b ≠ 0 := by
  classical
  let r : J ↪ Cardinal.{u} := embeddingToCardinal
  refine ⟨fun a b => if r a < r b then 1 else S b a, fun a b hab => ?_, fun a b hab => ?_⟩
  · by_cases h : r a < r b
    · simp [h, not_lt_of_gt h]
    · have h' : r b < r a := lt_of_le_of_ne (not_lt.mp h) fun e => hab (r.injective e.symm)
      simp only [h, h', ↓reduceIte, one_mul]
      exact (hS.symm b a hab.symm).symm
  · dsimp only
    split_ifs
    · exact one_ne_zero
    · intro h0
      have hu := hS.unit_coeff b a hab.symm
      simp only [h0, AddMonoidAlgebra.coeff_zero] at hu
      exact not_isUnit_zero hu

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}

/-- The coloured dot sums are central in the cyclotomic KLR algebras of the extended datum,
for every family of Rouquier parameters over a field. -/
theorem coverDotCentral (hQ : IsRouquierQ C Q) : CoverDotCentral Λ C Q := by
  obtain ⟨P, hSP, hP⟩ := exists_factor_of_isRouquierQ (isRouquierQ_cyclotomicCoverQ C Λ Q hQ)
  intro δ c z
  exact cyclotomicColourDot_commute _ _ hSP hP c z

end Categorification.Stendhal
