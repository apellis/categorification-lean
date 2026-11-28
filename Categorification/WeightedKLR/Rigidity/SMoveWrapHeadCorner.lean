/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtCoevaluationTop

/-!
# The wrap corner of the head of the wrap projective

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Lemma 7.3 and §7.3, proof of Proposition 7.22, gap (c), the normalization of the `Tor₀` of the
diagonal pair. Let `d` be a divided word with expansion `d̂`, `z₀ ∈ R^{λ₁}(d̂)` its reflected
divided-power idempotent and `L` the head of the wrap projective `wrapIdem z₀ · T` (the quotient
by the images of the cut projectives), a left module through the horizontal reflection. Under the
hypotheses of Lemma 7.3 in the form of `coevaluationTrace_eq_iff_isSimpleModule_wrapIdem`
(the second red strand's cyclotomic relation on the last black strand, every nonzero element of
`z₀ R^{λ₁}(d̂)` generates `z₀`, and `z₀ R^{λ₁}(d̂) z₀ = k z₀`), the vectors of `L` fixed by the
loading idempotent of the expanded wrap loading `(red₁ d̂ red₂)` have dimension `∏ nₐ!`:

  `dim e(red₁ d̂ red₂) L = ∏ nₐ!`

(`finrank_fixedSubspace_flipLeft_wrapHead_wrap`). The proof: `e(red₁ d̂ red₂)` is a sum of
`∏ nₐ!` orthogonal copies of the reflected wrap idempotent of `z₀` (`exists_isSplitting_wrap`),
and the latter fixes a line of `L` (`finrank_fixedSubspace_flipLeft_wrapHead`). This is the
expanded-word form of the normalization in Webster's proof that `e(𝐢_λ)` has one-dimensional
image in the simple head. No route hypotheses beyond those listed.

## Main results

* `finrank_fixedSubspace_flipLeft_wrapHead_wrap`.
-/

universe v

open CategoryTheory Abelian Limits MulOpposite

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TwoRedErase

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I : Type} {k : Type} [DecidableEq I] [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 2 → I →₀ ℕ) (d : List (I × ℕ))

local notation "νᵈ" => (expandDiv d : Multiset I)
local notation "z₀" => CycKLR.mk k Q (fun i => Polynomial.X ^ Λ 0 i) (expandDiv d : Multiset I)
  (hflip (divIdem (Seq.ofList (expandDiv d) rfl) (blocksDiv d 0)))

/-- **The expanded wrap corner of the head of the wrap projective** (Webster,
arXiv:1309.3796v3, §7.1, Lemma 7.3; §7.3, proof of Proposition 7.22, normalization of the
`Tor₀` of the diagonal pair): the vectors of `L = flipLeft (wrapIdem z₀ · T / trace of cuts)`
fixed by `e(red₁ d̂ red₂)` have dimension `∏ nₐ!`, under the hypotheses of
`finrank_fixedSubspace_flipLeft_wrapHead`. -/
theorem finrank_fixedSubspace_flipLeft_wrapHead_wrap (hR : LastDotRelation Q Λ νᵈ)
    (hne : z₀ ≠ 0)
    (hgen : ∀ y : CycKLR k Q (fun i => Polynomial.X ^ Λ 0 i) νᵈ, z₀ * y = y → y ≠ 0 →
      ∃ c, y * c = z₀)
    (hscalar : ∀ x : CycKLR k Q (fun i => Polynomial.X ^ Λ 0 i) νᵈ, z₀ * x * z₀ = x →
      ∃ c : k, x = c • z₀) :
    Module.finrank k (fixedSubspace (k := k)
      (flipLeft Q Λ νᵈ (rIdeal (wrapIdem Q Λ νᵈ z₀) ⧸ coevaluationTrace (cutIdem Q Λ νᵈ)))
      (loadingIdem Q Λ (wrap νᵈ (Seq.ofList (expandDiv d) rfl)) (wrap_ordered νᵈ _))) =
      (d.map fun q => q.2.factorial).prod := by
  classical
  have hz₀ := isIdempotentElem_wrapHeadIdem Q Λ d
  set W := wrapIdem Q Λ νᵈ z₀ with hW
  have he : IsIdempotentElem W := by rw [IsIdempotentElem, hW, wrapIdem_mul, hz₀.eq]
  have hfe : IsIdempotentElem (tensorFlip W) := by
    rw [IsIdempotentElem, ← tensorFlip_mul, he.eq]
  set M := flipLeft Q Λ νᵈ (rIdeal W ⧸ coevaluationTrace (cutIdem Q Λ νᵈ))
  obtain ⟨J₂, _, _, a, b, hS, hc₂⟩ := exists_isSplitting_wrap Q Λ d
  have E₃ := Limits.Bicone.homLinearEquiv (R := k) (lIdealBiconeIsBilimit hS) M
  have E₄ := LinearEquiv.piCongrRight fun _ : J₂ => lIdealHomEquiv (k := k) hfe M
  have E₀ := lIdealHomEquiv (k := k)
    (isIdempotentElem_mk_e (wrap νᵈ (Seq.ofList (expandDiv d) rfl)) (wrap_ordered νᵈ _)) M
  have hfin := finrank_fixedSubspace_flipLeft_wrapHead Q Λ νᵈ hR z₀ hz₀ hne hgen hscalar
  have : FiniteDimensional k (fixedSubspace (k := k) M (tensorFlip W)) :=
    Module.finite_of_finrank_eq_succ hfin
  rw [(E₀.symm.trans (E₃.trans E₄)).finrank_eq, Module.finrank_pi_fintype, hfin,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hc₂]

end Categorification.Stendhal
