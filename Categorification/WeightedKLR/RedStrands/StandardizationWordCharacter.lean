/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StandardizationProductTest
import Categorification.WeightedKLR.RedStrands.PrefixStandardCharacter
import Categorification.WeightedKLR.RedStrands.CyclotomicMaskTests

set_option backward.isDefEq.respectTransparency false

/-!
# Word characters of standardizations

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5,
proof of Proposition 5.6. The standardization `S(X ⊠ Z)` of a graded module `X` over the
algebra of the first `ℓ` red strands and a graded module `Z` over the cyclotomic quotient of
the last red strand has a word character determined by those of `X` and `Z`.

Here the word character of a module `M` is the family of Laurent polynomials
`gdim e(w) M` over the ordinary loadings `e(w)` of tensor words `w`. If the word characters of
`X` and `Z` are the values of linear functionals `f` and `g` on the corresponding ordinary
tensor vectors (and these functionals vanish on words of other black content), then the word
character of `S(X ⊠ Z)` is the value of `f ⊗ g` on the ordinary tensor vector of the full word.
This is Theorem 4.38's product test (`standardizationTestAt_word`) for arbitrary inputs; the
masked words of each surviving shuffle are reduced to ordinary loadings of the two factors.

## Main results

* `standardizationTestAt_word_of_wordCharacters`
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR KLRAlgebra Categorification.Graded QuantumGroup KL2 LieLean LieLean.QuantumGroup
open LieLean.QuantumGroup.GrandLoop LusztigF
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin (ℓ+1) → I →₀ ℕ) (C : CartanDatum I)
  (hQ : IsRouquierQ C Q) (θ β : Multiset I)
private abbrev grading :=
  stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
private abbrev symmetricQ : KLRSymm Q := fun i j h => (hQ.symm i j h).symm
variable (X : GFin (tensorProductGrade (restrictRedGrading Q Λ (grading Λ C hQ)) θ))
  (Z : GFin (CycKLR.grade (restrictBlackGrading Q Λ (grading Λ C hQ)) (Λ (Fin.last ℓ)) β))
variable {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y}
  (wt : Fin (ℓ+1) → Dom R)
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
private local instance wordCharacterVNeZero : NeZero v := ⟨RatFunc.X_ne_zero⟩
local notation "wt₀" => fun j : Fin ℓ => wt (Fin.castSucc j)
local notation "V₀" => TensorSpace (fun j : Fin ℓ => wt (Fin.castSucc j))
local notation "V₁" => IrreducibleModule R v (Subtype.val (wt (Fin.last ℓ)))
local notation "A₁" => fun i => Algebra.lsmul L L V₁ (F R v i)
local notation "hwv₁" => IrreducibleModule.hwv R v (Subtype.val (wt (Fin.last ℓ)))
local notation "π" => CycKLR.mk k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)

private theorem prefixValue_of_word (f : V₀ →ₗ[L] L)
    (hX : ∀ p : TensorWordAt ℓ θ, integralLaurentEval (gdimPoly (Graded.idem X.grading
      (ordinaryLoadingIdem (Q := Q) (Λ ∘ Fin.castSucc) θ p))) = f (barOrdinaryWord p.1 wt₀))
    (p : TensorWord I ℓ) (t : Seq ((stendhalWeight ℓ θ).map (addRedColor ℓ)))
    (hc : p.content.toMultiset = θ)
    (ht : List.ofFn t.1 = (expandDiv p.blocks).map (addRedColor ℓ)) :
    integralLaurentEval (gdimPoly (Graded.idem X.grading
      (parabolicPrefixProjection Q Λ θ (e t)))) = f (barOrdinaryWord p wt₀) := by
  subst hc
  rw [parabolicPrefixProjection_of_word (Q := Q) Λ p t ht]
  exact hX ⟨p, rfl⟩

/-- **Word character of a standardization** (Webster, arXiv:1309.3796v2, §5, proof of
Proposition 5.6, via the product test of Theorem 4.38). If the graded dimensions of `X` at the
ordinary loadings of the earlier words are given by a functional `f`, and those of `Z` at the
cyclotomic word idempotents by a functional `g`, each vanishing on words of other black
content, then the graded dimension of `S(X ⊠ Z)` at the ordinary loading of every tensor word
`w` is `(f ⊗ g)` of the ordinary tensor vector of `w`. -/
theorem standardizationTestAt_word_of_wordCharacters (f : V₀ →ₗ[L] L) (g : V₁ →ₗ[L] L)
    (highest : ∀ i, (wt (Fin.last ℓ)).1 (R.coroot i) = (Λ (Fin.last ℓ) i : ℤ))
    (hX : ∀ p : TensorWordAt ℓ θ, integralLaurentEval (gdimPoly (Graded.idem X.grading
      (ordinaryLoadingIdem (Q := Q) (Λ ∘ Fin.castSucc) θ p))) = f (barOrdinaryWord p.1 wt₀))
    (hX0 : ∀ p : TensorWord I ℓ, p.content.toMultiset ≠ θ → f (barOrdinaryWord p wt₀) = 0)
    (hZ : ∀ (s : List I) (h : (s : Multiset I) = β), integralLaurentEval (gdimPoly
      (Graded.idem Z.grading (π β (e (Seq.ofList s h))))) = g (ordinarySuffixOp A₁ s hwv₁))
    (hZ0 : ∀ s : List I, (s : Multiset I) ≠ β → g (ordinarySuffixOp A₁ s hwv₁) = 0)
    (ν : Multiset I) (w : TensorWordAt (ℓ+1) ν) :
    integralLaurentEval (gdimPoly (Graded.idem (standardizationTestAt Λ (grading Λ C hQ) θ β
      (symmetricQ C hQ) X Z ν).grading (ordinaryLoadingIdem (Q := Q) Λ ν w))) =
        factorTensorTest (fun _ : Unit => f) (fun _ : Unit => g) () ()
          (tensorSplitLast wt (barOrdinaryWord w.1 wt)) := by
  refine standardizationTestAt_word Λ C hQ θ β X Z wt (fun _ : Unit => f)
    (fun _ : Unit => g) () () highest ν w ?_ ?_ ?_ ?_
  · intro s hw u
    let c := ordinaryShuffleEquiv w.1 s hw u
    have hc : (prefixMaskWord w.1 c.1).content.toMultiset = θ :=
      (prefixMaskContent_iff w.1 θ c.1).mp c.2.1
    exact prefixValue_of_word Λ C hQ θ X wt f hX _ _ hc
      (ordinaryShuffleEquiv_left_word w.1 s hw u)
  · intro s hw u
    let c := ordinaryShuffleEquiv w.1 s hw u
    let l := finalMaskLetters w.1 c.1
    have h : (l : Multiset I) = β := (finalMaskContent_iff w.1 β c.1).mp c.2.2
    have he : u.1.split.2 = Seq.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
        (SingleRed.insertWord β (Seq.ofList l h)) := by
      apply Subtype.ext
      apply List.ofFn_injective
      rw [lastInput_labels, Seq.ofFn_ofList l h]
      exact ordinaryShuffleEquiv_right_word w.1 s hw u
    rw [he, parabolicLastCyclotomic_e]
    exact hZ l h
  · intro c hc
    exact hX0 _ fun he => hc ((prefixMaskContent_iff w.1 θ c).mpr he)
  · intro c hc
    exact hZ0 _ fun he => hc ((finalMaskContent_iff w.1 β c).mpr he)

end Categorification.Stendhal.FirstWeight
