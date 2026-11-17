/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StandardizationMaskComparison
import Categorification.WeightedKLR.RedStrands.StandardizationWordTests

/-!
# The standard module's product test on the whole tensor space

Webster, arXiv:1309.3796v2, §4.7, Theorem 4.38 and (5.10). The word character of a
standard module in the full direct sum is the product of its two factor coordinates
applied to the ordinary tensor word.
-/
noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR KLRAlgebra Categorification.Graded QuantumGroup KL2 LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u
variable {I : Type} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin (ℓ+1) → I →₀ ℕ) (C : CartanDatum I)
  (hQ : IsRouquierQ C Q) (θ β : Multiset I)
private abbrev grading := stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
private abbrev symmetricQ : KLRSymm Q := fun i j h => (hQ.symm i j h).symm
variable (X : GFin (tensorProductGrade (restrictRedGrading Q Λ (grading Λ C hQ)) θ))
  (Z : GFin (CycKLR.grade (restrictBlackGrading Q Λ (grading Λ C hQ)) (Λ (Fin.last ℓ)) β))
variable {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y} (wt : Fin (ℓ+1) → Dom R)
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
private local instance productTestVNeZero : NeZero v := ⟨RatFunc.X_ne_zero⟩
local notation "V₀" => TensorSpace (fun j : Fin ℓ => wt (Fin.castSucc j))
local notation "V₁" => IrreducibleModule R v (Subtype.val (wt (Fin.last ℓ)))

/-- Across all contents the standard test has precisely the factor product coordinate
on every ordinary loading, provided each factor test evaluates its own masked word. -/
theorem standardizationTestAt_word {A B : Type*} (f : A → V₀ →ₗ[L] L) (g : B → V₁ →ₗ[L] L)
    (a : A) (b : B) (highest : ∀ i, (wt (Fin.last ℓ)).1 (R.coroot i) = (Λ (Fin.last ℓ) i : ℤ))
    (ν : Multiset I) (w : TensorWordAt (ℓ+1) ν)
    (hx : ∀ (s : Seq (α+δ)) (hw : List.ofFn s.1 = expandDiv w.1.blocks) u,
      integralLaurentEval (gdimPoly (Graded.idem X.grading (parabolicPrefixProjection Q Λ θ (e u.1.split.1)))) =
        f a (prefixMaskVector w.1 wt (ordinaryShuffleEquiv w.1 s hw u).1))
    (hz : ∀ (s : Seq (α+δ)) (hw : List.ofFn s.1 = expandDiv w.1.blocks) u,
      integralLaurentEval (gdimPoly (Graded.idem Z.grading (parabolicLastCyclotomic Q Λ β (e u.1.split.2)))) =
        g b (finalMaskVector w.1 wt (ordinaryShuffleEquiv w.1 s hw u).1))
    (hf : ∀ c, (maskSubword false (lastRedBlackTags w.1 c) : Multiset _) ≠ α →
      f a (prefixMaskVector w.1 wt c) = 0)
    (hg : ∀ c, (maskSubword true (lastRedBlackTags w.1 c) : Multiset _) ≠ δ →
      g b (finalMaskVector w.1 wt c) = 0) :
    integralLaurentEval (gdimPoly (Graded.idem (standardizationTestAt Λ (grading Λ C hQ) θ β (symmetricQ C hQ) X Z ν).grading
      (ordinaryLoadingIdem (Q := Q) Λ ν w))) =
        factorTensorTest f g a b (tensorSplitLast wt (barOrdinaryWord w.1 wt)) := by
  by_cases h : θ+β = ν
  · subst ν
    obtain ⟨s,ho,hw,he⟩ := exists_ordinaryTestLoading (Q := Q) Λ θ β w
    rw [standardizationTestAt,dite_eq_left rfl,← he]
    exact standardizationWord_eq_factorTensorTest Λ C hQ θ β X Z wt f g a b highest w.1 s ho hw
      (hx s hw) (hz s hw) hf hg
  · rw [standardizationTestAt_of_ne _ _ _ _ _ _ _ h, map_zero]
    exact (factorTensorTest_word_of_content_ne θ β wt f g a b w.1 (fun he => h (he.trans w.2)) hf hg).symm

end Categorification.Stendhal.FirstWeight
