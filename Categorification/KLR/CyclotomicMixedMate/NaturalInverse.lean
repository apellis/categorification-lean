/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.Square

/-!
# Naturality of the removable-colour mixed inverse

Both comparison directions, the original mate equivalence and its actual inverse
are natural for arbitrary module morphisms, with the inversion hypotheses unchanged.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.MixedComparison
open MixedMate
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  (γ : Multiset I) (i j : I)
local notation "A" => CycKLR k Q a ((Singleton.singleton j : Multiset I) + γ)
local notation "C" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)
variable (M M' : Type w) [AddCommGroup M] [Module k M]
  [Module (CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)) M]
  [IsScalarTower k (CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)) M]
  [AddCommGroup M'] [Module k M']
  [Module (CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)) M']
  [IsScalarTower k (CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)) M']

/-- The concrete upper comparison is natural for all morphisms, not just free modules. -/
theorem upperComparison_natural (f : M →ₗ[C] M') (z : Target Q a γ i j M) :
    upperComparison Q a γ i j M' (mateTargetMap Q a γ i j M M' f z) =
      BalancedTensor.mapRight f (upperComparison Q a γ i j M z) := by
  have h : ∀ t : Ind Q j a ({i} + γ) M,
      @Eq (UpperTensor Q a γ i j M')
        ((cutTensor Q a γ i j M').toFun ((BalancedTensor.mapRight f).toFun t))
        ((BalancedTensor.mapRight f).toFun ((cutTensor Q a γ i j M).toFun t)) := by
    intro t
    simp only [LinearMap.toFun_eq_coe]
    induction t using BalancedTensor.induction_on with
    | zero => simp only [map_zero]
    | add s t hs ht => simp only [map_add, hs, ht]
    | tmul x m => simp only [BalancedTensor.mapRight_tmul, cutTensor_tmul]
  exact h z.1

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (hij : i ≠ j) (hsym : KLRSymm Q)

theorem tensorForward_natural (f : M →ₗ[C] M') :
    (BalancedTensor.mapRight f).comp (tensorForward Q a γ i j hPQ hP hij hsym M) =
      (tensorForward Q a γ i j hPQ hP hij hsym M').comp (BalancedTensor.mapRight f) := by
  apply BalancedTensor.extB
  intro z m
  rfl

theorem tensorInverse_natural (f : M →ₗ[C] M') :
    (BalancedTensor.mapRight f).comp (tensorInverse Q a γ i j hPQ hP hij hsym M) =
      (tensorInverse Q a γ i j hPQ hP hij hsym M').comp (BalancedTensor.mapRight f) := by
  apply BalancedTensor.extB
  intro z m
  rfl

/-- The equivalence's forward naturality is that of the original ordinary mate. -/
theorem originalMateEquiv_natural (f : M →ₗ[C] M') :
    (mateTargetMap Q a γ i j M M' f).comp
      (originalMateEquiv Q a γ i j hPQ hP hij hsym M).toLinearMap =
        (originalMateEquiv Q a γ i j hPQ hP hij hsym M').toLinearMap.comp
          (mateSourceMap Q a γ i j M M' f) := by
  rw [originalMateEquiv_eq_mate, originalMateEquiv_eq_mate]
  exact mate_natural Q a γ i j M M' f

/-- The actual inverse is natural on arbitrary original cyclotomic module maps. -/
theorem mateInverse_natural (f : M →ₗ[C] M') :
    (mateSourceMap Q a γ i j M M' f).comp (mateInverse Q a γ i j hPQ hP hij hsym M) =
      (mateInverse Q a γ i j hPQ hP hij hsym M').comp (mateTargetMap Q a γ i j M M' f) := by
  apply LinearMap.ext
  intro z
  apply (originalMateEquiv Q a γ i j hPQ hP hij hsym M').injective
  change (originalMateEquiv Q a γ i j hPQ hP hij hsym M').toLinearMap _ =
    (originalMateEquiv Q a γ i j hPQ hP hij hsym M').toLinearMap _
  rw [originalMateEquiv_eq_mate]
  change mate Q a γ i j M' (mateSourceMap Q a γ i j M M' f
    (mateInverse Q a γ i j hPQ hP hij hsym M z)) =
      mate Q a γ i j M' (mateInverse Q a γ i j hPQ hP hij hsym M'
        (mateTargetMap Q a γ i j M M' f z))
  rw [mate_mateInverse]
  have h := LinearMap.congr_fun (mate_natural Q a γ i j M M' f)
    (mateInverse Q a γ i j hPQ hP hij hsym M z)
  simpa only [LinearMap.coe_comp, Function.comp_apply, mate_mateInverse] using h.symm

end Categorification.KLR.KLRAlgebra.AbsentColour.MixedComparison
