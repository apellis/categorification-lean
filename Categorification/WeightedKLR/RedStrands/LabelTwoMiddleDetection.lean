/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleDots
import Categorification.WeightedKLR.RedStrands.ParabolicStandardUpper
import Categorification.WeightedKLR.Rigidity.SingleBlackExtremal
import Categorification.WeightedKLR.RedStrands.FirstWeightBoundary
import Categorification.WeightedKLR.RedStrands.SingleBlack

/-!
# Separated factors detect the label-two middle corner

Webster, arXiv:1309.3796v2, §8.2, preceding Proposition 8.4.
The diagrammatic middle standard acts on the parabolic standardization of
the regular two-factor module. The middle corner recovers both factors
via the identity shuffle.
-/

noncomputable section

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra
open scoped TensorProduct Polynomial

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "oneBlack" => ({()} : Multiset Unit)
local notation "q₀" => parameter k
local notation "wt₂" => weights
local notation "A" => TensorProductAlgebra k q₀ wt₂ (oneBlack + oneBlack)
local notation "D" => parabolicFactorAlgebra q₀ wt₂ oneBlack oneBlack
local notation "V" => ParabolicStandard q₀ wt₂ oneBlack oneBlack D
local notation "S" => Standard k
local notation "E" => seqIdem q₀ wt₂ loading loading_ordered
local notation "g" => leftStandardUnit q₀ wt₂ loading loading_ordered
local notation "U" => parabolicStandardUnit q₀ wt₂ oneBlack oneBlack D
local notation "wt₁" => wt₂ ∘ (Fin.castSucc : Fin 1 → Fin 2)
local notation "u" => (default : Seq oneBlack)
local notation "t" => SingleRed.insertWord oneBlack u
local notation "P" => stendhalQ q₀ wt₂
local notation "α" => Multiset.map (addRedColor 1) (stendhalWeight 1 oneBlack)
local notation "lc" => Sum.map (id : Unit → Unit) (fun _ : Fin 1 => Fin.last 1)
local notation "δ" => Multiset.map lc (stendhalWeight 1 oneBlack)
local notation "H" => parabolicInputWeights_add (ℓ := 1) oneBlack oneBlack

private theorem prefixOrdered : IsRedOrdered t := SingleRed.ordered oneBlack t

private theorem middleTwoPiece : twoPieceLoading oneBlack oneBlack t u = loading := by decide +kernel

private theorem prefixIdem :
    TensorProductAlgebra.mk q₀ wt₁ oneBlack (StendhalAlgebra.e t prefixOrdered) = 1 := by
  have h := oneBlack_extremal_loadingIdem_eq_one q₀ wt₁ ()
  change SingleRed.mk q₀ wt₁ oneBlack (StendhalAlgebraAllOrders.e t) = 1 at h
  rw [← h]
  apply congrArg (TensorProductAlgebra.mk q₀ wt₁ oneBlack)
  apply Subtype.ext
  rfl

private abbrev cutTensor : TensorKLR P α δ :=
  e (Seq.map (addRedColor 1) t) ⊗ₜ[k] e (Seq.map lc t)

private abbrev affineElement (a : KLRAlgebra k P (α + δ)) : A :=
  TensorProductAlgebra.mk q₀ wt₂ (oneBlack + oneBlack) (orderProjection q₀ wt₂ (oneBlack + oneBlack)
    (StendhalAlgebraAllOrders.ofKLR k q₀ wt₂ (oneBlack + oneBlack) (castKLR P H a)))

private theorem cutTensor_proj :
    parabolicInputMap q₀ wt₂ oneBlack oneBlack (cutTensor k) = (1 : D) := by
  rw [cutTensor, parabolicInputMap, Algebra.TensorProduct.map_tmul,
    redSubfamilyProjection_e q₀ wt₂ Fin.castSucc (Fin.castSucc_injective 1) oneBlack t prefixOrdered,
    parabolicLastCyclotomic_e q₀ wt₂ oneBlack u, prefixIdem, e_single, map_one,
    ← Algebra.TensorProduct.one_def]

private theorem cutTensor_actual :
    affineElement k (concat P α δ (cutTensor k)) = E := by
  unfold affineElement cutTensor
  rw [concat_e_tmul_e, castKLR_e]
  apply congrArg (TensorProductAlgebra.mk q₀ wt₂ (oneBlack + oneBlack))
  apply Subtype.ext
  have hh : Seq.cast H ((Seq.map (addRedColor 1) t).append (Seq.map lc t)) = loading :=
    middleTwoPiece
  change StendhalAlgebraAllOrders.e _ * _ = StendhalAlgebraAllOrders.e loading
  rw [hh, StendhalAlgebraAllOrders.e_mul_redOrderedIdem, ite_eq_left loading_ordered]

private theorem parameterSymm : KLRSymm q₀ := fun a b h => (h (Subsingleton.elim a b)).elim

local notation "ρ" => parabolicStandardAction q₀ wt₂ oneBlack oneBlack D (parameterSymm k)

private instance : Module A V := Module.compHom V (ρ).toRingHom

private instance : IsScalarTower k A V where
  smul_assoc c a x := by
    change ρ (c • a) x = c • ρ a x
    rw [map_smul, LinearMap.smul_apply]

private theorem prefixHigher_eq_zero (s : Seq (stendhalWeight 1 oneBlack)) (hs : IsRedOrdered s)
    (hh : StendhalLT t s) :
    TensorProductAlgebra.mk q₀ wt₁ oneBlack (StendhalAlgebra.e s hs) = 0 := by
  by_cases hv : IsViolated s
  · change (StendhalAlgebra.violatedIdeal k q₀ wt₁ oneBlack).ringCon.mk' _ = 0
    rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
    exact TwoSidedIdeal.subset_span ⟨s, hs, hv, rfl⟩
  · obtain ⟨r, hr⟩ := (FirstWeight.boundaryEquiv () 1).surjective ⟨s, hs, hv⟩
    have hr0 : r = 0 := Subsingleton.elim _ _
    have hx : s = t := ((congrArg Subtype.val hr).symm.trans (by
      rw [hr0]
      apply Subtype.ext
      funext j
      fin_cases j <;> rfl))
    subst s
    exact (hh.2 hh.1).elim

private theorem higherZero (s : Seq (stendhalWeight 2 (oneBlack + oneBlack))) (hs : IsRedOrdered s)
    (hlt : StendhalLT loading s) :
    ρ (seqIdem q₀ wt₂ s hs) = 0 := by
  have hlt' : StendhalLT (twoPieceLoading oneBlack oneBlack t u) s := middleTwoPiece.symm ▸ hlt
  apply parabolicStandardAction_upper_eq_zero q₀ wt₂ oneBlack oneBlack (N := D) (parameterSymm k) t u _ s hs hlt'
  intro c hc h n
  rw [prefixHigher_eq_zero k c hc h, TensorProduct.zero_tmul]
  exact zero_mul n

private theorem unit_fixed (n : D) : E • (U n) = U n := by
  have h := parabolicStandardAction_concat_unit q₀ wt₂ oneBlack oneBlack D (parameterSymm k) (cutTensor k) n
  change ρ (affineElement k (concat P α δ (cutTensor k))) (U n) = _ at h
  have hr : parabolicInputMap q₀ wt₂ oneBlack oneBlack (cutTensor k) • n = n :=
    (congrArg (fun a : D => a • n) (cutTensor_proj k)).trans (one_smul D n)
  have hl := congrArg (fun a : A => ρ a (U n)) (cutTensor_actual k)
  exact hl.symm.trans (h.trans (congrArg U hr))

/-- The cyclic map from the actual middle standard to the induced
regular separated test module. -/
def testModuleMap : S →ₗ[A] V :=
  leftStandardLift (Q := q₀) (Λ := wt₂) loading loading_ordered (U (1 : D))
    (fun s hs a hlt => by
      rw [mul_smul]
      change ρ (seqIdem q₀ wt₂ s hs) _ = 0
      rw [higherZero k s hs hlt, LinearMap.zero_apply])

/-- The diagrammatic generator maps to the unit in the identity shuffle. -/
theorem testModuleMap_generator : testModuleMap k g = U (1 : D) :=
  leftStandardLift_unit (Q := q₀) (Λ := wt₂) loading loading_ordered _
    (unit_fixed k _) _

private def testFixed : fixSub k S E →ₗ[k] LinearMap.range U where
  toFun x := ⟨testModuleMap k x.val, by
    have h : E • (testModuleMap k x.val) = testModuleMap k x.val := by
      rw [← map_smul, show E • x.val = x.val from x.property]
    have q := parabolicStandardAction_concat_mem_range q₀ wt₂ oneBlack oneBlack D (parameterSymm k)
      (cutTensor k) (testModuleMap k x.val)
    change ρ (affineElement k (concat P α δ (cutTensor k))) _ ∈ LinearMap.range U at q
    rw [cutTensor_actual] at q
    change E • (testModuleMap k x.val) ∈ LinearMap.range U at q
    rwa [h] at q⟩
  map_add' x y := Subtype.ext ((testModuleMap k).map_add x.val y.val)
  map_smul' c x := Subtype.ext (((testModuleMap k).restrictScalars k).map_smul c x.val)

private theorem affineOnGenerator (a : TensorKLR P α δ) :
    testModuleMap k (affineElement k (concat P α δ a) • g) =
      U (parabolicInputMap q₀ wt₂ oneBlack oneBlack a) := by
  let z := affineElement k (concat P α δ a)
  have hs := (testModuleMap k).map_smul z g
  have hgen := congrArg (fun m : V => z • m) (testModuleMap_generator k)
  have h := parabolicStandardAction_concat_unit q₀ wt₂ oneBlack oneBlack D (parameterSymm k) a (1 : D)
  change z • (U (1 : D)) = _ at h
  have hr : parabolicInputMap q₀ wt₂ oneBlack oneBlack a • (1 : D) =
      parabolicInputMap q₀ wt₂ oneBlack oneBlack a := mul_one _
  exact hs.trans (hgen.trans (h.trans (congrArg U hr)))

private theorem cutFixed_mul (w : S) : E • (E • w) = E • w := by
  rw [smul_smul, seqIdem_mul_self]

set_option backward.isDefEq.respectTransparency false in
private theorem testFixed_surj : Function.Surjective (testFixed k) := by
  rintro ⟨y, n, rfl⟩
  have hsurj : Function.Surjective (parabolicInputMap q₀ wt₂ oneBlack oneBlack) :=
    Algebra.TensorProduct.map_surjective _ _ (parabolicPrefixProjection_surjective q₀ wt₂ oneBlack)
      (parabolicLastCyclotomic_surjective q₀ wt₂ oneBlack)
  obtain ⟨a, ha⟩ := hsurj n
  let w : S := affineElement k (concat P α δ a) • g
  refine ⟨⟨E • w, cutFixed_mul k w⟩, Subtype.ext ?_⟩
  change testModuleMap k (E • w) = U n
  have hw : testModuleMap k w = U n := (affineOnGenerator k a).trans (congrArg U ha)
  exact ((testModuleMap k).map_smul E w).trans
    ((congrArg (fun m : V => E • m) hw).trans (unit_fixed k n))

/-- The actual middle standard endomorphisms detect the full regular
tensor product of its two one-black factors. -/
def standardEnd_detectFactors : Module.End A S →ₗ[k] D :=
  (LinearEquiv.ofInjective U
    (parabolicStandardUnit_injective q₀ wt₂ oneBlack oneBlack D (parameterSymm k))).symm.toLinearMap.comp
      ((testFixed k).comp (leftStandardEndEquivFixed q₀ wt₂ loading loading_ordered).toLinearMap)

/-- The endomorphism-algebra calculation has no loss of dimension from
the violated or higher-cut relations at the separated factor level. -/
theorem standardEnd_detectFactors_surjective : Function.Surjective (standardEnd_detectFactors k) :=
  (LinearEquiv.ofInjective U
    (parabolicStandardUnit_injective q₀ wt₂ oneBlack oneBlack D (parameterSymm k))).symm.surjective.comp
      ((testFixed_surj k).comp (leftStandardEndEquivFixed q₀ wt₂ loading loading_ordered).surjective)

/-- The detected factor coordinate of a middle-fixed vector is its
coefficient in the identity shuffle. -/
theorem testModuleMap_fixed (x : fixSub k S E) :
    testModuleMap k x.val =
      U (standardEnd_detectFactors k
        ((leftStandardEndEquivFixed q₀ wt₂ loading loading_ordered).symm x)) := by
  unfold standardEnd_detectFactors
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  change (testFixed k x).val = _
  exact (congrArg Subtype.val ((LinearEquiv.ofInjective U
    (parabolicStandardUnit_injective q₀ wt₂ oneBlack oneBlack D (parameterSymm k))).apply_symm_apply
      (testFixed k x))).symm

private theorem adjoinRootPow_finrank (n : ℕ) :
    Module.finrank k (AdjoinRoot ((Polynomial.X : Polynomial k)^n)) = n := by
  change Module.finrank k (k[X] ⧸ Ideal.span {((Polynomial.X : Polynomial k)^n)}) = n
  rw [finrank_quotient_span_eq_natDegree, Polynomial.natDegree_X_pow]

private abbrev leftFactor := TensorProductAlgebra k q₀ wt₁ oneBlack
private abbrev rightFactor := CycKLR k q₀
  (fun j => (Polynomial.X : Polynomial k) ^ wt₂ (Fin.last 1) j) oneBlack

private theorem leftFactor_finrank : Module.finrank k (leftFactor k) = 2 :=
  ((SingleBlack.oneBlackOneRedEquiv () q₀ wt₁).toLinearEquiv.finrank_eq.trans
    (adjoinRootPow_finrank k (wt₁ 0 ()))).trans Finsupp.single_eq_same

private theorem rightFactor_finrank : Module.finrank k (rightFactor k) = 2 :=
  ((cyclotomicSingleEquiv q₀ () (fun j => (Polynomial.X : Polynomial k) ^ wt₂ (Fin.last 1) j)).toLinearEquiv.finrank_eq.trans
    (adjoinRootPow_finrank k (wt₂ (Fin.last 1) ()))).trans Finsupp.single_eq_same

private theorem finrank_tensor_four {M N : Type} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (hm : Module.finrank k M = 2) (hn : Module.finrank k N = 2) :
    Module.finrank k (M ⊗[k] N) = 4 := by
  rw [Module.finrank_tensorProduct, hm, hn]

/-- The two separated one-black algebras have dimensions two and two. -/
theorem separatedFactors_finrank : Module.finrank k D = 4 :=
  finrank_tensor_four k (leftFactor_finrank k) (rightFactor_finrank k)

end Categorification.Stendhal.LabelTwo
