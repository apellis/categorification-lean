/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleStandardEquiv

/-!
# Specialization of the label-two regular factor

Webster, arXiv:1309.3796v2, §8.2. Evaluation on the cyclic middle
generator identifies the middle endomorphism algebra with the
regular parabolic factor algebra. The actual sum element becomes the
dual-number specialization relation in the factor algebra.
-/

noncomputable section
set_option maxHeartbeats 1800000

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "oneBlack" => ({()} : Multiset Unit)
local notation "ν" => oneBlack + oneBlack
local notation "q" => parameter k
local notation "leftWeight" => Multiset.map (addRedColor 1) (stendhalWeight 1 oneBlack)
local notation "lc" => Sum.map (id : Unit → Unit) (fun _ : Fin 1 => Fin.last 1)
local notation "rightWeight" => Multiset.map lc (stendhalWeight 1 oneBlack)
local notation "P" => stendhalQ q weights
local notation "A" => TensorProductAlgebra k q weights ν
local notation "D" => parabolicFactorAlgebra q weights oneBlack oneBlack
local notation "V" => ParabolicStandard q weights oneBlack oneBlack D
local notation "U" => parabolicStandardUnit q weights oneBlack oneBlack D
local notation "S" => Standard k
local notation "B" => Module.End A S
local notation "g" => leftStandardUnit q weights loading loading_ordered
local notation "det" => standardEnd_detectFactors k

private theorem parameterSymmFactor : KLRSymm q :=
  fun a b h => (h (Subsingleton.elim a b)).elim

private abbrev affineConcat (a : TensorKLR P leftWeight rightWeight) : A :=
  tensorOfKLR q weights ν
    (castKLR P (parabolicInputWeights_add (ℓ := 1) oneBlack oneBlack) (concat P leftWeight rightWeight a))

private theorem concat_act_on_unit (a : TensorKLR P leftWeight rightWeight) (n : D) :
    affineConcat k a • U n = U (parabolicInputMap q weights oneBlack oneBlack a * n) :=
  parabolicStandardAction_concat_unit q weights oneBlack oneBlack D (parameterSymmFactor k) a n

/-- Evaluating a middle endomorphism on the cyclic generator reads its factor coordinate. -/
theorem testModuleMap_endomorphism_on_generator (a : B) :
    testModuleMap k (a g) = U (det a) := by
  let ev := leftStandardEndEquivFixed q weights loading loading_ordered
  exact (testModuleMap_fixed k (ev a)).trans
    (congrArg U (congrArg det (ev.symm_apply_apply a)))

private theorem detectFactors_inj : Function.Injective det := by
  intro a b h
  apply leftStandard_hom_ext loading loading_ordered
  apply testModuleMap_injective k
  exact (testModuleMap_endomorphism_on_generator k a).trans ((congrArg U h).trans (testModuleMap_endomorphism_on_generator k b).symm)

private theorem detectFactors_one : det (1 : B) = (1 : D) :=
  parabolicStandardUnit_injective q weights oneBlack oneBlack D (parameterSymmFactor k)
    ((testModuleMap_endomorphism_on_generator k (1 : B)).symm.trans (testModuleMap_generator k))

/-- Evaluation on the factor unit sends composition to the reverse product
of the two regular factor coordinates. -/
theorem standardEnd_detectFactors_mul_reverse (a b : B) :
    det (a * b) = det b * det a := by
  have hsurj : Function.Surjective (parabolicInputMap q weights oneBlack oneBlack) :=
    Algebra.TensorProduct.map_surjective _ _ (parabolicPrefixProjection_surjective q weights oneBlack)
      (parabolicLastCyclotomic_surjective q weights oneBlack)
  obtain ⟨t,ht⟩ := hsurj (det b)
  let z := affineConcat k t
  have hb : b g = z • g := by
    apply testModuleMap_injective k
    calc
      testModuleMap k (b g) = U (det b) := testModuleMap_endomorphism_on_generator k b
      _ = U (parabolicInputMap q weights oneBlack oneBlack t * (1 : D)) :=
        congrArg U ((mul_one _).trans ht).symm
      _ = z • U (1 : D) := (concat_act_on_unit k t 1).symm
      _ = z • testModuleMap k g := congrArg (fun y : V => z • y) (testModuleMap_generator k).symm
      _ = testModuleMap k (z • g) := ((testModuleMap k).map_smul z g).symm
  apply parabolicStandardUnit_injective q weights oneBlack oneBlack D (parameterSymmFactor k)
  calc
    U (det (a * b)) = testModuleMap k (a (b g)) := (testModuleMap_endomorphism_on_generator k (a*b)).symm
    _ = testModuleMap k (a (z • g)) := congrArg (fun w : S => testModuleMap k (a w)) hb
    _ = testModuleMap k (z • a g) := congrArg (testModuleMap k) (a.map_smul z g)
    _ = z • testModuleMap k (a g) := (testModuleMap k).map_smul z (a g)
    _ = z • U (det a) := congrArg (fun w : V => z • w) (testModuleMap_endomorphism_on_generator k a)
    _ = U (parabolicInputMap q weights oneBlack oneBlack t * det a) := concat_act_on_unit k t (det a)
    _ = U (det b * det a) := congrArg (fun n : D => U (n * det a)) ht

private theorem middleEnd_comm (a b : B) : a * b = b * a := by
  let ev := (middleEndomorphismEquiv k).symm
  exact ev.injective ((ev.map_mul a b).trans ((mul_comm _ _).trans (ev.map_mul b a).symm))

/-- The actual endomorphism algebra of the middle standard is the tensor
product of the two regular separated one-black algebras. -/
def middleEndomorphismFactorEquiv : B ≃ₐ[k] D := by
  let f : B →ₐ[k] D :=
    { toFun := det
      map_zero' := (det).map_zero
      map_one' := detectFactors_one k
      map_add' := (det).map_add
      map_mul' a b := (congrArg det (middleEnd_comm k a b)).trans
        (standardEnd_detectFactors_mul_reverse k b a)
      commutes' c := by
        rw [Algebra.algebraMap_eq_smul_one, (det).map_smul, detectFactors_one k]
        exact (Algebra.algebraMap_eq_smul_one c).symm }
  exact AlgEquiv.ofBijective f ⟨detectFactors_inj k, standardEnd_detectFactors_surjective k⟩

theorem middleEndomorphismFactorEquiv_apply (a : B) :
    middleEndomorphismFactorEquiv k a = det a := rfl


open Categorification.Webster.LabelTwo

/-- The separated square-zero dot algebra is identified with the actual
regular parabolic input algebra. -/
def middleRegularFactorEquiv : Middle k ≃ₐ[k] D :=
  (middlePolynomialEquiv k).symm.trans
    ((middleEndomorphismEquiv k).trans (middleEndomorphismFactorEquiv k))

/-- The sum differential as an element of the actual regular factor algebra. -/
def factorDotSum : D := middleEndomorphismFactorEquiv k (diagramPlus k)

theorem middleRegularFactorEquiv_dotSum :
    middleRegularFactorEquiv k (y₁ + y₂ : Middle k) = factorDotSum k := by
  have h₀ : (middlePolynomialEquiv k).symm (y₁ : Middle k) = squareQuotientVariable k 0 :=
    (middlePolynomialEquiv k).symm_apply_eq.mpr (middlePolynomialEquiv_variable_zero k).symm
  have h₁ : (middlePolynomialEquiv k).symm (y₂ : Middle k) = squareQuotientVariable k 1 :=
    (middlePolynomialEquiv k).symm_apply_eq.mpr (middlePolynomialEquiv_variable_one k).symm
  have h : (middlePolynomialEquiv k).symm (y₁ + y₂ : Middle k) =
      Ideal.Quotient.mk (middleDotIdeal k) (MvPolynomial.X 0 + MvPolynomial.X 1) := by
    rw [map_add, h₀, h₁, map_add]
    rfl
  change middleEndomorphismFactorEquiv k
    (middleEndomorphismEquiv k ((middlePolynomialEquiv k).symm (y₁ + y₂))) = _
  exact congrArg (middleEndomorphismFactorEquiv k)
    ((congrArg (middleEndomorphismEquiv k) h).trans (middleEndomorphismEquiv_sum k))

/-- The dual-number specialization of the actual regular factor algebra. -/
def factorSpecialize : D →ₐ[k] DualNumber k :=
  ((specialize (k := k)).restrictScalars k).comp (middleRegularFactorEquiv k).symm.toAlgHom

theorem factorSpecialize_surjective : Function.Surjective (factorSpecialize k) :=
  (augmentation_surjective (k := k)).comp (middleRegularFactorEquiv k).symm.surjective

private theorem specialize_eq_zero_iff_dotSum (a : Middle k) :
    specialize a = 0 ↔ ∃ b : Middle k, b * (y₁ + y₂) = a := by
  change a ∈ RingHom.ker specialize.toRingHom ↔ _
  rw [ker_specialize_eq_span]
  have hspan : a ∈ sumIdeal k ↔ ((y₁ : Middle k) + y₂) ∣ a :=
    Ideal.mem_span_singleton (α := Middle k)
  rw [hspan]
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨b, (mul_comm b (y₁ + y₂ : Middle k)).trans hb.symm⟩
  · rintro ⟨b,hb⟩
    exact ⟨b, hb.symm.trans (mul_comm b (y₁ + y₂ : Middle k))⟩

/-- The specialization has exactly the image of the actual factor
sum-of-dots right multiplication as its kernel. -/
theorem factorSpecialize_zero_iff (a : D) :
    factorSpecialize k a = 0 ↔ ∃ b : D, b * factorDotSum k = a := by
  let e := middleRegularFactorEquiv k
  change specialize (e.symm a) = 0 ↔ _
  rw [specialize_eq_zero_iff_dotSum]
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨e b, ?_⟩
    calc
      e b * factorDotSum k = e (b * (y₁ + y₂)) :=
        (congrArg (fun y : D => e b * y) (middleRegularFactorEquiv_dotSum k).symm).trans
          (e.map_mul b (y₁ + y₂)).symm
      _ = a := (congrArg e hb).trans (e.apply_symm_apply a)
  · rintro ⟨b,hb⟩
    refine ⟨e.symm b, e.injective ?_⟩
    exact (e.map_mul _ _).trans
      ((congrArg₂ (· * ·) (e.apply_symm_apply b) (middleRegularFactorEquiv_dotSum k)).trans
        (hb.trans (e.apply_symm_apply a).symm))

/-- Right multiplication by the actual sum element on the regular input. -/
def factorDotSumMap : Module.End D D where
  toFun n := n * factorDotSum k
  map_add' x y := add_mul x y (factorDotSum k)
  map_smul' c n := mul_assoc c n (factorDotSum k)

theorem factorDotSumSpecialization_exact :
    Function.Exact (factorDotSumMap k) (factorSpecialize k) :=
  factorSpecialize_zero_iff k

theorem factorSpecialize_ker_eq_range :
    LinearMap.ker (factorSpecialize k).toLinearMap =
      LinearMap.range ((factorDotSumMap k).restrictScalars k) :=
  LinearMap.exact_iff.mp (factorDotSumSpecialization_exact k)

/-- The dual-number specialization with the actual regular factor action. -/
def SpecializedMiddleFactor : Type := DualNumber k

instance : AddCommGroup (SpecializedMiddleFactor k) :=
  inferInstanceAs (AddCommGroup (DualNumber k))

instance : Module k (SpecializedMiddleFactor k) :=
  inferInstanceAs (Module k (DualNumber k))

instance : Module D (SpecializedMiddleFactor k) :=
  Module.compHom (DualNumber k) (factorSpecialize k).toRingHom

instance : IsScalarTower k D (SpecializedMiddleFactor k) where
  smul_assoc c a x := by
    let y : DualNumber k := x
    change factorSpecialize k (c • a) * y = c • (factorSpecialize k a * y)
    rw [map_smul, Algebra.smul_def c (factorSpecialize k a),
      Algebra.smul_def c (factorSpecialize k a * y), mul_assoc]

/-- The actual specialization as a left regular factor-module map. -/
def factorSpecializeLinear : D →ₗ[D] SpecializedMiddleFactor k where
  toFun := factorSpecialize k
  map_add' := (factorSpecialize k).map_add
  map_smul' a b := (factorSpecialize k).map_mul a b

/-- The actual parabolic regular input modulo the sum of dots is the
dual-number module with its specialized factor action. -/
def factorDotSumQuotientEquiv :
    (D ⧸ LinearMap.range (factorDotSumMap k)) ≃ₗ[D] SpecializedMiddleFactor k :=
  (Submodule.quotEquivOfEq _ _
    (LinearMap.exact_iff.mp (show Function.Exact (factorDotSumMap k) (factorSpecializeLinear k)
      from factorDotSumSpecialization_exact k)).symm).trans
    (LinearMap.quotKerEquivOfSurjective (factorSpecializeLinear k) (factorSpecialize_surjective k))
end Categorification.Stendhal.LabelTwo
