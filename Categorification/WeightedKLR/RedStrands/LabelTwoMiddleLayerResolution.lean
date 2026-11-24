/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardLayerProjective
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleExact

/-!
# The periodic label-two resolution over its layer algebra

The actual diagrammatic alternating middle complex is an augmented
projective resolution after quotienting out loading idempotents strictly
above the middle cut. This fixes the coefficient and the ambient algebra
for the relative derived calculation in Webster §8.2.
-/

noncomputable section

set_option maxHeartbeats 700000

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "blackWeight" => (({()} : Multiset Unit) + {()})
local notation "Ambient" => TensorProductAlgebra k (parameter k) weights blackWeight
local notation "S" => Standard k
local notation "Qmod" => StandardDotSumQuotient k
local notation "Higher" => leftStandardHigherLoadingIdeal (parameter k) weights loading
local notation "B" => LeftStandardLayerAlgebra (parameter k) weights loading
local notation "p" => RingCon.mkₐ k (TwoSidedIdeal.ringCon Higher)

/-- The actual augmentation target is a left module over the middle layer algebra. -/
def middleLayerQuotientAction : B →ₐ[k] Module.End k Qmod := by
  let f : Ambient →ₐ[k] Module.End k Qmod := Algebra.lsmul k k (A := Ambient) Qmod
  apply (Higher).ringCon.liftₐ f
  apply (TwoSidedIdeal.ringCon_le_iff (I := Higher) (J := TwoSidedIdeal.ker f.toRingHom)).mp
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨t, ht, hlt, rfl⟩
  apply (TwoSidedIdeal.mem_ker _).mpr
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (diagramPlus k)) z
  change seqIdem (parameter k) weights t ht • (LinearMap.range (diagramPlus k)).mkQ x = 0
  rw [← map_smul, seqIdem_smul_leftStandard_eq_zero (parameter k) weights loading_ordered ht hlt,
    map_zero]

instance : Module B Qmod := Module.compHom Qmod (middleLayerQuotientAction k).toRingHom

/-- Restriction of the layer action recovers the original action on the quotient. -/
theorem middleLayerQuotient_smul_mk (a : Ambient) (z : Qmod) : p a • z = a • z := rfl


private def relativeLinear (f : Module.End Ambient S) : Module.End B S where
  toFun := f
  map_add' := f.map_add
  map_smul' b z := by
    obtain ⟨a, rfl⟩ := (Higher).ringCon.mk'_surjective b
    exact f.map_smul a z

private def relativeAugmentation : S →ₗ[B] Qmod where
  toFun := (LinearMap.range (diagramPlus k)).mkQ
  map_add' := (LinearMap.range (diagramPlus k)).mkQ.map_add
  map_smul' b z := by
    obtain ⟨a, rfl⟩ := (Higher).ringCon.mk'_surjective b
    exact (LinearMap.range (diagramPlus k)).mkQ.map_smul a z

private abbrev actualRelativeDifferential (n : ℕ) : ModuleCat.of B S ⟶ ModuleCat.of B S :=
  ModuleCat.ofHom (relativeLinear k (if Even n then diagramPlus k else diagramMinus k))

private theorem relativeSquare (n : ℕ) :
    actualRelativeDifferential k (n + 1) ≫ actualRelativeDifferential k n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (if Even n then diagramPlus k else diagramMinus k)
    ((if Even (n + 1) then diagramPlus k else diagramMinus k) x) = 0
  by_cases h : Even n
  · have hs : ¬ Even (n + 1) := by simpa [Nat.even_add_one] using h
    rw [ite_eq_left h, ite_eq_right hs]
    exact (diagramMinusPlus_exact k _).mpr ⟨x, rfl⟩
  · have hs : Even (n + 1) := by simpa [Nat.even_add_one] using h
    rw [ite_eq_right h, ite_eq_left hs]
    exact (diagramPlusMinus_exact k _).mpr ⟨x, rfl⟩

/-- The alternating diagrammatic dot complex over the middle layer. -/
def relativeMiddleComplex : ChainComplex (ModuleCat B) ℕ :=
  ChainComplex.of (fun _ => ModuleCat.of B S) (actualRelativeDifferential k) (relativeSquare k)

private theorem relativeMiddle_d (n : ℕ) :
    (relativeMiddleComplex k).d (n + 1) n = actualRelativeDifferential k n :=
  ChainComplex.of_d (fun _ : ℕ => ModuleCat.of B S) (actualRelativeDifferential k) n

private theorem relativeMiddleExactAt (n : ℕ) : (relativeMiddleComplex k).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n
    (ComplexShape.prev_eq' _ (by rfl)) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  change Function.Exact ((relativeMiddleComplex k).d (n + 2) (n + 1))
    ((relativeMiddleComplex k).d (n + 1) n)
  have h₁ : (relativeMiddleComplex k).d (n + 2) (n + 1) = actualRelativeDifferential k (n + 1) :=
    relativeMiddle_d k (n + 1)
  rw [h₁, relativeMiddle_d k n]
  change Function.Exact
    (⇑(if Even (n + 1) then diagramPlus k else diagramMinus k))
    (⇑(if Even n then diagramPlus k else diagramMinus k))
  by_cases h : Even n
  · have hs : ¬ Even (n + 1) := by simpa [Nat.even_add_one] using h
    simpa only [ite_eq_right hs, ite_eq_left h] using! diagramMinusPlus_exact k
  · have hs : Even (n + 1) := by simpa [Nat.even_add_one] using h
    simpa only [ite_eq_left hs, ite_eq_right h] using! diagramPlusMinus_exact k

local notation "M" => ModuleCat.of B Qmod
local notation "C" => relativeMiddleComplex k
local notation "shape" => ComplexShape.down ℕ

private theorem relativeZeroAug : actualRelativeDifferential k 0 ≫
    ModuleCat.ofHom (relativeAugmentation k) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (LinearMap.range (diagramPlus k)).mkQ (diagramPlus k x) = 0
  exact Submodule.Quotient.mk_eq_zero _ |>.mpr ⟨x, rfl⟩

/-- The actual alternating periodic resolution augmented over its layer algebra. -/
def relativeMiddleToQuotient : C ⟶ (ChainComplex.single₀ (ModuleCat B)).obj M :=
  (ChainComplex.toSingle₀Equiv C M).symm ⟨ModuleCat.ofHom (relativeAugmentation k), by
    rw [relativeMiddle_d k 0]
    exact relativeZeroAug k⟩

/-- The layer augmentation is a quasi-isomorphism. -/
theorem relativeMiddleToQuotient_quasiIso : QuasiIso (relativeMiddleToQuotient k) := by
  constructor
  intro n
  cases n with
  | succ n =>
      exact (quasiIsoAt_iff_exactAt' _ (n + 1) (ChainComplex.exactAt_succ_single_obj _ _)).mpr
        (relativeMiddleExactAt k n)
  | zero =>
      let f := ((HomologicalComplex.shortComplexFunctor' (ModuleCat B) shape 1 0 0).map
        (relativeMiddleToQuotient k))
      apply (ChainComplex.quasiIsoAt₀_iff _).mpr
      change ShortComplex.QuasiIso f
      have hg : ((C).sc' 1 0 0).g = 0 := (C).shape 0 0 (by decide)
      have hf' : (((ChainComplex.single₀ (ModuleCat B)).obj M).sc' 1 0 0).f = 0 := rfl
      have hg' : (((ChainComplex.single₀ (ModuleCat B)).obj M).sc' 1 0 0).g = 0 := rfl
      have haug : (relativeMiddleToQuotient k).f 0 = ModuleCat.ofHom (relativeAugmentation k) :=
        ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
      refine (ShortComplex.quasiIso_iff_of_zeros' f hg hf' hg').mpr ⟨?_, ?_⟩
      · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
        change Function.Exact ((C).d 1 0) ((relativeMiddleToQuotient k).f 0)
        rw [haug, relativeMiddle_d k 0]
        exact diagramMiddleAugmentation_exact k
      · change Epi ((relativeMiddleToQuotient k).f 0)
        rw [haug]
        exact (ModuleCat.epi_iff_surjective _).mpr
          (Submodule.mkQ_surjective (LinearMap.range (diagramPlus k)))

/-- The periodic diagram complex computes derived tensor over the middle layer algebra. -/
def relativeMiddleProjectiveResolution : ProjectiveResolution M where
  complex := C
  projective _ := by
    have : Module.Projective B S :=
      leftStandardLayer_projective (parameter k) weights loading loading_ordered
    change Projective (ModuleCat.of B S)
    infer_instance
  π := relativeMiddleToQuotient k
  quasiIso := relativeMiddleToQuotient_quasiIso k

end Categorification.Stendhal.LabelTwo
