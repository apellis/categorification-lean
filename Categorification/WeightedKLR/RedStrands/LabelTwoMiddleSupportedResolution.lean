/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardParameterTransport
import Categorification.WeightedKLR.RedStrands.OffDiagonalParameters
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleAmbientAcyclicity
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleAmbientTor
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleOrderedQuotient
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleWeightSupportedResolution
import Categorification.WeightedKLR.RedStrands.StandardStratificationStd

/-!
# Higher-supported resolutions at the label-two middle loading

Webster's standard stratification at the standard rank-one parameters
gives an ordered projective resolution. Its loading support transfers to
the actual diagonal-zero label-two presentation, giving ambient derived
acyclicity of the middle standard for the reflected dot-sum coefficient.
-/

noncomputable section

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory ModuleFiltration QuantumGroup KL3.Diagram

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

private def rankOneCartan : CartanDatum Unit where
  dot _ _ := 2
  symm _ _ := rfl
  dot_self_pos _ := by decide
  dot_self_even _ := ⟨1, rfl⟩
  dot_nonpos i j hij := (hij (Subsingleton.elim i j)).elim
  dvd_two_mul _ _ := ⟨2, rfl⟩

local notation "ν₂" => (({()} : Multiset Unit) + {()})
local notation "qCL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars rankOneCartan k)
local notation "q" => parameter k
local notation "ACL" => TensorProductAlgebra k qCL weights ν₂
local notation "Ambient" => TensorProductAlgebra k q weights ν₂
local notation "Labels" => {s : KLR.Seq (stendhalWeight 2 ν₂) // IsRedOrdered s}
set_option quotPrecheck false in
local notation "StdCL" =>
  fun l : Labels => ModuleCat.of ACL (leftStandard qCL weights l.1 l.2)
set_option quotPrecheck false in
local notation "U" l:arg =>
  (leftUpper qCL weights l.1 l.2).comap (lIdeal (seqIdem qCL weights l.1 l.2)).subtype

private theorem rankOneRouquier : IsRouquierQ rankOneCartan qCL where
  symm i j hij := (hij (Subsingleton.elim i j)).elim
  homogeneous i j hij := (hij (Subsingleton.elim i j)).elim
  unit_coeff i j hij := (hij (Subsingleton.elim i j)).elim

private theorem rankOneSymm : KLRSymm qCL :=
  fun i j hij => (hij (Subsingleton.elim i j)).elim

private def rankOneParameterChange : ACL ≃ₐ[k] Ambient :=
  tensorProductUnitParameterEquiv weights ν₂

private theorem rankOneParameterChange_idem (s : KLR.Seq (stendhalWeight 2 ν₂)) (hs : IsRedOrdered s) :
    rankOneParameterChange k (seqIdem qCL weights s hs) = seqIdem q weights s hs :=
  tensorProductOffDiagonalEquiv_e (Q := qCL) (Q' := q) (Λ := weights) (ν := ν₂)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim) s hs

/-- The higher support of every loading-standard projective resolution transports
from the standard rank-one parameters to the actual label-two algebra. -/
theorem exists_loadingStandard_supportedResolution_of_CLFiltration
    (hU : ∀ t : Labels, ∃ m : List Labels, (∀ v ∈ m, StendhalLT t.1 v.1) ∧
      HasFiltration StdCL m (ModuleCat.of ACL (U t))) (s : Labels) :
    ∃ P : ProjectiveResolution (ModuleCat.of Ambient (leftStandard q weights s.1 s.2)), ∀ n : ℕ,
      ∃ (J : Type) (label : J → Labels)
        (inc : ∀ j, lIdeal (seqIdem q weights (label j).1 (label j).2) →ₗ[Ambient]
          P.complex.X (n + 1)),
        (∀ j, StendhalLT s.1 (label j).1) ∧ ∀ x : P.complex.X (n + 1),
          x ∈ Submodule.span Ambient {y | ∃ j z, inc j z = y} :=
  exists_ordered_projectiveResolution_leftStandard_transport weights
    (rankOneParameterChange k).toRingEquiv (rankOneParameterChange_idem k) hU s

/-- The higher support of the standard projective resolution transports from the
standard rank-one parameters to the actual label-two middle cut. -/
theorem exists_middleStandard_supportedResolution_of_CLFiltration
    (hU : ∀ t : Labels, ∃ m : List Labels, (∀ v ∈ m, StendhalLT t.1 v.1) ∧
      HasFiltration StdCL m (ModuleCat.of ACL (U t))) :
    ∃ P : ProjectiveResolution (ModuleCat.of Ambient (Standard k)), ∀ n : ℕ,
      ∃ (J : Type) (label : J → Labels)
        (inc : ∀ j, lIdeal (seqIdem q weights (label j).1 (label j).2) →ₗ[Ambient]
          P.complex.X (n + 1)),
        (∀ j, StendhalLT loading (label j).1) ∧ ∀ x : P.complex.X (n + 1),
          x ∈ Submodule.span Ambient {y | ∃ j z, inc j z = y} :=
  exists_loadingStandard_supportedResolution_of_CLFiltration k hU ⟨loading, loading_ordered⟩

private theorem rankOneCLFiltration (d : DecidableEq Unit) (t : Labels) :
    letI : DecidableEq Unit := d
    ∃ m : List Labels, (∀ v ∈ m, StendhalLT t.1 v.1) ∧
      HasFiltration StdCL m (ModuleCat.of ACL (U t)) := by
  have h : d = (fun a b : Unit => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst d
  exact exists_hasFiltration_leftUpper_std (rankOneRouquier k) (rankOneSymm k) weights ν₂ t.1 t.2

/-- Every actual label-two loading standard has a projective resolution with
higher loading support in every positive degree. -/
theorem exists_loadingStandard_supportedResolution (s : Labels) :
    ∃ P : ProjectiveResolution (ModuleCat.of Ambient (leftStandard q weights s.1 s.2)), ∀ n : ℕ,
      ∃ (J : Type) (label : J → Labels)
        (inc : ∀ j, lIdeal (seqIdem q weights (label j).1 (label j).2) →ₗ[Ambient]
          P.complex.X (n + 1)),
        (∀ j, StendhalLT s.1 (label j).1) ∧ ∀ x : P.complex.X (n + 1),
          x ∈ Submodule.span Ambient {y | ∃ j z, inc j z = y} :=
  exists_loadingStandard_supportedResolution_of_CLFiltration k
    (rankOneCLFiltration k instDecidableEqPUnit) s

/-- The actual middle standard has a projective resolution with higher loading
support in every positive degree. -/
theorem exists_middleStandard_supportedResolution :
    ∃ P : ProjectiveResolution (ModuleCat.of Ambient (Standard k)), ∀ n : ℕ,
      ∃ (J : Type) (label : J → Labels)
        (inc : ∀ j, lIdeal (seqIdem q weights (label j).1 (label j).2) →ₗ[Ambient]
          P.complex.X (n + 1)),
        (∀ j, StendhalLT loading (label j).1) ∧ ∀ x : P.complex.X (n + 1),
          x ∈ Submodule.span Ambient {y | ∃ j z, inc j z = y} :=
  exists_loadingStandard_supportedResolution k ⟨loading, loading_ordered⟩

open CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w

variable [HasDerivedCategory.{w, 0}
  (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()}))]

section IntegralHomology

variable [HasDerivedCategory.{w, 0} ℤ]

/-- The diagrammatic middle standard is acyclic away from degree zero for ambient
derived tensor with the reflected diagrammatic dot-sum coefficient. -/
theorem middleStandard_derivedTensorHomology_isZero (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
      ((derivedTensor ℤ Ambient (rightMiddleDotSumQuotient k : Type)).obj
        (Q.obj (DGModuleCat.of Ambient (InDegreeZero (Standard k)))))) := by
  obtain ⟨P, hP⟩ := exists_middleStandard_supportedResolution k
  exact middleStandard_derivedTensorHomology_isZero_of_higher_support k P hP n hn

end IntegralHomology

section GroundField

variable [HasDerivedCategory.{w, 0} k]

/-- The actual middle standard is ambient acyclic for the reflected coefficient
over the ground field. -/
theorem middleAmbientAcyclic : MiddleAmbientAcyclic k := by
  obtain ⟨P, hP⟩ := exists_middleStandard_supportedResolution k
  exact middleAmbientAcyclic_of_supportedResolution k P hP

/-- The actual ambient derived tensor of the reflected sum quotient with the
sum quotient has the same Tor objects as the relative middle calculation. -/
def actualAmbientMiddleToRelativeTorIso (h₂ : (2 : k) ≠ 0) (n : ℕ) :
    ambientMiddleSumHomology k (-(n : ℤ)) ≅ relativeMiddleTor k n :=
  ambientMiddleToRelativeTorIso k (middleAmbientAcyclic k) h₂ n

end GroundField


section FixedWeight

open CategoryTheory DG
open scoped DG.DegreeZero

local instance : InternalGrading Ambient :=
  gradedAlgebraInternalGrading (middleTensorGrade k (labelTwoGradingDatum k))
local instance : BigradedDGRing Ambient :=
  gradedAlgebraBigradedDGRing (middleTensorGrade k (labelTwoGradingDatum k))
local instance : InternalGrading k := scalarInternalGrading k
local instance : BigradedDGRing k := scalarBigradedDGRing k

variable [CatModule.HasDerivedCategory.{w,0} (WeightCategory
  (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()})))]
  [CatModule.HasDerivedCategory.{w,0} (WeightCategory k)]

/-- The actual label-two middle standard is acyclic at every weight for the
reflected dot-sum coefficient. -/
theorem middleStandardWeight_cohomology_isZero (X : WeightCategory k) (n : ℤ) (hn : n ≠ 0) :
    Limits.IsZero ((CatModule.DerivedCategory.cohomologyFunctor X n).obj
      ((middleReflectedWeightDerivedTensor k).obj
        (CatModule.DerivedCategory.Q.obj (middleStandardWeightModule k)))) := by
  let σ := (rankOneParameterChange k).toRingEquiv
  let hσ := rankOneParameterChange_idem k
  let hU := rankOneCLFiltration k instDecidableEqPUnit
  exact middleStandardWeight_cohomology_isZero_of_ordered_covers k
    (orderedStandardCoversTransport weights σ hσ hU)
    (middleOrderedCoversTransport_quotient k σ hσ hU) X n hn

end FixedWeight

end Categorification.Stendhal.LabelTwo

