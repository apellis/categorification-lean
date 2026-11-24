/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedHomologyShift
import Categorification.Algebra.DerivedTensorOrdinaryLinear
import Categorification.Algebra.DerivedTensorTriangulated
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleExact
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleRelativeTor
import Categorification.WeightedKLR.RedStrands.OppositeStandardTor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Ambient Tor of the label-two middle quotient

The actual alternating dot maps supply two short exact sequences with
the middle standard as the middle term. Degree-zero derived tensor
gives the vanishing sum map and the twice-epsilon difference map. The
kernel and cokernel in these coordinates give the first positive Tor
groups, and the higher groups follow by the two connecting
isomorphisms. The resulting comparison with the relative groups is
degreewise over the ground field.
-/

noncomputable section

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "blackWeight" => (({()} : Multiset Unit) + {()})
local notation "Ambient" => TensorProductAlgebra k (parameter k) weights blackWeight
local notation "S" => Standard k

/-- The alternating companion to the actual middle dot-sum quotient. -/
abbrev StandardDotDifferenceQuotient :=
  S ⧸ LinearMap.range (diagramMinus k)

section

variable {R X : Type} [Ring R] [AddCommGroup X] [Module R X]

private theorem range_mem_eq_zero_of_exact (f g : Module.End R X) (hex : Function.Exact f g)
    (z : X) (hz : z ∈ LinearMap.range f) : g z = 0 :=
  (hex z).mpr hz

private def exactCompanionInclusion (f g : Module.End R X) (hex : Function.Exact f g) :
    (X ⧸ LinearMap.range f) →ₗ[R] X :=
  (LinearMap.range f).liftQ g (fun z hz => LinearMap.mem_ker.mpr
    (range_mem_eq_zero_of_exact f g hex z hz))

private def exactCompanionSequence (f g : Module.End R X) (hex : Function.Exact f g) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk (ModuleCat.ofHom (exactCompanionInclusion f g hex))
    (ModuleCat.ofHom (LinearMap.range g).mkQ) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range f) z
      change (LinearMap.range g).mkQ (g x) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩)

private theorem exactCompanionSequence_shortExact (f g : Module.End R X)
    (hex : Function.Exact f g) :
    (exactCompanionSequence f g hex).ShortExact := by
  let sc := exactCompanionSequence f g hex
  have : Mono sc.f := (ModuleCat.mono_iff_injective sc.f).mpr <| by
    apply (injective_iff_map_eq_zero (f := sc.f.hom)).mpr
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range f) z
    intro hz
    apply (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mpr
    exact (hex x).mp hz
  have : Epi sc.g :=
    (ModuleCat.epi_iff_surjective sc.g).mpr (Submodule.mkQ_surjective (LinearMap.range g))
  constructor
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact sc).mpr
  intro (x : X)
  change (Submodule.Quotient.mk x : X ⧸ LinearMap.range g) = 0 ↔
    ∃ z, exactCompanionInclusion f g hex z = x
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(LinearMap.range f).mkQ y, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range f) z
    exact ⟨y, rfl⟩

end

/-- The diagrammatic short exact sequence from the difference quotient
through the middle standard to the sum quotient. -/
def middleSumShortExactSequence : ShortComplex (ModuleCat Ambient) :=
  exactCompanionSequence (diagramMinus k) (diagramPlus k) (diagramMinusPlus_exact k)

/-- The diagrammatic short exact sequence from the sum quotient
through the middle standard to the difference quotient. -/
def middleDifferenceShortExactSequence : ShortComplex (ModuleCat Ambient) :=
  exactCompanionSequence (diagramPlus k) (diagramMinus k) (diagramPlusMinus_exact k)

theorem middleSumShortExactSequence_exact : (middleSumShortExactSequence k).ShortExact :=
  exactCompanionSequence_shortExact _ _ _

theorem middleDifferenceShortExactSequence_exact :
    (middleDifferenceShortExactSequence k).ShortExact :=
  exactCompanionSequence_shortExact _ _ _

end Categorification.Stendhal.LabelTwo

namespace Categorification.Stendhal.LabelTwo

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w

variable (k : Type) [Field k]
local notation "Ambient" =>
  TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()})
local notation "Coeff" => MiddleTensorCoefficient k

variable [HasDerivedCategory.{w, 0}
  (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()}))]
  [HasDerivedCategory.{w, 0} k]

private abbrev ambientTensorHomology (n : ℤ) : ModuleCat Ambient ⥤ ModuleCat k :=
  degreeZeroModuleFunctor Ambient ⋙ Q ⋙ derivedTensor k Ambient Coeff ⋙ homologyFunctor k n

/-- The degree-`n` ambient derived tensor of the two actual sum quotients. -/
abbrev ambientMiddleSumHomology (n : ℤ) : ModuleCat k :=
  (ambientTensorHomology k n).obj (middleSumShortExactSequence k).X₃

/-- The degree-`n` ambient derived tensor with the actual difference quotient. -/
abbrev ambientMiddleDifferenceHomology (n : ℤ) : ModuleCat k :=
  (ambientTensorHomology k n).obj (middleDifferenceShortExactSequence k).X₃

/-- The middle standard has no ambient derived tensor homology outside degree zero. -/
def MiddleAmbientAcyclic : Prop :=
  ∀ n : ℤ, n ≠ 0 → IsZero ((ambientTensorHomology k n).obj (ModuleCat.of Ambient (Standard k)))

private def shiftedAmbientTensor (S : ShortComplex (ModuleCat Ambient)) (hS : S.ShortExact)
    (n : ℤ) (h₀ : IsZero ((ambientTensorHomology k n).obj S.X₂))
    (h₁ : IsZero ((ambientTensorHomology k (n + 1)).obj S.X₂)) :
    (ambientTensorHomology k n).obj S.X₃ ≅ (ambientTensorHomology k (n + 1)).obj S.X₁ := by
  let F := derivedTensor k Ambient Coeff
  let sc := S.map (degreeZeroModuleFunctor Ambient)
  let ex := exists_distinguished_of_shortExact sc (degreeZeroModuleFunctor_shortExact S hS)
  let d := Classical.choose ex
  let T := Triangle.mk (Q.map sc.f) (Q.map sc.g) d
  have hT : T ∈ distTriang (DerivedCategory.{w,0} Ambient) := Classical.choose_spec ex
  exact homologyShiftIso k (F.mapTriangle.obj T) (F.map_distinguished T hT) n h₀ h₁

/-- The two consecutive higher Tor groups identify by the alternating actual
short exact sequence, provided the middle standard is ambient acyclic. -/
def ambientMiddleSumShiftIso (h : MiddleAmbientAcyclic k)
    (n : ℤ) (h₀ : n ≠ 0) (h₁ : n + 1 ≠ 0) :
    ambientMiddleSumHomology k n ≅ ambientMiddleDifferenceHomology k (n + 1) :=
  shiftedAmbientTensor k (middleSumShortExactSequence k) (middleSumShortExactSequence_exact k)
    n (h n h₀) (h (n + 1) h₁)

/-- The reverse shift uses the companion actual short exact sequence. -/
def ambientMiddleDifferenceShiftIso (h : MiddleAmbientAcyclic k)
    (n : ℤ) (h₀ : n ≠ 0) (h₁ : n + 1 ≠ 0) :
    ambientMiddleDifferenceHomology k n ≅ ambientMiddleSumHomology k (n + 1) :=
  shiftedAmbientTensor k (middleDifferenceShortExactSequence k)
    (middleDifferenceShortExactSequence_exact k) n (h n h₀) (h (n + 1) h₁)

end Categorification.Stendhal.LabelTwo

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
  TensorProductOver MulOpposite Categorification.Webster.LabelTwo
open scoped DG.DegreeZero DualNumber

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w

variable (k : Type) [Field k]

local notation "Ambient" =>
  TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()})
local notation "Coeff" => MiddleTensorCoefficient k
local notation "S" => Standard k
local notation "Tens" => TensorProductOver Ambient Coeff S
local notation "Ord" => BalancedTensor k k Ambient Coeff S

private def ambientStandardBalancedEquiv : Tens ≃ₗ[k] Ord where
  __ := ordinaryBalancedTensorAddEquiv (A := k) (middleTensorCoefficient_algebraMap_smul k)
  map_smul' c z := by
    let e := ordinaryBalancedTensorAddEquiv (A := k) (N := S)
      (middleTensorCoefficient_algebraMap_smul k)
    change e (c • z) = c • e z
    induction z using TensorProductOver.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul m z => rfl
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem ambientStandardBalanced_map (f : Module.End Ambient S) (z : Tens) :
    ambientStandardBalancedEquiv k (TensorProductOver.map LinearMap.id f z) =
      BalancedTensor.mapRight f (ambientStandardBalancedEquiv k z) := by
  induction z using TensorProductOver.induction_on with
  | zero => simp only [map_zero]
  | tmul m s => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable [HasDerivedCategory.{w, 0}
  (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()}))]
  [HasDerivedCategory.{w, 0} k]

local notation "H₀" => ambientTensorHomology k 0
set_option quotPrecheck false in
local notation "Hstd" => (H₀).obj (ModuleCat.of Ambient S)

private def ambientH0StandardCoords : Hstd ≃ₗ[k] DualNumber k :=
  (ambientDerivedTensorH0Equiv (k := k) (A := Ambient) (N := Coeff) S).trans
    ((ambientStandardBalancedEquiv k).trans (middleStandardTensorEquiv k))

private theorem ambientH0StandardCoords_map (f : Module.End Ambient S) (t : Hstd) :
    ambientH0StandardCoords k ((H₀).map (ModuleCat.ofHom f) t) =
      middleStandardTensorEquiv k
        (BalancedTensor.mapRight f
          (ambientStandardBalancedEquiv k
            (ambientDerivedTensorH0Equiv (k := k) (A := Ambient) (N := Coeff) S t))) := by
  let e := ambientDerivedTensorH0Equiv (k := k) (A := Ambient) (N := Coeff) S
  let z := e t
  have h := ambientH0Map_naturality (k := k) (A := Ambient) (N := Coeff) f z
  change e ((H₀).map (ModuleCat.ofHom f) (e.symm z)) = _ at h
  have ht : e ((H₀).map (ModuleCat.ofHom f) t) = TensorProductOver.map LinearMap.id f z :=
    (congrArg (fun t' => e ((H₀).map (ModuleCat.ofHom f) t')) (e.symm_apply_apply t)).symm.trans h
  exact (congrArg (fun s => middleStandardTensorEquiv k (ambientStandardBalancedEquiv k s)) ht).trans
    (congrArg (middleStandardTensorEquiv k) (ambientStandardBalanced_map k f z))

private theorem ambientH0StandardPlus :
    (H₀).map (ModuleCat.ofHom (diagramPlus k)) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply (ambientH0StandardCoords k).injective
  change ambientH0StandardCoords k ((H₀).map (ModuleCat.ofHom (diagramPlus k)) t) =
    ambientH0StandardCoords k 0
  rw [map_zero, ambientH0StandardCoords_map]
  exact middleStandardTensorEquiv_plus k _

private theorem ambientH0StandardMinus (t : Hstd) :
    ambientH0StandardCoords k ((H₀).map (ModuleCat.ofHom (diagramMinus k)) t) =
      twiceEps (ambientH0StandardCoords k t) := by
  rw [ambientH0StandardCoords_map, twiceEps_apply]
  exact middleStandardTensorEquiv_minus k _

end Categorification.Stendhal.LabelTwo

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
  TensorProductOver MulOpposite Categorification.Webster.LabelTwo
open scoped DG.DegreeZero DualNumber

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w

variable (k : Type) [Field k]

local notation "Ambient" =>
  TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()})
local notation "Coeff" => MiddleTensorCoefficient k
local notation "S" => Standard k

local notation "Cplus" => middleSumShortExactSequence k
local notation "Cminus" => middleDifferenceShortExactSequence k
local notation "Std" => ModuleCat.of Ambient S
local notation "SumQ" => ModuleCat.of Ambient (StandardDotSumQuotient k)
local notation "DiffQ" => ModuleCat.of Ambient (StandardDotDifferenceQuotient k)

private abbrev sumQuotientMap : Std ⟶ SumQ := (Cplus).g
private abbrev differenceQuotientMap : Std ⟶ DiffQ := (Cminus).g
private abbrev sumInclusionMap : DiffQ ⟶ Std := (Cplus).f
private abbrev differenceInclusionMap : SumQ ⟶ Std := (Cminus).f

private theorem differenceSumComp :
    (differenceQuotientMap k) ≫ (sumInclusionMap k) = ModuleCat.ofHom (diagramPlus k) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro (v : S)
  rfl

private theorem sumDifferenceComp :
    (sumQuotientMap k) ≫ (differenceInclusionMap k) = ModuleCat.ofHom (diagramMinus k) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro (v : S)
  rfl

variable [HasDerivedCategory.{w, 0}
  (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()}))]
  [HasDerivedCategory.{w, 0} k]

local notation "H₀" => ambientTensorHomology k 0
set_option quotPrecheck false in
local notation "Hstd" => (H₀).obj (ModuleCat.of Ambient S)

private theorem ambientTensorHomology_exact (C : ShortComplex (ModuleCat Ambient))
    (hC : C.ShortExact) (n : ℤ) : (C.map (ambientTensorHomology k n)).Exact := by
  let F := derivedTensor k Ambient Coeff
  let sc := C.map (degreeZeroModuleFunctor Ambient)
  obtain ⟨d, hp⟩ := exists_distinguished_of_shortExact sc (degreeZeroModuleFunctor_shortExact C hC)
  let T := Triangle.mk (Q.map sc.f) (Q.map sc.g) d
  have hT : T ∈ distTriang (DerivedCategory.{w, 0} Ambient) := hp
  exact homology_distinguished_pair_exact k (F.mapTriangle.obj T) (F.map_distinguished T hT) n
    (C.map (ambientTensorHomology k n)).zero

private def ambientTensorHomology_toKernel (C : ShortComplex (ModuleCat Ambient))
    (hC : C.ShortExact) (h : IsZero ((ambientTensorHomology k (-1)).obj C.X₂)) :
    (ambientTensorHomology k (-1)).obj C.X₃ ≅ kernel ((H₀).map C.f) := by
  let F := derivedTensor k Ambient Coeff
  let sc := C.map (degreeZeroModuleFunctor Ambient)
  let ex := exists_distinguished_of_shortExact sc (degreeZeroModuleFunctor_shortExact C hC)
  let d := Classical.choose ex
  let T := Triangle.mk (Q.map sc.f) (Q.map sc.g) d
  have hT : T ∈ distTriang (DerivedCategory.{w, 0} Ambient) := Classical.choose_spec ex
  exact homologyShiftKernelIso k (F.mapTriangle.obj T) (F.map_distinguished T hT) (-1) h

private theorem sumQuotient_epi : Epi ((H₀).map (sumQuotientMap k)) :=
  (ModuleCat.epi_iff_surjective _).mpr
    (ambientH0Map_surjective (k := k) (A := Ambient) (N := Coeff) _
      (Submodule.mkQ_surjective (LinearMap.range (diagramPlus k))))

private theorem differenceQuotient_epi : Epi ((H₀).map (differenceQuotientMap k)) :=
  (ModuleCat.epi_iff_surjective _).mpr
    (ambientH0Map_surjective (k := k) (A := Ambient) (N := Coeff) _
      (Submodule.mkQ_surjective (LinearMap.range (diagramMinus k))))

private theorem sumInclusion_zero : (H₀).map (sumInclusionMap k) = 0 := by
  have := differenceQuotient_epi k
  apply (cancel_epi ((H₀).map (differenceQuotientMap k))).mp
  rw [← Functor.map_comp, differenceSumComp, ambientH0StandardPlus, comp_zero]

private theorem sumAugmentation_isIso : IsIso ((H₀).map (sumQuotientMap k)) := by
  have := sumQuotient_epi k
  have : Mono ((H₀).map (sumQuotientMap k)) :=
    (ambientTensorHomology_exact k Cplus (middleSumShortExactSequence_exact k) 0).mono_g_iff.mpr
      (sumInclusion_zero k)
  exact isIso_of_mono_of_epi _

private def sumAugmentationIso : Hstd ≅ ambientMiddleSumHomology k 0 := by
  exact @asIso _ _ _ _ ((H₀).map (sumQuotientMap k)) (sumAugmentation_isIso k)

/-- Ambient degree-zero derived tensor is the actual middle dual-number coefficient. -/
def ambientMiddleSumHomologyZero : ambientMiddleSumHomology k 0 ≅ ModuleCat.of k (DualNumber k) :=
  (sumAugmentationIso k).symm ≪≫ (ambientH0StandardCoords k).toModuleIso

private theorem differenceInclusion_square :
    (H₀).map (differenceInclusionMap k) ≫ (ambientH0StandardCoords k).toModuleIso.hom =
      (ambientMiddleSumHomologyZero k).hom ≫ ModuleCat.ofHom (twiceEps (k := k)) := by
  have := sumQuotient_epi k
  apply (cancel_epi ((H₀).map (sumQuotientMap k))).mp
  rw [← Category.assoc, ← Functor.map_comp, sumDifferenceComp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro (x : Hstd)
  change ambientH0StandardCoords k ((H₀).map (ModuleCat.ofHom (diagramMinus k)) x) = _
  have he := (sumAugmentationIso k).toLinearEquiv.symm_apply_apply x
  exact (ambientH0StandardMinus k x).trans
    (congrArg (fun y => twiceEps (ambientH0StandardCoords k y)) he).symm

end Categorification.Stendhal.LabelTwo

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
  TensorProductOver MulOpposite Categorification.Webster.LabelTwo
open scoped DG.DegreeZero DualNumber

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w

variable (k : Type) [Field k]

local notation "Ambient" =>
  TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()})
local notation "S" => Standard k
local notation "Dε" => ModuleCat.ofHom (twiceEps (k := k))

private def twiceEpsKernelLine (h₂ : (2 : k) ≠ 0) :
    kernel Dε ≅ ModuleCat.of k k :=
  ModuleCat.kernelIsoKer Dε ≪≫ (twiceEpsKernelEquiv h₂).toModuleIso

private def twiceEpsCokernelLine (h₂ : (2 : k) ≠ 0) :
    cokernel Dε ≅ ModuleCat.of k k :=
  ModuleCat.cokernelIsoRangeQuotient Dε ≪≫ (twiceEpsCokernelEquiv h₂).toModuleIso

variable [HasDerivedCategory.{w, 0}
  (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()}))]
  [HasDerivedCategory.{w, 0} k]

local notation "H₀" => ambientTensorHomology k 0
local notation "Cplus" => middleSumShortExactSequence k
local notation "Cminus" => middleDifferenceShortExactSequence k

private def differenceAugmentationCokernel :
    ambientMiddleDifferenceHomology k 0 ≅ cokernel ((H₀).map (differenceInclusionMap k)) := by
  let C := (Cminus).map (H₀)
  letI : Epi C.g := differenceQuotient_epi k
  let hc := (ambientTensorHomology_exact k Cminus (middleDifferenceShortExactSequence_exact k) 0).gIsCokernel
  exact IsColimit.coconePointUniqueUpToIso hc (colimit.isColimit _)

private def ambientMiddleDifferenceHomologyZero (h₂ : (2:k) ≠ 0) :
    ambientMiddleDifferenceHomology k 0 ≅ ModuleCat.of k k :=
  differenceAugmentationCokernel k ≪≫
    cokernel.mapIso _ Dε (ambientMiddleSumHomologyZero k)
      (ambientH0StandardCoords k).toModuleIso (differenceInclusion_square k) ≪≫
    twiceEpsCokernelLine k h₂

private def ambientFirstSum (h : MiddleAmbientAcyclic k) (h₂ : (2:k) ≠ 0) :
    ambientMiddleSumHomology k (-1) ≅ ModuleCat.of k k :=
  ambientTensorHomology_toKernel k Cplus (middleSumShortExactSequence_exact k)
      (h (-1) (by decide)) ≪≫ kernelIsoOfEq (sumInclusion_zero k) ≪≫
    kernelZeroIsoSource ≪≫ ambientMiddleDifferenceHomologyZero k h₂

private def ambientFirstDifference (h : MiddleAmbientAcyclic k) (h₂ : (2:k) ≠ 0) :
    ambientMiddleDifferenceHomology k (-1) ≅ ModuleCat.of k k :=
  ambientTensorHomology_toKernel k Cminus (middleDifferenceShortExactSequence_exact k)
      (h (-1) (by decide)) ≪≫
    kernel.mapIso _ Dε (ambientMiddleSumHomologyZero k)
      (ambientH0StandardCoords k).toModuleIso (differenceInclusion_square k) ≪≫
    twiceEpsKernelLine k h₂

/-- In characteristic different from two the actual paired ambient Tor groups
are one-dimensional in every positive homological degree. -/
def ambientMiddlePositiveHomology (h : MiddleAmbientAcyclic k) (h₂ : (2:k) ≠ 0) :
    (n : ℕ) → (ambientMiddleSumHomology k (Int.negSucc n) ≅ ModuleCat.of k k) ×
      (ambientMiddleDifferenceHomology k (Int.negSucc n) ≅ ModuleCat.of k k)
  | 0 => ⟨ambientFirstSum k h h₂, ambientFirstDifference k h h₂⟩
  | n + 1 => by
    let ih := ambientMiddlePositiveHomology h h₂ n
    have h₀ : Int.negSucc (n + 1) ≠ 0 := by omega
    have h₁ : Int.negSucc (n + 1) + 1 ≠ 0 := by omega
    have he : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
    exact ⟨(by simpa only [he] using ambientMiddleSumShiftIso k h _ h₀ h₁) ≪≫ ih.2,
      (by simpa only [he] using ambientMiddleDifferenceShiftIso k h _ h₀ h₁) ≪≫ ih.1⟩

end Categorification.Stendhal.LabelTwo

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
open scoped DG.DegreeZero

universe w

variable (k : Type) [Field k]
local notation "weightsBlack" => (({()} : Multiset Unit) + {()})
local notation "Ambient" => TensorProductAlgebra k (parameter k) weights weightsBlack
local notation "Labels" => {t : KLR.Seq (stendhalWeight 2 weightsBlack) // IsRedOrdered t}
local notation "Coeff" => MiddleTensorCoefficient k

variable [HasDerivedCategory.{w, 0}
  (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()}))]
  [HasDerivedCategory.{w, 0} k]

/-- The higher-supported resolution gives ambient acyclicity over the ground field. -/
theorem middleAmbientAcyclic_of_supportedResolution
    (P : ProjectiveResolution (ModuleCat.of Ambient (Standard k)))
    (hs : ∀ n : ℕ, ∃ (J : Type) (label : J → Labels)
      (inc : ∀ j, lIdeal (seqIdem (parameter k) weights (label j).1 (label j).2) →ₗ[Ambient]
        P.complex.X (n + 1)),
      (∀ j, StendhalLT loading (label j).1) ∧ ∀ x : P.complex.X (n + 1),
        x ∈ Submodule.span Ambient {y | ∃ j z, inc j z = y}) :
    MiddleAmbientAcyclic k := by
  intro n hn
  change IsZero ((homologyFunctor k n).obj
    ((derivedTensor k Ambient Coeff).obj (Q.obj (DGModuleCat.of Ambient (InDegreeZero (Standard k))))))
  apply isZero_homology_of_isZero_intHomology k
  exact isZero_derivedTensorHomology_of_projectiveResolution_loading_support (A := k) (M := Coeff) P
    (fun i : Labels => seqIdem (parameter k) weights i.1 i.2)
    (fun i => StendhalLT loading i.1) (fun i => seqIdem_mul_self (parameter k) weights i.1 i.2)
    hs (fun i hi => coefficient_kills_higher k i.1 i.2 hi) n hn

/-- Over a field of characteristic different from two the diagrammatic
ambient Tor groups are isomorphic to the computed relative middle groups. -/
def ambientMiddleToRelativeTorIso (h : MiddleAmbientAcyclic k) (h₂ : (2 : k) ≠ 0) (n : ℕ) :
    ambientMiddleSumHomology k (-(n : ℤ)) ≅ relativeMiddleTor k n := by
  cases n with
  | zero => exact ambientMiddleSumHomologyZero k ≪≫ (relativeMiddleTorZero k).symm
  | succ n =>
    have he : -(↑(n+1) : ℤ) = Int.negSucc n := by omega
    rw [he]
    exact (ambientMiddlePositiveHomology k h h₂ n).1 ≪≫ (relativeMiddleTorPositive k n h₂).symm

end Categorification.Stendhal.LabelTwo
