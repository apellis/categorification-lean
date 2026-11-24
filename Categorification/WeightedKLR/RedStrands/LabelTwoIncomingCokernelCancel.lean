/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingCokernelTor
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingCokernelSurjective
import Categorification.Algebra.DerivedTensorCoefficientExact
import Categorification.Algebra.ReflectedVectorDual

/-!
# Cancellation in first ambient Tor of the label-two incoming cokernel

The right-module reflection of the incoming short exact sequence gives
a distinguished triangle after derived tensor with the incoming cokernel.
The connecting sequence identifies the first self Tor as zero once the
first Tor map of the incoming crossing is surjective.
-/

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero
noncomputable section

universe w

section Generic

variable {k : Type} [Field k] [DG.HasDerivedCategory.{w,0} k]

private local instance : (homologyFunctor (A := k) k 0).ShiftSequence ℤ := by
  let : (DG.HomotopyCategory.homologyFunctor.{0} k k 0).ShiftSequence ℤ := by
    change (DG.HomotopyCategory.forget.{0} k k ⋙
      _root_.HomotopyCategory.homologyFunctor (ModuleCat k) (ComplexShape.up ℤ) 0).ShiftSequence ℤ
    infer_instance
  exact Functor.ShiftSequence.induced (homologyFunctorFactorsh k 0) ℤ
    (homologyFunctor k) (homologyFunctorFactorsh k)

private theorem isZero_last_homology_of_epi (D : Triangle (DerivedCategory.{w,0} k))
    (hD : D ∈ distTriang _) (n : ℤ) (h : Epi ((homologyFunctor k n).map D.mor₁))
    (hZ : IsZero ((homologyFunctor k (n+1)).obj D.obj₁)) :
    IsZero ((homologyFunctor k n).obj D.obj₃) := by
  let F := homologyFunctor (A := k) k 0
  have h₂ : (F.shift n).map D.mor₂ = 0 :=
    (F.homologySequence_epi_shift_map_mor₁_iff D hD n).mp h
  let δ := F.homologySequenceδ D n (n+1) rfl
  have hz : δ = 0 := hZ.eq_of_tgt _ _
  have hMono : Mono δ :=
    (F.homologySequence_exact₃ D hD n (n+1) rfl).mono_g_iff.mpr h₂
  exact @IsZero.of_mono_eq_zero _ _ _ _ _ δ hMono hz

variable {A M N P : Type} [Ring A] [Algebra k A] [DG.HasDerivedCategory.{w,0} A]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [SMulCommClass k Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module Aᵐᵒᵖ N] [SMulCommClass k Aᵐᵒᵖ N] [IsScalarTower k Aᵐᵒᵖ N]
  [AddCommGroup P] [Module k P] [Module Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P] [IsScalarTower k Aᵐᵒᵖ P]

private abbrev moduleObject (X : ModuleCat A) :=
  Q.obj (DGModuleCat.of A (InDegreeZero X))

private theorem coefficient_first_homology_isZero_of_surjective (X : ModuleCat A)
    (f : M →ₗ[k] N) (hf : BalancedTensor.IsBimoduleHom (A := A) f)
    (g : N →ₗ[k] P) (hg : BalancedTensor.IsBimoduleHom (A := A) g)
    (hfg : Function.Exact f g) (hi : Function.Injective f) (hs : Function.Surjective g)
    (hz : IsZero ((homologyFunctor k 0).obj ((derivedTensor k A M).obj (moduleObject X))))
    (he : Function.Surjective ((homologyFunctor k (-1)).map
      ((derivedTensorCoefficientMap f hf).app (moduleObject X)))) :
    IsZero ((homologyFunctor k (-1)).obj ((derivedTensor k A P).obj (moduleObject X))) := by
  obtain ⟨δ,hδ⟩ := exists_distinguished_derivedTensorCoefficient X f hf g hg hfg hi hs
  let D := Triangle.mk ((derivedTensorCoefficientMap f hf).app (moduleObject X))
    ((derivedTensorCoefficientMap g hg).app (moduleObject X)) δ
  exact isZero_last_homology_of_epi D hδ (-1) ((ModuleCat.epi_iff_surjective _).mpr he) hz

end Generic

section LabelTwo

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "T" => TensorProductAlgebra k (parameter k) weights ν
local notation "TRaw" => TensorProductAlgebra k (parameter k)
  (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ())
local notation "I" => IncomingExteriorCoefficient k
local notation "R" => MiddleTensorCoefficient k
local notation "B" => StandardDotSumQuotient k
local notation "K" => IncomingMiddleCokernel k

local instance cancelIncomingRightModule : Module Tᵐᵒᵖ I := inferInstanceAs (Module TRawᵐᵒᵖ I)
local instance cancelIncomingGroundComm : SMulCommClass k Tᵐᵒᵖ I := inferInstanceAs (SMulCommClass k TRawᵐᵒᵖ I)
local instance cancelIncomingScalarTower : IsScalarTower k Tᵐᵒᵖ I := inferInstanceAs (IsScalarTower k TRawᵐᵒᵖ I)

local notation "ρ" => tensorReflect (Q := parameter k) (Λ := weights) («ν» := ν)

local notation "C" => ReflectedRight (ρ) K

private abbrev quotientMap : B →ₗ[T] K :=
  (LinearMap.range (normalizedIncoming k)).mkQ

private def reflectedQuotientMap : R →ₗ[k] C :=
  (quotientMap k).restrictScalars k

private theorem reflectedQuotientMap_rightLinear :
    BalancedTensor.IsBimoduleHom (A := T) (reflectedQuotientMap k) := by
  intro a z
  change quotientMap k (((ρ) a).unop • (show B from z)) =
    ((ρ) a).unop • quotientMap k (show B from z)
  exact (quotientMap k).map_smul _ _

private theorem reflectedQuotientMap_exact :
    Function.Exact (reflectedIncomingMap k) (reflectedQuotientMap k) := by
  change Function.Exact (normalizedIncoming k) (quotientMap k)
  exact LinearMap.exact_iff.mpr (Submodule.ker_mkQ _)

private theorem reflectedQuotientMap_surjective :
    Function.Surjective (reflectedQuotientMap k) :=
  (LinearMap.range (normalizedIncoming k)).mkQ_surjective

variable [DG.HasDerivedCategory.{w,0} k]
  [DG.HasDerivedCategory.{w,0} (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()}))]

private abbrev derivedObject (Z : Type) [AddCommGroup Z] [Module T Z] :=
  Q.obj (DGModuleCat.of T (InDegreeZero Z))

private theorem incomingCokernelH0_isZero :
    IsZero ((homologyFunctor k 0).obj ((derivedTensor k T I).obj (derivedObject k K))) := by
  let S := incomingLiftShortComplex k
  let g := S.g.hom
  have hg : Function.Surjective g :=
    (ModuleCat.epi_iff_surjective S.g).mp (incomingLiftShortComplex_shortExact k).epi_g
  let t := ambientH0Map (k := k) (N := I) g
  have hs := ambientH0Map_surjective (k := k) (N := I) g hg
  have hEpi : Epi t := (ModuleCat.epi_iff_surjective t).mpr hs
  exact @IsZero.of_epi_eq_zero _ _ _ _ _ t hEpi
    ((incomingMiddleStandardHomology_zero_isZero k).eq_of_src _ _)

private abbrev firstTorCoefficientMap :=
  (homologyFunctor k (-1)).map
    ((derivedTensorCoefficientMap (reflectedIncomingMap k) (reflectedIncomingMap_op_smul k)).app
      (derivedObject k K))

/-- Surjectivity of the reflected incoming map on first Tor forces the
first ambient Tor of the incoming cokernel with itself to vanish. -/
theorem incomingCokernelSelfTorOne_isZero_of_surjective
    (h : Function.Surjective (firstTorCoefficientMap k)) :
    IsZero ((homologyFunctor k (-1)).obj ((derivedTensor k T C).obj (derivedObject k K))) := by
  let X := ModuleCat.of T K
  let f := reflectedIncomingMap k
  let g := reflectedQuotientMap k
  have hf : BalancedTensor.IsBimoduleHom (A := T) f := reflectedIncomingMap_op_smul k
  have hg : BalancedTensor.IsBimoduleHom (A := T) g := reflectedQuotientMap_rightLinear k
  have hi : Function.Injective f := labelTwoNormalizedIncoming_injective k
  exact coefficient_first_homology_isZero_of_surjective X f hf g hg
    (reflectedQuotientMap_exact k) hi (reflectedQuotientMap_surjective k)
    (incomingCokernelH0_isZero k) h

end LabelTwo

end
end Categorification.Stendhal.LabelTwo
