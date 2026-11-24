/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingCokernelSurjective
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingCokernelCancel
import Categorification.WeightedKLR.RedStrands.LabelTwoOutgoingCokernelExact
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorProjectiveAcyclic
import Categorification.Algebra.ReflectedVectorDual
import Categorification.Algebra.ExactDerivedTensor
import Categorification.Algebra.DerivedTensorDegreeZero
import Categorification.Algebra.DerivedHomologyShift
import Categorification.Algebra.DerivedTensorFiltration
import Categorification.Algebra.DerivedTensorCoefficientExact

/-!
# Third ambient Tor of the label-two final simple

The first ambient self Tor of the incoming cokernel vanishes by
cancellation. Two dimension shifts across the final short exact
sequence, using projectivity of the exterior term on both sides,
identify it with the third Tor of the final simple.
-/

namespace Categorification

open DirectSum MulOpposite CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero
noncomputable section

section Reflection
variable {k A V : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup V] [Module A V]

/-- Reflection by an involution preserves module projectivity. -/
theorem ReflectedRight.projective (τ : A →ₐ[k] Aᵐᵒᵖ)
    (hτ : Function.Involutive (fun a => (τ a).unop)) [Module.Projective A V] :
    Module.Projective Aᵐᵒᵖ (ReflectedRight τ V) := by
  let h : A ≃+* Aᵐᵒᵖ :=
    { __ := τ.toRingHom
      invFun := fun a => (τ a.unop).unop
      left_inv := hτ
      right_inv := fun a => unop_injective (hτ a.unop) }
  let : RingHomInvPair (h : A →+* Aᵐᵒᵖ) (h.symm : Aᵐᵒᵖ →+* A) := .of_ringEquiv h
  let : RingHomInvPair (h.symm : Aᵐᵒᵖ →+* A) (h : A →+* Aᵐᵒᵖ) := .of_ringEquiv_symm h
  let : RingHomSurjective (h : A →+* Aᵐᵒᵖ) := ⟨h.surjective⟩
  let e : V ≃ₛₗ[(h : A →+* Aᵐᵒᵖ)] ReflectedRight τ V :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => congrArg (· • x) (hτ a).symm }
  exact Module.Projective.of_equiv e
end Reflection

universe w u
section Vanishing

variable {k A M X : Type u} [Field k] [Ring A]
    [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [SMulCommClass k Aᵐᵒᵖ M]
    [Module.Projective Aᵐᵒᵖ M] [AddCommGroup X] [Module A X]
    [DG.HasDerivedCategory.{w,u} k] [DG.HasDerivedCategory.{w,u} A]

/-- A projective right coefficient has no higher derived tensor homology with an ordinary module. -/
theorem derivedTensor_projectiveCoefficient_isZero (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor k n).obj
      ((derivedTensor k A M).obj (Q.obj (DGModuleCat.of A (InDegreeZero X))))) := by
  let X₀ := DGModuleCat.of A (InDegreeZero X)
  let Y := (DGModuleCat.tensorFunctor k (InDegreeZero M)).obj X₀
  let e : (derivedTensor k A M).obj (Q.obj X₀) ≅ Q.obj Y :=
    (QCompDerivedTensorIso k A M).app X₀
  let eH := (homologyFunctor k n).mapIso e
  have hY : Subsingleton (cohomology Y n) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    induction x using cohomology.induction_on with
    | h z =>
      have h₀ := Categorification.TensorProductOver.mem_grading_zero_inDegreeZero (B := A) (M := M) (N := X) z.val
      have hs := decompose_of_mem_same (grading (M := Y)) z.property.1
      have hn₀ := decompose_of_mem_ne (grading (M := Y)) h₀ (Ne.symm hn)
      have hz : z.val = 0 := hs.symm.trans hn₀
      apply (cohomology.mk_eq_zero_iff z).mpr
      rw [hz]
      exact zero_mem _
  have hZ : Subsingleton ((homologyFunctor k n).obj (Q.obj Y)) :=
    (cohomologyAddEquiv k Y n).symm.injective.subsingleton
  exact (ModuleCat.isZero_iff_subsingleton.mpr hZ).of_iso eH
end Vanishing

end
end Categorification

namespace Categorification

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero
noncomputable section

universe w u

section Shift
variable {k A R : Type u} [Field k] [Ring A]
    [AddCommGroup R] [Module k R] [Module Aᵐᵒᵖ R] [SMulCommClass k Aᵐᵒᵖ R]
    [DG.HasDerivedCategory.{w,u} k] [DG.HasDerivedCategory.{w,u} A]

private abbrev ordinaryObject (X : ModuleCat.{u} A) :=
  Q.obj (DGModuleCat.of A (InDegreeZero X))

/-- The homology shift across a short exact sequence in the ordinary left argument. -/
def derivedTensorOrdinaryLeftShift (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact)
    (n : ℤ)
    (h₀ : IsZero ((homologyFunctor k n).obj ((derivedTensor k A R).obj (ordinaryObject S.X₂))))
    (h₁ : IsZero ((homologyFunctor k (n+1)).obj ((derivedTensor k A R).obj (ordinaryObject S.X₂)))) :
    (homologyFunctor k n).obj ((derivedTensor k A R).obj (ordinaryObject S.X₃)) ≅
    (homologyFunctor k (n+1)).obj ((derivedTensor k A R).obj (ordinaryObject S.X₁)) := by
  let C := S.map (degreeZeroModuleFunctor A)
  let ex := exists_distinguished_of_shortExact C (degreeZeroModuleFunctor_shortExact S hS)
  let δ := Classical.choose ex
  let D := Triangle.mk (Q.map C.f) (Q.map C.g) δ
  let F := derivedTensor k A R
  exact homologyShiftIso k (F.mapTriangle.obj D) (F.map_distinguished D (Classical.choose_spec ex))
    n h₀ h₁

variable {M N P : Type u} [Algebra k A]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [SMulCommClass k Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module Aᵐᵒᵖ N] [SMulCommClass k Aᵐᵒᵖ N] [IsScalarTower k Aᵐᵒᵖ N]
  [AddCommGroup P] [Module k P] [Module Aᵐᵒᵖ P] [SMulCommClass k Aᵐᵒᵖ P] [IsScalarTower k Aᵐᵒᵖ P]

/-- The homology shift across a short exact sequence in the ordinary right argument. -/
def derivedTensorOrdinaryCoefficientShift (X : ModuleCat.{u} A)
    (f : M →ₗ[k] N) (hf : BalancedTensor.IsBimoduleHom (A := A) f)
    (g : N →ₗ[k] P) (hg : BalancedTensor.IsBimoduleHom (A := A) g)
    (hfg : Function.Exact f g) (hi : Function.Injective f) (hs : Function.Surjective g)
    (n : ℤ)
    (h₀ : IsZero ((homologyFunctor k n).obj ((derivedTensor k A N).obj (ordinaryObject X))))
    (h₁ : IsZero ((homologyFunctor k (n+1)).obj ((derivedTensor k A N).obj (ordinaryObject X)))) :
    (homologyFunctor k n).obj ((derivedTensor k A P).obj (ordinaryObject X)) ≅
    (homologyFunctor k (n+1)).obj ((derivedTensor k A M).obj (ordinaryObject X)) := by
  let ex := exists_distinguished_derivedTensorCoefficient X f hf g hg hfg hi hs
  let δ := Classical.choose ex
  let D := Triangle.mk ((derivedTensorCoefficientMap f hf).app (ordinaryObject X))
    ((derivedTensorCoefficientMap g hg).app (ordinaryObject X)) δ
  exact homologyShiftIso k D (Classical.choose_spec ex) n h₀ h₁

end Shift
end
end Categorification

set_option backward.isDefEq.respectTransparency false

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero
noncomputable section

universe w
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "TNorm" => TensorProductAlgebra k (parameter k) weights ν
local notation "ΛRaw" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "νRaw" => Multiset.replicate 2 ()
local notation "T" => TensorProductAlgebra k (parameter k) ΛRaw νRaw
local notation "K" => IncomingMiddleCokernel k
local notation "L" => labelTwoExteriorCokernel (parameter k)
private abbrev exteriorProjector : T := labelTwoLeftExteriorProjector (parameter k)
local notation "P" => lIdeal (exteriorProjector k)

local notation "σ" => tensorReflect (Q := parameter k) (Λ := ΛRaw) («ν» := νRaw)
local instance thirdTorCokernelModule : Module T K := inferInstanceAs (Module TNorm K)
local instance thirdTorCokernelScalarTower : IsScalarTower k T K := inferInstanceAs (IsScalarTower k TNorm K)

section Reflection

variable {𝕜 A U V : Type} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
  [AddCommGroup U] [Module 𝕜 U] [Module A U] [IsScalarTower 𝕜 A U]
  [AddCommGroup V] [Module 𝕜 V] [Module A V] [IsScalarTower 𝕜 A V]

private abbrev reflectLinear (τ : A →ₐ[𝕜] Aᵐᵒᵖ) (f : U →ₗ[A] V) :
    ReflectedRight τ U →ₗ[𝕜] ReflectedRight τ V := f.restrictScalars 𝕜

private theorem reflectLinear_bimodule (τ : A →ₐ[𝕜] Aᵐᵒᵖ) (f : U →ₗ[A] V) :
    BalancedTensor.IsBimoduleHom (A := A) (reflectLinear τ f) := by
  intro a u
  change f ((τ a).unop • (show U from u)) = (τ a).unop • f (show U from u)
  exact f.map_smul _ _

end Reflection

private abbrev finalAug : P →ₗ[T] L := labelTwoExteriorAugmentation (parameter k)

private abbrev descendedOutgoing : K →ₗ[T] P := incomingCokernelToExterior k

private theorem outgoing_reflected_exact :
    Function.Exact (reflectLinear (σ) (descendedOutgoing k))
      (reflectLinear (σ) (finalAug k)) := incomingCokernelToExterior_exact k

variable [DG.HasDerivedCategory.{w,0} k]
  [DG.HasDerivedCategory.{w,0} (TensorProductAlgebra k (parameter k)
    (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ()))]

local instance thirdTorNormalizedDerived : DG.HasDerivedCategory.{w,0} TNorm :=
  inferInstanceAs (DG.HasDerivedCategory.{w,0} T)

/-- Ambient cohomology of the reflected right factor tensored with the left factor. -/
abbrev reflectedAmbientHomology (M N : Type) [AddCommGroup M] [Module T M]
    [Module k M] [IsScalarTower k T M] [AddCommGroup N] [Module T N] (n : ℤ) : ModuleCat k :=
  (homologyFunctor k n).obj
    ((derivedTensor k T (ReflectedRight (σ) M)).obj (Q.obj (DGModuleCat.of T (InDegreeZero N))))

private theorem rightExterior_acyclic {X : Type} [AddCommGroup X] [Module T X]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor k n).obj ((derivedTensor k T (ReflectedRight (σ) P)).obj
      (Q.obj (DGModuleCat.of T (InDegreeZero X))))) := by
  let : Module.Projective T P := labelTwoLeftExterior_projective k
  let : Module.Projective Tᵐᵒᵖ (ReflectedRight (σ) P) :=
    ReflectedRight.projective (σ) unop_tensorReflect_unop_tensorReflect
  exact derivedTensor_projectiveCoefficient_isZero n hn

private theorem leftExterior_acyclic (X : Type) [AddCommGroup X] [Module k X] [Module Tᵐᵒᵖ X]
    [SMulCommClass k Tᵐᵒᵖ X] (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor k n).obj ((derivedTensor k T X).obj
      (Q.obj (DGModuleCat.of T (InDegreeZero P))))) := by
  exact isZero_homology_of_isZero_intHomology k _ n
    (labelTwoLeftExterior_derivedTensorHomology_isZero k X n hn)

private def leftShiftForSimple :
    reflectedAmbientHomology k L L (-3) ≅ reflectedAmbientHomology k L K (-2) :=
  derivedTensorOrdinaryLeftShift (R := ReflectedRight (σ) L) (outgoingCokernelShortComplex k)
    (outgoingCokernelShortComplex_shortExact k) (-3)
    (leftExterior_acyclic k (ReflectedRight (σ) L) (-3) (by decide))
    (leftExterior_acyclic k (ReflectedRight (σ) L) (-3 + 1) (by decide))

private def rightShiftForSimple :
    reflectedAmbientHomology k L K (-2) ≅ reflectedAmbientHomology k K K (-1) := by
  let X := ModuleCat.of T K
  let f : ReflectedRight (σ) K →ₗ[k] ReflectedRight (σ) P := reflectLinear (σ) (descendedOutgoing k)
  let g : ReflectedRight (σ) P →ₗ[k] ReflectedRight (σ) L := reflectLinear (σ) (finalAug k)
  exact derivedTensorOrdinaryCoefficientShift X f
    (reflectLinear_bimodule (σ) (descendedOutgoing k)) g
    (reflectLinear_bimodule (σ) (finalAug k)) (outgoing_reflected_exact k)
    (incomingCokernelToExterior_injective k) (labelTwoNormalizedAugmentation_surjective k) (-2)
    (rightExterior_acyclic k (X := K) (-2) (by decide))
    (rightExterior_acyclic k (X := K) (-2 + 1) (by decide))

/-- The third ambient Tor of the final simple vanishes if the first ambient Tor
of the intermediate incoming cokernel vanishes. -/
theorem labelTwoSimpleTorThree_isZero_of_cokernel
    (h : IsZero (reflectedAmbientHomology k K K (-1))) :
    IsZero (reflectedAmbientHomology k L L (-3)) :=
  h.of_iso ((leftShiftForSimple k).trans (rightShiftForSimple k))

/-- With two invertible, the third ambient self Tor of the actual
final simple vanishes once the middle standard is acyclic in degree −1. -/
theorem labelTwoSimpleTorThree_isZero_of_middleAcyclic [NeZero (2 : k)]
    (h : IsZero ((homologyFunctor k (-1)).obj
      ((derivedTensor k TNorm (MiddleTensorCoefficient k)).obj
        (Q.obj (DGModuleCat.of TNorm (InDegreeZero (Standard k))))))) :
    IsZero (reflectedAmbientHomology k L L (-3)) := by
  have hs := incomingCokernelTorOne_map_surjective_of_middleAcyclic k h
  have hc := incomingCokernelSelfTorOne_isZero_of_surjective k hs
  exact labelTwoSimpleTorThree_isZero_of_cokernel k hc

end
end Categorification.Stendhal.LabelTwo
