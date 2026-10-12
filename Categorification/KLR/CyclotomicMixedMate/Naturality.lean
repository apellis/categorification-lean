/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.MixedMate

/-!
# Naturality of the original mixed mate

The actual crossing and ordinary mate commute with arbitrary module morphisms.
These equalities are used to prove naturality of the inverse mixed mate.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.MixedMate
open MulOpposite
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  (γ : Multiset I) (i j : I)
variable (N N' : Type w) [AddCommGroup N] [Module k N]
  [Module (CycKLR k Q a γ) N] [IsScalarTower k (CycKLR k Q a γ) N]
  [AddCommGroup N'] [Module k N'] [Module (CycKLR k Q a γ) N']
  [IsScalarTower k (CycKLR k Q a γ) N']

/-- Postcompose the crossing with original double induction of a morphism. -/
def naturalityLeft (f : N →ₗ[CycKLR k Q a γ] N') :
    Ind Q i a ({j} + γ) (Ind Q j a γ N) →ₗ[k]
      Ind Q j a ({i} + γ) (Ind Q i a γ N') :=
  ((doubleMap Q a γ j i N f).restrictScalars k).comp (crossing Q a γ i j N)

/-- Precompose the crossing with original double induction of a morphism. -/
def naturalityRight (f : N →ₗ[CycKLR k Q a γ] N') :
    Ind Q i a ({j} + γ) (Ind Q j a γ N) →ₗ[k]
      Ind Q j a ({i} + γ) (Ind Q i a γ N') :=
  (crossing Q a γ i j N').comp ((doubleMap Q a γ i j N f).restrictScalars k)

/-- Naturality on every original lower module morphism. -/
theorem crossing_natural (f : N →ₗ[CycKLR k Q a γ] N') :
    naturalityLeft Q a γ i j N N' f = naturalityRight Q a γ i j N N' f := by
  apply BalancedTensor.ext
  intro z m
  induction m using BalancedTensor.induction_on with
  | zero => simp only [BalancedTensor.tmul_zero, map_zero]
  | add m m' hm hm' => simp only [BalancedTensor.tmul_add, map_add, hm, hm']
  | tmul y n =>
    change BalancedTensor.mapRight (BalancedTensor.mapRight f)
      (crossing Q a γ i j N (BalancedTensor.tmul z (BalancedTensor.tmul y n))) =
      crossing Q a γ i j N'
        (BalancedTensor.mapRight (BalancedTensor.mapRight f)
          (BalancedTensor.tmul z (BalancedTensor.tmul y n)))
    simp only [crossing_tmul, BalancedTensor.mapRight_tmul]

open scoped ModuleCat.Algebra
variable (M M' : Type w) [AddCommGroup M] [Module k M]
  [Module (CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)) M]
  [IsScalarTower k (CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)) M]
  [AddCommGroup M'] [Module k M']
  [Module (CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)) M']
  [IsScalarTower k (CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)) M']
local notation "C" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)
local notation "A" => CycKLR k Q a ((Singleton.singleton j : Multiset I) + γ)
local notation "U" => CycKLR k Q a
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton j : Multiset I) + γ))
local notation "V" => CycKLR k Q a
  ((Singleton.singleton j : Multiset I) + ((Singleton.singleton i : Multiset I) + γ))

def mateSourceMap (f : M →ₗ[C] M') :
    Ind Q j a γ (Res Q i a γ M) →ₗ[A] Ind Q j a γ (Res Q i a γ M') :=
  BalancedTensor.mapRight (N := Res Q i a γ M) (N' := Res Q i a γ M')
    (resMap Q i a γ M f)

def upperIndMap (f : M →ₗ[C] M') :
    (upperTransport Q a γ i j).obj (ModuleCat.of V (Ind Q j a ({i} + γ) M)) →ₗ[U]
      (upperTransport Q a γ i j).obj (ModuleCat.of V (Ind Q j a ({i} + γ) M')) where
  toFun t := indMap Q j a ({i} + γ) M f t
  map_add' := map_add _
  map_smul' s t := (indMap Q j a ({i} + γ) M f).map_smul ((κ Q a γ i j).symm s)
    (show Ind Q j a ({i} + γ) M from t)

def mateTargetMap (f : M →ₗ[C] M') :
    Res Q i a ({j} + γ)
      ((upperTransport Q a γ i j).obj (ModuleCat.of V (Ind Q j a ({i} + γ) M))) →ₗ[A]
    Res Q i a ({j} + γ)
      ((upperTransport Q a γ i j).obj (ModuleCat.of V (Ind Q j a ({i} + γ) M'))) :=
  resMap Q i a ({j} + γ) _ (upperIndMap Q a γ i j M M' f)

/-- The computed original ordinary mate is natural on all module morphisms. -/
theorem mate_natural (f : M →ₗ[C] M') :
    (mateTargetMap Q a γ i j M M' f).comp (mate Q a γ i j M) =
      (mate Q a γ i j M').comp (mateSourceMap Q a γ i j M M' f) := by
  apply BalancedTensor.extB
  intro y m
  apply Subtype.ext
  change indMap Q j a ({i} + γ) M f (mate Q a γ i j M (BalancedTensor.tmul y m)).1 =
    (mate Q a γ i j M'
      (BalancedTensor.tmul y (resMap Q i a γ M f m))).1
  rw [mate_tmul, mate_tmul]
  rfl

end Categorification.KLR.KLRAlgebra.AbsentColour.MixedMate
