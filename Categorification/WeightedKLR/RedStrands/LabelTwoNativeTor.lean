/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoProjectiveResolution
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Tor over the label-two middle algebra

Webster, arXiv:1309.3796v2, §8.2, printed page 81, proof of Proposition 8.4.
The actual tensor of the periodic projective resolution identifies with
the specialized complex. Exact scalar restriction then identifies Mathlib
Tor over the middle algebra with the previously computed homology over
the ground field.
-/

namespace Categorification.Webster.LabelTwo

open CategoryTheory MonoidalCategory TensorProduct TrivSqZeroExt
open scoped DualNumber

noncomputable section

universe u
variable {k : Type u} [Field k]

attribute [local instance] quotientAlgebra quotientModule

local notation "A" => Middle k
local notation "B" => DualNumber k
local notation "V" => ModuleCat.of A A
local notation "W" => ModuleCat.of A B
local notation "shape" => ComplexShape.down ℕ

local instance : MonoidalCategory (ModuleCat.{u} A) :=
  ModuleCat.monoidalCategory (R := A)

/-- Tensor by the middle quotient and retain the ground-field action. -/
def tensorOverMiddle : ModuleCat.{u} A ⥤ ModuleCat.{u} k :=
  (tensorLeft W) ⋙ ModuleCat.restrictScalars (algebraMap k A)

instance : (tensorOverMiddle (k := k)).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change ((f.hom+g.hom).lTensor B) z = (f.hom.lTensor B) z+(g.hom.lTensor B) z
    rw [LinearMap.lTensor_add]
    rfl

local notation "F" => tensorOverMiddle (k := k)

private theorem specialize_algebraMap (r : k) :
    specialize (algebraMap k A r) = algebraMap k B r := by
  change specialize (inl (inl r))=inl r
  simp [specialize]

private def tensorRegularLinear : (F).obj V →ₗ[k] B where
  toFun z := TensorProduct.rid A B z
  map_add' x y := map_add (TensorProduct.rid A B) x y
  map_smul' r z := by
    change TensorProduct.rid A B ((algebraMap k A r) • (show B ⊗[A] A from z)) =
      r • TensorProduct.rid A B z
    rw [map_smul]
    change specialize (algebraMap k A r) * (TensorProduct.rid A B z) =
      r • TensorProduct.rid A B z
    rw [specialize_algebraMap,← Algebra.smul_def]

private def tensorRegularEquiv : (F).obj V ≃ₗ[k] B :=
  LinearEquiv.ofBijective (tensorRegularLinear (k := k)) (TensorProduct.rid A B).bijective

private theorem periodic_d_succ (n : ℕ) :
    ((periodicComplex (k := k)).d (n+1) n).hom = if Even n then plus else minus := by
  change (ChainComplex.of.d (fun _ => V) _ (n+1) n).hom = _
  rw [ChainComplex.of_d]
  change (if Even n then ModuleCat.ofHom (plus (k := k)) else ModuleCat.ofHom minus).hom = _
  by_cases h : Even n <;> simp [h]

private theorem tensor_d_succ (n : ℕ) :
    ((postTensorComplex (k := k)).d (n+1) n).hom = if Even n then 0 else twiceEps := by
  change (ChainComplex.of.d (fun _ => ModuleCat.of k B) _ (n+1) n).hom = _
  rw [ChainComplex.of_d]
  change (if Even n then 0 else ModuleCat.ofHom (twiceEps (k := k))).hom = _
  by_cases h : Even n <;> simp [h]

local notation "L" => Functor.obj (Functor.mapHomologicalComplex (F) (shape)) (periodicComplex (k := k))
local notation "T" => postTensorComplex (k := k)

/-- The actual tensor of the projective resolution is the specialized chain complex. -/
def tensorResolutionIso : (L) ≅ (T) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun _ => (tensorRegularEquiv (k := k)).toModuleIso) ?_
  intro i j h
  obtain rfl : i = j+1 := h.symm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change ((T).d (j+1) j).hom (TensorProduct.rid A B z) =
    TensorProduct.rid A B (((periodicComplex (k := k)).d (j+1) j).hom.lTensor B z)
  rw [tensor_d_succ,periodic_d_succ]
  by_cases hj : Even j
  · rw [ite_eq_left hj,ite_eq_left hj,LinearMap.zero_apply]
    exact (tensor_plus_zero z).symm
  · rw [ite_eq_right hj,ite_eq_right hj,twiceEps_apply]
    exact (tensor_minus_mul z).symm

local instance : MonoidalPreadditive (ModuleCat.{u} A) :=
  ModuleCat.instMonoidalPreadditive (R := A)

private abbrev restrictMiddle : ModuleCat.{u} A ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k A)

local notation "restr" => restrictMiddle (k := k)
local notation "G" => tensorLeft W

/-- Mathlib's middle Tor, viewed as a module over the ground field. -/
abbrev middleTor (n : ℕ) : ModuleCat k :=
  Functor.obj (restr) (Functor.obj (Functor.obj (CategoryTheory.Tor (ModuleCat A) n) W) W)

/-- Restricting scalars identifies the native Tor groups with the
homology of the specialized middle complex. -/
def middleTorHomologyIso (n : ℕ) : middleTor (k := k) n ≅ (T).homology n := by
  let P := periodicProjectiveResolution (k := k)
  let K := ((G).mapHomologicalComplex (shape)).obj P.complex
  have e₁ : middleTor (k := k) n ≅ (restr).obj (K.homology n) :=
    (restr).mapIso (P.isoLeftDerivedObj (G) n)
  have hExact (S : ShortComplex (ModuleCat.{u} A)) (hS : S.Exact) :
      (S.map (restr)).Exact := by
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS
  have preserving := ((Functor.exact_tfae (restr)).out 2 4).mp hExact
  letI : Limits.PreservesFiniteLimits (restr) := preserving.1
  letI : Limits.PreservesFiniteColimits (restr) := preserving.2
  letI : (restr).PreservesHomology := Functor.preservesHomologyOfExact (restr)
  have e₂ : (restr).obj (K.homology n) ≅ (L).homology n :=
    ((K.sc n).mapHomologyIso (restr)).symm
  exact e₁ ≪≫ e₂ ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat k) (shape) n).mapIso
      (tensorResolutionIso (k := k))

/-- The middle Tor at degree zero is the single dual-number quotient. -/
def middleTorZero : middleTor (k := k) 0 ≅ ModuleCat.of k B :=
  middleTorHomologyIso 0 ≪≫ postTensorHomologyZero

/-- Each positive middle Tor over a field of characteristic different from
two is one-dimensional. -/
def middleTorPositive (n : ℕ) (h2 : (2:k)≠0) :
    middleTor (k := k) (n+1) ≅ ModuleCat.of k k :=
  middleTorHomologyIso (n+1) ≪≫
    if h : Even n then postTensorHomologyOdd n h h2
    else postTensorHomologyPositiveEven n h h2

end

end Categorification.Webster.LabelTwo
