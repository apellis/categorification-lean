/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoPeriodic
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The specialized label-two unknot complex

Webster, arXiv:1309.3796v2, §8.2, printed page 81, proof of Proposition 8.4.
Tensoring the periodic middle resolution with the quotient by the plus
differential alternates zero with multiplication by twice epsilon. This
module computes the ungraded homology of that complex over a field where
two is nonzero.
-/

namespace Categorification.Webster.LabelTwo

universe u

open TrivSqZeroExt
open scoped DualNumber

section Periodic

variable {k : Type*} [CommRing k]

/-- Specialization to the relation `y₁ + y₂ = 0`, with `y₁` sent to `ε`. -/
def specialize : Middle k →ₐ[DualNumber k] DualNumber k :=
  DualNumber.lift ⟨(AlgHom.id _ _, -ε), by simp, fun _ => Commute.all _ _⟩

@[simp] theorem specialize_y₁ : specialize (y₁ : Middle k) = ε := by
  simp [specialize,y₁]

@[simp] theorem specialize_y₂ : specialize (y₂ : Middle k) = -ε := by
  simp [specialize,y₂]

private theorem specialize_coordinates (a b c d : k) :
    specialize (⟨⟨a,b⟩,⟨c,d⟩⟩ : Middle k) = ⟨a,b-c⟩ := by
  apply TrivSqZeroExt.ext
  · change a+(c* -0)=a
    simp
  · change b+(c* -1+d* -0)=b-c
    simp [sub_eq_add_neg]

local instance quotientAlgebra : Algebra (Middle k) (DualNumber k) :=
  (specialize (k := k)).toRingHom.toAlgebra
local instance quotientModule : Module (Middle k) (DualNumber k) :=
  (quotientAlgebra (k := k)).toModule

/-- The augmentation by the middle quotient, viewed as a module map. -/
abbrev augmentation : Middle k →ₗ[Middle k] DualNumber k :=
  Algebra.linearMap (Middle k) (DualNumber k)

theorem augmentation_surjective : Function.Surjective (augmentation (k := k)) := by
  intro x
  refine ⟨inl x,?_⟩
  change specialize (inl x) = x
  simp [specialize]

theorem ker_augmentation : (augmentation (k := k)).ker = plus.range := by
  ext x
  change specialize x = 0 ↔ _
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  constructor
  · intro hx
    rw [specialize_coordinates] at hx
    have ha : a=0 := congrArg (fun z : DualNumber k => z.fst) hx
    have hc : b-c=0 := congrArg (fun z : DualNumber k => z.snd) hx
    have hc' : c=b := (sub_eq_zero.mp hc).symm
    subst a
    subst c
    exact ⟨⟨⟨b,0⟩,⟨d,0⟩⟩, by rw [plus_coordinates,add_zero]⟩
  · rintro ⟨⟨⟨e,f⟩,⟨g,h⟩⟩,hx⟩
    rw [← hx,plus_coordinates,specialize_coordinates,sub_self]
    rfl

private noncomputable def quotEquivOfKerEq {R M N : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (q : M →ₗ[R] N) (P : Submodule R M) (hq : Function.Surjective q)
    (hker : q.ker = P) : (M ⧸ P) ≃ₗ[R] N :=
  (Submodule.quotEquivOfEq P q.ker hker.symm).trans (q.quotKerEquivOfSurjective hq)

open TensorProduct

local notation "A" => Middle k
local notation "B" => DualNumber k

/-- The regular middle module tensored over the middle algebra with the quotient. -/
noncomputable def tensorQuotientEquiv : B ⊗[A] A ≃ₗ[B] B := AlgebraTensorModule.rid A B B

/-- The plus differential vanishes after tensoring with the quotient. -/
theorem tensor_plus_zero (z : B ⊗[A] A) :
    tensorQuotientEquiv (AlgebraTensorModule.lTensor B B (plus (k := k)) z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul b a =>
      rw [AlgebraTensorModule.lTensor_tmul, tensorQuotientEquiv, AlgebraTensorModule.rid_tmul]
      change specialize ((y₁+y₂)*a)*b = 0
      simp
  | add z₁ z₂ h₁ h₂ => rw [map_add,map_add,h₁,h₂,add_zero]

/-- The minus differential becomes multiplication by `2ε` after tensoring. -/
theorem tensor_minus_mul (z : B ⊗[A] A) :
    tensorQuotientEquiv (AlgebraTensorModule.lTensor B B (minus (k := k)) z) =
      (ε+ε)*tensorQuotientEquiv z := by
  induction z using TensorProduct.inductionOn with
  | tmul b a =>
      rw [AlgebraTensorModule.lTensor_tmul, tensorQuotientEquiv,
        AlgebraTensorModule.rid_tmul, AlgebraTensorModule.rid_tmul]
      change specialize ((y₁-y₂)*a)*b = (ε+ε)*(specialize a*b)
      simp [mul_assoc,sub_eq_add_neg]
  | add z₁ z₂ h₁ h₂ => rw [map_add,map_add,map_add,h₁,h₂,mul_add]


end Periodic

section Homology

variable {k : Type u} [Field k]

local notation "B" => DualNumber k

open CategoryTheory CategoryTheory.Limits

private abbrev scalarPart : B →ₗ[k] k := (TrivSqZeroExt.fstHom k k k).toLinearMap

/-- The only nonzero differential in the specialized complex. -/
def twiceEps : B →ₗ[k] B := (2:k) • (inrHom k k).comp scalarPart

theorem twiceEps_eq_zero_of_two_eq_zero (h2 : (2:k)=0) :
    (twiceEps (k := k)) = 0 := by
  rw [twiceEps,h2,zero_smul]

theorem twiceEps_coordinates (x : B) : twiceEps x = inr ((2:k)*x.fst) := by
  apply TrivSqZeroExt.ext
  · change (2:k)*0 = 0
    exact mul_zero _
  · rfl

theorem twiceEps_apply (x : B) : twiceEps x = (ε+ε)*x := by
  rw [twiceEps_coordinates]
  apply TrivSqZeroExt.ext
  · change 0 = (0+0)*x.fst
    simp
  · change (2:k)*x.fst = (0+0)*x.snd+(1+1)*x.fst
    rw [zero_add,zero_mul,zero_add,one_add_one_eq_two]

theorem ker_twiceEps (h2 : (2:k)≠0) :
    (twiceEps (k := k)).ker = scalarPart.ker := by
  ext x
  change twiceEps x = 0 ↔ x.fst = 0
  rw [twiceEps_coordinates]
  constructor
  · intro h
    have hx : (2:k)*x.fst=0 := congrArg (fun z : B => z.snd) h
    exact (mul_eq_zero.mp hx).resolve_left h2
  · intro h
    rw [h,mul_zero,inr_zero]

theorem range_twiceEps (h2 : (2:k)≠0) :
    (twiceEps (k := k)).range = scalarPart.ker := by
  ext x
  change (∃ z : B, twiceEps z=x) ↔ x.fst=0
  constructor
  · rintro ⟨z,rfl⟩
    rw [twiceEps_coordinates]
    rfl
  · intro hx
    refine ⟨inl (x.snd/2),?_⟩
    rw [twiceEps_coordinates]
    apply TrivSqZeroExt.ext
    · exact hx.symm
    · change (2:k)*(x.snd/2)=x.snd
      rw [mul_comm,div_mul_cancel₀ _ h2]

private def scalarCyclesEquiv : (scalarPart (k := k)).ker ≃ₗ[k] k where
  toFun x := x.val.snd
  invFun a := ⟨inr a,rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply TrivSqZeroExt.ext
    · exact (show x.val.fst=0 from x.prop).symm
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem scalarPart_surjective : Function.Surjective (scalarPart (k := k)) :=
  fun a => ⟨inl a,rfl⟩

local notation "V" => ModuleCat.of k (DualNumber k)
local notation "D" => ModuleCat.ofHom (twiceEps (k := k))

/-- In an odd degree, the incoming differential is twice epsilon and the
outgoing differential is zero. -/
def postTensorOdd : ShortComplex (ModuleCat.{u} k) :=
  ShortComplex.mk (X₁ := V) (X₂ := V) (X₃ := V) D 0 comp_zero

/-- In a positive even degree, the incoming differential is zero and the
outgoing differential is twice epsilon. -/
def postTensorPositiveEven : ShortComplex (ModuleCat.{u} k) :=
  ShortComplex.mk (X₁ := V) (X₂ := V) (X₃ := V) 0 D zero_comp

/-- At degree zero, both differentials are zero. -/
def postTensorZero : ShortComplex (ModuleCat.{u} k) :=
  ShortComplex.mk (X₁ := V) (X₂ := V) (X₃ := V) 0 0 comp_zero

private noncomputable def scalarQuotientEquiv (h2 : (2:k)≠0) :
    (B ⧸ (twiceEps (k := k)).range) ≃ₗ[k] k :=
  quotEquivOfKerEq scalarPart (twiceEps (k := k)).range scalarPart_surjective
    (range_twiceEps h2).symm

private def epsilonEquiv (h2 : (2:k)≠0) : (twiceEps (k := k)).ker ≃ₗ[k] k :=
  (LinearEquiv.ofEq _ _ (ker_twiceEps h2)).trans scalarCyclesEquiv

/-- The kernel of multiplication by twice epsilon is the epsilon line. -/
noncomputable abbrev twiceEpsKernelEquiv (h₂ : (2 : k) ≠ 0) :
    (twiceEps (k := k)).ker ≃ₗ[k] k := epsilonEquiv h₂

/-- The cokernel of multiplication by twice epsilon is the scalar line. -/
noncomputable abbrev twiceEpsCokernelEquiv (h₂ : (2 : k) ≠ 0) :
    (B ⧸ (twiceEps (k := k)).range) ≃ₗ[k] k := scalarQuotientEquiv h₂

/-- The odd homology is represented by the scalar class of the quotient. -/
noncomputable def oddHomologyIso (h2 : (2:k)≠0) :
    (postTensorOdd (k := k)).homology ≅ ModuleCat.of k k :=
  (ShortComplex.LeftHomologyData.ofHasCokernel (S := postTensorOdd (k := k)) rfl).homologyIso ≪≫
    ModuleCat.cokernelIsoRangeQuotient D ≪≫ (scalarQuotientEquiv h2).toModuleIso

/-- The positive even homology is represented by the epsilon line. -/
noncomputable def positiveEvenHomologyIso (h2 : (2:k)≠0) :
    (postTensorPositiveEven (k := k)).homology ≅ ModuleCat.of k k :=
  (ShortComplex.LeftHomologyData.ofHasKernel (S := postTensorPositiveEven (k := k)) rfl).homologyIso ≪≫
    ModuleCat.kernelIsoKer D ≪≫ (epsilonEquiv h2).toModuleIso

/-- The degree-zero homology is the middle quotient itself. -/
noncomputable def zeroHomologyIso : (postTensorZero (k := k)).homology ≅ V :=
  (ShortComplex.LeftHomologyData.ofZeros (S := postTensorZero (k := k)) rfl rfl).homologyIso

private noncomputable def tensorDifferential (n : ℕ) : V ⟶ V :=
  if Even n then 0 else D

private theorem tensorDifferential_square (n : ℕ) :
    tensorDifferential (k := k) (n+1) ≫ tensorDifferential n = 0 := by
  by_cases h : Even n <;> simp [tensorDifferential,Nat.even_add_one,h]

/-- The specialized periodic chain complex, indexed with its augmentation
removed so that `degree n+1 → degree n` vanishes for even `n`. -/
noncomputable abbrev postTensorComplex : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (fun _ => V) tensorDifferential tensorDifferential_square

local notation "T" => postTensorComplex (k := k)
local notation "shape" => ComplexShape.down ℕ

private noncomputable def postTensorZeroIso : ((T).sc' 1 0 0) ≅ postTensorZero := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · change 𝟙 V ≫ 0 = (T).d (0+1) 0 ≫ 𝟙 V
    rw [Category.id_comp,Category.comp_id]
    change 0 = ChainComplex.of.d (fun _ => V) tensorDifferential (0+1) 0
    have hz : (0 : V ⟶ V) = tensorDifferential (k := k) 0 := by
      simp [tensorDifferential]
    exact hz.trans (ChainComplex.of_d (fun _ : ℕ => V) (tensorDifferential (k := k)) 0).symm
  · change 𝟙 V ≫ 0 = (T).d 0 0 ≫ 𝟙 V
    rw [Category.id_comp,Category.comp_id]
    exact ((T).shape 0 0 (by decide)).symm

private noncomputable def postTensorOddIso (n : ℕ) (h : Even n) :
    ((T).sc' (n+2) (n+1) n) ≅ postTensorOdd := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · change 𝟙 V ≫ D = (T).d ((n+1)+1) (n+1) ≫ 𝟙 V
    rw [Category.id_comp,Category.comp_id]
    change D = ChainComplex.of.d (fun _ => V) tensorDifferential ((n+1)+1) (n+1)
    simp [ChainComplex.of_d,tensorDifferential,Nat.even_add_one,h]
  · change 𝟙 V ≫ 0 = (T).d (n+1) n ≫ 𝟙 V
    rw [Category.id_comp,Category.comp_id]
    change 0 = ChainComplex.of.d (fun _ => V) tensorDifferential (n+1) n
    simp [ChainComplex.of_d,tensorDifferential,h]

private noncomputable def postTensorPositiveEvenIso (n : ℕ) (h : ¬ Even n) :
    ((T).sc' (n+2) (n+1) n) ≅ postTensorPositiveEven := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · change 𝟙 V ≫ 0 = (T).d ((n+1)+1) (n+1) ≫ 𝟙 V
    rw [Category.id_comp,Category.comp_id]
    change 0 = ChainComplex.of.d (fun _ => V) tensorDifferential ((n+1)+1) (n+1)
    simp [ChainComplex.of_d,tensorDifferential,Nat.even_add_one,h]
  · change 𝟙 V ≫ D = (T).d (n+1) n ≫ 𝟙 V
    rw [Category.id_comp,Category.comp_id]
    change D = ChainComplex.of.d (fun _ => V) tensorDifferential (n+1) n
    simp [ChainComplex.of_d,tensorDifferential,h]

/-- Degree zero of the specialized complex has the two quotient classes. -/
noncomputable def postTensorHomologyZero : (T).homology 0 ≅ V :=
  (T).homologyIsoSc' 1 0 0 ((shape).prev_eq' rfl)
    ((shape).next_eq_self' 0 (by simp [ComplexShape.down_Rel])) ≪≫
  ShortComplex.homologyMapIso postTensorZeroIso ≪≫ zeroHomologyIso

/-- The homology at a positive odd degree is one-dimensional, with its
scalar representative. -/
noncomputable def postTensorHomologyOdd (n : ℕ) (h : Even n) (h2 : (2:k)≠0) :
    (T).homology (n+1) ≅ ModuleCat.of k k :=
  (T).homologyIsoSc' (n+2) (n+1) n ((shape).prev_eq' rfl) ((shape).next_eq' rfl) ≪≫
  ShortComplex.homologyMapIso (postTensorOddIso n h) ≪≫ oddHomologyIso h2

/-- The homology at a positive even degree is one-dimensional, with its
epsilon representative. -/
noncomputable def postTensorHomologyPositiveEven (n : ℕ) (h : ¬ Even n) (h2 : (2:k)≠0) :
    (T).homology (n+1) ≅ ModuleCat.of k k :=
  (T).homologyIsoSc' (n+2) (n+1) n ((shape).prev_eq' rfl) ((shape).next_eq' rfl) ≪≫
  ShortComplex.homologyMapIso (postTensorPositiveEvenIso n h) ≪≫ positiveEvenHomologyIso h2

end Homology

end Categorification.Webster.LabelTwo
