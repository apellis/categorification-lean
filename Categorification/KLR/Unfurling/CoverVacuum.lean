/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.CoverVanishing
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The rank-zero vacuum of the unfurled product

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
proof of the theorem labelled `nondegenerate`, construction of representations.
The rank-zero cyclotomic algebra is the coefficient field. Consequently the
vacuum is the scalar-restriction functor between the two rank-zero weight spaces.
Its endomorphisms are scalars: evaluation on the regular module at one is
injective, and gives an algebra map to the field. In particular the endomorphism
ring is reduced. This construction imposes no condition on the levels or graph.

`coverProduct_vacuum_inl` and `coverProduct_vacuum_inr` give the lowest- and
highest-weight vanishing, respectively. These are the categorical inputs for
the vanishing hypotheses in `VacuumFurlingNilpotent`; concentration at the zero
furling block is a separate operation.
-/

open CategoryTheory CategoryTheory.Limits
open Categorification.TwoRep Categorification.KLR.CyclotomicAction
noncomputable section
namespace Categorification.KLR.Unfurling
universe u v w
variable {J : Type u} [DecidableEq J] {L : Type v} [Field L]
variable (n : J → J → ℕ) (Λ : J → ℕ)
abbrev VacuumBlocks := WeightBlocks (coverWeight n) ((fun j => (Λ j : ℤ)), 0)
  (-((fun j => (Λ j : ℤ)), 0))
def vacuumBlock : VacuumBlocks n Λ := ⟨0, by simp [blockWeight]⟩
instance : Subsingleton (VacuumBlocks n Λ) := coverWeight_weightBlocks_subsingleton n _ _
theorem vacuumBlock_eq_zero (β : VacuumBlocks n Λ) : β.1 = 0 :=
  congrArg Subtype.val (Subsingleton.elim β (vacuumBlock n Λ))
abbrev vacuumRing (β : VacuumBlocks n Λ) := CycKLR L (unfQ n) (fun j => Polynomial.X ^ Λ j) β.1

def vacuumRingEquiv (β : VacuumBlocks n Λ) : vacuumRing (L := L) n Λ β ≃ₐ[L] L :=
  (castCyc _ _ (vacuumBlock_eq_zero n Λ β)).trans
    (KLRAlgebra.cyclotomicZeroEquiv _ _)

def vacuumRegular : (coverFamily.{u,v,0} n (L := L) Λ).obj
    (-((fun j => (Λ j : ℤ)), 0)) :=
  fun β => ModuleCat.of (vacuumRing (L := L) n Λ β) (vacuumRing (L := L) n Λ β)

def vacuumGen (X : (coverFamily.{u,v,0} n (L := L) Λ).obj
    (-((fun j => (Λ j : ℤ)), 0))) (x : X (vacuumBlock n Λ)) :
    vacuumRegular n Λ ⟶ X := by
  intro β
  have hβ : β = vacuumBlock n Λ := Subsingleton.elim _ _
  subst β
  exact ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x)

@[simp] theorem vacuumGen_apply (X : (coverFamily.{u,v,0} n (L := L) Λ).obj
    (-((fun j => (Λ j : ℤ)), 0))) (x : X (vacuumBlock n Λ))
    (r : vacuumRing (L := L) n Λ (vacuumBlock n Λ)) :
    vacuumGen n Λ X x (vacuumBlock n Λ) r = r • x := rfl

theorem coverFamily_vacuum_lower (a : J) {x y}
    (h : x + (coverWeight n).iX a = y) (hy : y = -((fun j => (Λ j : ℤ)), 0)) :
    IsZero ((coverFamily.{u,v,w} n (L := L) Λ).E a h) ∧
      IsZero ((coverFamily.{u,v,w} n (L := L) Λ).F a h) := by
  subst hy
  have hz : IsEmpty (WeightBlocks (coverWeight n) ((fun j => (Λ j : ℤ)), 0) x) := by
    refine ⟨fun β => ?_⟩
    have he := vacuumBlock_eq_zero n Λ (blockSucc (coverWeight n) _ a h β)
    have hc := congrArg Multiset.card he
    simp only [blockSucc_val, Multiset.card_add, Multiset.card_singleton, Multiset.card_zero] at hc
    omega
  exact ⟨isZero_from_weightSpace _ _ _ _ hz _, isZero_to_weightSpace _ _ _ _ hz _⟩

variable {J₂ : Type u} [DecidableEq J₂] (n₂ : J₂ → J₂ → ℕ) (Λ₂ : J₂ → ℕ)

theorem coverProduct_vacuum_inl (a : J) {x y}
    (h : x + ((coverWeight n).prod (coverWeight n₂)).iX (.inl a) = y)
    (hy : y.1 = -((fun j => (Λ j : ℤ)), 0)) :
    IsZero ((coverProduct.{u,v,w} n (L := L) Λ n₂ Λ₂).E (.inl a) h) ∧
      IsZero ((coverProduct.{u,v,w} n (L := L) Λ n₂ Λ₂).F (.inl a) h) := by
  have hz := coverFamily_vacuum_lower.{u,v,w} n (L := L) Λ a
    (RouqFamily.fst_step (RD₂ := coverWeight n₂) a h) hy
  exact RouqFamily.homProduct_isZero_inl L _ _ a h hz.1 hz.2

theorem coverProduct_vacuum_inr (a : J₂) {x y}
    (h : x + ((coverWeight n).prod (coverWeight n₂)).iX (.inr a) = y)
    (hx : x.2 = ((fun j => (Λ₂ j : ℤ)), 0)) :
    IsZero ((coverProduct.{u,v,w} n (L := L) Λ n₂ Λ₂).E (.inr a) h) ∧
      IsZero ((coverProduct.{u,v,w} n (L := L) Λ n₂ Λ₂).F (.inr a) h) := by
  have hz := coverFamily_vacuum_lower.{u,v,w} n₂ (L := L) Λ₂ a
    (RouqFamily.neg_reg a (RouqFamily.snd_step (RD₁ := coverWeight n) a h))
    (congrArg Neg.neg hx)
  exact RouqFamily.homProduct_isZero_inr L _ _ a h hz.1 hz.2


def vacuumFunctor :
    (coverFamily.{u,v,0} n₂ (L := L) Λ₂).obj (-((fun j => (Λ₂ j : ℤ)), 0)) ⥤
    (coverFamily.{u,v,0} n (L := L) Λ).obj (-((fun j => (Λ j : ℤ)), 0)) :=
  Pi.eval _ (vacuumBlock n₂ Λ₂) ⋙
    ModuleCat.restrictScalars (algebraMap L (vacuumRing (L := L) n₂ Λ₂ (vacuumBlock n₂ Λ₂))) ⋙
    Functor.pi' (fun β => ModuleCat.restrictScalars (vacuumRingEquiv n Λ β).toAlgHom.toRingHom)

instance : (vacuumFunctor n (L := L) Λ n₂ Λ₂).Additive where
  map_add := by intros; rfl
instance : (vacuumFunctor n (L := L) Λ n₂ Λ₂).Linear L where
  map_smul := by
    intros X Y f r
    funext β
    apply ModuleCat.hom_ext
    ext x
    change (algebraMap L (vacuumRing (L := L) n₂ Λ₂ (vacuumBlock n₂ Λ₂)) r) •
        f (vacuumBlock n₂ Λ₂) x =
      (algebraMap L (vacuumRing (L := L) n₂ Λ₂ (vacuumBlock n₂ Λ₂))
        ((vacuumRingEquiv n Λ β) (algebraMap L _ r))) • f (vacuumBlock n₂ Λ₂) x
    rw [AlgEquiv.commutes]
    rfl

def vacuum : ((coverProduct.{u,v,0} n (L := L) Λ n₂ Λ₂).obj
    (-((fun j => (Λ j : ℤ)), 0), ((fun j => (Λ₂ j : ℤ)), 0))) :=
  LinearCat.LinFun.of (vacuumFunctor n Λ n₂ Λ₂)

def vacuumValue (η : End (vacuum n (L := L) Λ n₂ Λ₂)) :
    vacuumRing (L := L) n₂ Λ₂ (vacuumBlock n₂ Λ₂) :=
  η.hom.app (vacuumRegular n₂ Λ₂) (vacuumBlock n Λ)
    (1 : vacuumRing (L := L) n₂ Λ₂ (vacuumBlock n₂ Λ₂))

def vacuumEval (η : End (vacuum n (L := L) Λ n₂ Λ₂)) : L :=
  vacuumRingEquiv n₂ Λ₂ (vacuumBlock n₂ Λ₂) (vacuumValue n Λ n₂ Λ₂ η)

theorem vacuum_end_apply (η : End (vacuum n (L := L) Λ n₂ Λ₂))
    (X : (coverFamily.{u,v,0} n₂ (L := L) Λ₂).obj (-((fun j => (Λ₂ j : ℤ)), 0)))
    (x : X (vacuumBlock n₂ Λ₂)) :
    η.hom.app X (vacuumBlock n Λ) x = (vacuumValue n Λ n₂ Λ₂ η) • x := by
  have hn := congrArg (fun f => f (vacuumBlock n Λ)
      (1 : vacuumRing (L := L) n₂ Λ₂ (vacuumBlock n₂ Λ₂)))
    (η.hom.naturality (vacuumGen n₂ Λ₂ X x))
  change η.hom.app X (vacuumBlock n Λ)
    ((1 : vacuumRing (L := L) n₂ Λ₂ (vacuumBlock n₂ Λ₂)) • x) =
    (vacuumValue n Λ n₂ Λ₂ η) • x at hn
  simpa only [one_smul] using hn

theorem vacuumEval_injective : Function.Injective (vacuumEval n (L := L) Λ n₂ Λ₂) := by
  intro η θ h
  have he := (vacuumRingEquiv n₂ Λ₂ (vacuumBlock n₂ Λ₂)).injective h
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X β
  have hβ : β = vacuumBlock n Λ := Subsingleton.elim _ _
  subst β
  apply ModuleCat.hom_ext
  ext x
  have hη := vacuum_end_apply n Λ n₂ Λ₂ η X x
  have hθ := vacuum_end_apply n Λ n₂ Λ₂ θ X x
  rw [he] at hη
  exact hη.trans hθ.symm

def vacuumEv : End (vacuum n (L := L) Λ n₂ Λ₂) →ₐ[L] L where
  toFun := vacuumEval n Λ n₂ Λ₂
  map_zero' := by
    change (vacuumRingEquiv n₂ Λ₂ (vacuumBlock n₂ Λ₂)) 0 = 0
    exact map_zero _
  map_one' := by
    change (vacuumRingEquiv n₂ Λ₂ (vacuumBlock n₂ Λ₂)) 1 = 1
    exact map_one _
  map_add' η θ := by
    change (vacuumRingEquiv n₂ Λ₂ (vacuumBlock n₂ Λ₂))
      (vacuumValue n Λ n₂ Λ₂ η + vacuumValue n Λ n₂ Λ₂ θ) = _
    exact map_add _ _ _
  map_mul' η θ := by
    have he := vacuum_end_apply n Λ n₂ Λ₂ η (vacuumRegular n₂ Λ₂)
      (vacuumValue n Λ n₂ Λ₂ θ)
    change vacuumValue n Λ n₂ Λ₂ (η * θ) =
      vacuumValue n Λ n₂ Λ₂ η * vacuumValue n Λ n₂ Λ₂ θ at he
    change (vacuumRingEquiv n₂ Λ₂ (vacuumBlock n₂ Λ₂))
      (vacuumValue n Λ n₂ Λ₂ (η * θ)) = _
    rw [he, map_mul]
    rfl
  commutes' r := by
    change (vacuumRingEquiv n₂ Λ₂ (vacuumBlock n₂ Λ₂))
      ((algebraMap L (vacuumRing (L := L) n₂ Λ₂ (vacuumBlock n₂ Λ₂))
        ((vacuumRingEquiv n Λ (vacuumBlock n Λ)) (algebraMap L _ r))) * 1) = r
    rw [mul_one, AlgEquiv.commutes, AlgEquiv.commutes]
    rfl

theorem vacuumEv_injective : Function.Injective (vacuumEv n (L := L) Λ n₂ Λ₂) :=
  vacuumEval_injective n Λ n₂ Λ₂

instance vacuum_isReduced : IsReduced (End (vacuum n (L := L) Λ n₂ Λ₂)) :=
  isReduced_of_injective (vacuumEv n Λ n₂ Λ₂) (vacuumEv_injective n Λ n₂ Λ₂)

end Categorification.KLR.Unfurling
