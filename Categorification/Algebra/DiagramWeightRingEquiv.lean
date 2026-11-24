/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramBigrading
import DG.Bigraded.DegreeZero
import DG.Category.Resolution.KProjective

/-!
# Weight modules under a homogeneous ring equivalence

For Webster, arXiv:1309.3796v2, Lemma 6.5 and Proposition 7.11, restriction
along the equivalence of the diagonal diagram algebras identifies their
weight categories and the projective modules cut out by loading idempotents.
-/
noncomputable section
namespace Categorification

section WeightFunctor
open CategoryTheory DG CatModule DGCategory
open scoped DG.DegreeZero

private def placedRingHom {A B : Type*} [Ring A] [Ring B] (f : A →+* B) : A →ᵈᵍ+* B where
  toRingHom := f
  map_mem' {n a} ha := by
    apply (InDegreeZero.ring_mem_grading_iff (R := B)).mpr
    rcases (InDegreeZero.ring_mem_grading_iff (R := A)).mp ha with h | h
    · exact Or.inl h
    · exact Or.inr (h ▸ f.map_zero)
  map_d' a := by
    rw [InDegreeZero.ring_d_apply, InDegreeZero.ring_d_apply]
    exact f.map_zero

universe u
variable {A B : Type u} [Ring A] [Ring B] [InternalGrading A] [InternalGrading B]
  [BigradedDGRing A] [BigradedDGRing B] (e : A ≃+* B)
  (he : ∀ {j : ℤ} (a : A), e a ∈ wgrading j ↔ a ∈ wgrading j)

/-- The weight dg functor associated to a componentwise equivalence of
rings placed in cohomological degree zero. -/
def weightFunctorOfRingEquiv : WeightCategory A ⥤ WeightCategory B :=
  WeightCategory.mapFunctor (placedRingHom e.toRingHom) (fun {_j a} h => (he a).mpr h)

instance weightFunctorOfRingEquiv_additive : (weightFunctorOfRingEquiv e he).Additive where
  map_add := WeightCategory.hom_ext (e.map_add _ _)

instance weightFunctorOfRingEquiv_isDGFunctor : (weightFunctorOfRingEquiv e he).IsDGFunctor where
  map_mem' hf := (placedRingHom e.toRingHom).map_mem hf
  map_d' f := WeightCategory.hom_ext ((placedRingHom e.toRingHom).map_d f.val)

instance weightFunctorOfRingEquiv_isEquivalence : (weightFunctorOfRingEquiv e he).IsEquivalence where
  faithful := ⟨fun {X Y f g} h => WeightCategory.hom_ext (e.injective (congrArg Subtype.val h))⟩
  full := ⟨fun {X Y} f => by
    refine ⟨⟨e.symm f.val,(he _).mp ?_⟩,WeightCategory.hom_ext (e.apply_symm_apply f.val)⟩
    rw [e.apply_symm_apply]
    exact f.property⟩
  essSurj := ⟨fun X => ⟨⟨X.as⟩,⟨Iso.refl _⟩⟩⟩

local notation "F" => weightFunctorOfRingEquiv e he

/-- Restriction along a homogeneous ring equivalence identifies the projective
weight modules whenever their defining diagram idempotents correspond. -/
def weightRingEquivCornerIso (X : WeightCategory A) (p : Idempotent X)
    (q : Idempotent ((F).obj X)) (hp : (F).map p.val = q.val) :
    corner p ≅ (precomp F).obj (corner q) := by
  refine isoMk (fun Y => ?_) ?_ ?_ ?_
  · exact {
      toFun := fun x => ⟨(F).map x.val, by
        change q.val ≫ (F).map x.val = (F).map x.val
        exact (congrArg (· ≫ (F).map x.val) hp.symm).trans
          (((F).map_comp _ _).symm.trans (congrArg (F).map x.property))⟩
      invFun := fun y => ⟨(F).preimage y.val, (F).map_injective (by
        have h : (F).map ((F).preimage y.val) = y.val := (F).map_preimage _
        exact ((F).map_comp _ _).trans
          ((congrArg₂ (fun (i : (F).obj X ⟶ (F).obj X) (a : (F).obj X ⟶ (F).obj Y) =>
            i ≫ a) hp h).trans (y.property.trans h.symm)))⟩
      left_inv := fun x => Subtype.ext ((F).preimage_map _)
      right_inv := fun y => Subtype.ext ((F).map_preimage _)
      map_add' := fun _ _ => Subtype.ext (F).map_add }
  · intro Y n x
    change e x.val.val ∈ grading n ↔ x.val.val ∈ grading n
    rw [InDegreeZero.ring_mem_grading_iff,InDegreeZero.ring_mem_grading_iff,e.map_eq_zero_iff]
  · intro Y x
    exact Subtype.ext ((F).map_d _)
  · intro X Y f x
    exact Subtype.ext ((F).map_comp _ _)

end WeightFunctor

end Categorification
