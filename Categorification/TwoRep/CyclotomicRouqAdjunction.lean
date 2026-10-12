/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.AdditiveCat
import Categorification.TwoRep.CyclotomicLocalCommutator
import Categorification.TwoRep.RouqAdjunction

/-!
# Concrete interior cyclotomic opposite adjunction

The objects are the original `ModuleCat (CycKLR k Q a β)` and the 1-cells are the
original induction and idempotent restriction, bundled only with additivity.
`loc` transports the accepted `actualSumInvFrom` and `actualSumInvTo`, including
all five finite inverse identities, to `RouqLoc`. Its source weight is the negative
Kang–Kashiwara weight. The crossing remains the original `crossingNat` (minus psi).
The sigma, dotted unit, and dotted counit comparison lemmas identify the maps,
not just the source and target functors.

`oppositeAdjunction` applies Brundan's Theorem 4.3 to two adjacent actual inversions
and the accepted associated natural braid. Its unit and counit are precisely the
prescribed upper cup and lower cap. Both triangle identities hold for every
module at the displayed original algebras, without a pairing-perfectness or
opposite-adjunction hypothesis.

**Boundary:** this file proves the interior edge based at `{i} + β`, for arbitrary
`β` and all signs of the weight. It does not prove the edge based at a multiset
not containing `i`; that genuine boundary requires `absentEFEquiv`. No zero-category
replacement is made. A global cyclotomic CL action is not asserted here.
-/

noncomputable section
namespace Categorification.TwoRep.AdditiveCat
open CategoryTheory
universe v u
private def homAdd {C D : AdditiveCat.{v,u}} (F G : C ⟶ D) : (F ⟶ G) →+ (F.obj ⟶ G.obj) where
  toFun t := t.hom
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem hom_sum {C D : AdditiveCat.{v,u}} {F G : C ⟶ D}
    (n : ℕ) (t : ℕ → (F ⟶ G)) : (∑ m ∈ Finset.range n, t m).hom =
      ∑ m ∈ Finset.range n, (t m).hom := map_sum (homAdd F G) t (Finset.range n)

/-- Lift all five finite inverse equations, keeping the original natural transformations. -/
def sumInvTo {C D : AdditiveCat.{v,u}} {F G H : C ⟶ D}
    (f : F ⟶ G) (g : ℕ → (F ⟶ H)) (n : ℕ)
    (S : SumInvTo f.hom (fun m => (g m).hom) n) : SumInvTo f g n where
  f' := ObjectProperty.homMk S.f'
  g' m := ObjectProperty.homMk (S.g' m)
  total := by
    apply ObjectProperty.hom_ext
    change f.hom ≫ S.f' + (∑ m ∈ Finset.range n, g m ≫ ObjectProperty.homMk (S.g' m)).hom = 𝟙 _
    rw [hom_sum]
    exact S.total
  ff := ObjectProperty.hom_ext _ S.ff
  fg m hm := ObjectProperty.hom_ext _ (S.fg m hm)
  gf m hm := ObjectProperty.hom_ext _ (S.gf m hm)
  gg m m' hm hm' := by
    apply ObjectProperty.hom_ext
    have h := S.gg m m' hm hm'
    split_ifs at h ⊢ <;> exact h

/-- Lift the opposite finite inverse equations, without choosing new inverse components. -/
def sumInvFrom {C D : AdditiveCat.{v,u}} {F G H : C ⟶ D}
    (f : G ⟶ F) (g : ℕ → (H ⟶ F)) (n : ℕ)
    (S : SumInvFrom f.hom (fun m => (g m).hom) n) : SumInvFrom f g n where
  f' := ObjectProperty.homMk S.f'
  g' m := ObjectProperty.homMk (S.g' m)
  total := by
    apply ObjectProperty.hom_ext
    change S.f' ≫ f.hom + (∑ m ∈ Finset.range n, ObjectProperty.homMk (S.g' m) ≫ g m).hom = 𝟙 _
    rw [hom_sum]
    exact S.total
  ff := ObjectProperty.hom_ext _ S.ff
  fg m hm := ObjectProperty.hom_ext _ (S.fg m hm)
  gf m hm := ObjectProperty.hom_ext _ (S.gf m hm)
  gg m m' hm hm' := by
    apply ObjectProperty.hom_ext
    have h := S.gg m m' hm hm'
    split_ifs at h ⊢ <;> exact h
end Categorification.TwoRep.AdditiveCat

namespace Categorification.KLR.KLRAlgebra.AbsentColour
open CategoryTheory Categorification.TwoRep
open scoped ModuleCat.Algebra
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (a : I → Polynomial k) (β : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)

instance inductionFunctor_additive : (inductionFunctor.{u,v,w} Q i a β).Additive where
  map_add {N N'} f g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.extB
    intro z n
    exact BalancedTensor.tmul_add z (f n) (g n)

instance restrictionFunctor_additive : (restrictionFunctor.{u,v,w} Q i a β).Additive where
  map_add {N N'} f g := by ext x; rfl

namespace ConcreteAdjunction
open InductionCalculus
abbrev moduleCategory : AdditiveCat := AdditiveCat.of (ModuleCat.{max u v w} (CycKLR k Q a β))

def ind : moduleCategory.{u,v,w} Q a β ⟶ moduleCategory.{u,v,w} Q a (Si + β) :=
  @AdditiveFunctor.of _ _ _ _ _ _ (inductionFunctor.{u,v,w} Q i a β) (inductionFunctor_additive.{u,v,w} Q i a β)
def res : moduleCategory.{u,v,w} Q a (Si + β) ⟶ moduleCategory.{u,v,w} Q a β :=
  @AdditiveFunctor.of _ _ _ _ _ _ (restrictionFunctor.{u,v,w} Q i a β) (restrictionFunctor_additive.{u,v,w} Q i a β)
def adj : CategoryTheory.Bicategory.Adjunction (ind.{u,v,w} Q i a β) (res Q i a β) :=
  AdditiveCat.ofAdjunction (cyclotomicAdjunction.{u,v,w} Q i a β)
def dot : ind.{u,v,w} Q i a β ⟶ ind Q i a β := ObjectProperty.homMk (dotNat.{u,v,w} Q i a β)
def crossing : ind.{u,v,w} Q i a β ≫ ind Q i a (Si + β) ⟶
    ind Q i a β ≫ ind Q i a (Si + β) := ObjectProperty.homMk (crossingNat.{u,v,w} Q i a β)

open CategoryTheory.Bicategory

@[simp] theorem dot_pow_hom (n : ℕ) :
    (powComp (dot.{u,v,w} Q i a β) n).hom = powComp (dotNat Q i a β) n := by
  induction n with
  | zero => rfl
  | succ n hn => change (powComp (dot Q i a β) n).hom ≫ dotNat Q i a β = _; rw [hn]; rfl

theorem sigma_hom :
    (RightwardCrossing.sigma (E₁ := ind.{u,v,w} Q i a β) (R₁ := res.{u,v,w} Q i a β)
      (E₂ := ind.{u,v,w} Q i a (Si + β)) (R₂ := res.{u,v,w} Q i a (Si + β))
      (adj.{u,v,w} Q i a (Si + β)).unit
      (crossing Q i a β) (adj Q i a β).counit).hom = mixedMateNat Q i a β := by
  exact AdditiveCat.sigma_hom _ _ _

theorem cap_hom (n : ℕ) :
    (res.{u,v,w} Q i a β ◁ powComp (dot Q i a β) n ≫ (adj Q i a β).counit).hom =
      dottedCounit Q i a β n := by
  change Functor.whiskerLeft (restrictionFunctor Q i a β) (powComp (dot Q i a β) n).hom ≫
    (cyclotomicAdjunction Q i a β).counit = _
  rw [dot_pow_hom]
  rfl

theorem cup_hom (n : ℕ) :
    ((adj.{u,v,w} Q i a β).unit ≫ powComp (dot Q i a β) n ▷ res Q i a β).hom =
      dottedUnit Q i a β n := by
  change (cyclotomicAdjunction Q i a β).unit ≫
    Functor.whiskerRight (powComp (dot Q i a β) n).hom (restrictionFunctor Q i a β) = _
  rw [dot_pow_hom]
  rfl

theorem crossing_square : crossing.{u,v,w} Q i a β ≫ crossing Q i a β = 0 :=
  ObjectProperty.hom_ext _ (crossingNat_square Q i a β)

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ j l, j ≠ l → Q j l = P l j * MvPolynomial.rename ![1, 0] (P j l))
  (hP : ∀ j l, j ≠ l → P j l ≠ 0)
  (hQ : ∀ j l : I, j ≠ l → IsUnit (polyInY (Q j l)).leadingCoeff)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.RootDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) =
    -RD.pair (RD.iY i) (RD.iX j))
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX ((Singleton.singleton i : Multiset I) + β)))

/-- Actual local Rouquier data at the original algebra with one displayed terminal colour.
The Brundan source weight is the negative Kang–Kashiwara weight. -/
def loc : RouqLoc (E₁ := ind.{u,v,w} Q i a β) (R₁ := res.{u,v,w} Q i a β)
    (E₂ := ind.{u,v,w} Q i a (Si + β)) (R₂ := res.{u,v,w} Q i a (Si + β))
    (adj Q i a β) (adj Q i a (Si + β)) (dot Q i a β) (dot Q i a (Si + β))
    (crossing Q i a β) (-wt) where
  slide_left := by
    apply ObjectProperty.hom_ext
    exact sub_eq_iff_eq_add'.mpr (crossingNat_slide' Q i a β)
  slide_right := by
    apply ObjectProperty.hom_ext
    exact sub_eq_iff_eq_add'.mpr (crossingNat_slide Q i a β)
  invPos hh := by
    apply AdditiveCat.sumInvTo
    simp only [sigma_hom, cap_hom]
    exact actualSumInvTo Q i a β hPQ hP hQ ha RD Λ hΛ hdeg
      (neg_nonneg.mp hh)
  invNeg hh := by
    apply AdditiveCat.sumInvFrom
    simp only [sigma_hom, cup_hom, neg_neg]
    exact actualSumInvFrom Q i a β hPQ hP hQ ha RD Λ hΛ hdeg
      (neg_nonpos.mp hh)

omit [DecidableEq I] in
theorem adjacent_source_weight :
    -(RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX (Si + (Si + β))))) = -wt + 2 := by
  simp only [Multiset.map_add, Multiset.map_singleton, Multiset.sum_add,
    Multiset.sum_singleton, map_sub, map_add]
  have h := RD.pair_iY_iX_self i
  omega

/-- The opposite adjunction on the original interior induction/restriction functors.
Both prescribed maps come from the adjacent concrete Rouquier inverses. -/
def oppositeAdjunction : restrictionFunctor.{u,v,w} Q i a (Si + β) ⊣
    inductionFunctor.{u,v,w} Q i a (Si + β) :=
  AdditiveCat.toAdjunction
    ((loc.{u,v,w} Q i a β hPQ hP hQ ha RD Λ hΛ hdeg).leftAdjunction
      (loc.{u,v,w} Q i a (Si + β) hPQ hP hQ ha RD Λ hΛ hdeg)
      (adjacent_source_weight i β RD Λ) (crossing_square Q i a β)
      (crossing_square Q i a (Si + β))
      (AdditiveCat.braid_of _ _ _ _ _ (crossingNat_braid.{u,v,w} Q i a β)))

/-- The unit is exactly Brundan's prescribed cup from the upper concrete inversion. -/
theorem oppositeAdjunction_unit :
    (oppositeAdjunction.{u,v,w} Q i a β hPQ hP hQ ha RD Λ hΛ hdeg).unit =
      (loc.{u,v,w} Q i a (Si + β) hPQ hP hQ ha RD Λ hΛ hdeg).cupL.hom := rfl

/-- The counit is exactly Brundan's prescribed cap from the lower concrete inversion. -/
theorem oppositeAdjunction_counit :
    (oppositeAdjunction.{u,v,w} Q i a β hPQ hP hQ ha RD Λ hΛ hdeg).counit =
      (loc.{u,v,w} Q i a β hPQ hP hQ ha RD Λ hΛ hdeg).capL.hom := rfl

/-- The restriction triangle holds on every original cyclotomic module. -/
theorem restriction_triangle (M : ModuleCat.{max u v w} (CycKLR k Q a (Si + (Si + β)))) :
    (restrictionFunctor.{u,v,w} Q i a (Si + β)).map
        ((loc.{u,v,w} Q i a (Si + β) hPQ hP hQ ha RD Λ hΛ hdeg).cupL.hom.app M) ≫
      (loc.{u,v,w} Q i a β hPQ hP hQ ha RD Λ hΛ hdeg).capL.hom.app
        ((restrictionFunctor.{u,v,w} Q i a (Si + β)).obj M) =
      𝟙 ((restrictionFunctor.{u,v,w} Q i a (Si + β)).obj M) :=
  (oppositeAdjunction.{u,v,w} Q i a β hPQ hP hQ ha RD Λ hΛ hdeg).left_triangle_components M

/-- The induction triangle holds on every original cyclotomic module. -/
theorem induction_triangle (N : ModuleCat.{max u v w} (CycKLR k Q a (Si + β))) :
    (loc.{u,v,w} Q i a (Si + β) hPQ hP hQ ha RD Λ hΛ hdeg).cupL.hom.app
        ((inductionFunctor.{u,v,w} Q i a (Si + β)).obj N) ≫
      (inductionFunctor.{u,v,w} Q i a (Si + β)).map
        ((loc.{u,v,w} Q i a β hPQ hP hQ ha RD Λ hΛ hdeg).capL.hom.app N) =
      𝟙 ((inductionFunctor.{u,v,w} Q i a (Si + β)).obj N) :=
  (oppositeAdjunction.{u,v,w} Q i a β hPQ hP hQ ha RD Λ hΛ hdeg).right_triangle_components N

end ConcreteAdjunction
end Categorification.KLR.KLRAlgebra.AbsentColour
