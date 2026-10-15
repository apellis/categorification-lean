/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CyclotomicRouqAdjunction
import Categorification.TwoRep.RouqBoundaryAdjunction

/-!
# Genuine absent-colour cyclotomic opposite adjunction

For arbitrary `i ∉ β`, `absent_oppositeAdjunction` proves restriction left adjoint
to induction on the original cyclotomic module categories. `coefficient` is the
actual inverse of `absentEFEquiv`, and `equiv_single` identifies its forward basis
with the original dotted ordinary unit, including the `e x_last^d e` dot order.

The counit is the highest inverse coefficient with positive sign (zero in degree
zero). The unit is exactly the prescribed upper cup from `ConcreteAdjunction.loc`
at `β`; the upper source weight is `2 - ⟨hᵢ, Λ-β⟩`. Both triangles hold on every
original module, and both maps are natural. The lower multiset may be nonempty,
and no quotient nontriviality, homogeneity, projectivity, pairing-perfectness,
opposite-adjunction premise, or synthetic lower edge is assumed.

The hypotheses are those of the inversion: `KLRSymm Q` over a commutative ring `k`,
unit constant leading coefficients of the `Q_{jl}`, monic `a_j` and the Cartan-degree
condition. This result is ungraded; a global
weight-indexed action and distinct-colour compatibility are separate statements.
-/
noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.BoundaryAdjunction
open CategoryTheory Categorification.TwoRep
open scoped ModuleCat.Algebra
open InductionCalculus ConcreteAdjunction
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (a : I → Polynomial k) (β : Multiset I)
  (hsym : KLRSymm Q)
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.RootDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) =
    -RD.pair (RD.iY i) (RD.iX j)) (hi : i ∉ β)
local notation "R" => CycKLR k Q a β
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX β))
local notation "iso" => absentEFEquiv Q i a β
local notation "EFF" => inductionFunctor Q i a β ⋙ restrictionFunctor Q i a β

/-- Every finite basis vector is the original dotted unit, including its dot order. -/
theorem equiv_single (N : ModuleCat.{max u v w} R) (d : Fin (wt).toNat) (n : N) :
    iso N hsym hQ ha RD Λ hΛ hdeg hi (Pi.single d n) = (dottedUnit Q i a β d).app N n := by
  apply Subtype.ext
  rw [absentEFEquiv_single, dottedUnit_val]
  congr 1
  apply Subtype.ext
  change (lastIdem Q i a β * dotElement Q i a β ^ (d : ℕ)) * lastIdem Q i a β =
    lastIdem Q i a β * dotElement Q i a β ^ (d : ℕ)
  have hc : dotElement Q i a β ^ (d : ℕ) * lastIdem Q i a β =
      lastIdem Q i a β * dotElement Q i a β ^ (d : ℕ) :=
    ((dot_commute Q i a β 1).pow_left (d : ℕ)).eq
  rw [mul_assoc, hc,
    ← mul_assoc, lastIdem_mul]

/-- The actual inverse coefficient, natural on all original modules and zero out of range. -/
def coefficient (d : ℕ) : EFF ⟶ 𝟭 (ModuleCat.{max u v w} R) := by
  classical
  exact if hd : d < (wt).toNat then
    { app := fun N => ModuleCat.ofHom ((LinearMap.proj (⟨d, hd⟩ : Fin (wt).toNat)).comp
        (iso N hsym hQ ha RD Λ hΛ hdeg hi).symm.toLinearMap)
      naturality := fun N N' f => by
        ext z
        exact congrFun
          (absentEFEquiv_symm_natural Q i a β N hsym hQ ha RD Λ hΛ hdeg hi f.hom z)
          ⟨d, hd⟩ }
  else 0
local notation "coef" => coefficient Q i a β hsym hQ ha RD Λ hΛ hdeg hi

theorem coefficient_app (d : ℕ) (hd : d < (wt).toNat)
    (N : ModuleCat.{max u v w} R) (z : (EFF).obj N) :
    (coef d).app N z = (iso N hsym hQ ha RD Λ hΛ hdeg hi).symm z ⟨d, hd⟩ := by
  simp only [coefficient, dite_eq_left hd]
  rfl

theorem equiv_apply (N : ModuleCat.{max u v w} R) (v : Fin (wt).toNat → N) :
    iso N hsym hQ ha RD Λ hΛ hdeg hi v =
      ∑ d : Fin (wt).toNat, (dottedUnit Q i a β d).app N (v d) := by
  classical
  have hv : v = ∑ d : Fin (wt).toNat, Pi.single d (v d) := by ext j; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun d _ =>
    equiv_single Q i a β hsym hQ ha RD Λ hΛ hdeg hi N d (v d))

theorem coefficient_total :
    (∑ d ∈ Finset.range (wt).toNat, coef d ≫ dottedUnit.{u,v,w} Q i a β d) = 𝟙 _ := by
  ext N : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp only [NatTrans.comp_app, NatTrans.app_sum, ModuleCat.hom_sum,
    LinearMap.sum_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [coefficient_app _ _ _ _ _ _ _ _ _ _ _ _ _ (Fin.isLt _)]
  exact (equiv_apply Q i a β hsym hQ ha RD Λ hΛ hdeg hi N
    ((iso N hsym hQ ha RD Λ hΛ hdeg hi).symm z)).symm.trans
      ((iso N hsym hQ ha RD Λ hΛ hdeg hi).apply_symm_apply z)

theorem coefficient_entry (d e : ℕ) (hd : d < (wt).toNat) (he : e < (wt).toNat) :
    dottedUnit.{u,v,w} Q i a β d ≫ coef e = if d = e then 𝟙 _ else 0 := by
  classical
  ext N : 2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change N at m
  have h := (iso N hsym hQ ha RD Λ hΛ hdeg hi).symm_apply_apply
    (Pi.single (⟨d, hd⟩ : Fin (wt).toNat) m)
  rw [equiv_single.{u,v,w}] at h
  have hh := congrFun h ⟨e, he⟩
  change (coef e).app N ((dottedUnit Q i a β d).app N m) = _
  rw [coefficient_app _ _ _ _ _ _ _ _ _ _ _ _ _ he, hh]
  by_cases hde : d = e
  · subst e
    rw [ite_eq_left rfl]
    change (Pi.single (⟨d, hd⟩ : Fin (wt).toNat) m : Fin (wt).toNat → N) ⟨d, he⟩ = m
    rw [Pi.single_eq_same]
  · rw [ite_eq_right hde]
    change (Pi.single (⟨d, hd⟩ : Fin (wt).toNat) m : Fin (wt).toNat → N) ⟨e, he⟩ = 0
    exact Pi.single_eq_of_ne (M := fun _ : Fin (wt).toNat => N)
      (fun h => hde (congrArg Fin.val h).symm) m

open CategoryTheory.Bicategory

private def homAdd {A B : AdditiveCat} (F G : A ⟶ B) : (F ⟶ G) →+ (F.obj ⟶ G.obj) where
  toFun t := t.hom
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem hom_sum {A B : AdditiveCat} {F G : A ⟶ B}
    (n : ℕ) (t : ℕ → (F ⟶ G)) : (∑ m ∈ Finset.range n, t m).hom =
      ∑ m ∈ Finset.range n, (t m).hom := map_sum (homAdd F G) t (Finset.range n)

/-- The original inverse coefficients supply the finite boundary data. -/
def coefficients : RouqBoundary.Coefficients (adj.{u,v,w} Q i a β) (dot Q i a β)
    (wt).toNat where
  coeff d := ObjectProperty.homMk (coef d)
  total := by
    apply ObjectProperty.hom_ext
    rw [hom_sum]
    have hc (m : ℕ) :
        ((show ind.{u,v,w} Q i a β ≫ res Q i a β ⟶ 𝟙 (moduleCategory Q a β) from
            ObjectProperty.homMk (coef m)) ≫
          RouqBoundary.cupD (adj.{u,v,w} Q i a β) (dot Q i a β) m).hom =
          (coef m ≫ dottedUnit.{u,v,w} Q i a β m) := by
      change coef m ≫ (RouqBoundary.cupD (adj Q i a β) (dot Q i a β) m).hom = _
      rw [RouqBoundary.cupD, cup_hom]
      rfl
    simp only [hc]
    exact coefficient_total.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hi
  entry d e hd he := by
    apply ObjectProperty.hom_ext
    have hh := coefficient_entry.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hi d e hd he
    change (RouqBoundary.cupD (adj Q i a β) (dot Q i a β) d).hom ≫ coef e = _
    rw [RouqBoundary.cupD, cup_hom]
    split_ifs at hh ⊢ <;> exact hh

/-- The cap is the highest actual inverse coefficient, with degree zero retained. -/
def cap : EFF ⟶ 𝟭 (ModuleCat.{max u v w} R) :=
  if 0 < (wt).toNat then coef ((wt).toNat-1) else 0

omit [DecidableEq I] in
include hi hΛ hdeg in
/-- The source weight of the upper loc is exactly two minus the boundary degree. -/
theorem upper_weight :
    -(RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX ({i} + β)))) =
      2 - ((wt).toNat : ℤ) := by
  classical
  have hn := weight_nonneg_of_absent Q i a β RD Λ hi hΛ hdeg
  rw [Int.toNat_of_nonneg hn]
  simp only [Multiset.map_add, Multiset.map_singleton, Multiset.sum_add,
    Multiset.sum_singleton, map_sub, map_add, RD.pair_iY_iX_self]
  omega

/-- Genuine absent-colour opposite adjunction, on the original functors. -/
def absent_oppositeAdjunction : restrictionFunctor.{u,v,w} Q i a β ⊣ inductionFunctor Q i a β :=
  AdditiveCat.toAdjunction (RouqBoundary.oppositeAdjunction
    (coefficients.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hi)
    (loc.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg)
    (upper_weight Q i a β RD Λ hΛ hdeg hi) (crossing_square Q i a β))

/-- The unit is the prescribed upper cup, with no alternative Frobenius unit chosen. -/
theorem absent_oppositeAdjunction_unit :
    (absent_oppositeAdjunction.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hi).unit =
      (loc.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg).cupL.hom := rfl

/-- The counit is precisely the actual highest inverse coefficient. -/
theorem absent_oppositeAdjunction_counit :
    (absent_oppositeAdjunction.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hi).counit =
      cap.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hi := by
  change (RouqBoundary.cap
    (coefficients.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hi)).hom = _
  unfold RouqBoundary.cap cap
  split_ifs <;> rfl

/-- The cap extracts degree `n-1` with positive sign when the boundary degree is positive. -/
theorem cap_app (hn : 0 < (wt).toNat) (N : ModuleCat.{max u v w} R) (z : (EFF).obj N) :
    (cap Q i a β hsym hQ ha RD Λ hΛ hdeg hi).app N z =
      (iso N hsym hQ ha RD Λ hΛ hdeg hi).symm z ⟨(wt).toNat-1, by omega⟩ := by
  rw [cap, ite_eq_left hn, coefficient_app _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]

/-- Degree zero is not discarded or assumed nonzero. -/
theorem cap_degree_zero (hn : (wt).toNat = 0) :
    cap.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hi = 0 := by
  rw [cap, ite_eq_right (by omega)]

/-- Naturality of the cap for every linear map of original modules. -/
theorem cap_naturality {N N' : ModuleCat.{max u v w} R} (f : N ⟶ N') :
    (EFF).map f ≫ (cap Q i a β hsym hQ ha RD Λ hΛ hdeg hi).app N' =
      (cap Q i a β hsym hQ ha RD Λ hΛ hdeg hi).app N ≫ f :=
  (cap Q i a β hsym hQ ha RD Λ hΛ hdeg hi).naturality f

/-- The restriction triangle holds on all original modules at the upper block. -/
theorem restriction_triangle
    (M : ModuleCat.{max u v w} (CycKLR k Q a ((Singleton.singleton i : Multiset I) + β))) :
    (restrictionFunctor.{u,v,w} Q i a β).map
        ((loc.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg).cupL.hom.app M) ≫
      (cap.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hi).app
        ((restrictionFunctor.{u,v,w} Q i a β).obj M) =
      𝟙 ((restrictionFunctor.{u,v,w} Q i a β).obj M) := by
  let A := absent_oppositeAdjunction.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hi
  have h := A.left_triangle_components M
  dsimp only [A] at h
  rw [absent_oppositeAdjunction_unit, absent_oppositeAdjunction_counit] at h
  exact h

/-- The induction triangle holds on all original modules at an arbitrary absent-colour block. -/
theorem induction_triangle (N : ModuleCat.{max u v w} R) :
    (loc.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg).cupL.hom.app
        ((inductionFunctor.{u,v,w} Q i a β).obj N) ≫
      (inductionFunctor.{u,v,w} Q i a β).map
        ((cap.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hi).app N) =
      𝟙 ((inductionFunctor.{u,v,w} Q i a β).obj N) := by
  let A := absent_oppositeAdjunction.{u,v,w} Q i a β hsym hQ ha RD Λ hΛ hdeg hi
  have h := A.right_triangle_components N
  dsimp only [A] at h
  rw [absent_oppositeAdjunction_unit, absent_oppositeAdjunction_counit] at h
  exact h

end Categorification.KLR.KLRAlgebra.AbsentColour.BoundaryAdjunction
