/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.OrderedWeightDGFilteredVanishing
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleWeightTriangles

/-!
# The higher-supported graded resolution at the label-two middle cut

The ordered graded model augments to the actual middle standard as a
weight module. All strictly higher loading idempotents annihilate the
reflected dot-sum coefficient. Thus the derived tensor of the middle
standard is acyclic away from degree zero, as required for the two
companion triangles of Webster §8.2.
-/

noncomputable section

namespace Categorification.Stendhal.LabelTwo

open KLR CategoryTheory CategoryTheory.Limits Categorification.Graded DG
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "ν₂" => (({()} : Multiset Unit) + {()})
local notation "A₂" => TensorProductAlgebra k (parameter k) weights ν₂
local notation "𝒜₂" => middleTensorGrade k (labelTwoGradingDatum k)
local notation "ℳ₂" => middleStandardGrade k (labelTwoGradingDatum k)
local notation "S₂" => Standard k

local instance : InternalGrading A₂ := gradedAlgebraInternalGrading 𝒜₂
local instance : BigradedDGRing A₂ := gradedAlgebraBigradedDGRing 𝒜₂
local instance : InternalGrading k := scalarInternalGrading k
local instance : BigradedDGRing k := scalarBigradedDGRing k

local notation "W₂" => WeightCategory A₂

/-- The actual middle standard with its parabolic grading as a single chain term. -/
def middleGradedChainTerm : WeightGradedTerm A₂ where
  obj := ModuleCat.of A₂ S₂
  grade := fun i => (ℳ₂ i).toAddSubgroup
  decomp := by
    let d := (middleStandardGFin k (labelTwoGradingDatum k)).decomposition
    exact ⟨d.decompose', d.left_inv, d.right_inv⟩
  smul_mem ha hx := (middleStandardGFin k (labelTwoGradingDatum k)).gradedSMul.smul_mem ha hx

private abbrev middleStalkValue (X : W₂) := ModuleCat.of ℤ ((middleGradedChainTerm k).grade X.as)

private abbrev middleStalkChain (X : W₂) :=
  (ChainComplex.single₀ (ModuleCat ℤ)).obj (middleStalkValue k X)

private abbrev middleStalkCochain (X : W₂) :=
  (middleStalkChain k X).extend ComplexShape.embeddingDownNat

private def middleStalkZeroIso (X : W₂) : (middleStalkCochain k X).X 0 ≅ middleStalkValue k X :=
  (middleStalkChain k X).extendXIso ComplexShape.embeddingDownNat (i := 0) (i' := 0) rfl

private theorem middleStalk_off_zero (X : W₂) {n : ℤ} (hn : n ≠ 0) :
    IsZero ((middleStalkCochain k X).X n) := by
  by_cases h : ∃ m : ℕ, ComplexShape.embeddingDownNat.f m = n
  · obtain ⟨m, hm⟩ := h
    have hm₀ : m ≠ 0 := by
      intro h
      subst m
      exact hn hm.symm
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ)
      0 (middleStalkValue k X) m hm₀).of_iso
        ((middleStalkChain k X).extendXIso ComplexShape.embeddingDownNat hm)
  · exact HomologicalComplex.isZero_extend_X (middleStalkChain k X) _ n (fun m hm => h ⟨m, hm⟩)

private theorem middleStalk_d_zero (X : W₂) (n m : ℤ) :
    (middleStalkCochain k X).d n m = 0 :=
  HomologicalComplex.extend_single_d ComplexShape.embeddingDownNat (middleStalkValue k X) 0 n m

private def middleStalkAddEquiv (X : W₂) :
    ComplexSum (middleStalkCochain k X) ≃+ middleStalkValue k X where
  toFun x := (middleStalkZeroIso k X).hom (ComplexSum.component (middleStalkCochain k X) 0 x)
  invFun z := ComplexSum.of (middleStalkCochain k X) 0 ((middleStalkZeroIso k X).inv z)
  left_inv x := by
    dsimp only
    induction x using ComplexSum.induction_on with
    | zero => simp only [map_zero]
    | of n x =>
      by_cases h : n = 0
      · subst n
        rw [ComplexSum.component_of_same, Iso.hom_inv_id_apply]
      · have hx : x = 0 := (ModuleCat.isZero_iff_subsingleton.mp (middleStalk_off_zero k X h)).elim _ _
        simp only [hx, map_zero]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  right_inv z := by dsimp only; rw [ComplexSum.component_of_same, Iso.inv_hom_id_apply]
  map_add' x y := by simp only [map_add]

private def middleStalkAction {X Y : W₂} (a : X ⟶ Y) :
    middleStalkValue k X ⟶ middleStalkValue k Y :=
  ModuleCat.ofHom (({
    toFun := fun x => ⟨a.val • x.val, by
      have h := (middleGradedChainTerm k).smul_mem a.property x.property
      rwa [sub_add_cancel] at h⟩
    map_zero' := Subtype.ext (smul_zero _)
    map_add' x y := Subtype.ext (smul_add _ _ _) } :
      ((middleGradedChainTerm k).grade X.as) →+ ((middleGradedChainTerm k).grade Y.as)).toIntLinearMap)

private theorem middleStalk_component_map {K L : CochainComplex (ModuleCat ℤ) ℤ}
    (f : K ⟶ L) (j : ℤ) (x : ComplexSum K) :
    ComplexSum.component L j (ComplexSum.map f x) = f.f j (ComplexSum.component K j x) := by
  induction x using ComplexSum.induction_on with
  | zero => simp
  | of i x =>
    by_cases hij : i = j
    · subst j
      rw [ComplexSum.map_of, ComplexSum.component_of_same, ComplexSum.component_of_same]
    · rw [ComplexSum.map_of, ComplexSum.component_of_ne hij, ComplexSum.component_of_ne hij, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem middleStalk_coordinate_act {X Y : W₂} (a : X ⟶ Y)
    (z : (middleStalkCochain k X).X 0) :
    let f := HomologicalComplex.extendMap ((ChainComplex.single₀ _).map
      (middleStalkAction k a)) ComplexShape.embeddingDownNat
    (middleStalkZeroIso k Y).hom (f.f 0 z) =
      middleStalkAction k a ((middleStalkZeroIso k X).hom z) := by
  dsimp only
  rw [HomologicalComplex.extendMap_f _ _ (i := (0 : ℕ)) (i' := (0 : ℤ)) rfl,
    ChainComplex.single₀_map_f_zero]
  change (middleStalkZeroIso k Y).hom ((middleStalkZeroIso k Y).inv
    (middleStalkAction k a ((middleStalkZeroIso k X).hom z))) = _
  exact Iso.inv_hom_id_apply _ _

set_option backward.isDefEq.respectTransparency false in
/-- The middle standard's explicit stalk realization agrees with its
degree-zero diagram weight module. -/
def middleWeightStalkIso :
    weightDgModuleOfGradedTerm (middleGradedChainTerm k) ≅ middleStandardWeightModule k := by
  let c (X : W₂) : (middleStalkValue k X) ≃+ InDegreeZero ((ℳ₂ (X.as - 0)).toAddSubgroup) :=
    AddEquiv.addSubgroupCongr (congrArg (fun d => (ℳ₂ d).toAddSubgroup) (sub_zero X.as).symm)
  let e (X : W₂) := (middleStalkAddEquiv k X).trans (c X)
  refine CatModule.isoMk (fun X => e X) ?_ ?_ ?_
  · intro X n x
    symm
    change x ∈ DG.grading (M := ComplexSum (middleStalkCochain k X)) n ↔
      e X x ∈ DG.grading (M := InDegreeZero ((ℳ₂ (X.as - 0)).toAddSubgroup)) n
    rw [InDegreeZero.mem_grading_iff]
    by_cases h : n = 0
    · subst n
      refine ⟨fun _ => Or.inl rfl, fun _ => ?_⟩
      exact ComplexSum.mem_grading_iff.mpr ⟨_, (middleStalkAddEquiv k X).symm_apply_apply x⟩
    · rw [or_iff_right h]
      constructor
      · intro hx
        obtain ⟨z, rfl⟩ := ComplexSum.mem_grading_iff.mp hx
        have hz : z = 0 :=
          (ModuleCat.isZero_iff_subsingleton.mp (middleStalk_off_zero k X h)).elim _ _
        rw [hz, map_zero, map_zero]
      · intro hx
        have hx' : x = 0 := (e X).injective (hx.trans (map_zero (e X)).symm)
        rw [hx']
        exact zero_mem _
  · intro X x
    let x' : ComplexSum (middleStalkCochain k X) := x
    change e X (d x') = 0
    have h : ComplexSum.of (middleStalkCochain k X) 0
        ((middleStalkZeroIso k X).inv (middleStalkAddEquiv k X x')) = x' :=
      (middleStalkAddEquiv k X).symm_apply_apply x'
    have hz : d x' = 0 := by
      rw [← h, ComplexSum.d_of, middleStalk_d_zero]
      change ComplexSum.of _ _ 0 = 0
      exact map_zero _
    rw [hz, map_zero]
  · intro X Y a x
    apply Subtype.ext
    let K := middleStalkCochain k X
    let L := middleStalkCochain k Y
    let f : K ⟶ L := HomologicalComplex.extendMap ((ChainComplex.single₀ _).map
      (middleStalkAction k a)) ComplexShape.embeddingDownNat
    change ((middleStalkZeroIso k Y).hom
      (ComplexSum.component L 0 (ComplexSum.map f (x : ComplexSum K)))).val =
      a.val • ((middleStalkZeroIso k X).hom (ComplexSum.component K 0 x)).val
    rw [middleStalk_component_map]
    exact congrArg Subtype.val (middleStalk_coordinate_act k a (ComplexSum.component K 0 x))


universe v
section HigherSupport

open Categorification.ModuleFiltration MulOpposite

local notation "I₂" => {s : KLR.Seq (stendhalWeight 2 ν₂) // IsRedOrdered s}
set_option quotPrecheck false in
local notation "s₂" => (⟨loading, loading_ordered⟩ : I₂)
set_option quotPrecheck false in
local notation "idems₂" => fun t : I₂ => seqIdem (parameter k) weights t.1 t.2
set_option quotPrecheck false in
local notation "standards₂" => fun t : I₂ => ModuleCat.of A₂ (leftStandard (parameter k) weights t.1 t.2)

variable [CatModule.HasDerivedCategory.{v,0} (WeightCategory
  (TensorProductAlgebra k (parameter k) weights (({()} : Multiset Unit) + {()})))]
  [CatModule.HasDerivedCategory.{v,0} (WeightCategory k)]

/-- Higher-loading ordered covers for the actual middle standard make the
fixed-weight derived tensor cohomology vanish away from degree zero. -/
theorem middleStandardWeight_cohomology_isZero_of_ordered_covers
    (D : OrderedStandardCovers standards₂ idems₂ (fun s t => StendhalLT s.1 t.1))
    (hD : ∀ x : lIdeal (idems₂ s₂), D.quotient s₂ x = (Submodule.Quotient.mk x : S₂))
    (X : WeightCategory k) (n : ℤ) (hn : n ≠ 0) :
    Limits.IsZero ((CatModule.DerivedCategory.cohomologyFunctor X n).obj
      ((middleReflectedWeightDerivedTensor k).obj
        (CatModule.DerivedCategory.Q.obj (middleStandardWeightModule k)))) := by
  let T : ℤ → AddSubgroup (standards₂ s₂) := (middleGradedChainTerm k).grade
  have he₀ (i : I₂) : idems₂ i ∈ wgrading (M := A₂) 0 :=
    mk_e_mem_tensorProductGrade (labelTwoGradingDatum k) ν₂ i.1 i.2
  have he (i : I₂) : IsIdempotentElem (idems₂ i) :=
    seqIdem_mul_self (parameter k) weights i.1 i.2
  have htrans (a b c : I₂) (hab : StendhalLT a.1 b.1) (hbc : StendhalLT b.1 c.1) :
      StendhalLT a.1 c.1 := by
    exact ⟨fun r i => (hab.1 r i).trans (hbc.1 r i),
      fun hca => hab.2 (fun r i => (hbc.1 r i).trans (hca r i))⟩
  have hq ⦃j : ℤ⦄ ⦃x : lIdeal (idems₂ s₂)⦄ (hx : x.val ∈ wgrading j) :
      D.quotient s₂ x ∈ T j := by
    rw [hD]
    exact middleStandardQuotient_mem_grade k hx
  let L : Unit → ModuleCat A₂ᵐᵒᵖ := fun _ => ModuleCat.of _ (MiddleTensorCoefficient k)
  have hF : HasFiltration L [()] (ModuleCat.of _ (MiddleTensorCoefficient k)) :=
    HasFiltration.single (LinearEquiv.refl _ _)
  -- Use the stalk term's decomposition to identify the ordered resolution target.
  have hZ := (@orderedWeightDerivedTensor_cohomology_isZero_of_filtered_loading_support
    _ _ _ _ _ _ _ _ D s₂ he₀ he htrans T (middleGradedChainTerm k).decomp
      (middleGradedChainTerm k).smul_mem hq)
    (fun d => (middleTensorCoefficientGrade k d).toAddSubgroup)
    (middleCoefficient_scalarLeft k) (middleCoefficient_reflectedRight k)
    hF (fun i hi _ _ z => coefficient_kills_higher k i.1 i.2 hi z) X n hn
  let F := middleReflectedWeightDerivedTensor k
  let H := CatModule.DerivedCategory.cohomologyFunctor X n
  exact hZ.of_iso ((F ⋙ H).mapIso
    (CatModule.DerivedCategory.Q.mapIso (middleWeightStalkIso k))).symm

end HigherSupport

end Categorification.Stendhal.LabelTwo
