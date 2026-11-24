/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.WeightModuleExactTriangle
import Categorification.Algebra.DiagramWeightTensorCone
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import DG.Homotopy.CohomologyComparison

/-!
# Cohomology of two-stage diagram-weight tensors

The length-two case in Webster, arXiv:1309.3796v2, §7.1, Proposition 7.11,
requires two comparisons. Tensoring the resolution commutes with the two
mapping cones. In the resulting degree-zero terms, the middle component
of a cocycle represents its class modulo the first differential.
-/

noncomputable section
namespace Categorification
open CategoryTheory DG CatModule
open Stendhal.FundamentalCorner
open scoped DG.DegreeZero
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  {M N M' N' : CatModule.{w} C} (p : M ⟶ N) (q : M' ⟶ N') (e : M ≅ M') (e' : N ≅ N')
  (h : p ≫ e'.hom = e.hom ≫ q)

private def mapConeIso :
    cone p ≅ cone q where
  hom := cone.map e.hom e'.hom h
  inv := cone.map e.inv e'.inv (by rw [← cancel_epi e.hom, ← Category.assoc, ← h]; simp)
  hom_inv_id := by
    apply CatModule.Hom.ext
    rintro X ⟨x,y⟩
    exact Prod.ext (congrArg (shift.mk 1) (congrArg (fun k : M ⟶ M => k.app X (shift.unmk 1 x)) e.hom_inv_id))
      (congrArg (fun k : N ⟶ N => k.app X y) e'.hom_inv_id)
  inv_hom_id := by
    apply CatModule.Hom.ext
    rintro X ⟨x,y⟩
    exact Prod.ext (congrArg (shift.mk 1) (congrArg (fun k : M' ⟶ M' => k.app X (shift.unmk 1 x)) e.inv_hom_id))
      (congrArg (fun k : N' ⟶ N' => k.app X y) e'.inv_hom_id)

section Tensor
variable {A B T : Type u} [Ring A] [Ring B] [InternalGrading A] [InternalGrading B]
  [BigradedDGRing A] [BigradedDGRing B] [AddCommGroup T] [Module A T] [Module Bᵐᵒᵖ T]
  [SMulCommClass A Bᵐᵒᵖ T]
  (G : ℤ → AddSubgroup T)
  (hl : ∀ {i j : ℤ} {a : A} {x : T}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
  (hr : ∀ {i j : ℤ} {b : B} {x : T}, b ∈ wgrading i → x ∈ G j → MulOpposite.op b • x ∈ G (j+i))
  {L M N : CatModule.{u} (WeightCategory B)} (f : L ⟶ M) (g : M ⟶ N) (fg : f ≫ g = 0)
local notation "D" => diagramWeightBimodule G hl hr
local notation "F" => CatBimodule.tensorFunctor D

include fg in
/-- Tensoring the consecutive differentials leaves their composite zero. -/
theorem diagramWeightTensor_comp_zero :
    (F).map f ≫ (F).map g = 0 := by
  rw [← CategoryTheory.Functor.map_comp,fg]
  apply CatModule.Hom.ext
  intro X z
  apply DFunLike.congr_fun (CatTensorProduct.addHom_ext (f := ((D).tensorMap (0 : L ⟶ N)).app X) (g := 0) ?_) z
  intro Y x y
  exact (CatBimodule.tensorMap_tmul D (0 : L ⟶ N) X Y x y).trans (CatTensorProduct.tmul_zero Y x)
local notation "H" => coneDescent f g fg
local notation "H'" => coneDescent (CatBimodule.tensorMap D f) (CatBimodule.tensorMap D g) (diagramWeightTensor_comp_zero G hl hr f g fg)

private theorem tensor_descent :
    (F).map H = (diagramWeightTensorConeIso G hl hr f).hom ≫ H' := by
  apply CatModule.Hom.ext
  intro X z
  apply DFunLike.congr_fun (CatTensorProduct.addHom_ext (f := ((D).tensorMap H).app X)
    (g := ((diagramWeightTensorConeIso G hl hr f).hom ≫ H').app X) ?_) z
  intro Y x p
  change ((D).tensorMap H).app X (CatTensorProduct.tmul Y x p) =
      ((D).tensorMap g).app X (diagramWeightTensorConeAddEquiv G hl hr f X (CatTensorProduct.tmul Y x p)).2
  rw [diagramWeightTensorConeAddEquiv_tmul,CatBimodule.tensorMap_tmul,CatBimodule.tensorMap_tmul]
  rfl

/-- Tensoring the length-two model identifies with the iterated cone of the
two tensor maps, using the mixed term of the cone differential. -/
def diagramWeightTensorTwoStageIso :
    (F).obj (cone H) ≅ cone H' :=
  diagramWeightTensorConeIso G hl hr H ≪≫ mapConeIso _ _ (diagramWeightTensorConeIso G hl hr f)
    (Iso.refl _) (by rw [Iso.refl_hom,Category.comp_id]; exact tensor_descent G hl hr f g fg)
end Tensor
end Categorification

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory DG CatModule
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  {A B E : CatModule.{w} C} (f : A ⟶ B) (g : B ⟶ E) (fg : f ≫ g = 0) (X : C)
local notation "H" => coneDescent f g fg
local notation "K" => CatModule.obj (cone H) X

private abbrev leftCoord (z : K) : A.obj X :=
  shift.unmk 1 ((cone.fstHom f).app X (shift.unmk 1 ((cone.fstHom H).app X z)))
private abbrev midCoord (z : K) : B.obj X :=
  cone.sndAddHom f X (shift.unmk 1 ((cone.fstHom H).app X z))
private abbrev endCoord (z : K) : E.obj X := cone.sndAddHom H X z
private theorem parts_mem {z : K} {n : ℤ} :
    z ∈ DG.grading n ↔ leftCoord f g fg X z ∈ DG.grading (n+1+1) ∧
      midCoord f g fg X z ∈ DG.grading (n+1) ∧ endCoord f g fg X z ∈ DG.grading n :=
  and_assoc

variable (hA : ∀ (n : ℤ) (a : A.obj X), a ∈ DG.grading n ↔ n = 0 ∨ a = 0)
  (hB : ∀ (n : ℤ) (b : B.obj X), b ∈ DG.grading n ↔ n = 0 ∨ b = 0)
  (hE : ∀ (n : ℤ) (e : E.obj X), e ∈ DG.grading n ↔ n = 0 ∨ e = 0)

private theorem d_is_zero {V : Type*} [AddCommGroup V] [DGAddCommGroup V]
    (hV : ∀ (n : ℤ) (z : V), z ∈ DG.grading n ↔ n = 0 ∨ z = 0) (z : V) : d z = 0 := by
  have hh := (hV 1 _).mp (d_mem ((hV 0 z).mpr (Or.inl rfl)))
  exact hh.resolve_left (by decide)

include hA hB hE in
private theorem d_pieces (a : A.obj X) (b : B.obj X) (e : E.obj X) :
    d (weightTwoStagePack f g fg (X := X) a b e) = weightTwoStagePack f g fg (X := X) 0 (-f.app X a) (g.app X b) := by
  rw [weightTwoStagePack_d,d_is_zero hA,d_is_zero hB,d_is_zero hE,add_zero,add_zero]


/-- The two degree-zero maps, evaluated at one object as a short complex of abelian groups. -/
def weightTwoStageComplex : ShortComplex (ModuleCat.{w} ℤ) :=
  ShortComplex.mk (ModuleCat.ofHom (f.app X).toIntLinearMap) (ModuleCat.ofHom (g.app X).toIntLinearMap)
    (ModuleCat.hom_ext (LinearMap.ext fun y => congrArg (fun h : A ⟶ E => h.app X y) fg))
local notation "S" => weightTwoStageComplex f g fg X

include hA hB hE in
private def cyclesMiddle : cocycles K (-1) ≃+ (S).g.hom.ker where
  toFun z := ⟨midCoord f g fg X z, by
    let a := leftCoord f g fg X z
    let b := midCoord f g fg X z
    let e := endCoord f g fg X z
    have h : d (weightTwoStagePack f g fg (X := X) a b e) = 0 := cocycles.d_eq_zero z
    rw [d_pieces f g fg X hA hB hE] at h
    exact congrArg (endCoord f g fg X) h⟩
  invFun z := ⟨weightTwoStagePack f g fg (X := X) 0 z.val 0,
    (parts_mem f g fg X).mpr ⟨zero_mem _,(hB 0 _).mpr (Or.inl rfl),zero_mem _⟩, by
      let b : B.obj X := z.val
      change d (weightTwoStagePack f g fg (X := X) 0 b 0) = 0
      exact (d_pieces f g fg X hA hB hE 0 b 0).trans
        (Prod.ext (Prod.ext rfl (neg_eq_zero.mpr (map_zero _))) z.property)⟩
  left_inv z := by
    apply Subtype.ext
    have h := (parts_mem f g fg X).mp z.property.1
    exact Prod.ext (Prod.ext (((hA 1 _).mp h.1).resolve_left (by decide)).symm rfl)
      (((hE (-1) _).mp h.2.2).resolve_left (by decide)).symm
  right_inv _ := rfl
  map_add' _ _ := rfl

include hA hB hE in
private theorem boundary_range (y : (S).g.hom.ker) :
    y ∈ ((coboundaries K (-1)).addSubgroupOf _).map
      (cyclesMiddle f g fg X hA hB hE).toAddMonoidHom ↔ y ∈ (S).moduleCatToCycles.range := by
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨w,_,hw⟩ := AddSubgroup.mem_addSubgroupOf.mp hz
    let a := leftCoord f g fg X w
    let b := midCoord f g fg X w
    let e := endCoord f g fg X w
    change d (weightTwoStagePack f g fg (X := X) a b e) = _ at hw
    rw [d_pieces f g fg X hA hB hE] at hw
    exact ⟨-a,Subtype.ext ((map_neg (f.app X) a).trans (congrArg (midCoord f g fg X) hw))⟩
  · rintro ⟨a,rfl⟩
    let l := cyclesMiddle f g fg X hA hB hE
    refine ⟨l.symm ((S).moduleCatToCycles a),AddSubgroup.mem_addSubgroupOf.mpr ?_,l.apply_symm_apply _⟩
    refine ⟨weightTwoStagePack f g fg (X := X) (-a) 0 0, (parts_mem f g fg X).mpr
      ⟨(hA 0 _).mpr (Or.inl rfl),zero_mem _,zero_mem _⟩,?_⟩
    let a' : A.obj X := a
    refine (d_pieces f g fg X hA hB hE (-a') 0 0).trans ?_
    exact Prod.ext (Prod.ext rfl ((congrArg Neg.neg (map_neg (f.app X) a')).trans (neg_neg _))) (map_zero _)

/-- At cohomological degree minus one, the iterated cone of two maps between
degree-zero modules has the middle homology of their short complex. -/
def twoStageMiddleCohomologyEquiv :
    cohomology K (-1) ≃+ (S).homology :=
  (QuotientAddGroup.congr _ _ (cyclesMiddle f g fg X hA hB hE)
    (AddSubgroup.ext fun y => (boundary_range f g fg X hA hB hE y).trans Iff.rfl)).trans
    (S).moduleCatHomologyIso.symm.toLinearEquiv.toAddEquiv

include hA hB hE in
/-- When the end maps are injective and surjective, every degree other
than minus one has zero cohomology. -/
theorem twoStageCohomology_eq_zero_of_ne_middle
    (hi : Function.Injective (f.app X)) (hs : Function.Surjective (g.app X))
    (n : ℤ) (hn : n ≠ -1) (z : cohomology K n) : z = 0 := by
  obtain ⟨y,rfl⟩ := cohomology.mk_surjective K n z
  apply (cohomology.mk_eq_zero_iff y).mpr
  let a := leftCoord f g fg X y
  let b := midCoord f g fg X y
  let e := endCoord f g fg X y
  have h : d (weightTwoStagePack f g fg (X := X) a b e) = 0 := cocycles.d_eq_zero y
  rw [d_pieces f g fg X hA hB hE] at h
  have hfa : -f.app X a = 0 := congrArg (midCoord f g fg X) h
  have ha : a = 0 := hi ((neg_eq_zero.mp hfa).trans (map_zero _).symm)
  obtain ⟨_, hb, he⟩ := (parts_mem f g fg X).mp (cocycles.mem_grading y)
  have hb0 : b = 0 := ((hB _ _).mp hb).resolve_left (by omega)
  change ∃ t ∈ DG.grading (n-1), d t = weightTwoStagePack f g fg (X := X) a b e
  rw [ha,hb0]
  rcases (hE _ _).mp he with rfl | he0
  · obtain ⟨b',hu⟩ := hs e
    refine ⟨weightTwoStagePack f g fg (X := X) 0 b' 0,(parts_mem f g fg X).mpr
      ⟨zero_mem _,(hB 0 _).mpr (Or.inl rfl),zero_mem _⟩,?_⟩
    rw [d_pieces f g fg X hA hB hE,map_zero,neg_zero,hu]
  · change e = 0 at he0
    rw [he0]
    exact ⟨0,zero_mem _,d_zero⟩

end Categorification.Stendhal.FundamentalCorner