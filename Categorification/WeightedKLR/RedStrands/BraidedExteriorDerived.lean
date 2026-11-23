/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedExteriorTensor
import DG.Category.Derived.Tensor
import DG.Category.Weight
import DG.Homotopy.Comparison

/-!
# The derived braid in Webster's Figure 5

Webster, arXiv:1309.3796v2, §6.1, Definitions 6.2 and 6.6 and the proof of Proposition 6.9.
Use the integer weight categories of the two opposing orders. The source has internal coset
`ℤ`; the target has coset `c + ℤ`, where `c = 2 − ⟨λ₁, λ₀⟩`. The lower exterior standardization
is K-projective in the source, so its derived tensor with the braid is computed by the
ordinary categorical coend, without K-projectivity of the braid's output slices. Evaluation at
the source representable at zero identifies this coend with the loading cut. The Figure 5
comparison then reads the cut at coordinate `n` as the upper exterior standardization at its
intrinsic degree `n + c + ⟨λ₀ − α, λ₁⟩`, in cochain degree zero.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR DG Equiv QuantumGroup Categorification.Graded DirectSum MulOpposite CornerEndomorphism
open CategoryTheory
open scoped DG.DegreeZero

namespace FigureFiveWeight

/-- Fix the chosen internal pieces in the type of the two order rings. -/
def WithWeights (R : Type) [Ring R] (_W : ℤ → Submodule ℤ R) := R

section Weights

variable {R : Type} [Ring R] {W : ℤ → Submodule ℤ R}

instance : Ring (WithWeights R W) := inferInstanceAs (Ring R)

@[instance_reducible]
private def degreeZeroWeights [h : Decomposition W] : InternalGrading R where
  wgrading n := (W n).toAddSubgroup
  wdecomposition := { decompose' := h.decompose', left_inv := h.left_inv, right_inv := h.right_inv }
  isHomogeneous_grading' n j m hm := by
    rcases (mem_degreeZeroGrading_iff R).mp hm with rfl | rfl
    · exact mem_degreeZeroGrading_zero R _
    · change (decompose W (0 : R) j : R) ∈ degreeZeroGrading R n
      rw [decompose_zero, DFinsupp.zero_apply]
      exact zero_mem _
  d_mem_wgrading' _ := zero_mem _

instance [Decomposition W] : InternalGrading (WithWeights R W) := degreeZeroWeights (R := R) (W := W)

instance [Decomposition W] [hW : SetLike.GradedMonoid W] : BigradedDGRing (WithWeights R W) where
  one_mem := hW.one_mem
  mul_mem := hW.mul_mem

private theorem map_mem_degreeZero {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (f : M →+ N) {n : ℤ} {m : M} (hm : m ∈ degreeZeroGrading M n) :
    f m ∈ degreeZeroGrading N n := by
  rcases (mem_degreeZeroGrading_iff M).1 hm with hn | rfl
  · exact (mem_degreeZeroGrading_iff N).2 (Or.inl hn)
  · rw [map_zero]
    exact zero_mem _

private theorem bilinear_mem_degreeZero {L M N : Type} [AddCommGroup L] [AddCommGroup M]
    [AddCommGroup N] (f : L →+ M →+ N) {i j : ℤ} {l : L} {m : M}
    (hl : l ∈ degreeZeroGrading L i) (hm : m ∈ degreeZeroGrading M j) :
    f l m ∈ degreeZeroGrading N (i + j) := by
  rcases (mem_degreeZeroGrading_iff L).1 hl with rfl | rfl
  · rw [zero_add]
    exact map_mem_degreeZero _ hm
  · rw [map_zero, AddMonoidHom.zero_apply]
    exact zero_mem _

variable (W) [Decomposition W] [SetLike.GradedMonoid W]

local notation "K" => WeightCategory (WithWeights R W)

private abbrev unweighted (a : WithWeights R W) : R := a

private def pieceAct {M : Type} [AddCommGroup M] [Module R M] (L : ℤ → Submodule ℤ M)
    (hL : ∀ {i j : ℤ} {a : R} {x : M}, a ∈ W i → x ∈ L j → a • x ∈ L (i + j))
    {X Y : K} : (X ⟶ Y) →+ L X.as →+ L Y.as :=
  AddMonoidHom.mk' (fun f => AddMonoidHom.mk'
    (fun x => ⟨unweighted W f.1 • x.1, by
      have h := hL f.2 x.2
      rwa [sub_add_cancel] at h⟩)
    (fun x y => Subtype.ext (smul_add (unweighted W f.1) x.1 y.1)))
    (fun f g => AddMonoidHom.ext fun x => Subtype.ext (add_smul (unweighted W f.1) (unweighted W g.1) x.1))

/-- A module in cochain degree zero on the indicated integer coset. -/
def weightModule {M : Type} [AddCommGroup M] [Module R M] (L : ℤ → Submodule ℤ M)
    (hL : ∀ {i j : ℤ} {a : R} {x : M}, a ∈ W i → x ∈ L j → a • x ∈ L (i + j)) :
    CatModule.{0} K where
  obj X := L X.as
  isDGAddCommGroup X := DGAddCommGroup.degreeZero (L X.as)
  act := pieceAct W L hL
  act_mem' {X Y i j f x} hf hx := by
    refine bilinear_mem_degreeZero (pieceAct W L hL) ?_ hx
    have hf' := (WeightCategory.mem_grading_iff (A := WithWeights R W)).1 hf
    rcases (mem_degreeZeroGrading_iff (WithWeights R W)).1 hf' with hi | h
    · exact (mem_degreeZeroGrading_iff _).2 (Or.inl hi)
    · exact (mem_degreeZeroGrading_iff _).2 (Or.inr (Subtype.ext h))
  act_id' _ x := Subtype.ext (one_smul R x.1)
  act_comp' f g x := Subtype.ext (mul_smul (unweighted W g.1) (unweighted W f.1) x.1)
  d_act' {X Y i f} _ x := by
    have hf : d f = 0 := Subtype.ext rfl
    change 0 = pieceAct W L hL (d f) x + koszulSign i • pieceAct W L hL f 0
    rw [hf, map_zero, AddMonoidHom.zero_apply, map_zero, smul_zero, add_zero]

private theorem weightModule_act_val {M : Type} [AddCommGroup M] [Module R M]
    (L : ℤ → Submodule ℤ M)
    (hL : ∀ {i j : ℤ} {a : R} {x : M}, a ∈ W i → x ∈ L j → a • x ∈ L (i + j))
    {X Y : K} (f : X ⟶ Y) (x : (weightModule W L hL).obj X) :
    ((weightModule W L hL).act f x).val = unweighted W f.val • x.val := rfl

open CatModule in
/-- The graded retract of the regular module yields a K-projective weight module. -/
theorem weightModule_isKProjective {M : Type} [AddCommGroup M] [Module R M]
    (L : ℤ → Submodule ℤ M)
    (hL : ∀ {i j : ℤ} {a : R} {x : M}, a ∈ W i → x ∈ L j → a • x ∈ L (i + j))
    (i : M →ₗ[R] R) (p : R →ₗ[R] M) (hi : ∀ n x, x ∈ L n → i x ∈ W n)
    (hp : ∀ n a, a ∈ W n → p a ∈ L n) (hpi : Function.LeftInverse p i) :
    IsKProjective (weightModule W L hL) := by
  let X : K := ⟨0⟩
  let gen : (weightModule W L hL).obj X := ⟨p 1, hp 0 1 SetLike.GradedOne.one_mem⟩
  have action (a : R) : a • p 1 = p a := (p.map_smul a 1).symm.trans (congrArg p (mul_one a))
  let e : X ⟶ X := ⟨i (p 1), by
    change i (p 1) ∈ W (0 - 0)
    rw [sub_zero]
    exact hi 0 _ gen.2⟩
  have e_act : (i (p 1)) • p 1 = p 1 := (action _).trans (hpi _)
  let idem : DGCategory.Idempotent X :=
    { val := e
      mem_cocycles := ⟨WeightCategory.mem_grading_iff.2 (mem_degreeZeroGrading_zero _ _), Subtype.ext rfl⟩
      comp_self := Subtype.ext ((i.map_smul (i (p 1)) (p 1)).symm.trans (congrArg i e_act)) }
  refine IsCornerGenerator.isKProjective (g := gen) (e := idem) (k := 0) ?_
  refine ⟨mem_degreeZeroGrading_zero _ _, rfl, Subtype.ext e_act, ?_, ?_⟩
  · intro Y x
    let f : X ⟶ Y := ⟨i x.val, by
      change i x.val ∈ W (Y.as - 0)
      rw [sub_zero]
      exact hi Y.as _ x.2⟩
    exact ⟨f, Subtype.ext ((action _).trans (hpi x.val))⟩
  · intro Y f hf
    have h := congrArg (fun x : (weightModule W L hL).obj Y => i x.val) hf
    have hf' : i (unweighted W f.val • p 1) = i (0 : M) := h
    exact Subtype.ext ((i.map_smul (unweighted W f.val) (p 1)).symm.trans (hf'.trans (map_zero i)))

private theorem hom_mem_degreeZero_iff {X Y : K} {i : ℤ} {f : X ⟶ Y} :
    f ∈ DG.grading i ↔ f ∈ degreeZeroGrading (X ⟶ Y) i := by
  rw [WeightCategory.mem_grading_iff]
  change f.val ∈ degreeZeroGrading _ i ↔ f ∈ degreeZeroGrading _ i
  rw [mem_degreeZeroGrading_iff, mem_degreeZeroGrading_iff]
  exact or_congr_right ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

section Bimodule
open MulOpposite
variable {S : Type} [Ring S] (V : ℤ → Submodule ℤ S) [Decomposition V] [SetLike.GradedMonoid V]
  {M : Type} [AddCommGroup M] [Module R M] [Module Sᵐᵒᵖ M] [SMulCommClass R Sᵐᵒᵖ M]
  (G : ℤ → Submodule ℤ M)

local notation "J" => WeightCategory (WithWeights S V)

private def weightBimoduleRact
    (hr : ∀ {i j : ℤ} {b : S} {x : M}, b ∈ V i → x ∈ G j → op b • x ∈ G (j + i))
    {X : K} {Y Y' : J} : (Y ⟶ Y') →+ G (X.as - Y'.as) →+ G (X.as - Y.as) :=
  AddMonoidHom.mk' (fun f => AddMonoidHom.mk'
    (fun x => ⟨op (unweighted V f.val) • x.val, by
      have h := hr f.2 x.2
      rwa [show (X.as - Y'.as) + (Y'.as - Y.as) = X.as - Y.as by omega] at h⟩)
    (fun x y => Subtype.ext (smul_add (op (unweighted V f.val)) x.1 y.1)))
    (fun f g => AddMonoidHom.ext fun x => Subtype.ext (add_smul (op (unweighted V f.val)) (op (unweighted V g.val)) x.1))

/-- The components of a graded bimodule on the indicated pair of cosets. -/
def weightBimodule
    (hl : ∀ {i j : ℤ} {a : R} {x : M}, a ∈ W i → x ∈ G j → a • x ∈ G (i + j))
    (hr : ∀ {i j : ℤ} {b : S} {x : M}, b ∈ V i → x ∈ G j → op b • x ∈ G (j + i)) :
    CatBimodule.{0} K J where
  obj X Y := G (X.as - Y.as)
  isDGAddCommGroup X Y := DGAddCommGroup.degreeZero (G (X.as - Y.as))
  lact {_ _ Y} := pieceAct W (fun i => G (i - Y.as)) (fun {i j} _ _ ha hx => by
    have h := hl ha hx
    rwa [show i + (j - Y.as) = i + j - Y.as by omega] at h)
  ract := weightBimoduleRact W V G hr
  lact_mem' hf hx := bilinear_mem_degreeZero _ ((hom_mem_degreeZero_iff W).1 hf) hx
  ract_mem' {X Y Y' i j g x} hg hx := by
    rw [add_comm j i]
    exact bilinear_mem_degreeZero (weightBimoduleRact W V G hr (X := X))
      ((hom_mem_degreeZero_iff V).1 hg) hx
  lact_id' _ _ x := Subtype.ext (one_smul R x.val)
  ract_id' _ _ x := Subtype.ext (one_smul Sᵐᵒᵖ x.val)
  lact_comp' f g x := Subtype.ext (mul_smul (unweighted W g.val) (unweighted W f.val) x.val)
  ract_comp' f g x := Subtype.ext (mul_smul (op (unweighted V f.val)) (op (unweighted V g.val)) x.val)
  d_lact' {_ _ _ i _} _ x := Subtype.ext (by
    change (0 : M) = (0 : R) • x.val + koszulSign i • (_ • (0 : M))
    rw [zero_smul, smul_zero, smul_zero, add_zero])
  d_ract' {_ _ _ j x} _ g := Subtype.ext (by
    change (0 : M) = op (unweighted V g.val) • (0 : M) + koszulSign j • (op (0 : S) • x.val)
    rw [op_zero, zero_smul, smul_zero, smul_zero, add_zero])
  lact_ract' f g x := Subtype.ext (smul_comm (unweighted W f.val) (op (unweighted V g.val)) x.val)

end Bimodule

end Weights

section DerivedTensor

variable {C D : Type} [Category.{0} C] [Category.{0} D] [Preadditive C] [Preadditive D]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] [DGCategory D]
  (B : CatBimodule.{0} D C)

private def homotopyTensor : CatModule.HomotopyCategory.{0} C ⥤ CatModule.HomotopyCategory.{0} D :=
  CategoryTheory.Quotient.lift _ (B.tensorFunctor ⋙ CatModule.HomotopyCategory.quotient D)
    (fun _ _ _ _ h => CatModule.HomotopyCategory.eq_of_homotopy _ _ (B.homotopic_tensorMap h).some)

universe w w'
variable [CatModule.HasDerivedCategory.{w,0} C] [CatModule.HasDerivedCategory.{w',0} D]
open CatModule.DerivedCategory

private def derivedTensor : CatModule.DerivedCategory.{w,0} C ⥤ CatModule.DerivedCategory.{w',0} D :=
  (kProjectiveEquivalence C).inverse ⋙ (CatModule.HomotopyCategory.subcategoryKProjective C).ι ⋙
    homotopyTensor B ⋙ Qh

private def derivedTensorObjIso (P : CatModule.{0} C) (hP : CatModule.IsKProjective P) :
    (derivedTensor B).obj (Q.obj P) ≅ Q.obj (B.tensorObj P) := by
  let X : (CatModule.HomotopyCategory.subcategoryKProjective.{0} C).FullSubcategory :=
    ⟨(CatModule.HomotopyCategory.quotient C).obj P,
     (CatModule.HomotopyCategory.quotient_obj_mem_subcategoryKProjective_iff P).mpr hP⟩
  exact Qh.mapIso ((homotopyTensor B).mapIso
    ((CatModule.HomotopyCategory.subcategoryKProjective C).ι.mapIso
      ((kProjectiveEquivalence.{w} C).unitIso.app X).symm))

end DerivedTensor

section CoendSummand
open CatModule CatTensorProduct

variable {C D : Type} [Category.{0} C] [Category.{0} D] [Preadditive C] [Preadditive D]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [∀ X Y : D, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C] (B : CatBimodule.{0} D C) (X : C)
  {L : CatModule.{0} C} {T : CatModule.{0} D}

private theorem rid_tmul_ract (Y : D) (Z : C) (b : B.obj Y Z) (a : X ⟶ Z) :
    CatTensorProduct.rid (B.right Y) X (tmul Z b a) = B.ract a b :=
  (CatTensorProduct.rid_tmul (N := B.right Y) X Z b a).trans (B.right_ract Y a b)

private def representableEval : B.tensorObj (representable X) ⟶ B.left X where
  app Y := (CatTensorProduct.rid (B.right Y) X).toAddEquiv.toAddMonoidHom
  map_mem' h := (CatTensorProduct.rid _ X).map_mem h
  map_d' t := (CatTensorProduct.rid _ X).map_d t
  map_smul' {Y Y'} f t := by
    change CatTensorProduct.rid (B.right Y') X (B.tensorAct (representable X) f t) =
      B.lact f (CatTensorProduct.rid (B.right Y) X t)
    induction t using CatTensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add t t' h h' => simp only [map_add, h, h']
    | tmul Z b a =>
        rw [CatBimodule.tensorAct_tmul]
        exact (rid_tmul_ract B X Y' Z (B.lact f b) a).trans
          ((B.lact_ract' f a b).symm.trans (congrArg (B.lact f) (rid_tmul_ract B X Y Z b a).symm))

private def summandEval (i : L ⟶ representable X) (p : B.left X ⟶ T) : B.tensorObj L ⟶ T :=
  B.tensorFunctor.map i ≫ representableEval B X ≫ p

private theorem summandEval_tmul (i : L ⟶ representable X) (p : B.left X ⟶ T)
    (Y : D) (Z : C) (b : B.obj Y Z) (x : L.obj Z) :
    (summandEval B X i p).app Y (tmul Z b x) = p.app Y (B.ract (i.app Z x) b) := by
  change p.app Y (CatTensorProduct.rid (B.right Y) X ((B.tensorMap i).app Y (tmul Z b x))) = _
  rw [CatBimodule.tensorMap_tmul]
  exact congrArg (p.app Y) (rid_tmul_ract B X Y Z b (i.app Z x))

-- Co-Yoneda sends the tensor of a representable summand to the corresponding cut.
private def coendSummandIso (i : L ⟶ representable X) (g : L.obj X)
    (p : B.left X ⟶ T) (j : ∀ Y, T.obj Y →+ B.obj Y X)
    (hg : ∀ Z (x : L.obj Z), L.act (i.app Z x) g = x)
    (hj : ∀ Y y, p.app Y (j Y y) = y)
    (hp : ∀ Y b, j Y (p.app Y b) = B.ract (i.app X g) b) : B.tensorObj L ≅ T := by
  let f := summandEval B X i p
  let inv (Y : D) : (T.obj Y) →+ (B.tensorObj L).obj Y :=
    ((tmulAddHom (B.right Y) L X).flip g).comp (j Y)
  have hleft (Y : D) : (inv Y).comp (f.app Y) = AddMonoidHom.id _ := by
    apply CatTensorProduct.addHom_ext
    intro Z b x
    change tmul X (j Y ((summandEval B X i p).app Y (tmul Z b x))) g = tmul Z b x
    rw [summandEval_tmul]
    have hh : (i.app X g : X ⟶ X) ≫ (i.app Z x : X ⟶ Z) = i.app Z x :=
      (i.map_smul (i.app Z x) g).symm.trans (congrArg (i.app Z) (hg Z x))
    have hfix := (hp Y (B.ract (i.app Z x) b)).trans
      ((B.ract_comp' (i.app X g) (i.app Z x) b).symm.trans (congrArg (fun a => B.ract a b) hh))
    exact (congrArg (fun k => tmul X k g) (hfix.trans (B.right_ract Y (i.app Z x) b).symm)).trans
      ((ract_tmul (N := B.right Y) (M := L) (i.app Z x) b g).trans (congrArg (tmul Z b) (hg Z x)))
  have hright (Y : D) (y : T.obj Y) : f.app Y (inv Y y) = y := by
    change (summandEval B X i p).app Y (tmul X (j Y y) g) = y
    rw [summandEval_tmul]
    exact (congrArg (p.app Y) (hp Y (j Y y)).symm).trans
      ((congrArg (fun t => p.app Y (j Y t)) (hj Y y)).trans (hj Y y))
  let a (Y : D) : (B.tensorObj L).obj Y ≃+ T.obj Y :=
    { f.app Y with invFun := inv Y, left_inv := DFunLike.congr_fun (hleft Y), right_inv := hright Y }
  exact CatModule.isoMk a
    (fun {Y _ _} => ⟨fun h => mem_grading_of_injective (f.app Y) f.map_mem (a Y).injective h, f.map_mem⟩)
    (fun {_} => f.map_d) (fun f' t => f.map_smul f' t)

private theorem coendSummandIso_hom_app_tmul (i : L ⟶ representable X) (g : L.obj X)
    (p : B.left X ⟶ T) (j : ∀ Y, T.obj Y →+ B.obj Y X) (hg hj hp)
    (Y : D) (Z : C) (b : B.obj Y Z) (x : L.obj Z) :
    (coendSummandIso B X i g p j hg hj hp).hom.app Y (tmul Z b x) = p.app Y (B.ract (i.app Z x) b) :=
  summandEval_tmul B X i p Y Z b x

private theorem coendSummandIso_inv_app (i : L ⟶ representable X) (g : L.obj X)
    (p : B.left X ⟶ T) (j : ∀ Y, T.obj Y →+ B.obj Y X) (hg hj hp) (Y : D) (y : T.obj Y) :
    (coendSummandIso B X i g p j hg hj hp).inv.app Y y = tmul X (j Y y) g := rfl

end CoendSummand

end FigureFiveWeight

section WeightEvaluation
open CategoryTheory
open scoped DG.DegreeZero
variable {I k : Type} [DecidableEq I] [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin 2 → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight 2 ν))) → List ℕ}
  (C : CartanDatum I) (hR : IsRouquierQ C Q) (hρ : TypeA.IsReducedChoice ρ)

local notation "T" κ:arg => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ
local notation "A" => (T [0, 1])ᵐᵒᵖ
local notation "D" => (T [1, 0])ᵐᵒᵖ
local notation "M" => InDegreeZero (OpBimodule (T [0, 1]) (braidingBimodule k Q Λ ν [0, 1] [1, 0]))
local notation "LA" => figureFiveLowerOrderPieces (Λ := Λ) (ν := ν) C hR
local notation "UD" => figureFiveUpperOrderPieces (Λ := Λ) (ν := ν) C hR
local notation "NE" u:arg => figureFiveLowerExteriorPieces (Λ := Λ) C hR hρ u

/-- The weight category for the integer coset of the lower order in Webster's Figure 5. -/
abbrev figureFiveLowerWeightCategory := WeightCategory (FigureFiveWeight.WithWeights A LA)

/-- The weight category for the upper order in Webster's Figure 5. With a fixed choice of
coset offset `c`, object `n` represents internal degree `(n : ℂ) + c`. -/
abbrev figureFiveUpperWeightCategory := WeightCategory (FigureFiveWeight.WithWeights D UD)

local notation "CLo" => figureFiveLowerWeightCategory (Λ := Λ) (ν := ν) C hR
local notation "CUp" => figureFiveUpperWeightCategory (Λ := Λ) (ν := ν) C hR

/-- The lower exterior standardization in cochain degree zero, as a dg module on its
integer internal coset. Its value at weight `n` is the intrinsic lower exterior piece. -/
def figureFiveLowerWeightModule (u : Seq ν) : CatModule.{0} CLo :=
  FigureFiveWeight.weightModule LA (NE u) (fun {_ _ _ _} ha hx => figureFiveLowerExteriorPieces_smul C hR hρ u ha hx)

/-- Webster, arXiv:1309.3796v2, §6.1, proof of Proposition 6.9. The degree-zero loading retract gives a K-projective dg module in the source weight
category of the Figure 5 braid. -/
theorem figureFiveLowerWeightModule_isKProjective (u : Seq ν) :
    CatModule.IsKProjective (figureFiveLowerWeightModule (Λ := Λ) C hR hρ u) := by
  obtain ⟨hi, hp, hsplit⟩ := figureFiveLowerExterior_graded_retract (Λ := Λ) C hR hρ u
  refine FigureFiveWeight.weightModule_isKProjective LA (NE u) (fun {_ _ _ _} ha hx => figureFiveLowerExteriorPieces_smul C hR hρ u ha hx)
    (figureFiveLowerExteriorInclusion (Λ := Λ) C hR hρ u)
    (figureFiveLowerExteriorProjection (Λ := Λ) C hR hρ u) ?_ ?_ hsplit
  · intro n x hx
    rw [← figureFiveLowerExteriorGrade_int] at hx
    rw [← figureFiveLowerOrderGrade_int]
    exact hi hx
  · intro n a ha
    rw [← figureFiveLowerOrderGrade_int] at ha
    rw [← figureFiveLowerExteriorGrade_int]
    exact hp ha

variable {H : Type*} [AddCommGroup H] [Module ℂ H]
  (B : LinearMap.BilinForm ℂ (Module.Dual ℂ H)) (η : Fin 2 → Module.Dual ℂ H)
local notation "c" => (2 - B (η 1) (η 0))
local notation "BG" => (fun n : ℤ => figureFiveBraidGrade (Λ := Λ) (ν := ν) C hR B η ((n : ℂ) + c))
attribute [local instance] figureFiveBraidActionsCommute

/-- The Figure 5 braid on the two weight categories, with the output integer coordinate `n`
read at complex internal degree `n + c` and input coordinate `m` at degree `m`. -/
def figureFiveBraidWeightBimodule : CatBimodule.{0} CUp CLo := by
  refine FigureFiveWeight.weightBimodule UD LA BG ?_ ?_
  · intro i j a x ha hx
    rw [← figureFiveUpperOrderGrade_int] at ha
    change x ∈ figureFiveBraidGrade C hR B η ((j : ℂ) + c) at hx
    have h := figureFiveBraid_right_mem_grade C hR B η ha hx
    change a • x ∈ figureFiveBraidGrade C hR B η (((i + j : ℤ) : ℂ) + c)
    rw [show (((i + j : ℤ) : ℂ) + c) = (j : ℂ) + c + (i : ℂ) by push_cast; abel]
    exact h
  · intro i j a x ha hx
    rw [← figureFiveLowerOrderGrade_int] at ha
    change x ∈ figureFiveBraidGrade C hR B η ((j : ℂ) + c) at hx
    have h := figureFiveBraid_left_mem_grade C hR B η ha hx
    change op a • x ∈ figureFiveBraidGrade C hR B η (((j + i : ℤ) : ℂ) + c)
    rw [show (((j + i : ℤ) : ℂ) + c) = (i : ℂ) + ((j : ℂ) + c) by push_cast; ring]
    exact h

local instance figureFiveLowerWeightDerived : CatModule.HasDerivedCategory.{1,0} CLo := CatModule.HasDerivedCategory.standard CLo
local instance figureFiveUpperWeightDerived : CatModule.HasDerivedCategory.{1,0} CUp := CatModule.HasDerivedCategory.standard CUp

/-- The derived tensor of the Figure 5 braid on the two internal cosets, in the ambient
unbounded derived categories. -/
def figureFiveBraidDerivedTensor : CatModule.DerivedCategory.{1,0} CLo ⥤ CatModule.DerivedCategory.{1,0} CUp :=
  FigureFiveWeight.derivedTensor (C := CLo) («D» := CUp)
    (figureFiveBraidWeightBimodule (Λ := Λ) (ν := ν) C hR B η)

/-- Webster, arXiv:1309.3796v2, §6.1, Definition 6.6 and proof of Proposition 6.9.
The internally graded two-coset derived braid evaluated at the lower exterior projective
is the ordinary categorical tensor of the braid with that projective. -/
def figureFiveBraidDerivedTensorObjIso (u : Seq ν) :
    (figureFiveBraidDerivedTensor (Λ := Λ) (ν := ν) C hR B η).obj
        ((CatModule.DerivedCategory.Q (C := CLo)).obj (figureFiveLowerWeightModule (Λ := Λ) C hR hρ u)) ≅
      (CatModule.DerivedCategory.Q (C := CUp)).obj ((figureFiveBraidWeightBimodule (Λ := Λ) (ν := ν) C hR B η).tensorObj
        (figureFiveLowerWeightModule (Λ := Λ) C hR hρ u)) :=
  FigureFiveWeight.derivedTensorObjIso (C := CLo) («D» := CUp) _ _
    (figureFiveLowerWeightModule_isKProjective (Λ := Λ) C hR hρ u)

/-- For the two-red braid of Webster, arXiv:1309.3796v2, §6.1, Definition 6.6, the
ordinary coend on a supplied K-projective model represents the ambient derived value and
preserves its cochain upper bound. This intermediate statement assumes a bounded model in
the source weight category. Existence of finite graded models and termwise finiteness of
the output are separate from this bound. -/
theorem figureFiveBraidDerivedTensor_exists_cochain_bound
    (X : CatModule.DerivedCategory.{1,0} CLo) (P : CatModule.{0} CLo)
    (e : X ≅ (CatModule.DerivedCategory.Q (C := CLo)).obj P)
    (hP : CatModule.IsKProjective P) (b : ℤ)
    (hb : ∀ (m : CLo) (j : ℤ), b < j → ∀ x : P.obj m, x ∈ DG.grading j → x = 0) :
    ∃ N : CatModule.{0} CUp,
      Nonempty ((figureFiveBraidDerivedTensor (Λ := Λ) (ν := ν) C hR B η).obj X ≅
        (CatModule.DerivedCategory.Q (C := CUp)).obj N) ∧
      (∀ (n : CUp) (j : ℤ), b < j → ∀ x : N.obj n, x ∈ DG.grading j → x = 0) := by
  let F := figureFiveBraidDerivedTensor (Λ := Λ) (ν := ν) C hR B η
  let braid := figureFiveBraidWeightBimodule (Λ := Λ) (ν := ν) C hR B η
  refine ⟨braid.tensorObj P,
    ⟨F.mapIso e ≪≫ FigureFiveWeight.derivedTensorObjIso braid P hP⟩, ?_⟩
  intro n j hj x hx
  change x ∈ DG.grading («M» := CatTensorProduct (braid.right n) P) j at hx
  refine CatTensorProduct.induction_on_mem_grading (N := braid.right n) («M» := P)
    (P := fun x : CatTensorProduct (braid.right n) P => x = 0) rfl ?_
    (fun _ _ hu hv => by rw [hu, hv, add_zero]) (fun _ hu => by rw [hu, neg_zero]) hx
  intro m i l y z hy hz hij
  change y ∈ degreeZeroGrading _ i at hy
  rcases (mem_degreeZeroGrading_iff _).1 hy with rfl | hy0
  · rw [zero_add] at hij
    subst l
    rw [hb m j hj z hz, CatTensorProduct.tmul_zero]
  · rw [hy0, CatTensorProduct.zero_tmul]

section CoendCut
open CatModule CatTensorProduct

local notation "Y" u:arg => violCorner k Q Λ ν (figureFiveLower u) [1, 0]
local notation "e" u:arg => violMk k Q Λ ν (ofKLR k Q Λ ν (KLRAlgebra.e (figureFiveLower u)))
local notation "In" u:arg => figureFiveLowerExteriorInclusion (Λ := Λ) C hR hρ u
local notation "Pr" u:arg => figureFiveLowerExteriorProjection (Λ := Λ) C hR hρ u
local notation "NN" u:arg => figureFiveLowerWeightModule (Λ := Λ) C hR hρ u
local notation "BBim" => figureFiveBraidWeightBimodule (Λ := Λ) (ν := ν) C hR B η
local notation "Z" => (⟨0⟩ : CLo)
local notation "CutGrade" u:arg => figureFiveCutGrade (Λ := Λ) C hR B η (figureFiveLower u) 1 0
local notation "CutPieces" u:arg => (fun n : ℤ => Submodule.restrictScalars ℤ ((CutGrade u) ((n : ℂ) + c)))

private theorem lowerInclusion_mem (u : Seq ν) (m : CLo) (x : (NN u).obj m) :
    (In u) x.val ∈ LA (m.as - 0) := by
  have hx : x.val ∈ figureFiveLowerExteriorGrade (Λ := Λ) C hR hρ u (m.as : ℂ) := by
    rw [figureFiveLowerExteriorGrade_int]
    exact x.2
  rw [sub_zero, ← figureFiveLowerOrderGrade_int]
  exact (figureFiveLowerExterior_graded_retract (Λ := Λ) C hR hρ u).1 hx

private def lowerWeightInclusion (u : Seq ν) : NN u ⟶ representable Z where
  app m := AddMonoidHom.mk' (fun x => ⟨(In u) x.val, lowerInclusion_mem C hR hρ u m x⟩)
    (fun x y => Subtype.ext ((In u).map_add x.val y.val))
  map_mem' {_ _ _} hx := (FigureFiveWeight.hom_mem_degreeZero_iff LA).2
    (FigureFiveWeight.map_mem_degreeZero _ hx)
  map_d' x := by
    apply Subtype.ext
    change (In u) 0 = 0
    exact map_zero _
  map_smul' f x := Subtype.ext ((In u).map_smul f.val x.val)

/-- The degree-zero generator of the lower summand, obtained by projecting the regular unit. -/
def figureFiveLowerWeightGenerator (u : Seq ν) : (NN u).obj Z :=
  ⟨(Pr u) 1, by
    change (Pr u) 1 ∈ (NE u) 0
    rw [← figureFiveLowerExteriorGrade_int]
    apply (figureFiveLowerExterior_graded_retract (Λ := Λ) C hR hρ u).2.1
    rw [figureFiveLowerOrderGrade_int]
    exact SetLike.GradedOne.one_mem⟩

private theorem lowerWeightGenerator_act (u : Seq ν) (m : CLo) (x : (NN u).obj m) :
    (NN u).act ((lowerWeightInclusion C hR hρ u).app m x)
      (figureFiveLowerWeightGenerator (Λ := Λ) C hR hρ u) = x := by
  apply Subtype.ext
  change (In u) x.val • (Pr u) 1 = x.val
  calc
    _ = (Pr u) ((In u) x.val * 1) := ((Pr u).map_smul ((In u) x.val) 1).symm
    _ = x.val := by
      rw [mul_one]
      exact (figureFiveLowerExterior_graded_retract (Λ := Λ) C hR hρ u).2.2 x.val

/-- The cut of the Figure 5 braid at the lower loading, in cochain degree zero. -/
def figureFiveBraidCutWeightModule (u : Seq ν) : CatModule.{0} CUp :=
  FigureFiveWeight.weightModule UD (CutPieces u)
    (fun {_ _ _ _} ha hy => figureFiveBraidCut_smul_mem_grade C hR B η u ha hy)

local notation "Cut" u:arg => figureFiveBraidCutWeightModule (Λ := Λ) C hR B η u
local notation "Coend" u:arg => CatBimodule.tensorObj BBim (NN u)

private def cutBraidPiece (u : Seq ν) (n : CUp) (y : (Cut u).obj n) : (BBim).obj n Z :=
  ⟨figureFiveBraidCutInclusion u y.val, by
    change figureFiveBraidCutInclusion u y.val ∈ BG (n.as - 0)
    apply (show BG n.as ≤ BG (n.as - 0) by rw [sub_zero])
    exact (figureFiveBraidCut_mem_grade_iff C hR B η u n.as y.val _ rfl).1 y.2⟩

private def cutInclusion (u : Seq ν) (n : CUp) : (Cut u).obj n →+ (BBim).obj n Z :=
  AddMonoidHom.mk' (cutBraidPiece C hR B η u n) (fun _ _ => Subtype.ext (Subtype.ext rfl))

private theorem cutIdem (u : Seq ν) : (e u) * (e u) = e u := by
  rw [← map_mul, ← map_mul, KLRAlgebra.e_mul_e, ite_eq_left rfl]

private def cutProjectionPiece (u : Seq ν) (n : CUp) (b : (BBim).obj n Z) : (Cut u).obj n := by
  let g := figureFiveLowerWeightGenerator (Λ := Λ) C hR hρ u
  let b' := (BBim).ract ((lowerWeightInclusion C hR hρ u).app Z g) b
  have hb' : b'.val.val = e u * b.val.val :=
    congrArg (fun a => a * b.val.val) (figureFiveLowerExteriorInclusion_projection_one C hR hρ u)
  let y : Y u := ⟨e u * b.val.val, mem_violCorner_iff.2 ⟨by
    rw [← mul_assoc, cutIdem (k := k) (Q := Q) (Λ := Λ) u],
    by rw [mul_assoc, (mem_cornerBimodule.1 b.val.2).2]⟩⟩
  have hb : b'.val ∈ BG n.as := (show BG (n.as - 0) ≤ BG n.as by rw [sub_zero]) b'.2
  exact ⟨y, (figureFiveBraidCut_mem_grade_iff C hR B η u n.as y b'.val hb'.symm).2 hb⟩

private def cutProjection (u : Seq ν) : (BBim).left Z ⟶ Cut u where
  app n := AddMonoidHom.mk' (cutProjectionPiece C hR hρ B η u n)
    (fun b b' => Subtype.ext (Subtype.ext (mul_add (e u) b.val.val b'.val.val)))
  map_mem' {_ _ _} h := FigureFiveWeight.map_mem_degreeZero _ h
  map_d' _ := Subtype.ext (Subtype.ext (mul_zero _))
  map_smul' f b := Subtype.ext (Subtype.ext (mul_assoc (e u) b.val.val f.val.unop.val).symm)

private theorem cutProjection_inclusion (u : Seq ν) (n : CUp) (y : (Cut u).obj n) :
    (cutProjection C hR hρ B η u).app n (cutInclusion C hR B η u n y) = y :=
  Subtype.ext (Subtype.ext (mem_violCorner_iff.1 y.val.2).1)

private theorem cutInclusion_projection (u : Seq ν) (n : CUp) (b : (BBim).obj n Z) :
    cutInclusion C hR B η u n ((cutProjection C hR hρ B η u).app n b) =
      (BBim).ract ((lowerWeightInclusion C hR hρ u).app Z
        (figureFiveLowerWeightGenerator (Λ := Λ) C hR hρ u)) b :=
  Subtype.ext (Subtype.ext (congrArg (fun a => a * b.val.val)
    (figureFiveLowerExteriorInclusion_projection_one C hR hρ u).symm))

/-- Webster, arXiv:1309.3796v2, §6.1, proof of Proposition 6.9, Figure 5. The ordinary
categorical coend on the lower exterior projective is the loading cut. Its forward map
applies the inclusion into the source representable at zero and then co-Yoneda. Its inverse
sends a cut element `y` to `y ⊗ g`, where `g` is the projected regular unit. -/
def figureFiveBraidCoendCutIso (u : Seq ν) : Coend u ≅ Cut u :=
  FigureFiveWeight.coendSummandIso (BBim) Z (lowerWeightInclusion C hR hρ u)
    (figureFiveLowerWeightGenerator (Λ := Λ) C hR hρ u) (cutProjection C hR hρ B η u)
    (cutInclusion C hR B η u) (lowerWeightGenerator_act C hR hρ u)
    (cutProjection_inclusion C hR hρ B η u) (cutInclusion_projection C hR hρ B η u)

/-- On a pure coend tensor, evaluation is multiplication by the included lower diagram. -/
theorem figureFiveBraidCoendCutIso_hom_tmul (u : Seq ν) (n : CUp) (m : CLo)
    (b : (BBim).obj n m) (x : (NN u).obj m) :
    ((figureFiveBraidCoendCutIso (Λ := Λ) C hR hρ B η u).hom.app n
      (tmul (N := (BBim).right n) («M» := NN u) m b x)).val.val =
      ((In u) x.val).unop.val * b.val.val := by
  have h := FigureFiveWeight.coendSummandIso_hom_app_tmul (BBim) Z (lowerWeightInclusion C hR hρ u)
    (figureFiveLowerWeightGenerator (Λ := Λ) C hR hρ u) (cutProjection C hR hρ B η u)
    (cutInclusion C hR B η u) (lowerWeightGenerator_act C hR hρ u)
    (cutProjection_inclusion C hR hρ B η u) (cutInclusion_projection C hR hρ B η u) n m b x
  refine (congrArg (fun y : (Cut u).obj n => y.val.val) h).trans ?_
  change e u * (((In u) x.val).unop.val * b.val.val) = _
  rw [← mul_assoc, figureFiveLowerExteriorInclusion_fixed C hR hρ u x.val]

/-- The inverse to the multiplication map inserts the weight-zero generator. -/
theorem figureFiveBraidCoendCutIso_inv_apply (u : Seq ν) (n : CUp) (y : (Cut u).obj n) :
    (figureFiveBraidCoendCutIso (Λ := Λ) C hR hρ B η u).inv.app n y =
      tmul (N := (BBim).right n) («M» := NN u) Z (cutBraidPiece C hR B η u n y)
        (figureFiveLowerWeightGenerator (Λ := Λ) C hR hρ u) :=
  FigureFiveWeight.coendSummandIso_inv_app (BBim) Z (lowerWeightInclusion C hR hρ u)
    (figureFiveLowerWeightGenerator (Λ := Λ) C hR hρ u) (cutProjection C hR hρ B η u)
    (cutInclusion C hR B η u) (lowerWeightGenerator_act C hR hρ u)
    (cutProjection_inclusion C hR hρ B η u) (cutInclusion_projection C hR hρ B η u) n y

section ShiftedUpper
variable [Fintype I] (P : Matrix.Realization (UDot.A C) ℂ H)
  (hB : ∀ i x, B (P.root i) x = (UDot.di C i : ℂ) * x (P.coroot i))
  (hΛ : ∀ j i, η j (P.coroot i) = (Λ j i : ℂ)) (hSym : B.IsSymm)

local notation "shift" => B (η 0 - Multiset.sum (Multiset.map (Matrix.Realization.root P) ν)) (η 1)
local notation "Std" u:arg => figureFiveExteriorToCut (Λ := Λ) C hR hρ P B η hB hΛ hSym u
local notation "UpperPieces" u:arg => (fun n : ℤ => Submodule.restrictScalars ℤ
  (figureFiveUpperExteriorGrade (Λ := Λ) C hR hρ u (((n : ℂ) + c) + shift)))

include hB hΛ hSym in
private theorem shiftedUpper_smul_mem (u : Seq ν) {i j : ℤ} {a : D} {x : _}
    (ha : a ∈ UD i) (hx : x ∈ (UpperPieces u) j) : a • x ∈ (UpperPieces u) (i + j) := by
  have hx' := (figureFiveExteriorToCut_mem_grade_iff C hR hρ P B η hB hΛ hSym u ((j : ℂ) + c) x).2 hx
  have h := figureFiveBraidCut_smul_mem_grade C hR B η u ha hx'
  apply (figureFiveExteriorToCut_mem_grade_iff C hR hρ P B η hB hΛ hSym u
    (((i + j : ℤ) : ℂ) + c) (a • x)).1
  change (Std u) (a • x) ∈ _
  rw [(Std u).map_smul]
  exact h

/-- The upper exterior standardization in cochain degree zero, with the internal shift of
Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9. Its coordinate `n` is the intrinsic
upper piece in degree `(n : ℂ) + c + ⟨λ₀ − α, λ₁⟩`, where `c = 2 − ⟨λ₁, λ₀⟩`. -/
def figureFiveShiftedUpperWeightModule (u : Seq ν) : CatModule.{0} CUp :=
  FigureFiveWeight.weightModule UD (UpperPieces u)
    (fun {_ _ _ _} ha hx => shiftedUpper_smul_mem C hR hρ B η P hB hΛ hSym u ha hx)

local notation "Upper" u:arg => figureFiveShiftedUpperWeightModule (Λ := Λ) C hR hρ B η P hB hΛ hSym u

/-- The output weight coordinate reads the intrinsic upper degree after Webster's shift. -/
theorem figureFiveShiftedUpperWeightModule_obj (u : Seq ν) (n : CUp) :
    (Upper u).obj n = ↥((UpperPieces u) n.as) := rfl

/-- The upper weight module is concentrated in cochain degree zero at each internal weight. -/
theorem figureFiveShiftedUpperWeightModule_mem_grading_iff (u : Seq ν) (n : CUp) (j : ℤ) (x : (Upper u).obj n) :
    x ∈ DG.grading j ↔ j = 0 ∨ x = 0 := mem_degreeZeroGrading_iff _

private def cutUpperPieceEquiv (u : Seq ν) (n : CUp) : (Cut u).obj n ≃+ (Upper u).obj n := by
  let ev := Std u
  have h (x) : ev x ∈ (CutPieces u) n.as ↔ x ∈ (UpperPieces u) n.as :=
    figureFiveExteriorToCut_mem_grade_iff C hR hρ P B η hB hΛ hSym u ((n.as : ℂ) + c) x
  refine
    { toFun := fun y => ⟨ev.symm y.val, (h _).1 ?_⟩
      invFun := fun x => ⟨ev x.val, (h _).2 x.2⟩
      left_inv := fun y => Subtype.ext (ev.apply_symm_apply y.val)
      right_inv := fun x => Subtype.ext (ev.symm_apply_apply x.val)
      map_add' := fun y y' => Subtype.ext (ev.symm.map_add y.val y'.val) }
  rw [ev.apply_symm_apply]
  exact y.2

private def cutUpperHom (u : Seq ν) : Cut u ⟶ Upper u where
  app n := (cutUpperPieceEquiv C hR hρ B η P hB hΛ hSym u n).toAddMonoidHom
  map_mem' {_ _ _} h := FigureFiveWeight.map_mem_degreeZero _ h
  map_d' {n} _ := (cutUpperPieceEquiv C hR hρ B η P hB hΛ hSym u n).map_zero
  map_smul' f y := Subtype.ext ((Std u).symm.map_smul f.val y.val)

private def cutUpperIso (u : Seq ν) : Cut u ≅ Upper u := by
  let f := cutUpperHom C hR hρ B η P hB hΛ hSym u
  letI : IsIso f := CatModule.isIso_of_bijective f fun n =>
    (cutUpperPieceEquiv C hR hρ B η P hB hΛ hSym u n).bijective
  exact asIso f

/-- The ordinary coend comparison, followed by the inverse of the shifted Figure 5 map. -/
def figureFiveBraidCoendExteriorIso (u : Seq ν) : Coend u ≅ Upper u :=
  figureFiveBraidCoendCutIso C hR hρ B η u ≪≫ cutUpperIso C hR hρ B η P hB hΛ hSym u

/-- After the Figure 5 diagram map out of the upper standard, the coend comparison of a pure
tensor is the product of the lower inclusion and braid diagram in the violated quotient. -/
theorem figureFiveBraidCoendExteriorIso_hom_tmul (u : Seq ν) (n : CUp) (m : CLo)
    (b : (BBim).obj n m) (x : (NN u).obj m) :
    ((Std u) ((figureFiveBraidCoendExteriorIso (Λ := Λ) C hR hρ B η P hB hΛ hSym u).hom.app n
      (tmul (N := (BBim).right n) («M» := NN u) m b x)).val).val = ((In u) x.val).unop.val * b.val.val := by
  let y := (figureFiveBraidCoendCutIso (Λ := Λ) C hR hρ B η u).hom.app n
    (tmul (N := (BBim).right n) («M» := NN u) m b x)
  change ((Std u) ((Std u).symm y.val)).val = _
  exact (congrArg Subtype.val ((Std u).apply_symm_apply y.val)).trans
    (figureFiveBraidCoendCutIso_hom_tmul C hR hρ B η u n m b x)

/-- Webster, arXiv:1309.3796v2, §6.1, proof of Proposition 6.9, Figure 5. For two red
strands, the derived braid of the lower exterior projective in degree zero is the shifted
upper exterior standardization in degree zero. The comparison is in the ambient derived
categories of the two cosets; it does not assert a restriction of the functor to `D⁻` or the
reduction from more than two red strands. -/
def figureFiveBraidDerivedExteriorIso (u : Seq ν) :
    (figureFiveBraidDerivedTensor (Λ := Λ) (ν := ν) C hR B η).obj
      (CatModule.DerivedCategory.Q.obj (NN u)) ≅ CatModule.DerivedCategory.Q.obj (Upper u) :=
  figureFiveBraidDerivedTensorObjIso (Λ := Λ) C hR hρ B η u ≪≫
    CatModule.DerivedCategory.Q.mapIso (figureFiveBraidCoendExteriorIso (Λ := Λ) C hR hρ B η P hB hΛ hSym u)

end ShiftedUpper

end CoendCut

end WeightEvaluation

end Categorification.Stendhal.BraidedStendhalAlgebra
