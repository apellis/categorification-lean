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
ordinary categorical coend, without K-projectivity of the braid's output slices.
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

end WeightEvaluation

end Categorification.Stendhal.BraidedStendhalAlgebra
