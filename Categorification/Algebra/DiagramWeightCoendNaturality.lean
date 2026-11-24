/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightCoend

/-!
# Naturality of multiplication over a weight category

A right weight arrow acts as a dg map on the left module of a fixed
source weight. A homogeneous product that commutes with both outer
actions yields a natural map of these left-module families.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe u

variable {B C N : Type u} [Ring B] [Ring C]
  [InternalGrading B] [InternalGrading C] [BigradedDGRing B] [BigradedDGRing C]
  [AddCommGroup N] [Module B N] [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
  (H : ℤ → AddSubgroup N)
  (hL : ∀ {i j : ℤ} {b : B} {x : N}, b ∈ wgrading i → x ∈ H j → b • x ∈ H (i + j))
  (hR : ∀ {i j : ℤ} {c : C} {x : N}, c ∈ wgrading i → x ∈ H j → op c • x ∈ H (j + i))

local notation "D" => diagramWeightBimodule H hL hR

/-- A morphism in the right weight category acts by a map of left dg weight modules. -/
def diagramWeightRightMap {Z Z' : WeightCategory C} (g : Z ⟶ Z') : (D).left Z' ⟶ (D).left Z where
  app X := (D).ract g
  map_mem' hx := by
    have hg : g ∈ DG.grading (0 : ℤ) := WeightCategory.mem_grading_iff.mpr
      (InDegreeZero.ring_mem_grading_zero g.val)
    have h := (D).ract_mem' hg hx
    rw [add_zero] at h
    exact h
  map_d' {_X} x := by
    have hx : d x = 0 := InDegreeZero.d_apply (H (_X.as - Z'.as)) x
    have hgx : d ((D).ract g x) = 0 := InDegreeZero.d_apply (H (_X.as - Z.as)) _
    exact ((congrArg (fun y => (D).ract g y) hx).trans (map_zero ((D).ract g))).trans hgx.symm
  map_smul' f x := ((D).lact_ract' f g x).symm

/-- View the source-weight components as a family of left dg modules. -/
def diagramWeightLeftFunctor : (WeightCategory C)ᵒᵖ ⥤ CatModule (WeightCategory B) where
  obj Z := (D).left Z.unop
  map g := diagramWeightRightMap H hL hR g.unop
  map_id Z := CatModule.Hom.ext fun X x => (D).ract_id' X Z.unop x
  map_comp f g := CatModule.Hom.ext fun _ x => (D).ract_comp' g.unop f.unop x

end Categorification

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.DegreeZero

universe u

variable {A B C M N P : Type u} [Ring A] [Ring B] [Ring C]
  [InternalGrading A] [InternalGrading B] [InternalGrading C]
  [BigradedDGRing A] [BigradedDGRing B] [BigradedDGRing C]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [Module B N] [Module Cᵐᵒᵖ N] [SMulCommClass B Cᵐᵒᵖ N]
  (G : ℤ → AddSubgroup M) (H : ℤ → AddSubgroup N) (L : ℤ → AddSubgroup P)
  (hgL : ∀ {i j : ℤ} {a : A} {x : M}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i + j))
  (hgR : ∀ {i j : ℤ} {b : B} {x : M}, b ∈ wgrading i → x ∈ G j → op b • x ∈ G (j + i))
  (hhL : ∀ {i j : ℤ} {b : B} {y : N}, b ∈ wgrading i → y ∈ H j → b • y ∈ H (i + j))
  (hhR : ∀ {i j : ℤ} {c : C} {y : N}, c ∈ wgrading i → y ∈ H j → op c • y ∈ H (j + i))
  (β : M →+ N →+ P)
  (hw : ∀ {i j : ℤ} {x : M} {y : N}, x ∈ G i → y ∈ H j → β x y ∈ L (i + j))
  (hb : ∀ (b : B) (x : M) (y : N), β (op b • x) y = β x (b • y))
  (Z : WeightCategory C)

local notation "D₁" => diagramWeightBimodule G hgL hgR
local notation "D₂" => diagramWeightBimodule H hhL hhR
variable [Module A P] [Module Cᵐᵒᵖ P] [SMulCommClass A Cᵐᵒᵖ P]
  (hPL : ∀ {i j : ℤ} {a : A} {x : P}, a ∈ wgrading i → x ∈ L j → a • x ∈ L (i + j))
  (hPR : ∀ {i j : ℤ} {c : C} {x : P}, c ∈ wgrading i → x ∈ L j → op c • x ∈ L (j + i))
  (hβL : ∀ (a : A) (x : M) (y : N), β (a • x) y = a • β x y)

local notation "D₃" => diagramWeightBimodule L hPL hPR
local notation "prod" => diagramWeightCoendProductHom G H L hgL hgR hhL hhR β hw hb
local notation "F" => diagramWeightCoendProduct G H L hgL hgR hhL hhR β hw hb

/-- A homogeneous product respecting the outer right action is natural in
the source weight. -/
theorem diagramWeightCoendProductHom_natural {Z' : WeightCategory C} (g : Z ⟶ Z')
    (hβR : ∀ (c : C) (x : M) (y : N), β x (op c • y) = op c • β x y) :
    (D₁).tensorMap (diagramWeightRightMap H hhL hhR g) ≫ prod Z hPL hPR hβL =
      prod Z' hPL hPR hβL ≫ diagramWeightRightMap L hPL hPR g := by
  apply CatModule.Hom.ext
  intro X t
  let m := (D₁).tensorMap (diagramWeightRightMap H hhL hhR g)
  let r := diagramWeightRightMap L hPL hPR g
  have he : (F X Z).comp (m.app X) = (r.app X).comp (F X Z') := by
    apply CatTensorProduct.addHom_ext
    intro Y x y
    change (F X Z) (m.app X (CatTensorProduct.tmul Y x y)) =
      r.app X ((F X Z') (CatTensorProduct.tmul Y x y))
    have hm : m.app X (CatTensorProduct.tmul Y x y) =
        CatTensorProduct.tmul Y x ((D₂).ract g y) :=
      CatBimodule.tensorMap_tmul (D₁) (diagramWeightRightMap H hhL hhR g) X Y x y
    refine (congrArg (F X Z) hm).trans (Subtype.ext ?_)
    exact (diagramWeightCoendProduct_tmul G H L hgL hgR hhL hhR β hw hb X Z Y x
      ((D₂).ract g y)).trans ((hβR g.val x.val y.val).trans
      (congrArg (fun z : P => op g.val • z)
        (diagramWeightCoendProduct_tmul G H L hgL hgR hhL hhR β hw hb X Z' Y x y)).symm)
  exact DFunLike.congr_fun he t

/-- The coend product is natural throughout the family of left dg modules. -/
def diagramWeightCoendProductNatTrans
    (hβR : ∀ (c : C) (x : M) (y : N), β x (op c • y) = op c • β x y) :
    diagramWeightLeftFunctor H hhL hhR ⋙ (D₁).tensorFunctor ⟶
      diagramWeightLeftFunctor L hPL hPR where
  app Z := prod Z.unop hPL hPR hβL
  naturality := by
    intro U V f
    exact diagramWeightCoendProductHom_natural G H L hgL hgR hhL hhR β hw hb
      V.unop hPL hPR hβL f.unop hβR

/-- Bijective weight products identify the two families as dg module functors. -/
def diagramWeightCoendProductNatIso
    (hβR : ∀ (c : C) (x : M) (y : N), β x (op c • y) = op c • β x y)
    (hbij : ∀ X Z, Function.Bijective (F X Z)) :
    diagramWeightLeftFunctor H hhL hhR ⋙ (D₁).tensorFunctor ≅
      diagramWeightLeftFunctor L hPL hPR :=
  by
    let τ := diagramWeightCoendProductNatTrans G H L hgL hgR hhL hhR β hw hb hPL hPR hβL hβR
    refine NatIso.ofComponents (fun Z => ?_) ?_
    · have h : IsIso (τ.app Z) := CatModule.isIso_of_bijective _ (fun X => hbij X Z.unop)
      exact @asIso _ _ _ _ (τ.app Z) h
    · intro U V f
      exact τ.naturality f

end Categorification
