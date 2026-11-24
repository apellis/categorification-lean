/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightBimodule
import DG.Category.Homotopy.Shift

/-!
# Shifts of diagram weight tensors

The balanced tensor commutes with cohomological shifts when the weight
category arrows and the coefficient lie in cohomological degree zero.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG DGOpposite
open scoped DG.DegreeZero CatModule

universe u v w

section Coend

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DGAddCommGroup (X ⟶ Y)] [DGCategory C]
  (j : ℤ) (N : CatModule.{w} (DGOpposite C)) (M : CatModule.{w} C)

variable (htw : ∀ {X Y : C} (f : X ⟶ Y), CatModule.twist j f = f)

private def weightTensorShiftFamily (X : C) :
    N.obj (op X) →+ (CatModule.shift j M).obj X →+ Shift j (CatTensorProduct N M) :=
  ((CatTensorProduct.tmulAddHom N M X).compl₂ (Shift.unmk j).toAddMonoidHom).compr₂
    (Shift.mk j).toAddMonoidHom

private theorem weightTensorShiftFamily_apply (X : C) (x : N.obj (op X))
    (m : (CatModule.shift j M).obj X) :
    weightTensorShiftFamily j N M X x m =
      Shift.mk j (M := CatTensorProduct N M) (CatTensorProduct.tmul (N := N) (M := M) X x
        (Shift.unmk j (M := M.obj X) m)) := rfl

include htw in
private theorem weightTensorShiftFamily_balanced :
    CatTensorProduct.Balanced (weightTensorShiftFamily j N M) := by
  intro X Y f x m
  have h₀ := CatModule.shift.unmk_smul_eq (M := M) (n := j) f m
  have hu : Shift.unmk j (M := M.obj Y) (f • m) =
      f • Shift.unmk j (M := M.obj X) m := h₀.trans
    (congrArg (fun g : X ⟶ Y => g • Shift.unmk j (M := M.obj X) m) (htw f))
  simp only [weightTensorShiftFamily_apply, hu]
  exact congrArg (Shift.mk j (M := CatTensorProduct N M))
    (CatTensorProduct.ract_tmul (N := N) (M := M) f x (Shift.unmk j (M := M.obj X) m))

/-- Move a shift on the left weight module through a balanced tensor. -/
def weightTensorShiftHom :
    CatTensorProduct N (CatModule.shift j M) →+ Shift j (CatTensorProduct N M) :=
  CatTensorProduct.lift _ (weightTensorShiftFamily_balanced j N M htw)

private def weightTensorUnshiftFamily (X : C) :
    N.obj (op X) →+ M.obj X →+ CatTensorProduct N (CatModule.shift j M) :=
  (CatTensorProduct.tmulAddHom N (CatModule.shift j M) X).compl₂ (Shift.mk j).toAddMonoidHom

private theorem weightTensorUnshiftFamily_apply (X : C) (x : N.obj (op X)) (m : M.obj X) :
    weightTensorUnshiftFamily j N M X x m =
      CatTensorProduct.tmul (N := N) (M := CatModule.shift j M) X x (Shift.mk j (M := M.obj X) m) := rfl

include htw in
private theorem weightTensorUnshiftFamily_balanced :
    CatTensorProduct.Balanced (weightTensorUnshiftFamily j N M) := by
  intro X Y f x m
  have h₀ := CatModule.shift.smul_mk_eq (M := M) (n := j) f m
  have hm : f • (CatModule.shift.mk (M := M) j m) = CatModule.shift.mk (M := M) j (f • m) :=
    h₀.trans (congrArg (fun g : X ⟶ Y => CatModule.shift.mk (M := M) j (g • m)) (htw f))
  simp only [weightTensorUnshiftFamily_apply]
  exact (CatTensorProduct.ract_tmul (N := N) (M := CatModule.shift j M) f x
    (CatModule.shift.mk (M := M) j m)).trans
      (congrArg (CatTensorProduct.tmul (N := N) (M := CatModule.shift j M) Y x) hm)

/-- Inverse to the shift map on the underlying balanced tensor. -/
def weightTensorUnshiftHom :
    Shift j (CatTensorProduct N M) →+ CatTensorProduct N (CatModule.shift j M) :=
  (CatTensorProduct.lift _ (weightTensorUnshiftFamily_balanced j N M htw)).comp
    (Shift.unmk j).toAddMonoidHom

theorem weightTensorShiftHom_tmul (X : C) (x : N.obj (op X)) (m : (CatModule.shift j M).obj X) :
    weightTensorShiftHom j N M htw (CatTensorProduct.tmul (N := N) (M := CatModule.shift j M) X x m) =
      Shift.mk j (M := CatTensorProduct N M) (CatTensorProduct.tmul (N := N) (M := M) X x
        (Shift.unmk j (M := M.obj X) m)) :=
  (CatTensorProduct.lift_tmul (weightTensorShiftFamily j N M)
    (weightTensorShiftFamily_balanced j N M htw) X x m).trans
      (weightTensorShiftFamily_apply j N M X x m)

private theorem weightTensorUnshiftHom_mk_tmul (X : C) (x : N.obj (op X)) (m : M.obj X) :
    weightTensorUnshiftHom j N M htw
        (Shift.mk j (M := CatTensorProduct N M) (CatTensorProduct.tmul (N := N) (M := M) X x m)) =
      CatTensorProduct.tmul (N := N) (M := CatModule.shift j M) X x (Shift.mk j (M := M.obj X) m) := by
  change CatTensorProduct.lift _ (weightTensorUnshiftFamily_balanced j N M htw)
    (Shift.unmk j (Shift.mk j (CatTensorProduct.tmul X x m))) = _
  rw [Shift.unmk_mk]
  exact CatTensorProduct.lift_tmul _ _ X x m

/-- The underlying additive equivalence moving a shift through a weight coend. -/
def weightTensorShiftAddEquiv :
    CatTensorProduct N (CatModule.shift j M) ≃+ Shift j (CatTensorProduct N M) := by
  let f := weightTensorShiftHom j N M htw
  let g := weightTensorUnshiftHom j N M htw
  have hleft : g.comp f = AddMonoidHom.id _ := by
    apply CatTensorProduct.addHom_ext
    intro X x m
    change g (f (CatTensorProduct.tmul X x m)) = CatTensorProduct.tmul X x m
    exact (congrArg g (weightTensorShiftHom_tmul j N M htw X x m)).trans
      ((weightTensorUnshiftHom_mk_tmul j N M htw X x (Shift.unmk j m)).trans
        (congrArg (CatTensorProduct.tmul X x) (Shift.mk_unmk (n := j) m)))
  let m := (Shift.mk j : CatTensorProduct N M ≃+ _)
  have hright : (f.comp g).comp m.toAddMonoidHom = m.toAddMonoidHom := by
    apply CatTensorProduct.addHom_ext
    intro X y z
    change f (g (Shift.mk j (CatTensorProduct.tmul X y z))) = Shift.mk j (CatTensorProduct.tmul X y z)
    exact (congrArg f (weightTensorUnshiftHom_mk_tmul j N M htw X y z)).trans
      ((weightTensorShiftHom_tmul j N M htw X y (Shift.mk j z)).trans
        (congrArg (fun m => Shift.mk j (CatTensorProduct.tmul X y m)) (Shift.unmk_mk (n := j) z)))
  have hl (z : CatTensorProduct N (CatModule.shift j M)) : g (f z) = z := by
    have h := DFunLike.congr_fun hleft z
    exact h
  have hr (z : Shift j (CatTensorProduct N M)) : f (g z) = z := by
    have eq : m (m.symm z) = z := m.apply_symm_apply z
    have h : f (g (m (m.symm z))) = m (m.symm z) := DFunLike.congr_fun hright (m.symm z)
    exact (congrArg (fun y => f (g y)) eq).symm.trans (h.trans eq)
  exact { toFun := f, invFun := g, map_add' := f.map_add, left_inv := hl, right_inv := hr }

private theorem weightTensorShiftHom_mem {k : ℤ}
    {x : CatTensorProduct N (CatModule.shift j M)} (hx : x ∈ DG.grading k) :
    weightTensorShiftHom j N M htw x ∈ DG.grading k := by
  refine CatTensorProduct.lift_mem (weightTensorShiftFamily j N M)
    (weightTensorShiftFamily_balanced j N M htw) ?_ hx
  intro X a b z m hz hm
  rw [weightTensorShiftFamily_apply]
  have hm' : Shift.unmk j (M := M.obj X) m ∈ DG.grading (b + j) :=
    CatModule.shift.unmk_mem_grading (M := M) (n := j) hm
  have ht := CatTensorProduct.tmul_mem_grading (N := N) (M := M) hz hm'
  have hs := Shift.mk_mem_grading (n := j) ht
  rwa [← add_assoc, add_sub_cancel_right] at hs

private theorem weightTensorShiftHom_d
    (hdeg : ∀ (X : C) {i : ℤ} {x : N.obj (op X)}, x ∈ DG.grading i → i = 0 ∨ x = 0)
    (hd : ∀ (X : C) (x : N.obj (op X)), d x = 0)
    (x : CatTensorProduct N (CatModule.shift j M)) :
    weightTensorShiftHom j N M htw (d x) = d (weightTensorShiftHom j N M htw x) := by
  refine CatTensorProduct.lift_d (weightTensorShiftFamily j N M)
    (weightTensorShiftFamily_balanced j N M htw) ?_ x
  intro X i z hz m
  rcases hdeg X hz with rfl | rfl
  · let e := Shift.mk j (M := CatTensorProduct N M)
    let tm := CatTensorProduct.tmulAddHom N M X z
    let y := CatModule.shift.unmk (M := M) j m
    have hdy : CatModule.shift.unmk (M := M) j (d m) = koszulSign j • d y :=
      CatModule.shift.unmk_d m
    have hdz : d (tm y) = tm (d y) := by
      change d (CatTensorProduct.tmul (N := N) (M := M) X z y) =
        CatTensorProduct.tmul (N := N) (M := M) X z (d y)
      rw [CatTensorProduct.d_tmul_of_mem X hz, hd X z, CatTensorProduct.zero_tmul, zero_add,
        koszulSign_zero, one_smul]
    simp only [hd X z, map_zero, AddMonoidHom.zero_apply, zero_add, koszulSign_zero, one_smul,
      weightTensorShiftFamily_apply]
    have hpow : tm (koszulSign j • d y) = koszulSign j • tm (d y) :=
      map_units_zsmul tm (koszulSign j) (d y)
    exact (Shift.d_mk (n := j) (tm y)).trans
      (congrArg e ((congrArg (fun q => koszulSign j • q) hdz).trans
        (hpow.symm.trans (congrArg tm hdy.symm))))
  · simp only [map_zero, AddMonoidHom.zero_apply, smul_zero, add_zero]

/-- A coefficient concentrated in degree zero commutes with shifts in the weight coend. -/
def weightTensorShiftDGEquiv
    (hdeg : ∀ (X : C) {i : ℤ} {x : N.obj (op X)}, x ∈ DG.grading i → i = 0 ∨ x = 0)
    (hd : ∀ (X : C) (x : N.obj (op X)), d x = 0) :
    DGAddEquiv (CatTensorProduct N (CatModule.shift j M)) (Shift j (CatTensorProduct N M)) where
  toAddEquiv := weightTensorShiftAddEquiv j N M htw
  map_mem' := fun hx => weightTensorShiftHom_mem j N M htw hx
  map_d' := weightTensorShiftHom_d j N M htw hdeg hd

end Coend

variable {B : Type u} [Ring B] [InternalGrading B] [BigradedDGRing B]
local notation "C" => WeightCategory B

private theorem weight_twist_eq (j : ℤ) {X Y : C} (f : X ⟶ Y) :
    CatModule.twist j f = f := by
  have h : f ∈ DG.grading (0 : ℤ) := WeightCategory.mem_grading_iff.mpr
    (InDegreeZero.ring_mem_grading_zero f.val)
  rw [CatModule.twist_of_mem h, mul_zero, koszulSign_zero, one_smul]

section DiagramTensor

open MulOpposite

variable {A P : Type u} [Ring A] [InternalGrading A] [BigradedDGRing A]
  [AddCommGroup P] [Module A P] [Module Bᵐᵒᵖ P] [SMulCommClass A Bᵐᵒᵖ P]
  (G : ℤ → AddSubgroup P)
  (hl : ∀ {i j : ℤ} {a : A} {x : P}, a ∈ wgrading i → x ∈ G j → a • x ∈ G (i+j))
  (hr : ∀ {i j : ℤ} {b : B} {x : P}, b ∈ wgrading i → x ∈ G j → MulOpposite.op b • x ∈ G (j+i))

local notation "D" => diagramWeightBimodule G hl hr

/-- The graded diagram tensor commutes with cohomological shifts on dg modules. -/
def diagramWeightTensorShiftIso (L : CatModule.{u} (WeightCategory B)) (k : ℤ) :
    (D).tensorObj (CatModule.shift k L) ≅ CatModule.shift k ((D).tensorObj L) := by
  let ρ (X : WeightCategory A) := weightTensorShiftDGEquiv k ((D).right X) L (weight_twist_eq k)
    (fun Y {_} {_} h => (InDegreeZero.mem_grading_iff (M := G (X.as - Y.as))).mp h)
    (fun Y x => InDegreeZero.d_apply (G (X.as - Y.as)) x)
  refine CatModule.isoMk (fun X => (ρ X).toAddEquiv) ?_ ?_ ?_
  · intro X n x
    exact ⟨fun hx => (ρ X).symm_apply_apply x ▸ (ρ X).symm.map_mem hx,
      fun hx => (ρ X).map_mem hx⟩
  · intro X x
    exact (ρ X).map_d x
  · intro X Y f x
    change (ρ Y) ((D).tensorAct (CatModule.shift k L) f x) =
      Shift.mk k ((D).tensorAct L (CatModule.twist k f) (Shift.unmk k ((ρ X) x)))
    rw [weight_twist_eq]
    induction x using CatTensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul T b m =>
      have h := CatBimodule.tensorAct_tmul (B := D) (CatModule.shift k L) f T b m
      refine (congrArg (ρ Y) h).trans ?_
      change weightTensorShiftHom k ((D).right Y) L (weight_twist_eq k) (CatTensorProduct.tmul T ((D).lact f b) m) =
        Shift.mk k ((D).tensorAct L f (Shift.unmk k
          (weightTensorShiftHom k ((D).right X) L (weight_twist_eq k) (CatTensorProduct.tmul T b m))))
      rw [weightTensorShiftHom_tmul, weightTensorShiftHom_tmul, Shift.unmk_mk,
        CatBimodule.tensorAct_tmul]
    | add x y hx hy =>
      rw [map_add, map_add, map_add, map_add, map_add, hx, hy, map_add]

/-- The shift comparison is natural in the dg module being tensored. -/
def diagramWeightTensorShiftNatIso (k : ℤ) :
    shiftFunctor (CatModule.{u} (WeightCategory B)) k ⋙ (D).tensorFunctor ≅
      (D).tensorFunctor ⋙ shiftFunctor (CatModule.{u} (WeightCategory A)) k :=
  NatIso.ofComponents (fun L => diagramWeightTensorShiftIso G hl hr L k) (by
    intro L L' f
    apply CatModule.Hom.ext
    intro X x
    let J := (D).right X
    let l := ((D).tensorMap (CatModule.shiftMap k f)).app X
    let r := (CatModule.shiftMap k ((D).tensorMap f)).app X
    have eq : (weightTensorShiftHom k J L' (weight_twist_eq k)).comp l = r.comp (weightTensorShiftHom k J L (weight_twist_eq k)) := by
      apply CatTensorProduct.addHom_ext
      intro Y b y
      change weightTensorShiftHom k J L' (weight_twist_eq k) (l (CatTensorProduct.tmul Y b y)) =
        r (weightTensorShiftHom k J L (weight_twist_eq k) (CatTensorProduct.tmul Y b y))
      have h₁ := CatBimodule.tensorMap_tmul (D) (CatModule.shiftMap k f) X Y b y
      have h₂ := CatBimodule.tensorMap_tmul (D) f X Y b (Shift.unmk k y)
      refine (congrArg (weightTensorShiftHom k J L' (weight_twist_eq k)) h₁).trans ?_
      rw [weightTensorShiftHom_tmul, weightTensorShiftHom_tmul]
      change Shift.mk k (CatTensorProduct.tmul Y b (f.app Y (Shift.unmk k y))) =
        r (Shift.mk k (CatTensorProduct.tmul Y b (Shift.unmk k y)))
      exact (congrArg (Shift.mk k) h₂).symm
    exact DFunLike.congr_fun eq x)

theorem diagramWeightTensorShiftNatIso_hom_tmul (k : ℤ)
    (L : CatModule.{u} (WeightCategory B)) (X : WeightCategory A) (Y : WeightCategory B)
    (x : (D).obj X Y) (y : (CatModule.shift k L).obj Y) :
    ((diagramWeightTensorShiftNatIso G hl hr k).hom.app L).app X (CatTensorProduct.tmul (N := (D).right X) Y x y) =
      Shift.mk k (CatTensorProduct.tmul (N := (D).right X) (M := L) Y x
        (Shift.unmk k (M := L.obj Y) y)) :=
  weightTensorShiftHom_tmul k ((D).right X) L (weight_twist_eq k) Y x y

/-- The shift isomorphisms respect zero and addition of cohomological degrees. -/
instance diagramWeightTensor_commShift : (D).tensorFunctor.CommShift ℤ where
  commShiftIso := diagramWeightTensorShiftNatIso G hl hr
  commShiftIso_zero := by
    apply Iso.ext
    apply NatTrans.ext
    funext L
    apply CatModule.Hom.ext
    intro X x
    let f := ((diagramWeightTensorShiftNatIso G hl hr 0).hom.app L).app X
    let g := ((Functor.CommShift.isoZero (D).tensorFunctor ℤ).hom.app L).app X
    have eq : f = g := by
      apply CatTensorProduct.addHom_ext
      intro Y b y
      change f (CatTensorProduct.tmul Y b y) = g (CatTensorProduct.tmul Y b y)
      refine (diagramWeightTensorShiftNatIso_hom_tmul G hl hr 0 L X Y b y).trans ?_
      dsimp only [g]
      rw [Functor.CommShift.isoZero_hom_app]
      let p := CatTensorProduct.tmul (N := (D).right X) (M := CatModule.shift 0 L) Y b y
      let a := ((D).tensorFunctor.map ((shiftFunctorZero (CatModule (WeightCategory B)) ℤ).hom.app L))
      let b₀ := ((shiftFunctorZero (CatModule (WeightCategory A)) ℤ).inv.app ((D).tensorObj L))
      have h₁ := CatModule.comp_app a b₀ X p
      have h₂ := CatModule.shiftFunctorZero_inv_app_app ((D).tensorObj L) (a.app X p)
      have h₃ := CatBimodule.tensorMap_tmul (D) (CatModule.shiftZeroIso L).hom X Y b y
      exact (h₁.trans (h₂.trans
        (congrArg (Shift.mk 0 (M := ((D).tensorObj L).obj X)) h₃))).symm
    exact DFunLike.congr_fun eq x
  commShiftIso_add := by
    intro a b
    apply Iso.ext
    apply NatTrans.ext
    funext L
    apply CatModule.Hom.ext
    intro X x
    let f := ((diagramWeightTensorShiftNatIso G hl hr (a+b)).hom.app L).app X
    let g := ((Functor.CommShift.isoAdd (diagramWeightTensorShiftNatIso G hl hr a)
      (diagramWeightTensorShiftNatIso G hl hr b)).hom.app L).app X
    have eq : f = g := by
      apply CatTensorProduct.addHom_ext
      intro Y z y
      change f (CatTensorProduct.tmul Y z y) = g (CatTensorProduct.tmul Y z y)
      dsimp only [g]
      rw [Functor.CommShift.isoAdd_hom_app]
      let A₀ := (D).tensorObj L
      let q := CatTensorProduct.tmul (N := (D).right X) (M := CatModule.shift (a+b) L) Y z y
      let v := Shift.unmk (a+b) (M := L.obj Y) y
      let w : A₀.obj X := CatTensorProduct.tmul (N := (D).right X) (M := L) Y z v
      let r₁ := (shiftFunctorAdd (CatModule (WeightCategory B)) a b).hom.app L
      let h₁ := (D).tensorMap r₁
      let h₂ := (diagramWeightTensorShiftNatIso G hl hr b).hom.app (CatModule.shift a L)
      let h₃ := CatModule.shiftMap b ((diagramWeightTensorShiftNatIso G hl hr a).hom.app L)
      let h₄ := (shiftFunctorAdd (CatModule (WeightCategory A)) a b).inv.app A₀
      have hc₁ := CatModule.comp_app h₁ (h₂ ≫ h₃ ≫ h₄) X q
      have hc₂ := CatModule.comp_app h₂ (h₃ ≫ h₄) X (h₁.app X q)
      have hc₃ := CatModule.comp_app h₃ h₄ X (h₂.app X (h₁.app X q))
      have hc := hc₁.trans (hc₂.trans hc₃)
      have e₁ := CatBimodule.tensorMap_tmul (D) r₁ X Y z y
      have er₁ : r₁.app Y y = Shift.mk b (M := (CatModule.shift a L).obj Y)
          (Shift.mk a (M := L.obj Y) v) := by
        exact CatModule.shiftFunctorAdd'_hom_app_app a b (a+b) rfl L y
      let y₁ := Shift.mk a (M := L.obj Y) v
      let y₂ := Shift.mk b (M := (CatModule.shift a L).obj Y) y₁
      let t := CatTensorProduct.tmul (N := (D).right X) (M := CatModule.shift a L) Y z y₁
      let t₂ := Shift.mk b (M := ((D).tensorObj (CatModule.shift a L)).obj X) t
      let w₁ : (CatModule.shift a A₀).obj X := CatModule.shift.mk (M := A₀) (X := X) a w
      let w₂ : (CatModule.shift b (CatModule.shift a A₀)).obj X :=
        CatModule.shift.mk (M := CatModule.shift a A₀) (X := X) b w₁
      have e₁' : h₁.app X q = CatTensorProduct.tmul
          (N := (D).right X) (M := CatModule.shift b (CatModule.shift a L)) Y z y₂ :=
        e₁.trans (congrArg (CatTensorProduct.tmul (N := (D).right X)
          (M := CatModule.shift b (CatModule.shift a L)) Y z) er₁)
      have e₂ := diagramWeightTensorShiftNatIso_hom_tmul G hl hr b (CatModule.shift a L) X Y z y₂
      have e₂' : h₂.app X (CatTensorProduct.tmul
          (N := (D).right X) (M := CatModule.shift b (CatModule.shift a L)) Y z y₂) = t₂ :=
        e₂.trans (congrArg (fun y₀ => Shift.mk b (M := ((D).tensorObj (CatModule.shift a L)).obj X)
          (CatTensorProduct.tmul (N := (D).right X) (M := CatModule.shift a L) Y z y₀))
          (Shift.unmk_mk (n := b) y₁))
      have e₃ := CatModule.shiftMap_app_mk (n := b) ((diagramWeightTensorShiftNatIso G hl hr a).hom.app L) t
      have ea : ((diagramWeightTensorShiftNatIso G hl hr a).hom.app L).app X t = w₁ :=
        (diagramWeightTensorShiftNatIso_hom_tmul G hl hr a L X Y z y₁).trans
          (congrArg (fun y₀ => Shift.mk a (M := A₀.obj X)
            (CatTensorProduct.tmul (N := (D).right X) (M := L) Y z y₀)) (Shift.unmk_mk (n := a) v))
      have e₃' : h₃.app X t₂ = w₂ := e₃.trans
        (congrArg (Shift.mk b (M := (CatModule.shift a A₀).obj X)) ea)
      have e₄ : h₄.app X w₂ = Shift.mk (a+b) (M := A₀.obj X) w :=
        CatModule.shiftFunctorAdd'_inv_app_app a b (a+b) rfl A₀ (X := X) w₂
      have hc' : (h₁ ≫ h₂ ≫ h₃ ≫ h₄).app X q = Shift.mk (a+b) (M := A₀.obj X) w :=
        hc.trans ((congrArg (fun t₀ => h₄.app X (h₃.app X (h₂.app X t₀))) e₁').trans
          ((congrArg (fun t₀ => h₄.app X (h₃.app X t₀)) e₂').trans
            ((congrArg (h₄.app X) e₃').trans e₄)))
      exact (diagramWeightTensorShiftNatIso_hom_tmul G hl hr (a+b) L X Y z y).trans hc'.symm
    exact DFunLike.congr_fun eq x


variable [CatModule.HasDerivedCategory.{v,u} (WeightCategory A)]
  [CatModule.HasDerivedCategory.{v,u} (WeightCategory B)]

/-- The homotopy tensor is induced by the dg module tensor. -/
def diagramWeightTensorHomotopyFactors :
    CatModule.HomotopyCategory.quotient (WeightCategory B) ⋙ diagramWeightTensorHomotopy G hl hr ≅
      (D).tensorFunctor ⋙ CatModule.HomotopyCategory.quotient (WeightCategory A) :=
  CategoryTheory.Quotient.lift.isLift _ _ _

instance diagramWeightTensorHomotopy_commShift : (diagramWeightTensorHomotopy G hl hr).CommShift ℤ :=
  CategoryTheory.Quotient.liftCommShift ((D).tensorFunctor ⋙
      CatModule.HomotopyCategory.quotient (WeightCategory A))
    (CatModule.homotopic.{u} (WeightCategory B)) ℤ _

instance : NatTrans.CommShift (diagramWeightTensorHomotopyFactors G hl hr).hom ℤ :=
  CategoryTheory.Quotient.liftCommShift_compatibility ((D).tensorFunctor ⋙
      CatModule.HomotopyCategory.quotient (WeightCategory A))
    (CatModule.homotopic.{u} (WeightCategory B)) ℤ _

end DiagramTensor

end Categorification
