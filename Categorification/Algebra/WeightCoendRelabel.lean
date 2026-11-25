/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Category.Tensor.Bimodule
import Categorification.Algebra.WeightCoendReindex
import Categorification.Algebra.DiagramWeightRingEquiv

/-!
# Relabelling both diagram rings in a balanced tensor product

For the second crossing in Webster, arXiv:1309.3796v2, §7.2 before
Definition 7.12, the simultaneous permutation of the red labels acts on
the two corner rings and the off-diagonal coefficient.
-/
noncomputable section
namespace Categorification
open CategoryTheory DG DGOpposite
open scoped DG.DegreeZero CatModule
universe u
variable {A B A' B' : Type u} [Ring A] [Ring B] [Ring A'] [Ring B']
  [InternalGrading A] [InternalGrading B] [InternalGrading A'] [InternalGrading B']
  [BigradedDGRing A] [BigradedDGRing B] [BigradedDGRing A'] [BigradedDGRing B']
  (a : A ≃+* A') (b : B ≃+* B')
  (ha : ∀ {i : ℤ} (x : A), a x ∈ wgrading i ↔ x ∈ wgrading i)
  (hb : ∀ {i : ℤ} (x : B), b x ∈ wgrading i ↔ x ∈ wgrading i)
local notation "W" R:arg => WeightCategory R
local notation "FA" => weightFunctorOfRingEquiv a ha
local notation "FB" => weightFunctorOfRingEquiv b hb

variable (D : CatBimodule.{u} (W A) (W B)) (D' : CatBimodule.{u} (W A') (W B'))
  (ρ : ∀ (X : W A) (Y : W B), DGAddEquiv (D.obj X Y) (D'.obj ⟨X.as⟩ ⟨Y.as⟩))
  (right : ∀ {X : W A} {Y Z : W B} (f : Y ⟶ Z) (x : D.obj X Z), ρ X Y (D.ract f x) =
    D'.ract ((weightFunctorOfRingEquiv b hb).map f) (ρ X Z x))
  (left : ∀ {X X' : W A} {Y : W B} (f : X ⟶ X') (x : D.obj X Y), ρ X' Y (D.lact f x) =
    D'.lact ((weightFunctorOfRingEquiv a ha).map f) (ρ X Y x))
  (M : CatModule.{u} (W B'))

private def weightRelabel (R S : Type u) : W R ≃ W S where
  toFun X := ⟨X.as⟩
  invFun X := ⟨X.as⟩
  left_inv _ := rfl
  right_inv _ := rfl

local notation "E" => weightRelabel B B'
local notation "M₀" => Functor.obj (CatModule.precomp FB) M
private def weightHomRelabel (Y Z : W B) : (Y ⟶ Z) ≃ ((E) Y ⟶ (E) Z) :=
  Equiv.ofBijective (fun f => (FB).map f) ⟨(FB).map_injective,(FB).map_surjective⟩

local notation "re" X:arg => fun Y => DGAddEquiv.toAddEquiv (ρ X Y)
private abbrev unchangedFiber (Y : W B) : (M₀).obj Y ≃+ M.obj ((E) Y) := AddEquiv.refl _

include right in
private theorem relabelRight (X : W A) {Y Z : W B} (f : Y ⟶ Z) (v : D.obj X Z) :
    ρ X Y ((D.right X).ract f v) =
      (D'.right ((FA).obj X)).ract (weightHomRelabel b hb Y Z f) (ρ X Z v) := by
  exact (congrArg (ρ X Y) (CatBimodule.right_ract (B := D) X f v)).trans
    ((right f v).trans (CatBimodule.right_ract (B := D') ((FA).obj X) ((FB).map f) (ρ X Z v)).symm)

local notation "rcompat" X:arg => relabelRight a b ha hb D D' ρ right X
local notation "same" => unchangedFiber b hb M
private def relabelComponent (X : W A) :
    DGAddEquiv (CatTensorProduct (D.right X) M₀) (CatTensorProduct (D'.right ((FA).obj X)) M) :=
  weightCoendReindexDGEquiv (D.right X) M₀ (D'.right ((FA).obj X)) M E (re X) same
    (weightHomRelabel b hb) (rcompat X) (fun _ _ => rfl)
    (fun Y {_} {_} hg => (ρ X Y).map_mem hg) (fun _ {_} {_} h => h)
    (fun Y z => (ρ X Y).map_d z) (fun _ _ => rfl)

local notation "cmp" X:arg => relabelComponent a b ha hb D D' ρ right M X
private theorem relabelComponent_tmul (X : W A) (Y : W B) (p : D.obj X Y) (m : (M₀).obj Y) :
    (cmp X) (CatTensorProduct.tmul (N := D.right X) (M := M₀) Y p m) =
      CatTensorProduct.tmul (N := D'.right ((FA).obj X)) (M := M) ((E) Y) (ρ X Y p) ((same Y) m) :=
  weightCoendReindexAddEquiv_tmul (D.right X) M₀ (D'.right ((FA).obj X)) M E (re X) same
    (weightHomRelabel b hb) (rcompat X) (fun _ _ => rfl) Y p m

include ρ right left in
/-- Simultaneous relabelling of the two weight rings carries the tensor
over the source ring to the restriction of the tensor over the target. -/
def weightCoendRelabelIso :
    D.tensorObj M₀ ≅ (CatModule.precomp FA).obj (D'.tensorObj M) := by
  refine CatModule.isoMk (fun X => (cmp X).toAddEquiv) ?_ ?_ ?_
  · intro X i z
    exact ⟨fun h => (cmp X).symm_apply_apply z ▸ (cmp X).symm.map_mem h, (cmp X).map_mem⟩
  · intro X z
    exact (cmp X).map_d z
  · intro X X' f z
    have h : (cmp X').toAddEquiv.toAddMonoidHom.comp (D.tensorAct M₀ f) =
        (D'.tensorAct M ((FA).map f)).comp (cmp X).toAddEquiv.toAddMonoidHom := by
      apply CatTensorProduct.addHom_ext
      intro Y p m
      change (cmp X') (D.tensorAct M₀ f (CatTensorProduct.tmul Y p m)) =
        D'.tensorAct M ((FA).map f) ((cmp X) (CatTensorProduct.tmul Y p m))
      let sf := (FA).map f
      refine (congrArg (cmp X') (CatBimodule.tensorAct_tmul (B := D) M₀ f Y p m)).trans ?_
      refine (relabelComponent_tmul a b ha hb D D' ρ right M X' Y (D.lact f p) m).trans ?_
      refine Eq.trans ?_ ((congrArg (D'.tensorAct M sf)
        (relabelComponent_tmul a b ha hb D D' ρ right M X Y p m)).symm)
      exact (congrArg (fun t => CatTensorProduct.tmul (N := D'.right ((FA).obj X')) (M := M)
        ((E) Y) t ((same Y) m)) (left f p)).trans
        (CatBimodule.tensorAct_tmul (B := D') M sf ((E) Y) (ρ X Y p) ((same Y) m)).symm
    exact DFunLike.congr_fun h z

end Categorification
