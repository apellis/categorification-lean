/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Derived.DegreeZeroHomology
import Categorification.Algebra.DerivedTensor
import Categorification.Algebra.DerivedTensorFiltration

/-!
# Ordinary tensor as degree-zero derived tensor

The connective-resolution comparison over the chosen scalar ring
identifies the degree-zero derived tensor of ordinary modules with the
ordinary balanced tensor. The comparison respects the right tensor map
of each ordinary module homomorphism.
-/


open CategoryTheory

open scoped DG.DegreeZero DG.DGModuleCat.Algebra

noncomputable section

namespace DG.DerivedCategory

universe w u

variable {k : Type u} [CommRing k] [HasDerivedCategory.{w,u} k]

private def scalarDegreeZeroCohomologyEquiv (M : DGModuleCat.{u} k)
    (hM : ∀ x : M, x ∈ grading 0) (hd : ∀ x : M, d x = 0) :
    M ≃ₗ[k] cohomology M 0 := by
  let incl : M →+ cocycles M 0 := (AddMonoidHom.id M).codRestrict _
    (fun x => mem_cocycles.mpr ⟨hM x, hd x⟩)
  let f : M →ₗ[k] cohomology M 0 :=
    { toFun := fun x => cohomology.mk M 0 (incl x)
      map_add' := fun x y => ((cohomology.mk M 0).comp incl).map_add x y
      map_smul' := fun r x => by
        change cohomology.mkOf (hM (r • x)) (hd (r • x)) = r • cohomology.mkOf (hM x) (hd x)
        exact (cohomology.groundModule_smul_mkOf (R := k) k r (hM x) (hd x)).symm }
  apply LinearEquiv.ofBijective f
  constructor
  · apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    have hx' : cohomology.mk M 0 (incl x) = 0 := hx
    obtain ⟨z, hz, hz'⟩ := mem_coboundaries.mp ((cohomology.mk_eq_zero_iff _).mp hx')
    change d z = x at hz'
    rw [hd] at hz'
    exact hz'.symm
  · intro x
    obtain ⟨z, rfl⟩ := cohomology.mk_surjective M 0 x
    exact ⟨z.1, rfl⟩

/-- The degree-zero homology comparison is linear over the ground field. -/
def scalarDegreeZeroHomologyQEquiv (M : DGModuleCat.{u} k)
    (hM : ∀ x : M, x ∈ grading 0) (hd : ∀ x : M, d x = 0) :
    M ≃ₗ[k] (homologyFunctor k 0).obj (Q.obj M) :=
  (scalarDegreeZeroCohomologyEquiv M hM hd).trans
    ((homologyFunctorFactors k 0).app M).symm.toLinearEquiv

/-- The degree-zero linear comparison is natural in a diagram module map. -/
theorem scalarDegreeZeroHomologyQEquiv_naturality {M N : DGModuleCat.{u} k} (f : M ⟶ N)
    (hM : ∀ x : M, x ∈ grading 0) (hdM : ∀ x : M, d x = 0)
    (hN : ∀ x : N, x ∈ grading 0) (hdN : ∀ x : N, d x = 0) (x : M) :
    (homologyFunctor k 0).map (Q.map f) (scalarDegreeZeroHomologyQEquiv M hM hdM x) =
      scalarDegreeZeroHomologyQEquiv N hN hdN (f x) := by
  let e := homologyFunctorFactors (A := k) k 0
  change (e.inv.app M ≫ (Q ⋙ homologyFunctor k 0).map f)
      (scalarDegreeZeroCohomologyEquiv M hM hdM x) =
    e.inv.app N (scalarDegreeZeroCohomologyEquiv N hN hdN (f x))
  rw [← e.inv.naturality f]
  rfl

end DG.DerivedCategory

namespace Categorification

open CategoryTheory DG DG.DerivedCategory TensorProductOver MulOpposite
open scoped DG.DegreeZero

noncomputable section

universe w u

variable {k A N : Type u} [CommRing k] [Ring A]
  [AddCommGroup N] [Module k N] [Module Aᵐᵒᵖ N] [SMulCommClass k Aᵐᵒᵖ N]
  [HasDerivedCategory.{w,u} k] [HasDerivedCategory.{w,u} A]

private abbrev ambientH0 {X : Type u} [AddCommGroup X] [Module A X] :=
  (homologyFunctor k 0).obj ((derivedTensor k A N).obj
    (Q.obj (DGModuleCat.of A (InDegreeZero X))))

private def ordinaryH0Equiv {X : Type u} [AddCommGroup X] [Module A X] :
    TensorProductOver A N X ≃ₗ[k] (homologyFunctor k 0).obj
      (Q.obj ((DGModuleCat.tensorFunctor k (InDegreeZero N)).obj
        (DGModuleCat.of A (InDegreeZero X)))) :=
  scalarDegreeZeroHomologyQEquiv
    ((DGModuleCat.tensorFunctor (B := A) k (InDegreeZero N)).obj
      (DGModuleCat.of A (InDegreeZero X)))
    (TensorProductOver.mem_grading_zero_inDegreeZero (B := A) (M := N) (N := X))
    (TensorProductOver.d_inDegreeZero (B := A) (M := N) (N := X))

/-- The degree-zero ambient derived tensor is its ordinary tensor, linearly
over the ground ring. -/
def ambientDerivedTensorH0Equiv (X : Type u) [AddCommGroup X] [Module A X] :
    ambientH0 (k := k) (A := A) (N := N) (X := X) ≃ₗ[k] TensorProductOver A N X :=
  (derivedTensorHomologyIsoOrdinaryLinear (R := k) (A := k) (B := A) (M := N) X).toLinearEquiv.trans
    (ordinaryH0Equiv (k := k) (A := A) (N := N) (X := X)).symm

/-- The degree-zero derived tensor map induced by an ordinary module map. -/
abbrev ambientH0Map {X Y : Type u} [AddCommGroup X] [AddCommGroup Y] [Module A X] [Module A Y]
    (f : X →ₗ[A] Y) :=
  (homologyFunctor k 0).map ((derivedTensor k A N).map
    (Q.map ((degreeZeroModuleFunctor A).map (ModuleCat.ofHom f))))

/-- The degree-zero comparison identifies a derived module map with ordinary right tensor. -/
theorem ambientH0Map_naturality {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module A Y] (f : X →ₗ[A] Y) (z : TensorProductOver A N X) :
    (ambientDerivedTensorH0Equiv (k := k) (A := A) (N := N) Y)
      ((ambientH0Map (k := k) (A := A) (N := N) f)
        ((ambientDerivedTensorH0Equiv (k := k) (A := A) (N := N) X).symm z)) =
      TensorProductOver.map LinearMap.id f z := by
  let zd := ((degreeZeroModuleFunctor A).map (ModuleCat.ofHom f))
  let t := DGModuleCat.tensorFunctor (B := A) k (InDegreeZero N)
  let tX := t.obj (DGModuleCat.of A (InDegreeZero X))
  let tY := t.obj (DGModuleCat.of A (InDegreeZero Y))
  let dX := derivedTensorHomologyIsoOrdinaryLinear (R := k) (A := k) (B := A) (M := N) X
  let dY := derivedTensorHomologyIsoOrdinaryLinear (R := k) (A := k) (B := A) (M := N) Y
  let oX := ordinaryH0Equiv (k := k) (A := A) (N := N) (X := X)
  let oY := ordinaryH0Equiv (k := k) (A := A) (N := N) (X := Y)
  have hact : t.map zd z = TensorProductOver.map LinearMap.id f z := by
    induction z using TensorProductOver.induction_on with
    | zero => exact ((t.map zd).hom.map_zero).trans (map_zero _).symm
    | tmul m x => rfl
    | add x y hx hy =>
        exact ((t.map zd).hom.map_add x y).trans
          ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
  have hnat := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
      (derivedTensorHomologyIsoOrdinaryLinear_naturality (R := k) (A := k) (M := N) zd))
    (dX.inv (oX z))
  have hzero : (homologyFunctor k 0).map (Q.map (t.map zd)) (oX z) = oY (t.map zd z) :=
    scalarDegreeZeroHomologyQEquiv_naturality (M := tX) (N := tY) (t.map zd)
      (TensorProductOver.mem_grading_zero_inDegreeZero (B := A) (M := N) (N := X))
      (TensorProductOver.d_inDegreeZero (B := A) (M := N) (N := X))
      (TensorProductOver.mem_grading_zero_inDegreeZero (B := A) (M := N) (N := Y))
      (TensorProductOver.d_inDegreeZero (B := A) (M := N) (N := Y)) z
  have h₀ : dX.hom (dX.inv (oX z)) = oX z :=
    dX.toLinearEquiv.apply_symm_apply (oX z)
  change dY.hom (ambientH0Map (k := k) (A := A) (N := N) f (dX.inv (oX z))) =
    (homologyFunctor k 0).map (Q.map (t.map zd)) (dX.hom (dX.inv (oX z))) at hnat
  change oY.symm (dY.hom (ambientH0Map (k := k) (A := A) (N := N) f (dX.inv (oX z)))) = _
  have hh := hnat.trans ((congrArg ((homologyFunctor k 0).map (Q.map (t.map zd))) h₀).trans
    (hzero.trans (congrArg oY hact)))
  exact (congrArg oY.symm hh).trans (oY.symm_apply_apply _)

/-- Ordinary right-tensor maps induced by a surjection are surjective after
taking the ambient degree-zero homology identification. -/
theorem ambientH0Map_surjective {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module A Y] (f : X →ₗ[A] Y) (hf : Function.Surjective f) :
    Function.Surjective (ambientH0Map (k := k) (A := A) (N := N) f) := by
  let eX := ambientDerivedTensorH0Equiv (k := k) (A := A) (N := N) X
  let eY := ambientDerivedTensorH0Equiv (k := k) (A := A) (N := N) Y
  have hs : Function.Surjective
      (TensorProductOver.map (LinearMap.id : N →ₗ[Aᵐᵒᵖ] N) f) := by
    intro z
    induction z using TensorProductOver.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul m y =>
      obtain ⟨x, rfl⟩ := hf y
      exact ⟨TensorProductOver.tmul A m x, rfl⟩
    | add y z hy hz =>
      obtain ⟨v, rfl⟩ := hy
      obtain ⟨w, rfl⟩ := hz
      exact ⟨v + w, map_add _ _ _⟩
  intro y
  obtain ⟨x, hx⟩ := hs (eY y)
  refine ⟨eX.symm x, eY.injective ?_⟩
  exact (ambientH0Map_naturality (k := k) (N := N) f x).trans hx

end

end Categorification
