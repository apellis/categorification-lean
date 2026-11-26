/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorTwoFiltrations

set_option backward.isDefEq.respectTransparency false

/-!
# Derived tensor products along a ring isomorphism

Let `φ : B ≃+* B'` be an isomorphism of rings (dg rings in degree `0`). Restricting scalars along
`φ⁻¹` carries a right `B`-module `M` and a left `B`-module `X` to modules over `B'`, and the
derived tensor products `M ⊗ᴸ_B X` and `M ⊗ᴸ_{B'} X` have the same cohomology
(`isZero_derivedTensorHomology_of_ringEquiv`).

This is used with the anti-automorphism of a braid corner, which identifies the corner with its
opposite, in B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, proof of Lemma 6.11 (step `f_n → s_n`): the derived braiding of a right
module, a derived tensor product over the opposite corner, becomes a derived tensor product over
the corner of a right module with standard filtration and a left module with reflected standard
filtration.

## Main results

* `degreeZeroDGRingHom`: a ring homomorphism as a morphism of dg rings in degree `0`.
* `isKProjective_restrictScalars_ringEquiv`: restriction of scalars along a ring isomorphism
  preserves K-projective dg modules.
* `tensorRingEquiv`: `M ⊗_B P ≅ M ⊗_{B'} P` as dg abelian groups.
* `isZero_derivedTensorHomology_of_ringEquiv`.
-/

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w

/-- A ring homomorphism of rings in degree `0`, as a morphism of dg rings. -/
def degreeZeroDGRingHom {A B : Type*} [Ring A] [Ring B] (f : A →+* B) : A →ᵈᵍ+* B where
  toRingHom := f
  map_mem' {n a} ha := by
    apply (InDegreeZero.ring_mem_grading_iff (R := B)).mpr
    rcases (InDegreeZero.ring_mem_grading_iff (R := A)).mp ha with h | h
    · exact Or.inl h
    · exact Or.inr (h ▸ f.map_zero)
  map_d' a := by
    rw [InDegreeZero.ring_d_apply, InDegreeZero.ring_d_apply]
    exact f.map_zero

variable {B B' : Type} [Ring B] [Ring B'] (φ : B ≃+* B')

local notation "RS" => RestrictScalars (degreeZeroDGRingHom φ.symm.toRingHom)

section KProjective

variable {P : Type} [AddCommGroup P] [DGAddCommGroup P] [Module B P] [DGModule B P]

/-- **Restriction of scalars along a ring isomorphism preserves K-projectivity.** -/
theorem isKProjective_restrictScalars_ringEquiv (hP : IsKProjective.{0} B P) :
    IsKProjective.{0} B' (RS P) := by
  intro N _i₁ _i₂ _i₃ _i₄ hN f
  let g : P →ᵈᵍ[B] RestrictScalars (degreeZeroDGRingHom φ.toRingHom) N :=
    { toFun := fun p => f p
      map_add' := fun x y => map_add f x y
      map_smul' := fun b p => by
        have h := f.map_smul (φ b) p
        change f (φ.symm (φ b) • p) = φ b • f p at h
        rw [φ.symm_apply_apply] at h
        exact h
      map_mem' := fun hm => f.map_mem' hm
      map_d' := fun m => f.map_d' m }
  have hg := hP (RestrictScalars (degreeZeroDGRingHom φ.toRingHom) N)
  obtain ⟨h, hh⟩ := homotopic_zero_iff_exists.mp (hg hN g)
  let h' : Cochain B' (RS P) N (-1) :=
    { toFun := fun p => h p
      map_zero' := map_zero h
      map_add' := fun x y => map_add h x y
      map_mem' := fun i m hm => h.map_mem' i m hm
      map_smul' := fun {i b'} hb x => by
        have hb' : φ.symm b' ∈ grading i := (degreeZeroDGRingHom φ.symm.toRingHom).map_mem hb
        have := h.map_smul' hb' x
        change h (φ.symm b' • (show P from x)) =
          koszulSign (-1 * i) • (φ (φ.symm b') • (show N from h x)) at this
        rw [φ.apply_symm_apply] at this
        exact this }
  refine homotopic_zero_iff_exists.mpr ⟨h', ?_⟩
  ext x
  exact congrArg (fun c => c x) hh

end KProjective

section Tensor

variable (M : Type) [AddCommGroup M] [Module Bᵐᵒᵖ M]

/-- A right `B`-module as a right `B'`-module, through `φ⁻¹`. -/
abbrev ringEquivCoefficient : ModuleCat.{0} B'ᵐᵒᵖ :=
  (ModuleCat.restrictScalars (RingHom.op φ.symm.toRingHom)).obj (ModuleCat.of Bᵐᵒᵖ M)

local notation "M'" => ringEquivCoefficient φ M

variable (Y : Type) [AddCommGroup Y] [DGAddCommGroup Y] [Module B Y] [DGModule B Y]

/-- The identity of `M`, from the `B`-coefficient to the `B'`-coefficient. -/
private def coeffId : InDegreeZero M →+ InDegreeZero M' where
  toFun m := m
  map_zero' := rfl
  map_add' _ _ := rfl

private def coeffIdInv : InDegreeZero M' →+ InDegreeZero M where
  toFun m := m
  map_zero' := rfl
  map_add' _ _ := rfl

private def moduleId : Y →+ RS Y where
  toFun p := p
  map_zero' := rfl
  map_add' _ _ := rfl

private def moduleIdInv : RS Y →+ Y where
  toFun p := p
  map_zero' := rfl
  map_add' _ _ := rfl

private def tensorRingEquivHom :
    TensorProductOver B (InDegreeZero M) Y →+ TensorProductOver B' (InDegreeZero M') (RS Y) :=
  TensorProductOver.lift
    (((TensorProductOver.tmulAddHom B' (InDegreeZero M') (RS Y)).comp (coeffId φ M)).compl₂
      (moduleId φ Y))
    fun b m p => by
      obtain ⟨b', rfl⟩ := φ.symm.surjective b
      exact TensorProductOver.op_smul_tmul (A := B') b' (coeffId φ M m) (moduleId φ Y p)

private def tensorRingEquivInv :
    TensorProductOver B' (InDegreeZero M') (RS Y) →+ TensorProductOver B (InDegreeZero M) Y :=
  TensorProductOver.lift
    (((TensorProductOver.tmulAddHom B (InDegreeZero M) Y).comp (coeffIdInv φ M)).compl₂
      (moduleIdInv φ Y))
    fun b m p =>
      TensorProductOver.op_smul_tmul (A := B) (φ.symm b) (coeffIdInv φ M m) (moduleIdInv φ Y p)

/-- **Tensor products along a ring isomorphism**: `M ⊗_B Y ≅ M ⊗_{B'} Y` as dg abelian groups,
with `B'` acting through `φ⁻¹`. -/
def tensorRingEquiv :
    DGAddEquiv (TensorProductOver B (InDegreeZero M) Y)
      (TensorProductOver B' (InDegreeZero M') (RS Y)) :=
  DGAddEquiv.ofAddMonoidHom (tensorRingEquivHom φ M Y) (tensorRingEquivInv φ M Y)
    (fun x => by
      induction x using TensorProductOver.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul m p => rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (fun x => by
      induction x using TensorProductOver.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul m p => rfl
      | add x y hx hy => rw [map_add, map_add, hx, hy])
    (fun hy => TensorProductOver.lift_mem _ _
      (fun {i j m p} hm hp => TensorProductOver.tmul_mem_grading (A := B')
        (show coeffId φ M m ∈ grading i from hm) (show moduleId φ Y p ∈ grading j from hp)) hy)
    (fun y => TensorProductOver.lift_d _ _
      (fun {i m} hm p => TensorProductOver.d_tmul_of_mem (A := B')
        (show coeffId φ M m ∈ grading i from hm) (moduleId φ Y p)) y)

end Tensor

/-- An isomorphism of dg abelian groups transports vanishing of cohomology. -/
theorem subsingleton_cohomology_of_dgAddEquiv {Z Z' : Type*} [AddCommGroup Z] [DGAddCommGroup Z]
    [AddCommGroup Z'] [DGAddCommGroup Z'] (e : DGAddEquiv Z Z') (n : ℤ)
    [Subsingleton (cohomology Z' n)] : Subsingleton (cohomology Z n) := by
  let g := cohomology.mapAddMonoidHom e.symm.toAddEquiv.toAddMonoidHom
    (fun hm => e.symm.map_mem hm) (fun m => e.symm.map_d m) n
  refine Function.Surjective.subsingleton (f := g) fun x => ?_
  induction x using cohomology.induction_on with
  | h z =>
    refine ⟨cohomology.mk Z' n (cocycles.mapAddMonoidHom e.toAddEquiv.toAddMonoidHom
      (fun hm => e.map_mem hm) (fun m => e.map_d m) n z), ?_⟩
    rw [cohomology.mapAddMonoidHom_mk]
    congr 1
    exact Subtype.ext (e.symm_apply_apply (z : Z))

section Derived

variable [HasDerivedCategory.{w, 0} ℤ] [HasDerivedCategory.{w, 0} B]
  [HasDerivedCategory.{w, 0} B'] {A : Type} [Ring A] [HasDerivedCategory.{w, 0} A]
  (M : Type) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]

omit [HasDerivedCategory.{w, 0} ℤ] [HasDerivedCategory.{w, 0} B] in
private theorem subsingleton_of_derivedTensor {R : Type} [Ring R] [HasDerivedCategory.{w, 0} R]
    {A : Type} [Ring A] [HasDerivedCategory.{w, 0} A] (N : Type) [AddCommGroup N] [Module A N]
    [Module Rᵐᵒᵖ N] [SMulCommClass A Rᵐᵒᵖ N] {P : DGModuleCat.{0} R} (hP : IsKProjective.{0} R P)
    (X : ModuleCat.{0} R) (q : P ⟶ (degreeZeroModuleFunctor R).obj X) (hq : q.hom.IsQuasiIso)
    (n : ℤ) :
    IsZero ((homologyFunctor ℤ n).obj ((derivedTensor.{w} A R N).obj
        (Q.obj ((degreeZeroModuleFunctor R).obj X)))) ↔
      Subsingleton (cohomology (TensorProductOver R (InDegreeZero N) P) n) := by
  have : IsIso (Q.map q) := (isIso_Q_map_iff q).mpr hq
  let e := (homologyFunctor ℤ n).mapIso ((derivedTensor.{w} A R N).mapIso (asIso (Q.map q)).symm ≪≫
    derivedTensorObjIso hP)
  let Z := (DGModuleCat.tensorFunctor A (InDegreeZero N)).obj P
  let c := cohomologyAddEquiv ℤ Z n
  constructor
  · intro h
    have : Subsingleton ((homologyFunctor ℤ n).obj (Q.obj Z)) :=
      ModuleCat.isZero_iff_subsingleton.mp (h.of_iso e.symm)
    exact c.injective.subsingleton
  · intro h
    have : Subsingleton (cohomology Z n) := h
    exact (ModuleCat.isZero_iff_subsingleton.mpr c.surjective.subsingleton).of_iso e

/-- **Derived tensor products along a ring isomorphism**: if `M ⊗ᴸ_{B'} X` vanishes in degree
`n`, with `B'` acting through `φ⁻¹`, then so does `M ⊗ᴸ_B X`. -/
theorem isZero_derivedTensorHomology_of_ringEquiv (X : ModuleCat.{0} B) (n : ℤ)
    (h : IsZero ((homologyFunctor ℤ n).obj ((derivedTensor.{w} ℤ B' (ringEquivCoefficient φ M)).obj
      (Q.obj ((degreeZeroModuleFunctor B').obj
        ((ModuleCat.restrictScalars φ.symm.toRingHom).obj X)))))) :
    IsZero ((homologyFunctor ℤ n).obj ((derivedTensor.{w} A B M).obj
      (Q.obj ((degreeZeroModuleFunctor B).obj X)))) := by
  let R : ProjectiveResolution X := projectiveResolution X
  let P := projectiveResolutionDGModel R
  let q := projectiveResolutionDGAugToOrdinary R
  let P' : DGModuleCat.{0} B' := DGModuleCat.of B' (RS P)
  let q' : P' ⟶ (degreeZeroModuleFunctor B').obj
      ((ModuleCat.restrictScalars φ.symm.toRingHom).obj X) := DGModuleCat.ofHom
    { toFun := fun p => q.hom p
      map_add' := fun x y => map_add q.hom x y
      map_smul' := fun b x => q.hom.map_smul (φ.symm b) x
      map_mem' := fun hm => q.hom.map_mem' hm
      map_d' := fun m => q.hom.map_d' m }
  have hq' : q'.hom.IsQuasiIso := projectiveResolutionDGAugToOrdinary_quasiIso R
  have h' := (subsingleton_of_derivedTensor (ringEquivCoefficient φ M)
    (isKProjective_restrictScalars_ringEquiv φ (projectiveResolutionDGModel_kProjective R))
    _ q' hq' n).mp h
  exact (subsingleton_of_derivedTensor M (projectiveResolutionDGModel_kProjective R) X q
    (projectiveResolutionDGAugToOrdinary_quasiIso R) n).mpr
    (subsingleton_cohomology_of_dgAddEquiv (tensorRingEquiv φ M P) n)

end Derived

end Categorification
