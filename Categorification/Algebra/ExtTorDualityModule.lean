/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ExtTorDuality
import Categorification.Algebra.DerivedTensorTwoFiltrations

/-!
# Ext–Tor duality for ordinary modules

For an ordinary left `R`-module `X` and a right `R`-module `L` over a field `k`, a morphism
`X → L^*⟦n⟧` in `D(R)`, `L^* = HOM_k(L, k)`, vanishes as soon as `Tor_{-n}(L, X)`, the degree
`-n` homology of `L ⊗ᴸ_R X`, vanishes (`hom_dualModule_shift_eq_zero_of_isZero`). The proof
resolves `X` by projectives and applies the vanishing form of Ext–Tor duality to the resolution.

It is the form used for Webster, arXiv:1309.3796v3, Theorem 6.15: the higher Ext between the
tilting modules `𝔅_τ P` vanish because the higher Tor between standardly filtered modules do.
-/

namespace Categorification

open CategoryTheory CategoryTheory.Limits DG DG.DegreeZero DG.DerivedCategory

noncomputable section

open scoped DG.DGModule.HOM.LeftAction

section Vanishing

variable {k : Type} [Field k] {R : Type} [Ring R] (L : Type) [AddCommGroup L] [Module k L]
  [Module Rᵐᵒᵖ L] [SMulCommClass k Rᵐᵒᵖ L] [DG.HasDerivedCategory.{0, 0} R]
  [DG.HasDerivedCategory.{0, 0} ℤ]

/-- **Ext–Tor duality for an ordinary module**: if the degree `-n` homology of
`L ⊗ᴸ_R X` vanishes, every morphism `X → L^*⟦n⟧` in `D(R)` is zero, `L^* = HOM_k(L, k)`. -/
theorem hom_dualModule_shift_eq_zero_of_isZero (X : ModuleCat.{0} R) (n : ℤ)
    (hT : IsZero ((homologyFunctor ℤ (-n)).obj ((derivedTensor.{0} ℤ R
      (ModuleCat.of Rᵐᵒᵖ L)).obj (Q.obj ((degreeZeroModuleFunctor R).obj X)))))
    (f : Q.obj ((degreeZeroModuleFunctor R).obj X) ⟶
      (Q.obj (dualModule (k := k) L))⟦n⟧) : f = 0 := by
  let P := projectiveResolution X
  have hP := projectiveResolutionDGModel_kProjective (R := R) P
  have : IsIso (Q.map (projectiveResolutionDGAugToOrdinary P)) :=
    (isIso_Q_map_iff _).mpr (projectiveResolutionDGAugToOrdinary_quasiIso P)
  let I₀ := asIso (Q.map (projectiveResolutionDGAugToOrdinary P))
  let I : Q.obj (projectiveResolutionDGModel P) ≅ Q.obj ((degreeZeroModuleFunctor R).obj X) := I₀
  have hT' := hT.of_iso ((homologyFunctor ℤ (-n)).mapIso
      ((derivedTensorObjIso hP).symm ≪≫ (derivedTensor.{0} ℤ R (ModuleCat.of Rᵐᵒᵖ L)).mapIso I))
  have : Subsingleton (cohomology (TensorProductOver R (InDegreeZero L)
      (projectiveResolutionDGModel P)) (-n)) :=
    (cohomologyAddEquiv ℤ _ (-n)).subsingleton_congr.2
      (ModuleCat.subsingleton_of_isZero hT')
  have h0 := hom_dualModule_shift_eq_zero (k := k) L hP n (I.hom ≫ f)
  rw [show f = I.inv ≫ (I.hom ≫ f) by simp, h0, comp_zero]

end Vanishing

section DegreeZeroDual

variable {k : Type} [Field k] {R : Type} [Ring R] (L : Type) [AddCommGroup L] [Module k L]
  [Module Rᵐᵒᵖ L] [SMulCommClass k Rᵐᵒᵖ L]

variable (k) in
/-- The `k`-dual of a right `R`-module, a left `R`-module by `(r φ)(l) = φ(l r)`. -/
def RightDual : Type := Module.Dual k L

instance : AddCommGroup (RightDual k L) := inferInstanceAs (AddCommGroup (Module.Dual k L))

instance : Module k (RightDual k L) := inferInstanceAs (Module k (Module.Dual k L))

variable {L} in
/-- An element of `RightDual k L` as a functional. -/
def RightDual.toDual (φ : RightDual k L) : Module.Dual k L := φ

variable (k R) in
/-- Right multiplication by `r` on `L`, as a `k`-linear map. -/
def opSmulLin (r : R) : L →ₗ[k] L where
  toFun l := MulOpposite.op r • l
  map_add' := smul_add _
  map_smul' c l := (smul_comm c (MulOpposite.op r) l).symm

variable (k R) in
/-- The action of `R` on the dual of a right `R`-module. -/
def rightDualRingHom : R →+* Module.End k (Module.Dual k L) where
  toFun r := (opSmulLin k R L r).dualMap
  map_one' := LinearMap.ext fun φ => LinearMap.ext fun m => by
    simp [opSmulLin, LinearMap.dualMap_apply]
  map_mul' r₁ r₂ := LinearMap.ext fun φ => LinearMap.ext fun m => by
    simp [opSmulLin, LinearMap.dualMap_apply, mul_smul]
  map_zero' := LinearMap.ext fun φ => LinearMap.ext fun m => by
    simp [opSmulLin, LinearMap.dualMap_apply]
  map_add' r₁ r₂ := LinearMap.ext fun φ => LinearMap.ext fun m => by
    simp [opSmulLin, LinearMap.dualMap_apply, add_smul]

instance : Module R (RightDual k L) :=
  (Module.compHom (Module.Dual k L) (rightDualRingHom k R L) : Module R (Module.Dual k L))

theorem rightDual_smul_apply (r : R) (φ : RightDual k L) (l : L) :
    (RightDual.toDual (r • φ)) l = RightDual.toDual φ (MulOpposite.op r • l) := rfl

instance : SMulCommClass R k (RightDual k L) where
  smul_comm _ _ _ := LinearMap.ext fun _ => rfl

/-- A cochain of nonzero degree between modules concentrated in degree zero vanishes. -/
theorem cochain_eq_zero_of_ne {n : ℤ} (hn : n ≠ 0) (z : Cochain k (InDegreeZero L) k n) :
    z = 0 := Cochain.ext fun y => by
  have hy : y ∈ grading (M := InDegreeZero L) 0 := (InDegreeZero.mem_grading_iff _).2 (Or.inl rfl)
  have := (mem_grading_iff (R := k)).1 (z.map_mem hy)
  rcases this with h | h
  · omega
  · exact h

/-- The degree-zero cochain of a functional. -/
def dualCochain (φ : Module.Dual k L) : Cochain k (InDegreeZero L) k 0 where
  toFun y := φ (InDegreeZero.equiv L y)
  map_zero' := map_zero φ
  map_add' y y' := map_add φ _ _
  map_mem' i y hy := by
    rcases (InDegreeZero.mem_grading_iff _).1 hy with rfl | rfl
    · exact (mem_grading_iff (R := k)).2 (Or.inl rfl)
    · exact (mem_grading_iff (R := k)).2 (Or.inr (map_zero φ))
  map_smul' {i a} ha y := by
    rcases (mem_grading_iff (R := k)).1 ha with rfl | rfl
    · simp only [mul_zero, koszulSign_zero, one_smul]
      exact map_smul φ a _
    · simp

theorem dualCochain_apply (φ : Module.Dual k L) (y : InDegreeZero L) :
    dualCochain L φ y = φ (InDegreeZero.equiv L y) := rfl

/-- The degree-zero component of `HOM_k(L, k)`, as a functional. -/
def cochainDual (z : Cochain k (InDegreeZero L) k 0) : Module.Dual k L where
  toFun l := z ((InDegreeZero.equiv L).symm l)
  map_add' l l' := map_add z _ _
  map_smul' c l := by
    have := z.map_smul (mem_grading_zero_field c) ((InDegreeZero.equiv L).symm l)
    change z (c • (InDegreeZero.equiv L).symm l) = c • z _
    simpa using this

open scoped DG.DGModule.HOM.LeftAction

/-- **The dual of a module in degree zero**: `HOM_k(L, k) ≅ L^*` as dg `R`-modules, with `L^*`
in degree zero. -/
def rightDualDGEquiv :
    InDegreeZero (RightDual k L) ≃ᵈᵍ[R] DGModule.HOM k (InDegreeZero L) k where
  toFun φ := DirectSum.of _ 0 (dualCochain L (InDegreeZero.equiv _ φ).toDual)
  invFun x := (InDegreeZero.equiv _).symm (cochainDual L (x 0))
  left_inv φ := by
    simp only [DirectSum.of_eq_same]
    rfl
  right_inv x := by
    refine DFinsupp.ext fun n => ?_
    by_cases hn : n = 0
    · subst hn
      simp only [DirectSum.of_eq_same]
      exact Cochain.ext fun y => rfl
    · exact (cochain_eq_zero_of_ne L hn _).trans (cochain_eq_zero_of_ne L hn _).symm
  map_add' φ φ' := by
    rw [← map_add]
    rfl
  map_smul' r φ := by
    simp only [RingHom.id_apply]
    refine DFinsupp.ext fun n => ?_
    by_cases hn : n = 0
    · subst hn
      have hr : r ∈ grading (M := R) 0 := InDegreeZero.ring_mem_grading_iff.2 (Or.inl rfl)
      refine Cochain.ext fun y => ?_
      have hy : y ∈ grading (M := InDegreeZero L) 0 :=
        (InDegreeZero.mem_grading_iff _).2 (Or.inl rfl)
      have h := DGModule.HOM.LeftAction.smul_of_apply (A := k) hr
        (dualCochain L (InDegreeZero.equiv _ φ).toDual) hy
      simp only [mul_zero, add_zero, koszulSign_zero, one_smul] at h
      simp only [DirectSum.of_eq_same]
      exact h.symm
    · exact (cochain_eq_zero_of_ne L hn _).trans (cochain_eq_zero_of_ne L hn _).symm
  map_mem' {n φ} hφ := by
    rcases (InDegreeZero.mem_grading_iff _).1 hφ with rfl | rfl
    · exact of_mem_summand _ _
    · rw [show dualCochain L (InDegreeZero.equiv _ (0 : InDegreeZero (RightDual k L))).toDual = 0
        from Cochain.ext fun y => rfl, map_zero]
      exact zero_mem _
  map_d' φ := by
    rw [InDegreeZero.d_apply, DGModule.HOM.d_of,
      cochain_eq_zero_of_ne L (n := 0 + 1) (by omega) (δ 0 (0 + 1) _)]
    rw [show dualCochain L (InDegreeZero.equiv _ (0 : InDegreeZero (RightDual k L))).toDual = 0
        from Cochain.ext fun y => rfl, map_zero, map_zero]

end DegreeZeroDual

section RightDualVanishing

variable {k : Type} [Field k] {R : Type} [Ring R] (L : Type) [AddCommGroup L] [Module k L]
  [Module Rᵐᵒᵖ L] [SMulCommClass k Rᵐᵒᵖ L] [DG.HasDerivedCategory.{0, 0} R]
  [DG.HasDerivedCategory.{0, 0} ℤ]

/-- **Ext–Tor duality, ordinary form**: if `Tor_{-n}(L, X)` vanishes, every morphism
`X → L^*⟦n⟧` in `D(R)` is zero, `L^* = Hom_k(L, k)` the dual module in degree zero. -/
theorem hom_rightDual_shift_eq_zero_of_isZero (X : ModuleCat.{0} R) (n : ℤ)
    (hT : IsZero ((homologyFunctor ℤ (-n)).obj ((derivedTensor.{0} ℤ R
      (ModuleCat.of Rᵐᵒᵖ L)).obj (Q.obj ((degreeZeroModuleFunctor R).obj X)))))
    (f : Q.obj ((degreeZeroModuleFunctor R).obj X) ⟶
      (Q.obj ((degreeZeroModuleFunctor R).obj (ModuleCat.of R (RightDual k L))))⟦n⟧) :
    f = 0 := by
  let e : (degreeZeroModuleFunctor R).obj (ModuleCat.of R (RightDual k L)) ≅
      dualModule (k := k) L := DGModuleCat.isoOfDGModuleEquiv (rightDualDGEquiv L)
  have h0 := hom_dualModule_shift_eq_zero_of_isZero (k := k) L X n hT
    (f ≫ (shiftFunctor _ n).map (Q.map e.hom))
  have : f = (f ≫ (shiftFunctor _ n).map (Q.map e.hom)) ≫ (shiftFunctor _ n).map (Q.map e.inv) := by
    rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [this, h0, zero_comp]

end RightDualVanishing

end

end Categorification
