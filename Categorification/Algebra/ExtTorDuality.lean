/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensor
import DG.Derived.ConnectedK0
import DG.Module.HomShiftIso
import DG.Module.HomTensor
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Duals of acyclic complexes over a field

Over a field `k`, the dual `HOM_k(Y, k)` of a dg `k`-module `Y` has `Hⁿ(HOM_k(Y, k)) = 0`
whenever `H⁻ⁿ(Y) = 0` (`subsingleton_cohomology_HOM_field`). This is the vanishing half of
`Hⁿ(HOM_k(Y, k)) ≅ H⁻ⁿ(Y)^*`: a cocycle `z` of degree `n` is a functional on `Y⁻ⁿ` vanishing on
the boundaries; it vanishes on the cycles, hence factors through `d : Y⁻ⁿ → Y¹⁻ⁿ`, and an
extension of the induced functional on `d(Y⁻ⁿ)` to `Y¹⁻ⁿ` is a cochain `g` with `δ g = z`.

It is the input of the Ext–Tor duality used for Webster, arXiv:1309.3796v3, Theorem 6.15
(the higher Ext between tilting modules vanish).
-/

universe u

namespace Categorification

open DG DG.DegreeZero DirectSum CategoryTheory

noncomputable section

section FieldDual

variable {k : Type u} [Field k] {Y : Type u} [AddCommGroup Y] [DGAddCommGroup Y] [Module k Y]
  [DGModule k Y]

theorem mem_grading_zero_field (c : k) : c ∈ grading (M := k) 0 :=
  (mem_grading_iff (R := k)).2 (Or.inl rfl)

theorem smul_mem_grading_field (c : k) {j : ℤ} {y : Y} (hy : y ∈ grading j) :
    c • y ∈ grading j := by
  simpa using smul_mem_grading (A := k) (mem_grading_zero_field c) hy

variable (k Y) in
/-- The projection onto the homogeneous component of degree `j`, as a `k`-linear map. -/
def gradeProj (j : ℤ) : Y →ₗ[k] Y where
  toFun y := (decompose (grading (M := Y)) y j : Y)
  map_add' y y' := by simp only [decompose_add, DirectSum.add_apply, AddSubgroup.coe_add]
  map_smul' c y := by
    have := decompose_map (k := 0) ({ toFun := (c • ·), map_zero' := smul_zero c, map_add' := smul_add c } : Y →+ Y)
      (fun {n m} hm => by rw [add_zero]; exact smul_mem_grading_field c hm) y j
    rw [add_zero] at this
    simpa using this

theorem gradeProj_of_mem {j : ℤ} {y : Y} (hy : y ∈ grading j) : gradeProj k Y j y = y :=
  decompose_of_mem_same _ hy

theorem gradeProj_of_mem_ne {i j : ℤ} {y : Y} (hy : y ∈ grading i) (h : i ≠ j) :
    gradeProj k Y j y = 0 :=
  decompose_of_mem_ne _ hy h

theorem gradeProj_mem (j : ℤ) (y : Y) : gradeProj k Y j y ∈ grading j :=
  (decompose (grading (M := Y)) y j).2

theorem gradeProj_d (j : ℤ) (y : Y) : gradeProj k Y (j + 1) (d y) = d (gradeProj k Y j y) :=
  decompose_d y j

/-- A cochain of degree `n` with values in `k` only sees the component of degree `-n`. -/
theorem cochain_apply_gradeProj {n : ℤ} (z : Cochain k Y k n) (y : Y) :
    z y = z (gradeProj k Y (-n) y) := by
  induction y using DG.induction_on with
  | h_zero => simp
  | @h_homogeneous i y =>
    by_cases hi : i = -n
    · subst hi
      rw [gradeProj_of_mem y.2]
    · rw [gradeProj_of_mem_ne y.2 hi, map_zero]
      exact ((mem_grading_iff (R := k)).1 (z.map_mem y.2)).resolve_left (by omega)
  | h_add y y' hy hy' => rw [map_add, hy, hy', map_add, map_add]

/-- A cochain with values in `k`, as a `k`-linear map. -/
def cochainLinear {n : ℤ} (z : Cochain k Y k n) : Y →ₗ[k] k where
  toFun := z
  map_add' := map_add z
  map_smul' c y := by
    have := z.map_smul (mem_grading_zero_field c) y
    simpa using this

/-- If `H⁻ⁿ(Y) = 0`, every cocycle of degree `n` of `HOM_k(Y, k)` is a coboundary. -/
theorem exists_δ_eq_of_exact {n : ℤ}
    (h : ∀ y ∈ grading (M := Y) (-n), d y = 0 → ∃ x ∈ grading (M := Y) (-n - 1), d x = y)
    (z : Cochain k Y k n) (hz : δ n (n + 1) z = 0) :
    ∃ g : Cochain k Y k (n - 1), δ (n - 1) n g = z := by
  let S := DGModule.gradingSubmodule k k Y (-n)
  let D : S →ₗ[k] Y := DGModule.dLinear k k Y ∘ₗ S.subtype
  have hzd : ∀ x : Y, z (d x) = 0 := fun x => by
    have := congrArg (fun c => c x) hz
    simp only [δ_apply n (n + 1) rfl, Cochain.zero_apply, DG.DegreeZero.d_apply, zero_sub,
      neg_eq_zero] at this
    exact (koszulSign n).isUnit.smul_eq_zero.1 this
  have hker : LinearMap.ker D ≤ LinearMap.ker (cochainLinear z ∘ₗ S.subtype) := by
    intro y hy
    obtain ⟨x, -, hxy⟩ := h y y.2 hy
    change z y = 0
    rw [← hxy, hzd]
  let ψ₀ : LinearMap.range D →ₗ[k] k :=
    (LinearMap.ker D).liftQ (cochainLinear z ∘ₗ S.subtype) hker ∘ₗ
      (D.quotKerEquivRange).symm.toLinearMap
  have hψ₀ : ∀ y : S, ψ₀ ⟨D y, LinearMap.mem_range_self D y⟩ = z y := fun y => by
    simp only [ψ₀, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [show (⟨D y, LinearMap.mem_range_self D y⟩ : LinearMap.range D) =
      D.quotKerEquivRange (Submodule.Quotient.mk y) from rfl, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend ψ₀
  let gl : Y →ₗ[k] k := koszulSign n • (ψ ∘ₗ gradeProj k Y (1 - n))
  have hgl : ∀ y, gl y = koszulSign n • ψ (gradeProj k Y (1 - n) y) := fun _ => rfl
  let g : Cochain k Y k (n - 1) :=
    { toFun := gl
      map_zero' := map_zero gl
      map_add' := map_add gl
      map_mem' := fun i y hy => by
        by_cases hi : i = 1 - n
        · exact (mem_grading_iff (R := k)).2 (Or.inl (by omega))
        · rw [hgl, gradeProj_of_mem_ne hy hi, map_zero, smul_zero]
          exact zero_mem _
      map_smul' := fun {i a} ha y => by
        rcases (mem_grading_iff (R := k)).1 ha with rfl | rfl
        · simp only [mul_zero, koszulSign, Int.negOnePow_zero, one_smul]
          exact gl.map_smul a y
        · simp }
  refine ⟨g, Cochain.ext fun y => ?_⟩
  rw [δ_apply (n - 1) n (by omega)]
  change d (gl y) - koszulSign (n - 1) • gl (d y) = z y
  rw [DG.DegreeZero.d_apply, zero_sub, hgl, show (1 - n) = -n + 1 by omega, gradeProj_d,
    cochain_apply_gradeProj z y]
  have e : ψ (d (gradeProj k Y (-n) y)) = z (gradeProj k Y (-n) y) := by
    have := congrArg (fun f => f ⟨D ⟨_, gradeProj_mem (k := k) (-n) y⟩,
      LinearMap.mem_range_self D _⟩) hψ
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    rw [hψ₀] at this
    exact this
  have hs : koszulSign (n - 1) * koszulSign n = -1 := by
    rw [koszulSign, koszulSign, ← Int.negOnePow_add, show n - 1 + n = 2 * n - 1 by omega,
      Int.negOnePow_sub, Int.negOnePow_one, Int.negOnePow_two_mul, mul_neg, mul_one]
  rw [e, smul_smul, hs, Units.neg_smul, one_smul, neg_neg]

/-- **Duals of acyclic complexes over a field**: if `H⁻ⁿ(Y) = 0` then
`Hⁿ(HOM_k(Y, k)) = 0`. -/
theorem subsingleton_cohomology_HOM_field {n : ℤ} [Subsingleton (cohomology Y (-n))] :
    Subsingleton (cohomology (DGModule.HOM k Y k) n) := by
  have h : ∀ y ∈ grading (M := Y) (-n), d y = 0 → ∃ x ∈ grading (M := Y) (-n - 1), d x = y :=
    fun y hy hdy => (cohomology.mk_eq_zero_iff (M := Y) (n := -n) ⟨y, hy, hdy⟩).1
      (Subsingleton.elim _ _)
  refine ⟨fun a b => ?_⟩
  suffices ∀ a : cohomology (DGModule.HOM k Y k) n, a = 0 by rw [this a, this b]
  intro a
  induction a using cohomology.induction_on with
  | h x =>
    rw [cohomology.mk_eq_zero_iff]
    obtain ⟨⟨z, hz'⟩, hd⟩ := x.2
    have hd : d (DirectSum.of (fun n => Cochain k Y k n) n z) = 0 := by rw [hz']; exact hd
    rw [DGModule.HOM.d_of] at hd
    rw [← hz']
    have hz : δ n (n + 1) z = 0 := DirectSum.of_injective (β := fun n => Cochain k Y k n) _
      (by rw [hd, map_zero])
    obtain ⟨g, hg⟩ := exists_δ_eq_of_exact h z hz
    refine ⟨DirectSum.of _ (n - 1) g, of_mem_summand _ _, ?_⟩
    rw [DGModule.HOM.d_of, ← hg]
    exact DGModule.HOM.of_congr (by omega) fun y => by rw [show n - 1 + 1 = n by omega]

end FieldDual

section Derived

open scoped DG.DGModule.HOM.LeftAction

variable {k : Type u} [Field k] {R : Type u} [Ring R] (L : Type u) [AddCommGroup L] [Module k L]
  [Module Rᵐᵒᵖ L] [SMulCommClass k Rᵐᵒᵖ L] [DG.HasDerivedCategory.{u, u} R]

/-- The `k`-dual `HOM_k(L, k)` of a right `R`-module `L`, a left dg `R`-module. -/
abbrev dualModule : DGModuleCat.{u} R :=
  DGModuleCat.of R (DGModule.HOM k (InDegreeZero L) k)

/-- **Ext–Tor duality, vanishing form**: for a K-projective `P` with
`H⁻ⁿ(L ⊗_R P) = 0`, every morphism `P → L^*⟦n⟧` in `D(R)` is zero, `L^* = HOM_k(L, k)`. The
derived Hom out of `P` is the cohomology of `HOM_R(P, L^*) ≅ HOM_k(L ⊗_R P, k)` (currying),
which vanishes in degree `n` by `subsingleton_cohomology_HOM_field`. -/
theorem hom_dualModule_shift_eq_zero {P : DGModuleCat.{u} R} (hP : IsKProjective.{u} R P) (n : ℤ)
    [Subsingleton (cohomology (TensorProductOver R (InDegreeZero L) P) (-n))]
    (f : DG.DerivedCategory.Q.obj P ⟶ (DG.DerivedCategory.Q.obj (dualModule (k := k) L))⟦n⟧) :
    f = 0 := by
  have : Subsingleton (cohomology (DGModule.HOM k (TensorProductOver R (InDegreeZero L) P) k) n) :=
    subsingleton_cohomology_HOM_field
  have : Subsingleton (cohomology (DGModule.HOM R P (DGModule.HOM k (InDegreeZero L) k)) n) :=
    ((TensorProductOver.curryEquiv k R (InDegreeZero L) P k).cohomologyAddEquiv n).symm.subsingleton
  exact (DG.DerivedCategory.homShiftAddEquivOfIsKProjective hP _ n).injective
    (Subsingleton.elim _ _)

end Derived

end

end Categorification
