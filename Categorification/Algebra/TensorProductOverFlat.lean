/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Module.TensorProductOver
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Exact.Basic

/-!
# Projective modules are flat for the balanced tensor product

For a projective left `A`-module `N`, the functor `- ⊗_A N` on right `A`-modules preserves
injective maps (`DG.TensorProductOver.map_injective_of_projective`). The proof reduces to a free
module `ι →₀ A`, for which `M ⊗_A (ι →₀ A) → (ι →₀ M)`, `m ⊗ g ↦ Σ_i (m • g i)` at `i`, has the
left inverse `m` at `i` `↦ m ⊗ single i 1`.

This is used for the long exact sequence of a derived tensor product in the coefficient
(B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Lemma 6.11, step `f_n → s_n`).
-/

open MulOpposite

namespace DG.TensorProductOver

variable {A M M' N : Type*} [Ring A] [AddCommGroup M] [Module Aᵐᵒᵖ M] [AddCommGroup M']
  [Module Aᵐᵒᵖ M'] [AddCommGroup N] [Module A N]

section Free

variable (A M) (ι : Type*)

/-- `M ⊗_A (ι →₀ A) → (ι →₀ M)`, `m ⊗ g ↦ Σ_i single i (m • g i)`. -/
noncomputable def freeCoord : TensorProductOver A M (ι →₀ A) →+ (ι →₀ M) :=
  lift
    { toFun := fun m => (Finsupp.liftAddHom fun i =>
          (Finsupp.singleAddHom i).comp ((AddMonoidHom.flip (smulAddHom Aᵐᵒᵖ M) m).comp
            (opAddEquiv : A ≃+ Aᵐᵒᵖ).toAddMonoidHom))
      map_zero' := by ext; simp
      map_add' := fun m m' => by ext; simp }
    fun a m g => by
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add g g' hg hg' => simp only [map_add, smul_add, hg, hg']
      | single i b =>
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.liftAddHom_apply_single,
          AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
          AddMonoidHom.coe_coe, opAddEquiv_apply, AddMonoidHom.flip_apply, smulAddHom_apply,
          Finsupp.singleAddHom_apply, Finsupp.smul_single, smul_eq_mul, op_mul, mul_smul]

theorem freeCoord_tmul_single (m : M) (i : ι) (b : A) :
    freeCoord A M ι (tmul A m (Finsupp.single i b)) = Finsupp.single i (op b • m) := by
  simp [freeCoord]

/-- The left inverse of `freeCoord`: `single i m ↦ m ⊗ single i 1`. -/
noncomputable def freeCoordInv : (ι →₀ M) →+ TensorProductOver A M (ι →₀ A) :=
  Finsupp.liftAddHom fun i => (tmulAddHom A M (ι →₀ A)).flip (Finsupp.single i 1)

theorem freeCoordInv_freeCoord (x : TensorProductOver A M (ι →₀ A)) :
    freeCoordInv A M ι (freeCoord A M ι x) = x := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul m g =>
    induction g using Finsupp.induction_linear with
    | zero => rw [tmul_zero, map_zero, map_zero]
    | add g g' hg hg' => rw [tmul_add, map_add, map_add, hg, hg']
    | single i b =>
      rw [freeCoord_tmul_single, freeCoordInv, Finsupp.liftAddHom_apply_single,
        AddMonoidHom.flip_apply, tmulAddHom_apply, op_smul_tmul, Finsupp.smul_single,
        smul_eq_mul, mul_one]

theorem freeCoord_injective : Function.Injective (freeCoord A M ι) :=
  Function.LeftInverse.injective (freeCoordInv_freeCoord A M ι)

variable {A M ι}

theorem freeCoord_map (f : M →ₗ[Aᵐᵒᵖ] M') (x : TensorProductOver A M (ι →₀ A)) :
    freeCoord A M' ι (map f LinearMap.id x) = Finsupp.mapRange f (map_zero f) (freeCoord A M ι x) := by
  induction x using induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Finsupp.mapRange_add (map_add f)]
  | tmul m g =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' =>
      rw [tmul_add, map_add, map_add, hg, hg', map_add, Finsupp.mapRange_add (map_add f)]
    | single i b =>
      rw [map_tmul, LinearMap.id_apply, freeCoord_tmul_single, freeCoord_tmul_single,
        Finsupp.mapRange_single, map_smul]

/-- Tensoring with a free module preserves injective maps. -/
theorem map_injective_free {f : M →ₗ[Aᵐᵒᵖ] M'} (hf : Function.Injective f) :
    Function.Injective (map f (LinearMap.id : (ι →₀ A) →ₗ[A] (ι →₀ A))) := by
  intro x y h
  apply freeCoord_injective A M ι
  have := congrArg (freeCoord A M' ι) h
  rw [freeCoord_map, freeCoord_map] at this
  exact Finsupp.mapRange_injective _ (map_zero f) hf this

theorem freeCoord_freeCoordInv (x : ι →₀ M') : freeCoord A M' ι (freeCoordInv A M' ι x) = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single i m =>
    rw [freeCoordInv, Finsupp.liftAddHom_apply_single, AddMonoidHom.flip_apply, tmulAddHom_apply,
      freeCoord_tmul_single, op_one, one_smul]

/-- Tensoring with a free module preserves exactness. -/
theorem exact_map_free {M'' : Type*} [AddCommGroup M''] [Module Aᵐᵒᵖ M''] {f : M →ₗ[Aᵐᵒᵖ] M'}
    {g : M' →ₗ[Aᵐᵒᵖ] M''} (h : Function.Exact f g) :
    Function.Exact (map f (LinearMap.id : (ι →₀ A) →ₗ[A] (ι →₀ A))) (map g LinearMap.id) := by
  classical
  intro x
  constructor
  · intro hx
    have hx' : Finsupp.mapRange g (map_zero g) (freeCoord A M' ι x) = 0 := by
      rw [← freeCoord_map, hx, map_zero]
    have : ∀ i, ∃ m, f m = freeCoord A M' ι x i := fun i =>
      (h _).1 (by simpa using DFunLike.congr_fun hx' i)
    choose c hc using this
    let y : ι →₀ M := Finsupp.onFinset (freeCoord A M' ι x).support
      (fun i => if freeCoord A M' ι x i = 0 then 0 else c i) (fun i hi => by
        simp only [Finsupp.mem_support_iff]
        intro h0; exact hi (by simp [h0]))
    refine ⟨freeCoordInv A M ι y, freeCoord_injective A M' ι ?_⟩
    rw [freeCoord_map, freeCoord_freeCoordInv]
    ext i
    simp only [Finsupp.mapRange_apply, y, Finsupp.onFinset_apply]
    split_ifs with h0
    · rw [map_zero, h0]
    · exact hc i
  · rintro ⟨y, rfl⟩
    rw [← AddMonoidHom.comp_apply, ← map_comp]
    have : g.comp f = 0 := LinearMap.ext fun m => h.apply_apply_eq_zero m
    rw [this]
    induction y using induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
    | tmul m n => simp

end Free

/-- **Projective modules are flat for the balanced tensor product**: for a projective left
`A`-module `N`, `f ⊗ N` is injective when `f` is. -/
theorem map_injective_of_projective [Module.Projective A N] {f : M →ₗ[Aᵐᵒᵖ] M'}
    (hf : Function.Injective f) : Function.Injective (map f (LinearMap.id : N →ₗ[A] N)) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective A N)
  let π := Finsupp.linearCombination A (id : N → N)
  have hπs : ∀ n, π (s n) = n := fun n => LinearMap.congr_fun hs n
  have hleft : ∀ x : TensorProductOver A M N,
      map LinearMap.id π (map LinearMap.id s x) = x := by
    intro x
    induction x using induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul m n => rw [map_tmul, map_tmul, LinearMap.id_apply, LinearMap.id_apply, hπs]
  have hcomm : ∀ x : TensorProductOver A M N,
      map f LinearMap.id (map LinearMap.id s x) = map LinearMap.id s (map f LinearMap.id x) := by
    intro x
    induction x using induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | tmul m n => rfl
  intro x y h
  have hs' := map_injective_free (ι := N) hf
    (show map f LinearMap.id (map LinearMap.id s x) = map f LinearMap.id (map LinearMap.id s y) by
      rw [hcomm, hcomm, h])
  rw [← hleft x, ← hleft y, hs']

/-- For a projective left `A`-module `N`, `- ⊗_A N` sends an exact pair of right `A`-modules to
an exact pair. -/
theorem exact_map_of_projective [Module.Projective A N] {M'' : Type*} [AddCommGroup M'']
    [Module Aᵐᵒᵖ M''] {f : M →ₗ[Aᵐᵒᵖ] M'} {g : M' →ₗ[Aᵐᵒᵖ] M''} (h : Function.Exact f g) :
    Function.Exact (map f (LinearMap.id : N →ₗ[A] N)) (map g LinearMap.id) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective A N)
  let π := Finsupp.linearCombination A (id : N → N)
  have hπs : ∀ n, π (s n) = n := fun n => LinearMap.congr_fun hs n
  have hleft : ∀ {X : Type _} [AddCommGroup X] [Module Aᵐᵒᵖ X] (x : TensorProductOver A X N),
      map LinearMap.id π (map LinearMap.id s x) = x := by
    intro X _ _ x
    induction x using induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul m n => rw [map_tmul, map_tmul, LinearMap.id_apply, LinearMap.id_apply, hπs]
  have hcomm : ∀ {X Y : Type _} [AddCommGroup X] [Module Aᵐᵒᵖ X] [AddCommGroup Y]
      [Module Aᵐᵒᵖ Y] (u : X →ₗ[Aᵐᵒᵖ] Y) (x : TensorProductOver A X N),
      map u LinearMap.id (map LinearMap.id s x) = map LinearMap.id s (map u LinearMap.id x) := by
    intro X Y _ _ _ _ u x
    induction x using induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | tmul m n => rfl
  have hcomm' : ∀ {X Y : Type _} [AddCommGroup X] [Module Aᵐᵒᵖ X] [AddCommGroup Y]
      [Module Aᵐᵒᵖ Y] (u : X →ₗ[Aᵐᵒᵖ] Y) (x : TensorProductOver A X (N →₀ A)),
      map u LinearMap.id (map LinearMap.id π x) = map LinearMap.id π (map u LinearMap.id x) := by
    intro X Y _ _ _ _ u x
    induction x using induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | tmul m n => rfl
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := ((exact_map_free (A := A) (ι := N) h) (map LinearMap.id s x)).1
      (by rw [hcomm, hx, map_zero])
    exact ⟨map LinearMap.id π y, by rw [hcomm', hy, hleft]⟩
  · rintro ⟨y, rfl⟩
    rw [← AddMonoidHom.comp_apply, ← map_comp]
    have : g.comp f = 0 := LinearMap.ext fun m => h.apply_apply_eq_zero m
    rw [this]
    induction y using induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
    | tmul m n => simp

/-- `- ⊗_A N` preserves surjective maps. -/
theorem map_surjective {f : M →ₗ[Aᵐᵒᵖ] M'} (hf : Function.Surjective f) :
    Function.Surjective (map f (LinearMap.id : N →ₗ[A] N)) := by
  intro x
  induction x using induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩
  | tmul m n =>
    obtain ⟨m', rfl⟩ := hf m
    exact ⟨tmul A m' n, rfl⟩

end DG.TensorProductOver
