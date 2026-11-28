/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# The dual of a finitely generated projective right module

For rings `A`, `B` and an `(A, B)`-bimodule `M` (a left `A`-module with a commuting left
`Bᵐᵒᵖ`-action), the dual `M^∨ = Hom_{Bᵐᵒᵖ}(M, B)` of right `B`-linear maps is a
`(B, A)`-bimodule: `(b φ)(m) = b φ(m)` and `(φ a)(m) = φ(a m)`.

## Main definitions and results

* `Categorification.RightDualModule B M`: the dual `M^∨`, with its `(B, A)`-bimodule structure.
* `Categorification.RightDualModule.exists_dualBasis`: a finitely generated projective right
  module has a finite dual basis, `m = Σ_i e_i φ_i(m)`.
* `Categorification.RightDualModule.dualBasisVec`, `dualBasisCoord`, `sum_dualBasis`: a chosen
  dual basis.
* `Categorification.RightDualModule.projective`: `M^∨` is a projective left `B`-module.

This is the dual basis lemma for projective modules over a noncommutative ring; it is used for
the adjunction `M^∨ ⊗ᴸ_A - ⊣ M ⊗ᴸ_B -` of derived tensor products.
-/

open MulOpposite

namespace Categorification

/-- The dual `Hom_{Bᵐᵒᵖ}(M, B)` of a right `B`-module `M` (a left `Bᵐᵒᵖ`-module), as a type
carrying the left `B`-module structure `(b φ)(m) = b φ(m)`. -/
def RightDualModule (B : Type*) [Ring B] (M : Type*) [AddCommGroup M] [Module Bᵐᵒᵖ M] :
    Type _ :=
  M →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ

namespace RightDualModule

variable {B : Type*} [Ring B] {M : Type*} [AddCommGroup M] [Module Bᵐᵒᵖ M]

instance : AddCommGroup (RightDualModule B M) :=
  inferInstanceAs (AddCommGroup (M →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ))

instance : FunLike (RightDualModule B M) M Bᵐᵒᵖ :=
  inferInstanceAs (FunLike (M →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ) M Bᵐᵒᵖ)

instance : LinearMapClass (RightDualModule B M) Bᵐᵒᵖ M Bᵐᵒᵖ :=
  inferInstanceAs (LinearMapClass (M →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ) Bᵐᵒᵖ M Bᵐᵒᵖ)

/-- A right linear map `M → B` as an element of the dual. -/
def ofLinearMap (f : M →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ) : RightDualModule B M := f

@[simp]
theorem ofLinearMap_apply (f : M →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ) (m : M) : ofLinearMap f m = f m := rfl

@[ext]
theorem ext {φ ψ : RightDualModule B M} (h : ∀ m, φ m = ψ m) : φ = ψ :=
  LinearMap.ext h

@[simp]
theorem zero_apply (m : M) : (0 : RightDualModule B M) m = 0 := rfl

@[simp]
theorem add_apply (φ ψ : RightDualModule B M) (m : M) : (φ + ψ) m = φ m + ψ m := rfl

theorem sum_apply {ι : Type*} (s : Finset ι) (φ : ι → RightDualModule B M) (m : M) :
    (∑ i ∈ s, φ i) m = ∑ i ∈ s, φ i m :=
  LinearMap.sum_apply s φ m

instance : SMul B (RightDualModule B M) where
  smul b φ := ofLinearMap
    { toFun := fun m => φ m * op b
      map_add' := fun m m' => by rw [map_add, add_mul]
      map_smul' := fun c m => by
        rw [map_smul, smul_eq_mul, smul_eq_mul, mul_assoc]
        rfl }

@[simp]
theorem smul_apply (b : B) (φ : RightDualModule B M) (m : M) : (b • φ) m = φ m * op b := rfl

instance : Module B (RightDualModule B M) where
  one_smul φ := ext fun m => by rw [smul_apply, op_one, mul_one]
  mul_smul b b' φ := ext fun m => by rw [smul_apply, smul_apply, smul_apply, op_mul, mul_assoc]
  smul_zero b := ext fun m => by rw [smul_apply, zero_apply, zero_mul]
  smul_add b φ ψ := ext fun m => by rw [smul_apply, add_apply, add_apply, add_mul]; rfl
  add_smul b b' φ := ext fun m => by rw [smul_apply, add_apply, op_add, mul_add]; rfl
  zero_smul φ := ext fun m => by rw [smul_apply, op_zero, mul_zero, zero_apply]

section Bimodule

variable {A : Type*} [Ring A] [Module A M] [SMulCommClass A Bᵐᵒᵖ M]

instance : SMul Aᵐᵒᵖ (RightDualModule B M) where
  smul a φ := ofLinearMap
    { toFun := fun m => φ (a.unop • m)
      map_add' := fun m m' => by rw [smul_add, map_add]
      map_smul' := fun c m => by
        rw [smul_comm, map_smul]
        rfl }

@[simp]
theorem op_smul_apply (a : Aᵐᵒᵖ) (φ : RightDualModule B M) (m : M) :
    (a • φ) m = φ (a.unop • m) := rfl

instance : Module Aᵐᵒᵖ (RightDualModule B M) where
  one_smul φ := ext fun m => by rw [op_smul_apply, unop_one, one_smul]
  mul_smul a a' φ := ext fun m => by
    rw [op_smul_apply, op_smul_apply, op_smul_apply, unop_mul, mul_smul]
  smul_zero a := ext fun m => by rw [op_smul_apply, zero_apply, zero_apply]
  smul_add a φ ψ := ext fun m => rfl
  add_smul a a' φ := ext fun m => by
    rw [op_smul_apply, add_apply, unop_add, add_smul, map_add]; rfl
  zero_smul φ := ext fun m => by rw [op_smul_apply, unop_zero, zero_smul, map_zero, zero_apply]

instance : SMulCommClass B Aᵐᵒᵖ (RightDualModule B M) where
  smul_comm _ _ _ := ext fun _ => rfl

end Bimodule

section DualBasis

variable (B M)

/-- **The dual basis lemma**: a finitely generated projective right module has a finite dual
basis `(e_i, φ_i)`, `m = Σ_i e_i φ_i(m)`. -/
theorem exists_dualBasis [Module.Projective Bᵐᵒᵖ M] [Module.Finite Bᵐᵒᵖ M] :
    ∃ (n : ℕ) (e : Fin n → M) (φ : Fin n → RightDualModule B M),
      ∀ m : M, ∑ i, φ i m • e i = m := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' Bᵐᵒᵖ M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨n, fun i => f (Pi.single i 1), fun i => ofLinearMap ((LinearMap.proj i).comp s),
    fun m => ?_⟩
  conv_rhs => rw [← LinearMap.id_apply (R := Bᵐᵒᵖ) m, ← hs, LinearMap.comp_apply,
    ← Finset.univ_sum_single (s m), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_smul]
  congr 1
  ext j
  simp [Pi.single_apply]

variable [Module.Projective Bᵐᵒᵖ M] [Module.Finite Bᵐᵒᵖ M]

/-- The length of the chosen dual basis. -/
noncomputable def dualRank : ℕ := (exists_dualBasis B M).choose

/-- The vectors `e_i` of the chosen dual basis. -/
noncomputable def dualBasisVec : Fin (dualRank B M) → M :=
  (exists_dualBasis B M).choose_spec.choose

/-- The coordinate functions `φ_i` of the chosen dual basis. -/
noncomputable def dualBasisCoord : Fin (dualRank B M) → RightDualModule B M :=
  (exists_dualBasis B M).choose_spec.choose_spec.choose

/-- `m = Σ_i e_i φ_i(m)`. -/
theorem sum_dualBasis (m : M) :
    ∑ i, dualBasisCoord B M i m • dualBasisVec B M i = m :=
  (exists_dualBasis B M).choose_spec.choose_spec.choose_spec m

/-- `ψ = Σ_i ψ(e_i) φ_i` for every `ψ` in the dual. -/
theorem sum_dualBasis_dual (ψ : RightDualModule B M) :
    ∑ i, unop (ψ (dualBasisVec B M i)) • dualBasisCoord B M i = ψ := by
  ext m
  rw [sum_apply]
  conv_rhs => rw [← sum_dualBasis B M m, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_apply, op_unop, map_smul, smul_eq_mul]

/-- **The dual of a finitely generated projective right module is a projective left module.** -/
instance projective : Module.Projective B (RightDualModule B M) := by
  let s : RightDualModule B M →ₗ[B] (Fin (dualRank B M) → B) :=
    { toFun := fun ψ i => unop (ψ (dualBasisVec B M i))
      map_add' := fun ψ ψ' => funext fun i => by
        rw [add_apply, unop_add]
        rfl
      map_smul' := fun b ψ => funext fun i => by
        rw [smul_apply, unop_mul, unop_op]
        rfl }
  let π : (Fin (dualRank B M) → B) →ₗ[B] RightDualModule B M :=
    { toFun := fun c => ∑ i, c i • dualBasisCoord B M i
      map_add' := fun c c' => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => add_smul _ _ _
      map_smul' := fun b c => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_smul _ _ _ }
  exact Module.Projective.of_split s π (LinearMap.ext fun ψ => sum_dualBasis_dual B M ψ)

end DualBasis

end RightDualModule

end Categorification
