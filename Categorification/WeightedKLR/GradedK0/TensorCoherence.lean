/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ExtTensorK0Equiv
import Categorification.Algebra.Graded.K0Map
import Categorification.Algebra.InductionAlongAssoc
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Associativity of the graded tensor comparison

For Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Proposition 2.18 and Theorem 2.19, the tensor comparison on projective classes
intertwines both associators. The right-associated three-factor comparison
is injective by pairing with external products of the graded simple tops.
-/

noncomputable section

namespace Categorification.Graded

open scoped TensorProduct
open DirectSum

section Grading

variable {k X Y Z : Type*} [CommRing k] [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y] [AddCommGroup Z] [Module k Z]
  (𝒳 : ℤ → Submodule k X) (𝒴 : ℤ → Submodule k Y) (𝒵 : ℤ → Submodule k Z)

theorem tensorAssoc_mem_grading {d : ℤ} {x : (X ⊗[k] Y) ⊗[k] Z}
    (hx : x ∈ tensorGrading (tensorGrading 𝒳 𝒴) 𝒵 d) :
    TensorProduct.assoc k X Y Z x ∈ tensorGrading 𝒳 (tensorGrading 𝒴 𝒵) d := by
  refine tensorGrading_map_mem _ _ _ (TensorProduct.assoc k X Y Z).toLinearMap
    (fun i j xy z hxy hz => ?_) hx
  refine tensorGrading_map_mem 𝒳 𝒴
    (fun n => tensorGrading 𝒳 (tensorGrading 𝒴 𝒵) (n + j))
    ((TensorProduct.assoc k X Y Z).toLinearMap ∘ₗ ((TensorProduct.mk k _ Z).flip z))
    (fun p q x y hx hy => ?_) hxy
  rw [add_assoc]
  exact tmul_mem_tensorGrading hx (tmul_mem_tensorGrading hy hz)

theorem tensorAssoc_symm_mem_grading {d : ℤ} {x : X ⊗[k] (Y ⊗[k] Z)}
    (hx : x ∈ tensorGrading 𝒳 (tensorGrading 𝒴 𝒵) d) :
    (TensorProduct.assoc k X Y Z).symm x ∈ tensorGrading (tensorGrading 𝒳 𝒴) 𝒵 d := by
  refine tensorGrading_map_mem _ _ _ (TensorProduct.assoc k X Y Z).symm.toLinearMap
    (fun i j x yz hx hyz => ?_) hx
  refine tensorGrading_map_mem 𝒴 𝒵
    (fun n => tensorGrading (tensorGrading 𝒳 𝒴) 𝒵 (i + n))
    ((TensorProduct.assoc k X Y Z).symm.toLinearMap ∘ₗ (TensorProduct.mk k X _ x))
    (fun p q y z hy hz => ?_) hyz
  rw [← add_assoc]
  exact tmul_mem_tensorGrading (tmul_mem_tensorGrading hx hy) hz

end Grading

section Associator

open InductionAlong

universe u v

variable {k : Type v} [Field k] {A B C : Type u}
  [Ring A] [Algebra k A] [Ring B] [Algebra k B] [Ring C] [Algebra k C]
  (𝒜 : ℤ → Submodule k A) (ℬ : ℤ → Submodule k B) (𝒞 : ℤ → Submodule k C)

/-- Transport of projective classes along the graded tensor associator. -/
def K0.tensorAssoc :
    K0 (tensorGrading (tensorGrading 𝒜 ℬ) 𝒞) →ₗ[LaurentPolynomial ℤ]
      K0 (tensorGrading 𝒜 (tensorGrading ℬ 𝒞)) :=
  K0.map (Algebra.TensorProduct.assoc k k k A B C)
    (fun _ _ hx => tensorAssoc_symm_mem_grading 𝒜 ℬ 𝒞 hx)

/-- The tensor associator sends `(x ⊠ y) ⊠ z` to `x ⊠ (y ⊠ z)` on projective classes. -/
theorem K0.tensorAssoc_extTensor (x : K0 𝒜) (y : K0 ℬ) (z : K0 𝒞) :
    K0.tensorAssoc 𝒜 ℬ 𝒞 (K0.extTensor (tensorGrading 𝒜 ℬ) 𝒞 (K0.extTensor 𝒜 ℬ x y) z) =
      K0.extTensor 𝒜 (tensorGrading ℬ 𝒞) x (K0.extTensor ℬ 𝒞 y z) := by
  induction x using K0.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, LinearMap.neg_apply, hx]
  | of P =>
    induction y using K0.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
    | neg y hy => simp only [map_neg, LinearMap.neg_apply, hy]
    | of Q =>
      induction z using K0.induction_on with
      | zero => simp only [map_zero]
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | neg z hz => simp only [map_neg, hz]
      | of R =>
        simp only [K0.extTensor_of]
        exact K0.map_of_semilinear _ _ _ _ (extAssoc k P.carrier Q.carrier R.carrier)
          (extAssoc_smul k P.carrier Q.carrier R.carrier)
          (fun _ _ hx => tensorAssoc_mem_grading P.grading Q.grading R.grading hx)
          (fun _ _ hx => tensorAssoc_symm_mem_grading P.grading Q.grading R.grading hx)

end Associator


section Triple

universe u v

variable {k : Type v} [Field k] {A B C : Type u}
  [Ring A] [Algebra k A] [Ring B] [Algebra k B] [Ring C] [Algebra k C]
  (𝒜 : ℤ → Submodule k A) (ℬ : ℤ → Submodule k B) (𝒞 : ℤ → Submodule k C)

local notation "L" => LaurentPolynomial ℤ

/-- The left-associated tensor comparison on three factors. -/
def K0.extTensorLeft :
    (K0 𝒜 ⊗[L] K0 ℬ) ⊗[L] K0 𝒞 →ₗ[L] K0 (tensorGrading (tensorGrading 𝒜 ℬ) 𝒞) :=
  TensorProduct.lift (K0.extTensor (tensorGrading 𝒜 ℬ) 𝒞) ∘ₗ
    TensorProduct.map (TensorProduct.lift (K0.extTensor 𝒜 ℬ)) LinearMap.id

/-- The right-associated tensor comparison on three factors. -/
def K0.extTensorRight :
    K0 𝒜 ⊗[L] (K0 ℬ ⊗[L] K0 𝒞) →ₗ[L] K0 (tensorGrading 𝒜 (tensorGrading ℬ 𝒞)) :=
  TensorProduct.lift (K0.extTensor 𝒜 (tensorGrading ℬ 𝒞)) ∘ₗ
    TensorProduct.map LinearMap.id (TensorProduct.lift (K0.extTensor ℬ 𝒞))

@[simp] theorem K0.extTensorLeft_tmul (xy : K0 𝒜 ⊗[L] K0 ℬ) (z : K0 𝒞) :
    K0.extTensorLeft 𝒜 ℬ 𝒞 (xy ⊗ₜ z) =
      K0.extTensor (tensorGrading 𝒜 ℬ) 𝒞 (TensorProduct.lift (K0.extTensor 𝒜 ℬ) xy) z := by
  simp only [K0.extTensorLeft, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.lift.tmul]

@[simp] theorem K0.extTensorRight_tmul (x : K0 𝒜) (yz : K0 ℬ ⊗[L] K0 𝒞) :
    K0.extTensorRight 𝒜 ℬ 𝒞 (x ⊗ₜ yz) =
      K0.extTensor 𝒜 (tensorGrading ℬ 𝒞) x (TensorProduct.lift (K0.extTensor ℬ 𝒞) yz) := by
  simp only [K0.extTensorRight, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.lift.tmul]

/-- Both ways of comparing the three factors agree after applying the tensor associator. -/
theorem K0.tensorAssoc_extTensorLeft (t : (K0 𝒜 ⊗[L] K0 ℬ) ⊗[L] K0 𝒞) :
    K0.tensorAssoc 𝒜 ℬ 𝒞 (K0.extTensorLeft 𝒜 ℬ 𝒞 t) =
      K0.extTensorRight 𝒜 ℬ 𝒞 (TensorProduct.assoc L _ _ _ t) := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul xy z =>
    induction xy using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul x y =>
      simp only [K0.extTensorLeft_tmul, TensorProduct.lift.tmul,
        TensorProduct.assoc_tmul, K0.extTensorRight_tmul, K0.tensorAssoc_extTensor]

private theorem toLaurentSeries_one : toLaurentSeries (1 : L) = 1 := by
  ext d
  simp [← LaurentPolynomial.T_zero, HahnSeries.coeff_one, eq_comm]

private theorem pairingRight_smul (M : GFin 𝒜) (p : L) (x : K0 𝒜) :
    pairingRight M (p • x) =
      toLaurentSeries (LaurentPolynomial.invert p) * pairingRight M x := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [add_smul, map_add, hp, hq, map_add, map_add, add_mul]
  | C_mul_T n r =>
    calc
      pairingRight M ((LaurentPolynomial.C r * LaurentPolynomial.T n) • x) =
          r • (HahnSeries.single (-n) 1 * pairingRight M x) := by
        rw [mul_smul, LaurentPolynomial.C_eq_algebraMap, algebraMap_smul, map_zsmul,
          K0.T_smul, pairingRight_shiftHom]
      _ = _ := by
        rw [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T,
          ← LaurentPolynomial.smul_eq_C_mul, map_zsmul, ← smul_mul_assoc,
          ← mul_one (LaurentPolynomial.T (-n) : L), toLaurentSeries_T_mul,
          toLaurentSeries_one, mul_one]

variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [GradedAlgebra 𝒞]
  [HasGdim 𝒜] [HasGdim ℬ] [HasGdim 𝒞]

/-- The right-associated comparison is injective, using the pair comparison
hypotheses to furnish dual simple tops for each of the three factors. -/
theorem K0.extTensorRight_injective (H₁₂ : TensorK0Hyp 𝒜 ℬ) (H₂₃ : TensorK0Hyp ℬ 𝒞) :
    Function.Injective (K0.extTensorRight 𝒜 ℬ 𝒞) := by
  classical
  let b := (K0.indecBasis 𝒜).tensorProduct ((K0.indecBasis ℬ).tensorProduct (K0.indecBasis 𝒞))
  have detect (i : _) (x : _) :
      pairingRight ((GProj.IndecClass.topFin H₁₂.fdA i.1).extTensor (H₂₃.topT i.2.1 i.2.2))
        (K0.extTensorRight 𝒜 ℬ 𝒞 x) =
      toLaurentSeries (LaurentPolynomial.invert (b.repr x i)) := by
    let M := (GProj.IndecClass.topFin H₁₂.fdA i.1).extTensor (H₂₃.topT i.2.1 i.2.2)
    change pairingRight M (K0.extTensorRight 𝒜 ℬ 𝒞 x) = _
    have hδ (j : _) : pairingRight M (K0.extTensorRight 𝒜 ℬ 𝒞 (b j)) = if j = i then 1 else 0 := by
      rcases i with ⟨i₁, i₂, i₃⟩
      rcases j with ⟨j₁, j₂, j₃⟩
      simp only [b, M, Module.Basis.tensorProduct_apply, K0.extTensorRight_tmul,
        TensorProduct.lift.tmul, K0.indecBasis_apply, TensorK0Hyp.topT, pairingRight_extTensor,
        H₁₂.pairingRight_topA, H₂₃.pairingRight_topA, H₂₃.pairingRight_topB, Prod.mk.injEq]
      by_cases h₁ : j₁ = i₁ <;> by_cases h₂ : j₂ = i₂ <;> by_cases h₃ : j₃ = i₃ <;>
        simp [h₁, h₂, h₃]
    obtain ⟨f, rfl⟩ := b.repr.symm.surjective x
    rw [b.repr.apply_symm_apply]
    induction f using Finsupp.induction_linear with
    | zero => simp only [map_zero, Finsupp.zero_apply]
    | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]
    | single j r =>
      rw [b.repr_symm_single, map_smul, pairingRight_smul, hδ, Finsupp.single_apply]
      split <;> simp
  intro x y h
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  apply LaurentPolynomial.invert.injective
  apply toLaurentSeries_injective
  rw [← detect i x, ← detect i y, h]

end Triple

end Categorification.Graded
