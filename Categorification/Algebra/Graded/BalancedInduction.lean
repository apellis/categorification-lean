/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.TensorHomDuality
import Categorification.Algebra.Graded.G0
import Categorification.Algebra.BalancedTensorAssoc
import Categorification.Algebra.HomTensorComp

/-!
# Tensoring finite-dimensional graded modules with a graded bimodule

For graded algebras `A`, `B` and a finite-dimensional graded `(B, A)`-bimodule `M`, the functor
`N ↦ M ⊗_A N` on finite-dimensional graded left modules, with the tensor product grading. Right
modules are left modules over the opposite algebras, so this also covers `N ↦ N ⊗_A M` on right
modules. In B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§4.6 and §6.1, the functors `𝔉_i` and the braiding functors `𝔅` (Definition 6.6) are of this
form on finite-dimensional modules.

## Main definitions and results

* `GFin.induce ℳ N` : the graded module `M ⊗_A N`.
* `GFin.induceCongr` : an isomorphism `N ≅ N'` gives `M ⊗_A N ≅ M ⊗_A N'`.
* `GFin.induceCongrLeft` : a graded bimodule isomorphism `M ≅ M'` gives `M ⊗_A N ≅ M' ⊗_A N`.
* `GFin.induceInduceIso` : `M' ⊗_B (M ⊗_A N) ≅ (M' ⊗_B M) ⊗_A N`.
-/

noncomputable section

namespace Categorification.Graded

open DirectSum MulOpposite BalancedTensor
open scoped TensorProduct

universe u

variable {k : Type*} [Field k] {A B : Type u} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] (ℬ : ℤ → Submodule k B)

theorem finite_balancedTensor {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    {M : Type*} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M] [Module Aᵐᵒᵖ M] [Module.Finite k M] (N : Type*) [AddCommGroup N] [Module k N]
    [Module A N] [Module.Finite k N] : Module.Finite k (BalancedTensor k B A M N) := by
  have : Module.Finite k (M ⊗[k] N) := Module.Finite.tensorProduct k _ _
  exact Module.Finite.of_surjective
    (((BalancedTensor.mk k B A M N).restrictScalars k : M ⊗[k] N →ₗ[k] BalancedTensor k B A M N))
    (BalancedTensor.mk_surjective (k := k) (B := B) (A := A) (M := M) (N := N))

section Induce

variable {M : Type u} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul ℬ ℳ]
  [SetLike.GradedSMul (oppositeGrade 𝒜) ℳ]

variable [Module.Finite k M]

/-- **`M ⊗_A N`** for a finite-dimensional graded `(B, A)`-bimodule `M`, with the tensor product
grading. -/
def GFin.induce (N : GFin 𝒜) : GFin ℬ where
  carrier := BalancedTensor k B A M N.carrier
  grading := balancedGrading B A ℳ N.grading
  decomposition := balancedDecomposition (B := B) (ℳ := ℳ) (𝒩 := N.grading) 𝒜
    (op_smul_mem_of_mem 𝒜 ℳ)
  gradedSMul := gradedSMul_balanced (B := B) (A := A) (ℳ := ℳ) (𝒩 := N.grading) ℬ
  finiteDimensional := finite_balancedTensor (B := B) (A := A) (M := M) N.carrier

variable {𝒜 ℬ ℳ}

omit [IsScalarTower k Aᵐᵒᵖ M] in
theorem GFin.tmul_mem_induce (N : GFin 𝒜) {i j : ℤ} {m : M} {n : N.carrier} (hm : m ∈ ℳ i)
    (hn : n ∈ N.grading j) :
    (tmul m n : BalancedTensor k B A M N.carrier) ∈ (GFin.induce 𝒜 ℬ ℳ N).grading (i + j) :=
  tmul_mem_balancedGrading hm hn

/-- An isomorphism `N ≅ N'` gives `M ⊗_A N ≅ M ⊗_A N'`. -/
def GFin.induceCongr {N N' : GFin 𝒜} (e : N.Iso N') :
    (GFin.induce 𝒜 ℬ ℳ N).Iso (GFin.induce 𝒜 ℬ ℳ N') :=
  GradedEquiv.ofPreserves (BalancedTensor.congrRight e.toLinearEquiv)
    (fun _ _ hy => mapRight_mem_balancedGrading (ℳ := ℳ) e.preservesGrading hy)

/-- A degree-preserving isomorphism of graded bimodules `M ≅ M'` gives `M ⊗_A N ≅ M' ⊗_A N`. -/
def GFin.induceCongrLeft {M' : Type u} [AddCommGroup M'] [Module k M'] [Module B M']
    [IsScalarTower k B M'] [Module Aᵐᵒᵖ M'] [SMulCommClass B Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
    {ℳ' : ℤ → Submodule k M'} [Decomposition ℳ'] [SetLike.GradedSMul ℬ ℳ']
    [SetLike.GradedSMul (oppositeGrade 𝒜) ℳ'] [Module.Finite k M']
    (f : M ≃ₗ[B] M') (hf : IsBimoduleHom (A := A) f.toLinearMap)
    (hgr : ∀ ⦃d : ℤ⦄ ⦃m : M⦄, m ∈ ℳ d → f m ∈ ℳ' d) (N : GFin 𝒜) :
    (GFin.induce 𝒜 ℬ ℳ N).Iso (GFin.induce 𝒜 ℬ ℳ' N) :=
  GradedEquiv.ofPreserves (congrLeftBimodule k N.carrier f hf) fun _ _ hy =>
    balancedGrading_map_mem _ ((congrLeftBimodule k N.carrier f hf).toLinearMap.restrictScalars k)
      (fun _ _ _ _ hm hn => tmul_mem_balancedGrading (B := B) (A := A) (hgr hm) hn) hy

end Induce

/-! ### Composition -/

section Compose

variable {C : Type u} [Ring C] [Algebra k C] [GradedAlgebra ℬ] (𝒞 : ℤ → Submodule k C)
  {M : Type u} [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
  [Module Aᵐᵒᵖ M] [SMulCommClass B Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  (ℳ : ℤ → Submodule k M) [Decomposition ℳ] [SetLike.GradedSMul ℬ ℳ]
  [SetLike.GradedSMul (oppositeGrade 𝒜) ℳ] [Module.Finite k M]
  {M' : Type u} [AddCommGroup M'] [Module k M'] [Module C M'] [IsScalarTower k C M']
  [Module Bᵐᵒᵖ M'] [SMulCommClass C Bᵐᵒᵖ M'] [IsScalarTower k Bᵐᵒᵖ M']
  (ℳ' : ℤ → Submodule k M') [Decomposition ℳ'] [SetLike.GradedSMul 𝒞 ℳ']
  [SetLike.GradedSMul (oppositeGrade ℬ) ℳ'] [Module.Finite k M']

instance : IsScalarTower k Aᵐᵒᵖ (BalancedTensor k C B M' M) where
  smul_assoc c a t := by
    induction t using BalancedTensor.induction_on with
    | zero => rw [smul_zero, smul_zero, smul_zero]
    | tmul x y =>
      change tmul x ((c • a) • y) = c • tmul x (a • y)
      rw [smul_assoc, BalancedTensor.tmul_smul]
    | add s t hs ht => rw [smul_add, smul_add, hs, ht, smul_add]

@[instance_reducible] def compDecomposition : Decomposition (balancedGrading C B ℳ' ℳ) :=
  balancedDecomposition (B := C) (ℳ := ℳ') (𝒩 := ℳ) ℬ (op_smul_mem_of_mem ℬ ℳ')

omit [Algebra k B] [IsScalarTower k B M] [Decomposition ℳ] [Module.Finite k M]
  [SMulCommClass C Bᵐᵒᵖ M'] [IsScalarTower k Bᵐᵒᵖ M'] [Decomposition ℳ'] [Module.Finite k M'] in
theorem compGradedSMul : SetLike.GradedSMul 𝒞 (balancedGrading C B ℳ' ℳ) :=
  gradedSMul_balanced (B := C) (A := B) (ℳ := ℳ') (𝒩 := ℳ) 𝒞

omit [GradedAlgebra 𝒜] [IsScalarTower k Aᵐᵒᵖ M] [Decomposition ℳ] [Module.Finite k M]
  [IsScalarTower k Bᵐᵒᵖ M'] [Decomposition ℳ'] [Module.Finite k M'] in
theorem compGradedSMulRight : SetLike.GradedSMul (oppositeGrade 𝒜) (balancedGrading C B ℳ' ℳ) where
  smul_mem {l d} a t ha ht := by
    have key := balancedGrading_map_mem (fun e => balancedGrading C B ℳ' ℳ (e + l)) ((mapRight (rmul B M a)).restrictScalars k)
      (fun i j x y hx hy => by
        rw [LinearMap.restrictScalars_apply, mapRight_tmul, add_assoc]
        refine tmul_mem_balancedGrading hx ?_
        rw [add_comm]
        exact SetLike.GradedSMul.smul_mem (A := oppositeGrade 𝒜) ha hy) ht
    rw [show l +ᵥ d = d + l from add_comm l d]
    exact key

/-- **`M' ⊗_B (M ⊗_A N) ≅ (M' ⊗_B M) ⊗_A N`**, as graded modules. -/
def GFin.induceInduceIso (N : GFin 𝒜) :
    letI := compDecomposition (C := C) ℬ ℳ ℳ'
    letI := compGradedSMul (B := B) 𝒞 ℳ ℳ'
    letI := compGradedSMulRight (B := B) (C := C) 𝒜 ℳ ℳ'
    letI := finite_balancedTensor (k := k) (B := C) (A := B) (M := M') M
    (GFin.induce ℬ 𝒞 ℳ' (GFin.induce 𝒜 ℬ ℳ N)).Iso
      (GFin.induce 𝒜 𝒞 (balancedGrading C B ℳ' ℳ) N) :=
  letI := compDecomposition (C := C) ℬ ℳ ℳ'
  letI := compGradedSMul (B := B) 𝒞 ℳ ℳ'
  letI := compGradedSMulRight (B := B) (C := C) 𝒜 ℳ ℳ'
  letI := finite_balancedTensor (k := k) (B := C) (A := B) (M := M') M
  GradedEquiv.ofPreserves (BalancedTensor.assoc k C B A M' M N.carrier).symm fun _ _ hy =>
    balancedGrading_map_mem _ ((BalancedTensor.assoc k C B A M' M N.carrier).symm.toLinearMap.restrictScalars k)
      (fun i j x t hx ht => by
        refine balancedGrading_map_mem
          (fun e => (GFin.induce 𝒜 𝒞 (balancedGrading C B ℳ' ℳ) N).grading (i + e))
          (((BalancedTensor.assoc k C B A M' M N.carrier).symm.toLinearMap.restrictScalars k).comp
            (BalancedTensor.mkBil k C B M' _ x))
          (fun a b y n hy hn => ?_) ht
        have h := tmul_mem_balancedGrading (B := C) (A := A) (tmul_mem_balancedGrading (B := C)
          (A := B) hx hy) hn
        rw [add_assoc] at h
        exact h) hy

end Compose

end Categorification.Graded
