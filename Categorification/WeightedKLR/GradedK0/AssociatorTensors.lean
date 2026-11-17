/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.Induction
import Categorification.WeightedKLR.Induction.ModuleMonoidal
import Categorification.WeightedKLR.GradedK0.ScalarComparison

/-!
# Pure tensors under the induction associator

Supporting the graded associativity of induction in Webster arXiv:1209.2463v4,
§2.4, Definition 2.17 and Theorem 2.19.
-/

noncomputable section

namespace Categorification.InductionAlong

open MulOpposite

section AssociatorTensors

open scoped TensorProduct

universe u w

variable (k : Type*) [CommRing k] {A₁ A₂ A₃ B₁₂ B₂₃ D D' : Type u}
  [Ring A₁] [Algebra k A₁] [Ring A₂] [Algebra k A₂] [Ring A₃] [Algebra k A₃]
  [Ring B₁₂] [Algebra k B₁₂] [Ring B₂₃] [Algebra k B₂₃]
  [Ring D] [Algebra k D] [Ring D'] [Algebra k D']
  (φ₁₂ : A₁ ⊗[k] A₂ →ₙ+* B₁₂) (hφ₁₂ : ∀ (r : k) t, φ₁₂ (r • t) = r • φ₁₂ t)
  (φ₂₃ : A₂ ⊗[k] A₃ →ₙ+* B₂₃) (hφ₂₃ : ∀ (r : k) t, φ₂₃ (r • t) = r • φ₂₃ t)
  (ψ : B₁₂ ⊗[k] A₃ →ₙ+* D) (ψ' : A₁ ⊗[k] B₂₃ →ₙ+* D') (c : D ≃ₐ[k] D')
  (hc : ∀ x y z, c (ψ (φ₁₂ (x ⊗ₜ y) ⊗ₜ z)) = ψ' (x ⊗ₜ φ₂₃ (y ⊗ₜ z)))
  {M N P : Type w} [AddCommGroup M] [Module k M] [Module A₁ M] [IsScalarTower k A₁ M]
  [AddCommGroup N] [Module k N] [Module A₂ N] [IsScalarTower k A₂ N]
  [AddCommGroup P] [Module k P] [Module A₃ P] [IsScalarTower k A₃ P]

/-- The nested unit tensor in the right-associated induction. -/
def indAssocUnit (m : M) (n : N) (p : P) :
    IndK k (ExtTensor k M (IndK k (ExtTensor k N P) φ₂₃)) ψ' :=
  IndK.tmul (k := k) (φ := ψ') (unitGen ψ')
    (ExtTensor.tmul (k := k) (Q := IndK k (ExtTensor k N P) φ₂₃) m
      (IndK.tmul (k := k) (φ := φ₂₃) (unitGen φ₂₃) (ExtTensor.tmul n p)))

/-- The left comparison on a pure tensor. -/
theorem indAssocLeft_pure (z : Corner ψ) (w : Corner φ₁₂) (m : M) (n : N) (p : P) :
    indAssocLeft k φ₁₂ hφ₁₂ ψ M N P
      (IndK.tmul (k := k) (φ := ψ) z
        (ExtTensor.tmul (k := k) (P := IndK k (ExtTensor k M N) φ₁₂)
          (IndK.tmul (k := k) (φ := φ₁₂) w (ExtTensor.tmul m n)) p)) =
      Ind.tmul (φ := ψ.comp (tensorLeft k A₃ φ₁₂ hφ₁₂))
        (compMul (tensorLeft k A₃ φ₁₂ hφ₁₂) ψ z (leftCorner w))
        (ExtTensor.tmul (ExtTensor.tmul m n) p) := by
  change compEquiv _ _ _ (Ind.mapEquiv (extIndLeftInd k φ₁₂ hφ₁₂ M N P)
    (Ind.tmul (φ := ψ) z (ExtTensor.tmul (k := k)
      (P := IndK k (ExtTensor k M N) φ₁₂)
      (Ind.tmul (φ := φ₁₂) w (ExtTensor.tmul m n)) p))) = _
  rw [Ind.mapEquiv_tmul]
  change compEquiv _ _ _ (Ind.tmul (φ := ψ) z
    (extIndLeft k A₃ φ₁₂ hφ₁₂ (ExtTensor k M N) P
      (ExtTensor.tmul (k := k) (P := IndK k (ExtTensor k M N) φ₁₂)
        (Ind.tmul (φ := φ₁₂) w (ExtTensor.tmul m n)) p))) = _
  rw [extIndLeft_tmul_tmul, compEquiv_tmul_tmul]

/-- The inverse right comparison on the nested unit tensor. -/
theorem indAssocRight_symm_unit (m : M) (n : N) (p : P) :
    (indAssocRight k φ₂₃ hφ₂₃ ψ' M N P).symm (indAssocUnit k φ₂₃ ψ' m n p) =
      Ind.tmul (φ := ψ'.comp (tensorRight k A₁ φ₂₃ hφ₂₃))
        (unitGen (ψ'.comp (tensorRight k A₁ φ₂₃ hφ₂₃)))
        (ExtTensor.tmul m (ExtTensor.tmul n p)) := by
  change compEquiv _ _ _ (Ind.mapEquiv (extIndRightInd k φ₂₃ hφ₂₃ M N P)
    (Ind.tmul (φ := ψ') (unitGen ψ') (ExtTensor.tmul (k := k)
      (Q := IndK k (ExtTensor k N P) φ₂₃) m
      (Ind.tmul (φ := φ₂₃) (unitGen φ₂₃) (ExtTensor.tmul n p))))) = _
  rw [Ind.mapEquiv_tmul]
  change compEquiv _ _ _ (Ind.tmul (φ := ψ') (unitGen ψ')
    (extIndRight k A₁ φ₂₃ hφ₂₃ (ExtTensor k N P) M
      (ExtTensor.tmul (k := k) (Q := IndK k (ExtTensor k N P) φ₂₃) m
        (Ind.tmul (φ := φ₂₃) (unitGen φ₂₃) (ExtTensor.tmul n p))))) = _
  rw [extIndRight_tmul_tmul, compEquiv_tmul_tmul]
  congr 1
  apply Subtype.ext
  change ψ' 1 * ψ' ((1 : A₁) ⊗ₜ[k] φ₂₃ 1) = ψ' ((1 : A₁) ⊗ₜ[k] φ₂₃ 1)
  rw [← map_mul, one_mul]

/-- Undo the right comparison in the definition of the associator. Keeping the
input abstract avoids unfolding nested tensor-module structures. -/
theorem indAssocRight_symm_indAssoc
    (x : IndK k (ExtTensor k (IndK k (ExtTensor k M N) φ₁₂) P) ψ) :
    (indAssocRight k φ₂₃ hφ₂₃ ψ' M N P).symm
      (indAssoc k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc M N P x) =
      Ind.transport (Algebra.TensorProduct.assoc k k k A₁ A₂ A₃).toRingEquiv c.toRingEquiv
        (assoc_intertwines k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc)
        (extAssoc k M N P) (extAssoc_smul k M N P)
        (indAssocLeft k φ₁₂ hφ₁₂ ψ M N P x) := by
  exact (indAssocRight k φ₂₃ hφ₂₃ ψ' M N P).symm_apply_apply _

/-- The induction associator on pure tensors. The coefficient is moved to the
outside, leaving only degree-zero induction units on the inside. -/
theorem indAssoc_pure (z : Corner ψ) (w : Corner φ₁₂) (m : M) (n : N) (p : P) :
    indAssoc k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc M N P
      (IndK.tmul (k := k) (φ := ψ) z
        (ExtTensor.tmul (k := k) (P := IndK k (ExtTensor k M N) φ₁₂)
          (IndK.tmul (k := k) (φ := φ₁₂) w (ExtTensor.tmul m n)) p)) =
      c (z.1 * ψ (w.1 ⊗ₜ[k] (1 : A₃))) •
        indAssocUnit k φ₂₃ ψ' m n p := by
  let E := indAssocRight k φ₂₃ hφ₂₃ ψ' M N P
  have hsmul := E.symm.map_smul (c (z.1 * ψ (w.1 ⊗ₜ[k] (1 : A₃))))
    (indAssocUnit k φ₂₃ ψ' m n p)
  apply E.symm.injective
  refine (indAssocRight_symm_indAssoc k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc _).trans
    (Eq.trans ?_ hsmul.symm)
  change _ = c (z.1 * ψ (w.1 ⊗ₜ[k] (1 : A₃))) •
    (indAssocRight k φ₂₃ hφ₂₃ ψ' M N P).symm (indAssocUnit k φ₂₃ ψ' m n p)
  rw [indAssocRight_symm_unit, indAssocLeft_pure, Ind.transport_tmul,
    extAssoc_tmul_tmul, Ind.smul_tmul]
  congr 1
  apply Subtype.ext
  exact (transportCorner (Algebra.TensorProduct.assoc k k k A₁ A₂ A₃).toRingEquiv
    c.toRingEquiv (assoc_intertwines k φ₁₂ hφ₁₂ φ₂₃ hφ₂₃ ψ ψ' c hc)
    (compMul (tensorLeft k A₃ φ₁₂ hφ₁₂) ψ z (leftCorner w))).2.symm

end AssociatorTensors

end Categorification.InductionAlong
