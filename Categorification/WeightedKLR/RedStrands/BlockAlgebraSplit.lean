/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceBlockAlgebra
import Categorification.Algebra.PiTensorProductSnoc

/-!
# The block algebra of `ℓ + 1` red strands as a tensor product

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Proposition 5.3 and proof of Proposition 5.5. The block algebra
`B = R(b_0) ⊗ R^{λ_1}(b_1) ⊗ ⋯ ⊗ R^{λ_{ℓ+1}}(b_{ℓ+1})` of `ℓ + 1` red strands is the tensor product
`B' ⊗ R^{λ_{ℓ+1}}(b_{ℓ+1})` of the block algebra of the first `ℓ` red strands and the last factor
(`blockSplit`), the inverse being `x ⊗ y ↦ x · y` through `initBlockAlgHom` and
`lastBlockAlgHom` (`blockSplit_initBlockAlgHom`, `blockSplit_lastBlockAlgHom`,
`blockSplit_symm_tmul`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR
open scoped TensorProduct

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (b : Fin (ℓ + 2) → Multiset I)

local notation "B" => BlockAlgebra k Q Λ b
local notation "B'" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b)
local notation "Cyc" => CycKLR k Q (redCyc Λ (Fin.last ℓ)) (rightBlock b (Fin.last ℓ))
local notation "Fac" => fun r : Fin (ℓ + 1) => CycKLR k Q (redCyc Λ r) (rightBlock b r)

/-- **The block algebra of `ℓ + 1` red strands as `B' ⊗ R^{λ_{ℓ+1}}(b_{ℓ+1})`.** -/
def blockSplit : B ≃ₐ[k] B' ⊗[k] Cyc :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : KLRAlgebra k Q (leftBlock b) ≃ₐ[k] _)
    (PiTensorProduct.snocAlgEquiv k Fac)).trans
    (Algebra.TensorProduct.assoc k k k (KLRAlgebra k Q (leftBlock b))
      (⨂[k] j : Fin ℓ, CycKLR k Q (redCyc Λ j.castSucc) (rightBlock b j.castSucc)) Cyc).symm

theorem blockSplit_tmul_tprod (a : KLRAlgebra k Q (leftBlock b))
    (f : ∀ r : Fin (ℓ + 1), CycKLR k Q (redCyc Λ r) (rightBlock b r)) :
    blockSplit Q Λ b (a ⊗ₜ PiTensorProduct.tprod k f) =
      (a ⊗ₜ PiTensorProduct.tprod k (fun j : Fin ℓ => f j.castSucc) : B') ⊗ₜ f (Fin.last ℓ) := by
  rw [blockSplit, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  erw [PiTensorProduct.snocAlgEquiv_tprod]
  rfl

theorem mulSingle_castSucc_comp (j : Fin ℓ) (c : CycKLR k Q (redCyc Λ j.castSucc)
    (rightBlock b j.castSucc)) :
    (fun j' : Fin ℓ => (Pi.mulSingle (M := Fac) j.castSucc c) j'.castSucc) =
      Pi.mulSingle (M := fun j : Fin ℓ => CycKLR k Q (redCyc Λ j.castSucc)
        (rightBlock b j.castSucc)) j c := by
  funext j'
  by_cases h : j' = j
  · subst h
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne (fun h' => h (Fin.castSucc_injective _ h')),
      Pi.mulSingle_eq_of_ne h]

/-- **`B' → B ≅ B' ⊗ R^{λ_{ℓ+1}}(b_{ℓ+1})` is `x ↦ x ⊗ 1`.** -/
theorem blockSplit_comp_initBlockAlgHom :
    (blockSplit Q Λ b).toAlgHom.comp (initBlockAlgHom Q Λ b) =
      Algebra.TensorProduct.includeLeft := by
  apply Algebra.TensorProduct.ext
  · refine AlgHom.ext fun a => ?_
    change blockSplit Q Λ b (initBlockAlgHom Q Λ b (a ⊗ₜ 1)) = (a ⊗ₜ 1 : B') ⊗ₜ 1
    rw [initBlockAlgHom_tmul_one, PiTensorProduct.one_def, blockSplit_tmul_tprod]
    rfl
  · apply PiTensorProduct.algHom_ext
    intro j
    refine AlgHom.ext fun c => ?_
    change blockSplit Q Λ b (initBlockAlgHom Q Λ b (1 ⊗ₜ PiTensorProduct.singleAlgHom (R := k)
        (A := fun r : Fin ℓ =>
          CycKLR k Q (redCyc (Λ ∘ Fin.castSucc) r) (rightBlock (initBlocks b) r)) j c)) =
      (1 ⊗ₜ PiTensorProduct.singleAlgHom (R := k) (A := fun r : Fin ℓ =>
          CycKLR k Q (redCyc (Λ ∘ Fin.castSucc) r) (rightBlock (initBlocks b) r)) j c : B') ⊗ₜ 1
    rw [initBlockAlgHom_one_tmul_single]
    erw [PiTensorProduct.singleAlgHom_apply, blockSplit_tmul_tprod]
    simp only [MonoidHom.mulSingle_apply]
    erw [Pi.mulSingle_eq_of_ne (Fin.castSucc_lt_last j).ne', mulSingle_castSucc_comp Q Λ b j c]
    rfl

theorem blockSplit_initBlockAlgHom (x : B') :
    blockSplit Q Λ b (initBlockAlgHom Q Λ b x) = x ⊗ₜ 1 :=
  AlgHom.congr_fun (blockSplit_comp_initBlockAlgHom Q Λ b) x

/-- **`R^{λ_{ℓ+1}}(b_{ℓ+1}) → B ≅ B' ⊗ R^{λ_{ℓ+1}}(b_{ℓ+1})` is `y ↦ 1 ⊗ y`.** -/
theorem blockSplit_lastBlockAlgHom (y : Cyc) :
    blockSplit Q Λ b (lastBlockAlgHom Q Λ b y) = 1 ⊗ₜ y := by
  rw [lastBlockAlgHom_apply]
  erw [PiTensorProduct.singleAlgHom_apply, blockSplit_tmul_tprod]
  simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
  congr 1
  change (1 : KLRAlgebra k Q (leftBlock b)) ⊗ₜ PiTensorProduct.tprod k _ = 1 ⊗ₜ
    PiTensorProduct.tprod k 1
  congr 2
  funext j
  exact Pi.mulSingle_eq_of_ne (Fin.castSucc_lt_last j).ne _

theorem blockSplit_symm_tmul (x : B') (y : Cyc) :
    (blockSplit Q Λ b).symm (x ⊗ₜ y) = initBlockAlgHom Q Λ b x * lastBlockAlgHom Q Λ b y := by
  apply (blockSplit Q Λ b).injective
  rw [AlgEquiv.apply_symm_apply, map_mul, blockSplit_initBlockAlgHom, blockSplit_lastBlockAlgHom,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end StendhalAlgebra

end Categorification.Stendhal
