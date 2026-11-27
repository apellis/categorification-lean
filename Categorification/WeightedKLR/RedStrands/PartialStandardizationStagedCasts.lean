/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationStagedBlocks
import Categorification.WeightedKLR.RedStrands.TwoPieceStandardizationNatural
import Categorification.WeightedKLR.RedStrands.PartialStandardizationCutTransfer

/-!
# Weights and spectators for the comparison of the staged standardization

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Definition 5.4. Auxiliary statements for the comparison of the standardization in stages with
singleton blocks (`singStd`) with the standardization of Definition 5.4:

* `singWeight_eq_blockPrefix`: for blocks with `b_0 = 0`, the weight `b_1 + ⋯ + b_n` of the
  singleton blocks is the black weight of the blocks;
* `leftStandardizationWeightCast`: the standardization does not depend on the presentation of
  the black weight;
* `initSpectatorAction`: a spectator action on a right module over the block algebra, together
  with the last factor, acting on its restriction to the first red strands.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR MulOpposite StendhalAlgebra
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)

omit [DecidableEq I] in
/-- **The weight of the singleton blocks** `b_1 + ⋯ + b_n` is the black weight of the blocks
`b_0, …, b_n` when `b_0 = 0`. -/
theorem singWeight_eq_blockPrefix : (n : ℕ) → (b : Fin (n + 1) → Multiset I) →
    leftBlock b = 0 → singWeight n (b ∘ Fin.succ) = blockPrefix b (n + 1)
  | 0, b, hb0 => by
    rw [show blockPrefix b 1 = b 0 by simp [blockPrefix]]
    exact hb0.symm
  | n + 1, b, hb0 => by
    change singWeight n (initBlocks b ∘ Fin.succ) + lastBlock b = _
    rw [singWeight_eq_blockPrefix n (initBlocks b) hb0, blockPrefix_last]

section WeightCast

variable {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {b : Fin (ℓ + 1) → Multiset I} {ν ν' : Multiset I}
  (hb : blockPrefix b (ℓ + 1) = ν) (hb' : blockPrefix b (ℓ + 1) = ν')
  (hα : RootNonViolated (ν := ν) (blockRoot b)) (hα' : RootNonViolated (ν := ν') (blockRoot b))
  (M : Type*) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]

omit [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] in
/-- **The standardization along two presentations of the black weight.** -/
def leftStandardizationWeightCast :
    LeftStandardization Q Λ b hb hα M ≃ₗ[k] LeftStandardization Q Λ b hb' hα' M := by
  subst hb hb'
  exact LinearEquiv.refl k _

omit [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] in
theorem leftStandardizationWeightCast_smul (t : TensorProductAlgebra k Q Λ ν)
    (y : LeftStandardization Q Λ b hb hα M) :
    leftStandardizationWeightCast Q hb hb' hα hα' M (t • y) =
      castTensorProductAlgebra Q Λ (hb.symm.trans hb') t •
        leftStandardizationWeightCast Q hb hb' hα hα' M y := by
  subst hb hb'
  rfl

theorem leftStandardizationWeightCast_mapRight (g : M →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M)
    (y : LeftStandardization Q Λ b hb hα M) :
    leftStandardizationWeightCast Q hb hb' hα hα' M
        (BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ ν)
          (M := BlockLeftStandard Q Λ b hb hα) g y) =
      BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ ν')
        (M := BlockLeftStandard Q Λ b hb' hα') g
        (leftStandardizationWeightCast Q hb hb' hα hα' M y) := by
  subst hb hb'
  rfl

end WeightCast

variable {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) in
theorem castTensorProductAlgebra_trans {ν₁ ν₂ ν₃ : Multiset I} (h₁ : ν₁ = ν₂) (h₂ : ν₂ = ν₃)
    (t : TensorProductAlgebra k Q Λ ν₁) :
    castTensorProductAlgebra Q Λ h₂ (castTensorProductAlgebra Q Λ h₁ t) =
      castTensorProductAlgebra Q Λ (h₁.trans h₂) t := by
  subst h₁ h₂
  rfl

section Spectator

variable (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (b : Fin (n + 2) → Multiset I)

local notation "𝔹" => BlockAlgebra k Q Λ b
local notation "B'" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b)
local notation "Cyc" => CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last n) i)
  (lastBlock b)

/-- The last singleton block as the cyclotomic quotient (Theorem 4.20 for one red strand). -/
def singLastCyc : singLast Q Λ (b ∘ Fin.succ) →ₐ[k] Cyc :=
  (SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => Λ (Fin.last n)) (lastBlock b)).symm.toAlgHom.comp
    (tensorProductAlgebraCast Q (natAdd_last_label Λ) (b (Fin.last n).succ)).toAlgHom

theorem singLastBlockHom_eq (c : singLast Q Λ (b ∘ Fin.succ)) :
    singLastBlockHom Q n Λ b c =
      op (lastBlockAlgHom Q Λ b (CycKLR.flip _ _ (singLastCyc Q n Λ b c))) := rfl

variable (M : Type*) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]

/-- The right action of the last factor on the restriction to the first red strands, as a map
of algebras. -/
def lastFactorEndAlg : Cyc →ₐ[k] Module.End B'ᵐᵒᵖ (InitRestrict Q Λ b M) where
  toFun := lastFactorEnd Q Λ b
  map_one' := lastFactorEnd_one Q Λ b
  map_mul' := lastFactorEnd_mul Q Λ b
  map_zero' := by
    have := lastFactorEnd_add Q Λ b (M := M) (0 : Cyc) 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  map_add' := lastFactorEnd_add Q Λ b
  commutes' c := by
    refine LinearMap.ext fun m => ?_
    obtain ⟨m, rfl⟩ := (initRestrictOf Q Λ b).surjective m
    rw [lastFactorEnd_of, Algebra.algebraMap_eq_smul_one, CycKLR.flip_smul_one_last,
      map_smul (lastBlockAlgHom Q Λ b), map_one (lastBlockAlgHom Q Λ b), MulOpposite.op_smul,
      op_one, smul_assoc, one_smul, map_smul (initRestrictOf Q Λ b), Module.algebraMap_end_apply]

/-- Endomorphisms of `M` over the block algebra, restricted to the first red strands. -/
def initRestrictEndAlg : Module.End 𝔹ᵐᵒᵖ M →ₐ[k] Module.End B'ᵐᵒᵖ (InitRestrict Q Λ b M) where
  toFun := initRestrictEnd Q Λ b
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable {M} (E : AlgCat.{0} k) (ρ : E →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)

/-- **The spectator of the first stage**: the last singleton block, acting through the last
factor, and the spectator `E`, acting on the restriction of `M` to the first red strands. -/
def initSpectatorAction :
    (AlgCat.of k (singLast Q Λ (b ∘ Fin.succ) ⊗[k] E) : AlgCat.{0} k) →ₐ[k]
      Module.End B'ᵐᵒᵖ (InitRestrict Q Λ b M) :=
  Algebra.TensorProduct.lift ((lastFactorEndAlg Q n Λ b M).comp (singLastCyc Q n Λ b))
    ((initRestrictEndAlg Q n Λ b M).comp ρ) fun c e =>
      LinearMap.ext fun m => LinearMap.congr_fun
        (lastFactorEnd_comp_initRestrictEnd Q Λ b (ρ e) (singLastCyc Q n Λ b c)) m

theorem initSpectatorAction_tmul (c : singLast Q Λ (b ∘ Fin.succ)) (e : E) :
    initSpectatorAction Q n Λ b E ρ (c ⊗ₜ e) =
      lastFactorEnd Q Λ b (singLastCyc Q n Λ b c) * initRestrictEnd Q Λ b (ρ e) :=
  Algebra.TensorProduct.lift_tmul _ _ _ c e

end Spectator

end Categorification.Stendhal
