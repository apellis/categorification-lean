/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EiFiltrationStatement
import Categorification.WeightedKLR.RedStrands.BlockBlackResMaps
import Categorification.WeightedKLR.RedStrands.TwoPieceLastBlackRes

/-!
# The module of the induction hypothesis in the `Eᵢ`-filtration

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. For a right module `M` over the block algebra `B` of `ℓ + 1` red strands with an
action `ρ` of an algebra `C`, the restriction of `M` to the block algebra `B'` of the first `ℓ`
red strands carries the commuting actions of the last cyclotomic factor (`m ↦ m · flip(c)`) and
of `C`, together an action of `R^{λ_ℓ}(β) ⊗ C` (`inductionAction`); the induction hypothesis is
applied to it. For a block `κ < ℓ`, `ₖEᵢ` of the restriction is the restriction of `ₖEᵢ M`
(`initBlackResEquiv`), compatibly with both actions.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

section Action

variable (b : Fin (ℓ + 2) → Multiset I)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]

local notation "B'" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b)
local notation "Cyc" β => CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) β

/-- The last cyclotomic factor acting on the restriction of `M`, as a map of algebras. -/
def lastFactorEndAlg : (Cyc (lastBlock b)) →ₐ[k] Module.End B'ᵐᵒᵖ (InitRestrict Q Λ b M) where
  toFun := lastFactorEnd Q Λ b
  map_one' := lastFactorEnd_one Q Λ b
  map_mul' := lastFactorEnd_mul Q Λ b
  map_zero' := by
    have := lastFactorEnd_add Q Λ b (M := M) 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  map_add' := lastFactorEnd_add Q Λ b
  commutes' c := LinearMap.ext fun m => by
    obtain ⟨m, rfl⟩ := (initRestrictOf Q Λ b).surjective m
    rw [Module.algebraMap_end_apply, lastFactorEnd_of, Algebra.algebraMap_eq_smul_one,
      CycKLR.flip_smul_one_last, map_smul (lastBlockAlgHom Q Λ b), map_one (lastBlockAlgHom Q Λ b),
      MulOpposite.op_smul, op_one, smul_assoc, one_smul, map_smul (initRestrictOf Q Λ b)]

theorem lastFactorEndAlg_apply (c : Cyc (lastBlock b)) :
    lastFactorEndAlg Q Λ b M c = lastFactorEnd Q Λ b c := rfl

/-- Restriction to the first `ℓ` red strands on endomorphisms, as a map of algebras. -/
def initRestrictEndAlg : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M →ₐ[k]
    Module.End B'ᵐᵒᵖ (InitRestrict Q Λ b M) where
  toFun := initRestrictEnd Q Λ b
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := LinearMap.ext fun m => by
    obtain ⟨m, rfl⟩ := (initRestrictOf Q Λ b).surjective m
    rw [initRestrictEnd_of, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      map_smul (initRestrictOf Q Λ b)]

theorem initRestrictEndAlg_apply (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) :
    initRestrictEndAlg Q Λ b M g = initRestrictEnd Q Λ b g := rfl

variable {β' : Multiset I} (hβ : lastBlock b = β') (C : Type) [Ring C] [Algebra k C]
  (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)

/-- **The action of `R^{λ_ℓ}(β') ⊗ C` on the restriction of `M`**: `c ⊗ x` acts by
`m ↦ ρ(x)(m) · flip(c)`, along `β = β'`. -/
def inductionAction : ((Cyc β') ⊗[k] C) →ₐ[k] Module.End B'ᵐᵒᵖ (InitRestrict Q Λ b M) :=
  Algebra.TensorProduct.lift
    ((lastFactorEndAlg Q Λ b M).comp
      (CyclotomicAction.castCyc Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
        hβ.symm).toAlgHom)
    ((initRestrictEndAlg Q Λ b M).comp ρ)
    fun _ x => (lastFactorEnd_comp_initRestrictEnd Q Λ b (ρ x) _ :)

theorem inductionAction_tmul_one (c : Cyc β') :
    inductionAction Q Λ b M hβ C ρ (c ⊗ₜ 1) = lastFactorEnd Q Λ b
      (CyclotomicAction.castCyc Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
        hβ.symm c) := by
  rw [inductionAction, Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rfl

theorem inductionAction_one_tmul (x : C) :
    inductionAction Q Λ b M hβ C ρ (1 ⊗ₜ x) = initRestrictEnd Q Λ b (ρ x) := by
  rw [inductionAction, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

end Action

section InitBlackRes

variable (i : I) (κ : Fin ℓ) {b b' : Fin (ℓ + 2) → Multiset I} (h0 : leftBlock b' = leftBlock b)
  (hr : ∀ r, r ≠ κ.castSucc → rightBlock b' r = rightBlock b r)
  (hκ : {i} + rightBlock b' κ.castSucc = rightBlock b κ.castSucc)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]

local notation "E" => blockBlackRes Q Λ i κ.castSucc h0 hr hκ
local notation "E₁" => initBlockBlackRes Q Λ i κ h0 hr hκ
local notation "M'" => BlockBlackRes Q Λ i κ.castSucc h0 hr hκ M
local notation "R₁" => BlockBlackRes Q (Λ ∘ Fin.castSucc) i κ (b := initBlocks b)
  (b' := initBlocks b') h0 (initBlocks_rightBlock_of_ne κ hr) hκ (InitRestrict Q Λ b M)
local notation "B₁'" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b')

theorem op_initBlockBlackRes_smul (a : B₁') (m : M) :
    (op (E₁ a) : (BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b))ᵐᵒᵖ) •
        initRestrictOf Q Λ b m =
      initRestrictOf Q Λ b ((op (E (initBlockAlgHom Q Λ b' a)) :
        (BlockAlgebra k Q Λ b)ᵐᵒᵖ) • m) := by
  rw [op_smul_initRestrictOf, initBlockAlgHom_blockBlackRes_castSucc]

/-- The underlying map of `ₖEᵢ(M|_{B'}) ≅ (ₖEᵢ M)|_{B'}`. -/
def initBlackResFun (x : R₁) : M' :=
  Res.mk ((initRestrictOf Q Λ b).symm x.val) (by
    have h := x.prop
    rw [show x.val = initRestrictOf Q Λ b ((initRestrictOf Q Λ b).symm x.val) from
      ((initRestrictOf Q Λ b).apply_symm_apply _).symm] at h
    change (op (E₁ 1) : (BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b))ᵐᵒᵖ) • _ = _ at h
    rw [op_initBlockBlackRes_smul, map_one] at h
    exact (initRestrictOf Q Λ b).injective h)

/-- The underlying map of `(ₖEᵢ M)|_{B'} ≅ ₖEᵢ(M|_{B'})`. -/
def initBlackResInv (y : M') : R₁ :=
  Res.mk (initRestrictOf Q Λ b y.val) (by
    change (op (E₁ 1) : (BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b))ᵐᵒᵖ) • _ = _
    rw [op_initBlockBlackRes_smul, map_one]
    exact congrArg (initRestrictOf Q Λ b) y.prop)

/-- **`ₖEᵢ` commutes with the restriction to the first `ℓ` red strands**, `κ < ℓ`:
`ₖEᵢ(M|_{B'}) ≅ (ₖEᵢ M)|_{B'}` as right modules over the block algebra of `b'`. -/
def initBlackResEquiv : R₁ ≃ₗ[B₁'ᵐᵒᵖ] InitRestrict Q Λ b' M' where
  toFun x := initRestrictOf Q Λ b' (initBlackResFun Q Λ i κ h0 hr hκ M x)
  invFun y := initBlackResInv Q Λ i κ h0 hr hκ M ((initRestrictOf Q Λ b').symm y)
  left_inv x := Res.ext (by
    change initRestrictOf Q Λ b ((initRestrictOf Q Λ b).symm x.val) = x.val
    exact (initRestrictOf Q Λ b).apply_symm_apply _)
  right_inv y := by
    change initRestrictOf Q Λ b' (Res.mk _ _) = y
    obtain ⟨y, rfl⟩ := (initRestrictOf Q Λ b').surjective y
    congr 1
  map_add' x x' := rfl
  map_smul' a x := by
    induction a using MulOpposite.rec' with | _ a =>
    rw [RingHom.id_apply, op_smul_initRestrictOf]
    congr 1
    refine Res.ext ?_
    change (initRestrictOf Q Λ b).symm
        ((op (E₁ a) : (BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b))ᵐᵒᵖ) • x.val) =
      (op (E (initBlockAlgHom Q Λ b' a)) : (BlockAlgebra k Q Λ b)ᵐᵒᵖ) •
        (initRestrictOf Q Λ b).symm x.val
    obtain ⟨m, hm⟩ := (initRestrictOf Q Λ b).surjective x.val
    rw [← hm, op_initBlockBlackRes_smul, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]

theorem initBlackResEquiv_val (x : R₁) :
    ((initRestrictOf Q Λ b').symm (initBlackResEquiv Q Λ i κ h0 hr hκ M x)).val =
      (initRestrictOf Q Λ b).symm x.val := rfl

/-- **Naturality of `initBlackResEquiv`** in endomorphisms of `M`. -/
theorem initBlackResEquiv_natural (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) (x : R₁) :
    initBlackResEquiv Q Λ i κ h0 hr hκ M (Res.map (initRestrictEnd Q Λ b g) x) =
      initRestrictEnd Q Λ b' (Res.map g) (initBlackResEquiv Q Λ i κ h0 hr hκ M x) := rfl

theorem op_blockBlackRes_one_smul_of_mem (x : R₁) :
    (op (E 1) : (BlockAlgebra k Q Λ b)ᵐᵒᵖ) • (initRestrictOf Q Λ b).symm x.val =
      (initRestrictOf Q Λ b).symm x.val :=
  (initBlackResFun Q Λ i κ h0 hr hκ M x).prop

/-- **`initBlackResEquiv` intertwines the actions of the last cyclotomic factor.** -/
theorem initBlackResEquiv_lastFactorEnd
    (d : CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
      (lastBlock b')) (x : R₁) :
    initBlackResEquiv Q Λ i κ h0 hr hκ M (Res.map (lastFactorEnd Q Λ b
        (CyclotomicAction.castCyc Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
          (hr (Fin.last ℓ) (Fin.castSucc_lt_last κ).ne') d)) x) =
      lastFactorEnd Q Λ b' d (initBlackResEquiv Q Λ i κ h0 hr hκ M x) := by
  apply (initRestrictOf Q Λ b').symm.injective
  apply Res.ext
  have hfix := op_blockBlackRes_one_smul_of_mem Q Λ i κ h0 hr hκ M x
  obtain ⟨m, hm⟩ := (initRestrictOf Q Λ b).surjective x.val
  change (initRestrictOf Q Λ b).symm (lastFactorEnd Q Λ b _ x.val) =
    (op (E (lastBlockAlgHom Q Λ b' (CycKLR.flip _ _ d))) : (BlockAlgebra k Q Λ b)ᵐᵒᵖ) •
      (initRestrictOf Q Λ b).symm x.val
  rw [← hm] at hfix ⊢
  rw [lastFactorEnd_of, LinearEquiv.symm_apply_apply] at *
  rw [blockBlackRes_lastBlockAlgHom_castSucc, op_mul, mul_smul,
    ← mul_smul (op (E 1) : (BlockAlgebra k Q Λ b)ᵐᵒᵖ), ← op_mul,
    ← (commute_blockBlackRes_one_lastBlockAlgHom_castSucc Q Λ i κ h0 hr hκ _).eq, op_mul,
    mul_smul, LinearEquiv.symm_apply_apply, hfix]
  exact congrArg (fun z => (op (lastBlockAlgHom Q Λ b z) : (BlockAlgebra k Q Λ b)ᵐᵒᵖ) • m)
    (cycFlip_castCyc _ _ d)

end InitBlackRes

end StendhalAlgebra

end Categorification.Stendhal
