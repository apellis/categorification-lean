/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiFiltrationStatement
import Categorification.WeightedKLR.RedStrands.BlockAlgebraSplit
import Categorification.WeightedKLR.RedStrands.EiInductionAction
import Categorification.Algebra.InductionAlongTensorFactorAction
import Categorification.Algebra.InductionAlongTransportNaturality

/-!
# `ₖFᵢ` commutes with restriction to the first red strands

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. Let `b'` be blocks of `ℓ + 1` red strands and `b` the blocks with one
black strand of colour `i` added to the block `κ + 1`, `κ < ℓ`. Through the splittings
`B(b') ≅ B'(b') ⊗ R^{λ_{ℓ+1}}(b'_{ℓ+1})` and `B(b) ≅ B'(b) ⊗ R^{λ_{ℓ+1}}(b'_{ℓ+1})` of the block
algebras (`blockSplit`), the map `B(b') → B(b)` of `ₖFᵢ` is `ₖFᵢ ⊗ 1`
(`splitBig_blockBlackRes`). Hence, for a right `B(b')`-module `M`, induction along it is
induction along `B'(b') → B'(b)` of the restriction of `M` (`initBlackIndEquiv`).
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
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (κ : Fin ℓ)
  {b b' : Fin (ℓ + 2) → Multiset I} (h0 : leftBlock b' = leftBlock b)
  (hr : ∀ r, r ≠ κ.castSucc → rightBlock b' r = rightBlock b r)
  (hκ : {i} + rightBlock b' κ.castSucc = rightBlock b κ.castSucc)

local notation "E" => blockBlackRes Q Λ i κ.castSucc h0 hr hκ
local notation "E₁" => initBlockBlackRes Q Λ i κ h0 hr hκ
local notation "Cyc'" => CycKLR k Q (redCyc Λ (Fin.last ℓ)) (rightBlock b' (Fin.last ℓ))
local notation "B₁" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b)
local notation "B₁'" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b')

omit [DecidableEq I] in
theorem lastBlock_eq_of_castSucc {b b' : Fin (ℓ + 2) → Multiset I} {κ : Fin ℓ}
    (hr : ∀ r, r ≠ κ.castSucc → rightBlock b' r = rightBlock b r) :
    rightBlock b' (Fin.last ℓ) = rightBlock b (Fin.last ℓ) :=
  hr _ (ne_of_gt (Fin.castSucc_lt_last κ))

theorem castCyc_symm_castCyc {a : I → Polynomial k} {β δ : Multiset I} (h : β = δ)
    (y : CycKLR k Q a β) :
    CyclotomicAction.castCyc Q a h.symm (CyclotomicAction.castCyc Q a h y) = y := by
  subst h
  rfl

/-- The splitting of the block algebra of `b`, with last factor that of `b'`. -/
def splitBig : BlockAlgebra k Q Λ b ≃ₐ[k] B₁ ⊗[k] Cyc' :=
  (blockSplit Q Λ b).trans (Algebra.TensorProduct.congr AlgEquiv.refl
    (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ))
      (lastBlock_eq_of_castSucc hr).symm))

theorem splitBig_initBlockAlgHom (x : B₁) :
    splitBig Q Λ κ hr (initBlockAlgHom Q Λ b x) = x ⊗ₜ 1 := by
  rw [splitBig, AlgEquiv.trans_apply, blockSplit_initBlockAlgHom,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  change x ⊗ₜ[k] (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ)) _) 1 = x ⊗ₜ[k] 1
  rw [map_one]

theorem splitBig_lastBlockAlgHom (y : Cyc') :
    splitBig Q Λ κ hr (lastBlockAlgHom Q Λ b (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ))
      (lastBlock_eq_of_castSucc hr) y)) = 1 ⊗ₜ y := by
  rw [splitBig, AlgEquiv.trans_apply, blockSplit_lastBlockAlgHom,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  change (1 : B₁) ⊗ₜ[k] _ = 1 ⊗ₜ[k] y
  congr 1
  exact castCyc_symm_castCyc Q (lastBlock_eq_of_castSucc hr) y

theorem blockBlackRes_one_eq_init : E 1 = initBlockAlgHom Q Λ b (E₁ 1) := by
  conv_lhs => rw [← map_one (initBlockAlgHom Q Λ b')]
  exact (initBlockAlgHom_blockBlackRes_castSucc Q Λ i κ h0 hr hκ 1).symm

/-- **`ₖFᵢ` on the split block algebras is `ₖFᵢ ⊗ 1`.** -/
theorem splitBig_blockBlackRes (x : B₁') (y : Cyc') :
    splitBig Q Λ κ hr (E (initBlockAlgHom Q Λ b' x * lastBlockAlgHom Q Λ b' y)) = E₁ x ⊗ₜ y := by
  rw [map_mul (E), ← initBlockAlgHom_blockBlackRes_castSucc,
    blockBlackRes_lastBlockAlgHom_castSucc, blockBlackRes_one_eq_init, map_mul, map_mul,
    splitBig_initBlockAlgHom, splitBig_lastBlockAlgHom, splitBig_initBlockAlgHom,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  simp only [mul_one, one_mul]
  rw [← map_mul (E₁), mul_one]

/-- The splitting of the opposite block algebra of `b'`. -/
def splitSmallOp : (BlockAlgebra k Q Λ b')ᵐᵒᵖ ≃ₐ[k] B₁'ᵐᵒᵖ ⊗[k] Cyc'ᵐᵒᵖ :=
  (AlgEquiv.op (blockSplit Q Λ b')).trans (Algebra.TensorProduct.opAlgEquiv k k B₁' Cyc').symm

/-- The splitting of the opposite block algebra of `b`, with last factor that of `b'`. -/
def splitBigOp : (BlockAlgebra k Q Λ b)ᵐᵒᵖ ≃ₐ[k] B₁ᵐᵒᵖ ⊗[k] Cyc'ᵐᵒᵖ :=
  (AlgEquiv.op (splitBig Q Λ κ hr)).trans (Algebra.TensorProduct.opAlgEquiv k k B₁ Cyc').symm

theorem splitSmallOp_op (x : B₁') (y : Cyc') :
    splitSmallOp Q Λ (b' := b') (op (initBlockAlgHom Q Λ b' x * lastBlockAlgHom Q Λ b' y)) =
      op x ⊗ₜ op y := by
  change (Algebra.TensorProduct.opAlgEquiv k k B₁' Cyc').symm
    (op (blockSplit Q Λ b' (initBlockAlgHom Q Λ b' x * lastBlockAlgHom Q Λ b' y))) = _
  rw [← blockSplit_symm_tmul, AlgEquiv.apply_symm_apply,
    Algebra.TensorProduct.opAlgEquiv_symm_tmul]

theorem splitSmallOp_symm_tmul (x : B₁') (y : Cyc') :
    (splitSmallOp Q Λ (b' := b')).symm (op x ⊗ₜ op y) =
      op (initBlockAlgHom Q Λ b' x * lastBlockAlgHom Q Λ b' y) := by
  rw [AlgEquiv.symm_apply_eq, splitSmallOp_op]

/-- `ₖFᵢ ⊗ 1` on the split opposite algebras. -/
abbrev splitRes : @NonUnitalRingHom (B₁'ᵐᵒᵖ ⊗[k] Cyc'ᵐᵒᵖ) (B₁ᵐᵒᵖ ⊗[k] Cyc'ᵐᵒᵖ)
    Ring.toNonAssocRing.toNonUnitalNonAssocSemiring
    Ring.toNonAssocRing.toNonUnitalNonAssocSemiring :=
  tensorLeft k Cyc'ᵐᵒᵖ (blockBlackResOp Q (Λ ∘ Fin.castSucc) i κ (b := initBlocks b)
    (b' := initBlocks b') h0 (initBlocks_rightBlock_of_ne κ hr) hκ)
    (blockBlackResOp_smul Q (Λ ∘ Fin.castSucc) i κ h0 (initBlocks_rightBlock_of_ne κ hr) hκ)

/-- **The splittings intertwine `ₖFᵢ` with `ₖFᵢ ⊗ 1`.** -/
theorem splitRes_splitSmallOp (t : (BlockAlgebra k Q Λ b')ᵐᵒᵖ) :
    splitRes Q Λ i κ h0 hr hκ (splitSmallOp Q Λ t) =
      splitBigOp Q Λ κ hr (blockBlackResOp Q Λ i κ.castSucc h0 hr hκ t) := by
  obtain ⟨x, rfl⟩ := MulOpposite.op_surjective t
  obtain ⟨s, rfl⟩ := (blockSplit Q Λ b').symm.surjective x
  induction s using TensorProduct.inductionOn with
  | tmul x y =>
    rw [blockSplit_symm_tmul, splitSmallOp_op, tensorLeft_tmul]
    change _ = (Algebra.TensorProduct.opAlgEquiv k k B₁ Cyc').symm
      (op (splitBig Q Λ κ hr (E (initBlockAlgHom Q Λ b' x * lastBlockAlgHom Q Λ b' y))))
    rw [splitBig_blockBlackRes, Algebra.TensorProduct.opAlgEquiv_symm_tmul]
    rfl
  | add s s' hs hs' => rw [map_add, op_add, map_add, map_add, hs, hs', map_add, map_add]

section Module

variable (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b')ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b')ᵐᵒᵖ M]

/-- A right module over the block algebra of `b'` as a module over the split algebra. -/
@[nolint unusedArguments]
def SplitModule (_Q : I → I → MvPolynomial (Fin 2) k) (_Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (_b' : Fin (ℓ + 2) → Multiset I) (M : Type) : Type := M

instance : AddCommGroup (SplitModule Q Λ b' M) := inferInstanceAs (AddCommGroup M)
instance : Module k (SplitModule Q Λ b' M) := inferInstanceAs (Module k M)
instance : Module (B₁'ᵐᵒᵖ ⊗[k] Cyc'ᵐᵒᵖ) (SplitModule Q Λ b' M) :=
  Module.compHom M (splitSmallOp Q Λ (b' := b')).symm.toRingEquiv.toRingHom

theorem splitModule_smul (t : B₁'ᵐᵒᵖ ⊗[k] Cyc'ᵐᵒᵖ) (m : SplitModule Q Λ b' M) :
    t • m = (show SplitModule Q Λ b' M from
      ((splitSmallOp Q Λ (b' := b')).symm t • (show M from m))) := rfl

instance : IsScalarTower k (B₁'ᵐᵒᵖ ⊗[k] Cyc'ᵐᵒᵖ) (SplitModule Q Λ b' M) where
  smul_assoc c t m := by
    change (splitSmallOp Q Λ (b' := b')).symm (c • t) • (show M from m) =
      c • ((splitSmallOp Q Λ (b' := b')).symm t • (show M from m))
    rw [map_smul]
    exact smul_assoc c ((splitSmallOp Q Λ (b' := b')).symm t) (show M from m)

/-- The identity `M → SplitModule M`. -/
def toSplitModule : M ≃+ SplitModule Q Λ b' M := AddEquiv.refl M

theorem toSplitModule_smul (t : (BlockAlgebra k Q Λ b')ᵐᵒᵖ) (m : M) :
    toSplitModule Q Λ (b' := b') M (t • m) =
      (splitSmallOp Q Λ (b' := b')).toRingEquiv t • toSplitModule Q Λ (b' := b') M m := by
  change t • m = (splitSmallOp Q Λ (b' := b')).symm (splitSmallOp Q Λ t) • m
  rw [AlgEquiv.symm_apply_apply]

/-- The restriction of the split module to the first factor is the restriction of `M`. -/
def leftFactorSplitEquiv :
    LeftFactorRes k B₁'ᵐᵒᵖ Cyc'ᵐᵒᵖ (SplitModule Q Λ b' M) ≃ₗ[B₁'ᵐᵒᵖ]
      InitRestrict Q Λ b' M where
  toFun m := initRestrictOf Q Λ b' (show M from m)
  invFun m := (show LeftFactorRes k B₁'ᵐᵒᵖ Cyc'ᵐᵒᵖ (SplitModule Q Λ b' M) from
    (initRestrictOf Q Λ b').symm m)
  map_add' _ _ := rfl
  map_smul' a m := by
    induction a using MulOpposite.rec' with | _ x =>
    rw [RingHom.id_apply, op_smul_initRestrictOf]
    change initRestrictOf Q Λ b' ((splitSmallOp Q Λ (b' := b')).symm (op x ⊗ₜ op 1) •
      (show M from m)) = _
    rw [splitSmallOp_symm_tmul, map_one, mul_one]
  left_inv _ := rfl
  right_inv _ := rfl

local notation "φ₁" => blockBlackResOp Q (Λ ∘ Fin.castSucc) i κ (b := initBlocks b)
  (b' := initBlocks b') h0 (initBlocks_rightBlock_of_ne κ hr) hκ
local notation "φ" => blockBlackResOp Q Λ i κ.castSucc h0 hr hκ

/-- The transport of `ₖFᵢ M` to the split algebras. -/
def splitIndTransport :
    IndK k M φ ≃+ IndK k (SplitModule Q Λ b' M) (splitRes Q Λ i κ h0 hr hκ) :=
  Ind.transport (splitSmallOp Q Λ (b' := b')).toRingEquiv (splitBigOp Q Λ κ hr).toRingEquiv
    (splitRes_splitSmallOp Q Λ i κ h0 hr hκ) (toSplitModule Q Λ (b' := b') M) fun t m => by
      change t • m = (splitSmallOp Q Λ (b' := b')).symm (splitSmallOp Q Λ t) • m
      rw [AlgEquiv.symm_apply_apply]

theorem splitIndTransport_smul (t : (BlockAlgebra k Q Λ b)ᵐᵒᵖ) (w : IndK k M φ) :
    splitIndTransport Q Λ i κ h0 hr hκ M (t • w) =
      splitBigOp Q Λ κ hr t • splitIndTransport Q Λ i κ h0 hr hκ M w :=
  Ind.transport_smul _ _ _ _ _ t w

/-- Induction along `ₖFᵢ ⊗ 1` as induction along `ₖFᵢ` of the first factor. -/
abbrev splitLeftEquiv :
    IndK k (SplitModule Q Λ b' M) (splitRes Q Λ i κ h0 hr hκ) ≃ₗ[k]
      IndK k (LeftFactorRes k B₁'ᵐᵒᵖ Cyc'ᵐᵒᵖ (SplitModule Q Λ b' M)) φ₁ :=
  indLeftFactorEquiv φ₁ (blockBlackResOp_smul Q (Λ ∘ Fin.castSucc) i κ h0
    (initBlocks_rightBlock_of_ne κ hr) hκ) (splitRes Q Λ i κ h0 hr hκ) (fun _ _ => rfl)

theorem splitLeftEquiv_tmul_one_smul (a : B₁ᵐᵒᵖ)
    (w : IndK k (SplitModule Q Λ b' M) (splitRes Q Λ i κ h0 hr hκ)) :
    splitLeftEquiv Q Λ i κ h0 hr hκ M ((a ⊗ₜ 1 : B₁ᵐᵒᵖ ⊗[k] Cyc'ᵐᵒᵖ) • w) =
      a • splitLeftEquiv Q Λ i κ h0 hr hκ M w :=
  indLeftFactorEquiv_tmul_one_smul _ _ _ _ a w

/-- **`ₖFᵢ M ≅ ₖFᵢ(M|_{B'})` as additive groups**, through the splittings. -/
def initIndFwd : IndK k M φ ≃+ IndK k (InitRestrict Q Λ b' M) φ₁ :=
  ((splitIndTransport Q Λ i κ h0 hr hκ M).trans
    (splitLeftEquiv Q Λ i κ h0 hr hκ M).toAddEquiv).trans
    (Ind.mapEquiv (leftFactorSplitEquiv Q Λ M)).toAddEquiv

theorem splitBigOp_op_initBlockAlgHom (x : B₁) :
    splitBigOp Q Λ κ hr (op (initBlockAlgHom Q Λ b x)) = op x ⊗ₜ 1 := by
  change (Algebra.TensorProduct.opAlgEquiv k k B₁ Cyc').symm
    (op (splitBig Q Λ κ hr (initBlockAlgHom Q Λ b x))) = _
  rw [splitBig_initBlockAlgHom, Algebra.TensorProduct.opAlgEquiv_symm_tmul]
  rfl

theorem initIndFwd_smul (x : B₁) (w : IndK k M φ) :
    initIndFwd Q Λ i κ h0 hr hκ M (op (initBlockAlgHom Q Λ b x) • w) =
      op x • initIndFwd Q Λ i κ h0 hr hκ M w := by
  rw [initIndFwd, AddEquiv.trans_apply, AddEquiv.trans_apply, splitIndTransport_smul,
    splitBigOp_op_initBlockAlgHom]
  change Ind.mapEquiv (leftFactorSplitEquiv Q Λ M) (splitLeftEquiv Q Λ i κ h0 hr hκ M
      ((op x ⊗ₜ 1 : B₁ᵐᵒᵖ ⊗[k] Cyc'ᵐᵒᵖ) • splitIndTransport Q Λ i κ h0 hr hκ M w)) =
    op x • Ind.mapEquiv (leftFactorSplitEquiv Q Λ M) (splitLeftEquiv Q Λ i κ h0 hr hκ M
      (splitIndTransport Q Λ i κ h0 hr hκ M w))
  rw [splitLeftEquiv_tmul_one_smul, map_smul]

end Module

end StendhalAlgebra

end Categorification.Stendhal
