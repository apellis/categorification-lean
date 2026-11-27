/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiFiltrationStatement
import Categorification.WeightedKLR.RedStrands.BlockAlgebraSplit
import Categorification.WeightedKLR.RedStrands.EiInductionAction
import Categorification.Algebra.InductionAlongTensorFactorAction
import Categorification.Algebra.InductionAlongTransportNaturality
import Categorification.Algebra.InductionAlongTensorSplit

/-!
# `ₖFᵢ` commutes with restriction to the first red strands

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. Let `b'` be blocks of `ℓ + 1` red strands and `b` the blocks with one
black strand of colour `i` added to the block `κ + 1`, `κ < ℓ`. Through the splittings
`B(b') ≅ B'(b') ⊗ R^{λ_{ℓ+1}}(b'_{ℓ+1})` and `B(b) ≅ B'(b) ⊗ R^{λ_{ℓ+1}}(b'_{ℓ+1})` of the block
algebras (`blockSplit`), the map `B(b') → B(b)` of `ₖFᵢ` is `ₖFᵢ ⊗ 1`
(`splitBig_blockBlackRes`). Hence, for a right `B(b')`-module `M`, induction along it is
induction along `B'(b') → B'(b)` of the restriction of `M` (`initBlackIndEquiv`), naturally in
`M` (`initBlackIndEquiv_natural`) and compatibly with the last cyclotomic factor
(`initBlackIndEquiv_lastFactorEnd`).
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

local notation "φ₁" => blockBlackResOp Q (Λ ∘ Fin.castSucc) i κ (b := initBlocks b)
  (b' := initBlocks b') h0 (initBlocks_rightBlock_of_ne κ hr) hκ
local notation "φ" => blockBlackResOp Q Λ i κ.castSucc h0 hr hκ

theorem initRestrictOf_splitSmallOp_symm_tmul_one (x : B₁'ᵐᵒᵖ) (m : M) :
    initRestrictOf Q Λ b' ((splitSmallOp Q Λ (b' := b')).symm
      ((x ⊗ₜ (1 : Cyc'ᵐᵒᵖ) : B₁'ᵐᵒᵖ ⊗[k] Cyc'ᵐᵒᵖ)) • m) = x • initRestrictOf Q Λ b' m := by
  induction x using MulOpposite.rec' with | _ x =>
  rw [op_smul_initRestrictOf, show (1 : Cyc'ᵐᵒᵖ) = op 1 from rfl, splitSmallOp_symm_tmul,
    map_one, mul_one]

/-- **`ₖFᵢ M ≅ ₖFᵢ(M|_{B'})` as additive groups**, through the splittings. -/
def initIndFwd : IndK k M φ ≃+ IndK k (InitRestrict Q Λ b' M) φ₁ :=
  splitInd (splitSmallOp Q Λ (b' := b')) (splitBigOp Q Λ κ hr) φ φ₁
    (blockBlackResOp_smul Q (Λ ∘ Fin.castSucc) i κ h0 (initBlocks_rightBlock_of_ne κ hr) hκ)
    (splitRes_splitSmallOp Q Λ i κ h0 hr hκ) (initRestrictOf Q Λ b' (M := M)).toAddEquiv
    (initRestrictOf_splitSmallOp_symm_tmul_one Q Λ M)

theorem splitBigOp_op_initBlockAlgHom (x : B₁) :
    splitBigOp Q Λ κ hr (op (initBlockAlgHom Q Λ b x)) = op x ⊗ₜ 1 := by
  change (Algebra.TensorProduct.opAlgEquiv k k B₁ Cyc').symm
    (op (splitBig Q Λ κ hr (initBlockAlgHom Q Λ b x))) = _
  rw [splitBig_initBlockAlgHom, Algebra.TensorProduct.opAlgEquiv_symm_tmul]
  rfl

/-- **`initIndFwd` is linear over the first `ℓ` red strands.** -/
theorem initIndFwd_smul (x : B₁) (w : IndK k M φ) :
    initIndFwd Q Λ i κ h0 hr hκ M (op (initBlockAlgHom Q Λ b x) • w) =
      op x • initIndFwd Q Λ i κ h0 hr hκ M w := by
  rw [← (splitBigOp Q Λ κ hr).symm_apply_apply (op (initBlockAlgHom Q Λ b x)),
    splitBigOp_op_initBlockAlgHom]
  exact splitInd_smul _ _ _ _ _ _ _ _ (op x) w

/-- **`initIndFwd` is natural** in endomorphisms of `M`. -/
theorem initIndFwd_map (g : Module.End (BlockAlgebra k Q Λ b')ᵐᵒᵖ M) (w : IndK k M φ) :
    initIndFwd Q Λ i κ h0 hr hκ M (IndK.map g w) =
      IndK.map (initRestrictEnd Q Λ b' g) (initIndFwd Q Λ i κ h0 hr hκ M w) :=
  splitInd_map _ _ _ _ _ _ _ _ g (initRestrictEnd Q Λ b' g) (fun _ => rfl) w

theorem splitBigOp_op_lastBlockAlgHom (y : Cyc') :
    splitBigOp Q Λ κ hr (op (lastBlockAlgHom Q Λ b (CyclotomicAction.castCyc Q
      (redCyc Λ (Fin.last ℓ)) (lastBlock_eq_of_castSucc hr) y))) = 1 ⊗ₜ op y := by
  change (Algebra.TensorProduct.opAlgEquiv k k B₁ Cyc').symm
    (op (splitBig Q Λ κ hr (lastBlockAlgHom Q Λ b _))) = _
  rw [splitBig_lastBlockAlgHom, Algebra.TensorProduct.opAlgEquiv_symm_tmul]
  rfl

/-- **`initIndFwd` intertwines the last factors.** -/
theorem initIndFwd_last (z : Cyc') (w : IndK k M φ) :
    initIndFwd Q Λ i κ h0 hr hκ M (op (lastBlockAlgHom Q Λ b
        (CycKLR.flip (redCyc Λ (Fin.last ℓ)) (rightBlock b (Fin.last ℓ))
          (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ)) (lastBlock_eq_of_castSucc hr) z)))
          • w) =
      IndK.map (lastFactorEnd Q Λ b' z) (initIndFwd Q Λ i κ h0 hr hκ M w) := by
  rw [cycFlip_castCyc, ← (splitBigOp Q Λ κ hr).symm_apply_apply (op (lastBlockAlgHom Q Λ b _)),
    splitBigOp_op_lastBlockAlgHom]
  refine splitInd_one_tmul_smul _ _ _ _ _ _ _ _ _ (lastFactorEnd Q Λ b' z) (fun m => ?_) w
  change initRestrictOf Q Λ b' ((splitSmallOp Q Λ (b' := b')).symm
    ((1 : B₁'ᵐᵒᵖ) ⊗ₜ op (CycKLR.flip (redCyc Λ (Fin.last ℓ)) (rightBlock b' (Fin.last ℓ)) z)) •
      m) = _
  rw [show (1 : B₁'ᵐᵒᵖ) = op 1 from rfl, splitSmallOp_symm_tmul, map_one, one_mul]
  rfl

local notation "Fκ" => BlockBlackInd Q Λ i κ.castSucc h0 hr hκ M

theorem initIndFwd_symm_smul (x : B₁) (w : IndK k (InitRestrict Q Λ b' M) φ₁) :
    (initIndFwd Q Λ i κ h0 hr hκ M).symm (op x • w) =
      op (initBlockAlgHom Q Λ b x) • (initIndFwd Q Λ i κ h0 hr hκ M).symm w := by
  apply (initIndFwd Q Λ i κ h0 hr hκ M).injective
  rw [initIndFwd_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- **`ₖFᵢ` commutes with the restriction to the first `ℓ` red strands**, `κ < ℓ`:
`ₖFᵢ(M|_{B'}) ≅ (ₖFᵢ M)|_{B}` as right modules over the block algebra of the first `ℓ` red
strands of `b`. -/
def initBlackIndEquiv :
    IndK k (InitRestrict Q Λ b' M) φ₁ ≃ₗ[B₁ᵐᵒᵖ] InitRestrict Q Λ b Fκ where
  toFun w := initRestrictOf Q Λ b ((initIndFwd Q Λ i κ h0 hr hκ M).symm w)
  invFun y := initIndFwd Q Λ i κ h0 hr hκ M ((initRestrictOf Q Λ b).symm y)
  map_add' w w' := by rw [map_add, map_add]
  map_smul' a w := by
    induction a using MulOpposite.rec' with | _ x =>
    rw [RingHom.id_apply, op_smul_initRestrictOf, initIndFwd_symm_smul]
  left_inv w := by
    change initIndFwd Q Λ i κ h0 hr hκ M ((initRestrictOf Q Λ b).symm
      (initRestrictOf Q Λ b _)) = w
    rw [LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
  right_inv y := by
    change initRestrictOf Q Λ b ((initIndFwd Q Λ i κ h0 hr hκ M).symm
      (initIndFwd Q Λ i κ h0 hr hκ M _)) = y
    rw [AddEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem initBlackIndEquiv_symm_apply (y : InitRestrict Q Λ b Fκ) :
    (initBlackIndEquiv Q Λ i κ h0 hr hκ M).symm y =
      initIndFwd Q Λ i κ h0 hr hκ M ((initRestrictOf Q Λ b).symm y) := rfl

/-- **Naturality of `initBlackIndEquiv`** in endomorphisms of `M`. -/
theorem initBlackIndEquiv_natural (g : Module.End (BlockAlgebra k Q Λ b')ᵐᵒᵖ M)
    (w : IndK k (InitRestrict Q Λ b' M) φ₁) :
    initBlackIndEquiv Q Λ i κ h0 hr hκ M (IndK.map (initRestrictEnd Q Λ b' g) w) =
      initRestrictEnd Q Λ b (IndK.map g) (initBlackIndEquiv Q Λ i κ h0 hr hκ M w) := by
  apply (initBlackIndEquiv Q Λ i κ h0 hr hκ M).symm.injective
  rw [LinearEquiv.symm_apply_apply, initBlackIndEquiv_symm_apply]
  change _ = initIndFwd Q Λ i κ h0 hr hκ M (IndK.map g
    ((initIndFwd Q Λ i κ h0 hr hκ M).symm w))
  rw [initIndFwd_map, AddEquiv.apply_symm_apply]

/-- **`initBlackIndEquiv` intertwines the actions of the last cyclotomic factor.** -/
theorem initBlackIndEquiv_lastFactorEnd (z : Cyc') (w : IndK k (InitRestrict Q Λ b' M) φ₁) :
    initBlackIndEquiv Q Λ i κ h0 hr hκ M (IndK.map (lastFactorEnd Q Λ b' z) w) =
      lastFactorEnd Q Λ b (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ))
        (lastBlock_eq_of_castSucc hr) z) (initBlackIndEquiv Q Λ i κ h0 hr hκ M w) := by
  apply (initBlackIndEquiv Q Λ i κ h0 hr hκ M).symm.injective
  rw [LinearEquiv.symm_apply_apply, initBlackIndEquiv_symm_apply]
  change _ = initIndFwd Q Λ i κ h0 hr hκ M (op (lastBlockAlgHom Q Λ b
    (CycKLR.flip (redCyc Λ (Fin.last ℓ)) (rightBlock b (Fin.last ℓ))
      (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ)) (lastBlock_eq_of_castSucc hr) z))) •
    (initIndFwd Q Λ i κ h0 hr hκ M).symm w)
  rw [initIndFwd_last, AddEquiv.apply_symm_apply]

end Module

end StendhalAlgebra

end Categorification.Stendhal
