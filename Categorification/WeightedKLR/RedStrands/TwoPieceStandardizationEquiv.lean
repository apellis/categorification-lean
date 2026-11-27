/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceStandardization

/-!
# `M ⊗_B S^L_α ≅ S(X_M)`: the standardization of `ℓ + 1` red strands through that of the first `ℓ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Definition 5.4 and proof of Proposition 5.5. For a right module `M` over the block algebra `B`
of `ℓ + 1` red strands, the standardization `M ⊗_B S^L_α` is the two-piece standardization of
`X_M = M ⊗_{B'} S^L_{α'}`, regarded as a module over the factor algebra
`T^{λ'} ⊗ R^{λ_{ℓ+1}}(β)`. The map `S(X_M) → M ⊗_B S^L_α` extends
`m ⊗ l ↦ m ⊗ Φ([l ⊠ 1])`, where `Φ : S(S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β)) ≅ S^L_α` is the two-piece
isomorphism (`twoPieceStandardizationTo`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (b : Fin (ℓ + 2) → Multiset I)

local notation "𝔹" => BlockAlgebra k Q Λ b
local notation "B'" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b)
local notation "Cyc" => CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
  (lastBlock b)
local notation "fl" => CycKLR.flip (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
  (lastBlock b)
local notation "Told" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (initWeight b)
local notation "Tν" => TensorProductAlgebra k Q Λ (initWeight b + lastBlock b)
local notation "D" => parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b)
set_option quotPrecheck false in
local notation "N₀" => (rootSplitInput Q Λ b).carrier
local notation "KL'" => KMod (k := k) (ModuleCat.of Told
  (LeftRootStandard Q (Λ ∘ Fin.castSucc) (ν := initWeight b) (blockRoot (initBlocks b))))
local notation "KC" => KMod (k := k) (ModuleCat.of Cyc Cyc)

/-- The scalar tower `k → T(θ + β) → S N`. -/
local instance parabolicStandardT_isScalarTower_twoPieceStd {θ β : Multiset I} (N : Type*)
    [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
    [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] :
    IsScalarTower k (TensorProductAlgebra k Q Λ (θ + β)) (ParabolicStandardT Q Λ θ β N hQ) :=
  ⟨fun c t y => DFunLike.congr_fun (map_smul (parabolicStandardAction Q Λ θ β N hQ) c t) y⟩

variable (hα' : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (hα : RootNonViolated (ν := initWeight b + lastBlock b) (blockRoot b))

local notation "L'" => BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα'
local notation "L" => BlockLeftStandard Q Λ b (blockPrefix_last b) hα
set_option quotPrecheck false in
local notation "Φ" => twoPieceRootStandardEquiv Q Λ hQ b
set_option quotPrecheck false in
local notation "F'" => leftBlockActionOf Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα'
set_option quotPrecheck false in
local notation "F" => leftBlockActionOf Q Λ b (blockPrefix_last b) hα

/-- `ExtTensor.tmul l y` with `l` in `S^L_{α'}`. -/
abbrev splitTmul (l : L') (y : Cyc) : N₀ :=
  ExtTensor.tmul (k := k) (P := KL') (Q := KC) l y

theorem splitTmul_smul (c : k) (l : L') (y : Cyc) :
    splitTmul Q Λ b hα' (c • l) y = c • splitTmul Q Λ b hα' l y := by
  rw [splitTmul, splitTmul, ExtTensor.smul_tmul']
  exact congrArg (fun v : KL' => ExtTensor.tmul (k := k) (P := KL') (Q := KC) v y)
    (algebraMap_smul Told c l).symm

/-- `l ↦ Φ([l ⊠ 1])`, from `S^L_{α'}` to `S^L_α`. -/
def splitUnitMap : L' →ₗ[k] L where
  toFun l := Φ (parabolicStandardTUnit Q Λ (initWeight b) (lastBlock b) hQ (splitTmul Q Λ b hα' l 1))
  map_add' l l' := by
    rw [splitTmul, ExtTensor.add_tmul, parabolicStandardTUnit_add, map_add]
  map_smul' c l := by
    rw [RingHom.id_apply, splitTmul_smul]
    have h1 : parabolicStandardTUnit Q Λ (initWeight b) (lastBlock b) hQ
        (c • splitTmul Q Λ b hα' l 1) =
        c • parabolicStandardTUnit Q Λ (initWeight b) (lastBlock b) hQ (splitTmul Q Λ b hα' l 1) :=
      map_smul (parabolicStandardUnit Q Λ (initWeight b) (lastBlock b) N₀) c _
    rw [h1, ← algebraMap_smul Tν c, map_smul]
    exact algebraMap_smul Tν c _

theorem splitUnitMap_apply (l : L') :
    splitUnitMap Q Λ hQ b hα' hα l =
      Φ (parabolicStandardTUnit Q Λ (initWeight b) (lastBlock b) hQ (splitTmul Q Λ b hα' l 1)) := rfl

/-- `Φ([F'(x) l ⊠ 1]) = F(x) Φ([l ⊠ 1])` for `x ∈ B'`. -/
theorem splitUnitMap_initBlock (x : B') (l : L') :
    splitUnitMap Q Λ hQ b hα' hα (F' x l) =
      F (initBlockAlgHom Q Λ b x) (splitUnitMap Q Λ hQ b hα' hα l) :=
  LinearMap.congr_fun (twoPieceRootStandardEquiv_initBlockAlg Q Λ hQ b hα' hα x)
    (parabolicStandardTUnit Q Λ (initWeight b) (lastBlock b) hQ (splitTmul Q Λ b hα' l 1))

/-- `F(ι₂(flip z)) Φ([l ⊠ 1]) = Φ([l ⊠ z])` for `z` in the last factor. -/
theorem splitUnitMap_lastBlock (z : Cyc) (l : L') :
    F (lastBlockAlgHom Q Λ b (fl z)) (splitUnitMap Q Λ hQ b hα' hα l) =
      Φ (parabolicStandardTUnit Q Λ (initWeight b) (lastBlock b) hQ (splitTmul Q Λ b hα' l z)) := by
  have h := LinearMap.congr_fun (twoPieceRootStandardEquiv_lastBlockAlg Q Λ hQ b hα (fl z))
    (parabolicStandardTUnit Q Λ (initWeight b) (lastBlock b) hQ (splitTmul Q Λ b hα' l 1))
  rw [LinearMap.comp_apply, LinearMap.comp_apply, CycKLR.flip_flip,
    parabolicStandardMapT_unit] at h
  rw [splitUnitMap_apply]
  refine h.symm.trans ?_
  change Φ (parabolicStandardTUnit Q Λ (initWeight b) (lastBlock b) hQ
    (splitTmul Q Λ b hα' l ((1 : Cyc) • z))) = _
  rw [one_smul]

section Module

variable (M : Type*) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]

local notation "Y" => LeftStandardization Q Λ b (blockPrefix_last b) hα M
local notation "XL" => LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα'
  (InitRestrict Q Λ b M)
local notation "X" => TwoPieceInput Q Λ b M hα'
local notation "ofR" => initRestrictOf Q Λ b (M := M)
local notation "ofX" => twoPieceInputOf Q Λ b M hα'

/-- `(l, m) ↦ Φ([l ⊠ 1]) ⊗ m`. -/
def splitInputBil : L' →ₗ[k] InitRestrict Q Λ b M →ₗ[k] Y :=
  (BalancedTensor.mkBil k Tν (BlockAlgebra k Q Λ b)ᵐᵒᵖ L M).compl₁₂
    (splitUnitMap Q Λ hQ b hα' hα) (ofR).symm.toLinearMap

omit [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] in
theorem splitInputBil_apply (l : L') (m : InitRestrict Q Λ b M) :
    splitInputBil Q Λ hQ b hα' hα M l m =
      BalancedTensor.tmul (splitUnitMap Q Λ hQ b hα' hα l) ((ofR).symm m) := rfl

omit [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] in
theorem splitInputBil_balanced (l : L') (a : B'ᵐᵒᵖ) (m : InitRestrict Q Λ b M) :
    splitInputBil Q Λ hQ b hα' hα M (op a • l) m = splitInputBil Q Λ hQ b hα' hα M l (a • m) := by
  obtain ⟨x, rfl⟩ := MulOpposite.op_surjective a
  rw [splitInputBil_apply, splitInputBil_apply]
  change BalancedTensor.tmul (splitUnitMap Q Λ hQ b hα' hα (F' x l)) _ = _
  rw [splitUnitMap_initBlock]
  exact BalancedTensor.op_smul_tmul (B := Tν) (splitUnitMap Q Λ hQ b hα' hα l)
    (op (initBlockAlgHom Q Λ b x)) ((ofR).symm m)

/-- **The map `X_M → M ⊗_B S^L_α`**, `m ⊗ l ↦ m ⊗ Φ([l ⊠ 1])`. -/
def splitInputMap : X →ₗ[k] Y :=
  (BalancedTensor.lift (splitInputBil Q Λ hQ b hα' hα M)
    (splitInputBil_balanced Q Λ hQ b hα' hα M)).comp (ofX).symm.toLinearMap

omit [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] in
theorem splitInputMap_of (l : L') (m : InitRestrict Q Λ b M) :
    splitInputMap Q Λ hQ b hα' hα M (ofX (BalancedTensor.tmul l m)) =
      BalancedTensor.tmul (splitUnitMap Q Λ hQ b hα' hα l) ((ofR).symm m) := rfl

theorem splitInputMap_tmul_smul (t : Told) (c : Cyc) (l : L') (m : InitRestrict Q Λ b M) :
    splitInputMap Q Λ hQ b hα' hα M ((t ⊗ₜ c : D) • ofX (BalancedTensor.tmul l m)) =
      BalancedTensor.tmul (M := L) (Φ (parabolicStandardTUnit Q Λ (initWeight b) (lastBlock b) hQ
        ((t ⊗ₜ c : D) • splitTmul Q Λ b hα' l 1))) ((ofR).symm m) := by
  rw [tmul_smul_twoPieceInputOf, splitInputMap_of]
  obtain ⟨m, rfl⟩ := (ofR).surjective m
  rw [lastFactorEnd_of, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    ← BalancedTensor.op_smul_tmul (B := Tν) (M := L), op_op_smul_blockLeftStandard]
  change BalancedTensor.tmul (M := L) (F (lastBlockAlgHom Q Λ b (fl c))
    (splitUnitMap Q Λ hQ b hα' hα (t • l))) m = _
  rw [splitUnitMap_lastBlock, splitTmul, ExtTensor.smul_tmul, smul_eq_mul, mul_one]

theorem splitInputMap_smul_of (d : D) (l : L') (m : InitRestrict Q Λ b M) :
    splitInputMap Q Λ hQ b hα' hα M (d • ofX (BalancedTensor.tmul l m)) =
      BalancedTensor.tmul (M := L) (Φ (parabolicStandardTUnit Q Λ (initWeight b) (lastBlock b) hQ
        (d • splitTmul Q Λ b hα' l 1))) ((ofR).symm m) := by
  induction d using TensorProduct.inductionOn with
  | tmul t c => exact splitInputMap_tmul_smul Q Λ hQ b hα' hα M t c l m
  | add d d' hd hd' =>
    rw [add_smul, map_add, hd, hd', add_smul, parabolicStandardTUnit_add, map_add,
      BalancedTensor.add_tmul]

theorem splitInputMap_parabolic (w : TensorKLR (stendhalQ Q Λ)
      (Multiset.map (addRedColor ℓ) (stendhalWeight ℓ (initWeight b)))
      (Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
        (stendhalWeight 1 (lastBlock b)))) (x : XL) :
    splitInputMap Q Λ hQ b hα' hα M
        (parabolicInputMap Q Λ (initWeight b) (lastBlock b) w • ofX x) =
      parabolicAffine Q Λ (initWeight b) (lastBlock b) (concat (stendhalQ Q Λ) _ _ w) •
        splitInputMap Q Λ hQ b hα' hα M (ofX x) := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [map_zero, smul_zero, map_zero, smul_zero]
  | tmul l m =>
    rw [splitInputMap_smul_of, parabolicStandardTUnit_smul, map_smul, splitInputMap_of,
      BalancedTensor.smul_tmul']
    rfl
  | add x y hx hy => rw [map_add, smul_add, map_add, hx, hy, map_add, smul_add]

/-- **The map `S(X_M) → M ⊗_B S^L_α`**, extending `m ⊗ l ↦ m ⊗ Φ([l ⊠ 1])`. -/
def splitStandardTo :
    ParabolicStandardT Q Λ (initWeight b) (lastBlock b) X hQ →ₗ[Tν] Y where
  toFun := parabolicDesc Q Λ (initWeight b) (lastBlock b) (N := X) (Algebra.lsmul k k Y)
    (splitInputMap Q Λ hQ b hα' hα M) (fun w n =>
      splitInputMap_parabolic Q Λ hQ b hα' hα M w ((ofX).symm n))
  map_add' := map_add _
  map_smul' a z := parabolicDesc_smul Q Λ (initWeight b) (lastBlock b) (N := X) hQ
    (Algebra.lsmul k k Y)
    (splitInputMap Q Λ hQ b hα' hα M) (fun w n =>
      splitInputMap_parabolic Q Λ hQ b hα' hα M w ((ofX).symm n)) a z

theorem splitStandardTo_unit (n : X) :
    splitStandardTo Q Λ hQ b hα' hα M (parabolicStandardTUnit Q Λ (initWeight b) (lastBlock b) hQ n) =
      splitInputMap Q Λ hQ b hα' hα M n :=
  parabolicDesc_unit Q Λ (initWeight b) (lastBlock b) (N := X) _ _ _ n

end Module

end StendhalAlgebra

end Categorification.Stendhal
