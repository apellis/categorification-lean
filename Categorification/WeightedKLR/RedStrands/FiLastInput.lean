/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiLastInduction
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastInduction
import Categorification.Algebra.InductionAlongTensorFactorNatural

/-!
# `₂Fᵢ` of the two-piece input is the two-piece input of `ₗFᵢ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. Let `b` be blocks of `ℓ + 1` red strands and `c` the blocks with one
black strand of colour `i` added to the last block. For a right `B(b)`-module `M`, inducing the
input `X_M = M ⊗_{B'} S^L_{α'}` of the two-piece standardization along the last factor gives the
input `X_{ₗFᵢ M}` of `ₗFᵢ M`, as modules over `T^{λ'}(θ) ⊗ R^{λ_ℓ}(i + β)`
(`fiLastInputEquiv`), naturally in endomorphisms of `M` (`fiLastInputEquiv_natural`).
The induction along the last factor moves through the left standard module of the first red
strands (`indBalancedEquiv`) and becomes `ₗFᵢ M` restricted to the first red strands
(`lastBlackIndEquiv`).
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
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)
  {b c : Fin (ℓ + 2) → Multiset I} (h0 : leftBlock b = leftBlock c)
  (hr : ∀ r, r ≠ Fin.last ℓ → rightBlock b r = rightBlock c r)
  (hκ : {i} + rightBlock b (Fin.last ℓ) = rightBlock c (Fin.last ℓ))
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  (hα₁ : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (hαc : RootNonViolated (ν := initWeight c) (blockRoot (initBlocks c)))

local notation "Cyc" β => CycKLR k Q (redCyc Λ (Fin.last ℓ)) β
local notation "β" => lastBlock b
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Tfam" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
local notation "Tθ" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (initWeight b)
local notation "B₁" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b)
local notation "Nb" => TwoPieceInput Q Λ b M hα₁
local notation "Fr" => LastIndRight Q Λ i (initWeight b) (lastBlock b) (TwoPieceInput Q Λ b M hα₁)
local notation "Mf" => BlockBlackInd Q Λ i (Fin.last ℓ) h0 hr hκ M
local notation "L₀" => BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα₁
local notation "φc" => lastCycHom Q Λ i (b := b)
local notation "Xr" => RightFactorRes k (Cyc β) Tθ (TwoPieceInput Q Λ b M hα₁)
local notation "Rr" => RightFactorRes k (Cyc (Si + β)) Tθ
  (LastIndRight Q Λ i (initWeight b) (lastBlock b) (TwoPieceInput Q Λ b M hα₁))

include h0 hr in
/-- The first red strands of `c` have the weight of those of `b`. -/
theorem initWeight_lastBig : initWeight c = initWeight b :=
  initWeight_eq_of_last h0.symm (fun r h => (hr r h).symm)

include hκ in
theorem lastBlock_lastBig : lastBlock c = Si + lastBlock b := hκ.symm

include h0 hr hα₁ in
theorem rootNonViolated_lastBig :
    RootNonViolated (ν := initWeight b) (blockRoot (initBlocks c)) :=
  rootNonViolated_initBlocks_of_last h0.symm (fun r h => (hr r h).symm) hα₁

/-- **`₂Fᵢ X_M`, restricted to the last factor, is induction of `X_M` along the last
cyclotomic factor.** -/
def fiLastIndRight : Rr ≃ₗ[Cyc (Si + β)] IndK k Xr φc :=
  indRightFactorEquivB φc (lastCycHom_smul Q Λ i) (parabolicRightHom Q Λ i (initWeight b)
    (lastBlock b)) (fun _ _ => rfl)

/-- The last cyclotomic factor acting on `LastCycRes M`. -/
def lastCycResFactor (a : Cyc β) : LastCycRes Q Λ b M →ₗ[B₁ᵐᵒᵖ] LastCycRes Q Λ b M :=
  lastFactorEnd Q Λ b a

/-- `X_M` restricted to the last factor as `L₀ ⊗_{B'} LastCycRes M`. -/
def twoPieceLastCycRes : Xr ≃ₗ[k] BalancedTensor k Tθ B₁ᵐᵒᵖ L₀ (LastCycRes Q Λ b M) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem twoPieceLastCycRes_smul (a : Cyc β) (x : Xr) :
    twoPieceLastCycRes Q Λ M hα₁ (a • x) =
      BalancedTensor.mapRight (lastCycResFactor Q Λ M a) (twoPieceLastCycRes Q Λ M hα₁ x) := by
  change twoPieceInputAction Q Λ b M hα₁ ((1 : Tθ) ⊗ₜ a) x = _
  rw [twoPieceInputAction_tmul, one_smul]
  rfl

theorem lastBlackIndEquiv_rSmul' (r : B₁ᵐᵒᵖ) (w : IndK k (LastCycRes Q Λ b M) φc) :
    lastBlackIndEquiv Q Λ i h0 hr hκ M (IndK.map (rSmulA (A := Cyc β) r) w) =
      r • lastBlackIndEquiv Q Λ i h0 hr hκ M w := by
  induction r using MulOpposite.rec' with | _ x =>
  exact lastBlackIndEquiv_rSmul Q Λ i h0 hr hκ M x w

/-- **`₂Fᵢ` moves through the left standard module of the first red strands.** -/
def fiLastBalanced :
    IndK k Xr φc ≃+ BalancedTensor k Tθ B₁ᵐᵒᵖ L₀ (LastBlackRes Q Λ i h0 hr hκ M) :=
  indBalancedEquiv (lastCycHom_smul Q Λ i) (lastCycResFactor Q Λ M) (fun _ _ => rfl)
    (twoPieceLastCycRes Q Λ M hα₁) (twoPieceLastCycRes_smul Q Λ M hα₁)
    (lastBlackIndEquiv Q Λ i h0 hr hκ M) (lastBlackIndEquiv_rSmul' Q Λ i h0 hr hκ M)

/-- The left standardization of `ₗFᵢ M` over the first red strands of `b`, as that over the
first red strands of `c`. -/
def fiLastCast :
    BalancedTensor k Tθ B₁ᵐᵒᵖ L₀ (LastBlackRes Q Λ i h0 hr hκ M) ≃ₗ[Tθ]
      FamilyCast Tfam (initWeight_lastBig h0 hr) (LeftStandardization Q (Λ ∘ Fin.castSucc)
        (initBlocks c) rfl hαc (InitRestrict Q Λ c Mf)) :=
  (leftStandardizationCast Q (Λ ∘ Fin.castSucc) (InitRestrict Q Λ c Mf)
    (initBlocks_lastBig h0 hr) (initWeight_lastBig h0 hr) rfl
    (rootNonViolated_lastBig h0 hr hα₁) hα₁).symm.trans
    (leftStandardizationFamilyCast (Q := Q) (Λ := Λ ∘ Fin.castSucc) (InitRestrict Q Λ c Mf)
      (initWeight_lastBig h0 hr) rfl (initWeight_lastBig h0 hr) hαc
      (rootNonViolated_lastBig h0 hr hα₁))


local notation "Y" => FactorCast Q Λ (initWeight_lastBig h0 hr) (rfl : Si + lastBlock b = _)
  (FactorCast Q Λ (rfl : initWeight c = initWeight c) (lastBlock_lastBig i hκ)
    (TwoPieceInput Q Λ c Mf hαc))

theorem fiLastBalanced_smul (y : Cyc (Si + β)) (w : IndK k Xr φc) :
    fiLastBalanced Q Λ i h0 hr hκ M hα₁ (y • w) =
      BalancedTensor.mapRight (castBlockModuleMap (initBlocks_lastBig h0 hr)
        (lastFactorEnd Q Λ c (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ)) hκ y)))
        (fiLastBalanced Q Λ i h0 hr hκ M hα₁ w) :=
  indBalancedEquiv_smul _ _ _ _ _ _ _ y _
    (fun w => (lastBlackIndEquiv_lastSmul Q Λ i h0 hr hκ M y w).trans rfl) w

theorem fiLastBalanced_map (t : Tθ) (w : IndK k Xr φc) :
    fiLastBalanced Q Λ i h0 hr hκ M hα₁ (IndK.map (rightFactorCAct t) w) =
      t • fiLastBalanced Q Λ i h0 hr hκ M hα₁ w := by
  refine indBalancedEquiv_map _ _ _ _ _ _ _ (rightFactorCAct t) t (fun x => ?_) w
  change twoPieceInputAction Q Λ b M hα₁ (t ⊗ₜ (1 : Cyc β)) x = _
  rw [twoPieceInputAction_tmul, lastFactorEnd_one, BalancedTensor.mapRight_id]
  rfl

theorem leftStandardizationCast_symm_mapRight {ℓ' : ℕ} {Λ' : Fin ℓ' → I →₀ ℕ}
    {d d' : Fin (ℓ' + 1) → Multiset I} {ν : Multiset I} (h : d = d') {N : Type}
    [AddCommGroup N] [Module k N] [Module (BlockAlgebra k Q Λ' d)ᵐᵒᵖ N]
    [IsScalarTower k (BlockAlgebra k Q Λ' d)ᵐᵒᵖ N] (hb : blockPrefix d (ℓ' + 1) = ν)
    (hb' : blockPrefix d' (ℓ' + 1) = ν) (hα : RootNonViolated (ν := ν) (blockRoot d))
    (hα' : RootNonViolated (ν := ν) (blockRoot d'))
    (g : N →ₗ[(BlockAlgebra k Q Λ' d)ᵐᵒᵖ] N)
    (x : LeftStandardization Q Λ' d' hb' hα' (CastBlockModule Q Λ' h N)) :
    (leftStandardizationCast Q Λ' N h hb hb' hα hα').symm
        (BalancedTensor.mapRight (castBlockModuleMap h g) x) =
      BalancedTensor.mapRight g ((leftStandardizationCast Q Λ' N h hb hb' hα hα').symm x) := by
  apply (leftStandardizationCast Q Λ' N h hb hb' hα hα').injective
  rw [LinearEquiv.apply_symm_apply, leftStandardizationCast_mapRight,
    LinearEquiv.apply_symm_apply]

local notation "XLc" => LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks c) rfl hαc
  (InitRestrict Q Λ c Mf)

theorem fiLastCast_mapRight (g : Module.End (BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks c))ᵐᵒᵖ
      (InitRestrict Q Λ c Mf))
    (z : BalancedTensor k Tθ B₁ᵐᵒᵖ L₀ (LastBlackRes Q Λ i h0 hr hκ M)) :
    fiLastCast Q Λ i h0 hr hκ M hα₁ hαc
        (BalancedTensor.mapRight (castBlockModuleMap (initBlocks_lastBig h0 hr) g) z) =
      (show FamilyCast Tfam (initWeight_lastBig h0 hr) XLc from
        BalancedTensor.mapRight g (show XLc from fiLastCast Q Λ i h0 hr hκ M hα₁ hαc z)) := by
  rw [fiLastCast, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    leftStandardizationCast_symm_mapRight, leftStandardizationFamilyCast_mapRight]

theorem fiLastY_smul (t : Tθ) (y : Cyc (Si + β)) (v : XLc) :
    ((t ⊗ₜ y : parabolicFactorAlgebra Q Λ (initWeight b) (Si + lastBlock b)) •
      (show Y from v) : Y) =
      (show Y from (castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) (initWeight_lastBig h0 hr).symm t
        • (BalancedTensor.mapRight (lastFactorEnd Q Λ c
          (CyclotomicAction.castCyc Q (redCyc Λ (Fin.last ℓ)) hκ y)) : XLc →ₗ[Tfam (initWeight c)]
            XLc) v)) := by
  rw [factorCast_smul, castFactor_symm_tmul, factorCast_smul, castFactor_symm_tmul]
  change twoPieceInputAction Q Λ c Mf hαc (_ ⊗ₜ _) v = _
  rw [twoPieceInputAction_tmul]
  rfl

/-- The underlying additive isomorphism of `fiLastInputEquiv`. -/
def fiLastInputAdd : Fr ≃+ Y :=
  ((fiLastIndRight Q Λ i M hα₁).toAddEquiv.trans
    ((fiLastBalanced Q Λ i h0 hr hκ M hα₁).trans
      (fiLastCast Q Λ i h0 hr hκ M hα₁ hαc).toAddEquiv))

local notation "Dl" => parabolicFactorAlgebra Q Λ (initWeight b) (Si + lastBlock b)
local notation "F" => fiLastInputAdd Q Λ i h0 hr hκ M hα₁ hαc

theorem fiLastIndRight_cAct (t : Tθ) (x : Rr) :
    fiLastIndRight Q Λ i M hα₁ (rightFactorCAct t x) =
      IndK.map (rightFactorCAct t) (fiLastIndRight Q Λ i M hα₁ x) :=
  indRightFactorEquivB_cAct _ _ _ _ t x

theorem fiLastInputAdd_one_tmul (y : Cyc (Si + β)) (x : Fr) :
    F (((1 : Tθ) ⊗ₜ y : Dl) • x) = ((1 : Tθ) ⊗ₜ y : Dl) • F x := by
  change fiLastCast Q Λ i h0 hr hκ M hα₁ hαc (fiLastBalanced Q Λ i h0 hr hκ M hα₁
    (fiLastIndRight Q Λ i M hα₁ (y • (show Rr from x)))) = _
  rw [map_smul, fiLastBalanced_smul, fiLastCast_mapRight]
  change _ = ((1 : Tθ) ⊗ₜ y : Dl) • (show Y from (show XLc from fiLastCast Q Λ i h0 hr hκ M hα₁
    hαc (fiLastBalanced Q Λ i h0 hr hκ M hα₁ (fiLastIndRight Q Λ i M hα₁ x))))
  rw [fiLastY_smul, map_one, one_smul]

theorem fiLastY_tmul_one_smul (t : Tθ) (v : XLc) :
    ((t ⊗ₜ (1 : Cyc (Si + β)) : Dl) • (show Y from v) : Y) =
      (show Y from (castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) (initWeight_lastBig h0 hr).symm t
        • v)) := by
  rw [fiLastY_smul, map_one]
  change (show Y from _ • (BalancedTensor.mapRight (lastFactorEnd Q Λ c 1) :
    XLc →ₗ[Tfam (initWeight c)] XLc) v) = _
  rw [lastFactorEnd_one, BalancedTensor.mapRight_id]
  rfl

theorem fiLastInputAdd_tmul_one (t : Tθ) (x : Fr) :
    F ((t ⊗ₜ (1 : Cyc (Si + β)) : Dl) • x) = (t ⊗ₜ (1 : Cyc (Si + β)) : Dl) • F x := by
  change fiLastCast Q Λ i h0 hr hκ M hα₁ hαc (fiLastBalanced Q Λ i h0 hr hκ M hα₁
    (fiLastIndRight Q Λ i M hα₁ (rightFactorCAct t (show Rr from x)))) = _
  rw [fiLastIndRight_cAct, fiLastBalanced_map, map_smul,
    familyCast_tensorProductAlgebra_smul (P := XLc)]
  change _ = (t ⊗ₜ (1 : Cyc (Si + β)) : Dl) • (show Y from (show XLc from fiLastCast Q Λ i h0 hr
    hκ M hα₁ hαc (fiLastBalanced Q Λ i h0 hr hκ M hα₁ (fiLastIndRight Q Λ i M hα₁ x))))
  rw [fiLastY_tmul_one_smul]

/-- **`₂Fᵢ X_M ≅ X_{ₗFᵢ M}`** (Webster, arXiv:1309.3796v3, proof of Proposition 5.5, `F`-part):
inducing the input `X_M` of the two-piece standardization along the last factor gives the input
of `ₗFᵢ M`, as modules over `T^{λ'}(θ) ⊗ R^{λ_ℓ}(i + β)`. -/
def fiLastInputEquiv : Fr ≃ₗ[Dl] Y :=
  LinearEquiv.ofBijective
    (tensorLinearOfGenerators (F).toAddMonoidHom
      (fiLastInputAdd_tmul_one Q Λ i h0 hr hκ M hα₁ hαc)
      (fiLastInputAdd_one_tmul Q Λ i h0 hr hκ M hα₁ hαc))
    (F).bijective

theorem fiLastInputEquiv_apply (x : Fr) : fiLastInputEquiv Q Λ i h0 hr hκ M hα₁ hαc x = F x :=
  rfl

/-- An endomorphism of `M` on `LastCycRes M`, over the first red strands. -/
def lastCycResEndR (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) :
    LastCycRes Q Λ b M →ₗ[B₁ᵐᵒᵖ] LastCycRes Q Λ b M :=
  initRestrictEnd Q Λ b g

theorem lastBlackIndEquiv_natural' (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
    (w : IndK k (LastCycRes Q Λ b M) φc) :
    lastBlackIndEquiv Q Λ i h0 hr hκ M (IndK.map (lastCycResEnd Q Λ M g) w) =
      castBlockModuleMap (initBlocks_lastBig h0 hr)
        (initRestrictEnd Q Λ c (IndK.map g : Mf →ₗ[(BlockAlgebra k Q Λ c)ᵐᵒᵖ] Mf))
        (lastBlackIndEquiv Q Λ i h0 hr hκ M w) :=
  lastBlackIndEquiv_natural Q Λ i h0 hr hκ M g w

theorem twoPieceLastCycRes_map (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) (x : Xr) :
    twoPieceLastCycRes Q Λ M hα₁ (rightFactorResMap (twoPieceEnd Q Λ b hα₁ g) x) =
      BalancedTensor.mapRight (lastCycResEndR Q Λ M g) (twoPieceLastCycRes Q Λ M hα₁ x) :=
  rfl

theorem fiLastBalanced_natural (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) (w : IndK k Xr φc) :
    fiLastBalanced Q Λ i h0 hr hκ M hα₁
        (IndK.map (rightFactorResMap (twoPieceEnd Q Λ b hα₁ g)) w) =
      BalancedTensor.mapRight (castBlockModuleMap (initBlocks_lastBig h0 hr)
        (initRestrictEnd Q Λ c (IndK.map g : Mf →ₗ[(BlockAlgebra k Q Λ c)ᵐᵒᵖ] Mf)))
        (fiLastBalanced Q Λ i h0 hr hκ M hα₁ w) :=
  indBalancedEquiv_natural (lastCycHom_smul Q Λ i) (lastCycResFactor Q Λ M) (fun _ _ => rfl)
    (twoPieceLastCycRes Q Λ M hα₁) (twoPieceLastCycRes_smul Q Λ M hα₁)
    (lastBlackIndEquiv Q Λ i h0 hr hκ M) (lastBlackIndEquiv_rSmul' Q Λ i h0 hr hκ M)
    (rightFactorResMap (twoPieceEnd Q Λ b hα₁ g)) (lastCycResEnd Q Λ M g)
    (lastCycResEndR Q Λ M g) (fun _ => rfl) (twoPieceLastCycRes_map Q Λ M hα₁ g) _
    (lastBlackIndEquiv_natural' Q Λ i h0 hr hκ M g) w

/-- **Naturality of `fiLastInputEquiv`** in endomorphisms of `M`. -/
theorem fiLastInputEquiv_natural (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) (x : Fr) :
    fiLastInputEquiv Q Λ i h0 hr hκ M hα₁ hαc (IndK.map (twoPieceEnd Q Λ b hα₁ g) x) =
      factorCastMap Q Λ (initWeight_lastBig h0 hr) rfl (factorCastMap Q Λ rfl
        (lastBlock_lastBig i hκ) (twoPieceEnd Q Λ c hαc
          (blockBlackIndEnd Q Λ i (Fin.last ℓ) h0 hr hκ M g)))
        (fiLastInputEquiv Q Λ i h0 hr hκ M hα₁ hαc x) := by
  rw [fiLastInputEquiv_apply, fiLastInputEquiv_apply]
  change fiLastCast Q Λ i h0 hr hκ M hα₁ hαc (fiLastBalanced Q Λ i h0 hr hκ M hα₁
    (fiLastIndRight Q Λ i M hα₁ (show Rr from IndK.map (twoPieceEnd Q Λ b hα₁ g) x))) = _
  rw [show fiLastIndRight Q Λ i M hα₁ (show Rr from IndK.map (twoPieceEnd Q Λ b hα₁ g) x) =
    IndK.map (rightFactorResMap (twoPieceEnd Q Λ b hα₁ g)) (fiLastIndRight Q Λ i M hα₁ x) from
      indRightFactorEquivB_map _ _ _ _ (twoPieceEnd Q Λ b hα₁ g) x,
    fiLastBalanced_natural, fiLastCast_mapRight]
  rfl

end StendhalAlgebra

end Categorification.Stendhal
