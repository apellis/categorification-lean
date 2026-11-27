/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackResCast
import Categorification.WeightedKLR.RedStrands.BlockBlackResMaps
import Categorification.Algebra.TensorProductLinearGenerators

/-!
# `₂Eᵢ` of the two-piece input is the two-piece input of `ₗEᵢ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. For blocks `b, b'` of `ℓ + 1` red strands with `b_{ℓ+1} = i + b'_{ℓ+1}` and
`b_j = b'_j` otherwise, restricting the input `X_M = M ⊗_{B'} S^L_{α'}` of the two-piece
standardization along the last black strand of the last factor gives the input `X_{M e}` of
`ₗEᵢ M = M e`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

section CastNatural

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {c c' : Fin (ℓ + 1) → Multiset I}
  {ν ν' : Multiset I} (h : c = c')
  {N : Type} [AddCommGroup N] [Module k N] [Module (BlockAlgebra k Q Λ c)ᵐᵒᵖ N]
  [IsScalarTower k (BlockAlgebra k Q Λ c)ᵐᵒᵖ N]
  {N' : Type} [AddCommGroup N'] [Module k N'] [Module (BlockAlgebra k Q Λ c)ᵐᵒᵖ N']
  [IsScalarTower k (BlockAlgebra k Q Λ c)ᵐᵒᵖ N']

/-- A map of right `B(c)`-modules as a map of the transported right `B(c')`-modules. -/
def castBlockModuleMap (g : N →ₗ[(BlockAlgebra k Q Λ c)ᵐᵒᵖ] N') :
    CastBlockModule Q Λ h N →ₗ[(BlockAlgebra k Q Λ c')ᵐᵒᵖ] CastBlockModule Q Λ h N' where
  toFun n := (g (show N from n) : N')
  map_add' n n' := g.map_add (show N from n) (show N from n')
  map_smul' _ n := g.map_smul _ (show N from n)

theorem castBlockModuleMap_apply (g : N →ₗ[(BlockAlgebra k Q Λ c)ᵐᵒᵖ] N') (n : N) :
    castBlockModuleMap h g (show CastBlockModule Q Λ h N from n) =
      (show CastBlockModule Q Λ h N' from g n) := rfl

/-- **`leftStandardizationCast` is natural.** -/
theorem leftStandardizationCast_mapRight (hb : blockPrefix c (ℓ + 1) = ν)
    (hb' : blockPrefix c' (ℓ + 1) = ν) (hα : RootNonViolated (ν := ν) (blockRoot c))
    (hα' : RootNonViolated (ν := ν) (blockRoot c')) (g : N →ₗ[(BlockAlgebra k Q Λ c)ᵐᵒᵖ] N')
    (x : LeftStandardization Q Λ c hb hα N) :
    leftStandardizationCast Q Λ N' h hb hb' hα hα' (BalancedTensor.mapRight g x) =
      BalancedTensor.mapRight (castBlockModuleMap h g)
        (leftStandardizationCast Q Λ N h hb hb' hα hα' x) := by
  subst h
  induction x using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul l n => rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- **`leftStandardizationFamilyCast` is natural.** -/
theorem leftStandardizationFamilyCast_mapRight (h' : ν = ν') (hb : blockPrefix c (ℓ + 1) = ν)
    (hb' : blockPrefix c (ℓ + 1) = ν') (hα : RootNonViolated (ν := ν) (blockRoot c))
    (hα' : RootNonViolated (ν := ν') (blockRoot c)) (g : N →ₗ[(BlockAlgebra k Q Λ c)ᵐᵒᵖ] N')
    (x : LeftStandardization Q Λ c hb' hα' N) :
    (leftStandardizationFamilyCast (Q := Q) (Λ := Λ) N' h' hb hb' hα hα' (BalancedTensor.mapRight g x) :
        LeftStandardization Q Λ c hb hα N') =
      BalancedTensor.mapRight g (leftStandardizationFamilyCast (Q := Q) (Λ := Λ) N h' hb hb' hα hα' x :
        LeftStandardization Q Λ c hb hα N) := by
  subst h'
  rfl

/-- **`leftStandardizationFamilyCast` is natural**, inverse form. -/
theorem leftStandardizationFamilyCast_symm_mapRight (h' : ν = ν')
    (hb : blockPrefix c (ℓ + 1) = ν) (hb' : blockPrefix c (ℓ + 1) = ν')
    (hα : RootNonViolated (ν := ν) (blockRoot c)) (hα' : RootNonViolated (ν := ν') (blockRoot c))
    (g : N →ₗ[(BlockAlgebra k Q Λ c)ᵐᵒᵖ] N') (x : LeftStandardization Q Λ c hb hα N) :
    (leftStandardizationFamilyCast (Q := Q) (Λ := Λ) N' h' hb hb' hα hα').symm
        (show FamilyCast (TensorProductAlgebra k Q Λ) h' (LeftStandardization Q Λ c hb hα N') from
          BalancedTensor.mapRight g x) =
      BalancedTensor.mapRight g ((leftStandardizationFamilyCast (Q := Q) (Λ := Λ) N h' hb hb' hα
        hα').symm (show FamilyCast (TensorProductAlgebra k Q Λ) h' (LeftStandardization Q Λ c hb hα N)
          from x)) := by
  subst h'
  rfl

theorem familyCast_tensorProductAlgebra_smul {ν ν' : Multiset I} (h' : ν = ν') {P : Type}
    [AddCommGroup P] [Module k P] [Module (TensorProductAlgebra k Q Λ ν) P]
    [IsScalarTower k (TensorProductAlgebra k Q Λ ν) P] (t : TensorProductAlgebra k Q Λ ν')
    (p : P) :
    t • (show FamilyCast (TensorProductAlgebra k Q Λ) h' P from p) =
      (show FamilyCast (TensorProductAlgebra k Q Λ) h' P from
        castTensorProductAlgebra Q Λ h'.symm t • p) := by
  subst h'
  rfl

end CastNatural

theorem cycFlip_castCyc {I : Type} [DecidableEq I] {k : Type} [Field k]
    {Q : I → I → MvPolynomial (Fin 2) k} (a : I → Polynomial k) {β δ : Multiset I} (h : β = δ)
    (z : CycKLR k Q a β) :
    CycKLR.flip a δ (CyclotomicAction.castCyc Q a h z) =
      CyclotomicAction.castCyc Q a h (CycKLR.flip a β z) := by
  subst h
  rfl

theorem cycFlip_one {I : Type} [DecidableEq I] {k : Type} [Field k]
    {Q : I → I → MvPolynomial (Fin 2) k} (a : I → Polynomial k) (β : Multiset I) :
    CycKLR.flip a β (1 : CycKLR k Q a β) = 1 := by
  rw [← map_one (CycKLR.mk k Q a β), CycKLR.flip_mk, KLRAlgebra.hflip_one]

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)
  {b b' : Fin (ℓ + 2) → Multiset I} (h0 : leftBlock b' = leftBlock b)
  (hr : ∀ r, r ≠ Fin.last ℓ → rightBlock b' r = rightBlock b r)
  (hκ : {i} + rightBlock b' (Fin.last ℓ) = rightBlock b (Fin.last ℓ))

local notation "BB" => BlockAlgebra k Q Λ b
local notation "BB'" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b)
local notation "E" => blockBlackRes Q Λ i (Fin.last ℓ) h0 hr hκ
local notation "hinit" => initBlocks_eq_of_last h0 hr

variable (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]

local notation "M'" => BlockBlackRes Q Λ i (Fin.last ℓ) h0 hr hκ M
local notation "CM'" => CastBlockModule Q (Λ ∘ Fin.castSucc) hinit (InitRestrict Q Λ b' M')

theorem op_blockBlackRes_one_smul_val (m : M') : (op (E 1) : BBᵐᵒᵖ) • m.val = m.val := m.prop

theorem blockBlackRes_one_mul_initBlockAlgHom (x : BB') :
    E 1 * initBlockAlgHom Q Λ b x = initBlockAlgHom Q Λ b x * E 1 := by
  rw [blockBlackRes_one_eq_lastBlockAlgHom]
  exact (commute_initBlockAlgHom_lastBlockAlgHom Q Λ b x _).symm.eq

theorem op_smul_castInitBlackRes_val (x : BB') (m : CM') :
    ((op x : BB'ᵐᵒᵖ) • m : CM').val =
      (op (initBlockAlgHom Q Λ b x) : BBᵐᵒᵖ) • (show M' from m).val := by
  change (op (E (initBlockAlgHom Q Λ b' ((blockAlgebraCast Q (Λ ∘ Fin.castSucc) hinit).symm x)))
    : BBᵐᵒᵖ) • (show M' from m).val = _
  rw [blockBlackRes_initBlockAlgHom_last, AlgEquiv.apply_symm_apply,
    ← blockBlackRes_one_mul_initBlockAlgHom, op_mul, mul_smul, op_blockBlackRes_one_smul_val]

/-- The inclusion `M e → M`, as a map of right `B'`-modules. -/
def lastBlackIncl : CM' →ₗ[BB'ᵐᵒᵖ] InitRestrict Q Λ b M where
  toFun m := initRestrictOf Q Λ b (show M' from m).val
  map_add' _ _ := rfl
  map_smul' a m := by
    induction a using MulOpposite.rec' with | _ x =>
    rw [RingHom.id_apply, op_smul_initRestrictOf, ← op_smul_castInitBlackRes_val]

theorem lastBlackIncl_apply (m : CM') :
    lastBlackIncl Q Λ i h0 hr hκ M m = initRestrictOf Q Λ b (show M' from m).val := rfl

theorem op_blockBlackRes_one_smul_idem (m : M) :
    (op (E 1) : BBᵐᵒᵖ) • (op (E 1) : BBᵐᵒᵖ) • m = (op (E 1) : BBᵐᵒᵖ) • m := by
  rw [smul_smul, ← op_mul, (isIdempotentElem_blockBlackRes_one Q Λ i h0 hr hκ).eq]

/-- The projection `M → M e`, `m ↦ m e`, as a map of right `B'`-modules. -/
def lastBlackProj : InitRestrict Q Λ b M →ₗ[BB'ᵐᵒᵖ] CM' where
  toFun m := (Res.mk ((op (E 1) : BBᵐᵒᵖ) • (initRestrictOf Q Λ b).symm m)
    (op_blockBlackRes_one_smul_idem Q Λ i h0 hr hκ M _) : M')
  map_add' m m' := Res.ext (smul_add _ _ _)
  map_smul' a m := by
    induction a using MulOpposite.rec' with | _ x =>
    refine Res.ext ?_
    rw [RingHom.id_apply, op_smul_castInitBlackRes_val]
    change (op (E 1) : BBᵐᵒᵖ) • (op (initBlockAlgHom Q Λ b x) : BBᵐᵒᵖ) •
        (initRestrictOf Q Λ b).symm m =
      (op (initBlockAlgHom Q Λ b x) : BBᵐᵒᵖ) • (op (E 1) : BBᵐᵒᵖ) • (initRestrictOf Q Λ b).symm m
    rw [smul_smul, smul_smul, ← op_mul, ← op_mul, blockBlackRes_one_mul_initBlockAlgHom]

theorem lastBlackProj_val (m : InitRestrict Q Λ b M) :
    (show M' from lastBlackProj Q Λ i h0 hr hκ M m).val =
      (op (E 1) : BBᵐᵒᵖ) • (initRestrictOf Q Λ b).symm m := rfl

theorem lastBlackProj_comp_incl :
    (lastBlackProj Q Λ i h0 hr hκ M).comp (lastBlackIncl Q Λ i h0 hr hκ M) = LinearMap.id :=
  LinearMap.ext fun m => Res.ext (op_blockBlackRes_one_smul_val Q Λ i h0 hr hκ M m)

local notation "Cyc" => CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
  (lastBlock b)
local notation "cL" => AbsentColour.cyclotomicLast Q i
  (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) (lastBlock b')
local notation "cc" => CyclotomicAction.castCyc Q
  (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i) hκ

theorem lastBlockAlgHom_flip_castCyc (c) :
    lastBlockAlgHom Q Λ b (CycKLR.flip _ (lastBlock b) (cc (cL c))) =
      E (lastBlockAlgHom Q Λ b' (CycKLR.flip _ (lastBlock b') c)) := by
  rw [blockBlackRes_lastBlockAlgHom_last]
  exact congrArg (lastBlockAlgHom Q Λ b)
    ((cycFlip_castCyc (Q := Q) (redCyc Λ (Fin.last ℓ)) hκ _).trans
      (congrArg _ (CycKLR.flip_cyclotomicLast (redCyc Λ (Fin.last ℓ)) (lastBlock b') i c)))

theorem lastBlockAlgHom_flip_castCyc_one :
    lastBlockAlgHom Q Λ b (CycKLR.flip _ (lastBlock b) (cc (cL 1))) = E 1 := by
  rw [lastBlockAlgHom_flip_castCyc, cycFlip_one, map_one]

theorem lastBlackIncl_comp_proj :
    (lastBlackIncl Q Λ i h0 hr hκ M).comp (lastBlackProj Q Λ i h0 hr hκ M) =
      lastFactorEnd Q Λ b (cc (cL 1)) := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨m, rfl⟩ := (initRestrictOf Q Λ b).surjective m
  rw [lastFactorEnd_of, lastBlockAlgHom_flip_castCyc_one]
  rfl

include h0 hr in
theorem initWeight_eq_of_last : initWeight b' = initWeight b :=
  congrArg (fun c => blockPrefix c (ℓ + 1)) (initBlocks_eq_of_last h0 hr)

variable (hα' : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))
  (hα'' : RootNonViolated (ν := initWeight b') (blockRoot (initBlocks b')))

include h0 hr hα' in
theorem rootNonViolated_initBlocks_of_last :
    RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b')) := by
  rw [initBlocks_eq_of_last h0 hr]
  exact hα'

local notation "hθ" => initWeight_eq_of_last h0 hr
local notation "hα₁" => rootNonViolated_initBlocks_of_last h0 hr hα'
local notation "Tfam" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc)
local notation "Tθ" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (initWeight b)
local notation "XL'" => LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b') rfl hα''
  (InitRestrict Q Λ b' M')
local notation "XL" => LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα'
  (InitRestrict Q Λ b M)
local notation "L₀" => BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα'

local notation "XC" => LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα' CM'

/-- The input `X_{M e}` over `T^{λ'}(θ)`, with `M e` regarded over the blocks `b`. -/
def lastBlackInputCast : FamilyCast Tfam hθ XL' ≃ₗ[Tθ] XC :=
  (leftStandardizationFamilyCast (Q := Q) (Λ := Λ ∘ Fin.castSucc) (InitRestrict Q Λ b' M') hθ
    rfl hθ hα'' hα₁).symm.trans
    (leftStandardizationCast Q (Λ ∘ Fin.castSucc) (InitRestrict Q Λ b' M') hinit hθ rfl hα₁ hα')

/-- `M e → M` on `M ⊗_{B'} S^L_{α'}`. -/
def lastBlackInclRight : XC →ₗ[Tθ] XL := BalancedTensor.mapRight (lastBlackIncl Q Λ i h0 hr hκ M)

/-- **`X_{M e} → X_M`**: the inclusion `M e → M` on the inputs of the two-piece
standardization, over `T^{λ'}(θ)`. -/
def lastBlackInputIncl : FamilyCast Tfam hθ XL' →ₗ[Tθ] XL :=
  (lastBlackInclRight Q Λ i h0 hr hκ M hα').comp
    (lastBlackInputCast Q Λ i h0 hr hκ M hα' hα'').toLinearMap

theorem lastBlackInputIncl_injective :
    Function.Injective (lastBlackInputIncl Q Λ i h0 hr hκ M hα' hα'') :=
  (BalancedTensor.mapRight_retract_injective (M := L₀)
    (lastBlackProj_comp_incl Q Λ i h0 hr hκ M)).comp
    (LinearEquiv.injective _)

theorem mem_range_lastBlackInputIncl (x : XL) :
    x ∈ LinearMap.range (lastBlackInputIncl Q Λ i h0 hr hκ M hα' hα'') ↔
      (BalancedTensor.mapRight (lastFactorEnd Q Λ b (cc (cL 1))) : XL →ₗ[Tθ] XL) x = x := by
  rw [← lastBlackIncl_comp_proj Q Λ i h0 hr hκ M, ← BalancedTensor.mem_range_mapRight_retract
    (lastBlackProj_comp_incl Q Λ i h0 hr hκ M)]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(lastBlackInputCast Q Λ i h0 hr hκ M hα' hα'').symm y, ?_⟩
    rw [lastBlackInputIncl, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    rfl

omit [DecidableEq I] in
include hκ in
theorem lastBlock_eq_of_last : lastBlock b = {i} + lastBlock b' := hκ.symm

local notation "N₁" => FactorCast Q Λ (rfl : initWeight b = initWeight b)
  (lastBlock_eq_of_last i hκ) (TwoPieceInput Q Λ b M hα')
local notation "X₁" => FactorCast Q Λ (initWeight_eq_of_last h0 hr)
  (rfl : lastBlock b' = lastBlock b') (TwoPieceInput Q Λ b' M' hα'')
local notation "Cyc'" => CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
  (lastBlock b')
local notation "ofX" => twoPieceInputOf Q Λ b M hα'
local notation "ofX'" => twoPieceInputOf Q Λ b' M' hα''

theorem rightAppendHom_tmul_smul (t : Tθ) (c : Cyc') (x : XL) :
    (rightAppendHom Q Λ i (initWeight b) (lastBlock b') (t ⊗ₜ c) • (show N₁ from ofX x) : N₁) =
      (show N₁ from ofX (t • (BalancedTensor.mapRight (lastFactorEnd Q Λ b (cc (cL c))) :
        XL →ₗ[Tθ] XL) x)) := by
  rw [factorCast_smul]
  change (show N₁ from (castFactor Q Λ rfl (lastBlock_eq_of_last i hκ)).symm (t ⊗ₜ cL c) • ofX x)
    = _
  rw [castFactor_symm_tmul, twoPieceInput_smul_def, twoPieceInputAction_tmul]
  rfl

theorem factorCast_tmul_smul_ofX' (t : Tθ) (c : Cyc') (x : XL') :
    ((t ⊗ₜ c : parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b')) • (show X₁ from ofX' x)
      : X₁) = (show X₁ from ofX' (castTensorProductAlgebra Q (Λ ∘ Fin.castSucc)
        (initWeight_eq_of_last h0 hr).symm t •
          (BalancedTensor.mapRight (lastFactorEnd Q Λ b' c) : XL' →ₗ[Tfam (initWeight b')] XL') x))
      := by
  rw [factorCast_smul, castFactor_symm_tmul, twoPieceInput_smul_def, twoPieceInputAction_tmul]
  rfl

theorem lastBlackIncl_comp_lastFactorEnd (c : Cyc') :
    (lastBlackIncl Q Λ i h0 hr hκ M).comp (castBlockModuleMap hinit (lastFactorEnd Q Λ b' c)) =
      (lastFactorEnd Q Λ b (cc (cL c))).comp (lastBlackIncl Q Λ i h0 hr hκ M) := by
  refine LinearMap.ext fun m => ?_
  change initRestrictOf Q Λ b ((op (E (lastBlockAlgHom Q Λ b' (CycKLR.flip _ (lastBlock b') c)))
    : BBᵐᵒᵖ) • (show M' from m).val) = initRestrictOf Q Λ b ((op (lastBlockAlgHom Q Λ b
      (CycKLR.flip _ (lastBlock b) (cc (cL c)))) : BBᵐᵒᵖ) • (show M' from m).val)
  rw [lastBlockAlgHom_flip_castCyc]

theorem lastBlackInclRight_mapRight (c : Cyc') (z : XC) :
    lastBlackInclRight Q Λ i h0 hr hκ M hα'
        (BalancedTensor.mapRight (castBlockModuleMap hinit (lastFactorEnd Q Λ b' c)) z) =
      BalancedTensor.mapRight (lastFactorEnd Q Λ b (cc (cL c)))
        (lastBlackInclRight Q Λ i h0 hr hκ M hα' z) := by
  rw [lastBlackInclRight, ← LinearMap.comp_apply, ← BalancedTensor.mapRight_comp,
    lastBlackIncl_comp_lastFactorEnd, BalancedTensor.mapRight_comp, LinearMap.comp_apply]

theorem lastBlackInputCast_mapRight (c : Cyc') (x : XL') :
    lastBlackInputCast Q Λ i h0 hr hκ M hα' hα''
        (show FamilyCast Tfam hθ XL' from
          (BalancedTensor.mapRight (lastFactorEnd Q Λ b' c) : XL' →ₗ[Tfam (initWeight b')] XL') x) =
      BalancedTensor.mapRight (castBlockModuleMap hinit (lastFactorEnd Q Λ b' c))
        (lastBlackInputCast Q Λ i h0 hr hκ M hα' hα'' (show FamilyCast Tfam hθ XL' from x)) := by
  rw [lastBlackInputCast, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    leftStandardizationFamilyCast_symm_mapRight, leftStandardizationCast_mapRight]

/-- **The inclusion `X_{M e} → X_M` is natural for the last factor.** -/
theorem lastBlackInputIncl_mapRight (c : Cyc') (x : XL') :
    lastBlackInputIncl Q Λ i h0 hr hκ M hα' hα''
        (show FamilyCast Tfam hθ XL' from
          (BalancedTensor.mapRight (lastFactorEnd Q Λ b' c) : XL' →ₗ[Tfam (initWeight b')] XL') x) =
      BalancedTensor.mapRight (lastFactorEnd Q Λ b (cc (cL c)))
        (lastBlackInputIncl Q Λ i h0 hr hκ M hα' hα'' (show FamilyCast Tfam hθ XL' from x)) := by
  change lastBlackInclRight Q Λ i h0 hr hκ M hα' (lastBlackInputCast Q Λ i h0 hr hκ M hα' hα'' _) =
    BalancedTensor.mapRight (lastFactorEnd Q Λ b (cc (cL c)))
      (lastBlackInclRight Q Λ i h0 hr hκ M hα' (lastBlackInputCast Q Λ i h0 hr hκ M hα' hα'' _))
  rw [lastBlackInputCast_mapRight, lastBlackInclRight_mapRight]

theorem factorCast_tmul_smul' (t : Tθ) (c : Cyc') (x : X₁) :
    ((t ⊗ₜ c : parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b')) • x : X₁) =
      (show X₁ from ofX' (castTensorProductAlgebra Q (Λ ∘ Fin.castSucc)
        (initWeight_eq_of_last h0 hr).symm t •
          (BalancedTensor.mapRight (lastFactorEnd Q Λ b' c) : XL' →ₗ[Tfam (initWeight b')] XL')
            (show XL' from x))) :=
  factorCast_tmul_smul_ofX' Q Λ i h0 hr hκ M hα'' t c x

theorem rightAppendHom_one_smul (x : XL) :
    (rightAppendHom Q Λ i (initWeight b) (lastBlock b') 1 • (show N₁ from ofX x) : N₁) =
      (show N₁ from ofX ((BalancedTensor.mapRight (lastFactorEnd Q Λ b (cc (cL 1))) :
        XL →ₗ[Tθ] XL) x)) := by
  rw [Algebra.TensorProduct.one_def, rightAppendHom_tmul_smul, one_smul]

local notation "inc" => lastBlackInputIncl Q Λ i h0 hr hκ M hα' hα''

theorem mapRight_lastBlackInputIncl (x : FamilyCast Tfam hθ XL') :
    (BalancedTensor.mapRight (lastFactorEnd Q Λ b (cc (cL 1))) : XL →ₗ[Tθ] XL) (inc x) = inc x :=
  (mem_range_lastBlackInputIncl Q Λ i h0 hr hκ M hα' hα'' (inc x)).1 ⟨x, rfl⟩

theorem familyCast_smul_initWeight (t : Tθ) (x : XL') :
    t • (show FamilyCast Tfam hθ XL' from x) = (show FamilyCast Tfam hθ XL' from
      castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) (initWeight_eq_of_last h0 hr).symm t • x) :=
  familyCast_tensorProductAlgebra_smul hθ t x

/-- The underlying additive map of `X_{M e} ≅ ₂Eᵢ X_M`. -/
def lastBlackInputHom : X₁ →+ RightResRight Q Λ i (initWeight b) (lastBlock b') N₁ where
  toFun x := Res.mk (show N₁ from ofX (inc (show FamilyCast Tfam hθ XL' from x)))
    (by rw [rightAppendHom_one_smul, mapRight_lastBlackInputIncl])
  map_zero' := Res.ext (by
    change (show N₁ from ofX (inc 0)) = 0
    rw [map_zero]
    rfl)
  map_add' x y := Res.ext (by
    change (show N₁ from ofX (inc (show FamilyCast Tfam hθ XL' from x + y))) =
      (show N₁ from ofX (inc (show FamilyCast Tfam hθ XL' from x))) +
        (show N₁ from ofX (inc (show FamilyCast Tfam hθ XL' from y)))
    rw [show (show FamilyCast Tfam hθ XL' from x + y) =
      (show FamilyCast Tfam hθ XL' from x) + (show FamilyCast Tfam hθ XL' from y) from rfl,
      map_add]
    rfl)

theorem lastBlackInputHom_val (x : X₁) :
    (lastBlackInputHom Q Λ i h0 hr hκ M hα' hα'' x).val =
      (show N₁ from ofX (inc (show FamilyCast Tfam hθ XL' from x))) := rfl

theorem lastBlackInputHom_tmul_one (t : Tθ) (x : X₁) :
    lastBlackInputHom Q Λ i h0 hr hκ M hα' hα''
        ((t ⊗ₜ (1 : Cyc') : parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b')) • x) =
      (t ⊗ₜ (1 : Cyc') : parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b')) •
        lastBlackInputHom Q Λ i h0 hr hκ M hα' hα'' x := by
  refine Res.ext ?_
  rw [Res.val_smul, lastBlackInputHom_val, lastBlackInputHom_val,
    rightAppendHom_tmul_smul Q Λ i hκ M hα',
    mapRight_lastBlackInputIncl Q Λ i h0 hr hκ M hα' hα'',
    factorCast_tmul_smul' Q Λ i h0 hr hκ M hα'', lastFactorEnd_one,
    BalancedTensor.mapRight_id, LinearMap.id_apply]
  change (show N₁ from ofX (inc (show FamilyCast Tfam hθ XL' from
    castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) (initWeight_eq_of_last h0 hr).symm t •
      (show XL' from x)))) = _
  rw [← familyCast_smul_initWeight, map_smul]

theorem lastBlackInputHom_one_tmul (c : Cyc') (x : X₁) :
    lastBlackInputHom Q Λ i h0 hr hκ M hα' hα''
        (((1 : Tθ) ⊗ₜ c : parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b')) • x) =
      ((1 : Tθ) ⊗ₜ c : parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b')) •
        lastBlackInputHom Q Λ i h0 hr hκ M hα' hα'' x := by
  refine Res.ext ?_
  rw [Res.val_smul, lastBlackInputHom_val, lastBlackInputHom_val,
    rightAppendHom_tmul_smul Q Λ i hκ M hα',
    factorCast_tmul_smul' Q Λ i h0 hr hκ M hα'', map_one, one_smul, one_smul]
  change (show N₁ from ofX (inc (show FamilyCast Tfam hθ XL' from
    (BalancedTensor.mapRight (lastFactorEnd Q Λ b' c) : XL' →ₗ[Tfam (initWeight b')] XL')
      (show XL' from x)))) = _
  rw [lastBlackInputIncl_mapRight]

theorem lastBlackInputHom_injective :
    Function.Injective (lastBlackInputHom Q Λ i h0 hr hκ M hα' hα'') := by
  intro x y hxy
  have h := congrArg Res.val hxy
  rw [lastBlackInputHom_val, lastBlackInputHom_val] at h
  exact lastBlackInputIncl_injective Q Λ i h0 hr hκ M hα' hα'' ((twoPieceInputOf Q Λ b M hα').injective h)

theorem lastBlackInputHom_surjective :
    Function.Surjective (lastBlackInputHom Q Λ i h0 hr hκ M hα' hα'') := by
  intro y
  have hy : (BalancedTensor.mapRight (lastFactorEnd Q Λ b (cc (cL 1))) : XL →ₗ[Tθ] XL)
      (show XL from y.val) = show XL from y.val := by
    have h1 := y.prop
    rw [show y.val = (show N₁ from ofX (show XL from y.val)) from rfl,
      rightAppendHom_one_smul Q Λ i hκ M hα'] at h1
    exact (twoPieceInputOf Q Λ b M hα').injective h1
  obtain ⟨x, hx⟩ := (mem_range_lastBlackInputIncl Q Λ i h0 hr hκ M hα' hα'' _).2 hy
  exact ⟨x, Res.ext (by rw [lastBlackInputHom_val, hx]; rfl)⟩

/-- **`₂Eᵢ X_M ≅ X_{M e}`** (Webster, arXiv:1309.3796v3, proof of Proposition 5.5): restricting the
input `X_M` of the two-piece standardization along the last black strand of colour `i` of the last
factor gives the input of `ₗEᵢ M = M e`, as modules over `T^{λ'}(θ) ⊗ R^{λ_ℓ}(b'_{ℓ+1})`. -/
def lastBlackInputEquiv :
    X₁ ≃ₗ[parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b')]
      RightResRight Q Λ i (initWeight b) (lastBlock b') N₁ :=
  LinearEquiv.ofBijective
    (tensorLinearOfGenerators (lastBlackInputHom Q Λ i h0 hr hκ M hα' hα'')
      (lastBlackInputHom_tmul_one Q Λ i h0 hr hκ M hα' hα'')
      (lastBlackInputHom_one_tmul Q Λ i h0 hr hκ M hα' hα''))
    ⟨lastBlackInputHom_injective Q Λ i h0 hr hκ M hα' hα'',
      lastBlackInputHom_surjective Q Λ i h0 hr hκ M hα' hα''⟩

theorem lastBlackInputEquiv_val (x : X₁) :
    (lastBlackInputEquiv Q Λ i h0 hr hκ M hα' hα'' x).val =
      (show N₁ from ofX (inc (show FamilyCast Tfam hθ XL' from x))) := rfl

end StendhalAlgebra

end Categorification.Stendhal
