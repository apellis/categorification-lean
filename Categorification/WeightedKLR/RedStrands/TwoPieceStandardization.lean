/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceBlockAlgebraAction

/-!
# The standardization of `ℓ + 1` red strands through that of the first `ℓ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Definition 5.4 and proof of Proposition 5.5. Let `M` be a right module over the block algebra
`B` of `ℓ + 1` red strands. Restricting along the block algebra `B'` of the first `ℓ` red strands
(`initBlockAlgHom`), `X_M = M ⊗_{B'} S^L_{α'}` is a left `T^{λ'}`-module, and the last factor
`R^{λ_{ℓ+1}}(β)` acts on it through `M` (`m ↦ m · flip(c)`), commuting with `T^{λ'}`. So `X_M` is a
module over the factor algebra `T^{λ'} ⊗ R^{λ_{ℓ+1}}(β)` (`TwoPieceInput`).

## Main definitions

* `StendhalAlgebra.InitRestrict`: `M` as a right `B'`-module.
* `StendhalAlgebra.lastFactorEnd`: the right action of the last factor on `M`, flipped.
* `StendhalAlgebra.TwoPieceInput`: `X_M` as a module over the factor algebra.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (b : Fin (ℓ + 2) → Multiset I)

local notation "𝔹" => BlockAlgebra k Q Λ b
local notation "B'" => BlockAlgebra k Q (Λ ∘ Fin.castSucc) (initBlocks b)
local notation "Cyc" => CycKLR k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
  (lastBlock b)
local notation "fl" => CycKLR.flip (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
  (lastBlock b)
local notation "Told" => TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) (initWeight b)
local notation "D" => parabolicFactorAlgebra Q Λ (initWeight b) (lastBlock b)

/-- A right module over the block algebra of `ℓ + 1` red strands, restricted to the block algebra
of the first `ℓ`. -/
@[nolint unusedArguments]
def InitRestrict (_Q : I → I → MvPolynomial (Fin 2) k) (_Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (_b : Fin (ℓ + 2) → Multiset I) (M : Type*) : Type _ := M

variable (M : Type*) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]


instance : AddCommGroup (InitRestrict Q Λ b M) := inferInstanceAs (AddCommGroup M)
instance : Module k (InitRestrict Q Λ b M) := inferInstanceAs (Module k M)
instance : Module B'ᵐᵒᵖ (InitRestrict Q Λ b M) :=
  Module.compHom M (AlgHom.op (initBlockAlgHom Q Λ b)).toRingHom
variable {M} in
/-- The identity `M → InitRestrict M`. -/
def initRestrictOf : M ≃ₗ[k] InitRestrict Q Λ b M := LinearEquiv.refl k M

theorem op_smul_initRestrictOf (x : B') (m : M) :
    (op x : B'ᵐᵒᵖ) • initRestrictOf Q Λ b m =
      initRestrictOf Q Λ b ((op (initBlockAlgHom Q Λ b x) : 𝔹ᵐᵒᵖ) • m) :=
  rfl

instance [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] :
    IsScalarTower k B'ᵐᵒᵖ (InitRestrict Q Λ b M) where
  smul_assoc c a m := by
    change (AlgHom.op (initBlockAlgHom Q Λ b) (c • a)) • (initRestrictOf Q Λ b).symm m =
      c • ((AlgHom.op (initBlockAlgHom Q Λ b) a) • (initRestrictOf Q Λ b).symm m)
    rw [map_smul, smul_assoc]

variable {M}

/-- The right action of `flip(c)`, `c` in the last factor, on `M`, as a map of right
`B'`-modules. -/
def lastFactorEnd (c : Cyc) : InitRestrict Q Λ b M →ₗ[B'ᵐᵒᵖ] InitRestrict Q Λ b M where
  toFun m := initRestrictOf Q Λ b
    ((op (lastBlockAlgHom Q Λ b (fl c)) : 𝔹ᵐᵒᵖ) • (initRestrictOf Q Λ b).symm m)
  map_add' m m' := by rw [map_add, smul_add, map_add]
  map_smul' a m := by
    obtain ⟨m, rfl⟩ := (initRestrictOf Q Λ b).surjective m
    induction a using MulOpposite.rec' with | _ x =>
    rw [op_smul_initRestrictOf, RingHom.id_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, op_smul_initRestrictOf, smul_smul, smul_smul, ← op_mul,
      ← op_mul, (commute_initBlockAlgHom_lastBlockAlgHom Q Λ b x (fl c)).eq]

theorem lastFactorEnd_of (c : Cyc) (m : M) :
    lastFactorEnd Q Λ b c (initRestrictOf Q Λ b m) =
      initRestrictOf Q Λ b ((op (lastBlockAlgHom Q Λ b (fl c)) : 𝔹ᵐᵒᵖ) • m) := rfl

theorem flip_one_last : fl (1 : Cyc) = 1 := by
  rw [← map_one (CycKLR.mk k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
    (lastBlock b)), CycKLR.flip_mk, KLRAlgebra.hflip_one]

theorem lastFactorEnd_one : lastFactorEnd Q Λ b (1 : Cyc) = (LinearMap.id :
    InitRestrict Q Λ b M →ₗ[B'ᵐᵒᵖ] InitRestrict Q Λ b M) := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨m, rfl⟩ := (initRestrictOf Q Λ b).surjective m
  rw [lastFactorEnd_of, flip_one_last, map_one, op_one, one_smul, LinearMap.id_apply]

theorem lastFactorEnd_mul (c c' : Cyc) :
    lastFactorEnd Q Λ b (M := M) (c * c') = lastFactorEnd Q Λ b c ∘ₗ lastFactorEnd Q Λ b c' := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨m, rfl⟩ := (initRestrictOf Q Λ b).surjective m
  rw [LinearMap.comp_apply, lastFactorEnd_of, lastFactorEnd_of, lastFactorEnd_of,
    CycKLR.flip_mul, map_mul, op_mul, mul_smul]

theorem CycKLR.flip_smul_one_last (c : k) : fl (c • (1 : Cyc)) = c • 1 := by
  rw [← map_one (CycKLR.mk k Q (fun i : I => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) i)
    (lastBlock b)), ← map_smul, CycKLR.flip_mk, KLRAlgebra.hflip_smul, KLRAlgebra.hflip_one]

theorem flip_add_last (c c' : Cyc) : fl (c + c') = fl c + fl c' := by
  obtain ⟨u, rfl⟩ := CycKLR.mk_surjective c
  obtain ⟨u', rfl⟩ := CycKLR.mk_surjective c'
  rw [← map_add, CycKLR.flip_mk, CycKLR.flip_mk, CycKLR.flip_mk, KLRAlgebra.hflip_add, map_add]

theorem lastFactorEnd_add (c c' : Cyc) :
    lastFactorEnd Q Λ b (M := M) (c + c') = lastFactorEnd Q Λ b c + lastFactorEnd Q Λ b c' := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨m, rfl⟩ := (initRestrictOf Q Λ b).surjective m
  rw [LinearMap.add_apply, lastFactorEnd_of, lastFactorEnd_of, lastFactorEnd_of, flip_add_last,
    map_add, op_add, add_smul, map_add]

section Input

variable [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  (hα' : RootNonViolated (ν := initWeight b) (blockRoot (initBlocks b)))

local notation "L'" => BlockLeftStandard Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα'

theorem BalancedTensor.mapRight_add' {g g' : InitRestrict Q Λ b M →ₗ[B'ᵐᵒᵖ] InitRestrict Q Λ b M} :
    BalancedTensor.mapRight (k := k) (B := Told) (M := L') (g + g') =
      BalancedTensor.mapRight g + BalancedTensor.mapRight g' :=
  BalancedTensor.extB fun l m => BalancedTensor.tmul_add l (g m) (g' m)

variable (M) in
/-- The action of the last factor on `X_M = M ⊗_{B'} S^L_{α'}`, through `m ↦ m · flip(c)`. -/
def lastFactorAction : Cyc →ₐ[k] Module.End k
    (LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα' (InitRestrict Q Λ b M)) where
  toFun c := (BalancedTensor.mapRight (k := k) (B := Told) (M := L') (lastFactorEnd Q Λ b c)).restrictScalars k
  map_one' := by
    rw [lastFactorEnd_one, BalancedTensor.mapRight_id]
    rfl
  map_mul' c c' := by
    rw [lastFactorEnd_mul, BalancedTensor.mapRight_comp]
    rfl
  map_zero' := by
    have h : lastFactorEnd Q Λ b (M := M) (0 : Cyc) = 0 := by
      have := lastFactorEnd_add Q Λ b (M := M) (0 : Cyc) 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    rw [h]
    refine LinearMap.ext fun x => ?_
    induction x using BalancedTensor.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul l m => exact BalancedTensor.tmul_zero (N := InitRestrict Q Λ b M) l
    | add x y hx hy =>
      rw [map_add, hx, hy, LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply,
        add_zero]
  map_add' c c' := by
    rw [lastFactorEnd_add, BalancedTensor.mapRight_add']
    rfl
  commutes' c := by
    refine LinearMap.ext fun x => ?_
    induction x using BalancedTensor.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul l m =>
      obtain ⟨m, rfl⟩ := (initRestrictOf Q Λ b).surjective m
      rw [Module.algebraMap_end_apply]
      change BalancedTensor.tmul l (lastFactorEnd Q Λ b _ _) = _
      rw [lastFactorEnd_of, Algebra.algebraMap_eq_smul_one, CycKLR.flip_smul_one_last,
        map_smul (lastBlockAlgHom Q Λ b), map_one (lastBlockAlgHom Q Λ b), MulOpposite.op_smul,
        op_one, smul_assoc, one_smul, map_smul (initRestrictOf Q Λ b)]
      exact BalancedTensor.tmul_smul c l _
    | add x y hx hy => rw [map_add, map_add, hx, hy]

variable (M) in
/-- **The factor algebra `T^{λ'} ⊗ R^{λ_{ℓ+1}}(β)` acting on `X_M`.** -/
def twoPieceInputAction : D →ₐ[k] Module.End k
    (LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα' (InitRestrict Q Λ b M)) :=
  Algebra.TensorProduct.lift (Algebra.lsmul k k _) (lastFactorAction Q Λ b M hα')
    fun t c => LinearMap.ext fun x =>
      ((BalancedTensor.mapRight (k := k) (B := Told) (M := L') (lastFactorEnd Q Λ b c)).map_smul
        t x).symm

variable (M) in
/-- **`X_M = M ⊗_{B'} S^L_{α'}`** as a module over the factor algebra `T^{λ'} ⊗ R^{λ_{ℓ+1}}(β)`:
`T^{λ'}` acts on `S^L_{α'}` and `c` in the last factor by `m ↦ m · flip(c)`. -/
def TwoPieceInput : Type _ :=
  LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα' (InitRestrict Q Λ b M)

instance : AddCommGroup (TwoPieceInput Q Λ b M hα') :=
  inferInstanceAs (AddCommGroup
    (LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα' (InitRestrict Q Λ b M)))
instance : Module k (TwoPieceInput Q Λ b M hα') :=
  inferInstanceAs (Module k
    (LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα' (InitRestrict Q Λ b M)))
instance : Module D (TwoPieceInput Q Λ b M hα') :=
  Module.compHom
    (LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα' (InitRestrict Q Λ b M))
    (twoPieceInputAction Q Λ b M hα').toRingHom
instance : IsScalarTower k D (TwoPieceInput Q Λ b M hα') :=
  ⟨fun c d x => DFunLike.congr_fun (map_smul (twoPieceInputAction Q Λ b M hα') c d) x⟩

variable (M) in
/-- The identity `X_M → TwoPieceInput`. -/
def twoPieceInputOf : LeftStandardization Q (Λ ∘ Fin.castSucc) (initBlocks b) rfl hα'
    (InitRestrict Q Λ b M) ≃ₗ[k] TwoPieceInput Q Λ b M hα' := LinearEquiv.refl k _

theorem tmul_smul_twoPieceInputOf (t : Told) (c : Cyc) (l : L') (m : InitRestrict Q Λ b M) :
    (t ⊗ₜ c : D) • twoPieceInputOf Q Λ b M hα' (BalancedTensor.tmul l m) =
      twoPieceInputOf Q Λ b M hα' (BalancedTensor.tmul (t • l) (lastFactorEnd Q Λ b c m)) := by
  change twoPieceInputAction Q Λ b M hα' (t ⊗ₜ c) _ = _
  rw [twoPieceInputAction, Algebra.TensorProduct.lift_tmul, Module.End.mul_apply]
  exact (BalancedTensor.smul_tmul' t l (lastFactorEnd Q Λ b c m))

end Input

end StendhalAlgebra

end Categorification.Stendhal
