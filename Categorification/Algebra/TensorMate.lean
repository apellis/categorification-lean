/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.RightDualModule
import DG.Module.TensorProductOver

/-!
# The mate of an isomorphism of tensor products of bimodules

Let `K` be an `(R₂, R₁)`-bimodule, `K_b` an `(R₃, R₀)`-bimodule, `S` an `(R₁, R₀)`-bimodule that
is finitely generated projective as a right `R₀`-module, and `S₊` an `(R₂, R₃)`-bimodule. A map
of `(R₂, R₀)`-bimodules `κ : K ⊗_{R₁} S → S₊ ⊗_{R₃} K_b` has a mate

`Φ : S₊^∨ ⊗_{R₂} K → K_b ⊗_{R₀} S^∨`, `f ⊗ r ↦ Σ_i ev_f (κ (r ⊗ e_i)) ⊗ φ_i`,

where `(e_i, φ_i)` is a dual basis of `S` and `ev_f (p ⊗ x) = f(p) x`. It is a map of
`(R₃, R₁)`-bimodules (`TensorMate.mateLinear`, `TensorMate.mate_op_smul`).

This is the bimodule isomorphism `Φ` that the exchange of right adjoints
(`rightAdjointExchangeIso`) takes as input, for B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, Lemma 7.19, trace half: with `κ` the isomorphism of
Lemma 7.19 (K), its mate is the comparison of the trace half.

## Main definitions

* `TensorMate.dualEv`: `ev_f : S₊ ⊗_{R₃} K_b → K_b`, `p ⊗ x ↦ f(p) x`.
* `TensorMate.mate`, `TensorMate.mateLinear`: the mate `Φ`.

## Main results

* `TensorMate.mate_tmul`, `TensorMate.mate_op_smul`.
-/

noncomputable section

namespace Categorification

namespace TensorMate

open DG MulOpposite
open scoped DG.TensorProductOver.RightAction

universe u

variable {R₀ R₁ R₂ R₃ : Type u} [Ring R₀] [Ring R₁] [Ring R₂] [Ring R₃]
  {K : Type u} [AddCommGroup K] [Module R₂ K] [Module R₁ᵐᵒᵖ K] [SMulCommClass R₂ R₁ᵐᵒᵖ K]
  {Kb : Type u} [AddCommGroup Kb] [Module R₃ Kb] [Module R₀ᵐᵒᵖ Kb] [SMulCommClass R₃ R₀ᵐᵒᵖ Kb]
  {S : Type u} [AddCommGroup S] [Module R₁ S] [Module R₀ᵐᵒᵖ S]
  {Sp : Type u} [AddCommGroup Sp] [Module R₂ Sp] [Module R₃ᵐᵒᵖ Sp] [SMulCommClass R₂ R₃ᵐᵒᵖ Sp]

section Eval

variable (Kb) in
/-- **The evaluation `ev_f : S₊ ⊗_{R₃} K_b → K_b`**, `p ⊗ x ↦ f(p) x`. -/
def dualEv (f : RightDualModule R₃ Sp) : TensorProductOver R₃ Sp Kb →+ Kb :=
  TensorProductOver.lift
    (AddMonoidHom.mk' (fun p => DistribSMul.toAddMonoidHom Kb (unop (f p))) fun p p' =>
      AddMonoidHom.ext fun x => by
        simp only [map_add, unop_add, AddMonoidHom.add_apply,
          DistribSMul.toAddMonoidHom_apply, add_smul])
    fun a p x => by
      simp only [AddMonoidHom.mk'_apply, DistribSMul.toAddMonoidHom_apply, map_smul,
        smul_eq_mul, unop_mul, unop_op, mul_smul]

theorem dualEv_tmul (f : RightDualModule R₃ Sp) (p : Sp) (x : Kb) :
    dualEv Kb f (TensorProductOver.tmul R₃ p x) = unop (f p) • x := rfl

theorem dualEv_add (f g : RightDualModule R₃ Sp) (q : TensorProductOver R₃ Sp Kb) :
    dualEv Kb (f + g) q = dualEv Kb f q + dualEv Kb g q := by
  induction q using TensorProductOver.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul p x => simp only [dualEv_tmul, RightDualModule.add_apply, unop_add, add_smul]
  | add q q' hq hq' => simp only [map_add, hq, hq']; abel

theorem dualEv_smul (a : R₃) (f : RightDualModule R₃ Sp) (q : TensorProductOver R₃ Sp Kb) :
    dualEv Kb (a • f) q = a • dualEv Kb f q := by
  induction q using TensorProductOver.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul p x => rw [dualEv_tmul, dualEv_tmul, RightDualModule.smul_apply, unop_mul, unop_op,
      mul_smul]
  | add q q' hq hq' => rw [map_add, map_add, hq, hq', smul_add]

theorem dualEv_op_smul (t : R₂) (f : RightDualModule R₃ Sp) (q : TensorProductOver R₃ Sp Kb) :
    dualEv Kb (op t • f) q = dualEv Kb f (t • q) := by
  induction q using TensorProductOver.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul p x => rfl
  | add q q' hq hq' => rw [map_add, hq, hq', smul_add, map_add]

theorem dualEv_rightAct (f : RightDualModule R₃ Sp) (c : R₀ᵐᵒᵖ)
    (q : TensorProductOver R₃ Sp Kb) : dualEv Kb f (c • q) = c • dualEv Kb f q := by
  induction q using TensorProductOver.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul p x =>
    change dualEv Kb f (TensorProductOver.tmul R₃ p (c • x)) = _
    rw [dualEv_tmul, dualEv_tmul, smul_comm]
  | add q q' hq hq' => rw [smul_add, map_add, map_add, hq, hq', smul_add]

end Eval

theorem tmul_sum {A M N : Type*} [Ring A] [AddCommGroup M] [Module Aᵐᵒᵖ M] [AddCommGroup N]
    [Module A N] {ι : Type*} (s : Finset ι) (m : M) (n : ι → N) :
    TensorProductOver.tmul A m (∑ i ∈ s, n i) = ∑ i ∈ s, TensorProductOver.tmul A m (n i) :=
  map_sum (TensorProductOver.tmulAddHom A M N m) n s

theorem sum_tmul {A M N : Type*} [Ring A] [AddCommGroup M] [Module Aᵐᵒᵖ M] [AddCommGroup N]
    [Module A N] {ι : Type*} (s : Finset ι) (m : ι → M) (n : N) :
    TensorProductOver.tmul A (∑ i ∈ s, m i) n = ∑ i ∈ s, TensorProductOver.tmul A (m i) n :=
  map_sum ((TensorProductOver.tmulAddHom A M N).flip n) m s

variable [Module.Projective R₀ᵐᵒᵖ S] [Module.Finite R₀ᵐᵒᵖ S]

local notation "e" => RightDualModule.dualBasisVec R₀ S
local notation "φ" => RightDualModule.dualBasisCoord R₀ S

section Mate

variable (R₀) (κ : TensorProductOver R₁ K S →+ TensorProductOver R₃ Sp Kb)
  (hκ : ∀ (t : R₂) (x : TensorProductOver R₁ K S), κ (t • x) = t • κ x)

/-- The bi-additive map `(f, r) ↦ Σ_i ev_f (κ (r ⊗ e_i)) ⊗ φ_i`. -/
def mateBil : RightDualModule R₃ Sp →+ K →+ TensorProductOver R₀ Kb (RightDualModule R₀ S) :=
  AddMonoidHom.mk' (fun f => AddMonoidHom.mk'
    (fun r => ∑ i, TensorProductOver.tmul R₀ (dualEv Kb f (κ (TensorProductOver.tmul R₁ r (e i))))
      (φ i))
    fun r r' => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProductOver.add_tmul, map_add, map_add, TensorProductOver.add_tmul])
    fun f g => AddMonoidHom.ext fun r => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dualEv_add, TensorProductOver.add_tmul]

omit [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] in
theorem mateBil_apply (f : RightDualModule R₃ Sp) (r : K) :
    mateBil R₀ κ f r = ∑ i, TensorProductOver.tmul R₀
      (dualEv Kb f (κ (TensorProductOver.tmul R₁ r (e i)))) (φ i) := rfl

omit [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] in
include hκ in
theorem mateBil_balanced (t : R₂) (f : RightDualModule R₃ Sp) (r : K) :
    mateBil R₀ κ (op t • f) r = mateBil R₀ κ f (t • r) := by
  simp only [mateBil_apply, dualEv_op_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hκ]
  rfl

/-- **The mate `Φ : S₊^∨ ⊗_{R₂} K → K_b ⊗_{R₀} S^∨`** of `κ : K ⊗_{R₁} S → S₊ ⊗_{R₃} K_b`. -/
def mate : TensorProductOver R₂ (RightDualModule R₃ Sp) K →+
    TensorProductOver R₀ Kb (RightDualModule R₀ S) :=
  TensorProductOver.lift (mateBil R₀ κ) (mateBil_balanced R₀ κ hκ)

omit [SMulCommClass R₃ R₀ᵐᵒᵖ Kb] in
theorem mate_tmul (f : RightDualModule R₃ Sp) (r : K) :
    mate R₀ κ hκ (TensorProductOver.tmul R₂ f r) = ∑ i, TensorProductOver.tmul R₀
      (dualEv Kb f (κ (TensorProductOver.tmul R₁ r (e i)))) (φ i) := rfl

theorem mate_smul (a : R₃) (y : TensorProductOver R₂ (RightDualModule R₃ Sp) K) :
    mate R₀ κ hκ (a • y) = a • mate R₀ κ hκ y := by
  induction y using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul f r =>
    rw [TensorProductOver.smul_tmul, mate_tmul, mate_tmul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dualEv_smul, TensorProductOver.smul_tmul]
  | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', smul_add]

/-- **The mate as a map of left `R₃`-modules.** -/
def mateLinear : TensorProductOver R₂ (RightDualModule R₃ Sp) K →ₗ[R₃]
    TensorProductOver R₀ Kb (RightDualModule R₀ S) where
  toFun := mate R₀ κ hκ
  map_add' := map_add _
  map_smul' := mate_smul R₀ κ hκ

theorem mateLinear_apply (y : TensorProductOver R₂ (RightDualModule R₃ Sp) K) :
    mateLinear R₀ κ hκ y = mate R₀ κ hκ y := rfl

end Mate

section Right

variable [SMulCommClass R₁ R₀ᵐᵒᵖ S] (R₀)
  (κ : TensorProductOver R₁ K S →+ TensorProductOver R₃ Sp Kb)
  (hκ : ∀ (t : R₂) (x : TensorProductOver R₁ K S), κ (t • x) = t • κ x)
  (hκr : ∀ (c : R₀ᵐᵒᵖ) (x : TensorProductOver R₁ K S), κ (c • x) = c • κ x)

/-- `r ⊗ b e_i = Σ_j (r ⊗ e_j) φ_j(b e_i)`. -/
theorem tmul_smul_dualBasisVec (r : K) (s : S) :
    (TensorProductOver.tmul R₁ r s : TensorProductOver R₁ K S) =
      ∑ j, φ j s • TensorProductOver.tmul R₁ r (e j) := by
  conv_lhs => rw [← RightDualModule.sum_dualBasis R₀ S s]
  rw [tmul_sum]
  rfl

include hκr in
/-- **The mate is right `R₁`-linear.** -/
theorem mate_op_smul (b : R₁) (y : TensorProductOver R₂ (RightDualModule R₃ Sp) K) :
    mate R₀ κ hκ (op b • y) = op b • mate R₀ κ hκ y := by
  induction y using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul f r =>
    change mate R₀ κ hκ (TensorProductOver.tmul R₂ f (op b • r)) =
      TensorProductOver.rightAct R₀ Kb (RightDualModule R₀ S) (op b) (mate R₀ κ hκ _)
    rw [mate_tmul, mate_tmul, map_sum]
    simp only [TensorProductOver.rightAct_tmul]
    have h1 : ∀ i, TensorProductOver.tmul R₁ (op b • r) (e i) =
        ∑ j, φ j (b • e i) • TensorProductOver.tmul R₁ r (e j) := fun i => by
      rw [TensorProductOver.op_smul_tmul, tmul_smul_dualBasisVec R₀]
    have h2 : ∀ i j, TensorProductOver.tmul R₀
        (dualEv Kb f (κ (φ j (b • e i) • TensorProductOver.tmul R₁ r (e j)))) (φ i) =
        TensorProductOver.tmul R₀ (dualEv Kb f (κ (TensorProductOver.tmul R₁ r (e j))))
          (unop (φ j (b • e i)) • φ i) := fun i j => by
      rw [hκr, dualEv_rightAct, ← TensorProductOver.op_smul_tmul, op_unop]
    simp only [h1, map_sum, sum_tmul, h2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← tmul_sum]
    congr 1
    exact RightDualModule.sum_dualBasis_dual R₀ S (op b • φ j)
  | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', smul_add]

end Right

end TensorMate

end Categorification
