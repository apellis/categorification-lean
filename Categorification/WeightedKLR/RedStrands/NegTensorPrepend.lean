/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.NegativeTensor
import LieLean.Algebra.QuantumGroup.Verma

/-!
# The coproduct map `u ⊗ w ↦ u_{(1)} ⊗ u_{(2)} v_λ ⊗ w`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 4.39, (4.40): the reflected red induction `Ĩ_λ^*` corresponds to
`u ⊗ w ↦ u_{(1)} ⊗ (u_{(2)} v_λ ⊗ w)` on `U⁻ ⊗ V^λ`, in Sweedler notation for the coproduct
of `u`. Here `U⁻ = 'f ⧸ J` is identified with the Verma module `M(0)` by `y ↦ y⁻ m₀`, and
`u_{(1)} ⊗ u_{(2)} v_λ` is the action of `Δ(u⁻)` on `m₀ ⊗ v_λ ∈ M(0) ⊗ V_λ`, read back in
`U⁻ ⊗ V_λ`. With `Δ(F_i) = F_i ⊗ K_{-ĩ} + 1 ⊗ F_i` this is the vector obtained from `1 ⊗ v_λ`
by the operators `F̃_i` of `U⁻ ⊗ V_λ` (`negCoprod_negF`).

## Main definitions and results

* `negCoprod` : `U⁻ → U⁻ ⊗ V_λ`, `u ↦ Δ(u)(1 ⊗ v_λ)`.
* `negTensorPrepend` : `U⁻ ⊗ V^λ → U⁻ ⊗ V_{λ₀} ⊗ V^λ`, `u ⊗ w ↦ Δ(u)(1 ⊗ v_{λ₀}) ⊗ w`.
* `negTensorPrepend_negTensorF` : it intertwines the operators `F̃_i`.
* `negWordVector_prependRed` : `p̃_{λ₀ w}` is the image of `p̃_w`.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance instNeZeroXNegTensorPrepend : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y}

private abbrev Factor (wt : Dom R) := IrreducibleModule R 𝕍 wt.1

local notation "ρ" => tensorRepresentation
local notation "Δ" => comul R 𝕍
local notation "Mv" => VermaModule R 𝕍 (0 : Y →+ ℤ)

private theorem powNeOne : ∀ n : ℕ, 0 < n → 𝕍 ^ n ≠ 1 :=
  pow_ne_one_of_transcendental' transcendental_ratFuncX

/-- `U⁻ ≃ M(0)`, `[y] ↦ y⁻ m₀`. -/
private def vermaEquiv : Um D 𝕍 ≃ₗ[𝕂] Mv :=
  VermaModule.equivSerreQuotient (R := R) 0 powNeOne

private theorem vermaEquiv_mk (y : LusztigF 𝕂 I) :
    vermaEquiv (R := R) (Submodule.Quotient.mk y) =
      minusHom R 𝕍 y • VermaModule.hwv R 𝕍 0 := rfl

private theorem vermaEquiv_negF (i : I) (u : Um D 𝕍) :
    vermaEquiv (R := R) (negF D i u) = F R 𝕍 i • vermaEquiv (R := R) u := by
  induction u using Submodule.Quotient.induction_on with
  | H y =>
    rw [negF_mk, vermaEquiv_mk, vermaEquiv_mk, map_mul, mul_smul]
    simp [minusHom]

private theorem vermaEquiv_symm_F (i : I) :
    (vermaEquiv (R := R)).symm.toLinearMap ∘ₗ Algebra.lsmul 𝕂 𝕂 Mv (F R 𝕍 i) =
      negF D i ∘ₗ (vermaEquiv (R := R)).symm.toLinearMap := by
  refine LinearMap.ext fun m => (vermaEquiv (R := R) (D := D)).injective ?_
  change vermaEquiv (vermaEquiv.symm (F R 𝕍 i • m)) = vermaEquiv (negF D i (vermaEquiv.symm m))
  rw [LinearEquiv.apply_symm_apply, vermaEquiv_negF, LinearEquiv.apply_symm_apply]

private def vermaPair (Λ : Dom R) :
    QuantumGroup R 𝕍 ⊗[𝕂] QuantumGroup R 𝕍 →ₐ[𝕂] Module.End 𝕂 (Mv ⊗[𝕂] Factor Λ) :=
  pairRep (Algebra.lsmul 𝕂 𝕂 Mv) (Algebra.lsmul 𝕂 𝕂 (Factor Λ))

private theorem vermaPair_tmul (Λ : Dom R) (a b : QuantumGroup R 𝕍) :
    vermaPair Λ (a ⊗ₜ[𝕂] b) =
      TensorProduct.map (Algebra.lsmul 𝕂 𝕂 Mv a) (Algebra.lsmul 𝕂 𝕂 (Factor Λ) b) :=
  TensorProduct.ext' fun x y => pairRep_tmul _ _ a b x y

private def negCoprodFree (Λ : Dom R) : LusztigF 𝕂 I →ₗ[𝕂] Um D 𝕍 ⊗[𝕂] Factor Λ :=
  TensorProduct.map (vermaEquiv (R := R) (D := D)).symm.toLinearMap LinearMap.id ∘ₗ
    LinearMap.applyₗ (VermaModule.hwv R 𝕍 0 ⊗ₜ[𝕂] IrreducibleModule.hwv R 𝕍 Λ.1) ∘ₗ
    (vermaPair Λ).toLinearMap ∘ₗ (Δ).toLinearMap ∘ₗ (minusHom R 𝕍).toLinearMap

private theorem negCoprodFree_apply (Λ : Dom R) (y : LusztigF 𝕂 I) :
    negCoprodFree (D := D) Λ y =
      TensorProduct.map (vermaEquiv (R := R) (D := D)).symm.toLinearMap LinearMap.id
        (vermaPair Λ (Δ (minusHom R 𝕍 y))
          (VermaModule.hwv R 𝕍 0 ⊗ₜ[𝕂] IrreducibleModule.hwv R 𝕍 Λ.1)) := rfl

variable (D) in
/-- `u ↦ u_{(1)} ⊗ u_{(2)} v_λ`: the coproduct of `u` applied to `1 ⊗ v_λ`, with `U⁻`
identified with the Verma module `M(0)`. -/
def negCoprod (Λ : Dom R) : Um D 𝕍 →ₗ[𝕂] Um D 𝕍 ⊗[𝕂] Factor Λ :=
  (serreSubmodule D 𝕍).liftQ (negCoprodFree Λ) fun y hy => by
    have h0 : minusHom R 𝕍 y = 0 :=
      (TwoSidedIdeal.mem_ker _).1 (serreIdeal_le_ker_minusHom RatFunc.X_ne_zero powNeOne
        (mem_serreSubmodule.mp hy))
    rw [LinearMap.mem_ker, negCoprodFree_apply, h0, map_zero, map_zero, LinearMap.zero_apply,
      map_zero]

theorem negCoprod_mk (Λ : Dom R) (y : LusztigF 𝕂 I) :
    negCoprod D Λ (Submodule.Quotient.mk y) = negCoprodFree Λ y := rfl

theorem negCoprod_one (Λ : Dom R) :
    negCoprod D Λ (Submodule.Quotient.mk 1) =
      (Submodule.Quotient.mk 1 : Um D 𝕍) ⊗ₜ[𝕂] IrreducibleModule.hwv R 𝕍 Λ.1 := by
  rw [negCoprod_mk, negCoprodFree_apply, map_one, map_one, map_one, Module.End.one_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]
  congr 1
  refine (vermaEquiv (R := R) (D := D)).symm_apply_eq.mpr ?_
  rw [vermaEquiv_mk, map_one, one_smul]

/-- `Δ(F_i u)(1 ⊗ v_λ) = F̃_i (Δ(u)(1 ⊗ v_λ))`. -/
theorem negCoprod_negF (Λ : Dom R) (i : I) (u : Um D 𝕍) :
    negCoprod D Λ (negF D i u) =
      TensorProduct.map (negF D i) (Algebra.lsmul 𝕂 𝕂 (Factor Λ) (K R 𝕍 (-ktilde R i)))
          (negCoprod D Λ u) +
        TensorProduct.map LinearMap.id (Algebra.lsmul 𝕂 𝕂 (Factor Λ) (F R 𝕍 i))
          (negCoprod D Λ u) := by
  induction u using Submodule.Quotient.induction_on with
  | H y =>
    rw [negF_mk, negCoprod_mk, negCoprod_mk, negCoprodFree_apply, negCoprodFree_apply,
      map_mul, map_mul, map_mul, Module.End.mul_apply]
    have hF : minusHom R 𝕍 (FreeAlgebra.ι 𝕂 i) = F R 𝕍 i := by simp [minusHom]
    rw [hF, comul_F, map_add, vermaPair_tmul, vermaPair_tmul, LinearMap.add_apply, map_add]
    set z := vermaPair Λ (Δ (minusHom R 𝕍 y))
      (VermaModule.hwv R 𝕍 0 ⊗ₜ[𝕂] IrreducibleModule.hwv R 𝕍 Λ.1)
    have h1 : TensorProduct.map (vermaEquiv (R := R) (D := D)).symm.toLinearMap LinearMap.id ∘ₗ
        TensorProduct.map (Algebra.lsmul 𝕂 𝕂 Mv (F R 𝕍 i))
          (Algebra.lsmul 𝕂 𝕂 (Factor Λ) (K R 𝕍 (-ktilde R i))) =
        TensorProduct.map (negF D i) (Algebra.lsmul 𝕂 𝕂 (Factor Λ) (K R 𝕍 (-ktilde R i))) ∘ₗ
          TensorProduct.map (vermaEquiv (R := R) (D := D)).symm.toLinearMap LinearMap.id := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, vermaEquiv_symm_F]
      rfl
    have h2 : TensorProduct.map (vermaEquiv (R := R) (D := D)).symm.toLinearMap LinearMap.id ∘ₗ
        TensorProduct.map (Algebra.lsmul 𝕂 𝕂 Mv (1 : QuantumGroup R 𝕍))
          (Algebra.lsmul 𝕂 𝕂 (Factor Λ) (F R 𝕍 i)) =
        TensorProduct.map LinearMap.id (Algebra.lsmul 𝕂 𝕂 (Factor Λ) (F R 𝕍 i)) ∘ₗ
          TensorProduct.map (vermaEquiv (R := R) (D := D)).symm.toLinearMap LinearMap.id := by
      rw [map_one, ← TensorProduct.map_comp, ← TensorProduct.map_comp]
      rfl
    exact congrArg₂ (· + ·) (LinearMap.congr_fun h1 z) (LinearMap.congr_fun h2 z)

/-! ### The map on `U⁻ ⊗ V^λ` -/

variable {n : ℕ}

/-- Reassociate `(u ⊗ v) ⊗ w ↦ u ⊗ (v ⊗ w)` with `v` in the new first factor. -/
private def prependAssoc (wt : Fin (n + 1) → Dom R) :
    (Um D 𝕍 ⊗[𝕂] Factor (wt 0)) ⊗[𝕂] TensorSpace (fun j : Fin n => wt j.succ) →ₗ[𝕂]
      NegTensor D wt :=
  TensorProduct.map LinearMap.id (tensorSplitFirst wt).symm.toLinearMap ∘ₗ
    (TensorProduct.assoc 𝕂 _ _ _).toLinearMap

private theorem prependAssoc_tmul (wt : Fin (n + 1) → Dom R) (u : Um D 𝕍) (v : Factor (wt 0))
    (z : TensorSpace (fun j : Fin n => wt j.succ)) :
    prependAssoc wt ((u ⊗ₜ[𝕂] v) ⊗ₜ[𝕂] z) = u ⊗ₜ[𝕂] prependTensor wt v z := rfl

variable (D) in
/-- **`u ⊗ w ↦ u_{(1)} ⊗ (u_{(2)} v_{λ₀} ⊗ w)`** (Webster, arXiv:1309.3796v3,
Proposition 4.39, (4.40)), where `λ₀` is the first label. -/
def negTensorPrepend (wt : Fin (n + 1) → Dom R) :
    NegTensor D (fun j : Fin n => wt j.succ) →ₗ[𝕂] NegTensor D wt :=
  prependAssoc wt ∘ₗ TensorProduct.map (negCoprod D (wt 0)) LinearMap.id

private theorem prependAssoc_negTensorF (wt : Fin (n + 1) → Dom R) (i : I) :
    negTensorF D wt i ∘ₗ prependAssoc wt =
      prependAssoc wt ∘ₗ TensorProduct.map
          (TensorProduct.map (negF D i) (Algebra.lsmul 𝕂 𝕂 (Factor (wt 0)) (K R 𝕍 (-ktilde R i))))
          (ρ _ (K R 𝕍 (-ktilde R i))) +
        prependAssoc wt ∘ₗ TensorProduct.map
          (TensorProduct.map LinearMap.id (Algebra.lsmul 𝕂 𝕂 (Factor (wt 0)) (F R 𝕍 i)))
          (ρ _ (K R 𝕍 (-ktilde R i))) +
        prependAssoc wt ∘ₗ TensorProduct.map LinearMap.id (ρ _ (F R 𝕍 i)) := by
  apply TensorProduct.ext_threefold
  intro u v z
  simp only [LinearMap.comp_apply, LinearMap.add_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, prependAssoc_tmul, negTensorF, Algebra.lsmul_coe]
  rw [tensorRepresentation_K_prepend, tensorRepresentation_F_prepend, TensorProduct.tmul_add,
    add_assoc]

/-- `negTensorPrepend` intertwines the operators `F̃_i`. -/
theorem negTensorPrepend_negTensorF (wt : Fin (n + 1) → Dom R) (i : I) :
    negTensorPrepend D wt ∘ₗ negTensorF D (fun j : Fin n => wt j.succ) i =
      negTensorF D wt i ∘ₗ negTensorPrepend D wt := by
  have hA : negCoprod D (wt 0) ∘ₗ negF D i =
      TensorProduct.map (negF D i) (Algebra.lsmul 𝕂 𝕂 (Factor (wt 0)) (K R 𝕍 (-ktilde R i))) ∘ₗ
          negCoprod D (wt 0) +
        TensorProduct.map LinearMap.id (Algebra.lsmul 𝕂 𝕂 (Factor (wt 0)) (F R 𝕍 i)) ∘ₗ
          negCoprod D (wt 0) :=
    LinearMap.ext fun u => negCoprod_negF (wt 0) i u
  rw [negTensorPrepend, LinearMap.comp_assoc, ← LinearMap.comp_assoc _ (prependAssoc wt),
    prependAssoc_negTensorF, negTensorF, LinearMap.comp_add, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, hA, TensorProduct.map_add_left, LinearMap.comp_add,
    LinearMap.add_comp, LinearMap.add_comp, LinearMap.comp_assoc, LinearMap.comp_assoc,
    LinearMap.comp_assoc, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    ← TensorProduct.map_comp, LinearMap.comp_add]
  rfl

theorem negTensorPrepend_negTensorDivF (wt : Fin (n + 1) → Dom R) (i : I) (a : ℕ)
    (z : NegTensor D (fun j : Fin n => wt j.succ)) :
    negTensorPrepend D wt (negTensorDivF D _ i a z) =
      negTensorDivF D wt i a (negTensorPrepend D wt z) := by
  have hpow : ∀ m : ℕ, negTensorPrepend D wt ∘ₗ
      ((negTensorF D (fun j : Fin n => wt j.succ) i) ^ m : Module.End 𝕂 _) =
      ((negTensorF D wt i) ^ m : Module.End 𝕂 _) ∘ₗ negTensorPrepend D wt := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, negTensorPrepend_negTensorF,
        LinearMap.comp_assoc]
  rw [negTensorDivF, negTensorDivF, qDivPow, qDivPow, LinearMap.smul_apply,
    LinearMap.smul_apply, map_smul]
  congr 1
  exact LinearMap.congr_fun (hpow a) z

private theorem negTensorPrepend_appendHighest (wt : Fin (n + 2) → Dom R) :
    negTensorPrepend D wt ∘ₗ TensorProduct.map LinearMap.id (appendHighest (fun j => wt j.succ)) =
      TensorProduct.map LinearMap.id (appendHighest wt) ∘ₗ
        negTensorPrepend D (fun j : Fin (n + 1) => wt j.castSucc) := by
  have hP : prependAssoc wt ∘ₗ TensorProduct.map LinearMap.id
      (appendHighest (fun j => wt j.succ)) =
      TensorProduct.map LinearMap.id (appendHighest wt) ∘ₗ
        prependAssoc (fun j : Fin (n + 1) => wt j.castSucc) := by
    apply TensorProduct.ext_threefold
    intro u v z
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      prependAssoc_tmul, appendHighest_apply]
    exact congrArg (u ⊗ₜ[𝕂] ·) (prependTensor_appendTensor wt v z _)
  rw [negTensorPrepend, negTensorPrepend, LinearMap.comp_assoc, ← TensorProduct.map_comp,
    LinearMap.id_comp, LinearMap.comp_id]
  rw [show TensorProduct.map (negCoprod D (wt 0)) (appendHighest (fun j => wt j.succ)) =
      TensorProduct.map LinearMap.id (appendHighest (fun j => wt j.succ)) ∘ₗ
        TensorProduct.map (negCoprod D (wt 0)) LinearMap.id by
    rw [← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id],
    ← LinearMap.comp_assoc, hP]
  rfl

/-- **`p̃_{λ₀ w} = u_{(1)} ⊗ (u_{(2)} v_{λ₀} ⊗ w)` applied to `p̃_w`** (Webster,
arXiv:1309.3796v3, Proposition 4.39, (4.40)): adding a red strand on the left of a word
applies `negTensorPrepend`. -/
theorem negWordVector_prependRed : ∀ {n : ℕ} (w : TensorWord I n) (wt : Fin (n + 1) → Dom R),
    negWordVector D w.prependRed wt =
      negTensorPrepend D wt (negWordVector D w (fun j => wt j.succ))
  | _, .empty, wt => by
    change (Submodule.Quotient.mk 1 : Um D 𝕍) ⊗ₜ[𝕂] appendTensor wt
        (PiTensorProduct.tprod 𝕂 (fun j : Fin 0 => IrreducibleModule.hwv R 𝕍 (wt j.castSucc).1))
        (IrreducibleModule.hwv R 𝕍 (wt (Fin.last 0)).1) =
      prependAssoc wt (negCoprod D (wt 0) (Submodule.Quotient.mk 1) ⊗ₜ[𝕂]
        PiTensorProduct.tprod 𝕂 (fun j : Fin 0 => IrreducibleModule.hwv R 𝕍 (wt j.succ).1))
    rw [negCoprod_one, prependAssoc_tmul, appendTensor_tprod]
    congr 1
    have h := prependTensor_tprod wt (fun j => IrreducibleModule.hwv R 𝕍 (wt j).1)
    refine Eq.trans ?_ h.symm
    congr 1
    funext j
    rw [show j = Fin.last 0 from Fin.ext (by have := j.2; simp only [Fin.val_last]; omega),
      Fin.snoc_last]
  | _, .red w, wt => by
    change TensorProduct.map LinearMap.id (appendHighest wt)
        (negWordVector D w.prependRed (fun j => wt j.castSucc)) =
      (negTensorPrepend D wt ∘ₗ TensorProduct.map LinearMap.id
        (appendHighest (fun j => wt j.succ))) (negWordVector D w _)
    rw [negTensorPrepend_appendHighest, LinearMap.comp_apply]
    exact congrArg _ (negWordVector_prependRed w (fun j => wt j.castSucc))
  | _, .black w i a, wt => by
    change negTensorDivF D wt i a (negWordVector D w.prependRed wt) =
      negTensorPrepend D wt (negTensorDivF D _ i a (negWordVector D w _))
    rw [negTensorPrepend_negTensorDivF, negWordVector_prependRed w wt]

end Categorification.Stendhal.FirstWeight
