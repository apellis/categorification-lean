/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorSplitFirst
import Categorification.WeightedKLR.RedStrands.TensorGenerators
import LieLean.Algebra.QuantumGroup.CrystalBasis.GrandLoop.Stable

/-!
# The module `U⁻ ⊗ V^λ` and the map `𝔮_N`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
before Proposition 4.39 and in its proof. The space `U⁻ ⊗ V_{λ₁} ⊗ ⋯ ⊗ V_{λ_ℓ}` carries the
operators `F̃_i (u ⊗ w) = F_i u ⊗ K_{-ĩ} w + u ⊗ F_i w`. The vectors `p̃_w` are defined by the
same recursion as the tensor vectors `p_w`, starting from `1 ⊗ v_λ` instead of `v_λ`.

The map `𝔮_N (u ⊗ w) = u v_{λ₀} ⊗ w` into `V_{λ₀} ⊗ V_{λ₁} ⊗ ⋯ ⊗ V_{λ_ℓ}` intertwines `F̃_i`
with the action of `F_i`, and sends `p̃_w` to the tensor vector of the word with a red strand
of label `λ₀` added on the left (`negTensorMap_negWordVector`).

Webster writes the operator as a right action `(u ⊗ w) · F_i = u F_i ⊗ K_i^{-1} w + ⋯`. With
right multiplication, `𝔮_N` would not intertwine it with the action on `V_{λ₀} ⊗ V^λ`, and
`p̃_∅^{i_1 ⋯ i_n}` would be `F_{i_1} ⋯ F_{i_n}` rather than the `F_{i_n} ⋯ F_{i_1}` stated
there. Both statements hold for left multiplication `F_i u`, which is used here.

## Main definitions

* `negF` : left multiplication by `F_i` on `U⁻`.
* `NegTensor`, `negTensorF` : the space `U⁻ ⊗ V^λ` and the operator `F̃_i`.
* `negWordVector` : the vectors `p̃_w`.
* `TensorWord.prependRed` : a red strand added on the left of a word.
* `negTensorMap` : the map `𝔮_N`.

## Main results

* `negTensorMap_negTensorF`, `negTensorMap_negTensorDivF` : `𝔮_N` intertwines `F̃_i` and its
  divided powers with the action on the tensor product.
* `negTensorMap_negWordVector` : `𝔮_N p̃_w = p_{r(w)}`.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y}

private abbrev Factor (wt : Dom R) := IrreducibleModule R 𝕍 wt.1

local notation "ρ" => tensorRepresentation
local notation "Δ" => comul R 𝕍
local notation "divF" => fun (i : I) (n : ℕ) => qDivPow (𝕍 ^ D.d i) n (F R 𝕍 i)

/-- `ℚ(v)` is transcendental over `ℚ` in its generator. -/
theorem transcendental_ratFuncX : Transcendental ℚ 𝕍 := by
  rw [← RatFunc.algebraMap_X]
  exact (transcendental_algebraMap_iff (RatFunc.algebraMap_injective ℚ)).2
    (Polynomial.transcendental_X ℚ)

local notation "hvt" => transcendental_ratFuncX

/-! ### Left multiplication on `U⁻` -/

variable (D) in
/-- Left multiplication by `F_i` on `U⁻ = 'f ⧸ J`. -/
def negF (i : I) : Um D 𝕍 →ₗ[𝕂] Um D 𝕍 :=
  (serreSubmodule D 𝕍).mapQ (serreSubmodule D 𝕍) (LinearMap.mulLeft 𝕂 (FreeAlgebra.ι 𝕂 i))
    (fun _ hy => mem_serreSubmodule.mpr ((LusztigF.serreIdeal D 𝕍).mul_mem_left _ _
      (mem_serreSubmodule.mp hy)))

omit [DecidableEq I] in
theorem negF_mk (i : I) (y : LusztigF 𝕂 I) :
    negF D i (Submodule.Quotient.mk y) = Submodule.Quotient.mk (FreeAlgebra.ι 𝕂 i * y) := rfl

/-- `ev_λ (F_i u) = F_i ev_λ(u)`. -/
theorem evq_negF (Λ : Dom R) (i : I) (u : Um D 𝕍) :
    evq hvt Λ (negF D i u) = F R 𝕍 i • evq hvt Λ u := by
  induction u using Submodule.Quotient.induction_on with
  | H y => exact ev_ι_mul Λ.1 i y

/-! ### The space `U⁻ ⊗ V^λ` -/

variable (D) in
/-- The space `U⁻ ⊗ V_{λ₁} ⊗ ⋯ ⊗ V_{λ_ℓ}`. -/
abbrev NegTensor {ℓ : ℕ} (wt : Fin ℓ → Dom R) := Um D 𝕍 ⊗[𝕂] TensorSpace wt

variable (D) in
/-- The operator `F̃_i (u ⊗ w) = F_i u ⊗ K_{-ĩ} w + u ⊗ F_i w`. -/
def negTensorF {ℓ : ℕ} (wt : Fin ℓ → Dom R) (i : I) : Module.End 𝕂 (NegTensor D wt) :=
  TensorProduct.map (negF D i) (ρ wt (K R 𝕍 (-ktilde R i))) +
    TensorProduct.map LinearMap.id (ρ wt (F R 𝕍 i))

variable (D) in
/-- The divided powers `F̃_i^{(a)}`. -/
def negTensorDivF {ℓ : ℕ} (wt : Fin ℓ → Dom R) (i : I) (a : ℕ) : Module.End 𝕂 (NegTensor D wt) :=
  qDivPow (𝕍 ^ D.d i) a (negTensorF D wt i)

/-- Append a highest weight vector in a new last factor. -/
def appendHighest {n : ℕ} (wt : Fin (n + 1) → Dom R) :
    TensorSpace (fun j : Fin n => wt j.castSucc) →ₗ[𝕂] TensorSpace wt :=
  (tensorSplitLast wt).symm.toLinearMap ∘ₗ
    (TensorProduct.mk 𝕂 _ _).flip (IrreducibleModule.hwv R 𝕍 (wt (Fin.last n)).1)

theorem appendHighest_apply {n : ℕ} (wt : Fin (n + 1) → Dom R)
    (x : TensorSpace (fun j : Fin n => wt j.castSucc)) :
    appendHighest wt x = appendTensor wt x (IrreducibleModule.hwv R 𝕍 (wt (Fin.last n)).1) := rfl

variable (D) in
/-- The vectors `p̃_w` (Webster, arXiv:1309.3796v3, before Proposition 4.39): the recursion of
the tensor vectors `p_w`, started from `1 ⊗ v_λ`. -/
def negWordVector : {n : ℕ} → TensorWord I n → (wt : Fin n → Dom R) → NegTensor D wt
  | _, .empty, wt => (Submodule.Quotient.mk 1 : Um D 𝕍) ⊗ₜ[𝕂]
      PiTensorProduct.tprod 𝕂 (fun j => IrreducibleModule.hwv R 𝕍 (wt j).1)
  | _, .red w, wt => TensorProduct.map LinearMap.id (appendHighest wt)
      (negWordVector w (fun j => wt (Fin.castSucc j)))
  | _, .black w i a, wt => negTensorDivF D wt i a (negWordVector w wt)

/-- Add a red strand on the left of a word. -/
def TensorWord.prependRed : {n : ℕ} → TensorWord I n → TensorWord I (n + 1)
  | _, .empty => .red .empty
  | _, .red w => .red w.prependRed
  | _, .black w i a => .black w.prependRed i a

/-! ### The map `𝔮_N` -/

variable (D) in
/-- **The map `𝔮_N`** (Webster, arXiv:1309.3796v3, proof of Proposition 4.39):
`u ⊗ w ↦ u v_{λ₀} ⊗ w`, where `λ₀` is the first label. -/
def negTensorMap {n : ℕ} (wt : Fin (n + 1) → Dom R) :
    NegTensor D (fun j : Fin n => wt j.succ) →ₗ[𝕂] TensorSpace wt :=
  (tensorSplitFirst wt).symm.toLinearMap ∘ₗ TensorProduct.map (evq hvt (wt 0)) LinearMap.id

theorem negTensorMap_tmul {n : ℕ} (wt : Fin (n + 1) → Dom R) (u : Um D 𝕍)
    (x : TensorSpace (fun j : Fin n => wt j.succ)) :
    negTensorMap D wt (u ⊗ₜ[𝕂] x) = prependTensor wt (evq hvt (wt 0) u) x := rfl

/-- The action of `F_i` on a vector with a prepended factor. -/
theorem tensorRepresentation_F_prepend {n : ℕ} (wt : Fin (n + 1) → Dom R) (i : I)
    (v : Factor (wt 0)) (z : TensorSpace (fun j : Fin n => wt j.succ)) :
    ρ wt (F R 𝕍 i) (prependTensor wt v z) =
      prependTensor wt (F R 𝕍 i • v) (ρ _ (K R 𝕍 (-ktilde R i)) z) +
        prependTensor wt v (ρ _ (F R 𝕍 i) z) := by
  apply (tensorSplitFirst wt).injective
  have h := intertwines_tensorSplitFirst wt (F R 𝕍 i) (prependTensor wt v z)
  simp only [LinearEquiv.coe_coe, AlgHom.comp_apply] at h
  rw [h, prependTensor, LinearEquiv.apply_symm_apply, comul_F, map_add, LinearMap.add_apply,
    pairRep_tmul, pairRep_tmul, map_add, prependTensor, prependTensor,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_one, Module.End.one_apply]
  rfl

/-- The action of `K_μ` on a vector with a prepended factor. -/
theorem tensorRepresentation_K_prepend {n : ℕ} (wt : Fin (n + 1) → Dom R) (μ : Y)
    (v : Factor (wt 0)) (z : TensorSpace (fun j : Fin n => wt j.succ)) :
    ρ wt (K R 𝕍 μ) (prependTensor wt v z) =
      prependTensor wt (K R 𝕍 μ • v) (ρ _ (K R 𝕍 μ) z) := by
  apply (tensorSplitFirst wt).injective
  have h := intertwines_tensorSplitFirst wt (K R 𝕍 μ) (prependTensor wt v z)
  simp only [LinearEquiv.coe_coe, AlgHom.comp_apply] at h
  rw [h, prependTensor, LinearEquiv.apply_symm_apply, comul_K, pairRep_tmul, prependTensor,
    LinearEquiv.apply_symm_apply]
  rfl

/-- `𝔮_N` intertwines `F̃_i` with `F_i`. -/
theorem negTensorMap_negTensorF {n : ℕ} (wt : Fin (n + 1) → Dom R) (i : I) :
    negTensorMap D wt ∘ₗ negTensorF D (fun j : Fin n => wt j.succ) i =
      ρ wt (F R 𝕍 i) ∘ₗ negTensorMap D wt := by
  apply TensorProduct.ext'
  intro u x
  simp only [LinearMap.comp_apply, negTensorF, LinearMap.add_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, map_add, negTensorMap_tmul]
  rw [tensorRepresentation_F_prepend, evq_negF]

theorem negTensorMap_pow_negTensorF {n : ℕ} (wt : Fin (n + 1) → Dom R) (i : I) (m : ℕ) :
    negTensorMap D wt ∘ₗ ((negTensorF D (fun j : Fin n => wt j.succ) i) ^ m :
        Module.End 𝕂 _) =
      ((ρ wt (F R 𝕍 i)) ^ m : Module.End 𝕂 _) ∘ₗ negTensorMap D wt := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, negTensorMap_negTensorF,
      LinearMap.comp_assoc]

/-- `𝔮_N` intertwines the divided powers `F̃_i^{(a)}` with `F_i^{(a)}`. -/
theorem negTensorMap_negTensorDivF {n : ℕ} (wt : Fin (n + 1) → Dom R) (i : I) (a : ℕ)
    (z : NegTensor D (fun j : Fin n => wt j.succ)) :
    negTensorMap D wt (negTensorDivF D _ i a z) = ρ wt (divF i a) (negTensorMap D wt z) := by
  change _ = ρ wt (qDivPow (𝕍 ^ D.d i) a (F R 𝕍 i)) (negTensorMap D wt z)
  rw [negTensorDivF, qDivPow, qDivPow, map_smul, map_pow, LinearMap.smul_apply,
    LinearMap.smul_apply, map_smul]
  congr 1
  exact LinearMap.congr_fun (negTensorMap_pow_negTensorF wt i a) z

private theorem negTensorMap_appendHighest {n : ℕ} (wt : Fin (n + 2) → Dom R) :
    negTensorMap D wt ∘ₗ TensorProduct.map LinearMap.id (appendHighest (fun j => wt j.succ)) =
      appendHighest wt ∘ₗ negTensorMap D (fun j : Fin (n + 1) => wt j.castSucc) := by
  apply TensorProduct.ext'
  intro u x
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    negTensorMap_tmul, appendHighest_apply]
  exact prependTensor_appendTensor wt _ x _

/-- **`𝔮_N p̃_w = p_{r(w)}`** (Webster, arXiv:1309.3796v3, proof of Proposition 4.39): `𝔮_N`
sends `p̃_w` to the tensor vector of the word with a red strand added on the left. -/
theorem negTensorMap_negWordVector : ∀ {n : ℕ} (w : TensorWord I n) (wt : Fin (n + 1) → Dom R),
    negTensorMap D wt (negWordVector D w (fun j => wt j.succ)) =
      tensorWordVector w.prependRed wt
  | _, .empty, wt => by
    change prependTensor wt (evq hvt (wt 0) (Submodule.Quotient.mk 1))
        (PiTensorProduct.tprod 𝕂 (fun j : Fin 0 => IrreducibleModule.hwv R 𝕍 (wt j.succ).1)) =
      appendTensor wt
        (PiTensorProduct.tprod 𝕂 (fun j : Fin 0 => IrreducibleModule.hwv R 𝕍 (wt j.castSucc).1))
        (IrreducibleModule.hwv R 𝕍 (wt (Fin.last 0)).1)
    rw [evq_mk, ev_one, appendTensor_tprod]
    have h := prependTensor_tprod wt (fun j => IrreducibleModule.hwv R 𝕍 (wt j).1)
    refine Eq.trans ?_ (h.trans ?_)
    · congr 1
    · congr 1
      funext j
      rw [show j = Fin.last 0 from Fin.ext (by have := j.2; simp only [Fin.val_last]; omega),
        Fin.snoc_last]
  | _, .red w, wt => by
    change (negTensorMap D wt ∘ₗ TensorProduct.map LinearMap.id
        (appendHighest (fun j => wt j.succ))) (negWordVector D w _) = _
    rw [negTensorMap_appendHighest, LinearMap.comp_apply]
    exact congrArg (appendHighest wt) (negTensorMap_negWordVector w (fun j => wt j.castSucc))
  | _, .black w i a, wt => by
    change negTensorMap D wt (negTensorDivF D _ i a (negWordVector D w _)) = _
    rw [negTensorMap_negTensorDivF]
    exact congrArg _ (negTensorMap_negWordVector w wt)

end Categorification.Stendhal.FirstWeight
