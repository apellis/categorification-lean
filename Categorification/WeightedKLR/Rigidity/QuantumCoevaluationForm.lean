/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.QuantumCoevaluation
import Categorification.WeightedKLR.RedStrands.TensorFormOrdered
import Categorification.WeightedKLR.Rigidity.QuantumCupCapTensor

/-!
# `coev_μ` against Webster's tensor form

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 7.20, convention point: the trace `qtr_μ` is, up to the scalar `a` of
`Θ(v_l^{μ*}) = a v_h^μ`, the transpose of `coev_μ` for the form of Proposition 4.33. The form
is the repaired two-factor form `TensorPairing.correctedForm` (quasi-R intertwiner on the second
argument; erratum to the formula before Proposition 4.33 in v2), and its ordered version
`TensorPairing.orderedForm`.

* `highestHead_quasiRAct`: contracting the first factor against `v_h` is unchanged by `Θ`
  (the terms of `Θ` of positive degree lower the first factor).
* `highestHead_coevaluationElement`: the `v_h`-component of `coev_μ(1)` is `v_h ⊗ v_l^{μ*}`.
* `quasiRAct_tensorBar_coevaluationElement`: `coev_μ(1)` is fixed by `Ψ = Θ ∘ (ψ ⊗ ψ)`.
* `correctedForm_coevaluationElement`: `⟨t, coev_μ(1)⟩ = \overline{a⁻¹ qtr_μ(t)}`; through
  `TensorPairing.orderedForm_binary` this is the two-factor case of `orderedForm`.
* `TensorCoevaluationTranspose`: the statement for `id ⊗ coev_μ ⊗ id` and `id ⊗ qtr_μ ⊗ id`
  needed by the class-functional form of Proposition 7.20 (not proved here beyond two factors).

The argument (invariance of `Θ (ψ ⊗ ψ) coev_μ(1)`, the invariant line, and evaluation of the
`v_h`-component) is ours; Webster does not spell out this identity.
-/

noncomputable section

namespace Categorification.Stendhal.QuantumDual

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped TensorProduct

local notation "vQ" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance : NeZero vQ := ⟨RatFunc.X_ne_zero⟩

section Head

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular) (Λ₁ Λ₂ : Dom R)

local notation "V" => fun w : Dom R => IrreducibleModule R vQ (Subtype.val w)
local notation "h" => fun w : Dom R => IrreducibleModule.hwv R vQ (Subtype.val w)
local notation "𝓑" => fun w : Dom R => IrreducibleModule.form (Subtype.val w) hR hvn_ratFunc
local notation "act₂" => TensorModule.actPair R vQ (V Λ₁) (V Λ₂)

/-- The contraction `x ⊗ y ↦ (v_h, x) y` of the first factor against its highest weight
vector. -/
def highestHead : V Λ₁ ⊗[𝕂] V Λ₂ →ₗ[𝕂] V Λ₂ :=
  TensorProduct.lid 𝕂 (V Λ₂) ∘ₗ TensorProduct.map ((𝓑 Λ₁) (h Λ₁)) LinearMap.id

omit [Finite I] in
theorem highestHead_tmul (x : V Λ₁) (y : V Λ₂) :
    highestHead hR Λ₁ Λ₂ (x ⊗ₜ[𝕂] y) = (𝓑 Λ₁) (h Λ₁) x • y := by
  simp [highestHead]

omit [Finite I] in
theorem form_hwv_minusHom_monomial {w : List I} (hw : w ≠ []) (x : V Λ₁) :
    (𝓑 Λ₁) (h Λ₁) (minusHom R vQ (monomial 𝕂 w) • x) = 0 := by
  obtain ⟨i, w', rfl⟩ : ∃ i w', w = i :: w' := List.exists_cons_of_ne_nil hw
  rw [monomial_cons, map_mul, minusHom_θ, mul_smul, IrreducibleModule.form_hwv_F_smul]

theorem form_hwv_quotientMinus {ν : I →₀ ℕ} (hν : ν ≠ 0) {a : Quotient D vQ}
    (ha : a ∈ quotientWeightSpace D ν) (x : V Λ₁) :
    (𝓑 Λ₁) (h Λ₁) (quotientMinus R a • x) = 0 := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp ha
  rw [AlgHom.toLinearMap_apply, quotientMinus_toQuotient]
  clear ha
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨w, hw, rfl⟩ := hf
    refine form_hwv_minusHom_monomial hR Λ₁ (fun h0 => hν ?_) x
    rw [← hw, h0, wordWeight_nil]
  | zero => rw [map_zero, zero_smul, map_zero]
  | add f g _ _ hf hg => rw [map_add, add_smul, map_add, hf, hg, add_zero]
  | smul c f _ hf => rw [map_smul (minusHom R vQ) c f, smul_assoc, LinearMap.map_smul, hf,
      smul_zero]

theorem highestHead_actPair_quasiR {ν : I →₀ ℕ} (hν : ν ≠ 0) (z : V Λ₁ ⊗[𝕂] V Λ₂) :
    highestHead hR Λ₁ Λ₂ (act₂ (quasiR R ν) z) = 0 := by
  obtain ⟨s, hs⟩ := quasiR_mem_range R ν
  rw [← hs]
  clear hs
  induction s using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply, map_add, ha, hb, add_zero]
  | tmul a c =>
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', add_zero]
    | tmul x y =>
      simp only [TensorProduct.map_tmul, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_subtype, AlgHom.toLinearMap_apply, TensorModule.act_tmul,
        highestHead_tmul]
      rw [form_hwv_quotientMinus hR Λ₁ hν a.2, zero_smul]

theorem highestHead_quasiRAct (z : V Λ₁ ⊗[𝕂] V Λ₂) :
    highestHead hR Λ₁ Λ₂ (quasiRAct (M₁ := V Λ₁) (isPlusLocallyNilpotent_hw Λ₂) z) =
      highestHead hR Λ₁ Λ₂ z := by
  rw [quasiRAct_apply, map_finsum _ (support_quasiR_finite (isPlusLocallyNilpotent_hw Λ₂) z),
    finsum_eq_single _ 0 fun ν hν => highestHead_actPair_quasiR hR Λ₁ Λ₂ hν z, quasiR_zero,
    map_one, Module.End.one_apply]

omit [Finite I] in
theorem form_hwv_ev (y : LusztigF 𝕂 I) :
    (𝓑 Λ₁) (h Λ₁) (ev R vQ Λ₁.1 y) = LusztigF.counit y := by
  beta_reduce
  rw [← ev_one, ev_apply, ev_apply, IrreducibleModule.form_mk]
  exact VermaModule.shapF_one_left R hvn_ratFunc Λ₁.1 y

omit [Finite I] [DecidableEq I] in
theorem counit_bar (y : LusztigF 𝕂 I) :
    LusztigF.counit (LusztigF.bar y) = RatFunc.bar (LusztigF.counit y) := by
  induction y using FreeAlgebra.induction with
  | grade0 c => rw [LusztigF.bar_algebraMap, counit_algebraMap, counit_algebraMap]
  | grade1 i =>
    change LusztigF.counit (LusztigF.bar (θ 𝕂 i)) = _
    rw [LusztigF.bar_θ, counit_θ, map_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]

theorem form_hwv_hwBar (x : V Λ₁) :
    (𝓑 Λ₁) (h Λ₁) (hwBar hR Λ₁ x) = RatFunc.bar ((𝓑 Λ₁) (h Λ₁) x) := by
  obtain ⟨y, rfl⟩ := ev_surjective Λ₁ x
  rw [hwBar_ev, form_hwv_ev, form_hwv_ev, counit_bar]

/-- The factorwise bar involution `ψ ⊗ ψ` of `V_{Λ₁} ⊗ V_{Λ₂}`. -/
def tensorBar : V Λ₁ ⊗[𝕂] V Λ₂ →+ V Λ₁ ⊗[𝕂] V Λ₂ :=
  barPair (hwBar hR Λ₁).toAddMonoidHom (hwBar hR Λ₂).toAddMonoidHom (hwBar_smul_U' hR Λ₁)
    (hwBar_smul_U' hR Λ₂)

local notation "b" => tensorBar hR Λ₁ Λ₂
local notation "Θ" => quasiRAct (M₁ := V Λ₁) (isPlusLocallyNilpotent_hw Λ₂)
local notation "act" => TensorModule.act R vQ (V Λ₁) (V Λ₂)

theorem tensorBar_tmul (x : V Λ₁) (y : V Λ₂) :
    b (x ⊗ₜ[𝕂] y) = hwBar hR Λ₁ x ⊗ₜ[𝕂] hwBar hR Λ₂ y := rfl

theorem tensorBar_tensorBar (z : V Λ₁ ⊗[𝕂] V Λ₂) : b (b z) = z :=
  barPair_barPair _ _ _ _ (hwBar_hwBar hR Λ₁) (hwBar_hwBar hR Λ₂) z

theorem tensorBar_smul (c : 𝕂) (z : V Λ₁ ⊗[𝕂] V Λ₂) : b (c • z) = RatFunc.bar c • b z := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
  | tmul x y =>
    rw [TensorProduct.smul_tmul', tensorBar_tmul, tensorBar_tmul, hwBar_smul,
      TensorProduct.smul_tmul']

theorem websterTheta_eq (z : V Λ₁ ⊗[𝕂] V Λ₂) :
    TensorPairing.websterTheta hR Λ₁ Λ₂ z = b (Θ (b z)) := rfl

theorem highestHead_tensorBar (z : V Λ₁ ⊗[𝕂] V Λ₂) :
    highestHead hR Λ₁ Λ₂ (b z) = hwBar hR Λ₂ (highestHead hR Λ₁ Λ₂ z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]
  | tmul x y =>
    rw [tensorBar_tmul, highestHead_tmul, highestHead_tmul, form_hwv_hwBar, hwBar_smul]

omit [Finite I] in
theorem highestHead_act_K (ζ : Y) (z : V Λ₁ ⊗[𝕂] V Λ₂) :
    highestHead hR Λ₁ Λ₂ (act (K R vQ ζ) z) =
      vQ ^ Λ₁.1 ζ • K R vQ ζ • highestHead hR Λ₁ Λ₂ z := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, smul_add, smul_add]
  | tmul x y =>
    rw [TensorModule.act, AlgHom.comp_apply, comul_K, TensorModule.act_tmul, highestHead_tmul,
      highestHead_tmul]
    beta_reduce
    rw [IrreducibleModule.form_comm, IrreducibleModule.isContravariant_form, rho_K,
      IrreducibleModule.hwv_mem_weightSpace ζ, map_smul, IrreducibleModule.form_comm,
      smul_comm (K R vQ ζ), smul_smul, smul_eq_mul]

omit [Finite I] in
theorem lift_form_hwv (y : V Λ₂) (z : V Λ₁ ⊗[𝕂] V Λ₂) :
    TensorProduct.lift ((LinearMap.mul 𝕂 𝕂).compl₁₂ ((𝓑 Λ₁) (h Λ₁)) ((𝓑 Λ₂) y)) z =
      (𝓑 Λ₂) y (highestHead hR Λ₁ Λ₂ z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => rw [map_add, hz, hz', map_add, map_add]
  | tmul x y' =>
    rw [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      highestHead_tmul, map_smul, smul_eq_mul]

theorem factorwise_tmul_left (x₁ : V Λ₁) (x₂ : V Λ₂) (z : V Λ₁ ⊗[𝕂] V Λ₂) :
    TensorPairing.factorwise hR Λ₁ Λ₂ (x₁ ⊗ₜ[𝕂] x₂) z =
      RatFunc.bar (TensorProduct.lift ((LinearMap.mul 𝕂 𝕂).compl₁₂ ((𝓑 Λ₁) x₁) ((𝓑 Λ₂) x₂))
        (b z)) := by
  change RatFunc.bar (((𝓑 Λ₁).tmul (𝓑 Λ₂)) (x₁ ⊗ₜ[𝕂] x₂) (b z)) = _
  congr 1
  generalize b z = z'
  induction z' using TensorProduct.inductionOn with
  | add z z' hz hz' => rw [map_add, hz, hz', map_add]
  | tmul y₁ y₂ =>
    simp [LinearMap.BilinForm.tmul, LinearMap.BilinForm.tensorDistrib_tmul, mul_comm]

omit [Finite I] in
theorem counit_barHom (u : QuantumGroup R vQ) :
    counit R vQ (barHom R u) = RatFunc.bar (counit R vQ u) := by
  induction u using QuantumGroup.induction_on with
  | algebraMap c => simp [barHom_algebraMap]
  | E i => simp
  | F i => simp
  | K μ => simp
  | mul x y hx hy => simp [hx, hy]
  | add x y hx hy => simp [hx, hy]

/-- If `z` is `U`-invariant, so is `Θ (ψ ⊗ ψ) z`. -/
theorem quasiRAct_tensorBar_invariant {z : V Λ₁ ⊗[𝕂] V Λ₂}
    (hz : ∀ u, act u z = counit R vQ u • z) (u : QuantumGroup R vQ) :
    act u (Θ (b z)) = counit R vQ u • Θ (b z) := by
  set W := TensorPairing.websterTheta hR Λ₁ Λ₂ z
  have hW : ∀ u', act₂ (barComul R u') W = counit R vQ u' • W := by
    intro u'
    rw [← TensorPairing.websterTheta_act, hz, websterTheta_eq, tensorBar_smul, map_smul,
      tensorBar_smul, RatFunc.bar_bar]
    rfl
  have e : Θ (b z) = b W := (tensorBar_tensorBar hR Λ₁ Λ₂ _).symm
  rw [e]
  calc act u (b W) = act₂ (barTensor R (barComul R (barHom R u))) (b W) := by
        rw [barTensor_barComul, barHom_barHom]; rfl
    _ = b (act₂ (barComul R (barHom R u)) W) := (barPair_actPair _ _ _ _ _ _).symm
    _ = counit R vQ u • b W := by rw [hW, tensorBar_smul, counit_barHom, RatFunc.bar_bar]

end Head

section Coevaluation

open Module

variable {I K H Y : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
    {Δ : LusztigCartanDatum I} {R : Δ.RootDatum Y}
    [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] (P : Matrix.Realization Δ.cartanMatrix K H)
variable [FiniteDimensional K H] (hR : R.IsXRegular) (μ : Dom R) (weight : P.integralWeights)
  (hdom : P.IsDominantIntegral (weight : Dual K H))
  (hm : ∀ j, (weight : Dual K H) (P.coroot j) = (μ.1 (R.coroot j) : K))
  (w : List I)
variable (hw : (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
  (hlong : ∀ i, (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsLeftDescent
    ((P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)
variable [Finite (P.weylGroup Δ.isGeneralizedCartan_cartanMatrix)]

local notation "μs" => dualWeight P μ weight hdom hm w hw hlong
local notation "Vμ" => IrreducibleModule R vQ (Subtype.val μ)
local notation "Vμs" =>
  IrreducibleModule R vQ (Subtype.val (dualWeight P μ weight hdom hm w hw hlong))
local notation "Θt" => twistLowestLinear P hR μ weight hdom hm w hw hlong
local notation "B" => IrreducibleModule.form (Subtype.val μ) hR hvn_ratFunc
local notation "Bs" =>
  IrreducibleModule.form (Subtype.val (dualWeight P μ weight hdom hm w hw hlong)) hR hvn_ratFunc
local notation "vls" => lowestVector P (dualWeight P μ weight hdom hm w hw hlong)
  (dualIntegralWeight P weight w) w
local notation "aμ" => dualLowestScalar P hR μ weight hdom hm w hw hlong
local notation "C" =>
  LinearEquiv.symm (TensorModule.mk Vμ Vμs) (coevaluationElement P hR μ weight hdom hm w hw hlong)
local notation "Θq" => quasiRAct (M₁ := Vμ) (isPlusLocallyNilpotent_hw μs)
local notation "bb" => tensorBar hR μ μs

theorem coevaluationElement_act (u : QuantumGroup R vQ) :
    TensorModule.act R vQ Vμ Vμs u C = counit R vQ u • C := by
  have h := coevaluationElement_smul P hR μ weight hdom hm w hw hlong u
  obtain ⟨z, hz⟩ := (TensorModule.mk Vμ Vμs).surjective
    (coevaluationElement P hR μ weight hdom hm w hw hlong)
  rw [← hz, TensorModule.smul_mk, ← map_smul] at h
  rw [← hz, LinearEquiv.symm_apply_apply]
  exact (TensorModule.mk Vμ Vμs).injective h

/-- **The `v_h`-component of `coev_μ(1)`**: contracting the first factor of `coev_μ(1)` against
`v_h^μ` gives the lowest weight vector `v_l` of `V_{μ*}`. -/
theorem highestHead_coevaluationElement : highestHead hR μ μs C = vls := by
  have ha := dualLowestScalar_ne_zero P hR μ weight hdom hm w hw hlong
  set t := highestHead hR μ μs C with ht_def
  have hK : t ∈ QuantumGroup.weightSpace R vQ Vμs (-μ.1) := by
    intro ζ
    have h1 := highestHead_act_K hR μ μs ζ C
    rw [coevaluationElement_act, counit_K, one_smul] at h1
    rw [AddMonoidHom.neg_apply, zpow_neg]
    calc QuantumGroup.K R vQ ζ • t =
          (vQ ^ μ.1 ζ)⁻¹ • (vQ ^ μ.1 ζ • QuantumGroup.K R vQ ζ • t) := by
          rw [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ RatFunc.X_ne_zero), one_smul]
      _ = _ := by rw [← h1]
  have hx := twistLowestLinear_mem_weightSpace P hR μ weight hdom hm w hw hlong hK
  rw [neg_neg] at hx
  obtain ⟨c', hc'⟩ := exists_eq_smul_hwv_of_mem_weightSpace
    (hvt := LusztigF.transcendental_ratFunc_X) (hR := hR) μ hx
  have ht : t = (c' / aμ) • vls := by
    apply twistLowestLinear_injective P hR μ weight hdom hm w hw hlong
    rw [hc', map_smul, twistLowestLinear_dualLowestVector, smul_smul, div_mul_cancel₀ _ ha]
  have hc : c' / aμ = 1 := by
    have h2 := tensorForm_coevaluationElement P hR μ weight hdom hm w hw hlong
      (IrreducibleModule.hwv R vQ μ.1) vls
    rw [lift_form_hwv, ← ht_def, ht, map_smul, smul_eq_mul,
      form_lowestVector P hR μs (dualIntegralWeight P weight w)
        (isDominantIntegral_dualIntegralWeight P weight hdom w hlong)
        (dualIntegralWeight_coroot P μ weight hdom hm w hw hlong) w hw, mul_one,
      quantumTrace_tmul, quantumTracePairing_apply, twistLowestLinear_dualLowestVector, map_smul,
      IrreducibleModule.form_hwv, smul_eq_mul, mul_one, inv_mul_cancel₀ ha] at h2
    exact h2
  rw [ht, hc, one_smul]

/-- **`coev_μ(1)` is fixed by Lusztig's involution `Ψ = Θ ∘ (ψ ⊗ ψ)`** of `V_μ ⊗ V_{μ*}`
([Lus] 24.3.2). -/
theorem quasiRAct_tensorBar_coevaluationElement : Θq (bb C) = C := by
  have hinv := quasiRAct_tensorBar_invariant hR μ μs
    (coevaluationElement_act P hR μ weight hdom hm w hw hlong)
  obtain ⟨s, hs⟩ : ∃ s : 𝕂, Θq (bb C) = s • C := by
    obtain ⟨s, h⟩ : ∃ s : 𝕂, TensorModule.mk Vμ Vμs (Θq (bb C)) =
        s • coevaluationElement P hR μ weight hdom hm w hw hlong :=
      ⟨_, eq_smul_coevaluationElement_of_invariant P hR μ weight hdom hm w hw hlong
        (TensorModule.mk Vμ Vμs (Θq (bb C))) fun u => by
          rw [TensorModule.smul_mk, hinv, map_smul]⟩
    refine ⟨s, (TensorModule.mk Vμ Vμs).injective ?_⟩
    rw [h, map_smul, LinearEquiv.apply_symm_apply]
  have hvls : hwBar hR μs vls = vls :=
    Stendhal.bar_dividedLoweringWord μs hR _
  have hvv := form_lowestVector P hR μs (dualIntegralWeight P weight w)
    (isDominantIntegral_dualIntegralWeight P weight hdom w hlong)
    (dualIntegralWeight_coroot P μ weight hdom hm w hw hlong) w hw
  have h1 : Bs vls (highestHead hR μ μs (Θq (bb C))) = 1 := by
    rw [highestHead_quasiRAct, highestHead_tensorBar,
      highestHead_coevaluationElement P hR μ weight hdom hm w hw hlong, hvls, hvv]
  have h2 : Bs vls (highestHead hR μ μs (Θq (bb C))) = s := by
    rw [hs, map_smul, highestHead_coevaluationElement P hR μ weight hdom hm w hw hlong, map_smul,
      hvv, smul_eq_mul, mul_one]
  rw [hs, ← h2, h1, one_smul]

/-- **The transpose identity for Webster's tensor form** (convention point (a) of Webster,
Proposition 7.20): for the repaired two-factor form `⟨-,-⟩` of Proposition 4.33 on
`V_μ ⊗ V_{μ*}`, `⟨t, coev_μ(1)⟩ = \overline{a⁻¹ qtr_μ(t)}`, where `Θ(v_l^{μ*}) = a v_h^μ`. -/
theorem correctedForm_coevaluationElement (z : Vμ ⊗[𝕂] Vμs) :
    TensorPairing.correctedForm hR μ μs z C =
      RatFunc.bar ((aμ)⁻¹ * quantumTrace P hR μ weight hdom hm w hw hlong
        (TensorModule.mk Vμ Vμs z)) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' =>
    rw [map_add, map_add, mul_add, map_add, ← hz, ← hz']
    simp only [TensorPairing.correctedForm, TensorPairing.factorwise, map_add,
      LinearMap.add_apply]
  | tmul x y =>
    rw [TensorPairing.correctedForm, factorwise_tmul_left, websterTheta_eq, tensorBar_tensorBar,
      quasiRAct_tensorBar_coevaluationElement P hR μ weight hdom hm w hw hlong]
    exact congrArg RatFunc.bar (tensorForm_coevaluationElement P hR μ weight hdom hm w hw hlong x y)

variable (w₀ : Fin 0 → Dom R)
variable {k m : ℕ} (wt : Fin (k + 2 + m) → Dom R) (wt' : Fin (k + m) → Dom R)
  (h₁ : ∀ i : Fin k, wt' (Fin.castAdd m i) = wt (Fin.castAdd m (Fin.castAdd 2 i)))
  (h₂ : wt (Fin.castAdd m (Fin.natAdd k 0)) = μ)
  (h₃ : wt (Fin.castAdd m (Fin.natAdd k 1)) = dualWeight P μ weight hdom hm w hw hlong)
  (h₄ : ∀ i : Fin m, wt' (Fin.natAdd k i) = wt (Fin.natAdd (k + 2) i))

/-- **The transpose identity for `id ⊗ coev_μ ⊗ id`**, in the form used by the class-functional
version of Webster, Proposition 7.20 (the trace half `T` as the adjoint of the coevaluation
half `K`): for the ordered forms of `V^{wt'}` and `V^{wt}` (Proposition 4.33 with the quasi-R
intertwiner on the second argument),
`⟨y, (id ⊗ coev_μ ⊗ id) x⟩_{wt} = ⟨a⁻¹ (id ⊗ qtr_μ ⊗ id) y, x⟩_{wt'}`, `Θ(v_l^{μ*}) = a v_h^μ`.
Since the forms are bar-semilinear in the first argument, the scalar on the right is `ā⁻¹`.
The two-factor case is `correctedForm_coevaluationElement` (with `orderedForm_binary`); the
general case is not proved here. -/
def TensorCoevaluationTranspose : Prop :=
  ∀ (x : FirstWeight.TensorSpace wt') (y : FirstWeight.TensorSpace wt),
    TensorPairing.orderedForm hR wt y
        (tensorCoevaluation P hR μ weight hdom hm w hw hlong w₀ wt wt' h₁ h₂ h₃ h₄ x) =
      TensorPairing.orderedForm hR wt'
        ((aμ)⁻¹ • tensorQuantumTrace P hR μ weight hdom hm w hw hlong w₀ wt wt' h₁ h₂ h₃ h₄ y) x

end Coevaluation

end Categorification.Stendhal.QuantumDual
