/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleBlackShapovalov
import LieLean.Algebra.QuantumGroup.Sl2.SimpleModule

/-!
# The printed quasi-R tensor form

Webster, arXiv:1309.3796v2, §4.7, Proposition 4.33, p. 44.
The form immediately before the proposition acts on the first argument by
the normalized intertwiner carrying the coproduct to the bar-coproduct.
LieLean's `quasiRAct` intertwines in the reverse direction, so conjugation
by the factorwise bar gives the operator used below.
-/

noncomputable section

namespace Categorification.Stendhal.TensorPairing

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop TensorProduct LusztigF
open scoped TensorProduct

local notation "𝕂" => RatFunc ℚ
local notation "q" => (RatFunc.X : 𝕂)
local instance : NeZero q := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} (hR : R.IsXRegular) (Λ₁ Λ₂ : Dom R)
local notation "V" => fun w : Dom R => IrreducibleModule R q (Subtype.val w)
local notation "h" => fun w : Dom R => IrreducibleModule.hwv R q (Subtype.val w)
local notation "𝓑" => fun w : Dom R => IrreducibleModule.form (Subtype.val w) hR hvn_ratFunc
local notation "T" => V Λ₁ ⊗[𝕂] V Λ₂

private abbrev componentBar : T →+ T :=
  barPair (hwBar hR Λ₁).toAddMonoidHom (hwBar hR Λ₂).toAddMonoidHom
    (hwBar_smul_U' hR Λ₁) (hwBar_smul_U' hR Λ₂)

local notation "b" => componentBar hR Λ₁ Λ₂
local notation "Θ" => quasiRAct (M₁ := V Λ₁) (isPlusLocallyNilpotent_hw Λ₂)
local notation "act" => TensorModule.act R q (V Λ₁) (V Λ₂)
local notation "act₂" => TensorModule.actPair R q (V Λ₁) (V Λ₂)

/-- The normalized intertwiner in the direction used before Proposition 4.33. -/
def websterTheta (x : T) : T := b (Θ (b x))

private theorem quasiR_highest (x : V Λ₁) : Θ (x ⊗ₜ[𝕂] h Λ₂) = x ⊗ₜ[𝕂] h Λ₂ := by
  rw [quasiRAct_apply, finsum_eq_single _ 0 fun ν hν => actPair_quasiR_tmul_eq_zero (fun y hy => ?_) _,
    quasiR_zero, map_one, Module.End.one_apply]
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hy
  rw [AlgHom.toLinearMap_apply, quotientPlus_toQuotient]
  change _ • Submodule.Quotient.mk (VermaModule.hwv R q Λ₂.1) = _
  rw [← Submodule.Quotient.mk_smul, VermaModule.plusHom_smul_hwv,
    LusztigF.counit_eq_zero_of_mem hν hv, zero_smul, Submodule.Quotient.mk_zero]

/-- The intertwiner of the printed form fixes vectors ending in a highest
weight vector, as in the last sentence of the proof of Proposition 4.33. -/
theorem websterTheta_append_highest (x : V Λ₁) :
    websterTheta hR Λ₁ Λ₂ (x ⊗ₜ[𝕂] h Λ₂) = x ⊗ₜ[𝕂] h Λ₂ := by
  change b (Θ ((hwBar hR Λ₁ x) ⊗ₜ[𝕂] (hwBar hR Λ₂ (h Λ₂)))) = _
  rw [hwBar_hwv, quasiR_highest]
  change hwBar hR Λ₁ (hwBar hR Λ₁ x) ⊗ₜ[𝕂] hwBar hR Λ₂ (h Λ₂) = _
  rw [hwBar_hwBar, hwBar_hwv]

/-- The operator in Webster's formula conjugates `Δ` to `barΔ` as used in the
first equality of the proof of Proposition 4.33. -/
theorem websterTheta_act (u : QuantumGroup R q) (x : T) :
    websterTheta hR Λ₁ Λ₂ (act u x) = act₂ (barComul R u) (websterTheta hR Λ₁ Λ₂ x) := by
  change b (Θ (b (act u x))) = _
  have hθ := act_quasiRAct_barPair _ _ (hwBar_smul_U' hR Λ₁) (hwBar_smul_U' hR Λ₂)
    (isPlusLocallyNilpotent_hw Λ₂) (barHom R u) x
  rw [barHom_barHom] at hθ
  rw [← hθ]
  exact barPair_actPair _ _ (hwBar_smul_U' hR Λ₁) (hwBar_smul_U' hR Λ₂) _ _

/-- The factorwise q-Shapovalov form of Webster §4.7. -/
def factorwise (x y : T) : 𝕂 := RatFunc.bar ((𝓑 Λ₁).tmul (𝓑 Λ₂) x (b y))

theorem factorwise_tmul (x x' : V Λ₁) (y y' : V Λ₂) :
    factorwise hR Λ₁ Λ₂ (x ⊗ₜ[𝕂] y) (x' ⊗ₜ[𝕂] y') =
      SingleBlack.websterForm Λ₁ hR x x' * SingleBlack.websterForm Λ₂ hR y y' := by
  change RatFunc.bar (LinearMap.BilinForm.tensorDistrib 𝕂 𝕂 ((𝓑 Λ₁) ⊗ₜ[𝕂] (𝓑 Λ₂))
    _ ((hwBar hR Λ₁ x') ⊗ₜ[𝕂] (hwBar hR Λ₂ y'))) = _
  rw [LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul, map_mul, mul_comm]
  rfl

/-- The formula immediately preceding Webster's Proposition 4.33, with the
quasi-R intertwiner in its printed first argument. -/
def printedForm (x y : T) : 𝕂 := factorwise hR Λ₁ Λ₂ (websterTheta hR Λ₁ Λ₂ x) y

private theorem factorwise_add_left (x y z : T) :
    factorwise hR Λ₁ Λ₂ (x+y) z = factorwise hR Λ₁ Λ₂ x z + factorwise hR Λ₁ Λ₂ y z := by
  simp [factorwise]

private theorem factorwise_add_right (x y z : T) :
    factorwise hR Λ₁ Λ₂ x (y+z) = factorwise hR Λ₁ Λ₂ x y + factorwise hR Λ₁ Λ₂ x z := by
  simp [factorwise]

private theorem lower_highest_orthogonal (i : I) :
    SingleBlack.websterForm Λ₁ hR (F R q i • h Λ₁) (h Λ₁) = 0 := by
  rw [SingleBlack.websterForm_adjoint, rho_F, rhoF, barHom_smul, map_mul, barHom_K, barHom_E,
    smul_assoc, mul_smul, IrreducibleModule.E_smul_hwv, smul_zero, smul_zero]
  simp [SingleBlack.websterForm]

local notation "Ω" => h Λ₁ ⊗ₜ[𝕂] h Λ₂
local notation "f" => fun (i : I) (w : Dom R) => F R q i • h w

/-- The printed two-factor form on the first lowering of the highest tensor.
The first summand's exponent records both the ordinary and the bar-coproduct;
the form conjugates the coefficient in its first argument. -/
theorem printedForm_first_lowering (i : I) :
    printedForm hR Λ₁ Λ₂ (act (F R q i) Ω) (act (F R q i) Ω) =
      SingleBlack.websterForm Λ₁ hR (f i Λ₁) (f i Λ₁) *
        ((q ^ D.d i) ^ (-(Λ₂.1 (R.coroot i))) * (q ^ D.d i) ^ (-(Λ₂.1 (R.coroot i)))) +
      SingleBlack.websterForm Λ₂ hR (f i Λ₂) (f i Λ₂) := by
  rw [printedForm, websterTheta_act, websterTheta_append_highest, barComul_F]
  change factorwise hR Λ₁ Λ₂ (act₂ _ Ω) (act₂ (comul R q (F R q i)) Ω) = _
  rw [comul_F]
  simp only [map_add, LinearMap.add_apply, TensorModule.act_tmul, one_smul]
  rw [show K R q (ktilde R i) • h Λ₂ = _ from
        Kt_smul_of_mem_weightSpace IrreducibleModule.hwv_mem_weightSpace i,
    K_neg_ktilde_smul_of_mem_weightSpace IrreducibleModule.hwv_mem_weightSpace]
  simp only [factorwise_add_left, factorwise_add_right, factorwise_tmul,
    SingleBlack.websterForm_smul_left, SingleBlack.websterForm_smul_right,
    SingleBlack.websterForm_hwv, lower_highest_orthogonal, zero_mul, mul_zero, add_zero, zero_add,
    mul_one, one_mul, map_zpow₀, map_pow, RatFunc.bar_X, inv_pow, inv_zpow']

section Fundamental

/-- Fundamental highest weight of the standard two-dimensional representation. -/
def fundamental : Dom sl2RootDatum :=
  ⟨AddMonoidHom.id ℤ, fun _ => by simp [sl2RootDatum]⟩

/-- The standard root datum of `sl₂` is X-regular. -/
theorem sl2XRegular : sl2RootDatum.IsXRegular := by
  change LinearIndependent ℤ sl2RootDatum.root
  rw [linearIndependent_unique_iff]
  intro hh
  have he := congrArg (fun t : ℤ →+ ℤ => t 1) hh
  norm_num at he

local notation "L" => IrreducibleModule sl2RootDatum q (Subtype.val fundamental)
local notation "v₀" => IrreducibleModule.hwv sl2RootDatum q (Subtype.val fundamental)
local notation "F₁" => F sl2RootDatum q ()
local notation "E₁" => E sl2RootDatum q ()
local notation "K₁" => K sl2RootDatum q 1
local notation "Δ" => TensorModule.act sl2RootDatum q L L
local notation "Φ" => printedForm sl2XRegular fundamental fundamental

/-- The highest tensor in two fundamental modules. -/
def highestPair : L ⊗[𝕂] L := v₀ ⊗ₜ[𝕂] v₀

/-- The vector assigned by Webster just before Lemma 4.36 to the loading
with one black strand after both fundamental red strands. -/
def loweredPair : L ⊗[𝕂] L := Δ F₁ highestPair

private theorem simple_norm : SingleBlack.websterForm fundamental sl2XRegular (F₁ • v₀) (F₁ • v₀) = 1 := by
  rw [SingleBlack.websterForm_lowered]
  change (q ^ 1) ^ ((1 : ℤ) - 1) * qIntZ (q ^ 1) 1 = 1
  rw [pow_one, sub_self, zpow_zero, one_mul, qIntZ_one (sub_inv_ne_zero_of_pow_ne_one RatFunc.X_ne_zero hvn_ratFunc)]

/-- On the terminal first lowering of two fundamental factors, the printed
quasi-R form gives `1+q⁻²`. -/
theorem printedForm_loweredPair : Φ loweredPair loweredPair = 1 + q ^ (-2 : ℤ) := by
  rw [loweredPair, highestPair, printedForm_first_lowering, simple_norm]
  change 1 * ((q ^ 1) ^ (-(1 : ℤ)) * (q ^ 1) ^ (-(1 : ℤ))) + 1 = _
  rw [one_mul, pow_one, ← zpow_add₀ RatFunc.X_ne_zero, add_comm]
  rfl

private theorem K_highest (m : ℤ) : K sl2RootDatum q m • v₀ = q ^ m • v₀ :=
  IrreducibleModule.hwv_mem_weightSpace m

private theorem E_first : E₁ • (F₁ • v₀) = v₀ := by
  have he := (nodeSl2 sl2RootDatum q L hvn_ratFunc (isInt transcendental_ratFunc_X sl2XRegular fundamental) ()).E_F_sub
    (mem_nodeWt_of_mem (i := ()) (IrreducibleModule.hwv_mem_weightSpace (R := sl2RootDatum) (v := q)
      (Λ := fundamental.1)))
  change E₁ • (F₁ • v₀) - F₁ • (E₁ • v₀) = qIntZ (q ^ 1) 1 • v₀ at he
  rwa [IrreducibleModule.E_smul_hwv, smul_zero, sub_zero, pow_one,
    qIntZ_one (sub_inv_ne_zero_of_pow_ne_one RatFunc.X_ne_zero hvn_ratFunc), one_smul] at he

private theorem E_loweredPair : Δ E₁ loweredPair = (q⁻¹ + q) • highestPair := by
  simp only [loweredPair, highestPair, TensorModule.act, AlgHom.comp_apply, comul_E, comul_F,
    map_add, LinearMap.add_apply, TensorModule.act_tmul, one_smul, Kt, sl2RootDatum_ktilde,
    K_highest, IrreducibleModule.E_smul_hwv, E_first, zero_tmul, zero_add,
    zpow_one, zpow_neg_one, add_smul]
  rw [smul_comm E₁, IrreducibleModule.E_smul_hwv, smul_zero, tmul_zero, add_zero,
    tmul_smul, smul_tmul', smul_tmul' (R := 𝕂) q]

private theorem K_highestPair : Δ K₁ highestPair = (q ^ 2) • highestPair := by
  simp only [highestPair, TensorModule.act, AlgHom.comp_apply, comul_K, TensorModule.act_tmul, K_highest,
    zpow_one, smul_tmul_smul, pow_two]

/-- With the same vector and printed `τ` of (3.24), the right-hand side of
the adjunction claimed in Proposition 4.33 is `1+q²`. -/
theorem printedForm_adjoint_loweredPair :
    Φ highestPair (Δ (barHom sl2RootDatum (rho sl2RootDatum q F₁)) loweredPair) = 1 + q ^ 2 := by
  have ht : barHom sl2RootDatum (rho sl2RootDatum q F₁) = q⁻¹ • (K₁ * E₁) := by
    rw [rho_F, rhoF, barHom_smul, map_mul, barHom_K, barHom_E]
    simp
  rw [ht, map_smul, map_mul, LinearMap.smul_apply, Module.End.mul_apply,
    E_loweredPair, map_smul, K_highestPair, smul_smul, smul_smul]
  have hc : q⁻¹ * (q⁻¹ + q) * q ^ 2 = 1 + q ^ 2 := by
    field_simp [RatFunc.X_ne_zero]
  rw [hc, highestPair, printedForm, websterTheta_append_highest, smul_tmul', factorwise_tmul,
    SingleBlack.websterForm_smul_right, SingleBlack.websterForm_hwv, mul_one, mul_one]

/-- Counterexample to adjunction in Webster, arXiv:1309.3796v2,
Proposition 4.33(2), using the tensor form printed immediately above it,
the coproduct of §1.2, and the adjoint in (3.24). -/
theorem printedForm_not_adjoint :
    Φ (Δ F₁ highestPair) loweredPair ≠
      Φ highestPair (Δ (barHom sl2RootDatum (rho sl2RootDatum q F₁)) loweredPair) := by
  change Φ loweredPair loweredPair ≠ _
  rw [printedForm_loweredPair, printedForm_adjoint_loweredPair]
  intro he
  have he' := add_left_cancel he
  rw [zpow_neg, zpow_ofNat] at he'
  have hh := (inv_eq_iff_eq_inv).mp he'
  apply hvn_ratFunc 4 (by decide)
  field_simp [RatFunc.X_ne_zero] at hh
  exact hh

/-- If the bar-conjugate coproduct is used to lower the highest tensor and
the quasi-R intertwiner is accordingly reversed, the same calculation gives
`1+q²`. This is a check on a candidate convention for this example. -/
theorem barCoproduct_loweredPair_norm :
    let z := TensorModule.actPair sl2RootDatum q L L (barComul sl2RootDatum F₁) highestPair
    factorwise sl2XRegular fundamental fundamental
      (quasiRAct (isPlusLocallyNilpotent_hw fundamental) z) z = 1 + q ^ 2 := by
  dsimp only
  rw [← act_quasiRAct, highestPair, quasiR_highest]
  change factorwise sl2XRegular fundamental fundamental
    (TensorModule.actPair sl2RootDatum q L L (comul sl2RootDatum q F₁) _)
    (TensorModule.actPair sl2RootDatum q L L (barComul sl2RootDatum F₁) _) = _
  simp only [comul_F, barComul_F, map_add, LinearMap.add_apply, TensorModule.act_tmul,
    one_smul, sl2RootDatum_ktilde, K_highest, zpow_neg_one, zpow_one, factorwise_add_left,
    factorwise_add_right, factorwise_tmul, SingleBlack.websterForm_smul_left,
    SingleBlack.websterForm_smul_right, SingleBlack.websterForm_hwv, lower_highest_orthogonal,
    simple_norm, map_inv₀, RatFunc.bar_X, inv_inv, mul_one, one_mul, zero_mul, mul_zero, add_zero,
    zero_add]
  ring

end Fundamental

end Categorification.Stendhal.TensorPairing
