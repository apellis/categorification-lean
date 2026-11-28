/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.QuantumTracePairing
import LieLean.Algebra.QuantumGroup.ModuleSymmetry.Integrable

/-!
# Invariant functionals from the vanishing on `F_i`-images

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 7.5. Webster shows that `[L_λ]` is invariant by checking that it has weight `0` and
that `Hom(F_i P, L_λ) = 0` for all projectives `P`, i.e. that the class functional of `L_λ`
vanishes on the images of the `F_i`; "the invariants are the vectors of weight `0` killed by
the `E_i`". This file proves the dual statement used there, for functionals on an integrable
module:

* `IntegrableSl2.apply_E_eq_zero`: on an integrable `U_q(𝔰𝔩₂)`-module, a functional that
  vanishes off weight `0` and on the image of `F` vanishes on the image of `E` (the string
  `F^{(j)} η` through weight `-2` reaches weight `0` only from `F^{(b)} η` with `b ≥ 1`, or from
  `E F η = [0] η = 0`).
* `apply_smul_eq_counit_mul`: on an integrable `U_q(g)`-module, a functional `f` with
  `f(K_μ m) = f(m)` and `f(F_i m) = 0` is invariant: `f(u m) = ε(u) f(m)`.
* `eq_smul_quantumTrace_of_F`: on `V_μ ⊗ V_{μ*}`, such a functional is
  `f(v_l ⊗ v_h) • qtr_μ` (the invariant line, `eq_smul_quantumTrace_of_invariant`).

The proof is ours (strings of integrable `𝔰𝔩₂`-modules, `IntegrableSl2.mem_strings`).
-/

noncomputable section

namespace LieLean.QuantumGroup.IntegrableSl2

variable {k : Type*} [Field k] {q : k} (hq0 : q ≠ 0) (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
  {M : Type*} [AddCommGroup M] [Module k M] (V : IntegrableSl2 q M)

include hq0 hq in
/-- **A functional killing the image of `F` and supported in weight `0` kills the image of
`E`**, on an integrable `U_q(𝔰𝔩₂)`-module. -/
theorem apply_E_eq_zero (f : M →ₗ[k] k) (hF : ∀ m, f (V.F m) = 0)
    (hwt : ∀ n : ℤ, n ≠ 0 → ∀ m ∈ V.wt n, f m = 0) (m : M) : f (V.E m) = 0 := by
  have hm : m ∈ ⨆ n, V.wt n := by rw [V.iSup_wt]; exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun m => f (V.E m) = 0) hm ?_ ?_ ?_
  · intro n x hx
    by_cases hn : n + 2 = 0
    · have hn' : n = -2 := by omega
      subst hn'
      have hs := mem_strings hq0 hq hx
      refine Submodule.span_induction (p := fun x _ => f (V.E x) = 0) ?_ ?_ ?_ ?_ hs
      · rintro _ ⟨j, η, hη, hE, rfl⟩
        rcases j with _ | b
        · rw [dF_zero, hE, map_zero]
        · rw [E_dF_succ_of_primitive hq0 hq hη hE b, map_smul]
          rcases b with _ | c
          · simp
          · have h1 := F_dF (V := V) hq0 hq c η
            have hc := qInt_ne_zero_of_pow_ne_one hq0 hq (Nat.succ_pos c)
            have h2 : V.dF (c + 1) η = (qInt q (c + 1))⁻¹ • V.F (V.dF c η) := by
              rw [h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
            rw [h2, map_smul, hF, smul_zero, smul_zero]
      · simp
      · intro x y _ _ hx hy
        rw [map_add, map_add, hx, hy, add_zero]
      · intro a x _ hx
        rw [map_smul, map_smul, hx, smul_zero]
    · exact hwt (n + 2) hn _ (V.E_mem hx)
  · simp
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, add_zero]

end LieLean.QuantumGroup.IntegrableSl2

namespace Categorification.Stendhal.QuantumDual

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop KLR.CycKLR Module
open scoped TensorProduct

section Integrable

variable {k I Y : Type*} [Field k] [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} {v : k} [NeZero v] (hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1)
  {M : Type*} [AddCommGroup M] [Module k M] [Module (QuantumGroup R v) M]
  [IsScalarTower k (QuantumGroup R v) M] (hM : IsIntegrable R v M)

include hv hM in
/-- **Invariance from the vanishing on `F_i`-images** (the step "`[L_λ]` is invariant" in the
proof of Webster's Proposition 7.5, dually): on an integrable module, a functional `f` with
`f(K_μ m) = f(m)` (weight `0`) and `f(F_i m) = 0` for all `i` is invariant,
`f(u m) = ε(u) f(m)`. -/
theorem apply_smul_eq_counit_mul (f : M →ₗ[k] k) (hK : ∀ (μ : Y) (m : M), f (K R v μ • m) = f m)
    (hF : ∀ (i : I) (m : M), f (F R v i • m) = 0) (u : QuantumGroup R v) (m : M) :
    f (u • m) = counit R v u * f m := by
  have hwt0 : ∀ (Λ : Y →+ ℤ) (μ : Y), Λ μ ≠ 0 → ∀ x ∈ weightSpace R v M Λ, f x = 0 := by
    intro Λ μ hΛ x hx
    have h1 := hK μ x
    rw [(mem_weightSpace.1 hx) μ, map_smul, smul_eq_mul] at h1
    have h2 : (v ^ Λ μ - 1) * f x = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (zpow_ne_one_of_pow_ne_one hv hΛ))
  have hE : ∀ (i : I) (m : M), f (E R v i • m) = 0 := by
    intro i m
    refine IntegrableSl2.apply_E_eq_zero (pow_ne_zero _ (NeZero.ne v)) (pow_d_ne_one hv i)
      (nodeSl2 R v M hv hM i) f (fun m => hF i m) (fun n hn x hx => ?_) m
    rw [nodeSl2_wt] at hx
    refine nodeWt_induction (P := fun x => f x = 0) hx (map_zero f)
      (fun a b ha hb => by rw [map_add, ha, hb, add_zero]) fun Λ hΛ y hy =>
        hwt0 Λ (R.coroot i) (by rw [hΛ]; exact hn) y hy
  induction u using QuantumGroup.induction_on generalizing m with
  | algebraMap c => rw [algebraMap_smul, map_smul, AlgHom.commutes, smul_eq_mul,
      Algebra.algebraMap_self, RingHom.id_apply]
  | E i => rw [hE, counit_E, zero_mul]
  | F i => rw [hF, counit_F, zero_mul]
  | K μ => rw [hK, counit_K, one_mul]
  | add a b ha hb => rw [add_smul, map_add, ha, hb, map_add, add_mul]
  | mul a b ha hb => rw [mul_smul, ha, hb, map_mul, mul_assoc]

end Integrable

/-! ### The invariant line on `V_μ ⊗ V_{μ*}` -/

section Line

variable {I K H Y : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Y]
    {Δ : LusztigCartanDatum I} {R : Δ.RootDatum Y}
    [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] (P : Matrix.Realization Δ.cartanMatrix K H)

local notation "vQ" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance : NeZero vQ := ⟨RatFunc.X_ne_zero⟩

variable [FiniteDimensional K H] (hR : R.IsXRegular) (μ : Dom R) (weight : P.integralWeights)
  (hdom : P.IsDominantIntegral (weight : Dual K H))
  (hm : ∀ j, (weight : Dual K H) (P.coroot j) = (μ.1 (R.coroot j) : K))
  (w : List I)
variable (hw : (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
  (hlong : ∀ i, (P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).IsLeftDescent
    ((P.coxeterSystem Δ.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)

local notation "μs" => dualWeight P μ weight hdom hm w hw hlong
local notation "Vμ" => IrreducibleModule R vQ (Subtype.val μ)
local notation "Vμs" =>
  IrreducibleModule R vQ (Subtype.val (dualWeight P μ weight hdom hm w hw hlong))
local notation "vl" => lowestVector P μ weight w

omit [Fintype I] in
private theorem ratFunc_X_pow_ne_one : ∀ n : ℕ, 0 < n → vQ ^ n ≠ 1 :=
  fun _ hn => LusztigF.pow_ne_one_of_transcendental LusztigF.transcendental_ratFunc_X hn

include hR in
/-- **The class functional of an invariant module is a multiple of `qtr_μ`** (the invariance
step of Webster's proof of Proposition 7.5, on `V_μ ⊗ V_{μ*}`): a functional of weight `0`
vanishing on the images of the `F_i` is `f(v_l ⊗ v_h) • qtr_μ`. -/
theorem eq_smul_quantumTrace_of_F (f : TensorModule 𝕂 Vμ Vμs →ₗ[𝕂] 𝕂)
    (hK : ∀ (y : Y) t, f (QuantumGroup.K R vQ y • t) = f t)
    (hF : ∀ (i : I) t, f (QuantumGroup.F R vQ i • t) = 0) :
    f = f (TensorModule.mk Vμ Vμs (vl ⊗ₜ IrreducibleModule.hwv R vQ μs.1)) •
      quantumTrace P hR μ weight hdom hm w hw hlong := by
  have hM : IsIntegrable R vQ (TensorModule 𝕂 Vμ Vμs) :=
    TensorModule.isIntegrable (IrreducibleModule.isIntegrable hR ratFunc_X_pow_ne_one μ.2)
      (IrreducibleModule.isIntegrable hR ratFunc_X_pow_ne_one μs.2)
  exact eq_smul_quantumTrace_of_invariant P hR μ weight hdom hm w hw hlong f
    (apply_smul_eq_counit_mul ratFunc_X_pow_ne_one hM f hK hF)

end Line

end Categorification.Stendhal.QuantumDual
