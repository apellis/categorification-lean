/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotSemilinear

/-!
# KL III Propositions 2.2, 2.4 over `ℚ(q)`; the nondegeneracy statement (Prop. 2.5)

Khovanov–Lauda III, arXiv:0807.3250v1, §2.1.3, specialised to KL III's setting: the field
`ℚ(q) = RatFunc ℚ`, `q` the indeterminate (`UDot.KL3.qK`), the normalisation
`(θ_i, θ_i) = (1 - q_i²)⁻¹` (`UDot.KL3.cK`), and the bar involution `q ↦ q⁻¹` (`barQ`).
(KL III's `q` is Lusztig's `v⁻¹`; the form on `'f` is `PreF.form C.dot q⁻¹ c`.)

## Proposition 2.5 (nondegeneracy)

KL III derive Proposition 2.5 from Lusztig, *Introduction to quantum groups*, Theorem 26.3.1
(canonical bases of `U̇`); it is **not** proved here. We record it as the proposition
`UDot.Nondegenerate (UDot.formUD …)` and prove:

* `UDot.nondegenerate_formUD_iff` — nondegeneracy of `( , )` on `U̇` is equivalent to the
  statement that the defining relations of `U̇ 1_λ` span the whole left radical of the form on
  the free algebra `'U 1_λ` (a quantum Gabber–Kac-type statement for `U̇`);
* `UDot.nondegenerate_hform_of_formUD` — nondegeneracy of `( , )` implies that of `⟨ , ⟩`
  (the second half of Prop. 2.5 given the first).
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical
open PreF

namespace UDot

variable {I : Type*} {K : Type*} [Field K]
variable {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (q : Kˣ) (c : I → K)

/-! ### Nondegeneracy -/

/-- A bilinear map `F` is *nondegenerate* if its left radical is zero. (For a symmetric form
this is the usual notion.) -/
def Nondegenerate {M : Type*} [AddCommGroup M] [Module K M] (F : M →ₗ[K] M →ₗ[K] K) : Prop :=
  ∀ x, (∀ y, F x y = 0) → x = 0

variable (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)

/-- **KL III Prop. 2.5 for `( , )`, reformulated**: `( , )` is nondegenerate on `U̇` iff for every
`λ`, every element of `'U 1_λ` in the left radical of `UDot.B` lies in the span of the relations
of `U̇ 1_λ`. -/
theorem nondegenerate_formUD_iff :
    Nondegenerate (formUD RD q c hq) ↔
      ∀ (lam : X) (z : Free K I), (∀ w, B C q c (RD.ellOf lam) z w = 0) →
        z ∈ Lrel C q (RD.ellOf lam) := by
  constructor
  · intro h lam z hz
    have h0 : ofB RD q lam (mk RD q lam z) = 0 := by
      refine h _ fun y => ?_
      rw [formUD_ofB]
      obtain ⟨w, hw⟩ := mk_surjective RD q lam (compB RD q lam y)
      rw [← hw, formU_mk, hz]
    have h1 : mk RD q lam z = 0 := by
      have := congrArg (compB RD q lam) h0
      rwa [compB_ofB_self, map_zero] at this
    exact (Submodule.Quotient.mk_eq_zero _).1 h1
  · intro h x hx
    refine DirectSum.ext (β := fun lam => U1 RD q lam) fun lam => ?_
    obtain ⟨z, hz⟩ := mk_surjective RD q lam (compB RD q lam x)
    have hz0 : z ∈ Lrel C q (RD.ellOf lam) := by
      refine h lam z fun w => ?_
      have := hx (ofB RD q lam (mk RD q lam w))
      rw [formUD_symm, formUD_ofB, ← hz, formU_symm, formU_mk] at this
      exact this
    rw [DirectSum.zero_apply]
    change compB RD q lam x = 0
    rw [← hz]
    exact mk_eq_zero RD q lam hz0

/-- **KL III Prop. 2.5, second half**: if `( , )` is nondegenerate on `U̇`, so is `⟨ , ⟩`. -/
theorem nondegenerate_hform_of_formUD (σ : K →+* K) (hσ : σ (q : K) = ((q⁻¹ : Kˣ) : K))
    (hσσ : ∀ a, σ (σ a) = a) (h : Nondegenerate (formUD RD q c hq)) (x : UD RD q)
    (hx : ∀ y, hform RD q c σ hσ hq x y = 0) : x = 0 := by
  have := h _ hx
  rw [← Upsi_Upsi RD q σ hσ hσσ x, this]
  simp [Upsi]

/-! ### KL III's setting: `ℚ(q)` -/

namespace KL3

/-- KL III's `q ∈ ℚ(q)ˣ` (the indeterminate). -/
abbrev qK : (RatFunc ℚ)ˣ := vQ

variable (C) in
/-- KL III's normalisation `(θ_i, θ_i) = (1 - q_i²)⁻¹` (KL III §2.1.1). -/
def cK (i : I) : RatFunc ℚ := (1 - ((qi C qK i : (RatFunc ℚ)ˣ) : RatFunc ℚ) ^ 2)⁻¹

theorem hqK : ∀ n : ℕ, 0 < n → qK ^ n ≠ 1 := fun _ hn => vQ_pow_ne_one hn

/-- KL III §2.1.1: `(θ_i, θ_j) = δ_{ij} (1 - q_i²)⁻¹`. -/
theorem fF_θ_θ (i j : I) :
    fF C qK (cK C) (θ i) (θ j) =
      if i = j then (1 - ((qi C qK i : (RatFunc ℚ)ˣ) : RatFunc ℚ) ^ 2)⁻¹ else 0 := by
  rw [fF, form_θ_θ]; rfl

/-- `cK` agrees with Lusztig's normalisation `(1 - v^{-(i·i)})⁻¹` at `v = q⁻¹`. -/
theorem cK_eq_lusztigC (i : I) : cK C i = lusztigC C.dot qK⁻¹ i := by
  rw [cK, lusztigC, inv_zpow', neg_neg, qi, ← Units.val_pow_eq_pow_val, ← zpow_natCast,
    ← zpow_mul, ← two_mul_di C i]
  congr 3
  push_cast; ring_nf

/-- **Khovanov–Lauda III, Proposition 2.2** over `ℚ(q)`: there is a unique bilinear pairing on
`U̇` with properties (ii)–(v) (KL III's normalisation `(θ_i, θ_i) = (1 - q_i²)⁻¹`). -/
theorem prop_2_2 : ∃! F : UD RD qK →ₗ[RatFunc ℚ] UD RD qK →ₗ[RatFunc ℚ] RatFunc ℚ,
    IsKLPairing RD qK (cK C) F :=
  UDot.prop_2_2 RD qK (cK C) hqK

/-- KL III's bilinear form `( , )` on `U̇` over `ℚ(q)`. -/
def form : UD RD qK →ₗ[RatFunc ℚ] UD RD qK →ₗ[RatFunc ℚ] RatFunc ℚ :=
  formUD RD qK (cK C) hqK

/-- **KL III Definition 2.3**: the semilinear form `⟨x, y⟩ = (ψ(x), y)` over `ℚ(q)`. -/
def sform (x y : UD RD qK) : RatFunc ℚ := hform RD qK (cK C) barQ barQ_vQ hqK x y

/-- **KL III Proposition 2.4** over `ℚ(q)`: (i) semilinearity, (ii) weights, (iii) for the
generators `E_{±i}` (with `τ(E_{εi}) = q_i⁻¹ K̃_{-εi} E_{-εi}`) and `K_μ` (with
`τ(K_μ) = K_{-μ}`), (iv) `⟨x⁺ 1_λ, x'⁺ 1_λ⟩ = (ψ(x), x')`, (v) `⟨x, y⟩ = ⟨ψ(y), ψ(x)⟩`. -/
theorem prop_2_4 :
    (∀ (r : RatFunc ℚ) x y, sform RD (r • x) y = barQ r * sform RD x y) ∧
    (∀ (r : RatFunc ℚ) x y, sform RD x (r • y) = r * sform RD x y) ∧
    (∀ (lam1 lam2 lam1' lam2' : X) x y, ¬ (lam1 = lam1' ∧ lam2 = lam2') →
      sform RD (idem RD qK lam1 lam2 x) (idem RD qK lam1' lam2' y) = 0) ∧
    (∀ l x y, sform RD (UE RD qK l x) y = sform RD x (Utau RD qK l y)) ∧
    (∀ μ x y, sform RD (UK RD qK μ x) y = sform RD x (UK RD qK (-μ) y)) ∧
    (∀ lam (x x' : PreF (RatFunc ℚ) I),
      sform RD (ofB RD qK lam (mk RD qK lam (posF x)))
        (ofB RD qK lam (mk RD qK lam (posF x'))) = fF C qK (cK C) (PreF.bar barQ x) x') ∧
    (∀ x y, sform RD x y =
      sform RD (Upsi RD qK barQ barQ_vQ y) (Upsi RD qK barQ barQ_vQ x)) :=
  ⟨hform_smul_left RD _ _ _ _ hqK, hform_smul_right RD _ _ _ _ hqK,
    hform_weight RD _ _ _ _ hqK, hform_tau_E RD _ _ _ _ hqK, hform_tau_K RD _ _ _ _ hqK,
    hform_posF RD _ _ _ _ hqK, hform_psi RD _ _ _ _ hqK barQ_barQ⟩

end KL3

/-! ### Example: the root datum of `sl₂` -/

/-- The root datum of `sl₂` (`SL₂` form): `I = {pt}`, `X = Y = ℤ`, `⟨y, x⟩ = y x`, `i_X = 2`,
`i = 1`. This shows the hypotheses of `UDot.RootDatum` are satisfiable. -/
def sl2RootDatum : RootDatum (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) ℤ ℤ where
  pair := AddMonoidHom.mul
  perfect_left := by
    refine ⟨fun a b h => ?_, fun f => ⟨f 1, AddMonoidHom.ext_int (by simp)⟩⟩
    simpa using DFunLike.congr_fun h 1
  perfect_right := by
    refine ⟨fun a b h => ?_, fun f => ⟨f 1, AddMonoidHom.ext_int (by simp)⟩⟩
    simpa using DFunLike.congr_fun h 1
  free_X := inferInstance
  finite_X := inferInstance
  free_Y := inferInstance
  finite_Y := inferInstance
  iX _ := 2
  iY _ := 1
  pair_iY_iX _ _ := by simp [CartanDatum.ofGraph]

/-- KL III Proposition 2.2 for `U̇(sl₂)` over `ℚ(q)` (a non-vacuity check). -/
example : ∃! F : UD sl2RootDatum KL3.qK →ₗ[RatFunc ℚ] UD sl2RootDatum KL3.qK →ₗ[RatFunc ℚ] RatFunc ℚ,
    IsKLPairing sl2RootDatum KL3.qK (KL3.cK (CartanDatum.ofGraph (⊥ : SimpleGraph Unit))) F :=
  KL3.prop_2_2 sl2RootDatum

end UDot

end Categorification.QuantumGroup

end
