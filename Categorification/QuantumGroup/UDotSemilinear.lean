/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotPairing

/-!
# The bar involution `ψ` of `U̇` and the semilinear form (KL III Def. 2.3, Prop. 2.4)

Khovanov–Lauda III, arXiv:0807.3250v1, §2.1.2–2.1.3.

* `ψ` is the `ℚ(q)`-antilinear algebra involution of `U` with `ψ(E_i) = E_i`, `ψ(F_i) = F_i`,
  `ψ(K_μ) = K_{-μ}`, extended to `U̇` by `ψ(1_λ) = 1_λ`. On `U̇ 1_λ` it is induced by the
  `σ`-semilinear ring endomorphism `PreF.bar σ` of the free algebra (fixing every `E_w`),
  which preserves the relations (`UDot.bar_Lrel`). Here `σ : K →+* K` is any ring
  endomorphism with `σ q = q⁻¹` (for `K = ℚ(q)`, `σ = barQ`); `ψ² = 1` when `σ² = 1`.
* **Definition 2.3**: `⟨x, y⟩ := (ψ(x), y)` (`UDot.hform`).
* `τ = ψρ` (KL III §2.1.2) satisfies `τ(E_i) = q_i⁻¹ K̃_{-i} F_i`, `τ(F_i) = q_i⁻¹ K̃_i E_i` —
  the same elements as `ρ̄(E_i)`, `ρ̄(F_i)` — and `τ(K_μ) = K_{-μ}`.

## Main results (KL III Proposition 2.4)

* `UDot.hform_smul_left`, `UDot.hform_smul_right` — (i) semilinearity;
* `UDot.hform_weight` — (ii);
* `UDot.hform_tau_E`, `UDot.hform_tau_K` — (iii) for the generators `E_{±i}`, `K_μ`;
* `UDot.hform_posF` — (iv): `⟨x⁺ 1_λ, x'⁺ 1_λ⟩ = (ψ(x), x')` for `x, x' ∈ 'f`;
* `UDot.hform_psi` — (v): `⟨x, y⟩ = ⟨ψ(y), ψ(x)⟩`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical
open PreF

namespace UDot

variable {I : Type*} {K : Type*} [Field K]
variable {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (q : Kˣ) (c : I → K) (σ : K →+* K)

/-! ### `ψ` on the free algebra -/

/-- `ψ` on `'U 1_λ`: the `σ`-semilinear ring endomorphism fixing every `E_w`. -/
def psiF : Free K I →ₛₗ[σ] Free K I where
  toFun := PreF.bar σ
  map_add' := map_add _
  map_smul' r x := PreF.bar_smul σ r x

theorem psiF_apply (x : Free K I) : psiF σ x = PreF.bar σ x := rfl

theorem bar_ew (t : List (Bool × I)) : PreF.bar σ (ew t : Free K I) = ew t := bar_word σ _

theorem bar_posF (T : PreF K I) : PreF.bar σ (posF T : Free K I) = posF (PreF.bar σ T) := by
  induction T using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | smul_word u r =>
    rw [map_smul, bar_smul, bar_smul, bar_word, map_smul, posF_word, bar_ew]

theorem bar_negF (T : PreF K I) : PreF.bar σ (negF T : Free K I) = negF (PreF.bar σ T) := by
  induction T using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | smul_word u r =>
    rw [map_smul, bar_smul, bar_smul, bar_word, map_smul, negF_word, bar_ew]

variable {q σ}

theorem σ_qi (hσ : σ (q : K) = ((q⁻¹ : Kˣ) : K)) (i : I) :
    σ ((qi C q i : Kˣ) : K) = (((qi C q i)⁻¹ : Kˣ) : K) := by
  rw [qi, σ_zpow hσ, zpow_neg]

theorem σ_qbr (hσ : σ (q : K) = ((q⁻¹ : Kˣ) : K)) (i : I) (n : ℤ) :
    σ (qbr (qi C q i) n) = qbr (qi C q i) n := by
  have h1 := σ_qi (C := C) hσ i
  have h2 : σ ((((qi C q i)⁻¹ : Kˣ)) : K) = ((qi C q i : Kˣ) : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, h1, Units.val_inv_eq_inv_val, inv_inv]
  rw [qbr, map_div₀, map_sub, map_sub, σ_zpow h1, σ_zpow h1, h1, h2, neg_neg,
    ← neg_div_neg_eq, neg_sub, neg_sub]

theorem bar_serreKL (hσ : σ (q : K) = ((q⁻¹ : Kˣ) : K)) (i j : I) :
    PreF.bar σ (serreKL C q i j) = serreKL C q i j := by
  rw [serreKL, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [bar_smul, map_mul, map_mul, bar_dpow σ hσ, bar_dpow σ hσ, bar_θ, map_pow, map_neg, map_one]

theorem bar_commRel (hσ : σ (q : K) = ((q⁻¹ : Kˣ) : K)) (ℓ : I → ℤ) (b : List (Bool × I))
    (i j : I) : PreF.bar σ (commRel C q ℓ b i j) = commRel C q ℓ b i j := by
  rw [commRel, map_sub, map_sub, bar_ew, bar_ew, bar_smul, map_one]
  split_ifs
  · rw [σ_qbr hσ]
  · rw [map_zero]

theorem bar_Lrel (hσ : σ (q : K) = ((q⁻¹ : Kˣ) : K)) (ℓ : I → ℤ) :
    Lrel C q ℓ ≤ (Lrel C q ℓ).comap (psiF σ) := by
  rw [Lrel, Submodule.span_le]
  intro z hz
  simp only [SetLike.mem_coe, Submodule.mem_comap, psiF_apply]
  refine Submodule.subset_span ?_
  rcases hz with ⟨a, b, i, j, rfl⟩ | ⟨a, b, i, j, hij, rfl | rfl⟩
  · rw [map_mul, map_mul, bar_ew, bar_ew, bar_commRel hσ]; exact Or.inl ⟨a, b, i, j, rfl⟩
  · rw [map_mul, map_mul, bar_ew, bar_ew, bar_posF, bar_serreKL hσ]
    exact Or.inr ⟨a, b, i, j, hij, Or.inl rfl⟩
  · rw [map_mul, map_mul, bar_ew, bar_ew, bar_negF, bar_serreKL hσ]
    exact Or.inr ⟨a, b, i, j, hij, Or.inr rfl⟩

/-! ### `ψ` on `U̇` -/

variable (q σ)
variable (hσ : σ (q : K) = ((q⁻¹ : Kˣ) : K))

/-- `ψ` on `U̇ 1_λ` (KL III §2.1.2–2.1.3): `σ`-semilinear, fixing every `E_w 1_λ`. -/
def psi (lam : X) : U1 RD q lam →ₛₗ[σ] U1 RD q lam :=
  (Lrel C q (RD.ellOf lam)).mapQ _ (psiF σ) (bar_Lrel hσ _)

theorem psi_mk (lam : X) (z : Free K I) :
    psi RD q σ hσ lam (mk RD q lam z) = mk RD q lam (PreF.bar σ z) := rfl

theorem psi_mk_ew (lam : X) (t : List (Bool × I)) :
    psi RD q σ hσ lam (mk RD q lam (ew t)) = mk RD q lam (ew t) := by
  rw [psi_mk, bar_ew]

/-- Two `σ`-semilinear endomorphisms of `U̇ 1_λ` agreeing on the `E_t 1_λ` are equal. -/
theorem semilin_ext {lam : X} {F G : U1 RD q lam →ₛₗ[σ] U1 RD q lam}
    (h : ∀ t, F (mk RD q lam (ew t)) = G (mk RD q lam (ew t))) (x : U1 RD q lam) : F x = G x := by
  obtain ⟨z, rfl⟩ := mk_surjective RD q lam x
  induction z using Free.induction with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul_ew t r => rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h]

theorem psi_psi (hσσ : ∀ a, σ (σ a) = a) (lam : X) (x : U1 RD q lam) :
    psi RD q σ hσ lam (psi RD q σ hσ lam x) = x := by
  obtain ⟨z, rfl⟩ := mk_surjective RD q lam x
  induction z using Free.induction with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul_ew t r =>
    rw [map_smul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, psi_mk_ew, psi_mk_ew, hσσ]

theorem psi_Egen (lam : X) (l : Bool × I) (x : U1 RD q lam) :
    psi RD q σ hσ lam (Egen RD q lam l x) = Egen RD q lam l (psi RD q σ hσ lam x) := by
  obtain ⟨z, rfl⟩ := mk_surjective RD q lam x
  rw [Egen_mk, psi_mk, psi_mk, Egen_mk, map_mul, bar_ew]

theorem psi_Kact (lam : X) (μ : Y) (x : U1 RD q lam) :
    psi RD q σ hσ lam (Kact RD q lam μ x) = Kact RD q lam (-μ) (psi RD q σ hσ lam x) := by
  have base : ∀ t, psi RD q σ hσ lam (Kact RD q lam μ (mk RD q lam (ew t))) =
      Kact RD q lam (-μ) (psi RD q σ hσ lam (mk RD q lam (ew t))) := by
    intro t
    rw [Kact_mk_ew, LinearMap.map_smulₛₗ, psi_mk_ew, Kact_mk_ew, qp, σ_zpow hσ, qp, map_neg,
      AddMonoidHom.neg_apply]
  obtain ⟨z, rfl⟩ := mk_surjective RD q lam x
  induction z using Free.induction with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul_ew t r =>
    rw [map_smul, map_smul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, base, map_smul]

theorem psi_oneL (lam ν : X) (x : U1 RD q lam) :
    psi RD q σ hσ lam (oneL RD q lam ν x) = oneL RD q lam ν (psi RD q σ hσ lam x) := by
  have base : ∀ t, psi RD q σ hσ lam (oneL RD q lam ν (mk RD q lam (ew t))) =
      oneL RD q lam ν (psi RD q σ hσ lam (mk RD q lam (ew t))) := by
    intro t
    rw [oneL_mk_ew, psi_mk_ew, oneL_mk_ew]
    split_ifs
    · rw [psi_mk_ew]
    · simp
  obtain ⟨z, rfl⟩ := mk_surjective RD q lam x
  induction z using Free.induction with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul_ew t r =>
    rw [map_smul, map_smul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, base, map_smul]

theorem psi_posF (lam : X) (x : PreF K I) :
    psi RD q σ hσ lam (mk RD q lam (posF x)) = mk RD q lam (posF (PreF.bar σ x)) := by
  rw [psi_mk, bar_posF]

/-- `ψ` on `U̇ = ⊕_λ U̇ 1_λ`, blockwise. -/
def Upsi (x : UD RD q) : UD RD q :=
  DFinsupp.mapRange (fun lam => psi RD q σ hσ lam) (fun _ => map_zero _) x

theorem Upsi_ofB (lam : X) (z : U1 RD q lam) :
    Upsi RD q σ hσ (ofB RD q lam z) = ofB RD q lam (psi RD q σ hσ lam z) :=
  DFinsupp.mapRange_single

theorem compB_Upsi (lam : X) (x : UD RD q) :
    compB RD q lam (Upsi RD q σ hσ x) = psi RD q σ hσ lam (compB RD q lam x) := by
  change (DFinsupp.mapRange (fun lam => psi RD q σ hσ lam) (fun _ => map_zero _) x) lam = _
  exact DFinsupp.mapRange_apply _ _ _ _

theorem Upsi_add (x y : UD RD q) :
    Upsi RD q σ hσ (x + y) = Upsi RD q σ hσ x + Upsi RD q σ hσ y :=
  DFinsupp.mapRange_add _ _ (fun _ => map_add _) _ _

theorem Upsi_smul (r : K) (x : UD RD q) : Upsi RD q σ hσ (r • x) = σ r • Upsi RD q σ hσ x := by
  induction x using UD_induction with
  | zero => simp [Upsi]
  | add x y hx hy => rw [smul_add, Upsi_add, Upsi_add, hx, hy, smul_add]
  | ofB lam z => rw [← map_smul, Upsi_ofB, Upsi_ofB, LinearMap.map_smulₛₗ, map_smul]

theorem Upsi_Upsi (hσσ : ∀ a, σ (σ a) = a) (x : UD RD q) : Upsi RD q σ hσ (Upsi RD q σ hσ x) = x := by
  induction x using UD_induction with
  | zero => simp [Upsi]
  | add x y hx hy => rw [Upsi_add, Upsi_add, hx, hy]
  | ofB lam z => rw [Upsi_ofB, Upsi_ofB, psi_psi RD q σ hσ hσσ]

/-! ### The semilinear form (Definition 2.3) -/

variable (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)

/-- **KL III Definition 2.3**: the semilinear form `⟨x, y⟩ := (ψ(x), y)` on `U̇`. -/
def hform (x y : UD RD q) : K := formUD RD q c hq (Upsi RD q σ hσ x) y

/-- **KL III Prop. 2.4 (i)**: `⟨f x, y⟩ = f̄ ⟨x, y⟩`. -/
theorem hform_smul_left (r : K) (x y : UD RD q) :
    hform RD q c σ hσ hq (r • x) y = σ r * hform RD q c σ hσ hq x y := by
  rw [hform, hform, Upsi_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- **KL III Prop. 2.4 (i)**: `⟨x, f y⟩ = f ⟨x, y⟩`. -/
theorem hform_smul_right (r : K) (x y : UD RD q) :
    hform RD q c σ hσ hq x (r • y) = r * hform RD q c σ hσ hq x y := by
  rw [hform, hform, map_smul, smul_eq_mul]

theorem Upsi_idem (lam1 lam2 : X) (x : UD RD q) :
    Upsi RD q σ hσ (idem RD q lam1 lam2 x) = idem RD q lam1 lam2 (Upsi RD q σ hσ x) := by
  rw [idem, LinearMap.comp_apply, LinearMap.comp_apply, Upsi_ofB, psi_oneL,
    LinearMap.comp_apply, LinearMap.comp_apply, compB_Upsi]

/-- **KL III Prop. 2.4 (ii)**. -/
theorem hform_weight (lam1 lam2 lam1' lam2' : X) (x y : UD RD q)
    (h : ¬ (lam1 = lam1' ∧ lam2 = lam2')) :
    hform RD q c σ hσ hq (idem RD q lam1 lam2 x) (idem RD q lam1' lam2' y) = 0 := by
  rw [hform, Upsi_idem, formUD_weight RD q c hq _ _ _ _ _ _ h]

theorem Upsi_UE (l : Bool × I) (x : UD RD q) :
    Upsi RD q σ hσ (UE RD q l x) = UE RD q l (Upsi RD q σ hσ x) := by
  induction x using UD_induction with
  | zero => simp [Upsi]
  | add x y hx hy => rw [map_add, Upsi_add, Upsi_add, hx, hy, map_add]
  | ofB lam z => rw [UE, blockMap_ofB, Upsi_ofB, Upsi_ofB, blockMap_ofB, psi_Egen]

theorem Upsi_UK (μ : Y) (x : UD RD q) :
    Upsi RD q σ hσ (UK RD q μ x) = UK RD q (-μ) (Upsi RD q σ hσ x) := by
  induction x using UD_induction with
  | zero => simp [Upsi]
  | add x y hx hy => rw [map_add, Upsi_add, Upsi_add, hx, hy, map_add]
  | ofB lam z => rw [UK, blockMap_ofB, Upsi_ofB, Upsi_ofB, UK, blockMap_ofB, psi_Kact]

/-- Left multiplication by `τ(E_{εi}) = q_i⁻¹ K̃_{-εi} E_{-εi}` on `U̇` (KL III §2.1.2); as an
element of `U` this is `ρ̄(E_{εi})`. -/
abbrev Utau (l : Bool × I) : UD RD q →ₗ[K] UD RD q := Urho RD q l

/-- **KL III Prop. 2.4 (iii)** for `u = E_{±i}`: `⟨E_{εi} x, y⟩ = ⟨x, τ(E_{εi}) y⟩`. -/
theorem hform_tau_E (l : Bool × I) (x y : UD RD q) :
    hform RD q c σ hσ hq (UE RD q l x) y = hform RD q c σ hσ hq x (Utau RD q l y) := by
  rw [hform, hform, Upsi_UE, formUD_rho_E]

/-- **KL III Prop. 2.4 (iii)** for `u = K_μ`: `⟨K_μ x, y⟩ = ⟨x, τ(K_μ) y⟩ = ⟨x, K_{-μ} y⟩`. -/
theorem hform_tau_K (μ : Y) (x y : UD RD q) :
    hform RD q c σ hσ hq (UK RD q μ x) y = hform RD q c σ hσ hq x (UK RD q (-μ) y) := by
  rw [hform, hform, Upsi_UK, formUD_rho_K]

/-- **KL III Prop. 2.4 (iv)**: `⟨x⁺ 1_λ, x'⁺ 1_λ⟩ = (ψ(x), x')` for `x, x' ∈ 'f`. -/
theorem hform_posF (lam : X) (x x' : PreF K I) :
    hform RD q c σ hσ hq (ofB RD q lam (mk RD q lam (posF x))) (ofB RD q lam (mk RD q lam (posF x'))) =
      fF C q c (PreF.bar σ x) x' := by
  rw [hform, Upsi_ofB, psi_posF, formUD_posF]

/-- **KL III Prop. 2.4 (v)**: `⟨x, y⟩ = ⟨ψ(y), ψ(x)⟩`. -/
theorem hform_psi (hσσ : ∀ a, σ (σ a) = a) (x y : UD RD q) :
    hform RD q c σ hσ hq x y = hform RD q c σ hσ hq (Upsi RD q σ hσ y) (Upsi RD q σ hσ x) := by
  rw [hform, hform, Upsi_Upsi RD q σ hσ hσσ, formUD_symm]

end UDot

end Categorification.QuantumGroup

end
