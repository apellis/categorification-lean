/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotSemilinear
import Categorification.QuantumGroup.UDotOmega
import Categorification.QuantumGroup.UDotIntegral

/-!
# The anti-automorphisms `σ`, `ρ̄` and `τ` of `U̇`

Khovanov–Lauda III, arXiv:0807.3250v1, §2.1.2 ("Some automorphisms of `U`") and the paragraph
after (2.7) in §2.1.3 ("The (anti) automorphisms `ψ, ω, σ, ρ` and `τ` all naturally extend to `U̇`
and `_𝒜U̇` if we set `ψ(1_λ) = 1_λ`, `ω(1_λ) = 1_{-λ}`, `σ(1_λ) = 1_{-λ}`, `ρ(1_λ) = 1_λ`,
`τ(1_λ) = 1_λ`").

* `σ` is the `ℚ(q)`-linear algebra anti-involution with `σ(E_i) = E_i`, `σ(F_i) = F_i`,
  `σ(1_λ) = 1_{-λ}`. On a signed sequence `t` it reverses the order:
  `σ(E_t 1_λ) = 1_{-λ} E_{t^rev} = E_{t^rev} 1_{-(λ + t_X)}` (`UDot.sigmaUD_E1`).
* `ρ̄ = ψρψ` is the `ℚ(q)`-linear anti-involution with `ρ̄(E_i) = q_i⁻¹ K̃_{-i} F_i`,
  `ρ̄(F_i) = q_i⁻¹ K̃_i E_i`, `ρ̄(1_λ) = 1_λ`, so
  `ρ̄(E_{εi} 1_λ) = q_i^{-1-ε⟨i,λ⟩} E_{-εi} 1_{λ+εi_X}` and, for a signed sequence `t`,
  `ρ̄(E_t 1_λ) = q^{rexp λ t} E_{ρW t} 1_{λ + t_X}` with `ρW t` the reversed sequence with all signs
  flipped (`UDot.rhobarUD_E1`, `UDot.rexp`).
* `τ = ψρ` is the `ℚ(q)`-antilinear anti-automorphism with `τ(E_i) = q_i⁻¹ K̃_{-i} F_i`,
  `τ(F_i) = q_i⁻¹ K̃_i E_i`, `τ(1_λ) = 1_λ`. Since `ψ² = 1`, `τ = ψρ = ρ̄ψ`; we define
  `UDot.tauUD := ρ̄ ∘ ψ`.

The anti-automorphisms do not preserve the blocks `U̇ 1_λ` (the right weight of `σ(E_t 1_λ)` is
`-(λ + t_X)`), so they are constructed on the whole of `U̇ = ⊕_λ U̇ 1_λ` by a generic construction
(`UDot.antiU`): a family `F λ t` of elements of `U̇`, anti-multiplicative on words
(`F λ (s t) = F λ t · F (λ + t_X) s`) and killing the relators with trivial prefix and suffix,
extends to a linear anti-homomorphism `U̇ → U̇`.

## Main results

* `UDot.sigmaUD_E1`, `UDot.sigmaUD_one` — `σ(E_t 1_λ) = E_{t^rev} 1_{-(λ+t_X)}`,
  `σ(1_λ) = 1_{-λ}`;
* `UDot.sigmaUD_mul`, `UDot.sigmaUD_sigmaUD` — `σ` is an anti-homomorphism and `σ² = 1`;
* `UDot.rhobarUD_E1`, `UDot.rhobarUD_mul`, `UDot.rhobarUD_rhobarUD` — `ρ̄` is an
  anti-involution; `UDot.rhobarUD_E`, `UDot.rhobarUD_F`: the values on `E_i 1_λ`, `F_i 1_λ`;
* `UDot.tauUD_E`, `UDot.tauUD_F` — **the formulas of KL III §2.1.3**:
  `τ(1_{λ+i_X} E_i 1_λ) = q_i^{-1-⟨i,λ⟩} 1_λ F_i 1_{λ+i_X}` and
  `τ(1_λ F_i 1_{λ+i_X}) = q_i^{1+⟨i,λ⟩} 1_{λ+i_X} E_i 1_λ`; `UDot.tauUD_one`: `τ(1_λ) = 1_λ`;
* `UDot.tauUD_mul`, `UDot.tauUD_smul` — `τ` is an antilinear anti-homomorphism;
  `UDot.tauUD_tauInv`, `UDot.tauInv_tauUD` — it is bijective, with inverse `ψρ̄`;
* `UDot.rhoUD` — `ρ = ψρ̄ψ` (`ρ(E_i) = q_i K̃_i F_i`), a linear anti-involution
  (`UDot.rhoUD_mul`, `UDot.rhoUD_rhoUD`); `UDot.tauUD_eq_psi_rho` (`τ = ψρ`, KL III's
  definition), `UDot.rhobarUD_eq_psi_rho_psi` (`ρ̄ = ψρψ`);
* relations: `UDot.sigmaUD_Uomega` (`σω = ωσ`), `UDot.sigmaUD_Upsi` (`σψ = ψσ`),
  `UDot.Uomega_rhobarUD` (`ωρ̄ = ρ̄ω`), `UDot.Uomega_tauUD` (`ωτ = τω`),
  `UDot.sigmaUD_tauUD_sigmaUD` (`στσ = τ⁻¹ = ψρ̄`);
* divided powers and `_𝒜 U̇`: `UDot.sigmaUD_E1dp` (`σ(E_d 1_λ) = E_{d^rev} 1_{-(λ+|d|_X)}`),
  `UDot.tauUD_E1dp` (`τ(E_d 1_λ) = q^{rexp} E_{ρ̄ d} 1_{λ+|d|_X}`), and `UDot.sigmaUD_mem_AUD`,
  `UDot.rhobarUD_mem_AUD`, `UDot.tauUD_mem_AUD`: `σ`, `ρ̄`, `τ` preserve `_𝒜 U̇` (KL III §2.1.3:
  "we obtain an algebra antiautomorphism `τ : _𝒜 U̇ → _𝒜 U̇`").

Throughout, `σK : K →+* K` is a ring endomorphism with `σK q = q⁻¹` (the bar involution of
`ℚ(q)`, `barQ`), as in `Categorification.QuantumGroup.UDotSemilinear`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical
open PreF

namespace UDot

variable {I : Type*} {K : Type*} [Field K]
variable {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (q : Kˣ)

/-! ### Generic anti-homomorphisms of `U̇` -/

section Anti

variable (F : X → List (Bool × I) → UD RD q)

/-- The linear map `'U 1_λ → U̇`, `E_w ↦ F λ w`. -/
def antiF (lam : X) : Free K I →ₗ[K] UD RD q := PreF.linLift fun w => F lam w.toList

theorem antiF_ew (lam : X) (t : List (Bool × I)) : antiF RD q F lam (ew t) = F lam t := by
  rw [antiF, ew, PreF.linLift_word]
  rfl

/-- The anti-multiplicativity hypothesis on words. -/
def AntiMul : Prop := ∀ lam s t, F lam (s ++ t) = F lam t * F (lam + RD.wX t) s

variable {RD q F}

/-- **Anti-multiplicativity of `antiF`**: `F_λ(x y) = F_λ(y) F_{λ+μ}(x)` for `y` of weight `μ`. -/
theorem antiF_mul (hF : AntiMul RD q F) (lam μ : X) (x : Free K I) {y : Free K I}
    (hy : y ∈ FX K RD μ) :
    antiF RD q F lam (x * y) = antiF RD q F lam y * antiF RD q F (lam + μ) x := by
  refine eqOn_supp ((antiF RD q F lam).comp (LinearMap.mulLeft K x))
    ((LinearMap.mulRight K (antiF RD q F (lam + μ) x)).comp (antiF RD q F lam)) ?_ y hy
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  rw [word_eq_ew]
  induction x using Free.induction with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, mul_add]
  | smul_ew s r =>
    rw [smul_mul_assoc, map_smul, map_smul, mul_smul_comm, ← ew_append, antiF_ew, antiF_ew,
      antiF_ew, hF, hw]

theorem ew_mem_FX' (t : List (Bool × I)) : (ew t : Free K I) ∈ FX K RD (RD.wX t) :=
  ew_mem_FX RD t

theorem commRel_mem_FX (ℓ : I → ℤ) (b : List (Bool × I)) (i j : I) :
    ∃ μ, (commRel C q ℓ b i j : Free K I) ∈ FX K RD μ := by
  refine ⟨RD.wX [(true, i), (false, j)], ?_⟩
  unfold commRel
  refine sub_mem (sub_mem (ew_mem_FX RD _) ?_) ?_
  · have := ew_mem_FX (K := K) RD [(false, j), (true, i)]
    convert this using 2
    simp; abel
  · split_ifs with h
    · subst h
      refine Submodule.smul_mem _ _ ?_
      have := ew_mem_FX (K := K) RD []
      convert this using 2
      simp
    · simp

theorem posF_serreKL_mem_FX (i j : I) : ∃ μ, (posF (serreKL C q i j) : Free K I) ∈ FX K RD μ :=
  ⟨_, Fg_le_FX RD _ _ (posF_mem_Fg (serreKL_mem_grade (C := C) (q := q) i j))⟩

theorem negF_serreKL_mem_FX (i j : I) : ∃ μ, (negF (serreKL C q i j) : Free K I) ∈ FX K RD μ :=
  ⟨_, Fg_le_FX RD _ _ (negF_mem_Fg (serreKL_mem_grade (C := C) (q := q) i j))⟩

/-- The relators with trivial prefix and suffix are killed. -/
structure KillsRel (F : X → List (Bool × I) → UD RD q) : Prop where
  comm : ∀ ν i j, antiF RD q F ν (commRel C q (RD.ellOf ν) [] i j) = 0
  pos : ∀ ν i j, i ≠ j → antiF RD q F ν (posF (serreKL C q i j)) = 0
  neg : ∀ ν i j, i ≠ j → antiF RD q F ν (negF (serreKL C q i j)) = 0

theorem antiF_relator (hF : AntiMul RD q F) (lam : X) (a b : List (Bool × I)) {r : Free K I}
    {μ : X} (hr : r ∈ FX K RD μ) (h0 : antiF RD q F (lam + RD.wX b) r = 0) :
    antiF RD q F lam (ew a * r * ew b) = 0 := by
  rw [antiF_mul hF lam _ _ (ew_mem_FX RD b), antiF_mul hF _ μ _ hr, h0, zero_mul, mul_zero]

/-- **The relations of `U̇ 1_λ` are killed.** -/
theorem Lrel_le_ker_antiF (hF : AntiMul RD q F) (hK : KillsRel F) (lam : X) :
    Lrel C q (RD.ellOf lam) ≤ LinearMap.ker (antiF RD q F lam) := by
  rw [Lrel, Submodule.span_le]
  intro z hz
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  rcases hz with ⟨a, b, i, j, rfl⟩ | ⟨a, b, i, j, hij, rfl | rfl⟩
  · obtain ⟨μ, hμ⟩ := commRel_mem_FX (RD := RD) (q := q) (RD.ellOf lam) b i j
    refine antiF_relator hF lam a b hμ ?_
    rw [← List.nil_append b, ← commRel_shift RD q (lam + RD.wX b) lam [] b rfl, List.nil_append]
    exact hK.comm _ i j
  · obtain ⟨μ, hμ⟩ := posF_serreKL_mem_FX (RD := RD) (q := q) i j
    exact antiF_relator hF lam a b hμ (hK.pos _ i j hij)
  · obtain ⟨μ, hμ⟩ := negF_serreKL_mem_FX (RD := RD) (q := q) i j
    exact antiF_relator hF lam a b hμ (hK.neg _ i j hij)

variable (RD q F) in
/-- **The linear map `U̇ → U̇` extending `E_t 1_λ ↦ F λ t`.** -/
def antiU (hF : AntiMul RD q F) (hK : KillsRel F) : UD RD q →ₗ[K] UD RD q :=
  DirectSum.toModule K X _ fun lam =>
    (Lrel C q (RD.ellOf lam)).liftQ (antiF RD q F lam) (Lrel_le_ker_antiF hF hK lam)

theorem antiU_E1 (hF : AntiMul RD q F) (hK : KillsRel F) (t : List (Bool × I)) (lam : X) :
    antiU RD q F hF hK (E1 RD q t lam) = F lam t := by
  rw [antiU, E1, ofB, DirectSum.toModule_lof]
  exact antiF_ew RD q F lam t


theorem antiU_ofB_mk (hF : AntiMul RD q F) (hK : KillsRel F) (lam : X) (z : Free K I) :
    antiU RD q F hF hK (ofB RD q lam (mk RD q lam z)) = antiF RD q F lam z := by
  rw [antiU, ofB, DirectSum.toModule_lof]
  rfl

/-- **`antiU` is an anti-homomorphism**, given that `F λ t · F μ s = 0` for `μ ≠ λ + t_X`. -/
theorem antiU_mul (hF : AntiMul RD q F) (hK : KillsRel F)
    (h0 : ∀ lam mu s t, lam + RD.wX t ≠ mu → F lam t * F mu s = 0) (x y : UD RD q) :
    antiU RD q F hF hK (x * y) = antiU RD q F hF hK y * antiU RD q F hF hK x := by
  have : (mulUD RD q).compr₂ (antiU RD q F hF hK) =
      ((mulUD RD q).compl₁₂ (antiU RD q F hF hK) (antiU RD q F hF hK)).flip := by
    refine UD_lin_ext RD q fun s mu => UD_lin_ext RD q fun t lam => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, LinearMap.compl₁₂_apply, ← mul_def,
      E1_mul_E1, antiU_E1]
    split_ifs with h
    · rw [antiU_E1, hF, h]
    · rw [map_zero, h0 _ _ _ _ h]
  have e := LinearMap.congr_fun (LinearMap.congr_fun this x) y
  simpa only [LinearMap.compr₂_apply, LinearMap.flip_apply, LinearMap.compl₁₂_apply, ← mul_def]
    using e

end Anti

/-! ### Helper lemmas -/

section Helpers

theorem wX_reverse (t : List (Bool × I)) : RD.wX t.reverse = RD.wX t := by
  simp [RootDatum.wX, List.map_reverse, List.sum_reverse]

theorem ρW_eq (t : List (Bool × I)) : ρW t = (t.map flipL).reverse := rfl

theorem wX_ρW (t : List (Bool × I)) : RD.wX (ρW t) = -RD.wX t := by
  rw [ρW_eq, wX_reverse, wX_map_flipL]

/-- The commutation relation (KL III eq. (2.4)) in `U̇`:
`E_i F_j 1_μ = F_j E_i 1_μ + δ_{ij} [⟨i, μ⟩]_i 1_μ`. -/
theorem E1_comm (mu : X) (i j : I) :
    E1 RD q [(true, i), (false, j)] mu = E1 RD q [(false, j), (true, i)] mu +
      (if j = i then qbr (qi C q i) (RD.pair (RD.iY i) mu) else 0) • E1 RD q [] mu := by
  have h := mk_comm (q := q) RD mu [] [] i j
  simp only [List.nil_append, wl_nil] at h
  rw [E1, E1, E1, h, map_add, map_smul]
  rfl

theorem rev_ew (t : List (Bool × I)) : PreF.rev (ew t : Free K I) = ew t.reverse := by
  rw [ew, PreF.rev_word]; rfl

theorem rev_posF (T : PreF K I) : PreF.rev (posF T : Free K I) = posF (PreF.rev T) := by
  induction T using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | smul_word u r =>
    rw [map_smul, map_smul, map_smul, map_smul, posF_word, rev_ew, PreF.rev_word, posF_word]
    congr 2
    simp only [posW, FreeMonoid.reverse]
    rw [← List.map_reverse]
    rfl

theorem rev_negF (T : PreF K I) : PreF.rev (negF T : Free K I) = negF (PreF.rev T) := by
  induction T using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | smul_word u r =>
    rw [map_smul, map_smul, map_smul, map_smul, negF_word, rev_ew, PreF.rev_word, negF_word]
    congr 2
    simp only [negW, FreeMonoid.reverse]
    rw [← List.map_reverse]
    rfl

/-- The reversal of KL III's Serre element is `±` itself: `rev(serre) = (-1)^N serre`. -/
theorem rev_serreKL' (i j : I) :
    PreF.rev (serreKL C q i j) = ((-1 : K) ^ C.serreN i j) • serreKL C q i j := by
  rw [rev_serreKL, serreKL_eq, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

variable {RD q}

theorem mk_posF_serreKL (mu : X) {i j : I} (hij : i ≠ j) :
    mk RD q mu (posF (serreKL C q i j)) = 0 :=
  mk_eq_zero RD q mu (Submodule.subset_span
    (Or.inr ⟨[], [], i, j, hij, Or.inl (by rw [ew_nil, one_mul, mul_one])⟩))

theorem mk_negF_serreKL (mu : X) {i j : I} (hij : i ≠ j) :
    mk RD q mu (negF (serreKL C q i j)) = 0 :=
  mk_eq_zero RD q mu (Submodule.subset_span
    (Or.inr ⟨[], [], i, j, hij, Or.inr (by rw [ew_nil, one_mul, mul_one])⟩))

theorem Upsi_E1 (σK : K →+* K) (hσ : σK (q : K) = ((q⁻¹ : Kˣ) : K)) (t : List (Bool × I))
    (lam : X) : Upsi RD q σK hσ (E1 RD q t lam) = E1 RD q t lam := by
  rw [E1, Upsi_ofB, psi_mk_ew]

theorem Upsi_smul_E1 (σK : K →+* K) (hσ : σK (q : K) = ((q⁻¹ : Kˣ) : K)) (r : K)
    (t : List (Bool × I)) (lam : X) :
    Upsi RD q σK hσ (r • E1 RD q t lam) = σK r • E1 RD q t lam := by
  rw [Upsi_smul, Upsi_E1]

/-- **`ψ` is multiplicative** on `U̇`. -/
theorem Upsi_mul (σK : K →+* K) (hσ : σK (q : K) = ((q⁻¹ : Kˣ) : K)) (x y : UD RD q) :
    Upsi RD q σK hσ (x * y) = Upsi RD q σK hσ x * Upsi RD q σK hσ y := by
  induction x using E1_induction with
  | zero => simp [Upsi]
  | add x x' hx hx' => rw [add_mul, Upsi_add, hx, hx', Upsi_add, add_mul]
  | smul_E1 r s mu =>
    induction y using E1_induction with
    | zero => simp [Upsi]
    | add y y' hy hy' => rw [mul_add, Upsi_add, hy, hy', Upsi_add, mul_add]
    | smul_E1 r' t lam =>
      rw [Upsi_smul_E1, Upsi_smul_E1, smul_mul_smul_comm, smul_mul_smul_comm, E1_mul_E1]
      split_ifs
      · rw [Upsi_smul_E1, map_mul]
      · rw [smul_zero, smul_zero]; simp [Upsi]

end Helpers

/-! ### `σ` -/

section Sigma

/-- `σ` on the basis: `σ(E_t 1_λ) = E_{t^rev} 1_{-(λ + t_X)}`. -/
def sigF (lam : X) (t : List (Bool × I)) : UD RD q := E1 RD q t.reverse (-(lam + RD.wX t))

theorem sigF_antiMul : AntiMul RD q (sigF RD q) := by
  intro lam s t
  simp only [sigF, E1_mul_E1, wX_reverse, RD.wX_append, List.reverse_append]
  rw [if_pos (by abel)]
  congr 1
  abel

theorem sigF_orth (lam mu : X) (s t : List (Bool × I)) (h : lam + RD.wX t ≠ mu) :
    sigF RD q lam t * sigF RD q mu s = 0 := by
  simp only [sigF, E1_mul_E1, wX_reverse]
  rw [if_neg]
  intro h'
  refine h (neg_inj.1 ?_)
  rw [← h']
  abel

/-- `σ` on a homogeneous element of `'U 1_λ`: `σ(z 1_λ) = rev(z) 1_{-(λ+κ)}` for `z` of weight
`κ`. -/
theorem antiF_sigF_of_mem_FX (lam κ : X) {z : Free K I} (hz : z ∈ FX K RD κ) :
    antiF RD q (sigF RD q) lam z = ofB RD q (-(lam + κ)) (mk RD q _ (PreF.rev z)) := by
  refine eqOn_supp (antiF RD q (sigF RD q) lam)
    ((ofB RD q (-(lam + κ))).comp ((mk RD q _).comp PreF.rev)) ?_ z hz
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  rw [word_eq_ew, antiF_ew, LinearMap.comp_apply, LinearMap.comp_apply, rev_ew, sigF, hw]
  rfl

theorem sigF_killsRel : KillsRel (sigF RD q) where
  comm ν i j := by
    simp only [commRel, map_sub, map_smul, antiF_ew, ← ew_nil, sigF, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.singleton_append, RD.wX_nil, add_zero]
    have hw : RD.wX [(false, j), (true, i)] = RD.wX [(true, i), (false, j)] := by
      simp only [RD.wX_cons, RD.wX_nil]; abel
    rw [hw, E1_comm]
    split_ifs with h
    · subst h
      have h0 : RD.wX [(true, j), (false, j)] = 0 := by simp [RD.wX_cons]
      rw [h0, add_zero, map_neg, qbr_neg, neg_smul]
      simp only [wl_nil, RootDatum.ellOf]
      abel
    · simp
  pos ν i j hij := by
    obtain ⟨κ, hκ⟩ := posF_serreKL_mem_FX (RD := RD) (q := q) i j
    rw [antiF_sigF_of_mem_FX RD q ν κ hκ, rev_posF, rev_serreKL', map_smul, map_smul,
      mk_posF_serreKL _ hij, smul_zero, map_zero]
  neg ν i j hij := by
    obtain ⟨κ, hκ⟩ := negF_serreKL_mem_FX (RD := RD) (q := q) i j
    rw [antiF_sigF_of_mem_FX RD q ν κ hκ, rev_negF, rev_serreKL', map_smul, map_smul,
      mk_negF_serreKL _ hij, smul_zero, map_zero]

/-- **The anti-involution `σ` of `U̇`** (KL III §2.1.2–2.1.3): `ℚ(q)`-linear, `σ(E_i) = E_i`,
`σ(F_i) = F_i`, `σ(1_λ) = 1_{-λ}`, reversing products. -/
def sigmaUD : UD RD q →ₗ[K] UD RD q := antiU RD q (sigF RD q) (sigF_antiMul RD q) (sigF_killsRel RD q)

/-- `σ(E_t 1_λ) = E_{t^rev} 1_{-(λ + t_X)}`. -/
theorem sigmaUD_E1 (t : List (Bool × I)) (lam : X) :
    sigmaUD RD q (E1 RD q t lam) = E1 RD q t.reverse (-(lam + RD.wX t)) :=
  antiU_E1 _ _ t lam

/-- `σ(1_λ) = 1_{-λ}`. -/
theorem sigmaUD_one (lam : X) : sigmaUD RD q (one RD q lam) = one RD q (-lam) := by
  rw [one_eq_E1, sigmaUD_E1]
  simp [one_eq_E1]

/-- **`σ` is an anti-homomorphism**: `σ(x y) = σ(y) σ(x)`. -/
theorem sigmaUD_mul (x y : UD RD q) :
    sigmaUD RD q (x * y) = sigmaUD RD q y * sigmaUD RD q x :=
  antiU_mul _ _ (sigF_orth RD q) x y

/-- **`σ² = 1`**. -/
theorem sigmaUD_sigmaUD (x : UD RD q) : sigmaUD RD q (sigmaUD RD q x) = x := by
  have : sigmaUD RD q ∘ₗ sigmaUD RD q = LinearMap.id := by
    refine UD_lin_ext RD q fun t lam => ?_
    rw [LinearMap.comp_apply, sigmaUD_E1, sigmaUD_E1, List.reverse_reverse, wX_reverse,
      LinearMap.id_apply]
    congr 1
    abel
  exact LinearMap.congr_fun this x

/-- **`σω = ωσ`**. -/
theorem sigmaUD_Uomega (x : UD RD q) :
    sigmaUD RD q (Uomega RD q x) = Uomega RD q (sigmaUD RD q x) := by
  have : sigmaUD RD q ∘ₗ Uomega RD q = Uomega RD q ∘ₗ sigmaUD RD q := by
    refine UD_lin_ext RD q fun t lam => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Uomega_E1, sigmaUD_E1, sigmaUD_E1, Uomega_E1,
      wX_map_flipL, List.map_reverse]
    congr 1
    abel
  exact LinearMap.congr_fun this x

variable (σK : K →+* K) (hσ : σK (q : K) = ((q⁻¹ : Kˣ) : K))

/-- **`σψ = ψσ`**. -/
theorem sigmaUD_Upsi (x : UD RD q) :
    sigmaUD RD q (Upsi RD q σK hσ x) = Upsi RD q σK hσ (sigmaUD RD q x) := by
  induction x using E1_induction with
  | zero => simp [Upsi]
  | add x y hx hy => rw [Upsi_add, map_add, hx, hy, map_add, Upsi_add]
  | smul_E1 r t lam =>
    rw [Upsi_smul_E1, map_smul, map_smul, sigmaUD_E1, Upsi_smul_E1]


theorem rev_dpE (x : Bool × I × ℕ) : PreF.rev (dpE C q x) = dpE C q x := by
  rw [dpE, map_smul, rev_ew, List.reverse_replicate]

theorem rev_dpW (d : List (Bool × I × ℕ)) : PreF.rev (dpW C q d) = dpW C q d.reverse := by
  induction d with
  | nil => simp [dpW, PreF.rev_one]
  | cons x d ih =>
    have h1 : dpW C q (x :: d) = dpE C q x * dpW C q d := by simp [dpW]
    have h2 : dpW C q [x] = dpE C q x := by simp [dpW]
    rw [h1, PreF.rev_mul, ih, rev_dpE, List.reverse_cons, dpW_append, h2]

/-- **`σ` on divided powers**: `σ(E_d 1_λ) = E_{d^rev} 1_{-(λ + |d|_X)}` for a dpss `d`
(`E_d = E_{ε₁i₁}^{(a₁)} ⋯ E_{εₘiₘ}^{(aₘ)}`). -/
theorem sigmaUD_E1dp (d : List (Bool × I × ℕ)) (lam : X) :
    sigmaUD RD q (E1dp RD q d lam) = E1dp RD q d.reverse (-(lam + wdp RD d)) := by
  rw [E1dp, sigmaUD, antiU_ofB_mk, antiF_sigF_of_mem_FX RD q lam _ (dpW_mem_FX RD q d), rev_dpW]
  rfl

/-- `σ` preserves the integral form `_𝒜 U̇`. -/
theorem sigmaUD_mem_AUD {x : UD RD q} (hx : x ∈ AUD RD q) : sigmaUD RD q x ∈ AUD RD q := by
  induction hx using NonUnitalSubring.closure_induction with
  | mem x hx =>
    obtain ⟨n, d, lam, rfl⟩ := hx
    rw [map_smul, sigmaUD_E1dp]
    exact gen_mem_AUD RD q n _ _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [sigmaUD_mul]; exact mul_mem hy hx

end Sigma

/-! ### `ρ̄` -/

section Rhobar

/-- The exponent of `q` in `ρ̄(E_t 1_λ) = q^{rexp λ t} E_{ρW t} 1_{λ + t_X}`:
`rexp λ (l t) = rexp λ t - d_i (1 + ε ⟨i, λ + t_X⟩)` for `l = (ε, i)`. -/
def rexp (lam : X) : List (Bool × I) → ℤ
  | [] => 0
  | l :: t => rexp lam t - di C l.2 * (1 + sgn l.1 * RD.pair (RD.iY l.2) (lam + RD.wX t))

@[simp] theorem rexp_nil (lam : X) : rexp RD lam [] = 0 := rfl

theorem rexp_cons (lam : X) (l : Bool × I) (t : List (Bool × I)) :
    rexp RD lam (l :: t) =
      rexp RD lam t - di C l.2 * (1 + sgn l.1 * RD.pair (RD.iY l.2) (lam + RD.wX t)) := rfl

theorem rexp_append (lam : X) (s t : List (Bool × I)) :
    rexp RD lam (s ++ t) = rexp RD lam t + rexp RD (lam + RD.wX t) s := by
  induction s with
  | nil => simp
  | cons l s ih =>
    rw [List.cons_append, rexp_cons, rexp_cons, ih, RD.wX_append,
      show lam + (RD.wX s + RD.wX t) = lam + RD.wX t + RD.wX s by abel]
    ring

theorem wX_perm {t t' : List (Bool × I)} (h : t.Perm t') : RD.wX t = RD.wX t' := by
  unfold RootDatum.wX
  exact (h.map _).sum_eq

/-- `rexp` is invariant under permutations: `d_i ⟨i, j_X⟩ = i·j` is symmetric. -/
theorem rexp_perm (lam : X) {t t' : List (Bool × I)} (h : t.Perm t') :
    rexp RD lam t = rexp RD lam t' := by
  induction h with
  | nil => rfl
  | cons x h ih => rw [rexp_cons, rexp_cons, ih, wX_perm RD h]
  | swap x y l =>
    obtain ⟨b1, i1⟩ := x
    obtain ⟨b2, i2⟩ := y
    simp only [rexp_cons, RD.wX_cons, map_add, map_zsmul, smul_eq_mul, RD.pair_iY_iX_eq_A]
    linear_combination (sgn b1 * sgn b2) * di_mul_A_comm C i1 i2
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- `ρ̄` on the basis: `ρ̄(E_t 1_λ) = q^{rexp λ t} E_{ρW t} 1_{λ + t_X}`. -/
def rhoF (lam : X) (t : List (Bool × I)) : UD RD q :=
  qp q (rexp RD lam t) • E1 RD q (ρW t) (lam + RD.wX t)

theorem rhoF_antiMul : AntiMul RD q (rhoF RD q) := by
  intro lam s t
  simp only [rhoF, smul_mul_smul_comm, E1_mul_E1, wX_ρW, RD.wX_append, ρW_append, rexp_append,
    qp_add]
  rw [if_pos (by abel)]
  congr 2
  abel

theorem rhoF_orth (lam mu : X) (s t : List (Bool × I)) (h : lam + RD.wX t ≠ mu) :
    rhoF RD q lam t * rhoF RD q mu s = 0 := by
  simp only [rhoF, smul_mul_smul_comm, E1_mul_E1, wX_ρW]
  rw [if_neg, smul_zero]
  intro h'
  refine h ?_
  rw [← h']
  abel

theorem perm_of_wt {u : FreeMonoid I} {P : Multiset I} (hu : QuantumGroup.wt u = P) :
    u.toList.Perm P.toList :=
  Multiset.coe_eq_coe.1 (hu.trans (Multiset.coe_toList P).symm)

/-- `ρ̄` on `x⁺ 1_λ` for `x ∈ 'f` of weight `P`: `ρ̄(x⁺ 1_λ) = q^{rexp} rev(x)⁻ 1_{λ + P}`. -/
theorem antiF_rhoF_posF (lam : X) (P : Multiset I) {z : PreF K I} (hz : z ∈ grade K P) :
    antiF RD q (rhoF RD q) lam (posF z) =
      qp q (rexp RD lam (posW P.toList)) • ofB RD q (lam + RD.wX (posW P.toList))
        (mk RD q _ (negF (PreF.rev z))) := by
  refine eqOn_supp ((antiF RD q (rhoF RD q) lam).comp posF.toLinearMap)
    (qp q (rexp RD lam (posW P.toList)) • (ofB RD q (lam + RD.wX (posW P.toList))).comp
      ((mk RD q _).comp (negF.toLinearMap.comp PreF.rev))) ?_ z hz
  intro u hu
  simp only [Set.mem_setOf_eq] at hu
  have hp : (posW u.toList).Perm (posW P.toList) := (perm_of_wt hu).map _
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.smul_apply, posF_word,
    antiF_ew, rhoF, PreF.rev_word, negF_word, rexp_perm RD lam hp, wX_perm RD hp, ρW_posW]
  rfl

theorem antiF_rhoF_negF (lam : X) (P : Multiset I) {z : PreF K I} (hz : z ∈ grade K P) :
    antiF RD q (rhoF RD q) lam (negF z) =
      qp q (rexp RD lam (negW P.toList)) • ofB RD q (lam + RD.wX (negW P.toList))
        (mk RD q _ (posF (PreF.rev z))) := by
  refine eqOn_supp ((antiF RD q (rhoF RD q) lam).comp negF.toLinearMap)
    (qp q (rexp RD lam (negW P.toList)) • (ofB RD q (lam + RD.wX (negW P.toList))).comp
      ((mk RD q _).comp (posF.toLinearMap.comp PreF.rev))) ?_ z hz
  intro u hu
  simp only [Set.mem_setOf_eq] at hu
  have hp : (negW u.toList).Perm (negW P.toList) := (perm_of_wt hu).map _
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.smul_apply, negF_word,
    antiF_ew, rhoF, PreF.rev_word, posF_word, rexp_perm RD lam hp, wX_perm RD hp, ρW_negW]
  rfl

theorem rexp_EF (ν : X) (i : I) : rexp RD ν [(true, i), (false, i)] = 0 := by
  simp only [rexp_cons, rexp_nil, RD.wX_cons, RD.wX_nil, map_add, map_zsmul, smul_eq_mul,
    RD.pair_iY_iX_self, sgn_true, sgn_false, map_zero]
  ring

theorem rhoF_killsRel : KillsRel (rhoF RD q) where
  comm ν i j := by
    have he : rexp RD ν [(false, j), (true, i)] = rexp RD ν [(true, i), (false, j)] :=
      rexp_perm RD ν (List.Perm.swap _ _ [])
    have hw : RD.wX [(false, j), (true, i)] = RD.wX [(true, i), (false, j)] :=
      wX_perm RD (List.Perm.swap _ _ [])
    have e1 : ρW [(true, i), (false, j)] = [(true, j), (false, i)] := rfl
    have e2 : ρW [(false, j), (true, i)] = [(false, i), (true, j)] := rfl
    simp only [commRel, map_sub, map_smul, antiF_ew, ← ew_nil, rhoF, he, hw, e1, e2, rexp_nil,
      qp_zero, one_smul, ρW_nil, RD.wX_nil, add_zero, wl_nil]
    rw [E1_comm RD q _ j i]
    split_ifs with h h' h'
    · subst h
      have h0 : RD.wX [(true, i), (false, i)] = 0 := by simp [RD.wX_cons]
      rw [rexp_EF, h0, add_zero]
      simp only [RootDatum.ellOf, qp_zero, one_smul]
      abel
    · exact absurd h.symm h'
    · exact absurd h'.symm h
    · simp
  pos ν i j hij := by
    rw [antiF_rhoF_posF RD q ν _ (serreKL_mem_grade (C := C) (q := q) i j), rev_serreKL',
      map_smul, map_smul, mk_negF_serreKL _ hij, smul_zero, map_zero, smul_zero]
  neg ν i j hij := by
    rw [antiF_rhoF_negF RD q ν _ (serreKL_mem_grade (C := C) (q := q) i j), rev_serreKL',
      map_smul, map_smul, mk_posF_serreKL _ hij, smul_zero, map_zero, smul_zero]

/-- **The linear anti-involution `ρ̄ = ψρψ` of `U̇`** (KL III §2.1.2–2.1.3):
`ρ̄(E_i) = q_i⁻¹ K̃_{-i} F_i`, `ρ̄(F_i) = q_i⁻¹ K̃_i E_i`, `ρ̄(1_λ) = 1_λ`, reversing products. -/
def rhobarUD : UD RD q →ₗ[K] UD RD q :=
  antiU RD q (rhoF RD q) (rhoF_antiMul RD q) (rhoF_killsRel RD q)

/-- `ρ̄(E_t 1_λ) = q^{rexp λ t} E_{ρW t} 1_{λ + t_X}`. -/
theorem rhobarUD_E1 (t : List (Bool × I)) (lam : X) :
    rhobarUD RD q (E1 RD q t lam) = qp q (rexp RD lam t) • E1 RD q (ρW t) (lam + RD.wX t) :=
  antiU_E1 _ _ t lam

/-- `ρ̄(1_λ) = 1_λ`. -/
theorem rhobarUD_one (lam : X) : rhobarUD RD q (one RD q lam) = one RD q lam := by
  rw [one_eq_E1, rhobarUD_E1]
  simp [one_eq_E1]

/-- **`ρ̄` is an anti-homomorphism**. -/
theorem rhobarUD_mul (x y : UD RD q) :
    rhobarUD RD q (x * y) = rhobarUD RD q y * rhobarUD RD q x :=
  antiU_mul _ _ (rhoF_orth RD q) x y

theorem qi_zpow_eq_qp (i : I) (n : ℤ) :
    (((qi C q i) ^ n : Kˣ) : K) = qp q (di C i * n) := by
  rw [qi, ← zpow_mul]; rfl

/-- **`ρ̄(E_i 1_λ) = q_i^{-1-⟨i,λ⟩} F_i 1_{λ+i_X}`**. -/
theorem rhobarUD_E (i : I) (lam : X) :
    rhobarUD RD q (E1 RD q [(true, i)] lam) =
      (((qi C q i) ^ (-1 - RD.pair (RD.iY i) lam) : Kˣ) : K) • E1 RD q [(false, i)] (lam + RD.iX i) := by
  rw [rhobarUD_E1, qi_zpow_eq_qp]
  simp only [rexp_cons, rexp_nil, RD.wX_cons, RD.wX_nil, add_zero, sgn_true, one_mul, one_smul]
  congr 1
  congr 1
  ring

/-- **`ρ̄(F_i 1_{λ+i_X}) = q_i^{1+⟨i,λ⟩} E_i 1_λ`**. -/
theorem rhobarUD_F (i : I) (lam : X) :
    rhobarUD RD q (E1 RD q [(false, i)] (lam + RD.iX i)) =
      (((qi C q i) ^ (1 + RD.pair (RD.iY i) lam) : Kˣ) : K) • E1 RD q [(true, i)] lam := by
  rw [rhobarUD_E1, qi_zpow_eq_qp]
  simp only [rexp_cons, rexp_nil, RD.wX_cons, RD.wX_nil, add_zero, sgn_false, neg_one_smul,
    add_neg_cancel_right, map_add, RD.pair_iY_iX_self]
  congr 2
  ring

theorem rexp_ρW (lam : X) (t : List (Bool × I)) :
    rexp RD lam t + rexp RD (lam + RD.wX t) (ρW t) = 0 := by
  induction t generalizing lam with
  | nil => simp
  | cons l t ih =>
    obtain ⟨b, i⟩ := l
    rw [ρW_cons, rexp_append, rexp_cons, RD.wX_cons, RD.wX_cons, RD.wX_nil, add_zero, sgn_not,
      rexp_cons, rexp_nil,
      show lam + (sgn b • RD.iX i + RD.wX t) + -sgn b • RD.iX i = lam + RD.wX t by
        rw [neg_smul]; abel]
    have := ih lam
    simp only [map_add, map_zsmul, smul_eq_mul, RD.pair_iY_iX_self, RD.wX_nil, add_zero,
      sgn_not] at this ⊢
    linear_combination this + 2 * di C i * sgn_mul_self b

/-- **`ρ̄² = 1`**. -/
theorem rhobarUD_rhobarUD (x : UD RD q) : rhobarUD RD q (rhobarUD RD q x) = x := by
  have : rhobarUD RD q ∘ₗ rhobarUD RD q = LinearMap.id := by
    refine UD_lin_ext RD q fun t lam => ?_
    rw [LinearMap.comp_apply, rhobarUD_E1, map_smul, rhobarUD_E1, smul_smul, ← qp_add, rexp_ρW,
      qp_zero, one_smul, ρW_ρW, wX_ρW, LinearMap.id_apply, add_neg_cancel_right]
  exact LinearMap.congr_fun this x

theorem rexp_flip (lam : X) (t : List (Bool × I)) :
    rexp RD (-lam) (t.map flipL) = rexp RD lam t := by
  induction t with
  | nil => rfl
  | cons l t ih =>
    rw [List.map_cons, rexp_cons, rexp_cons, ih, wX_map_flipL]
    simp only [flipL, sgn_not, ← neg_add, map_neg]
    ring

theorem ρW_map_flipL (t : List (Bool × I)) : ρW (t.map flipL) = (ρW t).map flipL := by
  rw [ρW_eq, ρW_eq, List.map_reverse]

/-- **`ωρ̄ = ρ̄ω`**. -/
theorem Uomega_rhobarUD (x : UD RD q) :
    Uomega RD q (rhobarUD RD q x) = rhobarUD RD q (Uomega RD q x) := by
  have : Uomega RD q ∘ₗ rhobarUD RD q = rhobarUD RD q ∘ₗ Uomega RD q := by
    refine UD_lin_ext RD q fun t lam => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, rhobarUD_E1, map_smul, Uomega_E1, Uomega_E1,
      rhobarUD_E1, rexp_flip, ρW_map_flipL, wX_map_flipL, neg_add]
  exact LinearMap.congr_fun this x

/-- `ρ̄ = ω σ` up to the powers `q^{rexp}`: `ρ̄(E_t 1_λ) = q^{rexp λ t} ω(σ(E_t 1_λ))`. -/
theorem rhobarUD_E1_eq_omega_sigma (t : List (Bool × I)) (lam : X) :
    rhobarUD RD q (E1 RD q t lam) =
      qp q (rexp RD lam t) • Uomega RD q (sigmaUD RD q (E1 RD q t lam)) := by
  rw [rhobarUD_E1, sigmaUD_E1, Uomega_E1, neg_neg, ρW_eq, List.map_reverse]

end Rhobar

/-! ### `τ = ψρ = ρ̄ψ` -/

section Tau

variable (σK : K →+* K) (hσ : σK (q : K) = ((q⁻¹ : Kˣ) : K))

theorem σK_qp (hσ : σK (q : K) = ((q⁻¹ : Kˣ) : K)) (n : ℤ) : σK (qp q n) = qp q (-n) :=
  PreF.σ_zpow hσ n

/-- **The antilinear anti-automorphism `τ = ψρ` of `U̇`** (KL III §2.1.2–2.1.3):
`τ(E_i) = q_i⁻¹ K̃_{-i} F_i`, `τ(F_i) = q_i⁻¹ K̃_i E_i`, `τ(1_λ) = 1_λ`, `τ(f x) = f̄ τ(x)`.
Since `ψ² = 1` and `ρ̄ = ψρψ`, `τ = ρ̄ψ`. -/
def tauUD (x : UD RD q) : UD RD q := rhobarUD RD q (Upsi RD q σK hσ x)

/-- `τ(E_t 1_λ) = q^{rexp λ t} E_{ρW t} 1_{λ + t_X}`. -/
theorem tauUD_E1 (t : List (Bool × I)) (lam : X) :
    tauUD RD q σK hσ (E1 RD q t lam) = qp q (rexp RD lam t) • E1 RD q (ρW t) (lam + RD.wX t) := by
  rw [tauUD, Upsi_E1, rhobarUD_E1]

theorem tauUD_add (x y : UD RD q) :
    tauUD RD q σK hσ (x + y) = tauUD RD q σK hσ x + tauUD RD q σK hσ y := by
  rw [tauUD, Upsi_add, map_add]; rfl

/-- **`τ` is antilinear**: `τ(f x) = f̄ τ(x)`. -/
theorem tauUD_smul (r : K) (x : UD RD q) :
    tauUD RD q σK hσ (r • x) = σK r • tauUD RD q σK hσ x := by
  rw [tauUD, Upsi_smul, map_smul]; rfl

/-- **`τ` is an anti-homomorphism**: `τ(x y) = τ(y) τ(x)`. -/
theorem tauUD_mul (x y : UD RD q) :
    tauUD RD q σK hσ (x * y) = tauUD RD q σK hσ y * tauUD RD q σK hσ x := by
  rw [tauUD, Upsi_mul, rhobarUD_mul]; rfl

/-- `τ(1_λ) = 1_λ`. -/
theorem tauUD_one (lam : X) : tauUD RD q σK hσ (one RD q lam) = one RD q lam := by
  rw [tauUD, one_eq_E1, Upsi_E1, ← one_eq_E1, rhobarUD_one]

/-- **KL III §2.1.3**: `τ(1_{λ+i_X} E_i 1_λ) = q_i^{-1-⟨i,λ⟩} 1_λ F_i 1_{λ+i_X}`. -/
theorem tauUD_E (i : I) (lam : X) :
    tauUD RD q σK hσ (E1 RD q [(true, i)] lam) =
      (((qi C q i) ^ (-1 - RD.pair (RD.iY i) lam) : Kˣ) : K) • E1 RD q [(false, i)] (lam + RD.iX i) := by
  rw [tauUD, Upsi_E1, rhobarUD_E]

/-- **KL III §2.1.3**: `τ(1_λ F_i 1_{λ+i_X}) = q_i^{1+⟨i,λ⟩} 1_{λ+i_X} E_i 1_λ`. -/
theorem tauUD_F (i : I) (lam : X) :
    tauUD RD q σK hσ (E1 RD q [(false, i)] (lam + RD.iX i)) =
      (((qi C q i) ^ (1 + RD.pair (RD.iY i) lam) : Kˣ) : K) • E1 RD q [(true, i)] lam := by
  rw [tauUD, Upsi_E1, rhobarUD_F]


/-- **The linear anti-involution `ρ = ψρ̄ψ` of `U̇`** (KL III §2.1.2: `ρ(E_i) = q_i K̃_i F_i`,
`ρ(F_i) = q_i K̃_{-i} E_i`, `ρ(1_λ) = 1_λ`). -/
def rhoUD (x : UD RD q) : UD RD q := Upsi RD q σK hσ (rhobarUD RD q (Upsi RD q σK hσ x))

/-- `ρ(E_t 1_λ) = q^{-rexp λ t} E_{ρW t} 1_{λ + t_X}`; e.g. `ρ(E_i 1_λ) = q_i^{1+⟨i,λ⟩} F_i 1_{λ+i_X}`. -/
theorem rhoUD_E1 (t : List (Bool × I)) (lam : X) :
    rhoUD RD q σK hσ (E1 RD q t lam) = qp q (-rexp RD lam t) • E1 RD q (ρW t) (lam + RD.wX t) := by
  rw [rhoUD, Upsi_E1, rhobarUD_E1, Upsi_smul_E1, σK_qp q σK hσ]

/-- `ρ` is linear. -/
theorem rhoUD_smul (hσσ : ∀ a, σK (σK a) = a) (r : K) (x : UD RD q) :
    rhoUD RD q σK hσ (r • x) = r • rhoUD RD q σK hσ x := by
  rw [rhoUD, Upsi_smul, map_smul, Upsi_smul, hσσ]
  rfl

/-- `ρ` is an anti-homomorphism. -/
theorem rhoUD_mul (x y : UD RD q) :
    rhoUD RD q σK hσ (x * y) = rhoUD RD q σK hσ y * rhoUD RD q σK hσ x := by
  rw [rhoUD, Upsi_mul, rhobarUD_mul, Upsi_mul]; rfl

/-- `ρ² = 1`. -/
theorem rhoUD_rhoUD (hσσ : ∀ a, σK (σK a) = a) (x : UD RD q) :
    rhoUD RD q σK hσ (rhoUD RD q σK hσ x) = x := by
  rw [rhoUD, rhoUD, Upsi_Upsi RD q σK hσ hσσ, rhobarUD_rhobarUD, Upsi_Upsi RD q σK hσ hσσ]

/-- **`τ = ψρ`** (KL III §2.1.2, the definition of `τ`). -/
theorem tauUD_eq_psi_rho (hσσ : ∀ a, σK (σK a) = a) (x : UD RD q) :
    tauUD RD q σK hσ x = Upsi RD q σK hσ (rhoUD RD q σK hσ x) := by
  rw [rhoUD, Upsi_Upsi RD q σK hσ hσσ]; rfl

/-- **`ρ̄ = ψρψ`** (KL III §2.1.2). -/
theorem rhobarUD_eq_psi_rho_psi (hσσ : ∀ a, σK (σK a) = a) (x : UD RD q) :
    rhobarUD RD q x = Upsi RD q σK hσ (rhoUD RD q σK hσ (Upsi RD q σK hσ x)) := by
  rw [rhoUD, Upsi_Upsi RD q σK hσ hσσ, Upsi_Upsi RD q σK hσ hσσ]

/-- The inverse `τ⁻¹ = ψρ̄` of `τ`. -/
def tauInv (x : UD RD q) : UD RD q := Upsi RD q σK hσ (rhobarUD RD q x)

/-- `τ τ⁻¹ = 1`. -/
theorem tauUD_tauInv (hσσ : ∀ a, σK (σK a) = a) (x : UD RD q) : tauUD RD q σK hσ (tauInv RD q σK hσ x) = x := by
  rw [tauUD, tauInv, Upsi_Upsi RD q σK hσ hσσ, rhobarUD_rhobarUD]

/-- `τ⁻¹ τ = 1`. -/
theorem tauInv_tauUD (hσσ : ∀ a, σK (σK a) = a) (x : UD RD q) : tauInv RD q σK hσ (tauUD RD q σK hσ x) = x := by
  rw [tauUD, tauInv, rhobarUD_rhobarUD, Upsi_Upsi RD q σK hσ hσσ]

/-- **`τ` is bijective** (an anti-automorphism of `U̇`). -/
theorem tauUD_bijective (hσσ : ∀ a, σK (σK a) = a) : Function.Bijective (tauUD RD q σK hσ) :=
  Function.bijective_iff_has_inverse.2 ⟨tauInv RD q σK hσ, tauInv_tauUD RD q σK hσ hσσ,
    tauUD_tauInv RD q σK hσ hσσ⟩

/-- `ωψ = ψω`. -/
theorem Uomega_Upsi (x : UD RD q) :
    Uomega RD q (Upsi RD q σK hσ x) = Upsi RD q σK hσ (Uomega RD q x) := by
  induction x using E1_induction with
  | zero => simp [Upsi]
  | add x y hx hy => rw [Upsi_add, map_add, hx, hy, map_add, Upsi_add]
  | smul_E1 r t lam => rw [Upsi_smul_E1, map_smul, map_smul, Uomega_E1, Upsi_smul_E1]

/-- **`ωτ = τω`**. -/
theorem Uomega_tauUD (x : UD RD q) :
    Uomega RD q (tauUD RD q σK hσ x) = tauUD RD q σK hσ (Uomega RD q x) := by
  rw [tauUD, tauUD, Uomega_rhobarUD, Uomega_Upsi]

theorem rexp_reverse (lam : X) (t : List (Bool × I)) :
    rexp RD (-(lam + RD.wX t)) t.reverse = -rexp RD lam t := by
  induction t generalizing lam with
  | nil => simp
  | cons l t ih =>
    obtain ⟨b, i⟩ := l
    rw [List.reverse_cons, rexp_append, RD.wX_cons, RD.wX_cons, RD.wX_nil, add_zero,
      show -(lam + (sgn b • RD.iX i + RD.wX t)) + sgn b • RD.iX i = -(lam + RD.wX t) by abel,
      ih, rexp_cons, rexp_cons, rexp_nil, RD.wX_nil, add_zero,
      show -(lam + (sgn b • RD.iX i + RD.wX t)) = -(lam + RD.wX t) - sgn b • RD.iX i by abel]
    simp only [map_sub, map_neg, map_zsmul, smul_eq_mul, RD.pair_iY_iX_self]
    linear_combination (2 * di C i) * sgn_mul_self b


/-- **`στσ = τ⁻¹`**. -/
theorem sigmaUD_tauUD_sigmaUD (x : UD RD q) :
    sigmaUD RD q (tauUD RD q σK hσ (sigmaUD RD q x)) = tauInv RD q σK hσ x := by
  induction x using E1_induction with
  | zero => simp [tauUD, tauInv, Upsi]
  | add x y hx hy =>
    rw [map_add, tauUD_add, map_add, hx, hy]
    simp only [tauInv, map_add, Upsi_add]
  | smul_E1 r t lam =>
    rw [map_smul, tauUD_smul, sigmaUD_E1, tauUD_E1, map_smul, map_smul, sigmaUD_E1, smul_smul,
      tauInv, map_smul, rhobarUD_E1, smul_smul, Upsi_smul_E1, map_mul, σK_qp q σK hσ,
      rexp_reverse]
    have e : (ρW t.reverse).reverse = ρW t := by
      rw [ρW_eq, ρW_eq, List.map_reverse, List.reverse_reverse]
    rw [e, wX_ρW, wX_reverse]
    congr 2
    abel

end Tau

/-! ### `ρ̄` and `τ` on divided powers; `τ(_𝒜 U̇) ⊆ _𝒜 U̇` -/

section Divided

/-- The signed sequence `(ε₁i₁)^{a₁} ⋯ (εₘiₘ)^{aₘ}` underlying a dpss. -/
def dpSeq (d : List (Bool × I × ℕ)) : List (Bool × I) :=
  (d.map fun x => List.replicate x.2.2 (x.1, x.2.1)).flatten

variable (C) in
/-- `∏_r [a_r]_{i_r}!` for a dpss. -/
def dpFacK (d : List (Bool × I × ℕ)) : K := (d.map fun x => qfact (qi C q x.2.1) x.2.2).prod

/-- The dpss of `ρ̄(E_d)`: reversed, all signs flipped. -/
def rhod (d : List (Bool × I × ℕ)) : List (Bool × I × ℕ) :=
  (d.map fun x => (!x.1, x.2.1, x.2.2)).reverse

theorem dpW_eq_smul_ew (d : List (Bool × I × ℕ)) :
    dpW C q d = (dpFacK C q d)⁻¹ • (ew (dpSeq d) : Free K I) := by
  induction d with
  | nil => simp [dpW, dpFacK, dpSeq]
  | cons x d ih =>
    have h1 : dpW C q (x :: d) = dpE C q x * dpW C q d := by simp [dpW]
    rw [h1, ih, dpE, smul_mul_smul_comm, ← ew_append]
    simp [dpFacK, dpSeq, mul_inv, mul_comm]

theorem dpSeq_rhod (d : List (Bool × I × ℕ)) : dpSeq (rhod d) = ρW (dpSeq d) := by
  induction d with
  | nil => rfl
  | cons x d ih =>
    simp only [rhod, dpSeq, List.map_cons, List.reverse_cons, List.map_append, List.map_reverse,
      List.flatten_append, List.flatten_cons, ρW_append] at ih ⊢
    rw [ih]
    simp [ρW, List.map_replicate]

theorem dpFacK_rhod (d : List (Bool × I × ℕ)) : dpFacK C q (rhod d) = dpFacK C q d := by
  simp [dpFacK, rhod, List.map_reverse, List.prod_reverse, Function.comp_def]

theorem wX_dpSeq (d : List (Bool × I × ℕ)) : RD.wX (dpSeq d) = wdp RD d := by
  induction d with
  | nil => rfl
  | cons x d ih =>
    simp only [dpSeq, List.map_cons, List.flatten_cons, RD.wX_append] at ih ⊢
    rw [ih, wX_replicate]
    simp [wdp]

theorem E1dp_eq (d : List (Bool × I × ℕ)) (lam : X) :
    E1dp RD q d lam = (dpFacK C q d)⁻¹ • E1 RD q (dpSeq d) lam := by
  rw [E1dp, dpW_eq_smul_ew, map_smul, map_smul]
  rfl

/-- **`ρ̄` on divided powers**: `ρ̄(E_d 1_λ) = q^{rexp λ d} E_{ρ̄ d} 1_{λ + |d|_X}`. -/
theorem rhobarUD_E1dp (d : List (Bool × I × ℕ)) (lam : X) :
    rhobarUD RD q (E1dp RD q d lam) =
      qp q (rexp RD lam (dpSeq d)) • E1dp RD q (rhod d) (lam + wdp RD d) := by
  rw [E1dp_eq, map_smul, rhobarUD_E1, E1dp_eq, dpSeq_rhod, dpFacK_rhod, wX_dpSeq, smul_comm]

variable (σK : K →+* K) (hσ : σK (q : K) = ((q⁻¹ : Kˣ) : K))

theorem σK_dpFacK (hσ : σK (q : K) = ((q⁻¹ : Kˣ) : K)) (d : List (Bool × I × ℕ)) :
    σK (dpFacK C q d) = dpFacK C q d := by
  simp only [dpFacK, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  exact PreF.σ_qfact σK hσ (di C x.2.1) x.2.2

/-- `ψ(E_d 1_λ) = E_d 1_λ`. -/
theorem Upsi_E1dp (d : List (Bool × I × ℕ)) (lam : X) :
    Upsi RD q σK hσ (E1dp RD q d lam) = E1dp RD q d lam := by
  rw [E1dp_eq, Upsi_smul_E1, map_inv₀, σK_dpFacK (C := C) q σK hσ]

/-- **`τ` on divided powers**: `τ(E_d 1_λ) = q^{rexp λ d} E_{ρ̄ d} 1_{λ + |d|_X}`; e.g.
`τ(E_i^{(a)} 1_λ) = q^{…} F_i^{(a)} 1_{λ + a i_X}`. -/
theorem tauUD_E1dp (d : List (Bool × I × ℕ)) (lam : X) :
    tauUD RD q σK hσ (E1dp RD q d lam) =
      qp q (rexp RD lam (dpSeq d)) • E1dp RD q (rhod d) (lam + wdp RD d) := by
  rw [tauUD, Upsi_E1dp, rhobarUD_E1dp]

/-- **`τ` preserves the integral form `_𝒜 U̇`** (KL III §2.1.3: "Restricting to the
`ℤ[q, q⁻¹]`-subalgebra `_𝒜 U̇` […] we obtain an algebra antiautomorphism `τ : _𝒜 U̇ → _𝒜 U̇`"). -/
theorem tauUD_mem_AUD {x : UD RD q} (hx : x ∈ AUD RD q) : tauUD RD q σK hσ x ∈ AUD RD q := by
  induction hx using NonUnitalSubring.closure_induction with
  | mem x hx =>
    obtain ⟨n, d, lam, rfl⟩ := hx
    rw [tauUD_smul, tauUD_E1dp, σK_qp q σK hσ, smul_smul, ← qp_add]
    exact gen_mem_AUD RD q _ _ _
  | zero => simp only [tauUD, Upsi, DFinsupp.mapRange_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [tauUD_add]; exact add_mem hx hy
  | neg x _ hx =>
    have : tauUD RD q σK hσ (-x) = -tauUD RD q σK hσ x := by
      rw [← neg_one_smul K x, tauUD_smul, map_neg, map_one, neg_one_smul]
    rw [this]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [tauUD_mul]; exact mul_mem hy hx

/-- `ρ̄` preserves the integral form `_𝒜 U̇`. -/
theorem rhobarUD_mem_AUD {x : UD RD q} (hx : x ∈ AUD RD q) : rhobarUD RD q x ∈ AUD RD q := by
  induction hx using NonUnitalSubring.closure_induction with
  | mem x hx =>
    obtain ⟨n, d, lam, rfl⟩ := hx
    rw [map_smul, rhobarUD_E1dp, smul_smul, ← qp_add]
    exact gen_mem_AUD RD q _ _ _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [rhobarUD_mul]; exact mul_mem hy hx

end Divided

end UDot

end Categorification.QuantumGroup

end
