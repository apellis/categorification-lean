/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.GammaFlagBubble
import Categorification.Flag.GammaCyclicSame

/-!
# The decompositions of `1_{E F 1_λ}` and `1_{F E 1_λ}` under `Γ_N`

KL III, arXiv:0807.3250v1, Definition 3.1, relation `eq_ident_decomp`
(`Categorification.KL3.Diagram.Rel.decompEF`, `decompFE`; in normal form
`Categorification.KL3.Diagram.dg_decompEF`, `dg_decompFE`) and Proposition 6.3 (the
`sl₂`-relations hold for `Γ_N`, by Lauda's computation, arXiv:0803.3652).

On the path model, for a composition `r` (the region `λ`), a colour `i` and
`n = ⟨i, λ⟩ = r_i - r_{i+1}`, pointwise on `Γ_N` of the 1-morphism with an arbitrary suffix `Y`:

* `decompEF_W` : on `E_i F_i Y`, when also `F_i E_i 1_λ ≠ 0`,
  `1 = -crossr ∘ crossl + ∑_{f=0}^{n-1} ∑_{g=0}^{f}` (cup with `n - 1 - f` dots on `F_i`)
  `∘ Γ(ccwL (-n - 1 + g)) ∘` (`f - g` dots on `E_i`, then cap) (`dcW`);
* `decompEF_W_top` : the same when `F_i E_i 1_λ = 0` (`r_{i+1} = 0`), without the crossing term;
* `decompFE_W`, `decompFE_W_top` : the mirror statements on `F_i E_i Y`, with `Γ(cwL (n - 1 + g))`
  (`dcWFE`).

When the 1-morphism itself is zero in the path model there is nothing to prove. The bubbles are
`Γ_N` of the labelled bubbles `ccwL`, `cwL` of Definition 3.1, real or fake (`ccwLH`, `cwLH`).

The proof: both sides agree at `1 ⊗ 1 ⊗ y` (`crosslW_same_one`, `crossrW_same_one`) and have the
same dot slides on both strands (`ext_two`). The sideways crossings of equal colours do not commute
with the dots; the defect is the cup-cap composite (`crosslW_same_dotE`, …), and the cap after
`crossl` (resp. `crossr`) and the cup before `crossr` (resp. `crossl`) are curls
(`capFEW_crosslW`, `crossrW_cupFEW`, `capEFW_crossrW`, `crosslW_cupEFW`), evaluated by the curl
relations (`curlLW_eq_curlLHS`, `curlRW_eq_curlRHS`). The resulting bubble terms telescope against
the dot slides of the double sum (`sum_tele`). In the degenerate cases the bubble terms cancel
because the dot is a root of the total Chern class of its block (`Eleft_charpoly`,
`Eright_charpoly`).
-/

noncomputable section

open scoped TensorProduct

namespace Categorification.KL3.Diagram.Signed

open Categorification.Flag

universe u

variable {K : Type u} [Field K] {m : ℕ}

attribute [local instance] rightAlgebra midAlgebra

/-! ### Naturality of cups and caps -/

section Natural

variable (c : Fin m) {s s' : Comp m} (hE : StepR (true, c) s s') (hF : StepR (false, c) s' s)

theorem cupFEW_natural {C : Type u} [CommRing C] {X X' : BRing (H K s) C} (φ : BHom X X')
    (x : X.T) :
    BHom.whiskerLeft (Fst (K := K) c hF) (BHom.whiskerLeft (Est (K := K) c hE) φ)
      (cupFEW K c hE hF X x) = cupFEW K c hE hF X' (φ x) := by
  rw [cupFEW_apply, cupFEW_apply, BHom.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul]

theorem cupEFW_natural {C : Type u} [CommRing C] {X X' : BRing (H K s') C} (φ : BHom X X')
    (x : X.T) :
    BHom.whiskerLeft (Est (K := K) c hE) (BHom.whiskerLeft (Fst (K := K) c hF) φ)
      (cupEFW K c hE hF X x) = cupEFW K c hE hF X' (φ x) := by
  rw [cupEFW_apply, cupEFW_apply, BHom.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul]

theorem capFEW_natural {C : Type u} [CommRing C] {X X' : BRing (H K s) C} (φ : BHom X X')
    (v : ((Fst (K := K) c hF).tensor ((Est (K := K) c hE).tensor X)).T) :
    capFEW K c hE hF X' (BHom.whiskerLeft (Fst (K := K) c hF) (BHom.whiskerLeft (Est (K := K) c hE) φ) v) =
      φ (capFEW K c hE hF X v) := by
  refine BRing.induction_on (P := fun v => capFEW K c hE hF X' (BHom.whiskerLeft (Fst (K := K) c hF)
      (BHom.whiskerLeft (Est (K := K) c hE) φ) v) = φ (capFEW K c hE hF X v)) v
    (by simp only [BHom.map_zero]) (fun a w => ?_) (fun v v' hv hv' => ?_)
  · refine BRing.induction_on (P := fun w => capFEW K c hE hF X' (BHom.whiskerLeft (Fst (K := K) c hF)
        (BHom.whiskerLeft (Est (K := K) c hE) φ) (BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor X) a w)) =
        φ (capFEW K c hE hF X (BRing.tmul (Fst (K := K) c hF) ((Est (K := K) c hE).tensor X) a w))) w
      (by simp only [BRing.tmul_zero, BHom.map_zero]) (fun b x => ?_) (fun w w' hw hw' => ?_)
    · beta_reduce
      rw [BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul, capFEW_tmul, capFEW_tmul, φ.map_left]
    · beta_reduce at hw hw' ⊢
      rw [BRing.tmul_add, BHom.map_add, BHom.map_add, hw, hw', BHom.map_add, BHom.map_add]
  · beta_reduce at hv hv' ⊢
    rw [BHom.map_add, BHom.map_add, hv, hv', BHom.map_add, BHom.map_add]

theorem capEFW_natural {C : Type u} [CommRing C] {X X' : BRing (H K s') C} (φ : BHom X X')
    (v : ((Est (K := K) c hE).tensor ((Fst (K := K) c hF).tensor X)).T) :
    capEFW K c hE hF X' (BHom.whiskerLeft (Est (K := K) c hE) (BHom.whiskerLeft (Fst (K := K) c hF) φ) v) =
      φ (capEFW K c hE hF X v) := by
  refine BRing.induction_on (P := fun v => capEFW K c hE hF X' (BHom.whiskerLeft (Est (K := K) c hE)
      (BHom.whiskerLeft (Fst (K := K) c hF) φ) v) = φ (capEFW K c hE hF X v)) v
    (by simp only [BHom.map_zero]) (fun a w => ?_) (fun v v' hv hv' => ?_)
  · refine BRing.induction_on (P := fun w => capEFW K c hE hF X' (BHom.whiskerLeft (Est (K := K) c hE)
        (BHom.whiskerLeft (Fst (K := K) c hF) φ) (BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor X) a w)) =
        φ (capEFW K c hE hF X (BRing.tmul (Est (K := K) c hE) ((Fst (K := K) c hF).tensor X) a w))) w
      (by simp only [BRing.tmul_zero, BHom.map_zero]) (fun b x => ?_) (fun w w' hw hw' => ?_)
    · beta_reduce
      rw [BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul, capEFW_tmul, capEFW_tmul, φ.map_left]
    · beta_reduce at hw hw' ⊢
      rw [BRing.tmul_add, BHom.map_add, BHom.map_add, hw, hw', BHom.map_add, BHom.map_add]
  · beta_reduce at hv hv' ⊢
    rw [BHom.map_add, BHom.map_add, hv, hv', BHom.map_add, BHom.map_add]

end Natural

/-- For equal colours and equal steps, the identification `τ` of the dot slides is the identity. -/
theorem tauU_self (c : Fin m) {t r₁ r₂ : Comp m} (h₁ : StepR (true, c) r₁ t)
    (h₂ : StepR (true, c) r₂ r₁) : tauU K c c h₁ h₂ h₁ h₂ = BHom.id _ := by
  unfold tauU
  rw [dif_pos rfl]
  refine BHom.ext fun y => ?_
  apply (eeEquiv K c c h₁ h₂ (eeVar c h₁ h₂) (eeVar_hv c h₁ h₂)).injective
  rw [tauEE_apply]
  rfl

theorem whiskerLeft_mul_sub {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (M : BRing A B) {N N' : BRing B C} (F G : BHom N N') (w : N.T) (w' : N'.T)
    (hF : ∀ z, F (w * z) = w' * F z - G z) (y : (M.tensor N).T) :
    BHom.whiskerLeft M F (BRing.tmul M N 1 w * y) =
      BRing.tmul M N' 1 w' * BHom.whiskerLeft M F y - BHom.whiskerLeft M G y := by
  have := whiskerLeft_mul_add M F (-G) w w' (fun z => by rw [hF, BHom.neg_apply]; abel) y
  rw [this, BHom.whiskerLeft_neg, BHom.neg_apply]
  abel


/-- A telescoping identity for the double sums of `eq_ident_decomp`. -/
theorem sum_tele {A : Type*} [AddCommGroup A] (N : ℕ) (D : ℕ → ℕ → ℕ → A) :
    ∑ f ∈ Finset.range N, ∑ g ∈ Finset.range (f + 1),
      (D g (N - 1 - f) (f - g + 1) - D g (N - f) (f - g)) =
      ∑ g ∈ Finset.range N, (D g 0 (N - g) - D g (N - g) 0) := by
  simp only [Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_Ico_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' : g < N := (Finset.mem_Ico.1 hg).2
  rw [Finset.sum_Ico_eq_sum_range]
  have := Finset.sum_range_sub (fun k => D g (N - (g + k)) (g + k - g)) (N - g)
  simp only at this
  convert this using 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [show N - 1 - (g + k) = N - (g + (k + 1)) by omega,
      show g + k - g + 1 = g + (k + 1) - g by omega]
  · rw [show N - (g + (N - g)) = 0 by omega, show g + (N - g) - g = N - g by omega,
      show N - (g + 0) = N - g by omega, show g + 0 - g = 0 by omega]


/-! ### The dot is a root of the total Chern class of its block -/

section Roots

variable (c : Fin m) {t r : Comp m} (h : StepR (true, c) t r)

theorem eRight_x_castSucc (α : ℕ) :
    eRight K c t h.2 (x K t c.castSucc α) =
      xB K (splitLab _ (movedVar c t h.2)) (some c.castSucc) α := by
  rcases α with _ | α
  · rw [x_zero, map_one, xB_zero]
  · rw [eRight_x, if_neg (castSucc_ne_succ' c), add_zero]

/-- Across `E_c` (from `t` to `r = +_c t`): `x(r)_{c,α+1} = x(t)_{c,α+1} + ξ x(t)_{c,α}`
(KL III eq. (5.16)). -/
theorem Eleft_x_succ (α : ℕ) :
    (stepB K (true, c) t r h).left (x K r c.castSucc (α + 1)) =
      (stepB K (true, c) t r h).right (x K t c.castSucc (α + 1)) +
        xiStep K (true, c) t r h * (stepB K (true, c) t r h).right (x K t c.castSucc α) := by
  have e1 : ((stepB K (true, c) t r h).left (x K r c.castSucc (α + 1)) : ERing K c t h.2) =
      eLeft K c t h.2 (hCast K h.1.symm (x K r c.castSucc (α + 1))) := rfl
  have e2 : ∀ β, ((stepB K (true, c) t r h).right (x K t c.castSucc β) : ERing K c t h.2) =
      eRight K c t h.2 (x K t c.castSucc β) := fun β => rfl
  rw [e1, e2, e2, hCast_x, eLeft_x, if_pos rfl, eRight_x_castSucc c h, eRight_x_castSucc c h]
  rfl

/-- **The dot of `E_c` is a root of the total Chern class of block `c` of the left region**:
`∑_{g=0}^{r_c} (-1)^g x(r)_{c,g} ξ^{r_c - g} = 0` in `Γ(E_c)`. -/
theorem Eleft_charpoly :
    ∑ g ∈ Finset.range (r c.castSucc + 1), (-1) ^ g *
      ((stepB K (true, c) t r h).left (x K r c.castSucc g) *
        xiStep K (true, c) t r h ^ (r c.castSucc - g)) = 0 := by
  have hr : r c.castSucc = t c.castSucc + 1 := by rw [← h.1, raise_castSucc]
  set n := r c.castSucc with hn
  set b : ℕ → (stepB K (true, c) t r h).T := fun g =>
    (-1) ^ g * ((stepB K (true, c) t r h).right (x K t c.castSucc g) *
      xiStep K (true, c) t r h ^ (n - g)) with hb
  have hsub := Finset.sum_range_sub b n
  have hbn : b n = 0 := by
    simp only [hb]
    rw [x_eq_zero (by omega), map_zero, zero_mul, mul_zero]
  have hb0 : b 0 = xiStep K (true, c) t r h ^ n := by
    simp only [hb]
    rw [pow_zero, one_mul, x_zero, map_one, one_mul, Nat.sub_zero]
  rw [Finset.sum_range_succ', pow_zero, one_mul, x_zero, map_one, one_mul, Nat.sub_zero]
  have hterm : ∀ g ∈ Finset.range n, (-1) ^ (g + 1) *
      ((stepB K (true, c) t r h).left (x K r c.castSucc (g + 1)) *
        xiStep K (true, c) t r h ^ (n - (g + 1))) =
      b (g + 1) - b g := by
    intro g hg
    have hg' := Finset.mem_range.1 hg
    simp only [hb]
    rw [Eleft_x_succ, show n - g = n - (g + 1) + 1 by omega, pow_succ]
    ring
  rw [Finset.sum_congr rfl hterm, hsub, hbn, hb0]
  ring

end Roots

theorem xbar_of_zero {n : ℕ} (d : Fin n → ℕ) (j : Fin n) (hd : d j = 0) (α : ℕ) :
    xbar K d j α = if α = 0 then 1 else 0 := by
  have h := sum_x_mul_xbar (k := K) (d := d) j α
  rw [Finset.sum_eq_single 0 (fun f _ hf => by rw [x_eq_zero (by omega), zero_mul])
    (fun h0 => absurd (Finset.mem_range.2 (Nat.succ_pos α)) h0), x_zero, one_mul,
    Nat.sub_zero] at h
  exact h

theorem PhiH_of_succ_zero (lam : Comp m) (i : Fin m) (h0 : lam i.succ = 0) (g : ℕ) :
    PhiH (K := K) lam i g = (-1) ^ g * x K lam i.castSucc g := by
  rw [PhiH, bubbleSeq, Finset.sum_eq_single (g, 0)]
  · rw [xbar_of_zero _ _ h0, if_pos rfl, mul_one]
  · intro p hp hpg
    rw [Finset.mem_antidiagonal] at hp
    rw [xbar_of_zero _ _ h0, if_neg (fun h => hpg (Prod.ext (by omega) h)), mul_zero]
  · intro h; exact absurd (Finset.mem_antidiagonal.2 (add_zero g)) h

section RootsR

variable (c : Fin m) {s r : Comp m} (h : StepR (true, c) s r)

theorem eLeft_x_succ_block (α : ℕ) :
    eLeft K c s h.2 (x K (raise c s) c.succ α) =
      xB K (splitLab _ (movedVar c s h.2)) (some c.succ) α := by
  rcases α with _ | α
  · rw [x_zero, map_one, xB_zero]
  · rw [eLeft_x, if_neg (castSucc_ne_succ' c).symm, add_zero]

/-- Across `E_c` (from `s` to `r = +_c s`): `x(s)_{c+1,α+1} = x(r)_{c+1,α+1} + ξ x(r)_{c+1,α}`
(KL III eq. (5.15)). -/
theorem Eright_x_succ (α : ℕ) :
    (stepB K (true, c) s r h).right (x K s c.succ (α + 1)) =
      (stepB K (true, c) s r h).left (x K r c.succ (α + 1)) +
        xiStep K (true, c) s r h * (stepB K (true, c) s r h).left (x K r c.succ α) := by
  have e1 : ((stepB K (true, c) s r h).right (x K s c.succ (α + 1)) : ERing K c s h.2) =
      eRight K c s h.2 (x K s c.succ (α + 1)) := rfl
  have e2 : ∀ β, ((stepB K (true, c) s r h).left (x K r c.succ β) : ERing K c s h.2) =
      eLeft K c s h.2 (hCast K h.1.symm (x K r c.succ β)) := fun β => rfl
  rw [e1, e2, e2, hCast_x, hCast_x, eRight_x, if_pos rfl, eLeft_x_succ_block c h,
    eLeft_x_succ_block c h]
  rfl

/-- **The dot of `E_c` is a root of the total Chern class of block `c + 1` of the right region**:
`∑_{g=0}^{s_{c+1}} (-1)^g x(s)_{c+1,g} ξ^{s_{c+1} - g} = 0` in `Γ(E_c)`. -/
theorem Eright_charpoly :
    ∑ g ∈ Finset.range (s c.succ + 1), (-1) ^ g *
      ((stepB K (true, c) s r h).right (x K s c.succ g) *
        xiStep K (true, c) s r h ^ (s c.succ - g)) = 0 := by
  have hr : r c.succ + 1 = s c.succ := by
    have := h.2
    rw [← h.1, raise_succ]; omega
  set n := s c.succ with hn
  set b : ℕ → (stepB K (true, c) s r h).T := fun g =>
    (-1) ^ g * ((stepB K (true, c) s r h).left (x K r c.succ g) *
      xiStep K (true, c) s r h ^ (n - g)) with hb
  have hsub := Finset.sum_range_sub b n
  have hbn : b n = 0 := by
    simp only [hb]
    rw [x_eq_zero (by omega), map_zero, zero_mul, mul_zero]
  have hb0 : b 0 = xiStep K (true, c) s r h ^ n := by
    simp only [hb]
    rw [pow_zero, one_mul, x_zero, map_one, one_mul, Nat.sub_zero]
  rw [Finset.sum_range_succ', pow_zero, one_mul, x_zero, map_one, one_mul, Nat.sub_zero]
  have hterm : ∀ g ∈ Finset.range n, (-1) ^ (g + 1) *
      ((stepB K (true, c) s r h).right (x K s c.succ (g + 1)) *
        xiStep K (true, c) s r h ^ (n - (g + 1))) =
      b (g + 1) - b g := by
    intro g hg
    have hg' := Finset.mem_range.1 hg
    simp only [hb]
    rw [Eright_x_succ, show n - g = n - (g + 1) + 1 by omega, pow_succ]
    ring
  rw [Finset.sum_congr rfl hterm, hsub, hbn, hb0]
  ring

end RootsR

theorem PsiH_of_castSucc_zero (lam : Comp m) (i : Fin m) (h0 : lam i.castSucc = 0) (g : ℕ) :
    PsiH (K := K) lam i g = (-1) ^ g * x K lam i.succ g := by
  rw [PsiH, bubbleSeq, Finset.sum_eq_single (g, 0)]
  · rw [xbar_of_zero _ _ h0, if_pos rfl, mul_one]
  · intro p hp hpg
    rw [Finset.mem_antidiagonal] at hp
    rw [xbar_of_zero _ _ h0, if_neg (fun h => hpg (Prod.ext (by omega) h)), mul_zero]
  · intro h; exact absurd (Finset.mem_antidiagonal.2 (add_zero g)) h

/-! ### The sideways crossings of equal colours -/

section SameSideways

variable (i : Fin m) {q r q' : Comp m} (hF : StepR (false, i) r q) (hE' : StepR (true, i) r q')
  {C : Type u} [CommRing C] (Y : BRing (H K r) C)

/-- The crossing `E_i E_i → E_i E_i` of `crossl`/`crossr`, whiskered: the dot on its left input. -/
theorem locSame_dotL (v : ((stepB K (true, i) r q' hE').tensor ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y))).T) :
    locTwo (crossU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y) (BRing.tmul (stepB K (true, i) r q' hE') ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)) (eXi K i r hE'.2) 1 * v) =
      locTwo (tauU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y) v + BRing.tmul (stepB K (true, i) r q' hE') ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)) 1 (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2) 1) *
        locTwo (crossU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y) v := by
  have := BHom.congr_apply ((crossU_rules (K := K) i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)).locL ((stepB K (false, i) r q hF).tensor Y)) v
  rw [BHom.comp_apply, BHom.add_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply] at this
  exact this

/-- The crossing of `crossl`/`crossr`, whiskered: the dot on its right input. -/
theorem locSame_dotR (v : ((stepB K (true, i) r q' hE').tensor ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y))).T) :
    locTwo (crossU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y) (BRing.tmul (stepB K (true, i) r q' hE') ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)) 1 (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2) 1) * v) =
      BRing.tmul (stepB K (true, i) r q' hE') ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)) (eXi K i r hE'.2) 1 * locTwo (crossU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y) v - locTwo (tauU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y) v := by
  have := BHom.congr_apply ((crossU_rules (K := K) i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)).locR ((stepB K (false, i) r q hF).tensor Y)) v
  rw [BHom.comp_apply, BHom.sub_apply, BHom.comp_apply, BHom.mulB_apply, BHom.mulB_apply] at this
  exact this

theorem locSame_tau (v : ((stepB K (true, i) r q' hE').tensor ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y))).T) :
    locTwo (tauU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y) v = v := by
  rw [tauU_self, locTwo_id, BHom.id_apply]

/-- **`crossl` of equal colours, the dot of `E_i`**: `crossl ∘ ξ_E = ξ_E ∘ crossl - cup ∘ cap`. -/
theorem crosslW_same_dotE (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    crosslW K i i hF hF hE' hE' Y (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2) 1 * z) = BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2) 1) * crosslW K i i hF hF hE' hE' Y z - cupFEW K i (hE' : StepR (true, i) r q') hE' Y (capEFW K i (hF : StepR (true, i) q r) hF Y z) := by
  simp only [crosslW, BHom.comp_apply]
  rw [cupFEW_mul, whiskerLeft_mul_sub _ _ _ _ _ (locSame_dotR i hF hE' Y), BHom.map_sub,
    whiskerLeft_mul_right _ _ _ _ (fun z => whiskerLeft_mul_left _ _ z _)]
  congr 1
  have e : ∀ V, BHom.whiskerLeft (stepB K (false, i) q' r hE') (locTwo (tauU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y)) V = V := fun V => by
    rw [tauU_self, locTwo_id, BHom.whiskerLeft_id, BHom.id_apply]
  rw [e, cupFEW_natural]

/-- **`crossl` of equal colours, the dot of `F_i`**: `crossl ∘ ξ_F = ξ_F ∘ crossl - cup ∘ cap`. -/
theorem crosslW_same_dotF (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    crosslW K i i hF hF hE' hE' Y (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2) 1) * z) = BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) (eXi K i r hE'.2) 1 * crosslW K i i hF hF hE' hE' Y z - cupFEW K i (hE' : StepR (true, i) r q') hE' Y (capEFW K i (hF : StepR (true, i) q r) hF Y z) := by
  simp only [crosslW, BHom.comp_apply]
  rw [cupFEW_mul, whiskerLeft_mul_right _ _ _ _ (locTwo_mul_suffix' _ _ _)]
  rw [whiskerLeft_mul_congr _ _ _ (BRing.tmul (stepB K (true, i) r q' hE') ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)) 1
      (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2) 1))
    (whiskerLeft_mul_congr _ _ _ _ (capEFW_slide i (hF : StepR (true, i) q r) hF Y _))]
  have key := whiskerLeft_mul_add (stepB K (false, i) q' r hE') (locTwo (crossU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y)) (locTwo (tauU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y))
    (BRing.tmul (stepB K (true, i) r q' hE') ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)) (eXi K i r hE'.2) 1)
    (BRing.tmul (stepB K (true, i) r q' hE') ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)) 1 (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2) 1)) (locSame_dotL i hF hE' Y)
  rw [eq_sub_of_add_eq' (key _).symm, BHom.map_sub,
    ← cupFEW_slide i (hE' : StepR (true, i) r q') hE', whiskerLeft_mul_left, whiskerLeft_mul_left]
  congr 1
  have e : ∀ V, BHom.whiskerLeft (stepB K (false, i) q' r hE') (locTwo (tauU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y)) V = V := fun V => by
    rw [tauU_self, locTwo_id, BHom.whiskerLeft_id, BHom.id_apply]
  rw [e, cupFEW_natural]

/-- **`crossr` of equal colours, the dot of `E_i`**: `crossr ∘ ξ_E = ξ_E ∘ crossr + cup ∘ cap`. -/
theorem crossrW_same_dotE (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    crossrW K i i hE' hE' hF hF Y (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2) 1) * w) = BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2) 1 * crossrW K i i hE' hE' hF hF Y w + cupEFW K i (hF : StepR (true, i) q r) hF Y (capFEW K i (hE' : StepR (true, i) r q') hE' Y w) := by
  simp only [crossrW, BHom.comp_apply]
  rw [whiskerLeft_mul_right _ _ _ _ (fun z => whiskerLeft_mul_left _ _ z _),
    whiskerLeft_mul_add _ _ _ _ _ (locSame_dotL i hF hE' Y), BHom.map_add, capFEW_mul]
  refine (add_comm _ _).trans ?_
  congr 1
  have e : ∀ V, BHom.whiskerLeft (stepB K (false, i) q' r hE') (locTwo (tauU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y)) V = V := fun V => by
    rw [tauU_self, locTwo_id, BHom.whiskerLeft_id, BHom.id_apply]
  rw [e, capFEW_natural]

/-- **`crossr` of equal colours, the dot of `F_i`**: `crossr ∘ ξ_F = ξ_F ∘ crossr + cup ∘ cap`. -/
theorem crossrW_same_dotF (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    crossrW K i i hE' hE' hF hF Y (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) (eXi K i r hE'.2) 1 * w) = BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2) 1) * crossrW K i i hE' hE' hF hF Y w + cupEFW K i (hF : StepR (true, i) q r) hF Y (capFEW K i (hE' : StepR (true, i) r q') hE' Y w) := by
  simp only [crossrW, BHom.comp_apply]
  rw [whiskerLeft_mul_left, whiskerLeft_mul_left,
    ← capFEW_slide i (hE' : StepR (true, i) r q') hE' _ _]
  have key := whiskerLeft_mul_sub (stepB K (false, i) q' r hE') (locTwo (crossU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y)) (locTwo (tauU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y))
    (BRing.tmul (stepB K (true, i) r q' hE') ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)) 1 (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2) 1))
    (BRing.tmul (stepB K (true, i) r q' hE') ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)) (eXi K i r hE'.2) 1) (locSame_dotR i hF hE' Y)
  rw [(sub_eq_iff_eq_add.1 (key _).symm), BHom.map_add]
  congr 1
  · rw [whiskerLeft_mul_image _ _ _ (BRing.tmul (stepB K (true, i) r q' hE')
        ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)) 1
        (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1
        (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2) 1)))
      (whiskerLeft_mul_image _ _ _ _ (fun y =>
        (cupEFW_slide i (hF : StepR (true, i) q r) hF Y y)))]
    rw [whiskerLeft_mul_right _ _ _ _ (locTwo_mul_suffix' _ _ _), capFEW_mul]
  · have e : ∀ V, BHom.whiskerLeft (stepB K (false, i) q' r hE') (locTwo (tauU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y)) V = V := fun V => by
      rw [tauU_self, locTwo_id, BHom.whiskerLeft_id, BHom.id_apply]
    rw [e, capFEW_natural]

/-- **The cap after `crossl` is a curl**: `cap_{FE} ∘ crossl = cap_{EF} ∘ curlL`. -/
theorem capFEW_crosslW (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    capFEW K i (hE' : StepR (true, i) r q') hE' Y (crosslW K i i hF hF hE' hE' Y z) = capEFW K i (hF : StepR (true, i) q r) hF Y (curlLW K i (hF : StepR (true, i) q r) hE' ((stepB K (false, i) r q hF).tensor Y) z) := by
  simp only [crosslW, curlLW, BHom.comp_apply]
  rw [capFEW_natural]

/-- **The cup before `crossr` is a curl**: `crossr ∘ cup_{FE} = curlL ∘ cup_{EF}`. -/
theorem crossrW_cupFEW (y : Y.T) :
    crossrW K i i hE' hE' hF hF Y (cupFEW K i (hE' : StepR (true, i) r q') hE' Y y) = curlLW K i (hF : StepR (true, i) q r) hE' ((stepB K (false, i) r q hF).tensor Y) (cupEFW K i (hF : StepR (true, i) q r) hF Y y) := by
  simp only [crossrW, curlLW, BHom.comp_apply]
  rw [cupFEW_natural]

variable (K) in
/-- The composite `(cup with a dots on F_i) ∘ b ∘ (c dots on E_i, then cap)` on `E_i F_i Y`,
`b ∈ H_r` acting in the region `r`. -/
def dcV (a c : ℕ) (b : H K r) (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T :=
  BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2 ^ a) 1) * cupEFW K i (hF : StepR (true, i) q r) hF Y (Y.left b * capEFW K i (hF : StepR (true, i) q r) hF Y (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2 ^ c) 1 * z))

theorem dcV_add (a c : ℕ) (b : H K r) (z z' : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    dcV K i hF Y (a) (c) (b) (z + z') = dcV K i hF Y (a) (c) (b) (z) + dcV K i hF Y (a) (c) (b) (z') := by
  simp only [dcV]
  rw [mul_add, BHom.map_add, mul_add, BHom.map_add, mul_add]

theorem dcV_dotE_in (a c : ℕ) (b : H K r) (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    dcV K i hF Y (a) (c) (b) (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2) 1 * z) = dcV K i hF Y (a) (c + 1) (b) (z) := by
  simp only [dcV]
  rw [← mul_assoc, BRing.tmul_mul_tmul, mul_one, ← pow_succ]

theorem dcV_dotF_in (a c : ℕ) (b : H K r) (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    dcV K i hF Y (a) (c) (b) (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2) 1) * z) = dcV K i hF Y (a) (c + 1) (b) (z) := by
  simp only [dcV]
  rw [mul_left_comm, capEFW_slide, ← mul_assoc, BRing.tmul_mul_tmul, mul_one, ← pow_succ']

theorem dcV_dotF_out (a c : ℕ) (b : H K r) (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2) 1) * dcV K i hF Y (a) (c) (b) (z) = dcV K i hF Y (a + 1) (c) (b) (z) := by
  simp only [dcV]
  rw [← mul_assoc, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, mul_one, ← pow_succ']

theorem dcV_dotE_out (a c : ℕ) (b : H K r) (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2) 1 * dcV K i hF Y (a) (c) (b) (z) = dcV K i hF Y (a + 1) (c) (b) (z) := by
  simp only [dcV]
  rw [mul_left_comm, cupEFW_slide, ← mul_assoc, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul,
    one_mul, mul_one, ← pow_succ]

theorem cupEFW_slide_pow (k : ℕ) (y : Y.T) :
    BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2 ^ k) 1 * cupEFW K i (hF : StepR (true, i) q r) hF Y y = BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2 ^ k) 1) * cupEFW K i (hF : StepR (true, i) q r) hF Y y := by
  induction k with
  | zero => simp only [pow_zero, ← BRing.one_eq]
  | succ k ih =>
    have e1 : BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2 ^ (k + 1)) 1 = BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2) 1 * BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2 ^ k) 1 := by
      rw [BRing.tmul_mul_tmul, mul_one, pow_succ']
    have e2 : BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2 ^ (k + 1)) 1) = BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2 ^ k) 1) * BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2) 1) := by
      rw [BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, mul_one, one_mul, pow_succ]
    rw [e1, e2, mul_assoc, ih, mul_left_comm, cupEFW_slide, mul_assoc]

theorem tmul_one_one_one :
    BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (1) 1) = 1 := by
  rw [← BRing.one_eq, ← BRing.one_eq]

/-- The cup after the cap after the curl. -/
theorem cupEF_capEF_curlL (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    cupEFW K i (hF : StepR (true, i) q r) hF Y (capEFW K i (hF : StepR (true, i) q r) hF Y (curlLW K i (hF : StepR (true, i) q r) hE' ((stepB K (false, i) r q hF).tensor Y) z)) =
      ∑ g ∈ Finset.range (nH r i + 1).toNat, dcV K i hF Y (0) ((nH r i - g).toNat) ((ccwLH r i (-nH r i - 1 + g))) (z) := by
  have hxi : xiStep K (true, i) q r hF = eXi K i q hF.2 := rfl
  rw [curlLW_eq_curlLHS, BHom.mulB_apply, Finset.sum_mul, BHom.map_sum, BHom.map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have e : ∀ (a b : (stepB K (true, i) q r hF).T), BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (a * b) 1 =
      BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) a 1 * BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) b 1 := fun a b => by
    rw [BRing.tmul_mul_tmul, mul_one]
  rw [hxi, e, ← BRing.tensor_left, mul_assoc,
    BHom.map_left, dcV, pow_zero, tmul_one_one_one, one_mul]

/-- The curl after the cup after the cap. -/
theorem curlL_cupEF_capEF (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    curlLW K i (hF : StepR (true, i) q r) hE' ((stepB K (false, i) r q hF).tensor Y) (cupEFW K i (hF : StepR (true, i) q r) hF Y (capEFW K i (hF : StepR (true, i) q r) hF Y z)) =
      ∑ g ∈ Finset.range (nH r i + 1).toNat, dcV K i hF Y ((nH r i - g).toNat) (0) ((ccwLH r i (-nH r i - 1 + g))) (z) := by
  have hxi : xiStep K (true, i) q r hF = eXi K i q hF.2 := rfl
  rw [curlLW_eq_curlLHS, BHom.mulB_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  have e : ∀ (a b : (stepB K (true, i) q r hF).T), BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (a * b) 1 =
      BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) a 1 * BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) b 1 := fun a b => by
    rw [BRing.tmul_mul_tmul, mul_one]
  rw [hxi, e, ← BRing.tensor_left, mul_assoc,
    cupEFW_slide_pow, mul_left_comm, ← BHom.map_left, dcV, pow_zero, ← BRing.one_eq, one_mul]

/-- **`crossr ∘ crossl` and the dot of `E_i`**. -/
theorem crossrl_dotE (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    crossrW K i i hE' hE' hF hF Y (crosslW K i i hF hF hE' hE' Y (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2) 1 * z)) = BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2) 1 * crossrW K i i hE' hE' hF hF Y (crosslW K i i hF hF hE' hE' Y z) + ∑ g ∈ Finset.range (nH r i + 1).toNat, (dcV K i hF Y (0) ((nH r i - g).toNat) ((ccwLH r i (-nH r i - 1 + g))) (z) - dcV K i hF Y ((nH r i - g).toNat) (0) ((ccwLH r i (-nH r i - 1 + g))) (z)) := by
  rw [crosslW_same_dotE, BHom.map_sub, crossrW_same_dotE, capFEW_crosslW, crossrW_cupFEW,
    cupEF_capEF_curlL, curlL_cupEF_capEF, Finset.sum_sub_distrib]
  abel

/-- **`crossr ∘ crossl` and the dot of `F_i`**. -/
theorem crossrl_dotF (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    crossrW K i i hE' hE' hF hF Y (crosslW K i i hF hF hE' hE' Y (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2) 1) * z)) = BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2) 1) * crossrW K i i hE' hE' hF hF Y (crosslW K i i hF hF hE' hE' Y z) + ∑ g ∈ Finset.range (nH r i + 1).toNat, (dcV K i hF Y (0) ((nH r i - g).toNat) ((ccwLH r i (-nH r i - 1 + g))) (z) - dcV K i hF Y ((nH r i - g).toNat) (0) ((ccwLH r i (-nH r i - 1 + g))) (z)) := by
  rw [crosslW_same_dotF, BHom.map_sub, crossrW_same_dotF, capFEW_crosslW, crossrW_cupFEW,
    cupEF_capEF_curlL, curlL_cupEF_capEF, Finset.sum_sub_distrib]
  abel

theorem crossSame_pow_one (g : ℕ) :
    crossU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (BRing.tmul (stepB K (true, i) r q' hE') (stepB K (true, i) q r hF) (eXi K i r hE'.2 ^ g) 1) =
      ∑ f ∈ Finset.range g, BRing.tmul (stepB K (true, i) r q' hE') (stepB K (true, i) q r hF) (eXi K i r hE'.2 ^ (g - 1 - f)) (eXi K i q hF.2 ^ f) := by
  have := crossU_same_tmul_pow (K := K) i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)
    (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) g 0
  rw [pow_zero, Finset.sum_range_zero, sub_zero, add_zero] at this
  exact this

theorem crossSame_one_pow (g : ℕ) :
    crossU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (BRing.tmul (stepB K (true, i) r q' hE') (stepB K (true, i) q r hF) 1 (eXi K i q hF.2 ^ g)) =
      -∑ f ∈ Finset.range g, BRing.tmul (stepB K (true, i) r q' hE') (stepB K (true, i) q r hF) (eXi K i r hE'.2 ^ (g - 1 - f)) (eXi K i q hF.2 ^ f) := by
  have := crossU_same_tmul_pow (K := K) i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)
    (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) 0 g
  rw [pow_zero, Finset.sum_range_zero, zero_sub, zero_add] at this
  exact this

/-- **`crossl` of equal colours at `1`**: `crossl(1 ⊗ 1 ⊗ y) = 1 ⊗ 1 ⊗ y`. -/
theorem crosslW_same_one (y : Y.T) :
    crosslW K i i hF hF hE' hE' Y (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y 1 y)) = BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y 1 y) := by
  have hri : r i.castSucc = q i.castSucc + 1 := by rw [← hF.1, raise_castSucc]
  have hd : dFE i (hE' : StepR (true, i) r q') = r i.castSucc := dFE_eq i _
  simp only [crosslW, BHom.comp_apply]
  rw [cupFEW_apply', BHom.map_sum, BHom.map_sum]
  have hterm : ∀ g ∈ Finset.range (dFE i (hE' : StepR (true, i) r q') + 1),
      BHom.whiskerLeft (stepB K (false, i) q' r hE') (BHom.whiskerLeft (stepB K (true, i) r q' hE') (capEFW K i (hF : StepR (true, i) q r) hF Y))
        (BHom.whiskerLeft (stepB K (false, i) q' r hE') (locTwo (crossU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y))
          (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)))
            ((-1) ^ (dFE i (hE' : StepR (true, i) r q') - g) *
              xsFE i (hE' : StepR (true, i) r q') (dFE i (hE' : StepR (true, i) r q') - g) :
                ERing K i r hE'.2)
            (BRing.tmul (stepB K (true, i) r q' hE') ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)) (eXi K i r hE'.2 ^ g) (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y 1 y))))) =
      if g = dFE i (hE' : StepR (true, i) r q') then BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y 1 y) else 0 := by
    intro g hg
    have hg' : g ≤ dFE i (hE' : StepR (true, i) r q') := Nat.lt_succ_iff.1 (Finset.mem_range.1 hg)
    rw [BHom.whiskerLeft_tmul, BHom.whiskerLeft_tmul, locTwo_tmul, crossSame_pow_one,
      BRing.sum_tmul, BHom.map_sum, BHom.map_sum]
    simp only [crosslCap_tmul i i hF hE' Y]
    split_ifs with hgd
    · rw [Finset.sum_eq_single (q i.castSucc)]
      · rw [capEFP_xi_pow i _ _ _ (le_refl _), if_pos rfl, map_one, one_mul, hgd, Nat.sub_self,
          pow_zero, one_mul, xsFE_eq, x_zero, map_one, show dFE i (hE' : StepR (true, i) r q') - 1 -
            q i.castSucc = 0 by omega, pow_zero]
      · intro f hf hfq
        have hf' := Finset.mem_range.1 hf
        rw [capEFP_xi_pow i _ _ _ (by omega), if_neg hfq, map_zero, zero_mul, BRing.tmul_zero]
      · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
    · rw [Finset.sum_eq_zero fun f hf => ?_, BRing.tmul_zero]
      have hf' := Finset.mem_range.1 hf
      rw [capEFP_xi_pow i _ _ _ (by omega), if_neg (by omega), map_zero, zero_mul, BRing.tmul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (dFE i (hE' : StepR (true, i) r q') + 1)) (dFE i (hE' : StepR (true, i) r q')),
    if_pos (Finset.mem_range.2 (Nat.lt_succ_self _))]

/-- **`crossr` of equal colours at `1`**: `crossr(1 ⊗ 1 ⊗ y) = -(1 ⊗ 1 ⊗ y)`. -/
theorem crossrW_same_one (y : Y.T) :
    crossrW K i i hE' hE' hF hF Y (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y 1 y)) = -BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y 1 y) := by
  have hrs : r i.succ + 1 = q i.succ := by
    have := hF.2
    rw [← hF.1, raise_succ]; omega
  have hd : dEF i (hF : StepR (true, i) q r) = q i.succ - 1 := dEF_eq i _
  have hr1 := hE'.2
  simp only [crossrW, BHom.comp_apply, BHom.whiskerLeft_tmul]
  rw [cupEFW_apply'', BRing.tmul_sum, BHom.map_sum, BRing.tmul_sum, BHom.map_sum]
  have hterm : ∀ g ∈ Finset.range (dEF i (hF : StepR (true, i) q r) + 1),
      capFEW K i (hE' : StepR (true, i) r q') hE' ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y))
        (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y))) 1 (locTwo (crossU K i i (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r) (hE' : StepR (true, i) r q') (hF : StepR (true, i) q r)) ((stepB K (false, i) r q hF).tensor Y)
          (BRing.tmul (stepB K (true, i) r q' hE') ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)) 1 ((-1) ^ (dEF i (hF : StepR (true, i) q r) - g) *
            BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2 ^ g) (BRing.tmul (stepB K (false, i) r q hF) Y 1
              (Y.left (x K r i.succ (dEF i (hF : StepR (true, i) q r) - g)) * y)))))) =
      if g = dEF i (hF : StepR (true, i) q r) then -BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y 1 y) else 0 := by
    intro g hg
    have hg' : g ≤ dEF i (hF : StepR (true, i) q r) := Nat.lt_succ_iff.1 (Finset.mem_range.1 hg)
    rw [tmul_neg_one_pow_mul, BHom.map_neg_one_pow_mul, tmul_neg_one_pow_mul,
      BHom.map_neg_one_pow_mul, locTwo_tmul, crossSame_one_pow, BRing.neg_tmul, BHom.map_neg,
      BRing.tmul_neg, BHom.map_neg, BRing.sum_tmul, BHom.map_sum, BRing.tmul_sum, BHom.map_sum]
    simp only [crossrCap_tmul i i hE' hF hF Y]
    split_ifs with hgd
    · rw [Finset.sum_eq_single 0]
      · rw [capFEP_xi_pow i (hE' : StepR (true, i) r q') hE' (g - 1 - 0) (by omega), if_pos (by omega), map_one, one_mul, pow_zero,
          hgd, Nat.sub_self, pow_zero, one_mul, x_zero, map_one, one_mul]
      · intro f hf hf0
        have hf' := Finset.mem_range.1 hf
        rw [capFEP_xi_pow i (hE' : StepR (true, i) r q') hE' (g - 1 - f) (by omega), if_neg (by omega),
          map_zero, zero_mul, BRing.zero_tmul]
      · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
    · rw [Finset.sum_eq_zero fun f hf => ?_, neg_zero, mul_zero]
      have hf' := Finset.mem_range.1 hf
      rw [capFEP_xi_pow i (hE' : StepR (true, i) r q') hE' (g - 1 - f) (by omega), if_neg (by omega),
        map_zero, zero_mul, BRing.zero_tmul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (dEF i (hF : StepR (true, i) q r) + 1)) (dEF i (hF : StepR (true, i) q r)),
    if_pos (Finset.mem_range.2 (Nat.lt_succ_self _))]

/-- The double sum of `eq_ident_decomp` on `E_i F_i Y`, pointwise. -/
theorem sumEF_dot (u : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T)
    (hin : ∀ a c b z, dcV K i hF Y (a) (c) (b) (u * z) = dcV K i hF Y (a) (c + 1) (b) (z))
    (hout : ∀ a c b z, u * dcV K i hF Y (a) (c) (b) (z) = dcV K i hF Y (a + 1) (c) (b) (z)) (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    ∑ f ∈ Finset.range (nH r i).toNat, ∑ g ∈ Finset.range (f + 1), dcV K i hF Y ((nH r i).toNat - 1 - f) (f - g) ((ccwLH r i (-nH r i - 1 + g))) (u * z) = u * ∑ f ∈ Finset.range (nH r i).toNat, ∑ g ∈ Finset.range (f + 1), dcV K i hF Y ((nH r i).toNat - 1 - f) (f - g) ((ccwLH r i (-nH r i - 1 + g))) (z) + ∑ g ∈ Finset.range (nH r i).toNat, (dcV K i hF Y (0) ((nH r i).toNat - g) ((ccwLH r i (-nH r i - 1 + g))) (z) - dcV K i hF Y ((nH r i).toNat - g) (0) ((ccwLH r i (-nH r i - 1 + g))) (z)) := by
  rw [← sum_tele (nH r i).toNat (fun g a c => dcV K i hF Y (a) (c) ((ccwLH r i (-nH r i - 1 + g))) (z)), Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hf' := Finset.mem_range.1 hf
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hin, hout, show (nH r i).toNat - 1 - f + 1 = (nH r i).toNat - f by omega]
  abel

theorem corr_eq (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) : ∑ g ∈ Finset.range (nH r i + 1).toNat, (dcV K i hF Y (0) ((nH r i - g).toNat) ((ccwLH r i (-nH r i - 1 + g))) (z) - dcV K i hF Y ((nH r i - g).toNat) (0) ((ccwLH r i (-nH r i - 1 + g))) (z)) = ∑ g ∈ Finset.range (nH r i).toNat, (dcV K i hF Y (0) ((nH r i).toNat - g) ((ccwLH r i (-nH r i - 1 + g))) (z) - dcV K i hF Y ((nH r i).toNat - g) (0) ((ccwLH r i (-nH r i - 1 + g))) (z)) := by
  by_cases hn : 0 ≤ nH r i
  · rw [show (nH r i + 1).toNat = (nH r i).toNat + 1 by omega, Finset.sum_range_succ,
      show (nH r i - ((nH r i).toNat : ℕ)).toNat = 0 by omega, sub_self, add_zero]
    refine Finset.sum_congr rfl fun g hg => ?_
    have hg' := Finset.mem_range.1 hg
    rw [show (nH r i - (g : ℕ)).toNat = (nH r i).toNat - g by omega]
  · rw [show (nH r i + 1).toNat = 0 by omega, show (nH r i).toNat = 0 by omega, Finset.sum_range_zero,
      Finset.sum_range_zero]

theorem dcV_one (a c : ℕ) (b : H K r) (hc : c < q i.castSucc) (y : Y.T) :
    dcV K i hF Y (a) (c) (b) (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y 1 y)) = 0 := by
  simp only [dcV]
  rw [BRing.tmul_mul_tmul, mul_one, one_mul, capEFW_tmul,
    capEFP_xi_pow i _ _ _ hc.le, if_neg hc.ne, map_zero, zero_mul, mul_zero, BHom.map_zero,
    mul_zero]

variable (K) in
/-- `Γ_N` of `(cup with a dots on F_i) ∘ b ∘ (c dots on E_i, then cap)` on `E_i F_i Y`, `b ∈ H_r`
the image of a bubble in the region `r` (`dotCapEF`, `cupDotEF` of Definition 3.1). -/
def dcW (a c : ℕ) (b : H K r) : BHom ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)) ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)) :=
  (BHom.mulB (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2 ^ a) 1))).comp ((cupEFW K i (hF : StepR (true, i) q r) hF Y).comp ((BHom.mulB (Y.left b)).comp
    ((capEFW K i (hF : StepR (true, i) q r) hF Y).comp (BHom.mulB (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2 ^ c) 1)))))

theorem dcW_apply (a c : ℕ) (b : H K r) (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    dcW K i hF Y a c b z = dcV K i hF Y (a) (c) (b) (z) := rfl

/-- **`eq_ident_decomp` on `E_i F_i`, first identity, under `Γ_N`** (KL III Definition 3.1,
`Rel.decompEF`; Proposition 6.3): on `E_i F_i Y` with `F_i E_i 1_λ ≠ 0` and `n = ⟨i, λ⟩`,
`1 = -crossr ∘ crossl + ∑_{f=0}^{n-1} ∑_{g=0}^{f}` (cup with `n - 1 - f` dots on `F_i`)
`∘ Γ(ccwL (-n - 1 + g)) ∘` (`f - g` dots on `E_i`, cap), the (real or fake) bubbles acting in the
region `λ` (`ccwLH`). -/
theorem decompEF_W (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    z = -crossrW K i i hE' hE' hF hF Y (crosslW K i i hF hF hE' hE' Y z) + ∑ f ∈ Finset.range (nH r i).toNat, ∑ g ∈ Finset.range (f + 1),
      dcW K i hF Y ((nH r i).toNat - 1 - f) (f - g) (ccwLH r i (-nH r i - 1 + g)) z := by
  simp only [dcW_apply]
  have hrs : r i.succ + 1 = q i.succ := by
    have := hF.2
    rw [← hF.1, raise_succ]; omega
  have hri : r i.castSucc = q i.castSucc + 1 := by rw [← hF.1, raise_castSucc]
  have hr1 := hE'.2
  have hn : nH r i = (r i.castSucc : ℤ) - r i.succ := rfl
  let Φ : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T →+ ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T := -((crossrW K i i hE' hE' hF hF Y).comp (crosslW K i i hF hF hE' hE' Y)).toAddHom +
    ∑ f ∈ Finset.range (nH r i).toNat, ∑ g ∈ Finset.range (f + 1),
      (dcW K i hF Y ((nH r i).toNat - 1 - f) (f - g) (ccwLH r i (-nH r i - 1 + g))).toAddHom
  have hΦ : ∀ z, Φ z = -crossrW K i i hE' hE' hF hF Y (crosslW K i i hF hF hE' hE' Y z) + ∑ f ∈ Finset.range (nH r i).toNat, ∑ g ∈ Finset.range (f + 1),
      dcV K i hF Y ((nH r i).toNat - 1 - f) (f - g) (ccwLH r i (-nH r i - 1 + g)) z := fun z => by
    simp only [Φ, AddMonoidHom.add_apply, AddMonoidHom.neg_apply, AddMonoidHom.finset_sum_apply,
      BHom.toAddHom_apply, BHom.comp_apply, dcW_apply]
    rfl
  have key := ext_two (Y := Y) (eXi K i q hF.2) (eXi K i q hF.2) (stepE_spanned i (hF : StepR (true, i) q r))
    (stepF_spanned i hF) Φ (AddMonoidHom.id _) (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2) 1) (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2) 1))
    (fun z => ?_) (fun z => rfl) (fun z => ?_) (fun z => rfl) (fun y => ?_) z
  · rw [← hΦ]; exact key.symm
  · rw [hΦ, hΦ, crossrl_dotE, sumEF_dot i hF Y _ (dcV_dotE_in i hF Y) (dcV_dotE_out i hF Y),
      corr_eq]
    rw [mul_add, mul_neg]
    abel
  · rw [hΦ, hΦ, crossrl_dotF, sumEF_dot i hF Y _ (dcV_dotF_in i hF Y) (dcV_dotF_out i hF Y),
      corr_eq]
    rw [mul_add, mul_neg]
    abel
  · rw [hΦ, crosslW_same_one, crossrW_same_one, neg_neg, AddMonoidHom.id_apply]
    rw [Finset.sum_eq_zero fun f hf => Finset.sum_eq_zero fun g hg => ?_, add_zero]
    have hf' := Finset.mem_range.1 hf
    have hg' := Finset.mem_range.1 hg
    exact dcV_one i hF Y _ _ _ (by omega) y

theorem cupEF_capEF_term (b : H K r) (k : ℕ) (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    cupEFW K i (hF : StepR (true, i) q r) hF Y (capEFW K i (hF : StepR (true, i) q r) hF Y (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) ((stepB K (true, i) q r hF).left b * xiStep K (true, i) q r hF ^ k) 1 * z)) = dcV K i hF Y (0) (k) (b) (z) := by
  have e : ∀ (a b : (stepB K (true, i) q r hF).T), BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (a * b) 1 =
      BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) a 1 * BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) b 1 := fun a b => by
    rw [BRing.tmul_mul_tmul, mul_one]
  have hxi : xiStep K (true, i) q r hF = eXi K i q hF.2 := rfl
  rw [hxi, e, ← BRing.tensor_left, mul_assoc, BHom.map_left, dcV, pow_zero, tmul_one_one_one,
    one_mul]

theorem term_cupEF_capEF (b : H K r) (k : ℕ) (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) ((stepB K (true, i) q r hF).left b * xiStep K (true, i) q r hF ^ k) 1 * cupEFW K i (hF : StepR (true, i) q r) hF Y (capEFW K i (hF : StepR (true, i) q r) hF Y z) = dcV K i hF Y (k) (0) (b) (z) := by
  have e : ∀ (a b : (stepB K (true, i) q r hF).T), BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (a * b) 1 =
      BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) a 1 * BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) b 1 := fun a b => by
    rw [BRing.tmul_mul_tmul, mul_one]
  have hxi : xiStep K (true, i) q r hF = eXi K i q hF.2 := rfl
  rw [hxi, e, ← BRing.tensor_left, mul_assoc, cupEFW_slide_pow, mul_left_comm, ← BHom.map_left, dcV,
    pow_zero, ← BRing.one_eq, one_mul]

/-- **Without `F_i E_i 1_λ`, the bubble terms of the dot slides cancel**: if `r_{i+1} = 0`, then
`∑_{g=0}^{n} Γ(ccwL (-n - 1 + g)) ξ^{n-g} = 0` on `E_i` (the dot is a root of the total Chern
class of block `i`). -/
theorem ell_zero (h0 : r i.succ = 0) :
    ∑ g ∈ Finset.range (nH r i + 1).toNat, (stepB K (true, i) q r hF).left (ccwLH r i (-nH r i - 1 + g)) * xiStep K (true, i) q r hF ^ (nH r i - g).toNat = 0 := by
  have hn : nH r i = (r i.castSucc : ℤ) - r i.succ := rfl
  have hc := Eleft_charpoly (K := K) i (hF : StepR (true, i) q r)
  rw [show (nH r i + 1).toNat = r i.castSucc + 1 by omega]
  rw [← hc]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' := Finset.mem_range.1 hg
  rw [ccwLH_eq, if_pos (by omega), show (-nH r i - 1 + (g : ℤ) + 1 + nH r i).toNat = g by omega,
    PhiH_of_succ_zero _ _ h0, map_mul, map_pow, map_neg, map_one, mul_assoc,
    show (nH r i - (g : ℤ)).toNat = r i.castSucc - g by omega]

theorem corr_zero (h0 : r i.succ = 0) (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) : ∑ g ∈ Finset.range (nH r i + 1).toNat, (dcV K i hF Y (0) ((nH r i - g).toNat) ((ccwLH r i (-nH r i - 1 + g))) (z) - dcV K i hF Y ((nH r i - g).toNat) (0) ((ccwLH r i (-nH r i - 1 + g))) (z)) = 0 := by
  have hs := ell_zero (K := K) i hF h0
  simp only [← cupEF_capEF_term, ← term_cupEF_capEF]
  rw [Finset.sum_sub_distrib, ← BHom.map_sum, ← BHom.map_sum, ← Finset.sum_mul, ← Finset.sum_mul,
    ← BRing.sum_tmul, hs, BRing.zero_tmul, zero_mul, zero_mul, BHom.map_zero, BHom.map_zero,
    sub_zero]

/-- The top term of the double sum at `1`. -/
theorem dcV_one_top (a : ℕ) (b : H K r) (y : Y.T) :
    dcV K i hF Y (a) (q i.castSucc) (b) (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y 1 y)) = BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2 ^ a) 1) * cupEFW K i (hF : StepR (true, i) q r) hF Y (Y.left b * y) := by
  simp only [dcV]
  rw [BRing.tmul_mul_tmul, mul_one, one_mul, capEFW_tmul, capEFP_xi_pow i _ _ _ le_rfl,
    if_pos rfl, map_one, one_mul]

/-- **`eq_ident_decomp` on `E_i F_i` when `F_i E_i 1_λ = 0`** (`r_{i+1} = 0`, so `n = r_i`):
`1 = ∑_{f=0}^{n-1} ∑_{g=0}^{f}` (cup with `n - 1 - f` dots on `F_i`) `∘ Γ(ccwL (-n - 1 + g)) ∘`
(`f - g` dots on `E_i`, cap). -/
theorem decompEF_W_top (h0 : r i.succ = 0) (z : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T) :
    z = ∑ f ∈ Finset.range (nH r i).toNat, ∑ g ∈ Finset.range (f + 1),
      dcW K i hF Y ((nH r i).toNat - 1 - f) (f - g) (ccwLH r i (-nH r i - 1 + g)) z := by
  have hri : r i.castSucc = q i.castSucc + 1 := by rw [← hF.1, raise_castSucc]
  have hqs : q i.succ = 1 := by
    have := hF.2
    have e : r i.succ = q i.succ - 1 := by rw [← hF.1, raise_succ]
    omega
  have hn : nH r i = (r i.castSucc : ℤ) - r i.succ := rfl
  let Φ : ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T →+ ((stepB K (true, i) q r hF).tensor ((stepB K (false, i) r q hF).tensor Y)).T := ∑ f ∈ Finset.range (nH r i).toNat, ∑ g ∈ Finset.range (f + 1),
      (dcW K i hF Y ((nH r i).toNat - 1 - f) (f - g) (ccwLH r i (-nH r i - 1 + g))).toAddHom
  have hΦ : ∀ z, Φ z = ∑ f ∈ Finset.range (nH r i).toNat, ∑ g ∈ Finset.range (f + 1), dcV K i hF Y ((nH r i).toNat - 1 - f) (f - g) ((ccwLH r i (-nH r i - 1 + g))) (z) := fun z => by
    simp only [Φ, AddMonoidHom.finset_sum_apply, BHom.toAddHom_apply, dcW_apply]
    rfl
  have key := ext_two (Y := Y) (eXi K i q hF.2) (eXi K i q hF.2) (stepE_spanned i (hF : StepR (true, i) q r))
    (stepF_spanned i hF) Φ (AddMonoidHom.id _) (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) (eXi K i q hF.2) 1) (BRing.tmul (stepB K (true, i) q r hF) ((stepB K (false, i) r q hF).tensor Y) 1 (BRing.tmul (stepB K (false, i) r q hF) Y (eXi K i q hF.2) 1))
    (fun z => ?_) (fun z => rfl) (fun z => ?_) (fun z => rfl) (fun y => ?_) z
  · exact key.symm.trans (hΦ z)
  · rw [hΦ, hΦ, sumEF_dot i hF Y _ (dcV_dotE_in i hF Y) (dcV_dotE_out i hF Y), ← corr_eq,
      corr_zero i hF Y h0, add_zero]
  · rw [hΦ, hΦ, sumEF_dot i hF Y _ (dcV_dotF_in i hF Y) (dcV_dotF_out i hF Y), ← corr_eq,
      corr_zero i hF Y h0, add_zero]
  · rw [hΦ, AddMonoidHom.id_apply, show (nH r i).toNat = q i.castSucc + 1 by omega,
      Finset.sum_eq_single (q i.castSucc)]
    · rw [Finset.sum_eq_single 0]
      · rw [Nat.sub_zero, show q i.castSucc + 1 - 1 - q i.castSucc = 0 by omega, dcV_one_top,
          pow_zero, tmul_one_one_one, one_mul, Nat.cast_zero, add_zero,
          show -nH r i - 1 = -nH r i - 1 + 0 by ring, ccwLH_eq, if_pos (by omega),
          show (-nH r i - 1 + 0 + 1 + nH r i).toNat = 0 by omega, PhiH_zero, map_one, one_mul,
          cupEFW_apply'', show dEF i (hF : StepR (true, i) q r) = 0 by rw [dEF_eq]; omega,
          Finset.sum_range_one, pow_zero, pow_zero, one_mul, x_zero, map_one, one_mul]
      · intro g hg hg0
        have hg' := Finset.mem_range.1 hg
        exact dcV_one i hF Y _ _ _ (by omega) y
      · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos _)) h
    · intro f hf hfq
      have hf' := Finset.mem_range.1 hf
      refine Finset.sum_eq_zero fun g hg => ?_
      have hg' := Finset.mem_range.1 hg
      exact dcV_one i hF Y _ _ _ (by omega) y
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) h

/-! ### The mirror statement on `F_i E_i` -/

/-- **The cap after `crossr` is a curl**: `cap_{EF} ∘ crossr = cap_{FE} ∘ (F_i ⊗ curlR)`. -/
theorem capEFW_crossrW (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    capEFW K i (hF : StepR (true, i) q r) hF Y (crossrW K i i hE' hE' hF hF Y w) = capFEW K i (hE' : StepR (true, i) r q') hE' Y (BHom.whiskerLeft (stepB K (false, i) q' r hE') (curlRW K i hE' (hF : StepR (true, i) q r) Y) w) := by
  simp only [crossrW, curlRW, BHom.comp_apply, BHom.whiskerLeft_comp]
  exact (capFEW_natural i (hE' : StepR (true, i) r q') hE' (capEFW K i (hF : StepR (true, i) q r) hF Y) _).symm

/-- **The cup before `crossl` is a curl**: `crossl ∘ cup_{EF} = (F_i ⊗ curlR) ∘ cup_{FE}`. -/
theorem crosslW_cupEFW (y : Y.T) :
    crosslW K i i hF hF hE' hE' Y (cupEFW K i (hF : StepR (true, i) q r) hF Y y) = BHom.whiskerLeft (stepB K (false, i) q' r hE') (curlRW K i hE' (hF : StepR (true, i) q r) Y) (cupFEW K i (hE' : StepR (true, i) r q') hE' Y y) := by
  simp only [crosslW, curlRW, BHom.comp_apply, BHom.whiskerLeft_comp]
  rw [← cupFEW_natural i (hE' : StepR (true, i) r q') hE' (cupEFW K i (hF : StepR (true, i) q r) hF Y) y]

variable (K) in
/-- The composite `(cup with a dots on E_i) ∘ b ∘ (c dots on F_i, then cap)` on `F_i E_i Y`. -/
def dcVFE (a c : ℕ) (b : H K r) (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T :=
  BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2 ^ a) 1) * cupFEW K i (hE' : StepR (true, i) r q') hE' Y (Y.left b * capFEW K i (hE' : StepR (true, i) r q') hE' Y (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) (eXi K i r hE'.2 ^ c) 1 * w))

theorem dcVFE_add (a c : ℕ) (b : H K r) (w w' : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    dcVFE K i hE' Y (a) (c) (b) (w + w') = dcVFE K i hE' Y (a) (c) (b) (w) + dcVFE K i hE' Y (a) (c) (b) (w') := by
  simp only [dcVFE]
  rw [mul_add, BHom.map_add, mul_add, BHom.map_add, mul_add]

theorem dcVFE_dotF_in (a c : ℕ) (b : H K r) (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    dcVFE K i hE' Y (a) (c) (b) (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) (eXi K i r hE'.2) 1 * w) = dcVFE K i hE' Y (a) (c + 1) (b) (w) := by
  simp only [dcVFE]
  rw [← mul_assoc, BRing.tmul_mul_tmul, mul_one, ← pow_succ]

theorem dcVFE_dotE_in (a c : ℕ) (b : H K r) (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    dcVFE K i hE' Y (a) (c) (b) (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2) 1) * w) = dcVFE K i hE' Y (a) (c + 1) (b) (w) := by
  simp only [dcVFE]
  rw [mul_left_comm, capFEW_slide, ← mul_assoc, BRing.tmul_mul_tmul, mul_one, ← pow_succ']

theorem dcVFE_dotE_out (a c : ℕ) (b : H K r) (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2) 1) * dcVFE K i hE' Y (a) (c) (b) (w) = dcVFE K i hE' Y (a + 1) (c) (b) (w) := by
  simp only [dcVFE]
  rw [← mul_assoc, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, mul_one, ← pow_succ']

theorem dcVFE_dotF_out (a c : ℕ) (b : H K r) (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) (eXi K i r hE'.2) 1 * dcVFE K i hE' Y (a) (c) (b) (w) = dcVFE K i hE' Y (a + 1) (c) (b) (w) := by
  simp only [dcVFE]
  rw [mul_left_comm, cupFEW_slide, ← mul_assoc, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul,
    one_mul, mul_one, ← pow_succ]

theorem curlR_elt_mul (k : ℕ) (b : H K r) (v : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2 ^ k) (Y.left b)) * v =
      BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y 1 (Y.left b)) * (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2 ^ k) 1) * v) := by
  rw [← mul_assoc, BRing.tmul_mul_tmul, BRing.tmul_mul_tmul, one_mul, one_mul, mul_one]

/-- The cup after the cap after `crossr`. -/
theorem cupFE_capEF_crossr (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    cupFEW K i (hE' : StepR (true, i) r q') hE' Y (capEFW K i (hF : StepR (true, i) q r) hF Y (crossrW K i i hE' hE' hF hF Y w)) =
      -∑ f ∈ Finset.range (-nH r i + 1).toNat, dcVFE K i hE' Y (0) ((-nH r i - f).toNat) ((cwLH r i (nH r i - 1 + f))) (w) := by
  rw [capEFW_crossrW, curlRW_eq_curlRHS, BHom.whiskerLeft_mulB, BHom.mulB_apply, BRing.tmul_neg,
    neg_mul, BHom.map_neg, BHom.map_neg, BRing.tmul_sum, Finset.sum_mul, BHom.map_sum,
    BHom.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [curlR_elt_mul, capFEW_mul, capFEW_slide, dcVFE, pow_zero, ← BRing.one_eq, ← BRing.one_eq,
    one_mul]

/-- `crossl` after the cup after the cap. -/
theorem crossl_cupEF_capFE (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    crosslW K i i hF hF hE' hE' Y (cupEFW K i (hF : StepR (true, i) q r) hF Y (capFEW K i (hE' : StepR (true, i) r q') hE' Y w)) =
      -∑ f ∈ Finset.range (-nH r i + 1).toNat, dcVFE K i hE' Y ((-nH r i - f).toNat) (0) ((cwLH r i (nH r i - 1 + f))) (w) := by
  rw [crosslW_cupEFW, curlRW_eq_curlRHS, BHom.whiskerLeft_mulB, BHom.mulB_apply, BRing.tmul_neg,
    neg_mul, BRing.tmul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [curlR_elt_mul, mul_left_comm, ← cupFEW_mul, dcVFE, pow_zero, ← BRing.one_eq, one_mul]

/-- **`crossl ∘ crossr` and the dot of `F_i`**. -/
theorem crosslr_dotF (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    crosslW K i i hF hF hE' hE' Y (crossrW K i i hE' hE' hF hF Y (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) (eXi K i r hE'.2) 1 * w)) = BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) (eXi K i r hE'.2) 1 * crosslW K i i hF hF hE' hE' Y (crossrW K i i hE' hE' hF hF Y w) + ∑ f ∈ Finset.range (-nH r i + 1).toNat, (dcVFE K i hE' Y (0) ((-nH r i - f).toNat) ((cwLH r i (nH r i - 1 + f))) (w) - dcVFE K i hE' Y ((-nH r i - f).toNat) (0) ((cwLH r i (nH r i - 1 + f))) (w)) := by
  rw [crossrW_same_dotF, BHom.map_add, crosslW_same_dotF, cupFE_capEF_crossr, crossl_cupEF_capFE,
    Finset.sum_sub_distrib]
  abel

/-- **`crossl ∘ crossr` and the dot of `E_i`**. -/
theorem crosslr_dotE (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    crosslW K i i hF hF hE' hE' Y (crossrW K i i hE' hE' hF hF Y (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2) 1) * w)) = BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2) 1) * crosslW K i i hF hF hE' hE' Y (crossrW K i i hE' hE' hF hF Y w) + ∑ f ∈ Finset.range (-nH r i + 1).toNat, (dcVFE K i hE' Y (0) ((-nH r i - f).toNat) ((cwLH r i (nH r i - 1 + f))) (w) - dcVFE K i hE' Y ((-nH r i - f).toNat) (0) ((cwLH r i (nH r i - 1 + f))) (w)) := by
  rw [crossrW_same_dotE, BHom.map_add, crosslW_same_dotE, cupFE_capEF_crossr, crossl_cupEF_capFE,
    Finset.sum_sub_distrib]
  abel

theorem sumFE_dot (v : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T)
    (hin : ∀ a c b w, dcVFE K i hE' Y (a) (c) (b) (v * w) = dcVFE K i hE' Y (a) (c + 1) (b) (w))
    (hout : ∀ a c b w, v * dcVFE K i hE' Y (a) (c) (b) (w) = dcVFE K i hE' Y (a + 1) (c) (b) (w)) (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    ∑ f ∈ Finset.range (-nH r i).toNat, ∑ g ∈ Finset.range (f + 1), dcVFE K i hE' Y ((-nH r i).toNat - 1 - f) (f - g) ((cwLH r i (nH r i - 1 + g))) (v * w) = v * ∑ f ∈ Finset.range (-nH r i).toNat, ∑ g ∈ Finset.range (f + 1), dcVFE K i hE' Y ((-nH r i).toNat - 1 - f) (f - g) ((cwLH r i (nH r i - 1 + g))) (w) + ∑ g ∈ Finset.range (-nH r i).toNat, (dcVFE K i hE' Y (0) ((-nH r i).toNat - g) ((cwLH r i (nH r i - 1 + g))) (w) - dcVFE K i hE' Y ((-nH r i).toNat - g) (0) ((cwLH r i (nH r i - 1 + g))) (w)) := by
  rw [← sum_tele (-nH r i).toNat (fun g a c => dcVFE K i hE' Y (a) (c) ((cwLH r i (nH r i - 1 + g))) (w)), Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hf' := Finset.mem_range.1 hf
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hin, hout, show (-nH r i).toNat - 1 - f + 1 = (-nH r i).toNat - f by omega]
  abel

theorem corrF_eq (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) : ∑ f ∈ Finset.range (-nH r i + 1).toNat, (dcVFE K i hE' Y (0) ((-nH r i - f).toNat) ((cwLH r i (nH r i - 1 + f))) (w) - dcVFE K i hE' Y ((-nH r i - f).toNat) (0) ((cwLH r i (nH r i - 1 + f))) (w)) = ∑ g ∈ Finset.range (-nH r i).toNat, (dcVFE K i hE' Y (0) ((-nH r i).toNat - g) ((cwLH r i (nH r i - 1 + g))) (w) - dcVFE K i hE' Y ((-nH r i).toNat - g) (0) ((cwLH r i (nH r i - 1 + g))) (w)) := by
  by_cases hn : 0 ≤ -nH r i
  · rw [show (-nH r i + 1).toNat = (-nH r i).toNat + 1 by omega, Finset.sum_range_succ,
      show (-nH r i - ((-nH r i).toNat : ℕ)).toNat = 0 by omega, sub_self, add_zero]
    refine Finset.sum_congr rfl fun g hg => ?_
    have hg' := Finset.mem_range.1 hg
    rw [show (-nH r i - (g : ℕ)).toNat = (-nH r i).toNat - g by omega]
  · rw [show (-nH r i + 1).toNat = 0 by omega, show (-nH r i).toNat = 0 by omega, Finset.sum_range_zero,
      Finset.sum_range_zero]

theorem dcVFE_one (a c : ℕ) (b : H K r) (hc : c + 1 < r i.succ) (y : Y.T) :
    dcVFE K i hE' Y (a) (c) (b) (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y 1 y)) = 0 := by
  simp only [dcVFE]
  rw [← capFEW_slide, BRing.tmul_mul_tmul, one_mul, BRing.tmul_mul_tmul, mul_one, one_mul,
    capFEW_tmul, capFEP_xi_pow i _ _ _ hc.le, if_neg hc.ne, map_zero, zero_mul, mul_zero,
    BHom.map_zero, mul_zero]

variable (K) in
/-- `Γ_N` of `(cup with a dots on E_i) ∘ b ∘ (c dots on F_i, then cap)` on `F_i E_i Y`, `b ∈ H_r`
the image of a bubble in the region `r` (`dotCapFE`, `cupDotFE` of Definition 3.1). -/
def dcWFE (a c : ℕ) (b : H K r) : BHom ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)) ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)) :=
  (BHom.mulB (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2 ^ a) 1))).comp ((cupFEW K i (hE' : StepR (true, i) r q') hE' Y).comp ((BHom.mulB (Y.left b)).comp
    ((capFEW K i (hE' : StepR (true, i) r q') hE' Y).comp (BHom.mulB (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) (eXi K i r hE'.2 ^ c) 1)))))

theorem dcWFE_apply (a c : ℕ) (b : H K r) (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    dcWFE K i hE' Y a c b w = dcVFE K i hE' Y (a) (c) (b) (w) := rfl

/-- **`eq_ident_decomp` on `F_i E_i`, second identity, under `Γ_N`** (KL III Definition 3.1,
`Rel.decompFE`; Proposition 6.3): on `F_i E_i Y` with `E_i F_i 1_λ ≠ 0` and `n = ⟨i, λ⟩`,
`1 = -crossl ∘ crossr + ∑_{f=0}^{-n-1} ∑_{g=0}^{f}` (cup with `-n - 1 - f` dots on `E_i`)
`∘ Γ(cwL (n - 1 + g)) ∘` (`f - g` dots on `F_i`, cap), the (real or fake) bubbles acting in the
region `λ` (`cwLH`). -/
theorem decompFE_W (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    w = -crosslW K i i hF hF hE' hE' Y (crossrW K i i hE' hE' hF hF Y w) + ∑ f ∈ Finset.range (-nH r i).toNat, ∑ g ∈ Finset.range (f + 1),
      dcWFE K i hE' Y ((-nH r i).toNat - 1 - f) (f - g) (cwLH r i (nH r i - 1 + g)) w := by
  simp only [dcWFE_apply]
  have hri : r i.castSucc = q i.castSucc + 1 := by rw [← hF.1, raise_castSucc]
  have hn : nH r i = (r i.castSucc : ℤ) - r i.succ := rfl
  let Φ : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T →+ ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T := -((crosslW K i i hF hF hE' hE' Y).comp (crossrW K i i hE' hE' hF hF Y)).toAddHom +
    ∑ f ∈ Finset.range (-nH r i).toNat, ∑ g ∈ Finset.range (f + 1),
      (dcWFE K i hE' Y ((-nH r i).toNat - 1 - f) (f - g) (cwLH r i (nH r i - 1 + g))).toAddHom
  have hΦ : ∀ w, Φ w = -crosslW K i i hF hF hE' hE' Y (crossrW K i i hE' hE' hF hF Y w) + ∑ f ∈ Finset.range (-nH r i).toNat, ∑ g ∈ Finset.range (f + 1), dcVFE K i hE' Y ((-nH r i).toNat - 1 - f) (f - g) ((cwLH r i (nH r i - 1 + g))) (w) := fun w => by
    simp only [Φ, AddMonoidHom.add_apply, AddMonoidHom.neg_apply, AddMonoidHom.finset_sum_apply,
      BHom.toAddHom_apply, BHom.comp_apply, dcWFE_apply]
    rfl
  have key := ext_two (Y := Y) (eXi K i r hE'.2) (eXi K i r hE'.2) (stepF_spanned i (hE' : StepR (false, i) q' r))
    (stepE_spanned i hE') Φ (AddMonoidHom.id _) (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) (eXi K i r hE'.2) 1) (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2) 1))
    (fun w => ?_) (fun w => rfl) (fun w => ?_) (fun w => rfl) (fun y => ?_) w
  · rw [← hΦ]; exact key.symm
  · rw [hΦ, hΦ, crosslr_dotF, sumFE_dot i hE' Y _ (dcVFE_dotF_in i hE' Y) (dcVFE_dotF_out i hE' Y),
      corrF_eq]
    rw [mul_add, mul_neg]
    abel
  · rw [hΦ, hΦ, crosslr_dotE, sumFE_dot i hE' Y _ (dcVFE_dotE_in i hE' Y) (dcVFE_dotE_out i hE' Y),
      corrF_eq]
    rw [mul_add, mul_neg]
    abel
  · rw [hΦ, crossrW_same_one, BHom.map_neg, crosslW_same_one, neg_neg, AddMonoidHom.id_apply]
    rw [Finset.sum_eq_zero fun f hf => Finset.sum_eq_zero fun g hg => ?_, add_zero]
    have hf' := Finset.mem_range.1 hf
    have hg' := Finset.mem_range.1 hg
    exact dcVFE_one i hE' Y _ _ _ (by omega) y

theorem cupFE_capFE_term (b : H K r) (k : ℕ) (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    cupFEW K i (hE' : StepR (true, i) r q') hE' Y (capFEW K i (hE' : StepR (true, i) r q') hE' Y (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2 ^ k) (Y.left b)) * w)) = dcVFE K i hE' Y (0) (k) (b) (w) := by
  rw [curlR_elt_mul, capFEW_mul, capFEW_slide, dcVFE, pow_zero, ← BRing.one_eq, ← BRing.one_eq,
    one_mul]

theorem term_cupFE_capFE (b : H K r) (k : ℕ) (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2 ^ k) (Y.left b)) * cupFEW K i (hE' : StepR (true, i) r q') hE' Y (capFEW K i (hE' : StepR (true, i) r q') hE' Y w) = dcVFE K i hE' Y (k) (0) (b) (w) := by
  rw [curlR_elt_mul, mul_left_comm, ← cupFEW_mul, dcVFE, pow_zero, ← BRing.one_eq, one_mul]

/-- **Without `E_i F_i 1_λ`, the bubble terms of the dot slides cancel** (`r_i = 0`). -/
theorem ellR_zero (h0 : r i.castSucc = 0) :
    ∑ f ∈ Finset.range (-nH r i + 1).toNat,
      BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2 ^ (-nH r i - f).toNat) (Y.left (cwLH r i (nH r i - 1 + f))) = 0 := by
  have hn : nH r i = (r i.castSucc : ℤ) - r i.succ := rfl
  have hc := Eright_charpoly (K := K) i hE'
  have e : ∀ f ∈ Finset.range (-nH r i + 1).toNat,
      BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2 ^ (-nH r i - f).toNat) (Y.left (cwLH r i (nH r i - 1 + f))) =
        BRing.tmul (stepB K (true, i) r q' hE') Y ((-1) ^ f * ((stepB K (true, i) r q' hE').right (x K r i.succ f) *
          xiStep K (true, i) r q' hE' ^ (r i.succ - f))) 1 := by
    intro f hf
    have hf' := Finset.mem_range.1 hf
    rw [← mul_one (Y.left _), ← BRing.tmul_balance, cwLH_eq, if_pos (by omega),
      show (nH r i - 1 + (f : ℤ) + 1 - nH r i).toNat = f by omega, PsiH_of_castSucc_zero _ _ h0,
      map_mul, map_pow, map_neg, map_one, mul_assoc,
      show (-nH r i - (f : ℤ)).toNat = r i.succ - f by omega]
    rfl
  rw [Finset.sum_congr rfl e, ← BRing.sum_tmul, show (-nH r i + 1).toNat = r i.succ + 1 by omega,
    hc, BRing.zero_tmul]

theorem corrF_zero (h0 : r i.castSucc = 0) (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) : ∑ f ∈ Finset.range (-nH r i + 1).toNat, (dcVFE K i hE' Y (0) ((-nH r i - f).toNat) ((cwLH r i (nH r i - 1 + f))) (w) - dcVFE K i hE' Y ((-nH r i - f).toNat) (0) ((cwLH r i (nH r i - 1 + f))) (w)) = 0 := by
  have hs := ellR_zero (K := K) i hE' Y h0
  simp only [← cupFE_capFE_term, ← term_cupFE_capFE]
  rw [Finset.sum_sub_distrib, ← BHom.map_sum, ← BHom.map_sum, ← Finset.sum_mul, ← Finset.sum_mul,
    ← BRing.tmul_sum, hs, BRing.tmul_zero, zero_mul, zero_mul, BHom.map_zero, BHom.map_zero,
    sub_zero]

/-- The top term of the double sum at `1`. -/
theorem dcVFE_one_top (a : ℕ) (b : H K r) (y : Y.T) :
    dcVFE K i hE' Y (a) (r i.succ - 1) (b) (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y 1 y)) = BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2 ^ a) 1) * cupFEW K i (hE' : StepR (true, i) r q') hE' Y (Y.left b * y) := by
  have hr := hE'.2
  simp only [dcVFE]
  rw [← capFEW_slide, BRing.tmul_mul_tmul, one_mul, BRing.tmul_mul_tmul, mul_one, one_mul,
    capFEW_tmul, capFEP_xi_pow i _ _ _ (by omega), if_pos (by omega), map_one, one_mul]

/-- **`eq_ident_decomp` on `F_i E_i` when `E_i F_i 1_λ = 0`** (`r_i = 0`, so `n = -r_{i+1}`):
`1 = ∑_{f=0}^{-n-1} ∑_{g=0}^{f}` (cup with `-n - 1 - f` dots on `E_i`) `∘ Γ(cwL (n - 1 + g)) ∘`
(`f - g` dots on `F_i`, cap). -/
theorem decompFE_W_top (h0 : r i.castSucc = 0) (w : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T) :
    w = ∑ f ∈ Finset.range (-nH r i).toNat, ∑ g ∈ Finset.range (f + 1),
      dcWFE K i hE' Y ((-nH r i).toNat - 1 - f) (f - g) (cwLH r i (nH r i - 1 + g)) w := by
  simp only [dcWFE_apply]
  have hr := hE'.2
  have hn : nH r i = (r i.castSucc : ℤ) - r i.succ := rfl
  let Φ : ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T →+ ((stepB K (false, i) q' r hE').tensor ((stepB K (true, i) r q' hE').tensor Y)).T := ∑ f ∈ Finset.range (-nH r i).toNat, ∑ g ∈ Finset.range (f + 1),
      (dcWFE K i hE' Y ((-nH r i).toNat - 1 - f) (f - g) (cwLH r i (nH r i - 1 + g))).toAddHom
  have hΦ : ∀ w, Φ w = ∑ f ∈ Finset.range (-nH r i).toNat, ∑ g ∈ Finset.range (f + 1), dcVFE K i hE' Y ((-nH r i).toNat - 1 - f) (f - g) ((cwLH r i (nH r i - 1 + g))) (w) := fun w => by
    simp only [Φ, AddMonoidHom.finset_sum_apply, BHom.toAddHom_apply, dcWFE_apply]
    rfl
  have key := ext_two (Y := Y) (eXi K i r hE'.2) (eXi K i r hE'.2) (stepF_spanned i (hE' : StepR (false, i) q' r))
    (stepE_spanned i hE') Φ (AddMonoidHom.id _) (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) (eXi K i r hE'.2) 1) (BRing.tmul (stepB K (false, i) q' r hE') ((stepB K (true, i) r q' hE').tensor Y) 1 (BRing.tmul (stepB K (true, i) r q' hE') Y (eXi K i r hE'.2) 1))
    (fun w => ?_) (fun w => rfl) (fun w => ?_) (fun w => rfl) (fun y => ?_) w
  · exact key.symm.trans (hΦ w)
  · rw [hΦ, hΦ, sumFE_dot i hE' Y _ (dcVFE_dotF_in i hE' Y) (dcVFE_dotF_out i hE' Y), ← corrF_eq,
      corrF_zero i hE' Y h0, add_zero]
  · rw [hΦ, hΦ, sumFE_dot i hE' Y _ (dcVFE_dotE_in i hE' Y) (dcVFE_dotE_out i hE' Y), ← corrF_eq,
      corrF_zero i hE' Y h0, add_zero]
  · rw [hΦ, AddMonoidHom.id_apply, show (-nH r i).toNat = (r i.succ - 1) + 1 by omega,
      Finset.sum_eq_single (r i.succ - 1)]
    · rw [Finset.sum_eq_single 0]
      · rw [Nat.sub_zero, show r i.succ - 1 + 1 - 1 - (r i.succ - 1) = 0 by omega, dcVFE_one_top,
          pow_zero, ← BRing.one_eq, ← BRing.one_eq, one_mul, Nat.cast_zero, add_zero, cwLH_eq,
          if_pos (by omega), show (nH r i - 1 + 1 - nH r i).toNat = 0 by omega, PsiH_zero,
          map_one, one_mul, cupFEW_apply',
          show dFE i (hE' : StepR (true, i) r q') = 0 by rw [dFE_eq]; omega,
          Finset.sum_range_one, pow_zero, pow_zero, one_mul, xsFE_eq, x_zero, map_one]
      · intro g hg hg0
        have hg' := Finset.mem_range.1 hg
        exact dcVFE_one i hE' Y _ _ _ (by omega) y
      · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos _)) h
    · intro f hf hfq
      have hf' := Finset.mem_range.1 hf
      refine Finset.sum_eq_zero fun g hg => ?_
      have hg' := Finset.mem_range.1 hg
      exact dcVFE_one i hE' Y _ _ _ (by omega) y
    · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) h

end SameSideways

end Categorification.KL3.Diagram.Signed

end
