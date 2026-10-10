/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicDiv

/-!
# The polynomial algebra behind Kang–Kashiwara Proposition 5.4

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, §5.2: Lemma 5.5 and Proposition 5.4, and
the two consequences for the map `A` used at the end of the proof of Theorem 5.2.

In KK, `A : R^Λ(β)[t_i] → R^Λ(β)[t_i]` is a right `R^Λ(β)`-linear map obtained by a diagram chase,
with `A(a t_i) − A(a) t_i ∈ R^Λ(β)` for all `a` (KK (5.11)) and `A(t_i^k S) = γ^{-1} t_i^k F`
(KK (5.10)), where `S` and `F` are central monic polynomials of degrees `2p` and
`⟨h_i, λ⟩ + 2p`. Here everything is stated for an arbitrary ring `R`, an additive map
`A : R[t] → R[t]` and an arbitrary unit `c` of a commutative ring `k` over which `R` is an algebra:

* `degree_sub_mul_lt` (KK (5.12)): `A(a f) − A(a) f` has degree `< deg f`;
* `apply_X_pow_eq` (**KK Lemma 5.5**): `A(t^k) = c · ((t^k F) /ₘ S)`;
* `phi_spec` (**KK Proposition 5.4**): with `e = deg S − deg F` and `l = deg F − deg S`
  (truncated subtraction), `A(t^k) = 0` for `k < e`, and for `k ≥ e`, `c⁻¹ A(t^k)` is monic of
  degree `k − e + l = k + deg F − deg S`;
* triangularity of such a map (`natDegree_apply`, `apply_eq_zero_iff`,
  `exists_sub_apply_degree_lt`, `degree_lt_of_apply_add_eq_zero`): `A(p) = 0` iff `deg p < e`;
  every polynomial is `A(p)` plus a polynomial of degree `< l`, uniquely modulo `ker A`. For
  `⟨h_i, λ⟩ ≥ 0` (`e = 0`) this says `A` is injective and `R[t] = A(R[t]) ⊕ R[t]_{< l}`; for
  `⟨h_i, λ⟩ ≤ 0` (`l = 0`) that `A` is surjective with kernel `R[t]_{< e}`, as used at the end of
  KK's proof of Theorem 5.2.
-/

namespace Categorification.KLR.PhiAlg

open Polynomial

section PhiAbstract

variable {R : Type*} [Ring R] {k : Type*} [CommRing k] [Algebra k R]

theorem degree_C_mul_le' (r : R) (p : R[X]) : (C r * p).degree ≤ p.degree := by
  rw [degree_le_iff_coeff_zero]
  intro n hn
  rw [coeff_C_mul, coeff_eq_zero_of_degree_lt hn, mul_zero]

theorem degree_mul_le_of_degree_le_zero {p q : R[X]} (hp : p.degree ≤ 0) :
    (p * q).degree ≤ q.degree := by
  rw [eq_C_of_degree_le_zero hp]; exact degree_C_mul_le' _ _

variable (A : R[X] →+ R[X])

/-- **KK (5.12)**: if `A` is right `R`-linear and `A(a t) − A(a) t` is constant for every `a`, then
`A(a f) − A(a) f` has degree `< m` whenever `deg f ≤ m`. -/
theorem degree_sub_mul_lt (hC : ∀ p (r : R), A (p * C r) = A p * C r)
    (hX : ∀ p, (A (p * X) - A p * X).degree ≤ 0) :
    ∀ (m : ℕ) (f : R[X]), f.natDegree ≤ m → ∀ p, (A (p * f) - A p * f).degree < (m : WithBot ℕ) := by
  intro m
  induction m with
  | zero =>
    intro f hf p
    rw [eq_C_of_natDegree_le_zero hf, hC, sub_self, degree_zero]
    exact WithBot.bot_lt_coe 0
  | succ m ih =>
    intro f hf p
    have hd : f.divX.natDegree ≤ m := by
      rw [natDegree_divX_eq_natDegree_tsub_one]; omega
    have hsplit : A (p * f) - A p * f =
        (A ((p * X) * f.divX) - A (p * X) * f.divX) + (A (p * X) - A p * X) * f.divX := by
      conv_lhs => rw [← divX_mul_X_add f]
      rw [mul_add, map_add, hC, mul_add, ← (commute_X f.divX).eq, ← mul_assoc]
      noncomm_ring
    rw [hsplit]
    refine (degree_add_le _ _).trans_lt (max_lt ((ih _ hd _).trans ?_) ?_)
    · exact WithBot.coe_lt_coe.2 (Nat.lt_succ_self m)
    · refine (degree_mul_le_of_degree_le_zero (hX p)).trans_lt ?_
      exact (degree_le_natDegree.trans (WithBot.coe_le_coe.2 hd)).trans_lt
        (WithBot.coe_lt_coe.2 (Nat.lt_succ_self m))

variable {S F : R[X]} (c : kˣ)

/-- **KK Lemma 5.5**: `A(t^k) = c · ((t^k F) /ₘ S)`. -/
theorem apply_X_pow_eq (hC : ∀ p (r : R), A (p * C r) = A p * C r)
    (hX : ∀ p, (A (p * X) - A p * X).degree ≤ 0) (hS : S.Monic) (hScen : ∀ q, Commute q S)
    (hAS : ∀ j : ℕ, A (X ^ j * S) = (c : k) • (X ^ j * F)) (j : ℕ) :
    A (X ^ j) = (c : k) • ((X ^ j * F) /ₘ S) := by
  nontriviality R
  have hlt := degree_sub_mul_lt A hC hX S.natDegree S le_rfl (X ^ j)
  rw [← degree_eq_natDegree hS.ne_zero] at hlt
  have heq : (c : k) • (X ^ j * F) = (A (X ^ j * S) - A (X ^ j) * S) + S * A (X ^ j) := by
    rw [hAS, (hScen (A (X ^ j))).eq]; abel
  calc A (X ^ j) = ((A (X ^ j * S) - A (X ^ j) * S) + S * A (X ^ j)) /ₘ S :=
        (divByMonic_add_mul_of_degree_lt hS _ hlt).symm
    _ = ((c : k) • (X ^ j * F)) /ₘ S := by rw [heq]
    _ = (c : k) • ((X ^ j * F) /ₘ S) := map_smul (divByMonicLin k hS) _ _


/-! ### Triangularity -/

section Triangular

variable (e l : ℕ) (hC : ∀ p (r : R), A (p * C r) = A p * C r)
  (hlow : ∀ j < e, A (X ^ j) = 0)
  (hhigh : ∀ j, e ≤ j → (((c⁻¹ : kˣ) : k) • A (X ^ j)).Monic ∧
    (((c⁻¹ : kˣ) : k) • A (X ^ j)).natDegree = j - e + l)

include hC in
theorem apply_eq_sum (p : R[X]) {N : ℕ} (hN : p.natDegree < N) :
    A p = ∑ j ∈ Finset.range N, A (X ^ j) * C (p.coeff j) := by
  conv_lhs => rw [as_sum_range_C_mul_X_pow' p hN]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← (commute_X_pow (C (p.coeff j)) j).eq, hC]

theorem smul_inv_smul' {M : Type*} [AddCommMonoid M] [Module k M] (q : M) : (c : k) • ((((c⁻¹ : kˣ) : k)) • q) = q := by
  rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

include hlow hhigh in
theorem degree_apply_X_pow_le (j : ℕ) (N : ℕ) (hj : j ≤ N) (hN : e ≤ N) :
    (A (X ^ j)).degree ≤ ((N - e + l : ℕ) : WithBot ℕ) := by
  rcases lt_or_ge j e with hje | hje
  · rw [hlow j hje, degree_zero]; exact bot_le
  · rw [← smul_inv_smul' c (A (X ^ j))]
    refine (degree_smul_le _ _).trans (degree_le_natDegree.trans ?_)
    rw [(hhigh j hje).2]; exact_mod_cast (show j - e + l ≤ N - e + l by omega)

include hC hlow hhigh in
/-- The degree bound in the triangularity of `A`. -/
theorem degree_apply_le (p : R[X]) (N : ℕ) (hp : p.natDegree ≤ N) (hN : e ≤ N) :
    (A p).degree ≤ ((N - e + l : ℕ) : WithBot ℕ) := by
  rw [apply_eq_sum A hC p (Nat.lt_succ_of_le hp)]
  refine (degree_sum_le _ _).trans (Finset.sup_le fun j hj => ?_)
  refine (degree_mul_le _ _).trans ?_
  have hj' : j ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  refine (add_le_add (degree_apply_X_pow_le A c e l hlow hhigh j N hj' hN) degree_C_le).trans ?_
  rw [add_zero]

include hC hlow hhigh in
/-- The top coefficient in the triangularity of `A`. -/
theorem coeff_apply (p : R[X]) (N : ℕ) (hp : p.natDegree ≤ N) (hN : e ≤ N) :
    (A p).coeff (N - e + l) = (c : k) • p.coeff N := by
  rw [apply_eq_sum A hC p (Nat.lt_succ_of_le hp), finsetSum_coeff,
    Finset.sum_eq_single N]
  · have hm := (hhigh N hN).1
    have hd := (hhigh N hN).2
    rw [coeff_mul_C, ← smul_inv_smul' c (A (X ^ N)), coeff_smul, ← hd, hm.coeff_natDegree,
      smul_one_mul]
  · intro j hj hjN
    have hj' : j < N := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) hjN
    rw [coeff_mul_C]
    rcases lt_or_ge j e with hje | hje
    · rw [hlow j hje, coeff_zero, zero_mul]
    · rw [coeff_eq_zero_of_degree_lt, zero_mul]
      exact (degree_apply_X_pow_le A c e l hlow hhigh j j le_rfl hje).trans_lt
        (by exact_mod_cast (show j - e + l < N - e + l by omega))
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self N)) h

theorem smul_ne_zero' {r : R} (hr : r ≠ 0) : (c : k) • r ≠ 0 := by
  intro h
  apply hr
  rw [← one_smul k r, ← Units.val_one, ← inv_mul_cancel c, Units.val_mul, mul_smul, h, smul_zero]

include hC hlow hhigh in
/-- `deg A(p) = deg p − e + l` and the leading coefficient of `A(p)` is `c` times that of `p`,
when `deg p ≥ e`. -/
theorem natDegree_apply (p : R[X]) (hp0 : p ≠ 0) (hN : e ≤ p.natDegree) :
    (A p).natDegree = p.natDegree - e + l ∧ (A p).leadingCoeff = (c : k) • p.leadingCoeff := by
  have hco := coeff_apply A c e l hC hlow hhigh p p.natDegree le_rfl hN
  have hne : (A p).coeff (p.natDegree - e + l) ≠ 0 := by
    rw [hco]; exact smul_ne_zero' c (leadingCoeff_ne_zero.2 hp0)
  have hdeg : (A p).natDegree = p.natDegree - e + l :=
    le_antisymm (natDegree_le_iff_degree_le.2 (degree_apply_le A c e l hC hlow hhigh p _ le_rfl hN))
      (le_natDegree_of_ne_zero hne)
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hco]; rfl⟩

include hC hlow hhigh in
/-- `A(p) = 0` exactly when `deg p < e`. -/
theorem apply_eq_zero_iff (p : R[X]) : A p = 0 ↔ p.degree < e := by
  constructor
  · intro h
    by_contra hp
    push Not at hp
    have hp0 : p ≠ 0 := by rintro rfl; rw [degree_zero] at hp; exact absurd hp (by simp)
    have hN : e ≤ p.natDegree := by
      rw [degree_eq_natDegree hp0] at hp; exact WithBot.coe_le_coe.1 hp
    have := (natDegree_apply A c e l hC hlow hhigh p hp0 hN).2
    rw [h, leadingCoeff_zero] at this
    exact smul_ne_zero' c (leadingCoeff_ne_zero.2 hp0) this.symm
  · intro h
    by_cases hp : p = 0
    · rw [hp, map_zero]
    rw [apply_eq_sum A hC p (N := e) ((natDegree_lt_iff_degree_lt hp).2 h)]
    exact Finset.sum_eq_zero fun j hj => by
      rw [hlow j (Finset.mem_range.1 hj), zero_mul]

include hC hlow hhigh in
/-- Every polynomial is `A(p)` plus a polynomial of degree `< l`. -/
theorem exists_sub_apply_degree_lt (q : R[X]) : ∃ p, (q - A p).degree < l := by
  induction hN : q.natDegree using Nat.strong_induction_on generalizing q with
  | _ N ih =>
    by_cases hq : q.degree < l
    · exact ⟨0, by rwa [map_zero, sub_zero]⟩
    push Not at hq
    have hq0 : q ≠ 0 := by rintro rfl; rw [degree_zero] at hq; exact absurd hq (by simp)
    have hlN : l ≤ N := by
      rw [degree_eq_natDegree hq0, hN] at hq; exact_mod_cast hq
    set p₁ : R[X] := X ^ (N - l + e) * C (((c⁻¹ : kˣ) : k) • q.leadingCoeff) with hp₁
    have hlc : ((c⁻¹ : kˣ) : k) • q.leadingCoeff ≠ 0 := smul_ne_zero' c⁻¹ (leadingCoeff_ne_zero.2 hq0)
    have hp₁0 : p₁ ≠ 0 := by
      rw [hp₁, (commute_X_pow _ _).eq, C_mul_X_pow_eq_monomial]
      exact (monomial_eq_zero_iff _ _).not.2 hlc
    have hp₁d : p₁.natDegree = N - l + e := by
      rw [hp₁, (commute_X_pow _ _).eq, C_mul_X_pow_eq_monomial, natDegree_monomial_eq _ hlc]
    have hp₁l : p₁.leadingCoeff = ((c⁻¹ : kˣ) : k) • q.leadingCoeff := by
      rw [leadingCoeff, hp₁d, hp₁, (commute_X_pow _ _).eq, C_mul_X_pow_eq_monomial,
        coeff_monomial_same]
    obtain ⟨hd, hl⟩ := natDegree_apply A c e l hC hlow hhigh p₁ hp₁0 (by omega)
    rw [hp₁l, smul_inv_smul'] at hl
    rw [hp₁d, show N - l + e - e + l = N by omega] at hd
    have hA0 : A p₁ ≠ 0 := by
      intro h; rw [h, leadingCoeff_zero] at hl; exact leadingCoeff_ne_zero.2 hq0 hl.symm
    by_cases hz : q - A p₁ = 0
    · exact ⟨p₁, by rw [hz, degree_zero]; exact bot_lt_iff_ne_bot.2 (by simp)⟩
    have hlt : (q - A p₁).natDegree < N := by
      have := degree_sub_lt_left (p := q) (q := A p₁) (by
        rw [degree_eq_natDegree hq0, degree_eq_natDegree hA0, hd, hN]) hq0 (by rw [hl])
      rw [degree_eq_natDegree hz, degree_eq_natDegree hq0, hN] at this
      exact_mod_cast this
    obtain ⟨p₂, hp₂⟩ := ih _ hlt (q - A p₁) rfl
    exact ⟨p₁ + p₂, by rwa [map_add, ← sub_sub]⟩

include hC hlow hhigh in
/-- Uniqueness: `A(p) + r = 0` with `deg r < l` forces `deg p < e` (so `A(p) = 0`, `r = 0`). -/
theorem degree_lt_of_apply_add_eq_zero {p r : R[X]} (hr : r.degree < l) (h : A p + r = 0) :
    p.degree < e := by
  by_contra hp
  push Not at hp
  have hp0 : p ≠ 0 := by rintro rfl; rw [degree_zero] at hp; exact absurd hp (by simp)
  have hN : e ≤ p.natDegree := by
    rw [degree_eq_natDegree hp0] at hp; exact_mod_cast hp
  obtain ⟨hd, hl⟩ := natDegree_apply A c e l hC hlow hhigh p hp0 hN
  have hA0 : A p ≠ 0 := by
    intro h0; rw [h0, leadingCoeff_zero] at hl
    exact smul_ne_zero' c (leadingCoeff_ne_zero.2 hp0) hl.symm
  have hAr : A p = -r := eq_neg_of_add_eq_zero_left h
  have : (A p).degree < l := by rw [hAr, degree_neg]; exact hr
  rw [degree_eq_natDegree hA0, hd] at this
  have : p.natDegree - e + l < l := by exact_mod_cast this
  omega

end Triangular

/-! ### KK Proposition 5.4 -/

theorem monic_divByMonic {p : R[X]} (hp : p.Monic) (hS : S.Monic) (h : S.natDegree ≤ p.natDegree) :
    (p /ₘ S).Monic := by
  nontriviality R
  have hsplit := modByMonic_add_div p S
  have hrS := degree_modByMonic_lt p hS
  have hq0 : p /ₘ S ≠ 0 := by
    intro h0
    rw [h0, mul_zero, add_zero] at hsplit
    have : p.degree < S.degree := hsplit ▸ hrS
    rw [degree_eq_natDegree hp.ne_zero, degree_eq_natDegree hS.ne_zero] at this
    exact absurd (by exact_mod_cast this : p.natDegree < S.natDegree) (not_lt.2 h)
  have hlq : (S * (p /ₘ S)).leadingCoeff = (p /ₘ S).leadingCoeff := leadingCoeff_monic_mul hS
  have hSq0 : S * (p /ₘ S) ≠ 0 := by
    intro h0; rw [h0, leadingCoeff_zero] at hlq; exact leadingCoeff_ne_zero.2 hq0 hlq.symm
  have hdeg : (p %ₘ S).degree < (S * (p /ₘ S)).degree := by
    refine hrS.trans_le ?_
    rw [degree_eq_natDegree hS.ne_zero, degree_eq_natDegree hSq0, hS.natDegree_mul' hq0]
    exact_mod_cast Nat.le_add_right _ _
  rw [Monic, ← leadingCoeff_monic_mul hS, ← leadingCoeff_add_of_degree_lt hdeg, hsplit]
  exact hp

/-- **KK Proposition 5.4**, in the form used for Theorem 5.2: with `e = deg S − deg F` and
`l = deg F − deg S` (truncated), `A(t^j) = 0` for `j < e`, and for `j ≥ e`, `c⁻¹ A(t^j)` is monic
of degree `j − e + l = j + deg F − deg S`. -/
theorem phi_spec [Nontrivial R] (hC : ∀ p (r : R), A (p * C r) = A p * C r)
    (hX : ∀ p, (A (p * X) - A p * X).degree ≤ 0) (hS : S.Monic) (hScen : ∀ q, Commute q S)
    (hAS : ∀ j : ℕ, A (X ^ j * S) = (c : k) • (X ^ j * F)) (hF : F.Monic) :
    (∀ j < S.natDegree - F.natDegree, A (X ^ j) = 0) ∧
    (∀ j, S.natDegree - F.natDegree ≤ j → (((c⁻¹ : kˣ) : k) • A (X ^ j)).Monic ∧
      (((c⁻¹ : kˣ) : k) • A (X ^ j)).natDegree =
        j - (S.natDegree - F.natDegree) + (F.natDegree - S.natDegree)) := by
  have hm : ∀ j : ℕ, (X ^ j * F).Monic := fun j => (monic_X_pow j).mul hF
  have hmd : ∀ j : ℕ, (X ^ j * F).natDegree = j + F.natDegree := by
    intro j; rw [(monic_X_pow j).natDegree_mul hF, natDegree_X_pow]
  have hA := apply_X_pow_eq A c hC hX hS hScen hAS
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [hA, (divByMonic_eq_zero_iff hS).2, smul_zero]
    rw [degree_eq_natDegree (hm j).ne_zero, degree_eq_natDegree hS.ne_zero, hmd]
    exact_mod_cast (show j + F.natDegree < S.natDegree by omega)
  · rw [hA, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    refine ⟨monic_divByMonic (hm j) hS (by rw [hmd]; omega), ?_⟩
    rw [natDegree_divByMonic _ hS, hmd]; omega

end PhiAbstract

end Categorification.KLR.PhiAlg
