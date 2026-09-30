/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.GammaIndepPath
import Categorification.Diagrams.KL3.GammaFlagBubble

/-!
# Total Chern classes separating the bubbles

Khovanov–Lauda III (arXiv:0807.3250v1), Lemma `lem_bubbles_same_orient_I` (TeX
`sln-2008-ArXiv.tex` l. 9608–9680): "sums of products of elements of the form
`(x(k)_{i+1,α} - x(k)_{i,α})` … are independent" — the images under `Γ_N` of the generators of
`Π_λ` are algebraically independent in bounded degree.

**This is where KL III's `Γ^G` (equivariant cohomology) matters.** In the (non-equivariant)
cohomology rings `H_k` used here the total Chern classes satisfy `∏_j x_j(t) = 1`, and the
bubble of colour `i` and degree `2α` is (up to sign) the degree-`α` part of `x_{i+1}(t)/x_i(t)`
(`Categorification.KL3.Diagram.Signed.cwRealH`). For `sl_n` (`n = m + 1` blocks) the `m`
ratios then only determine the classes up to a common factor `y` with `y^n = 1`, and in degree
`2` their linear parts satisfy one relation with coefficient `n`: in characteristic dividing `n`
the bubbles are **not** independent in any `H_k` (for `sl_2` in characteristic `2`,
`Γ_N` of the clockwise bubble of degree `2` is `-2 x_{1,1} = 0` for every `N`). KL III avoid this
with equivariant cohomology, where the `x_j(t)` are free. We avoid it by using colours that are
not the last one: we choose the ratios `x_{c+1}/x_c` freely for all colours `c` except the last
one, and absorb the relation `∏_j x_j = 1` into the last block (`chernData`). For `sl_n` this is
applied after the embedding `U(sl_n) → U(sl_{n+1})`, where the last colour of `sl_{n+1}` is not
in the image; the extra block plays the role of the equivariant parameters.

* `Xi`, `zsum`: the Chern roots of the strands (variables of weight `1`) and the free series
  `z_c = ∑_α z_{c,α}` (variables of weight `α + 1`) in the truncated polynomial ring `Tr`.
* `chernData`: total Chern classes of the blocks with `x_{c+1}/x_c = 1 + z_c` if `⟨c, λ⟩ ≥ 0`
  and `x_c/x_{c+1} = 1 + z_c` if `⟨c, λ⟩ < 0`, for every colour `c` but the last (`chernData_succ`).
* `hLift_bubVal`: under the ring map `hLift` of these classes, `Γ_N` of the generator `(c, n)` of
  `Π_λ` (`bubVal`, the real bubble of the orientation of KL III (3.24)) is `(-1)^{n+1} z_{c,n}`.
-/

noncomputable section

namespace Categorification.Flag.Indep

open Categorification.Flag MvPolynomial Categorification.KL3.Diagram.Signed

universe u

variable {K : Type u} [Field K] {M : ℕ}

/-! ## The variables -/

variable (M) in
/-- The variables: the Chern roots `inl t` of the strands and the bubble variables `inr (c, α)`. -/
abbrev VarS : Type := ℕ ⊕ (Fin M × ℕ)

variable (M) in
/-- The weights: `1` for the Chern roots, `α + 1` for `z_{c,α}`. -/
def wS : VarS M → ℕ := Sum.elim (fun _ => 1) (fun p => p.2 + 1)

theorem wS_inl (t : ℕ) : wS M (.inl t) = 1 := rfl

theorem wS_inr (c : Fin M) (n : ℕ) : wS M (.inr (c, n)) = n + 1 := rfl

theorem wS_pos : ∀ v : VarS M, 0 < wS M v
  | .inl _ => Nat.one_pos
  | .inr _ => Nat.succ_pos _

variable (K M) in
/-- The truncated polynomial ring of the argument. -/
abbrev TrS (D : ℕ) : Type u := Tr K (wS M) D

variable {D : ℕ}

variable (K M D) in
/-- The Chern root of the `t`-th strand. -/
def Xi (t : ℕ) : TrS K M D := mkT K (wS M) D (X (.inl t))

theorem goodXi_Xi (t : ℕ) : GoodXi K (wS M) D (Xi K M D t) := by
  refine ⟨?_, ?_⟩
  · rw [Xi, sc_X, wS_inl, pow_one]
  · rw [Xi, aug_mkT]; simp

variable (K M D) in
/-- The free series `z_c = ∑_{α < D} z_{c,α}` (the components of weight `> D` vanish). -/
def zsum (c : Fin M) : TrS K M D := ∑ n ∈ Finset.range D, mkT K (wS M) D (X (.inr (c, n)))

theorem aug_zsum (c : Fin M) : aug K (wS M) D (zsum K M D c) = 0 := by
  simp [zsum, aug_mkT]

theorem coeff_sc_zsum (c : Fin M) (n : ℕ) :
    (sc K (wS M) D (zsum K M D c)).coeff (n + 1) = mkT K (wS M) D (X (.inr (c, n))) := by
  rw [zsum, map_sum, Polynomial.finsetSum_coeff]
  simp only [sc_X, Polynomial.coeff_C_mul_X_pow, wS_inr]
  by_cases hn : n < D
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b _ hb; rw [ite_eq_right (by omega)]
    · intro h; exact absurd (Finset.mem_range.2 hn) h
  · rw [Finset.sum_eq_zero]
    · symm
      rw [mkT_eq_zero_iff]
      intro s hs
      rw [support_X, Finset.mem_singleton] at hs
      subst hs
      rw [Finsupp.weight_single, smul_eq_mul, one_mul]
      simp [wS]; omega
    · intro b hb; rw [ite_eq_right (by simp at hb; omega)]

/-! ## The total Chern classes -/

variable (K M D) in
/-- The ratio `x_{c+1}/x_c` of the colour `c`: `1 + z_c` or `(1 + z_c)⁻¹` according to the sign of
`⟨c, λ⟩`. -/
def ratio (pos : Fin M → Prop) [DecidablePred pos] (c : Fin M) : TrS K M D :=
  if pos c then 1 + zsum K M D c else invOne (zsum K M D c)

variable (K M D) in
/-- The partial products `∏_{c < j} ratio c`. -/
def bpre (pos : Fin M → Prop) [DecidablePred pos] (j : ℕ) : TrS K M D :=
  ∏ c ∈ Finset.univ.filter (fun c : Fin M => (c : ℕ) < j), ratio K M D pos c

variable (K M D) in
/-- **The total Chern classes** of the blocks: `bpre j` for `j < M`, and the inverse of their
product for the last block. -/
def chernData (pos : Fin M → Prop) [DecidablePred pos] (j : Fin (M + 1)) : TrS K M D :=
  if (j : ℕ) < M then bpre K M D pos j
  else invOne (∏ k ∈ Finset.range M, bpre K M D pos k - 1)

variable (pos : Fin M → Prop) [DecidablePred pos]

theorem aug_ratio (c : Fin M) : aug K (wS M) D (ratio K M D pos c) = 1 := by
  unfold ratio
  split_ifs
  · rw [map_add, map_one, aug_zsum, add_zero]
  · exact aug_invOne wS_pos (aug_zsum c)

theorem aug_bpre (j : ℕ) : aug K (wS M) D (bpre K M D pos j) = 1 := by
  rw [bpre, map_prod]
  exact Finset.prod_eq_one fun c _ => aug_ratio pos c

theorem aug_prod_sub : aug K (wS M) D (∏ k ∈ Finset.range M, bpre K M D pos k - 1) = 0 := by
  rw [map_sub, map_prod, Finset.prod_eq_one fun k _ => aug_bpre pos k, map_one, sub_self]

theorem aug_chernData (j : Fin (M + 1)) : aug K (wS M) D (chernData K M D pos j) = 1 := by
  unfold chernData
  split_ifs
  · exact aug_bpre pos _
  · exact aug_invOne wS_pos (aug_prod_sub pos)

theorem coeff_sc_chernData (j : Fin (M + 1)) :
    (sc K (wS M) D (chernData K M D pos j)).coeff 0 = 1 := by
  rw [coeff_sc_zero wS_pos, aug_chernData, map_one]

theorem prod_chernData : ∏ j, chernData K M D pos j = 1 := by
  rw [Fin.prod_univ_castSucc]
  have h1 : ∏ j : Fin M, chernData K M D pos j.castSucc = ∏ k ∈ Finset.range M, bpre K M D pos k := by
    rw [Finset.prod_range fun k => bpre K M D pos k]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [chernData, j.isLt]
  have h2 : chernData K M D pos (Fin.last M) =
      invOne (∏ k ∈ Finset.range M, bpre K M D pos k - 1) := by
    simp [chernData]
  rw [h1, h2]
  have := one_add_mul_invOne wS_pos (aug_prod_sub (K := K) (D := D) pos)
  rwa [add_sub_cancel] at this

theorem goodData_chernData : GoodData K (wS M) D (chernData K M D pos) :=
  ⟨coeff_sc_chernData pos, prod_chernData pos⟩

theorem bpre_succ (c : Fin M) : bpre K M D pos (c + 1) = bpre K M D pos c * ratio K M D pos c := by
  rw [bpre, bpre, ← Finset.prod_erase_mul _ _ (show c ∈ Finset.univ.filter
    (fun c' : Fin M => (c' : ℕ) < c + 1) by simp)]
  congr 1
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext c'
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne (Nat.lt_succ_iff.1 h2) (fun h => h1 (Fin.ext h))
  · intro h; exact ⟨fun e => by subst e; omega, by omega⟩

/-- **The ratio of consecutive blocks** for a colour which is not the last one. -/
theorem chernData_succ (c : Fin M) (hc : (c : ℕ) + 1 < M) :
    chernData K M D pos c.succ = chernData K M D pos c.castSucc * ratio K M D pos c := by
  simp only [chernData, Fin.val_succ, Fin.val_castSucc, ite_eq_left hc, ite_eq_left c.isLt]
  exact bpre_succ pos c

theorem prod_erase_mul (j : Fin (M + 1)) :
    (∏ j' ∈ Finset.univ.erase j, chernData K M D pos j') * chernData K M D pos j = 1 := by
  rw [Finset.prod_erase_mul _ _ (Finset.mem_univ j), prod_chernData]

/-! ## The bubbles -/

/-- `Γ_N` of the generator `(c, n)` of `Π_λ` (KL III (3.24)): the clockwise bubble with label
`⟨c, λ⟩ + n` if `⟨c, λ⟩ ≥ 0`, the counterclockwise bubble with label `-⟨c, λ⟩ + n` otherwise. -/
def bubVal {m : ℕ} (d : Comp m) (c : Fin m) (n : ℕ) : H K d :=
  if 0 ≤ nH d c then cwRealH d c ((nH d c).toNat + n) else ccwRealH d c ((-nH d c).toNat + n)

theorem sum_antidiagonal_coeff (P Q : Polynomial (TrS K M D)) (n : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, P.coeff p.1 * Q.coeff p.2 = (P * Q).coeff n :=
  (Polynomial.coeff_mul P Q n).symm

/-- **The bubbles are free**: under the total Chern classes `chernData`, `Γ_N` of the generator
`(c, n)` of `Π_λ` is `(-1)^{n+1} z_{c,n}`, for every colour `c` but the last. -/
theorem hLift_bubVal (d : Comp M) (hd : ∀ j, D ≤ d j)
    (hpos : ∀ c, pos c ↔ 0 ≤ nH d c) (c : Fin M) (hc : (c : ℕ) + 1 < M) (n : ℕ) :
    hLift d hd (chernData K M D pos) (coeff_sc_chernData pos) (prod_chernData pos)
      (bubVal d c n) = (-1) ^ (n + 1) * mkT K (wS M) D (X (.inr (c, n))) := by
  have hs := chernData_succ (K := K) (D := D) pos c hc
  by_cases hp : pos c
  · have h0 : 0 ≤ nH d c := (hpos c).1 hp
    have hr : ratio K M D pos c = 1 + zsum K M D c := ite_eq_left hp
    rw [bubVal, ite_eq_left h0, cwRealH, ite_eq_left (by simp only [nH] at h0 ⊢; omega)]
    have hi : (nH d c).toNat + n + d c.succ + 1 - d c.castSucc = n + 1 := by
      simp only [nH] at h0 ⊢; omega
    rw [hi, PsiH, bubbleSeq, map_mul, map_pow, map_neg, map_one, map_sum]
    congr 1
    simp only [map_mul, hLift_x, hLift_xbar]
    rw [sum_antidiagonal_coeff, ← map_mul, hs]
    have key : chernData K M D pos c.castSucc * ratio K M D pos c *
        ∏ j' ∈ Finset.univ.erase c.castSucc, chernData K M D pos j' = ratio K M D pos c := by
      rw [mul_comm (chernData K M D pos c.castSucc), mul_assoc, mul_comm (chernData K M D pos _),
        prod_erase_mul, mul_one]
    rw [key, hr, map_add (sc K (wS M) D), map_one (sc K (wS M) D),
      Polynomial.coeff_add, Polynomial.coeff_one, ite_eq_right (by omega),
      zero_add, coeff_sc_zsum]
  · have h0 : ¬ 0 ≤ nH d c := fun h => hp ((hpos c).2 h)
    have hr : ratio K M D pos c = invOne (zsum K M D c) := ite_eq_right hp
    rw [bubVal, ite_eq_right h0, ccwRealH, ite_eq_left (by simp only [nH] at h0 ⊢; omega)]
    have hi : (-nH d c).toNat + n + d c.castSucc + 1 - d c.succ = n + 1 := by
      simp only [nH] at h0 ⊢; omega
    rw [hi, PhiH, bubbleSeq, map_mul, map_pow, map_neg, map_one, map_sum]
    congr 1
    simp only [map_mul, hLift_x, hLift_xbar]
    rw [sum_antidiagonal_coeff, ← map_mul]
    have key : chernData K M D pos c.castSucc *
        ∏ j' ∈ Finset.univ.erase c.succ, chernData K M D pos j' = 1 + zsum K M D c := by
      have h1 := prod_erase_mul (K := K) (D := D) pos c.succ
      have h2 := one_add_mul_invOne (K := K) wS_pos (aug_zsum (D := D) c)
      rw [hs, hr] at h1
      calc chernData K M D pos c.castSucc * ∏ j' ∈ Finset.univ.erase c.succ, chernData K M D pos j'
          = chernData K M D pos c.castSucc * (∏ j' ∈ Finset.univ.erase c.succ,
              chernData K M D pos j') * ((1 + zsum K M D c) * invOne (zsum K M D c)) := by
            rw [h2, mul_one]
        _ = (1 + zsum K M D c) * ((∏ j' ∈ Finset.univ.erase c.succ, chernData K M D pos j') *
              (chernData K M D pos c.castSucc * invOne (zsum K M D c))) := by ring
        _ = 1 + zsum K M D c := by rw [h1, mul_one]
    rw [key, map_add (sc K (wS M) D), map_one (sc K (wS M) D),
      Polynomial.coeff_add, Polynomial.coeff_one, ite_eq_right (by omega),
      zero_add, coeff_sc_zsum]

end Categorification.Flag.Indep

end
