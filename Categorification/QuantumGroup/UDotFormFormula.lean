/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotMatchings
import Categorification.QuantumGroup.UDotKL3
import Categorification.QuantumGroup.FormWords
import Categorification.QuantumGroup.UDotSigmaTau

/-!
# KL III Theorem 2.7: the forms on `U̇` as sums over pairings

Khovanov–Lauda III, arXiv:0807.3250v1, §2.2, **Theorem 2.7** (TeX label `thm_form_formula`,
equation `eq_thm_pairing`, p. 17 of the arXiv PDF): for signed sequences `𝐢, 𝐣` and `λ, μ ∈ X`,

`(E_𝐢 1_λ, E_𝐣 1_μ) = ⟨E_𝐢 1_λ, E_𝐣 1_μ⟩ = δ_{λμ} Σ_{D ∈ p(𝐢, 𝐣)} q^{deg(D, λ)} ∏_{i ∈ I} 1/(1 - q_i²)^{κ_i}`,

`κ_i` the number of `i`-coloured strands of `D`.

## Pairings

An `(𝐢, 𝐣)`-pairing (lower sequence `𝐢`, upper sequence `𝐣`) is encoded as a pairing (in the sense
of `Categorification.QuantumGroup.UDotMatchings`) of the upper word `ρW(𝐢) 𝐣`: reading the boundary
of the strip from the lower right corner, first the lower endpoints from right to left, then the
upper endpoints from left to right, and recording a lower endpoint `±i` as `∓i`. Then an endpoint
recorded as `+` is a sink and one recorded as `-` a source, on both boundaries, and the pairings of
`ρW(𝐢) 𝐣` are exactly KL III's `p'(𝐢, 𝐣)` ("complete matchings … such that the two points in each
matching pair share the same label and their orientations are compatible").

The minimal diagram `D` used for the pairing `σ` is obtained from the minimal diagram `D_σ` of
the upper word `ρW(𝐢) 𝐣` (`UDot.mdeg`) by bending the first `|𝐢|` upper endpoints down around the
left side of the strip (nested caps, the innermost for the endpoint next to `𝐣`); this adds no
crossings, so `D` is still minimal. The cap through the `r`-th upper endpoint `ε i` (`r < |𝐢|`)
is oriented to the left iff `ε = +`, and the region to its right is the region adjacent to the
upper boundary right of `r`; so it has degree `c_{ε i, wR r} = (i·i)/2 (1 + ε ⟨i, wR r⟩)`
(`UDot.bendDeg`). Hence `deg(D, λ) = UDot.mdeg + UDot.bendDeg` (`UDot.pdeg`).

The factor `∏_i (1 - q_i²)^{-κ_i}` is the product over the strands of `D` of `(1 - q_i²)⁻¹`
(`UDot.arcProd`), i.e. of KL III's normalisation `c i = (θ_i, θ_i) = (1 - q_i²)⁻¹`.

## Proof

As in KL III: the pairing sum for one-sided words `P(u)` (`UDot.pairSum`) satisfies the
commutation relation of `U̇` (`UDot.pairSum_comm`: KL III's second and third lemmas after
Lemma 2.8, using the swap bijection `UDot.mdeg_swap` and the removal of adjacent cups
`UDot.sum_rm_matchings`), and on the normally ordered words `(-c)(+b)` it equals
`(1_λ, F_{c} E_{b} 1_λ) = q^{κ}(θ_b, θ_{c^{rev}})` (`UDot.pairSum_block`, via Lusztig's
permutation formula `PreF.form_wordFn`: KL III's Lemmas 2.8 and 2.9). By normal-ordering induction
(`UDot.normal_induction`) `P(u) = (1_λ, E_u 1_λ)` for every signed sequence `u`
(`UDot.φ_eq_pairSumL`), and bending (KL III Lemma after 2.8, property (iii) of Prop. 2.2) gives the
two-sided statement.

## Main results

* `UDot.pairSum_comm`, `UDot.pairSum_block`, `UDot.φ_eq_pairSumL`;
* `UDot.B_eq_pairingSum` — the formula for the form on `'U 1_λ`;
* **`UDot.thm_2_7`** — Theorem 2.7 for `( , )` and `⟨ , ⟩` on `U̇` over any field `K` and
  `q ∈ Kˣ` not a root of unity with KL III's normalisation `c i = (1 - q_i²)⁻¹`;
* **`UDot.KL3.thm_2_7`** — Theorem 2.7 over `ℚ(q)` for `UDot.KL3.form` and `UDot.KL3.sform`.
-/

noncomputable section

namespace Categorification.QuantumGroup

namespace UDot

open Finset Equiv PreF
open scoped Classical

variable {I : Type*} (C : CartanDatum I) {K : Type*} [Field K] (q : Kˣ) (c : I → K)

/-! ### The pairing sum of an upper word -/

/-- The pairing sum `P(L) = Σ_{σ} q^{deg(D_σ, λ)} ∏_{cups} c_{colour}` of the upper word `L`
(`ℓ = ⟨-, λ⟩`, `λ` the weight of the rightmost region). -/
def pairSum (ℓ : I → ℤ) {n : ℕ} (L : Fin n → Bool × I) : K :=
  ∑ σ ∈ matchings L, qp q (mdeg C ℓ L σ) * arcProd c L σ

theorem pairSum_cast (ℓ : I → ℤ) {n n' : ℕ} (h : n = n') (L : Fin n' → Bool × I) :
    pairSum C q c ℓ (fun x : Fin n => L (Fin.cast h x)) = pairSum C q c ℓ L := by
  subst h; rfl

/-! ### The commutation relation -/

section Comm

variable {m p : ℕ} (hp : p ≤ m)

theorem swap_emb (x : Fin m) : swap (rmP0 p hp) (rmP1 p hp) (rmEmb p x) = rmEmb p x :=
  swap_apply_of_ne_of_ne (rmEmb_ne_P0 p hp x) (rmEmb_ne_P1 p hp x)

theorem wR_swap (ℓ : I → ℤ) (L : Fin (m + 2) → Bool × I) (i : I) :
    wR C ℓ (L ∘ swap (rmP0 p hp) (rmP1 p hp)) (rmP1 p hp) i = wR C ℓ L (rmP1 p hp) i := by
  simp only [wR]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_filter] at hr
  have h0 : r ≠ rmP0 p hp := fun e => by
    rw [e] at hr; exact absurd hr.2 (not_lt.2 (rmP0_lt_P1 p hp).le)
  have h1 : r ≠ rmP1 p hp := fun e => by rw [e] at hr; exact lt_irrefl _ hr.2
  simp only [Function.comp_apply, swap_apply_of_ne_of_ne h0 h1]

/-- `q_i^{1 - n} (1 - q_i²)⁻¹ - q_i^{1 + n} (1 - q_i²)⁻¹ = [n]_{q_i}`. -/
theorem qp_sub_qp_eq_qbr (i : I) (hq2 : ((qi C q i : Kˣ) : K) ^ 2 ≠ 1) (n : ℤ) :
    (qp q (di C i * (1 - n)) - qp q (di C i * (1 + n))) * (1 - ((qi C q i : Kˣ) : K) ^ 2)⁻¹ =
      qbr (qi C q i) n := by
  set t := qi C q i with ht
  have e1 : qp q (di C i * (1 - n)) = ((t ^ (1 - n) : Kˣ) : K) := by
    rw [qp, ht, qi, ← zpow_mul]
  have e2 : qp q (di C i * (1 + n)) = ((t ^ (1 + n) : Kˣ) : K) := by
    rw [qp, ht, qi, ← zpow_mul]
  rw [e1, e2, qbr]
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  have h1 : (1 - (t : K) ^ 2) ≠ 0 := sub_ne_zero.2 (Ne.symm hq2)
  have h2 : (t : K) - ((t⁻¹ : Kˣ) : K) ≠ 0 := by
    rw [Units.val_inv_eq_inv_val]
    intro h
    apply hq2
    field_simp at h
    linear_combination h
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val,
    Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]
  rw [Units.val_inv_eq_inv_val] at h2
  rw [zpow_sub₀ ht0, zpow_add₀ ht0, zpow_neg, zpow_one, ← div_eq_mul_inv,
    div_eq_div_iff h1 h2]
  have hx : ((t : K) ^ n) ≠ 0 := zpow_ne_zero _ ht0
  field_simp
  ring

variable (hc : ∀ i, c i = (1 - ((qi C q i : Kˣ) : K) ^ 2)⁻¹)
  (hq2 : ∀ i, ((qi C q i : Kˣ) : K) ^ 2 ≠ 1)

include hc hq2 in
/-- **The pairing sum satisfies the commutation relation `E_i F_j 1_μ = F_j E_i 1_μ +
δ_{ij} [⟨i, μ⟩]_i 1_μ`** at the adjacent endpoints `p, p + 1` (KL III §2.2, the second and third
lemmas after Lemma 2.8). -/
theorem pairSum_comm (ℓ : I → ℤ) (L : Fin (m + 2) → Bool × I) (i j : I)
    (hL0 : L (rmP0 p hp) = (true, i)) (hL1 : L (rmP1 p hp) = (false, j)) :
    pairSum C q c ℓ L = pairSum C q c ℓ (L ∘ swap (rmP0 p hp) (rmP1 p hp)) +
      if j = i then qbr (qi C q i) (wR C ℓ L (rmP1 p hp) i) * pairSum C q c ℓ (L ∘ rmEmb p)
      else 0 := by
  set P0 := rmP0 p hp with hP0d
  set P1 := rmP1 p hp with hP1d
  set τ := swap P0 P1 with hτ
  have hττ : ∀ x, τ (τ x) = x := swap_apply_self _ _
  have hP1 : P1.val = P0.val + 1 := rfl
  have hLL : (L ∘ τ) ∘ τ = L := funext fun x => by simp [hττ]
  have hconj : ∀ σ : Perm (Fin (m + 2)), τ * (τ * σ * τ) * τ = σ := fun σ => by
    ext x; simp [hττ]
  have hτ0 : τ P0 = P1 := swap_apply_left _ _
  have hτ1 : τ P1 = P0 := swap_apply_right _ _
  -- split both sums according to whether `p` and `p + 1` are joined
  unfold pairSum
  rw [← Finset.sum_filter_add_sum_filter_not (matchings L) (fun σ => σ P0 = P1),
    ← Finset.sum_filter_add_sum_filter_not (matchings (L ∘ τ)) (fun σ => σ P0 = P1)]
  -- the pairings in which `p`, `p + 1` are not joined correspond bijectively
  have hnot : ∑ σ ∈ (matchings L).filter (fun σ => ¬ σ P0 = P1),
      qp q (mdeg C ℓ L σ) * arcProd c L σ =
      ∑ σ ∈ (matchings (L ∘ τ)).filter (fun σ => ¬ σ P0 = P1),
        qp q (mdeg C ℓ (L ∘ τ) σ) * arcProd c (L ∘ τ) σ := by
    refine Finset.sum_nbij' (fun σ => τ * σ * τ) (fun σ => τ * σ * τ) (fun σ hσ => ?_)
      (fun σ hσ => ?_) (fun σ _ => hconj σ) (fun σ _ => hconj σ) (fun σ hσ => ?_)
    · simp only [Finset.mem_filter, mem_matchings] at hσ ⊢
      refine ⟨hσ.1.conj τ hττ, fun e => hσ.2 ?_⟩
      simp only [Perm.mul_apply, hτ0] at e
      have e' : σ P1 = P0 := by rw [← hττ (σ P1), e, hτ1]
      rw [← e', hσ.1.invol]
    · simp only [Finset.mem_filter, mem_matchings] at hσ ⊢
      have h' := hσ.1.conj τ hττ
      rw [hLL] at h'
      refine ⟨h', fun e => hσ.2 ?_⟩
      simp only [Perm.mul_apply, hτ0] at e
      have e' : σ P1 = P0 := by rw [← hττ (σ P1), e, hτ1]
      rw [← e', hσ.1.invol]
    · simp only [Finset.mem_filter, mem_matchings] at hσ
      have hne : σ P0 ≠ P1 := hσ.2
      rw [mdeg_swap C hP1 (by rw [hL0]) (by rw [hL1]) hne hσ.1 ℓ,
        arcProd_swap hP1 hne hσ.1]
  rw [hnot]
  -- the pairings in which `p`, `p + 1` are joined
  by_cases hji : j = i
  · subst hji
    have hc0 : (L P1).2 = (L P0).2 := by rw [hL0, hL1]
    have hs0 : (L P1).1 = !(L P0).1 := by rw [hL0, hL1]; rfl
    have hc1 : ((L ∘ τ) P1).2 = ((L ∘ τ) P0).2 := by simp [hτ0, hτ1, hL0, hL1]
    have hs1 : ((L ∘ τ) P1).1 = !((L ∘ τ) P0).1 := by simp [hτ0, hτ1, hL0, hL1]
    have G := sum_rm_matchings C hp hc0 hs0 (fun e a => qp q e * a) ℓ c
    have G' := sum_rm_matchings C hp hc1 hs1 (fun e a => qp q e * a) ℓ c
    simp only [← hP0d, ← hP1d] at G G'
    have hemb : (L ∘ τ) ∘ rmEmb p = L ∘ rmEmb p := funext fun x => by
      exact congrArg L (swap_emb hp x)
    rw [hemb] at G'
    rw [G, G', if_pos rfl]
    have hcup : cupDeg C ℓ L P0 P1 = di C j * (1 - wR C ℓ L P1 j) := by
      simp [cupDeg, hL0]
    have hcup' : cupDeg C ℓ (L ∘ τ) P0 P1 = di C j * (1 + wR C ℓ L P1 j) := by
      simp only [cupDeg, Function.comp_apply, hτ0, hL1]
      rw [wR_swap C hp]
      simp only [sgn_false]
      ring
    have hcol : (L P0).2 = j := by rw [hL0]
    have hcol' : ((L ∘ τ) P0).2 = j := by simp [hτ0, hL1]
    simp only [hcup, hcup', hcol, hcol']
    rw [← qp_sub_qp_eq_qbr C q j (hq2 j), ← hc j, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun σ _ => (show
        qp q (mdeg C ℓ (L ∘ rmEmb p) σ + di C j * (1 - wR C ℓ L P1 j)) *
          (c j * arcProd c (L ∘ rmEmb p) σ) =
        qp q (mdeg C ℓ (L ∘ rmEmb p) σ + di C j * (1 + wR C ℓ L P1 j)) *
          (c j * arcProd c (L ∘ rmEmb p) σ) +
        (qp q (di C j * (1 - wR C ℓ L P1 j)) - qp q (di C j * (1 + wR C ℓ L P1 j))) * c j *
          (qp q (mdeg C ℓ (L ∘ rmEmb p) σ) * arcProd c (L ∘ rmEmb p) σ) by
      rw [qp_add, qp_add]; ring)), Finset.sum_add_distrib]
    ring
  · have e0 : (matchings L).filter (fun σ => σ P0 = P1) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun σ hσ e => hji (by
        have := (mem_matchings.1 hσ).col P0
        rw [e, hL0, hL1] at this; exact this)
    have e1 : (matchings (L ∘ τ)).filter (fun σ => σ P0 = P1) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun σ hσ e => hji (by
        have := (mem_matchings.1 hσ).col P0
        rw [e] at this; simp [hτ0, hτ1, hL0, hL1] at this; exact this.symm)
    rw [e0, e1, if_neg hji, Finset.sum_empty, Finset.sum_empty]
    ring

end Comm

/-! ### Normally ordered words `(-c)(+b)` -/

section Block

variable {m : ℕ}

/-- The exponent identity `Σ_x (b_x·b_x)/2 (1 + ⟨b_x, λ⟩) + Σ_{x < y, w x < w y} b_x·b_y =
κ - Σ_{inversions of w} b_x·b_y` with `κ = Σ_j (j·j)/2 ⟨j, λ⟩ + (ν·ν)/2`. -/
theorem block_exponent (ℓ : I → ℤ) (cc bb : Fin m → I) (w : Perm (Fin m))
    (hw : ∀ x, cc (Fin.rev (w x)) = bb x) :
    (∑ x, di C (bb x) * (1 + ℓ (bb x))) + (∑ x, ∑ y, if x < y ∧ w x < w y then C.dot (bb x) (bb y)
      else 0) = Kx C ℓ (List.ofFn cc : Multiset I) - invWt C.dot bb w := by
  set e : Fin m ≃ Fin m := w.trans Fin.revPerm
  have he : ∀ x, cc (e x) = bb x := fun x => hw x
  have hS1 : S1 C ℓ (List.ofFn cc : Multiset I) = ∑ x, di C (bb x) * ℓ (bb x) := by
    rw [S1, Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn, ← Equiv.sum_comp e]
    simp only [Function.comp_apply, he]
  have hW : wdot C.dot (List.ofFn cc : Multiset I) (List.ofFn cc : Multiset I) =
      ∑ x, ∑ y, C.dot (bb x) (bb y) := by
    rw [wdot, Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn, ← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Function.comp_apply, Multiset.map_coe, Multiset.sum_coe, List.map_ofFn,
      List.sum_ofFn]
    rw [← Equiv.sum_comp e]
    simp only [Function.comp_apply, he]
  have hInv : invWt C.dot bb w = ∑ x, ∑ y, if x < y ∧ w y < w x then C.dot (bb x) (bb y) else 0 := by
    rw [invWt, TypeA.invSet, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [C.symm]
  -- `Σ_{x,y} = Σ_{x = y} + 2 Σ_{x < y}`, and `Σ_{x < y} = Σ_{non-inversions} + Σ_{inversions}`
  have hsplit : ∑ x, ∑ y, C.dot (bb x) (bb y) =
      2 * (∑ x, di C (bb x)) + 2 * ((∑ x, ∑ y, if x < y ∧ w x < w y then C.dot (bb x) (bb y)
        else 0) + ∑ x, ∑ y, if x < y ∧ w y < w x then C.dot (bb x) (bb y) else 0) := by
    have h1 : ∀ x y, C.dot (bb x) (bb y) = (if x = y then C.dot (bb x) (bb y) else 0) +
        ((if x < y ∧ w x < w y then C.dot (bb x) (bb y) else 0) +
          (if x < y ∧ w y < w x then C.dot (bb x) (bb y) else 0)) +
        ((if y < x ∧ w y < w x then C.dot (bb y) (bb x) else 0) +
          (if y < x ∧ w x < w y then C.dot (bb y) (bb x) else 0)) := fun x y => by
      rcases lt_trichotomy x y with h | rfl | h
      · have hne : w x ≠ w y := fun e => h.ne (w.injective e)
        rcases lt_or_gt_of_ne hne with h' | h'
        · simp [h, h', h.ne, not_lt.2 h.le, not_lt.2 h'.le]
        · simp [h, h', h.ne, not_lt.2 h.le, not_lt.2 h'.le]
      · simp
      · have hne : w x ≠ w y := fun e => h.ne' (w.injective e)
        rcases lt_or_gt_of_ne hne with h' | h'
        · simp [h, h', h.ne', not_lt.2 h.le, not_lt.2 h'.le, C.symm (bb x) (bb y)]
        · simp [h, h', h.ne', not_lt.2 h.le, not_lt.2 h'.le, C.symm (bb x) (bb y)]
    rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => h1 x y]
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun x y => if y < x ∧ w y < w x then C.dot (bb y) (bb x) else 0),
      Finset.sum_comm (f := fun x y => if y < x ∧ w x < w y then C.dot (bb y) (bb x) else 0)]
    have hdiag : ∑ x, ∑ y, (if x = y then C.dot (bb x) (bb y) else 0) = 2 * ∑ x, di C (bb x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), two_mul_di]
    rw [hdiag]
    ring
  have h2 := two_mul_hsq C (List.ofFn cc : Multiset I)
  rw [hW, hsplit] at h2
  rw [Kx, hS1, hInv]
  simp only [mul_add, Finset.sum_add_distrib, mul_one] at h2 ⊢
  linarith

/-- **The pairing sum of `(-c)(+b)`** is `(1_λ, F_{c} E_{b} 1_λ) = q^{κ} (θ_b, θ_{c^{rev}})`
(KL III §2.2, Lemmas 2.8 and 2.9: the positive case is Lusztig's form on `f`). -/
theorem pairSum_block (ℓ : I → ℤ) (cc bb : Fin m → I) :
    pairSum C q c ℓ (blockWord cc bb) =
      qp q (Kx C ℓ (List.ofFn cc : Multiset I)) *
        fF C q c (wordFn bb) (wordFn fun y => cc (Fin.rev y)) := by
  rw [fF, form_wordFn, permSum, Finset.mul_sum, Finset.mul_sum, pairSum]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun w : Perm (Fin m) =>
    ∀ x, cc (Fin.rev (w x)) = bb x)]
  rw [Finset.sum_eq_zero (s := univ.filter fun w : Perm (Fin m) => ¬ ∀ x, cc (Fin.rev (w x)) = bb x)
    (fun w hw => by rw [if_neg (Finset.mem_filter.1 hw).2, mul_zero, mul_zero]), add_zero]
  symm
  refine Finset.sum_nbij (fun w => blockPerm w) (fun w hw => ?_) (fun w _ w' _ h => ?_)
    (fun σ hσ => ?_) (fun w hw => ?_)
  · exact mem_matchings.2 (isMatching_blockPerm (Finset.mem_filter.1 hw).2)
  · exact blockPerm_injective h
  · obtain ⟨w, hw, rfl⟩ := exists_blockPerm (mem_matchings.1 hσ)
    exact ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩, rfl⟩
  · have hw' := (Finset.mem_filter.1 hw).2
    rw [if_pos hw', mdeg_blockPerm C hw' ℓ, arcProd_blockPerm c hw',
      block_exponent C ℓ cc bb w hw', sub_eq_add_neg, qp_add]
    have : ((q⁻¹ ^ invWt C.dot bb w : Kˣ) : K) = qp q (-invWt C.dot bb w) := by
      rw [qp, inv_zpow', zpow_neg]
    rw [this]
    ring

theorem pairSum_block' (ℓ : I → ℤ) {m₁ m₂ : ℕ} (cc : Fin m₁ → I) (bb : Fin m₂ → I) :
    pairSum C q c ℓ (blockWord cc bb) =
      qp q (Kx C ℓ (List.ofFn cc : Multiset I)) *
        fF C q c (wordFn bb) (wordFn fun y => cc (Fin.rev y)) := by
  by_cases h : m₁ = m₂
  · subst h; exact pairSum_block C q c ℓ cc bb
  · have h0 : matchings (blockWord cc bb) = ∅ := Finset.eq_empty_of_forall_not_mem fun σ hσ =>
      h (card_eq_of_isMatching (mem_matchings.1 hσ))
    rw [pairSum, h0, Finset.sum_empty, fF, wordFn, wordFn, form_eq_zero_of_wt_ne, mul_zero]
    intro e
    have := congrArg Multiset.card e
    simp [wt] at this
    exact h this.symm

/-! ### Signed sequences as lists -/

/-- The pairing sum of the upper word `u` (a signed sequence). -/
def pairSumL (ℓ : I → ℤ) (u : List (Bool × I)) : K := pairSum C q c ℓ (fun p : Fin u.length => u.get p)

theorem ofFn_rev_get {α : Type*} (l : List α) :
    List.ofFn (fun y : Fin l.length => l.get (Fin.rev y)) = l.reverse := by
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  simp only [List.getElem_ofFn, List.get_eq_getElem, Fin.val_rev, List.getElem_reverse]
  congr 1
  omega

theorem pairSumL_block (ℓ : I → ℤ) (c' b : List I) :
    pairSumL C q c ℓ (negW c' ++ posW b) =
      qp q (Kx C ℓ c') * fF C q c (word (FreeMonoid.ofList b)) (word (FreeMonoid.ofList c'.reverse)) := by
  have hlen : (negW c' ++ posW b).length = c'.length + b.length := by simp [negW, posW]
  have hL : (fun p : Fin (c'.length + b.length) => (negW c' ++ posW b).get (Fin.cast hlen.symm p)) =
      blockWord (fun k : Fin c'.length => c'.get k) (fun x : Fin b.length => b.get x) := by
    funext z
    refine Fin.addCases (fun k => ?_) (fun x => ?_) z
    · rw [blockWord_left]
      simp only [List.get_eq_getElem, Fin.coe_cast, Fin.coe_castAdd]
      rw [List.getElem_append_left (by simp [negW])]
      simp [negW]
    · rw [blockWord_right]
      simp only [List.get_eq_getElem, Fin.coe_cast, Fin.coe_natAdd]
      rw [List.getElem_append_right (by simp [negW])]
      simp [negW, posW]
  rw [pairSumL, ← pairSum_cast C q c ℓ hlen.symm, hL, pairSum_block']
  congr 2
  · rw [List.ofFn_get]
  · rw [wordFn, List.ofFn_get]
  · rw [wordFn, ofFn_rev_get]

end Block

/-! ### The commutation relation for lists -/

section CommList

variable {α : Type*} (a b : List α) (x y : α)

theorem getElem_mid_left {k : ℕ} (hk : k < a.length) (h : k < (a ++ x :: y :: b).length) :
    (a ++ x :: y :: b)[k] = a[k] := List.getElem_append_left hk

theorem getElem_mid_x (h : a.length < (a ++ x :: y :: b).length) :
    (a ++ x :: y :: b)[a.length] = x := by
  rw [List.getElem_append_right (le_refl _)]; simp

theorem getElem_mid_y (h : a.length + 1 < (a ++ x :: y :: b).length) :
    (a ++ x :: y :: b)[a.length + 1] = y := by
  rw [List.getElem_append_right (by omega)]; simp

theorem getElem_mid_right {k : ℕ} (hk : a.length + 2 ≤ k) (h : k < (a ++ x :: y :: b).length) :
    (a ++ x :: y :: b)[k] = b[k - (a.length + 2)]'(by simp at h; omega) := by
  rw [List.getElem_append_right (by omega)]
  have : k - a.length = (k - (a.length + 2)) + 1 + 1 := by omega
  simp only [this, List.getElem_cons_succ]

end CommList

variable (hc : ∀ i, c i = (1 - ((qi C q i : Kˣ) : K) ^ 2)⁻¹)
  (hq2 : ∀ i, ((qi C q i : Kˣ) : K) ^ 2 ≠ 1)

include hc hq2 in
/-- **The commutation relation for the pairing sums of signed sequences**:
`P(a (+i)(-j) b) = P(a (-j)(+i) b) + δ_{ij} [⟨i, λ + b_X⟩]_i P(a b)`. -/
theorem pairSumL_comm (ℓ : I → ℤ) (a b : List (Bool × I)) (i j : I) :
    pairSumL C q c ℓ (a ++ (true, i) :: (false, j) :: b) =
      pairSumL C q c ℓ (a ++ (false, j) :: (true, i) :: b) +
        if j = i then qbr (qi C q i) (wl C ℓ b i) * pairSumL C q c ℓ (a ++ b) else 0 := by
  set m := a.length + b.length
  have hp : a.length ≤ m := by omega
  have hu : m + 2 = (a ++ (true, i) :: (false, j) :: b).length := by simp [m]; omega
  have hu' : m + 2 = (a ++ (false, j) :: (true, i) :: b).length := by simp [m]; omega
  have hab : m = (a ++ b).length := by simp [m]
  set u := a ++ (true, i) :: (false, j) :: b
  set L : Fin (m + 2) → Bool × I := fun z => u.get (Fin.cast hu z) with hLdef
  rw [pairSumL, pairSumL, pairSumL, ← pairSum_cast C q c ℓ hu, ← pairSum_cast C q c ℓ hu',
    ← pairSum_cast C q c ℓ hab]
  have v0 : (rmP0 a.length hp).val = a.length := rfl
  have v1 : (rmP1 a.length hp).val = a.length + 1 := rfl
  have hL0 : L (rmP0 a.length hp) = (true, i) := by
    simp only [hLdef, List.get_eq_getElem, Fin.coe_cast, v0, u]; exact getElem_mid_x _ _ _ _ _
  have hL1 : L (rmP1 a.length hp) = (false, j) := by
    simp only [hLdef, List.get_eq_getElem, Fin.coe_cast, v1, u]; exact getElem_mid_y _ _ _ _ _
  rw [pairSum_comm C q c hp hc hq2 ℓ L i j hL0 hL1]
  have e1 : L ∘ swap (rmP0 a.length hp) (rmP1 a.length hp) =
      fun z => (a ++ (false, j) :: (true, i) :: b).get (Fin.cast hu' z) := by
    funext z
    simp only [Function.comp_apply, hLdef, List.get_eq_getElem, Fin.coe_cast, u]
    by_cases h0 : z = rmP0 a.length hp
    · rw [h0, swap_apply_left]; simp only [v0, v1]; rw [getElem_mid_y, getElem_mid_x]
    by_cases h1 : z = rmP1 a.length hp
    · rw [h1, swap_apply_right]; simp only [v0, v1]; rw [getElem_mid_y, getElem_mid_x]
    rw [swap_apply_of_ne_of_ne h0 h1]
    have h0' : z.val ≠ a.length := fun e => h0 (Fin.ext e)
    have h1' : z.val ≠ a.length + 1 := fun e => h1 (Fin.ext e)
    by_cases hz : z.val < a.length
    · rw [getElem_mid_left _ _ _ _ hz, getElem_mid_left _ _ _ _ hz]
    · rw [getElem_mid_right _ _ _ _ (by omega), getElem_mid_right _ _ _ _ (by omega)]
  have e2 : L ∘ rmEmb a.length = fun z => (a ++ b).get (Fin.cast hab z) := by
    funext z
    simp only [Function.comp_apply, hLdef, List.get_eq_getElem, Fin.coe_cast, u, rmEmb_val]
    split_ifs with hz
    · rw [getElem_mid_left _ _ _ _ hz, List.getElem_append_left hz]
    · rw [getElem_mid_right _ _ _ _ (by omega), List.getElem_append_right (by omega)]
      congr 1; omega
  have e3 : wR C ℓ L (rmP1 a.length hp) i = wl C ℓ b i := by
    rw [wR, wl, aS, ← Fin.sum_univ_fun_getElem b (fun l => sgn l.1 * A C i l.2)]
    congr 1
    refine Finset.sum_bij' (fun r hr => ⟨r.val - (a.length + 2), by
        have := (Finset.mem_filter.1 hr).2; rw [Fin.lt_iff_val_lt_val, v1] at this
        have := r.isLt; omega⟩)
      (fun k _ => ⟨k.val + (a.length + 2), by have := k.isLt; omega⟩) (fun _ _ => mem_univ _)
      (fun k _ => ?_) (fun r hr => ?_) (fun k _ => ?_) (fun r hr => ?_)
    · simp only [Finset.mem_filter, mem_univ, true_and, Fin.lt_iff_val_lt_val, v1]; omega
    · have := (Finset.mem_filter.1 hr).2; rw [Fin.lt_iff_val_lt_val, v1] at this
      ext; simp only; omega
    · ext; simp
    · have h' := (Finset.mem_filter.1 hr).2; rw [Fin.lt_iff_val_lt_val, v1] at h'
      simp only [hLdef, List.get_eq_getElem, Fin.coe_cast, u]
      rw [getElem_mid_right _ _ _ _ (by omega)]
  rw [e1, e2, e3]

include hc hq2 in
/-- **`(1_λ, E_u 1_λ)` is the pairing sum of `u`** (KL III §2.2, proof of Theorem 2.7: the case
`𝐢 = ∅`, by normal-ordering induction). -/
theorem φ_eq_pairSumL (ℓ : I → ℤ) (u : List (Bool × I)) :
    φ C q c ℓ (ew u) = pairSumL C q c ℓ u := by
  induction u using normal_induction with
  | hN c' b => rw [φ_negW_posW, pairSumL_block]
  | hS a i j b h1 h2 => rw [φ_comm, pairSumL_comm C q c hc hq2, h1, h2]

/-! ### Two-sided pairings -/

theorem sum_gt_get {α : Type*} (u : List α) (r : Fin u.length) (f : α → ℤ) :
    ∑ r' ∈ univ.filter (r < ·), f (u.get r') = ((u.drop (r.val + 1)).map f).sum := by
  rw [← Fin.sum_univ_fun_getElem (u.drop (r.val + 1)) f]
  refine Finset.sum_bij' (fun r' hr => ⟨r'.val - (r.val + 1), by
      have := (Finset.mem_filter.1 hr).2; rw [Fin.lt_iff_val_lt_val] at this
      have := r'.isLt; rw [List.length_drop]; omega⟩)
    (fun k _ => ⟨k.val + (r.val + 1), by
      have := k.isLt; have h2 : (u.drop (r.val + 1)).length = u.length - (r.val + 1) :=
        List.length_drop; omega⟩)
    (fun _ _ => mem_univ _) (fun k _ => ?_) (fun r' hr => ?_) (fun k _ => ?_) (fun r' hr => ?_)
  · simp only [Finset.mem_filter, mem_univ, true_and, Fin.lt_iff_val_lt_val]; omega
  · have := (Finset.mem_filter.1 hr).2; rw [Fin.lt_iff_val_lt_val] at this
    ext; simp only; omega
  · ext; simp
  · have := (Finset.mem_filter.1 hr).2; rw [Fin.lt_iff_val_lt_val] at this
    have e : r.val + 1 + (r'.val - (r.val + 1)) = r'.val := by omega
    simp only [List.get_eq_getElem, List.getElem_drop, e]

/-- The region weights of an upper word given by a list. -/
theorem wR_get (ℓ : I → ℤ) (u : List (Bool × I)) (r : Fin u.length) (i : I) :
    wR C ℓ (fun p : Fin u.length => u.get p) r i = wl C ℓ (u.drop (r.val + 1)) i := by
  rw [wR, wl, aS, sum_gt_get u r (fun l => sgn l.1 * A C i l.2)]

/-- The total degree `Σ_{r < k} c_{ε_r i_r, wR r}` of the caps created by bending the first `k`
upper endpoints down around the left side of the strip. -/
def bendDeg (ℓ : I → ℤ) {n : ℕ} (L : Fin n → Bool × I) (k : ℕ) : ℤ :=
  ∑ r, if r.val < k then di C (L r).2 * (1 + sgn (L r).1 * wR C ℓ L r (L r).2) else 0

/-- The bending degree is the exponent of `ρ̄(E_s) E_t 1_λ = q^{rcx} E_{ρW(s) t} 1_λ` (KL III §2.2,
the lemma after Lemma 2.8: "the additional term matches the power of `q` in the formula
`ρ̄(1_μ E_{±i}) = q_i^{1 ∓ ⟨i, μ⟩} E_{∓i} 1_μ`"). -/
theorem bendDeg_eq_rcx (ℓ : I → ℤ) (s t : List (Bool × I)) :
    bendDeg C ℓ (fun p : Fin (ρW s ++ t).length => (ρW s ++ t).get p) s.length =
      rcx C (wl C ℓ t) s := by
  induction s generalizing t with
  | nil => simp [bendDeg, rcx]
  | cons l s ih =>
    obtain ⟨b, i⟩ := l
    have hl : ρW ((b, i) :: s) ++ t = ρW s ++ ((!b, i) :: t) := by
      rw [ρW_cons, List.append_assoc]; rfl
    rw [hl, List.length_cons, rcx]
    have hlen : (ρW s).length = s.length := by simp [ρW]
    set u := ρW s ++ ((!b, i) :: t)
    have hk : s.length < u.length := by simp [u, hlen]
    set r0 : Fin u.length := ⟨s.length, hk⟩
    have hu0 : u.get r0 = (!b, i) := by
      simp only [List.get_eq_getElem, u, r0]
      rw [List.getElem_append_right (by omega)]; simp [hlen]
    have hdrop : u.drop (s.length + 1) = t := by
      simp only [u]
      rw [List.drop_append_eq_append_drop]
      simp [hlen]
    have hsplit : bendDeg C ℓ (fun p : Fin u.length => u.get p) (s.length + 1) =
        bendDeg C ℓ (fun p : Fin u.length => u.get p) s.length +
          di C i * (1 + sgn (!b) * wl C ℓ t i) := by
      rw [bendDeg, bendDeg, ← Finset.sum_erase_add _ _ (mem_univ r0),
        ← Finset.sum_erase_add _ _ (mem_univ r0)]
      have e0 : (r0.val < s.length + 1) := by simp [r0]
      have e1 : ¬ (r0.val < s.length) := by simp [r0]
      rw [if_pos e0, if_neg e1, add_zero]
      have hsum : ∑ x ∈ univ.erase r0, (if x.val < s.length + 1 then di C (u.get x).2 *
          (1 + sgn (u.get x).1 * wR C ℓ (fun p : Fin u.length => u.get p) x (u.get x).2) else 0) =
          ∑ x ∈ univ.erase r0, (if x.val < s.length then di C (u.get x).2 *
          (1 + sgn (u.get x).1 * wR C ℓ (fun p : Fin u.length => u.get p) x (u.get x).2) else 0) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        have hne : r.val ≠ s.length := fun e => (Finset.mem_erase.1 hr).1 (Fin.ext e)
        by_cases h : r.val < s.length
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      rw [hsum]
      congr 1
      rw [wR_get, hu0]
      simp only [r0, hdrop]
    rw [hsplit, ih ((!b, i) :: t), wl_cons_rho, sgn_not]
    ring

/-- The `(𝐢, 𝐣)`-pairings (KL III's `p'(𝐢, 𝐣)`), as pairings of the boundary word `ρW(𝐢) 𝐣`
(see the module docstring). -/
def pairings (s t : List (Bool × I)) : Finset (Perm (Fin (ρW s ++ t).length)) :=
  matchings (fun p : Fin (ρW s ++ t).length => (ρW s ++ t).get p)

/-- **The degree `deg(D, λ)` of the minimal diagram of an `(𝐢, 𝐣)`-pairing** (KL III §2.2; `𝐢 = s`
lower, `𝐣 = t` upper, `ℓ = ⟨-, λ⟩`): the degree of the diagram of the boundary word plus the
degree of the bending caps. -/
def pdeg (ℓ : I → ℤ) (s t : List (Bool × I)) (σ : Perm (Fin (ρW s ++ t).length)) : ℤ :=
  mdeg C ℓ (fun p : Fin (ρW s ++ t).length => (ρW s ++ t).get p) σ +
    bendDeg C ℓ (fun p : Fin (ρW s ++ t).length => (ρW s ++ t).get p) s.length

/-- The strand factor `∏_{strands} c_{colour}` of an `(𝐢, 𝐣)`-pairing. -/
def pweight (s t : List (Bool × I)) (σ : Perm (Fin (ρW s ++ t).length)) : K :=
  arcProd c (fun p : Fin (ρW s ++ t).length => (ρW s ++ t).get p) σ

include hc hq2 in
/-- **KL III Theorem 2.7 on `'U 1_λ`**: `(E_s 1_λ, E_t 1_λ) = Σ_{D ∈ p(s, t)} q^{deg(D, λ)}
∏_{strands} (1 - q_i²)⁻¹`. -/
theorem B_eq_pairingSum (ℓ : I → ℤ) (s t : List (Bool × I)) :
    B C q c ℓ (ew s) (ew t) =
      ∑ σ ∈ pairings s t, qp q (pdeg C ℓ s t σ) * pweight c s t σ := by
  rw [B_ew_ew, φ_eq_pairSumL C q c hc hq2, pairSumL, pairSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [pdeg, pweight, qp_add, bendDeg_eq_rcx]
  ring

/-! ### Theorem 2.7 on `U̇` -/

section UDot

omit hc in
theorem qi_sq_ne_one (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (i : I) :
    ((qi C q i : Kˣ) : K) ^ 2 ≠ 1 := by
  intro h
  have hd := di_pos C i
  obtain ⟨n, hn⟩ : ∃ n : ℕ, di C i = n := ⟨(di C i).toNat, (Int.toNat_of_nonneg hd.le).symm⟩
  apply hq (2 * n) (by omega)
  have : qi C q i ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; simpa using h)
  rw [qi, hn, zpow_natCast, ← pow_mul, mul_comm] at this
  exact this

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : RootDatum C X Y)
  (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)

omit hq2 in
include hc in
/-- **Khovanov–Lauda III, Theorem 2.7** (`thm_form_formula`, eq. `eq_thm_pairing`), for the
bilinear form `( , )` of Proposition 2.2 on `U̇` over a field `K`, `q ∈ Kˣ` not a root of unity
and `c i = (θ_i, θ_i) = (1 - q_i²)⁻¹`: for signed sequences `𝐢 = s`, `𝐣 = t` and `λ, μ ∈ X`,
`(E_𝐢 1_λ, E_𝐣 1_μ) = δ_{λμ} Σ_{D ∈ p(𝐢, 𝐣)} q^{deg(D, λ)} ∏_{strands of D} (1 - q_i²)⁻¹`. -/
theorem thm_2_7 (s t : List (Bool × I)) (lam mu : X) :
    formUD RD q c hq (E1 RD q s lam) (E1 RD q t mu) =
      if lam = mu then
        ∑ σ ∈ pairings s t, qp q (pdeg C (RD.ellOf lam) s t σ) * pweight c s t σ
      else 0 := by
  rw [formUD_E1_E1]
  split_ifs
  · exact B_eq_pairingSum C q c hc (qi_sq_ne_one C q hq) (RD.ellOf lam) s t
  · rfl

omit hq2 in
include hc in
/-- **Khovanov–Lauda III, Theorem 2.7**, the first equality: `⟨E_𝐢 1_λ, E_𝐣 1_μ⟩ =
(E_𝐢 1_λ, E_𝐣 1_μ)` (as `E_𝐢 1_λ` is `ψ`-invariant), hence the same pairing formula for the
semilinear form of Definition 2.3. -/
theorem thm_2_7_hform (σ : K →+* K) (hσ : σ (q : K) = ((q⁻¹ : Kˣ) : K)) (s t : List (Bool × I))
    (lam mu : X) :
    hform RD q c σ hσ hq (E1 RD q s lam) (E1 RD q t mu) =
      formUD RD q c hq (E1 RD q s lam) (E1 RD q t mu) ∧
    hform RD q c σ hσ hq (E1 RD q s lam) (E1 RD q t mu) =
      if lam = mu then
        ∑ σ' ∈ pairings s t, qp q (pdeg C (RD.ellOf lam) s t σ') * pweight c s t σ'
      else 0 := by
  have h1 : hform RD q c σ hσ hq (E1 RD q s lam) (E1 RD q t mu) =
      formUD RD q c hq (E1 RD q s lam) (E1 RD q t mu) := by
    rw [hform, Upsi_E1]
  exact ⟨h1, h1.trans (thm_2_7 C q c hc RD hq s t lam mu)⟩

end UDot

namespace KL3

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : RootDatum C X Y)

/-- **Khovanov–Lauda III, Theorem 2.7** over `ℚ(q)` (KL III's setting: `q` the indeterminate,
`(θ_i, θ_i) = (1 - q_i²)⁻¹`): for all signed sequences `𝐢 = s`, `𝐣 = t` and `λ, μ ∈ X`,

`(E_𝐢 1_λ, E_𝐣 1_μ) = ⟨E_𝐢 1_λ, E_𝐣 1_μ⟩ = δ_{λμ} Σ_{D ∈ p(𝐢, 𝐣)} q^{deg(D, λ)} ∏_{i ∈ I}
(1 - q_i²)^{-κ_i}`,

with `p(𝐢, 𝐣) = UDot.pairings s t`, `deg(D, λ) = UDot.pdeg C ⟨-, λ⟩ s t D` and
`∏_i (1 - q_i²)^{-κ_i} = UDot.pweight (cK C) s t D` (the product over the strands). -/
theorem thm_2_7 (s t : List (Bool × I)) (lam mu : X) :
    form RD (E1 RD qK s lam) (E1 RD qK t mu) = sform RD (E1 RD qK s lam) (E1 RD qK t mu) ∧
    form RD (E1 RD qK s lam) (E1 RD qK t mu) =
      if lam = mu then
        ∑ D ∈ pairings s t, qp qK (pdeg C (RD.ellOf lam) s t D) * pweight (cK C) s t D
      else 0 := by
  have hc : ∀ i, cK C i = (1 - ((qi C qK i : (RatFunc ℚ)ˣ) : RatFunc ℚ) ^ 2)⁻¹ := fun _ => rfl
  obtain ⟨h1, -⟩ := thm_2_7_hform C qK (cK C) hc RD hqK barQ barQ_vQ s t lam mu
  exact ⟨h1.symm, UDot.thm_2_7 C qK (cK C) hc RD hqK s t lam mu⟩

end KL3

end UDot

end Categorification.QuantumGroup
