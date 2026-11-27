/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidRelBase

/-!
# Isotopy and dot relations on the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. The diagrams of the generators of the KLR
algebra of `λ` acting on the model `L ⊗ e T̃^{λ⁺}` of `K̃^{λ⁺}_λ` (`CupCap.midCross`,
`CupCap.midDot`) satisfy the isotopy relations (distant crossings commute, dots commute with the
crossings of other strands) and the relations between dots and crossings of the KLR algebra.

On a loading `t` of `λ` the crossing `ψ_p` is a diagram of `λ⁺` (`CupCap.midBody`) cut by the
window idempotent `E_t`; it is a multiple of a product of crossings `ψ_a` with `a` in an interval
determined by `p` and the position of the maximum. Distant crossings and dots on other strands
commute with it exactly. For the relations between dots and crossings, a crossing of `λ_{j+1}` with
a black strand is a crossing of two strands of different colours in `λ⁺`, after the black strand
passed under the maximum; the dot on the black strand slides along the passage up to diagrams in
which a strand leaves the window (`CupCap.slides_passing_x` and its mirror).

## Main results

* `CupCap.midRel_cross_cross`, `CupCap.midRel_dot_cross`: the isotopy relations.
* `CupCap.midRel_dot_cross_left`, `CupCap.midRel_dot_cross_right`: dots and crossings.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

section Generic

variable {J : Type*} [DecidableEq J] {k : Type*} [CommRing k] {μ : Multiset J}
  {Q' : J → J → MvPolynomial (Fin 2) k}

/-- **A dot on the passing strand**, moved up through the passage `underLeft` from the bottom:
the errors are the diagrams in which the crossing with the window strand `c` is replaced by the
idempotent of equal colours. -/
theorem ψw_reverse_mul_x_passing (q : ℕ) :
    ∀ (n : ℕ) (h : q + n < Multiset.card μ),
      (KLRAlgebra.ψw (List.range' q n).reverse * KLRAlgebra.x ⟨q, by omega⟩ :
          KLRAlgebra k Q' μ) =
        KLRAlgebra.x ⟨q + n, h⟩ * KLRAlgebra.ψw (List.range' q n).reverse +
          ∑ c : Fin n, KLRAlgebra.ψw (List.range' (q + 1 + c.val) (n - 1 - c.val)).reverse *
            KLRAlgebra.eqIdem (q + c.val) (by omega) *
            KLRAlgebra.ψw (List.range' q c.val).reverse
  | 0, h => by simp
  | n + 1, h => by
    have hr : (List.range' q (n + 1)).reverse = (q + n) :: (List.range' q n).reverse := by
      rw [← List.range'_append_1]; simp
    have hx := KLRAlgebra.x_succ_mul_ψ (k := k) (Q := Q') (ν := μ) (q + n) h
    have hx' : (KLRAlgebra.ψ (q + n) * KLRAlgebra.x ⟨q + n, by omega⟩ : KLRAlgebra k Q' μ) =
        KLRAlgebra.x ⟨q + (n + 1), h⟩ * KLRAlgebra.ψ (q + n) + KLRAlgebra.eqIdem (q + n) h := by
      rw [show (⟨q + (n + 1), h⟩ : Fin (Multiset.card μ)) = ⟨q + n + 1, h⟩ from
        Fin.ext (by simp; omega), hx]
      abel
    rw [hr, KLRAlgebra.ψw_cons, mul_assoc, ψw_reverse_mul_x_passing q n (by omega), mul_add,
      ← mul_assoc, hx', add_mul, Fin.sum_univ_castSucc, Finset.mul_sum]
    have hterm : ∀ c : Fin n,
        (KLRAlgebra.ψ (q + n) *
          (KLRAlgebra.ψw (List.range' (q + 1 + c.val) (n - 1 - c.val)).reverse *
            KLRAlgebra.eqIdem (q + c.val) (by omega) *
            KLRAlgebra.ψw (List.range' q c.val).reverse) : KLRAlgebra k Q' μ) =
        KLRAlgebra.ψw (List.range' (q + 1 + (Fin.castSucc c).val)
            (n + 1 - 1 - (Fin.castSucc c).val)).reverse *
          KLRAlgebra.eqIdem (q + (Fin.castSucc c).val) (by have := c.2; simp; omega) *
          KLRAlgebra.ψw (List.range' q (Fin.castSucc c).val).reverse := by
      intro c
      have hc := c.2
      simp only [Fin.val_castSucc]
      rw [show n + 1 - 1 - c.val = (n - 1 - c.val) + 1 by omega, ← List.range'_append_1,
        List.reverse_append, show q + 1 + c.val + (n - 1 - c.val) = q + n by omega]
      rw [List.range'_one]
      simp only [List.reverse_singleton, List.singleton_append, KLRAlgebra.ψw_cons, mul_assoc]
    simp only [hterm, Fin.val_last]
    have hlast : (List.range' (q + 1 + n) (n + 1 - 1 - n)) = [] := by
      rw [show n + 1 - 1 - n = 0 by omega]; rfl
    rw [hlast, List.reverse_nil, KLRAlgebra.ψw_nil, one_mul]
    simp only [mul_assoc]
    abel

/-! ### Ring identities used to reorganize the dot-crossing differences -/

theorem eSum_mul_dotCross_aux {R : Type*} [Ring R] {e e' B xa xb : R}
    (hB : e' * (B * e) = B * e) (hca : xa * e = e * xa) (hcb : xb * e' = e' * xb) :
    e' * (B * xa * e - xb * B * e) = B * xa * e - xb * B * e := by
  have h1 : B * xa * e = B * e * xa := by rw [mul_assoc, hca, ← mul_assoc]
  rw [h1, mul_assoc xb B e, mul_sub, ← mul_assoc e' (B * e) xa, hB, ← mul_assoc e' xb, ← hcb,
    mul_assoc xb e' (B * e), hB]

theorem dotCross_left_aux {R : Type*} [Ring R] {x2 ψ u x' e : R} (h : x' * u = u * x') :
    x2 * (ψ * u) * e - ψ * u * x' * e = (x2 * ψ - ψ * x') * (u * e) := by
  rw [mul_assoc ψ u x', ← h]; noncomm_ring

theorem dotCross_right_aux {R : Type*} [Ring R] {u ψ x2 x' e : R} (h : x' * u = u * x') :
    u * ψ * x2 * e - x' * (u * ψ) * e = u * ((ψ * x2 - x' * ψ) * e) := by
  rw [← mul_assoc x' u ψ, h]; noncomm_ring

theorem dotCross_split_aux {R : Type*} [Ring R] (x u ψ x2 x' e : R) :
    x * (u * ψ) * e - u * ψ * x' * e =
      (x * u - u * x2) * (ψ * e) + u * ((x2 * ψ - ψ * x') * e) := by
  noncomm_ring

theorem dotCross_pass_aux {R : Type*} [Ring R] {ψ u xp x2 x' S e : R} (h : u * xp = x2 * u + S) :
    ψ * u * xp * e - x' * (ψ * u) * e = (ψ * x2 - x' * ψ) * (u * e) + ψ * (S * e) := by
  rw [mul_assoc ψ u xp, h]; noncomm_ring

end Generic

section Cut

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Eat" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "dp" t:max a:max => dotPos (j := j) (hj := hj) (ν₀ := ν₀)
  (Fin.mk (midPos j t) (Nat.lt_succ_of_le (midPos_le j t))) a

omit [DecidableEq I] in
theorem card_plus'' : M = m + N := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)

/-! ### Labels -/

/-- The red strand `λ_{j+1}` and its neighbours have different labels. -/
theorem lbl_ne_succ_of_mid (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (h : p + 1 = midPos j s ∨ p = midPos j s) :
    s.lbl ⟨p, by omega⟩ ≠ s.lbl ⟨p + 1, hp⟩ := by
  have hj' : j < ℓ := lt_of_midPos_lt j (s := s) (p := p + 1) hp (by omega)
  obtain ⟨b, hb, hlb⟩ := midPos_of_lt j s hj'
  intro heq
  rcases h with h | h
  · have e1 : (⟨p + 1, hp⟩ : Fin m) = b := Fin.ext (by simp; omega)
    rw [e1, hlb] at heq
    have := congrArg Fin.val (lbl_eq_inr_unique heq hlb)
    simp at this; omega
  · have e1 : (⟨p, by omega⟩ : Fin m) = b := Fin.ext (by simp; omega)
    rw [e1, hlb] at heq
    have := congrArg Fin.val (lbl_eq_inr_unique heq.symm hlb)
    simp at this; omega

/-- The dots and crossings of two old strands in `λ⁺` below the window, cut by the window
idempotents. -/
theorem dotCrossLeft_mul_eSum (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (a : ℕ)
    (h : a + 1 < M) (P : Prop) [Decidable P]
    (hP : ∀ w : Seq (stendhalWeight 2 ν₀),
      ((insertSeq s n hn (Seq.map (cupColour j hj) w)).lbl ⟨a, by omega⟩ =
        (insertSeq s n hn (Seq.map (cupColour j hj) w)).lbl ⟨a + 1, h⟩ ↔ P)) :
    ((KLRAlgebra.x ⟨a, by omega⟩ * KLRAlgebra.ψ a - KLRAlgebra.ψ a * KLRAlgebra.x ⟨a + 1, h⟩) *
        Eat s n hn : Rp) = if P then Eat s n hn else 0 := by
  rw [eSum_insertSet, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun w _ => (KLRAlgebra.dot_cross_left a h _).trans
    (if_congr (hP w) rfl rfl)]
  split_ifs <;> simp

theorem dotCrossRight_mul_eSum (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (a : ℕ)
    (h : a + 1 < M) (P : Prop) [Decidable P]
    (hP : ∀ w : Seq (stendhalWeight 2 ν₀),
      ((insertSeq s n hn (Seq.map (cupColour j hj) w)).lbl ⟨a, by omega⟩ =
        (insertSeq s n hn (Seq.map (cupColour j hj) w)).lbl ⟨a + 1, h⟩ ↔ P)) :
    ((KLRAlgebra.ψ a * KLRAlgebra.x ⟨a, by omega⟩ - KLRAlgebra.x ⟨a + 1, h⟩ * KLRAlgebra.ψ a) *
        Eat s n hn : Rp) = if P then Eat s n hn else 0 := by
  rw [eSum_insertSet, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun w _ => (KLRAlgebra.dot_cross_right a h _).trans
    (if_congr (hP w) rfl rfl)]
  split_ifs <;> simp

omit [DecidableEq I] in
/-- Labels of two old strands below the window. -/
theorem lbl_insertSeq_iff_lt (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) {a : ℕ}
    (ha : a + 1 < n) (w : Seq (stendhalWeight 2 ν₀)) (h : a + 1 < M) :
    (insertSeq s n hn (Seq.map (cupColour j hj) w)).lbl ⟨a, by omega⟩ =
        (insertSeq s n hn (Seq.map (cupColour j hj) w)).lbl ⟨a + 1, h⟩ ↔
      s.lbl ⟨a, by omega⟩ = s.lbl ⟨a + 1, by omega⟩ := by
  rw [insertSeq_lbl_lt s hn _ ⟨a, by omega⟩ (by simp; omega) rfl,
    insertSeq_lbl_lt s hn _ ⟨a + 1, by omega⟩ (by simp; omega) rfl]
  exact (oldColour_injective j hj).eq_iff

omit [DecidableEq I] in
/-- Labels of two old strands above the window. -/
theorem lbl_insertSeq_iff_ge (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) {a : ℕ}
    (ha : n ≤ a) (ha' : a + 1 < m) (w : Seq (stendhalWeight 2 ν₀)) (h : a + N + 1 < M) :
    (insertSeq s n hn (Seq.map (cupColour j hj) w)).lbl ⟨a + N, by omega⟩ =
        (insertSeq s n hn (Seq.map (cupColour j hj) w)).lbl ⟨a + N + 1, h⟩ ↔
      s.lbl ⟨a, by omega⟩ = s.lbl ⟨a + 1, ha'⟩ := by
  rw [insertSeq_lbl_ge s hn _ ⟨a, by omega⟩ (by simp; omega) rfl,
    insertSeq_lbl_ge s hn _ ⟨a + 1, ha'⟩ (by simp; omega) (by simp; omega)]
  exact (oldColour_injective j hj).eq_iff

/-! ### The crossings on a loading -/

variable (j hj Q Λ Λc ν ν₀) in
/-- The diagram of `λ⁺` of the crossing `ψ_p` on the loading `s` of `λ`, before the window
idempotent `E_s`. -/
def midBody (s : Seq (stendhalWeight ℓ ν)) (p : ℕ) : Rp :=
  if hp : p + 1 < m then
    if p + 1 = midPos j s then
      match s.lbl ⟨p, by omega⟩ with
      | .inl _ => KLRAlgebra.ψ (p + N) * underLeft N p
      | .inr _ => 0
    else if p = midPos j s then
      match s.lbl ⟨p + 1, hp⟩ with
      | .inl i => Ring.inverse (cupScalar Q ν₀ i) • (underRight N p * KLRAlgebra.ψ (p + N))
      | .inr _ => 0
    else KLRAlgebra.ψ (crossPos (midPos j s) N p)
  else 0

theorem midCrossAt_eq_midBody (s : Seq (stendhalWeight ℓ ν)) (p : ℕ) :
    midCrossAt j hj Q Λ Λc ν ν₀ s p = midBody j hj Q Λ Λc ν ν₀ s p * E s := by
  unfold midCrossAt midBody
  split_ifs with hp h1 h2
  · cases s.lbl ⟨p, by omega⟩ <;> simp [mul_assoc]
  · cases s.lbl ⟨p + 1, hp⟩ <;> simp
  · rfl
  · simp

theorem midBody_far (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hf : p + 1 < midPos j s ∨ midPos j s + 1 ≤ p) :
    midBody j hj Q Λ Λc ν ν₀ s p = KLRAlgebra.ψ (crossPos (midPos j s) N p) := by
  unfold midBody
  rw [dite_eq_left hp, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem midBody_left_black (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p + 1 = midPos j s) {i : I} (hs : s.lbl ⟨p, by omega⟩ = .inl i) :
    midBody j hj Q Λ Λc ν ν₀ s p = KLRAlgebra.ψ (p + N) * underLeft N p := by
  unfold midBody
  rw [dite_eq_left hp, ite_eq_left hc]
  split
  · rfl
  · simp_all

theorem midBody_left_red (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p + 1 = midPos j s) {r : Fin ℓ} (hs : s.lbl ⟨p, by omega⟩ = .inr r) :
    midBody j hj Q Λ Λc ν ν₀ s p = 0 := by
  unfold midBody
  rw [dite_eq_left hp, ite_eq_left hc]
  split
  · simp_all
  · rfl

theorem midBody_right_black (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p = midPos j s) {i : I} (hs : s.lbl ⟨p + 1, hp⟩ = .inl i) :
    midBody j hj Q Λ Λc ν ν₀ s p =
      Ring.inverse (cupScalar Q ν₀ i) • (underRight N p * KLRAlgebra.ψ (p + N)) := by
  unfold midBody
  rw [dite_eq_left hp, ite_eq_right (by omega), ite_eq_left hc]
  split
  · simp_all
  · simp_all

theorem midBody_right_red (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p = midPos j s) {r : Fin ℓ} (hs : s.lbl ⟨p + 1, hp⟩ = .inr r) :
    midBody j hj Q Λ Λc ν ν₀ s p = 0 := by
  unfold midBody
  rw [dite_eq_left hp, ite_eq_right (by omega), ite_eq_left hc]
  split
  · simp_all
  · rfl

theorem midBody_out (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : ¬ p + 1 < m) :
    midBody j hj Q Λ Λc ν ν₀ s p = 0 := by
  unfold midBody
  rw [dite_eq_right hp]

/-- The crossing on a loading only depends on the labels of its strands and the position of the
maximum relative to it. -/
theorem midBody_eq_of {s s' : Seq (stendhalWeight ℓ ν)} {p : ℕ} (hp : p + 1 < m)
    (hl : s'.lbl ⟨p, by omega⟩ = s.lbl ⟨p, by omega⟩) (hl' : s'.lbl ⟨p + 1, hp⟩ = s.lbl ⟨p + 1, hp⟩)
    (h1 : p + 1 = midPos j s' ↔ p + 1 = midPos j s) (h2 : p = midPos j s' ↔ p = midPos j s)
    (h3 : crossPos (midPos j s') N p = crossPos (midPos j s) N p) :
    midBody j hj Q Λ Λc ν ν₀ s' p = midBody j hj Q Λ Λc ν ν₀ s p := by
  by_cases hc1 : p + 1 = midPos j s
  · rcases hb : s.lbl ⟨p, by omega⟩ with i | r
    · rw [midBody_left_black s hp hc1 hb, midBody_left_black s' hp (h1.2 hc1) (hl.trans hb)]
    · rw [midBody_left_red s hp hc1 hb, midBody_left_red s' hp (h1.2 hc1) (hl.trans hb)]
  by_cases hc2 : p = midPos j s
  · rcases hb : s.lbl ⟨p + 1, hp⟩ with i | r
    · rw [midBody_right_black s hp hc2 hb, midBody_right_black s' hp (h2.2 hc2) (hl'.trans hb)]
    · rw [midBody_right_red s hp hc2 hb, midBody_right_red s' hp (h2.2 hc2) (hl'.trans hb)]
  have hc1' : ¬ p + 1 = midPos j s' := fun h => hc1 (h1.1 h)
  have hc2' : ¬ p = midPos j s' := fun h => hc2 (h2.1 h)
  rw [midBody_far s hp (by omega), midBody_far s' hp (by omega), h3]

/-- The position of the maximum after a crossing. -/
theorem midPos_sadj_cases (t : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m) :
    ((p + 1 < midPos j t ∨ midPos j t + 1 ≤ p) ∧ midPos j (sadj m p • t) = midPos j t) ∨
      (p + 1 = midPos j t ∧ midPos j (sadj m p • t) = p) ∨
      (p = midPos j t ∧ midPos j (sadj m p • t) = p + 1) := by
  by_cases h1 : p + 1 = midPos j t
  · exact Or.inr (Or.inl ⟨h1, midPos_sadj_left j t hp h1⟩)
  by_cases h2 : p = midPos j t
  · exact Or.inr (Or.inr ⟨h2, midPos_sadj_right j t hp h2⟩)
  exact Or.inl ⟨by omega, midPos_sadj_of_far j t hp (by omega)⟩

omit [DecidableEq I] in
theorem lbl_sadj_far (t : Seq (stendhalWeight ℓ ν)) {q a : ℕ} (hq : q + 1 < m) (ha : a < m)
    (h : a ≠ q) (h' : a ≠ q + 1) : (sadj m q • t).lbl ⟨a, ha⟩ = t.lbl ⟨a, ha⟩ :=
  lbl_sadj_of_swapNat t hq _ _ (by unfold swapNat; split_ifs <;> simp_all)

/-- A crossing far to the right does not change the crossing `ψ_p`. -/
theorem midBody_sadj_of_lt (t : Seq (stendhalWeight ℓ ν)) {p q : ℕ} (hpq : p + 1 < q) :
    midBody j hj Q Λ Λc ν ν₀ (sadj m q • t) p = midBody j hj Q Λ Λc ν ν₀ t p := by
  by_cases hq : q + 1 < m
  swap
  · have : sadj m q = 1 := by unfold sadj; rw [dite_eq_right hq]
    rw [this, one_smul]
  have hp : p + 1 < m := by omega
  refine midBody_eq_of hp (lbl_sadj_far t hq _ (by omega) (by omega))
    (lbl_sadj_far t hq _ (by omega) (by omega)) ?_ ?_ ?_ <;>
  rcases midPos_sadj_cases (j := j) t hq with ⟨hf, he⟩ | ⟨hc, he⟩ | ⟨hc, he⟩ <;> rw [he] <;>
    (try unfold crossPos) <;> (try split_ifs) <;> omega

/-- A crossing far to the left does not change the crossing `ψ_q`. -/
theorem midBody_sadj_of_gt (t : Seq (stendhalWeight ℓ ν)) {p q : ℕ} (hpq : p + 1 < q) :
    midBody j hj Q Λ Λc ν ν₀ (sadj m p • t) q = midBody j hj Q Λ Λc ν ν₀ t q := by
  by_cases hq : q + 1 < m
  swap
  · rw [midBody_out _ hq, midBody_out _ hq]
  have hp : p + 1 < m := by omega
  refine midBody_eq_of hq (lbl_sadj_far t hp _ (by omega) (by omega))
    (lbl_sadj_far t hp _ (by omega) (by omega)) ?_ ?_ ?_ <;>
  rcases midPos_sadj_cases (j := j) t hp with ⟨hf, he⟩ | ⟨hc, he⟩ | ⟨hc, he⟩ <;> rw [he] <;>
    (try unfold crossPos) <;> (try split_ifs) <;> omega

/-- **The support of the crossing on a loading**: a multiple of a product of crossings `ψ_a`
with `a` between `lo` and `hi`. -/
theorem midBody_support (s : Seq (stendhalWeight ℓ ν)) (p : ℕ) :
    ∃ (r : k) (ρ : List ℕ), midBody j hj Q Λ Λc ν ν₀ s p = r • KLRAlgebra.ψw ρ ∧
      ∀ a ∈ ρ, (if midPos j s + 1 ≤ p then p + N else p) ≤ a ∧
        a ≤ (if p + 1 < midPos j s then p else p + N) := by
  by_cases hp : p + 1 < m
  swap
  · exact ⟨0, [], by rw [midBody_out s hp, zero_smul], by simp⟩
  by_cases hc1 : p + 1 = midPos j s
  · rcases hb : s.lbl ⟨p, by omega⟩ with i | r
    · refine ⟨1, (p + N) :: (List.range' p N).reverse, ?_, ?_⟩
      · rw [midBody_left_black s hp hc1 hb, one_smul, KLRAlgebra.ψw_cons]; rfl
      · intro a ha
        simp only [List.mem_cons, List.mem_reverse, List.mem_range'_1] at ha
        split_ifs <;> omega
    · exact ⟨0, [], by rw [midBody_left_red s hp hc1 hb, zero_smul], by simp⟩
  by_cases hc2 : p = midPos j s
  · rcases hb : s.lbl ⟨p + 1, hp⟩ with i | r
    · refine ⟨Ring.inverse (cupScalar Q ν₀ i), List.range' p N ++ [p + N], ?_, ?_⟩
      · rw [midBody_right_black s hp hc2 hb, KLRAlgebra.ψw_append, KLRAlgebra.ψw_cons,
          KLRAlgebra.ψw_nil, mul_one]; rfl
      · intro a ha
        simp only [List.mem_append, List.mem_range'_1, List.mem_singleton] at ha
        split_ifs <;> omega
    · exact ⟨0, [], by rw [midBody_right_red s hp hc2 hb, zero_smul], by simp⟩
  refine ⟨1, [crossPos (midPos j s) N p], ?_, ?_⟩
  · rw [midBody_far s hp (by omega), one_smul, KLRAlgebra.ψw_cons, KLRAlgebra.ψw_nil, mul_one]
  · intro a ha
    simp only [List.mem_singleton] at ha
    subst ha
    unfold crossPos
    split_ifs <;> omega

/-- **Distant crossings commute** on a loading. -/
theorem midBody_mul_midBody_comm (t : Seq (stendhalWeight ℓ ν)) {p q : ℕ} (hpq : p + 1 < q) :
    midBody j hj Q Λ Λc ν ν₀ t p * midBody j hj Q Λ Λc ν ν₀ t q =
      midBody j hj Q Λ Λc ν ν₀ t q * midBody j hj Q Λ Λc ν ν₀ t p := by
  obtain ⟨r, ρ, hr, hρ⟩ := midBody_support (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
    (ν₀ := ν₀) t p
  obtain ⟨r', ρ', hr', hρ'⟩ := midBody_support (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
    (ν₀ := ν₀) t q
  rw [hr, hr', smul_mul_smul_comm, smul_mul_smul_comm, mul_comm r,
    (KLRAlgebra.commute_ψw_ψw fun a ha b hb => ?_).eq]
  have h1 := hρ a ha
  have h2 := hρ' b hb
  left
  split_ifs at h1 h2 <;> omega

/-- **Dots on other strands commute with a crossing** on a loading. -/
theorem commute_x_midBody (t : Seq (stendhalWeight ℓ ν)) {p : ℕ} (a : Fin m) (h₁ : a.val ≠ p)
    (h₂ : a.val ≠ p + 1) :
    Commute (KLRAlgebra.x (dp t a) : Rp) (midBody j hj Q Λ Λc ν ν₀ t p) := by
  obtain ⟨r, ρ, hr, hρ⟩ := midBody_support (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
    (ν₀ := ν₀) t p
  rw [hr]
  refine Commute.smul_right (KLRAlgebra.commute_x_ψw fun b hb => ?_) r
  have h := hρ b hb
  have hd := dotPos_val' (j := j) (hj := hj) (ν₀ := ν₀)
    (Fin.mk (midPos j t) (Nat.lt_succ_of_le (midPos_le j t))) a
  simp only at hd
  rw [hd]
  split_ifs at h hd ⊢ <;> omega

theorem dotPos_sadj (t : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m) (a : Fin m)
    (h₁ : a.val ≠ p) (h₂ : a.val ≠ p + 1) : dp (sadj m p • t) a = dp t a := by
  apply Fin.ext
  rw [dotPos_val', dotPos_val']
  simp only
  rcases midPos_sadj_cases (j := j) t hp with ⟨hf, he⟩ | ⟨hc, he⟩ | ⟨hc, he⟩ <;> simp only [he] <;>
    split_ifs <;> omega

/-! ### Cutting the generators -/

theorem midCross_mul_eSum' (t : Seq (stendhalWeight ℓ ν)) (p : ℕ) :
    midCross j hj Q Λ Λc ν ν₀ p * E t = midBody j hj Q Λ Λc ν ν₀ t p * E t := by
  rw [midCross_mul_eSum, midCrossAt_eq_midBody]

theorem eSum_mul_midBody (t : Seq (stendhalWeight ℓ ν)) (p : ℕ) :
    E (sadj m p • t) * (midBody j hj Q Λ Λc ν ν₀ t p * E t) =
      midBody j hj Q Λ Λc ν ν₀ t p * E t := by
  rw [← midCrossAt_eq_midBody, eSum_mul_midCrossAt]

/-- Two crossings on the loading `t`. -/
theorem midCross_mul_midCross_mul_eSum (t : Seq (stendhalWeight ℓ ν)) (p q : ℕ) :
    midCross j hj Q Λ Λc ν ν₀ p * midCross j hj Q Λ Λc ν ν₀ q * E t =
      midBody j hj Q Λ Λc ν ν₀ (sadj m q • t) p * midBody j hj Q Λ Λc ν ν₀ t q * E t := by
  rw [mul_assoc, midCross_mul_eSum', ← eSum_mul_midBody, ← mul_assoc, midCross_mul_eSum',
    mul_assoc, eSum_mul_midBody, mul_assoc]

/-- A dot above a crossing on the loading `t`. -/
theorem midDot_mul_midCross_mul_eSum (t : Seq (stendhalWeight ℓ ν)) (a : Fin m) (p : ℕ) :
    midDot j hj Q Λ Λc ν ν₀ a * midCross j hj Q Λ Λc ν ν₀ p * E t =
      KLRAlgebra.x (dp (sadj m p • t) a) * midBody j hj Q Λ Λc ν ν₀ t p * E t := by
  rw [mul_assoc, midCross_mul_eSum', ← eSum_mul_midBody, ← mul_assoc, midDot_mul_eSum,
    mul_assoc, eSum_mul_midBody, mul_assoc]

/-- A dot below a crossing on the loading `t`. -/
theorem midCross_mul_midDot_mul_eSum (t : Seq (stendhalWeight ℓ ν)) (a : Fin m) (p : ℕ) :
    midCross j hj Q Λ Λc ν ν₀ p * midDot j hj Q Λ Λc ν ν₀ a * E t =
      midBody j hj Q Λ Λc ν ν₀ t p * KLRAlgebra.x (dp t a) * E t := by
  rw [mul_assoc, midDot_mul_eSum, (commute_x_eSum _ _).eq, ← mul_assoc, midCross_mul_eSum',
    mul_assoc, ← (commute_x_eSum _ _).eq, ← mul_assoc]

/-! ### Dots and crossings on a loading -/

omit [DecidableEq I] in
theorem dp_eq (t : Seq (stendhalWeight ℓ ν)) (a : ℕ) (ha : a < m) (v : ℕ) (hv : v < M)
    (h : (if a < midPos j t then a else a + N) = v) : dp t ⟨a, ha⟩ = ⟨v, hv⟩ :=
  Fin.ext ((dotPos_val' _ _).trans h)

theorem eSum_mid_eq (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (h : midPos j s = n) :
    (E s : Rp) = Eat s n hn :=
  congrArg (KLRAlgebra.eSum _) (insertSet_congr' s (midPos_le j s) hn h)

theorem mem_midExit_of (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (h : n = midPos j s)
    {y : Rp} (hy : y ∈ exitSpan Q Λ Λc j hj s n hn) : y ∈ midExit j hj Q Λ Λc ν ν₀ := by
  subst h; exact mem_midExit s hy

theorem ψ_self_mul_eSum (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p ≤ m) :
    (KLRAlgebra.ψ (p + N) * Eat s p hp : Rp) = Eat (sadj m p • s) p hp * KLRAlgebra.ψ (p + N) := by
  have h := ψ_crossPos_mul_eSum (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀) s hp
    (p := p) (Or.inr le_rfl)
  rwa [crossPos_self] at h

/-- The difference of the two sides of the first dot-crossing relation on a loading. -/
theorem dotCrossLeft_mem (i : Seq (stendhalWeight ℓ ν)) (p : ℕ) (h : p + 1 < m) :
    (KLRAlgebra.x (dp (sadj m p • i) ⟨p, by omega⟩) * midBody j hj Q Λ Λc ν ν₀ i p * E i -
        midBody j hj Q Λ Λc ν ν₀ i p * KLRAlgebra.x (dp i ⟨p + 1, h⟩) * E i -
        (if i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 1, h⟩ then E i else 0) : Rp) ∈
      midExit j hj Q Λ Λc ν ν₀ := by
  have hM : M = m + N := card_plus''
  rcases midPos_sadj_cases (j := j) i h with ⟨hf, he⟩ | ⟨hc, he⟩ | ⟨hc, he⟩
  · rw [midBody_far i h hf]
    rcases hf with hf | hf
    · have hcp : crossPos (midPos j i) N p = p := by unfold crossPos; split_ifs <;> omega
      rw [hcp, dp_eq (sadj m p • i) p (by omega) p (by omega) (by rw [he]; split_ifs <;> omega),
        dp_eq i (p + 1) h (p + 1) (by omega) (by split_ifs; omega), ← sub_mul,
        dotCrossLeft_mul_eSum i (midPos_le j i) p (by omega) _
          (fun w => lbl_insertSeq_iff_lt i (midPos_le j i) hf w _), sub_self]
      exact zero_mem _
    · have hcp : crossPos (midPos j i) N p = p + N := by unfold crossPos; split_ifs <;> omega
      rw [hcp, dp_eq (sadj m p • i) p (by omega) (p + N) (by omega)
          (by rw [he]; split_ifs <;> omega),
        dp_eq i (p + 1) h (p + N + 1) (by omega) (by split_ifs <;> omega), ← sub_mul,
        dotCrossLeft_mul_eSum i (midPos_le j i) (p + N) (by omega) _
          (fun w => lbl_insertSeq_iff_ge i (midPos_le j i) (by omega) h w _), sub_self]
      exact zero_mem _
  · have hne := lbl_ne_succ_of_mid (j := j) i h (Or.inl hc)
    rw [ite_eq_right hne, sub_zero]
    rcases hb : i.lbl ⟨p, by omega⟩ with i0 | r
    · have hcomm : Commute (KLRAlgebra.x ⟨p + N + 1, by omega⟩ : Rp) (underLeft N p) :=
        KLRAlgebra.commute_x_ψw fun b hb => by
          simp only [List.mem_reverse, List.mem_range'_1] at hb; simp only; omega
      rw [midBody_left_black i h hc hb,
        dp_eq (sadj m p • i) p (by omega) (p + N) (by omega) (by rw [he]; split_ifs <;> omega),
        dp_eq i (p + 1) h (p + N + 1) (by omega) (by split_ifs <;> omega),
        eSum_mid_eq i h.le hc.symm, dotCross_left_aux hcomm.eq,
        underLeft_mul_eSum i h.le, ← mul_assoc,
        dotCrossLeft_mul_eSum i (by omega : p ≤ m) (p + N) (by omega) _
          (fun w => lbl_insertSeq_iff_ge i (by omega : p ≤ m) le_rfl h w _),
        ite_eq_right hne, zero_mul]
      exact zero_mem _
    · rw [midBody_left_red i h hc hb]; simp
  · have hne := lbl_ne_succ_of_mid (j := j) i h (Or.inr hc)
    rw [ite_eq_right hne, sub_zero]
    rcases hb : i.lbl ⟨p + 1, h⟩ with i0 | r
    · rw [midBody_right_black i h hc hb,
        dp_eq (sadj m p • i) p (by omega) p (by omega) (by rw [he]; split_ifs <;> omega),
        dp_eq i (p + 1) h (p + N + 1) (by omega) (by split_ifs <;> omega),
        mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, ← smul_sub]
      refine Submodule.smul_mem _ _ ?_
      rw [eSum_mid_eq i (by omega : p ≤ m) hc.symm,
        dotCross_split_aux _ _ _ (KLRAlgebra.x ⟨p + N, by omega⟩),
        dotCrossLeft_mul_eSum i (by omega : p ≤ m) (p + N) (by omega) _
          (fun w => lbl_insertSeq_iff_ge i (by omega : p ≤ m) le_rfl h w _),
        ite_eq_right hne, mul_zero, add_zero, ψ_self_mul_eSum i (by omega : p ≤ m),
        ← mul_assoc]
      set i' := sadj m p • i
      have h1 : (KLRAlgebra.x ⟨p, by omega⟩ * underRight N p * Eat i' p (by omega) : Rp) =
          Eat i' (p + 1) h.le * (KLRAlgebra.x ⟨p, by omega⟩ * underRight N p) := by
        rw [mul_assoc, underRight_mul_eSum Q Λ Λc i' h.le, ← mul_assoc, ← mul_assoc,
          (commute_x_eSum _ _).eq]
      have h2 : (underRight N p * KLRAlgebra.x ⟨p + N, by omega⟩ * Eat i' p (by omega) : Rp) =
          Eat i' (p + 1) h.le * (underRight N p * KLRAlgebra.x ⟨p + N, by omega⟩) := by
        rw [mul_assoc, (commute_x_eSum _ _).eq, ← mul_assoc, underRight_mul_eSum Q Λ Λc i' h.le,
          mul_assoc]
      rw [sub_mul, h1, h2, ← mul_sub]
      exact mem_midExit_of i' h.le he.symm
        (exitSpan_mul_right i' h.le (slides_passing_x Q Λ Λc i' h.le) _)
    · rw [midBody_right_red i h hc hb]; simp

/-- The difference of the two sides of the second dot-crossing relation on a loading. -/
theorem dotCrossRight_mem (i : Seq (stendhalWeight ℓ ν)) (p : ℕ) (h : p + 1 < m) :
    (midBody j hj Q Λ Λc ν ν₀ i p * KLRAlgebra.x (dp i ⟨p, by omega⟩) * E i -
        KLRAlgebra.x (dp (sadj m p • i) ⟨p + 1, h⟩) * midBody j hj Q Λ Λc ν ν₀ i p * E i -
        (if i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 1, h⟩ then E i else 0) : Rp) ∈
      midExit j hj Q Λ Λc ν ν₀ := by
  have hM : M = m + N := card_plus''
  rcases midPos_sadj_cases (j := j) i h with ⟨hf, he⟩ | ⟨hc, he⟩ | ⟨hc, he⟩
  · rw [midBody_far i h hf]
    rcases hf with hf | hf
    · have hcp : crossPos (midPos j i) N p = p := by unfold crossPos; split_ifs <;> omega
      rw [hcp, dp_eq i p (by omega) p (by omega) (by split_ifs <;> omega),
        dp_eq (sadj m p • i) (p + 1) h (p + 1) (by omega) (by rw [he]; split_ifs; omega),
        ← sub_mul, dotCrossRight_mul_eSum i (midPos_le j i) p (by omega) _
          (fun w => lbl_insertSeq_iff_lt i (midPos_le j i) hf w _), sub_self]
      exact zero_mem _
    · have hcp : crossPos (midPos j i) N p = p + N := by unfold crossPos; split_ifs <;> omega
      rw [hcp, dp_eq i p (by omega) (p + N) (by omega) (by split_ifs <;> omega),
        dp_eq (sadj m p • i) (p + 1) h (p + N + 1) (by omega)
          (by rw [he]; split_ifs <;> omega),
        ← sub_mul,
        dotCrossRight_mul_eSum i (midPos_le j i) (p + N) (by omega) _
          (fun w => lbl_insertSeq_iff_ge i (midPos_le j i) (by omega) h w _), sub_self]
      exact zero_mem _
  · have hne := lbl_ne_succ_of_mid (j := j) i h (Or.inl hc)
    rw [ite_eq_right hne, sub_zero,
      ← eSum_mul_dotCross_aux (eSum_mul_midBody i p) (commute_x_eSum _ _).eq
        (commute_x_eSum _ _).eq]
    rcases hb : i.lbl ⟨p, by omega⟩ with i0 | r
    · have hpass : (underLeft N p * KLRAlgebra.x ⟨p, by omega⟩ : Rp) =
          KLRAlgebra.x ⟨p + N, by omega⟩ * underLeft N p +
            ∑ c : Fin N, KLRAlgebra.ψw (List.range' (p + 1 + c.val) (N - 1 - c.val)).reverse *
              KLRAlgebra.eqIdem (p + c.val) (by omega) *
              KLRAlgebra.ψw (List.range' p c.val).reverse :=
        ψw_reverse_mul_x_passing p N (by omega)
      rw [midBody_left_black i h hc hb,
        dp_eq i p (by omega) p (by omega) (by split_ifs <;> omega),
        dp_eq (sadj m p • i) (p + 1) h (p + N + 1) (by omega) (by rw [he]; split_ifs <;> omega),
        eSum_mid_eq i h.le hc.symm, eSum_mid_eq (sadj m p • i) (by omega : p ≤ m) he,
        dotCross_pass_aux hpass, underLeft_mul_eSum i h.le, ← mul_assoc _ (Eat i p _),
        dotCrossRight_mul_eSum i (by omega : p ≤ m) (p + N) (by omega) _
          (fun w => lbl_insertSeq_iff_ge i (by omega : p ≤ m) le_rfl h w _),
        ite_eq_right hne, zero_mul, zero_add, ← mul_assoc,
        ← ψ_self_mul_eSum i (by omega : p ≤ m), Finset.sum_mul, Finset.mul_sum]
      refine Submodule.sum_mem _ fun c _ => ?_
      rw [mul_assoc]
      have hy := ψ_crossPos_mul_mem_exitSpan (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
        (ν₀ := ν₀) i (by omega : p ≤ m) (Or.inr le_rfl)
        (exitTermLeft_mem (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) i h.le c)
      rw [crossPos_self] at hy
      exact mem_midExit_of (sadj m p • i) (by omega : p ≤ m) he.symm hy
    · rw [midBody_left_red i h hc hb]; simp
  · have hne := lbl_ne_succ_of_mid (j := j) i h (Or.inr hc)
    rw [ite_eq_right hne, sub_zero]
    rcases hb : i.lbl ⟨p + 1, h⟩ with i0 | r
    · rw [midBody_right_black i h hc hb,
        dp_eq i p (by omega) (p + N) (by omega) (by split_ifs <;> omega),
        dp_eq (sadj m p • i) (p + 1) h (p + N + 1) (by omega) (by rw [he]; split_ifs <;> omega),
        mul_smul_comm, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, ← smul_sub]
      refine Submodule.smul_mem _ _ ?_
      have hcomm : Commute (KLRAlgebra.x ⟨p + N + 1, by omega⟩ : Rp) (underRight N p) :=
        KLRAlgebra.commute_x_ψw fun b hb => by
          simp only [List.mem_range'_1] at hb; simp only; omega
      rw [eSum_mid_eq i (by omega : p ≤ m) hc.symm, dotCross_right_aux hcomm.eq,
        dotCrossRight_mul_eSum i (by omega : p ≤ m) (p + N) (by omega) _
          (fun w => lbl_insertSeq_iff_ge i (by omega : p ≤ m) le_rfl h w _),
        ite_eq_right hne, mul_zero]
      exact zero_mem _
    · rw [midBody_right_red i h hc hb]; simp

end Cut

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Rel

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Eat" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "μ" => midMapKLR j hj Q Λ Λc ν ν₀
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "σ" => midStendhal j hj Q Λ Λc ν ν₀
local notation "dp" t:max a:max => dotPos (j := j) (hj := hj) (ν₀ := ν₀)
  (Fin.mk (midPos j t) (Nat.lt_succ_of_le (midPos_le j t))) a

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

/-- Cutting by the sum of the window idempotents does not change the action. -/
theorem midElt_mul_midMapKLR_one (Y : Rp) :
    midElt j hj Q Λ Λc ν ν₀ (Y * μ 1) = midElt j hj Q Λ Λc ν ν₀ Y := by
  have h : bot (μ 1) * σ 1 = σ 1 := by
    rw [midStendhal_one_eq_bot, ← map_mul, ← midMapKLR_mul, one_mul]
  rw [midElt, midElt, map_mul]
  simp only [mul_assoc, h]

/-- Diagrams which agree on every window idempotent act alike. -/
theorem MidRel.of_mul_eSum {Y Y' : Rp} (h : ∀ t, Y * E t = Y' * E t) :
    MidRel j hj Q Λ Λc ν ν₀ L hL Y Y' := by
  refine MidRel.of_midElt_eq ?_
  rw [← midElt_mul_midMapKLR_one Y, ← midElt_mul_midMapKLR_one Y', midMapKLR_one,
    Finset.mul_sum, Finset.mul_sum, Finset.sum_congr rfl fun t _ => h t]

/-- **Distant crossings commute** on the model. -/
theorem midRel_cross_cross (p q : ℕ) (h : p + 1 < q) :
    MidRel j hj Q Λ Λc ν ν₀ L hL
      (midCross j hj Q Λ Λc ν ν₀ p * midCross j hj Q Λ Λc ν ν₀ q)
      (midCross j hj Q Λ Λc ν ν₀ q * midCross j hj Q Λ Λc ν ν₀ p) :=
  MidRel.of_mul_eSum fun t => by
    rw [midCross_mul_midCross_mul_eSum, midCross_mul_midCross_mul_eSum, midBody_sadj_of_lt t h,
      midBody_sadj_of_gt t h, midBody_mul_midBody_comm t h]

/-- **Dots commute with the crossings of other strands** on the model. -/
theorem midRel_dot_cross (a : Fin m) (p : ℕ) (h₁ : a.val ≠ p) (h₂ : a.val ≠ p + 1) :
    MidRel j hj Q Λ Λc ν ν₀ L hL
      (midDot j hj Q Λ Λc ν ν₀ a * midCross j hj Q Λ Λc ν ν₀ p)
      (midCross j hj Q Λ Λc ν ν₀ p * midDot j hj Q Λ Λc ν ν₀ a) :=
  MidRel.of_mul_eSum fun t => by
    rw [midDot_mul_midCross_mul_eSum, midCross_mul_midDot_mul_eSum]
    by_cases hp : p + 1 < m
    · rw [dotPos_sadj t hp a h₁ h₂, (commute_x_midBody t a h₁ h₂).eq]
    · simp [midBody_out t hp]

/-- **Dots and crossings**, first relation, on the model. -/
theorem midRel_dot_cross_left (p : ℕ) (h : p + 1 < m) (i : Seq (stendhalWeight ℓ ν)) :
    MidRel j hj Q Λ Λc ν ν₀ L hL
      ((midDot j hj Q Λ Λc ν ν₀ ⟨p, by omega⟩ * midCross j hj Q Λ Λc ν ν₀ p -
          midCross j hj Q Λ Λc ν ν₀ p * midDot j hj Q Λ Λc ν ν₀ ⟨p + 1, h⟩) *
        midIdem j hj Q Λ Λc ν ν₀ i)
      (if i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 1, h⟩ then midIdem j hj Q Λ Λc ν ν₀ i else 0) := by
  refine MidRel.of_sub_mem ?_
  rw [midIdem, sub_mul, midDot_mul_midCross_mul_eSum, midCross_mul_midDot_mul_eSum]
  exact dotCrossLeft_mem i p h

/-- **Dots and crossings**, second relation, on the model. -/
theorem midRel_dot_cross_right (p : ℕ) (h : p + 1 < m) (i : Seq (stendhalWeight ℓ ν)) :
    MidRel j hj Q Λ Λc ν ν₀ L hL
      ((midCross j hj Q Λ Λc ν ν₀ p * midDot j hj Q Λ Λc ν ν₀ ⟨p, by omega⟩ -
          midDot j hj Q Λ Λc ν ν₀ ⟨p + 1, h⟩ * midCross j hj Q Λ Λc ν ν₀ p) *
        midIdem j hj Q Λ Λc ν ν₀ i)
      (if i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 1, h⟩ then midIdem j hj Q Λ Λc ν ν₀ i else 0) := by
  refine MidRel.of_sub_mem ?_
  rw [midIdem, sub_mul, midDot_mul_midCross_mul_eSum, midCross_mul_midDot_mul_eSum]
  exact dotCrossRight_mem i p h

end Rel

end Categorification.Stendhal.CupCap
