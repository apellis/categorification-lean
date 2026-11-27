/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidRelSimple
import Categorification.WeightedKLR.Rigidity.CupCapPairPassage

/-!
# The braid relation on the model of a cap after `λ_j`: crossings away from `λ_{j+1}`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17.

## Main results

* `CupCap.braid_mul_eSum_of_lbl`: the braid relation on a sum of idempotents with constant
  labels at the three strands.
* `CupCap.ncEval_mul_of_cut`: elements agreeing after an idempotent evaluate polynomials alike.
* `CupCap.midCross_triple_mul_eSum`: three crossings cut by the window idempotents.
* `CupCap.midRel_braid_of_far`: the braid relation on loadings whose maximum is away from the
  three strands.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

section Generic

variable {J : Type*} [DecidableEq J] {k : Type*} [CommRing k]

theorem list_prod_ofFn_pow_mul_of_cut {A : Type*} [Ring A] {e : A} :
    ∀ {n : ℕ} (y z : Fin n → A) (_ : ∀ a, y a * e = z a * e) (_ : ∀ a, Commute (z a) e)
      (u : Fin n → ℕ),
      (List.ofFn fun a => y a ^ u a).prod * e = (List.ofFn fun a => z a ^ u a).prod * e
  | 0, _, _, _, _, _ => rfl
  | n + 1, y, z, hy, hz, u => by
    simp only [List.ofFn_succ, List.prod_cons]
    have ih := list_prod_ofFn_pow_mul_of_cut (fun a => y a.succ) (fun a => z a.succ)
      (fun a => hy a.succ) (fun a => hz a.succ) (fun a => u a.succ)
    have hc : Commute (List.ofFn fun a : Fin n => z a.succ ^ u a.succ).prod e := by
      refine Commute.list_prod_left _ _ fun w hw => ?_
      obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hw
      exact (hz a.succ).pow_left _
    rw [mul_assoc, ih, hc.eq, ← mul_assoc, pow_mul_eq_of_cut' (hy 0) (hz 0), mul_assoc, ← hc.eq,
      ← mul_assoc]
where
  pow_mul_eq_of_cut' {y z : A} (h : y * e = z * e) (hz : Commute z e) (n : ℕ) :
      y ^ n * e = z ^ n * e := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_assoc, h, hz.eq, ← mul_assoc, ih, mul_assoc, ← hz.eq, ← mul_assoc,
        ← pow_succ]

/-- Two families of elements which agree after an idempotent `e` commuting with the second family
evaluate every polynomial alike after `e`. -/
theorem ncEval_mul_of_cut {A : Type*} [Ring A] [Algebra k A] {e : A} {n : ℕ} (y z : Fin n → A)
    (hy : ∀ a, y a * e = z a * e) (hz : ∀ a, Commute (z a) e) (P : MvPolynomial (Fin n) k) :
    ncEval y P * e = ncEval z P * e := by
  unfold ncEval
  rw [Finsupp.sum, Finsupp.sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [mul_assoc, mul_assoc, list_prod_ofFn_pow_mul_of_cut y z hy hz]

/-- **The braid relation on a sum of idempotents** whose loadings have constant labels at the
three strands. -/
theorem braid_mul_eSum_of_lbl {μ : Multiset J} {Q' : J → J → MvPolynomial (Fin 2) k}
    (S : Finset (Seq μ)) (a : ℕ) (h : a + 2 < Multiset.card μ) (u₀ u₁ u₂ : J)
    (hl : ∀ t ∈ S, t.lbl ⟨a, by omega⟩ = u₀ ∧ t.lbl ⟨a + 1, by omega⟩ = u₁ ∧
      t.lbl ⟨a + 2, h⟩ = u₂) :
    ((KLRAlgebra.ψ a * KLRAlgebra.ψ (a + 1) * KLRAlgebra.ψ a -
        KLRAlgebra.ψ (a + 1) * KLRAlgebra.ψ a * KLRAlgebra.ψ (a + 1)) * KLRAlgebra.eSum Q' S :
        KLRAlgebra k Q' μ) =
      if u₀ = u₂ ∧ u₀ ≠ u₁ then
        ncEval ![KLRAlgebra.x ⟨a, by omega⟩, KLRAlgebra.x ⟨a + 1, by omega⟩,
          KLRAlgebra.x ⟨a + 2, h⟩] (qbar (Q' u₀ u₁)) * KLRAlgebra.eSum Q' S
      else 0 := by
  rw [KLRAlgebra.eSum, Finset.mul_sum]
  split_ifs with hc
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨h0, h1, h2⟩ := hl t ht
    rw [KLRAlgebra.braid a h t, h0, h1, h2]
    exact ite_eq_left_iff.2 fun h' => absurd hc h'
  · refine Finset.sum_eq_zero fun t ht => ?_
    obtain ⟨h0, h1, h2⟩ := hl t ht
    rw [KLRAlgebra.braid a h t, h0, h1, h2]
    exact ite_eq_right_iff.2 fun h' => absurd h' hc

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
local notation "C" => midCross j hj Q Λ Λc ν ν₀
local notation "CA" => midCrossAt j hj Q Λ Λc ν ν₀
local notation "D" => midDot j hj Q Λ Λc ν ν₀
local notation "dp" t:max a:max => dotPos (j := j) (hj := hj) (ν₀ := ν₀)
  (Fin.mk (midPos j t) (Nat.lt_succ_of_le (midPos_le j t))) a

omit [DecidableEq I] in
theorem card_plus_braid : M = m + N := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)

theorem midCrossAt_braid_far (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hf : p + 1 < midPos j s ∨ midPos j s + 1 ≤ p) :
    CA s p = KLRAlgebra.ψ (crossPos (midPos j s) N p) * E s := by
  unfold midCrossAt
  rw [dite_eq_left hp, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem midCrossAt_braid_left_black (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p + 1 = midPos j s) {i : I} (hs : s.lbl ⟨p, by omega⟩ = .inl i) :
    CA s p = KLRAlgebra.ψ (p + N) * underLeft N p * E s := by
  unfold midCrossAt
  rw [dite_eq_left hp, ite_eq_left hc]
  split
  · rfl
  · simp_all

theorem midCrossAt_braid_left_red (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p + 1 = midPos j s) {r : Fin ℓ} (hs : s.lbl ⟨p, by omega⟩ = .inr r) :
    CA s p = 0 := by
  unfold midCrossAt
  rw [dite_eq_left hp, ite_eq_left hc]
  split
  · simp_all
  · rfl

theorem midCrossAt_braid_right_black (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p = midPos j s) {i : I} (hs : s.lbl ⟨p + 1, hp⟩ = .inl i) :
    CA s p = Ring.inverse (cupScalar Q ν₀ i) • (underRight N p * KLRAlgebra.ψ (p + N) * E s) := by
  unfold midCrossAt
  rw [dite_eq_left hp, ite_eq_right (by omega), ite_eq_left hc]
  split
  · simp_all
  · simp_all

theorem midCrossAt_braid_right_red (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p = midPos j s) {r : Fin ℓ} (hs : s.lbl ⟨p + 1, hp⟩ = .inr r) :
    CA s p = 0 := by
  unfold midCrossAt
  rw [dite_eq_left hp, ite_eq_right (by omega), ite_eq_left hc]
  split
  · simp_all
  · rfl

/-- Two crossings on consecutive loadings. -/
theorem midCross_mul_midCrossAt (t : Seq (stendhalWeight ℓ ν)) (p q : ℕ) :
    C q * CA t p = CA (sadj m p • t) q * CA t p := by
  conv_lhs => rw [← eSum_mul_midCrossAt t p, ← mul_assoc, midCross_mul_eSum]

/-- **Three crossings cut by the window idempotents.** -/
theorem midCross_triple_mul_eSum (t : Seq (stendhalWeight ℓ ν)) (p q : ℕ) :
    C p * C q * C p * E t = CA (sadj m q • sadj m p • t) p * CA (sadj m p • t) q * CA t p := by
  rw [mul_assoc, midCross_mul_eSum, mul_assoc, midCross_mul_midCrossAt, ← mul_assoc,
    midCross_mul_midCrossAt]

/-- Three crossings, each the window idempotent after a diagram. -/
theorem midCrossAt_triple_of_body (t : Seq (stendhalWeight ℓ ν)) (p q : ℕ) (Y₁ Y₂ Y₃ : Rp)
    (h₁ : CA t p = Y₁ * E t) (h₂ : CA (sadj m p • t) q = Y₂ * E (sadj m p • t))
    (h₃ : CA (sadj m q • sadj m p • t) p = Y₃ * E (sadj m q • sadj m p • t)) :
    CA (sadj m q • sadj m p • t) p * CA (sadj m p • t) q * CA t p = Y₃ * Y₂ * Y₁ * E t := by
  have e₂ : CA (sadj m p • t) q * CA t p = Y₂ * CA t p := by
    rw [h₂, mul_assoc, eSum_mul_midCrossAt]
  have e₃ : CA (sadj m q • sadj m p • t) p * CA (sadj m p • t) q =
      Y₃ * CA (sadj m p • t) q := by
    rw [h₃, mul_assoc, eSum_mul_midCrossAt]
  rw [e₃, mul_assoc, e₂, h₁]
  simp only [mul_assoc]

/-- A polynomial in three dots of `T̃^λ` on the loading `t` is the same polynomial in the dots of
`λ⁺` at their positions. -/
theorem ncEval_midDot_three_mul_eSum (t : Seq (stendhalWeight ℓ ν)) (a b c : Fin m)
    (P : MvPolynomial (Fin 3) k) :
    ncEval ![D a, D b, D c] P * E t =
      ncEval ![KLRAlgebra.x (dp t a), KLRAlgebra.x (dp t b), KLRAlgebra.x (dp t c)] P * E t := by
  refine ncEval_mul_of_cut _ _ (fun d => ?_) (fun d => ?_) P
  · fin_cases d <;> exact midDot_mul_eSum t _
  · fin_cases d <;> exact commute_x_eSum _ _

omit [DecidableEq I] in
/-- The label of an old strand of the loading `s` in a bottom loading of the window at `n`. -/
theorem insertSeq_lbl_crossPos (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) {q : ℕ} (hq : q < m) {c : Fin M}
    (hc : c.val = crossPos n N q) :
    (insertSeq s n hn t).lbl c = oldColour j hj (s.lbl ⟨q, hq⟩) := by
  unfold crossPos at hc
  split_ifs at hc with h
  · exact insertSeq_lbl_lt s hn t ⟨q, hq⟩ h hc
  · exact insertSeq_lbl_ge s hn t ⟨q, hq⟩ (by simp; omega) hc

omit [DecidableEq I] in
theorem dotPos_val_crossPos (t : Seq (stendhalWeight ℓ ν)) (a : Fin m) :
    (dp t a).val = crossPos (midPos j t) N a.val := by
  rw [dotPos_val']; rfl

/-- **The braid relation of `λ⁺` on three old strands**, cut by the window idempotent at `n`. -/
theorem braid_mul_eSum_old (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) {p : ℕ}
    (h : p + 2 < m) (hf : p + 2 < n ∨ n ≤ p) {a : ℕ} (ha : a = crossPos n N p) (haM : a + 2 < M) :
    ((KLRAlgebra.ψ a * KLRAlgebra.ψ (a + 1) * KLRAlgebra.ψ a -
        KLRAlgebra.ψ (a + 1) * KLRAlgebra.ψ a * KLRAlgebra.ψ (a + 1)) * Eat s n hn : Rp) =
      if s.lbl ⟨p, by omega⟩ = s.lbl ⟨p + 2, h⟩ ∧ s.lbl ⟨p, by omega⟩ ≠ s.lbl ⟨p + 1, by omega⟩
      then ncEval ![KLRAlgebra.x ⟨a, by omega⟩, KLRAlgebra.x ⟨a + 1, by omega⟩,
          KLRAlgebra.x ⟨a + 2, haM⟩] (qbar (stendhalQ Q Λ (s.lbl ⟨p, by omega⟩)
            (s.lbl ⟨p + 1, by omega⟩))) * Eat s n hn
      else 0 := by
  have h1 : a + 1 = crossPos n N (p + 1) := by rw [ha]; unfold crossPos; split_ifs <;> omega
  have h2 : a + 2 = crossPos n N (p + 2) := by rw [ha]; unfold crossPos; split_ifs <;> omega
  rw [braid_mul_eSum_of_lbl _ a haM (oldColour j hj (s.lbl ⟨p, by omega⟩))
    (oldColour j hj (s.lbl ⟨p + 1, by omega⟩)) (oldColour j hj (s.lbl ⟨p + 2, h⟩))
    (fun t ht => by
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 ht
      exact ⟨insertSeq_lbl_crossPos s hn w _ ha, insertSeq_lbl_crossPos s hn w _ h1,
        insertSeq_lbl_crossPos s hn w _ h2⟩),
    stendhalQ_oldColour]
  simp only [(oldColour_injective j hj).eq_iff, ne_eq]

end Cut

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Far

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "C" => midCross j hj Q Λ Λc ν ν₀
local notation "D" => midDot j hj Q Λ Λc ν ν₀

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

/-- **The braid relation away from `λ_{j+1}`**: when the maximum is not next to the three strands,
the relation is the braid relation of `λ⁺`, exactly. -/
theorem braid_mul_eSum_of_far (p : ℕ) (h : p + 2 < m) (i : Seq (stendhalWeight ℓ ν))
    (hf : p + 2 < midPos j i ∨ midPos j i + 1 ≤ p) :
    (C p * C (p + 1) * C p - C (p + 1) * C p * C (p + 1)) * E i =
      if i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 2, h⟩ ∧ i.lbl ⟨p, by omega⟩ ≠ i.lbl ⟨p + 1, by omega⟩
      then ncEval ![D ⟨p, by omega⟩, D ⟨p + 1, by omega⟩, D ⟨p + 2, h⟩]
          (qbar (stendhalQ Q Λ (i.lbl ⟨p, by omega⟩) (i.lbl ⟨p + 1, by omega⟩))) * E i
      else 0 := by
  have hM := card_plus_braid (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  set c := midPos j i with hc
  set a := crossPos c N p with ha
  have h1 : crossPos c N (p + 1) = a + 1 := by rw [ha]; unfold crossPos; split_ifs <;> omega
  have haM : a + 2 < M := by rw [ha]; unfold crossPos; split_ifs <;> omega
  have e1 : midPos j (sadj m p • i) = c := midPos_sadj_of_far j i (by omega) (by omega)
  have e2 : midPos j (sadj m (p + 1) • sadj m p • i) = c :=
    (midPos_sadj_of_far j _ h (by omega)).trans e1
  have f1 : midPos j (sadj m (p + 1) • i) = c := midPos_sadj_of_far j i h (by omega)
  have f2 : midPos j (sadj m p • sadj m (p + 1) • i) = c :=
    (midPos_sadj_of_far j _ (by omega) (by omega)).trans f1
  have g : ∀ (t : Seq (stendhalWeight ℓ ν)) (q b : ℕ), q + 1 < m →
      (q + 1 < midPos j t ∨ midPos j t + 1 ≤ q) → crossPos (midPos j t) N q = b →
      midCrossAt j hj Q Λ Λc ν ν₀ t q = (KLRAlgebra.ψ b : Rp) * E t := by
    intro t q b hq hq' hb
    rw [midCrossAt_braid_far t hq hq', hb]
  have hL1 := midCrossAt_triple_of_body i p (p + 1) (KLRAlgebra.ψ a : Rp) (KLRAlgebra.ψ (a + 1))
    (KLRAlgebra.ψ a) (g i p a (by omega) (by omega) rfl)
    (g _ (p + 1) (a + 1) h (by omega) (by rw [e1, h1]))
    (g _ p a (by omega) (by omega) (by rw [e2]))
  have hL2 := midCrossAt_triple_of_body i (p + 1) p (KLRAlgebra.ψ (a + 1) : Rp) (KLRAlgebra.ψ a)
    (KLRAlgebra.ψ (a + 1)) (g i (p + 1) (a + 1) h (by omega) h1)
    (g _ p a (by omega) (by omega) (by rw [f1]))
    (g _ (p + 1) (a + 1) h (by omega) (by rw [f2, h1]))
  rw [sub_mul, midCross_triple_mul_eSum, midCross_triple_mul_eSum, hL1, hL2, ← sub_mul,
    braid_mul_eSum_old i (midPos_le j i) h (by omega) ha haM]
  refine if_congr Iff.rfl ?_ rfl
  rw [ncEval_midDot_three_mul_eSum]
  have hx : ∀ (q : ℕ) (hq : q < m) (b : ℕ) (hb : b < M), crossPos c N q = b →
      (KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀)
        (Fin.mk (midPos j i) (Nat.lt_succ_of_le (midPos_le j i))) ⟨q, hq⟩) : Rp) =
        KLRAlgebra.x ⟨b, hb⟩ := fun q hq b hb hqb =>
    congrArg _ (Fin.ext (by rw [dotPos_val_crossPos]; exact hqb))
  rw [hx p (by omega) a (by omega) rfl, hx (p + 1) (by omega) (a + 1) (by omega) h1,
    hx (p + 2) h (a + 2) haM (by rw [ha]; unfold crossPos; split_ifs <;> omega)]

/-- **The braid relation away from `λ_{j+1}`** on the model. -/
theorem midRel_braid_of_far (p : ℕ) (h : p + 2 < m) (i : Seq (stendhalWeight ℓ ν))
    (hf : p + 2 < midPos j i ∨ midPos j i + 1 ≤ p) :
    MidRel j hj Q Λ Λc ν ν₀ L hL ((C p * C (p + 1) * C p - C (p + 1) * C p * C (p + 1)) * E i)
      (if i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 2, h⟩ ∧ i.lbl ⟨p, by omega⟩ ≠ i.lbl ⟨p + 1, by omega⟩
      then ncEval ![D ⟨p, by omega⟩, D ⟨p + 1, by omega⟩, D ⟨p + 2, h⟩]
          (qbar (stendhalQ Q Λ (i.lbl ⟨p, by omega⟩) (i.lbl ⟨p + 1, by omega⟩))) * E i
      else 0) :=
  MidRel.of_eq (braid_mul_eSum_of_far p h i hf)

end Far

end Categorification.Stendhal.CupCap
