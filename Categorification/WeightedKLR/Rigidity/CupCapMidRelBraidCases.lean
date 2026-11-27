/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidRelBraid
import Categorification.WeightedKLR.Rigidity.CupCapMidRelBraidPair
import Categorification.WeightedKLR.Rigidity.CupCapMidRelSquare

/-!
# The braid relation on the model of a cap after `λ_j`: the maximum next to the strands

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. On a loading `i` of `λ` with the maximum,
directly before the red strand `λ_{j+1}`, at one of the three strands `p, p + 1, p + 2` of the
braid relation:

* `λ_{j+1}` at `p + 2`: both sides pass the two black strands under the maximum from the left;
  the braid relation of `λ⁺` with `λ_{j+1}` has no correction, and the crossing slides through
  the passage (`CupCap.slides_passing_ψ_left`);
* `λ_{j+1}` at `p`: the mirror image, with `CupCap.slides_passing_ψ`;

in both cases the two sides act alike, and the relation has no correction term since `λ_{j+1}`
is the only red strand of its label.

## Main results

* `CupCap.braid_mem_midExit_of_left`, `CupCap.braid_mem_midExit_of_right`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

section Labels

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} (j : ℕ) {ν : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)

omit [DecidableEq I] in
/-- The strand at the maximum is `λ_{j+1}`. -/
theorem lbl_midPos (i : Seq (stendhalWeight ℓ ν)) {c : ℕ} (hc : c < m) (h : c = midPos j i) :
    ∃ hj : j < ℓ, i.lbl ⟨c, hc⟩ = .inr ⟨j, hj⟩ := by
  have hjl := lt_of_midPos_lt j (s := i) (p := c) hc h.ge
  obtain ⟨b, hb, hlb⟩ := midPos_of_lt j i hjl
  exact ⟨hjl, by rw [show (⟨c, hc⟩ : Fin m) = b from Fin.ext (by rw [hb]; exact h)]; exact hlb⟩

/-- Two different strands do not both carry the label of `λ_{j+1}`. -/
theorem lbl_ne_of_midPos (i : Seq (stendhalWeight ℓ ν)) {c q : ℕ} (hc : c < m) (hq : q < m)
    (h : c = midPos j i) (hne : q ≠ c) : i.lbl ⟨q, hq⟩ ≠ i.lbl ⟨c, hc⟩ := by
  obtain ⟨hjl, hl⟩ := lbl_midPos j i hc h
  intro heq
  have := congrArg Fin.val (lbl_eq_inr_unique (heq.trans hl) hl)
  exact hne this

omit [DecidableEq I] in
theorem lbl_sadj_self (t : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 < m) :
    (sadj m q • t).lbl ⟨q, by omega⟩ = t.lbl ⟨q + 1, hq⟩ :=
  lbl_sadj_of_swapNat t hq _ _ (by simp [swapNat])

omit [DecidableEq I] in
theorem lbl_sadj_succ (t : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 < m) :
    (sadj m q • t).lbl ⟨q + 1, hq⟩ = t.lbl ⟨q, by omega⟩ :=
  lbl_sadj_of_swapNat t hq _ _ (by simp [swapNat])

omit [DecidableEq I] in
theorem lbl_sadj_other (t : Seq (stendhalWeight ℓ ν)) {q a : ℕ} (hq : q + 1 < m) (ha : a < m)
    (h : a ≠ q) (h' : a ≠ q + 1) : (sadj m q • t).lbl ⟨a, ha⟩ = t.lbl ⟨a, ha⟩ :=
  lbl_sadj_of_swapNat t hq _ _ (by unfold swapNat; split_ifs <;> simp_all)

omit [DecidableEq I] in
theorem sadj_braid_smul_loading (t : Seq (stendhalWeight ℓ ν)) {p : ℕ} (h : p + 2 < m) :
    sadj m p • sadj m (p + 1) • sadj m p • t = sadj m (p + 1) • sadj m p • sadj m (p + 1) • t := by
  rw [← mul_smul, ← mul_smul, ← mul_smul, ← mul_smul, sadj_braid h]

end Labels

section Cases

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
local notation "uR" => underRight (k := k) (Q := stendhalQ Q (plusLabels Λ Λc j hj))
  (ν := stendhalWeight (ℓ + 2) (ν + ν₀)) N
local notation "uL" => underLeft (k := k) (Q := stendhalQ Q (plusLabels Λ Λc j hj))
  (ν := stendhalWeight (ℓ + 2) (ν + ν₀)) N

theorem commute_ψ_uR {a q : ℕ} (h : q + N < a ∨ a + 1 < q) :
    Commute (KLRAlgebra.ψ a : Rp) (uR q) :=
  KLRAlgebra.commute_ψ_ψw fun l hl => by rw [List.mem_range'_1] at hl; omega

theorem commute_ψ_uL {a q : ℕ} (h : q + N < a ∨ a + 1 < q) :
    Commute (KLRAlgebra.ψ a : Rp) (uL q) :=
  KLRAlgebra.commute_ψ_ψw fun l hl => by
    rw [List.mem_reverse, List.mem_range'_1] at hl; omega

/-- A far crossing as a diagram before the window idempotent. -/
theorem midCrossAt_braid_far_eq (t : Seq (stendhalWeight ℓ ν)) (q b : ℕ) (hq : q + 1 < m)
    (hf : q + 1 < midPos j t ∨ midPos j t + 1 ≤ q) (hb : crossPos (midPos j t) N q = b) :
    CA t q = (KLRAlgebra.ψ b : Rp) * E t := by
  rw [midCrossAt_braid_far t hq hf, hb]

/-- The braid relation of `λ⁺` on the old strands `p, p + 1, p + 2` of `s` above the window at
`p`, when the first and the third have different labels. -/
theorem braid_eq_of_lbl_ne (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (h : p + 2 < m)
    (hne : s.lbl ⟨p, by omega⟩ ≠ s.lbl ⟨p + 2, h⟩) (hpm : p ≤ m) :
    (KLRAlgebra.ψ (p + N) * KLRAlgebra.ψ (p + N + 1) * KLRAlgebra.ψ (p + N) * Eat s p hpm : Rp) =
      KLRAlgebra.ψ (p + N + 1) * KLRAlgebra.ψ (p + N) * KLRAlgebra.ψ (p + N + 1) * Eat s p hpm := by
  have hM := card_plus_braid (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have := braid_mul_eSum_old (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) s hpm h
    (Or.inr le_rfl) (a := p + N) (by unfold crossPos; simp) (by omega)
  rw [ite_eq_right_iff.2 fun h' => absurd h'.1 hne, sub_mul, sub_eq_zero] at this
  exact this

/-- **The braid relation with `λ_{j+1}` at `p`**: the two sides differ by diagrams in which a strand
leaves the window at the top. -/
theorem braid_mem_midExit_of_right (p : ℕ) (h : p + 2 < m) (i : Seq (stendhalWeight ℓ ν))
    (hc : p = midPos j i) :
    (C p * C (p + 1) * C p - C (p + 1) * C p * C (p + 1)) * E i ∈ midExit j hj Q Λ Λc ν ν₀ := by
  have hM := card_plus_braid (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  set s1 := sadj m p • i
  set s2 := sadj m (p + 1) • s1
  set r1 := sadj m (p + 1) • i
  set r2 := sadj m p • r1
  have e1 : midPos j s1 = p + 1 := midPos_sadj_right j i (by omega) hc
  have e2 : midPos j s2 = p + 2 := midPos_sadj_right j s1 h e1.symm
  have f1 : midPos j r1 = p := (midPos_sadj_of_far j i h (by omega)).trans hc.symm
  have f2 : midPos j r2 = p + 1 := midPos_sadj_right j r1 (by omega) f1.symm
  rw [sub_mul, midCross_triple_mul_eSum, midCross_triple_mul_eSum]
  have la : r2.lbl ⟨p + 1 + 1, h⟩ = i.lbl ⟨p + 1, by omega⟩ := by
    rw [show (⟨p + 1 + 1, h⟩ : Fin m) = ⟨p + 2, h⟩ from rfl,
      lbl_sadj_other r1 (q := p) (a := p + 2) (by omega) h (by omega) (by omega)]
    exact lbl_sadj_succ i h
  have lb1 : s1.lbl ⟨p + 1 + 1, h⟩ = i.lbl ⟨p + 2, h⟩ :=
    lbl_sadj_other i (q := p) (a := p + 2) (by omega) h (by omega) (by omega)
  have lb2 : r1.lbl ⟨p + 1, by omega⟩ = i.lbl ⟨p + 2, h⟩ := lbl_sadj_self i h
  rcases ha : i.lbl ⟨p + 1, by omega⟩ with α | ra
  swap
  · rw [midCrossAt_braid_right_red i (by omega) hc ha, mul_zero,
      midCrossAt_braid_right_red r2 (p := p + 1) h f2.symm (la.trans ha),
      zero_mul, zero_mul, sub_zero]
    exact zero_mem _
  rcases hb : i.lbl ⟨p + 2, h⟩ with β | rb
  swap
  · rw [midCrossAt_braid_right_red s1 (p := p + 1) h e1.symm (lb1.trans hb),
      mul_zero, zero_mul,
      midCrossAt_braid_right_red r1 (by omega) f1.symm (lb2.trans hb),
      mul_zero, zero_mul, sub_zero]
    exact zero_mem _
  set κα := Ring.inverse (cupScalar Q ν₀ α)
  set κβ := Ring.inverse (cupScalar Q ν₀ β)
  have hL := midCrossAt_triple_of_body i p (p + 1) (κα • (uR p * KLRAlgebra.ψ (p + N)) : Rp)
    (κβ • (uR (p + 1) * KLRAlgebra.ψ (p + 1 + N))) (KLRAlgebra.ψ p)
    (by rw [midCrossAt_braid_right_black i (by omega) hc ha, smul_mul_assoc])
    (by rw [midCrossAt_braid_right_black s1 (p := p + 1) h e1.symm (lb1.trans hb),
      smul_mul_assoc])
    (midCrossAt_braid_far_eq s2 p p (by omega) (by rw [e2]; omega)
      (by rw [e2]; unfold crossPos; simp))
  have hR := midCrossAt_triple_of_body i (p + 1) p (KLRAlgebra.ψ (p + 1 + N) : Rp)
    (κβ • (uR p * KLRAlgebra.ψ (p + N))) (κα • (uR (p + 1) * KLRAlgebra.ψ (p + 1 + N)))
    (midCrossAt_braid_far_eq i (p + 1) (p + 1 + N) h (by rw [← hc]; omega)
      (by rw [← hc]; unfold crossPos; simp))
    (by rw [midCrossAt_braid_right_black r1 (by omega) f1.symm (lb2.trans hb), smul_mul_assoc])
    (by rw [midCrossAt_braid_right_black r2 (p := p + 1) h f2.symm (la.trans ha),
      smul_mul_assoc])
  -- the top loading
  obtain ⟨T, hT⟩ : ∃ T, T = sadj m p • s2 := ⟨_, rfl⟩
  have eT : midPos j T = p + 2 := by
    rw [hT]; exact (midPos_sadj_of_far j s2 (by omega) (by omega)).trans e2
  have hTL : E T * (CA s2 p * CA s1 (p + 1) * CA i p) = CA s2 p * CA s1 (p + 1) * CA i p := by
    have := eSum_mul_midCrossAt (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀) s2 p
    rw [← hT] at this
    simp only [← mul_assoc]
    rw [this]
  have hTR : E T * (CA r2 (p + 1) * CA r1 p * CA i (p + 1)) =
      CA r2 (p + 1) * CA r1 p * CA i (p + 1) := by
    have := eSum_mul_midCrossAt (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀)
      r2 (p + 1)
    rw [← sadj_braid_smul_loading i h, ← hT] at this
    simp only [← mul_assoc]
    rw [this]
  obtain ⟨P, hP0⟩ : ∃ P : Rp, P = passU Q Λ Λc j hj ν ν₀ p 2 := ⟨_, rfl⟩
  have hP : P = uR (p + 1) * uR p := by
    rw [hP0, passU_succ, passU_succ, passU_zero, mul_one]; rfl
  obtain ⟨R, hR0⟩ : ∃ R : Rp, R = KLRAlgebra.ψ (p + N + 1) * KLRAlgebra.ψ (p + N) * E i :=
    ⟨_, rfl⟩
  have hcomm := (commute_ψ_uR (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
    (ν₀ := ν₀) (ν := ν) (k := k) (a := p + 1 + N) (q := p) (by omega)).eq
  have eL : CA s2 p * CA s1 (p + 1) * CA i p = (κβ * κα) • (KLRAlgebra.ψ p * P * R) := by
    rw [hL, hP]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hR0]
    refine congrArg₂ (· • ·) (by ring) ?_
    simp only [mul_assoc]
    rw [← mul_assoc (KLRAlgebra.ψ (p + 1 + N)), hcomm, show p + 1 + N = p + N + 1 by omega]
    simp only [mul_assoc]
  have hbr := braid_eq_of_lbl_ne (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) i h
    (lbl_ne_of_midPos j i (by omega) h hc (by omega)).symm (by omega)
  have eR : CA r2 (p + 1) * CA r1 p * CA i (p + 1) =
      (κβ * κα) • (P * KLRAlgebra.ψ (p + N) * R) := by
    rw [hR, hP]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hR0]
    refine congrArg₂ (· • ·) (by ring) ?_
    have hE : (E i : Rp) = Eat i p (by omega) := by
      rw [insertSet_congr' i (midPos_le j i) (by omega) hc.symm]
    have hbr' := hbr
    simp only [mul_assoc] at hbr' ⊢
    rw [← mul_assoc (KLRAlgebra.ψ (p + 1 + N)), hcomm, show p + 1 + N = p + N + 1 by omega]
    simp only [mul_assoc]
    rw [hE, ← hbr']
  have hD := slides_passing_ψ (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) T
    (q := p) (by omega)
  rw [← hP0] at hD
  have hET : (E T : Rp) = Eat T (p + 2) (by omega) := by
    rw [insertSet_congr' T (midPos_le j T) (by omega) eT]
  rw [← hTL, ← hTR, eL, eR, ← mul_sub, ← smul_sub, mul_smul_comm, hET,
    show KLRAlgebra.ψ p * P * R - P * KLRAlgebra.ψ (p + N) * R =
      (KLRAlgebra.ψ p * P - P * KLRAlgebra.ψ (p + N)) * R by noncomm_ring, ← mul_assoc]
  refine Submodule.smul_mem _ _ (mem_midExit T ?_)
  rw [exitSpan_congr' T (midPos_le j T) (by omega) eT]
  exact exitSpan_mul_right T _ hD R

/-- **The braid relation with `λ_{j+1}` at `p + 2`**: the two sides differ by diagrams in which a
strand leaves the window at the top. -/
theorem braid_mem_midExit_of_left (p : ℕ) (h : p + 2 < m) (i : Seq (stendhalWeight ℓ ν))
    (hc : p + 2 = midPos j i) :
    (C p * C (p + 1) * C p - C (p + 1) * C p * C (p + 1)) * E i ∈ midExit j hj Q Λ Λc ν ν₀ := by
  have hM := card_plus_braid (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  set s1 := sadj m p • i
  set s2 := sadj m (p + 1) • s1
  set r1 := sadj m (p + 1) • i
  set r2 := sadj m p • r1
  have e1 : midPos j s1 = p + 1 + 1 := (midPos_sadj_of_far j i (by omega) (by omega)).trans hc.symm
  have e2 : midPos j s2 = p + 1 := midPos_sadj_left j s1 h e1.symm
  have f1 : midPos j r1 = p + 1 := midPos_sadj_left j i h hc
  have f2 : midPos j r2 = p := midPos_sadj_left j r1 (by omega) f1.symm
  rw [sub_mul, midCross_triple_mul_eSum, midCross_triple_mul_eSum]
  have la1 : s1.lbl ⟨p + 1, by omega⟩ = i.lbl ⟨p, by omega⟩ := lbl_sadj_succ i (by omega)
  have la2 : r1.lbl ⟨p, by omega⟩ = i.lbl ⟨p, by omega⟩ :=
    lbl_sadj_other i (q := p + 1) (a := p) h (by omega) (by omega) (by omega)
  have lb2 : s2.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 1, by omega⟩ := by
    rw [lbl_sadj_other s1 (q := p + 1) (a := p) h (by omega) (by omega) (by omega)]
    exact lbl_sadj_self i (by omega)
  rcases ha : i.lbl ⟨p, by omega⟩ with α | ra
  swap
  · rw [midCrossAt_braid_left_red s1 (p := p + 1) h e1.symm (la1.trans ha), mul_zero, zero_mul,
      midCrossAt_braid_left_red r1 (p := p) (by omega) f1.symm (la2.trans ha), mul_zero,
      zero_mul, sub_zero]
    exact zero_mem _
  rcases hb : i.lbl ⟨p + 1, by omega⟩ with β | rb
  swap
  · rw [midCrossAt_braid_left_red s2 (p := p) (by omega) e2.symm (lb2.trans hb), zero_mul,
      zero_mul, midCrossAt_braid_left_red i (p := p + 1) h hc hb, mul_zero, sub_zero]
    exact zero_mem _
  have hL := midCrossAt_triple_of_body i p (p + 1) (KLRAlgebra.ψ p : Rp)
    (KLRAlgebra.ψ (p + 1 + N) * uL (p + 1)) (KLRAlgebra.ψ (p + N) * uL p)
    (midCrossAt_braid_far_eq i p p (by omega) (by omega) (by rw [← hc]; unfold crossPos; simp))
    (midCrossAt_braid_left_black s1 (p := p + 1) h e1.symm (la1.trans ha))
    (midCrossAt_braid_left_black s2 (p := p) (by omega) e2.symm (lb2.trans hb))
  have hR := midCrossAt_triple_of_body i (p + 1) p
    (KLRAlgebra.ψ (p + 1 + N) * uL (p + 1) : Rp) (KLRAlgebra.ψ (p + N) * uL p)
    (KLRAlgebra.ψ (p + 1 + N))
    (midCrossAt_braid_left_black i (p := p + 1) h hc hb)
    (midCrossAt_braid_left_black r1 (p := p) (by omega) f1.symm (la2.trans ha))
    (midCrossAt_braid_far_eq r2 (p + 1) (p + 1 + N) h (by omega)
      (by rw [f2]; unfold crossPos; simp))
  have hW : ∀ (s : Seq (stendhalWeight ℓ ν)) (x : Rp),
      uL p * (uL (p + 1) * (Eat s (p + 1 + 1) (by omega) * x)) =
        Eat s p (by omega) * (uL p * (uL (p + 1) * x)) := by
    intro s x
    rw [← mul_assoc (uL (p + 1)), underLeft_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) s
      (q := p + 1) (by omega), mul_assoc, ← mul_assoc (uL p),
      underLeft_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) s (q := p) (by omega), mul_assoc]
  have hEi : (E i : Rp) = Eat i (p + 1 + 1) (by omega) := by
    rw [insertSet_congr' i (midPos_le j i) (by omega) hc.symm]
  have hψ1 : (KLRAlgebra.ψ p * Eat i (p + 1 + 1) (by omega) : Rp) =
      Eat s1 (p + 1 + 1) (by omega) * KLRAlgebra.ψ p := by
    have := ψ_crossPos_mul_eSum (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀) i
      (n := p + 1 + 1) (by omega) (p := p) (Or.inl (by omega))
    rwa [show crossPos (p + 1 + 1) N p = p by unfold crossPos; simp] at this
  have hself : ∀ x : Rp, KLRAlgebra.ψ (p + N) * (Eat i p (by omega) * x) =
      Eat s1 p (by omega) * (KLRAlgebra.ψ (p + N) * x) := by
    intro x
    have := ψ_crossPos_mul_eSum (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀) i
      (n := p) (by omega) (p := p) (Or.inr le_rfl)
    rw [crossPos_self] at this
    rw [← mul_assoc, this, mul_assoc]
  have hcomm := (commute_ψ_uL (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
    (ν₀ := ν₀) (ν := ν) (k := k) (a := p + 1 + N) (q := p) (by omega)).eq
  have hbr := braid_eq_of_lbl_ne (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) i h
    (lbl_ne_of_midPos j i h (by omega) hc (by omega)) (by omega)
  have hbr' : ∀ x : Rp, KLRAlgebra.ψ (p + N) * (KLRAlgebra.ψ (p + N + 1) *
      (KLRAlgebra.ψ (p + N) * (Eat i p (by omega) * x))) = KLRAlgebra.ψ (p + N + 1) *
      (KLRAlgebra.ψ (p + N) * (KLRAlgebra.ψ (p + N + 1) * (Eat i p (by omega) * x))) := by
    intro x
    have := congrArg (· * x) hbr
    simpa only [mul_assoc] using this
  have eL : CA s2 p * CA s1 (p + 1) * CA i p = KLRAlgebra.ψ (p + N) *
      (KLRAlgebra.ψ (p + N + 1) * (Eat s1 p (by omega) *
        (uL p * uL (p + 1) * KLRAlgebra.ψ p))) := by
    rw [hL, hEi]
    simp only [mul_assoc]
    rw [hψ1, ← mul_assoc (uL p), ← hcomm, mul_assoc, hW, show p + 1 + N = p + N + 1 by omega]
  have eR : CA r2 (p + 1) * CA r1 p * CA i (p + 1) = KLRAlgebra.ψ (p + N) *
      (KLRAlgebra.ψ (p + N + 1) * (Eat s1 p (by omega) *
        (KLRAlgebra.ψ (p + N) * (uL p * uL (p + 1))))) := by
    rw [hR, hEi]
    simp only [mul_assoc]
    rw [← mul_assoc (uL p), ← hcomm, mul_assoc, ← mul_one (Eat i (p + 1 + 1) _), hW, mul_one,
      show p + 1 + N = p + N + 1 by omega, ← hbr', hself]
  rw [eL, eR, ← mul_sub, ← mul_sub, ← mul_sub]
  have hD := slides_passing_ψ_left (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) s1
    (q := p) (by omega)
  have h1 := ψ_crossPos_mul_mem_exitSpan s1 (by omega) (p := p + 1) (Or.inr (by omega)) hD
  have h2 := ψ_crossPos_mul_mem_exitSpan _ (by omega) (p := p) (Or.inr le_rfl) h1
  rw [crossPos_self, show crossPos p N (p + 1) = p + N + 1 by unfold crossPos; simp; omega] at h2
  have eT : midPos j (sadj m p • s2) = p := midPos_sadj_left j s2 (by omega) e2.symm
  refine mem_midExit (sadj m p • s2) ?_
  rw [exitSpan_congr' _ (midPos_le j _) (by omega) eT]
  exact h2

end Cases

end Categorification.Stendhal.CupCap
