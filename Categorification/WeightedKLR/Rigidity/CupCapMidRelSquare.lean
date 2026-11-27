/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidRelBase
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftLoop
import Categorification.WeightedKLR.Rigidity.CupCapMidRightLoop

/-!
# The quadratic relation on the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. The diagrams of the crossings of `T̃^λ`
on the model `L ⊗ e T̃^{λ⁺}` of `K̃^{λ⁺}_λ` (`CupCap.midCross`) satisfy the quadratic KLR
relation `ψ_p² e(i) = Q_{i_p i_{p+1}}(x_p, x_{p+1}) e(i)` (`CupCap.midRel_cross_sq`).

Away from the red strand `λ_{j+1}` this is the quadratic relation of `λ⁺`. A black strand of
colour `i` crossing `λ_{j+1}` twice passes under the maximum and back: on its left this is the
relation (max2) in the model, from the left pull-off identity (`CupCap.leftLoop_midModel`), after
the dots of the quadratic relation of `λ⁺` slid down along the passage; on its right it is the
pull-off identity of Lemma 7.16 (`CupCap.rightLoop_midModel`). In both cases the scalar `κ_i` of
(max1) cancels against the normalization of the crossing moving the black strand to the left of
the maximum, which needs `κ_i` to be a unit.

## Main results

* `CupCap.x_passing_mul_underLeft`: a dot on the passing strand moved down a passage.
* `CupCap.ψ_sq_mul_eSum_insertSet`: the quadratic relation of `λ⁺` on two old strands.
* `CupCap.MidRel.of_tmul`: diagrams acting alike on the generators of the model act alike.
* `CupCap.midRel_crossAt_sq_left`, `CupCap.midRel_crossAt_sq_right`: the square of a crossing
  of a black strand with `λ_{j+1}`, on either side of it.
* `CupCap.midRel_cross_sq`: the quadratic relation on the model.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

section Generic

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

/-- **A dot on the passing strand**, moved down along the passage `underLeft`: the errors are
the diagrams in which the crossing with the window strand `c` is replaced by the idempotent of
equal colours. -/
theorem x_passing_mul_underLeft {μ : Multiset I} {Q' : I → I → MvPolynomial (Fin 2) k} (q : ℕ) :
    ∀ (n : ℕ) (h : q + n < Multiset.card μ),
      (KLRAlgebra.x ⟨q + n, h⟩ * KLRAlgebra.ψw (List.range' q n).reverse :
          KLRAlgebra k Q' μ) =
        KLRAlgebra.ψw (List.range' q n).reverse * KLRAlgebra.x ⟨q, by omega⟩ -
          ∑ c : Fin n, KLRAlgebra.ψw (List.range' (q + 1 + c.val) (n - 1 - c.val)).reverse *
            KLRAlgebra.eqIdem (q + c.val) (by omega) * KLRAlgebra.ψw (List.range' q c.val).reverse
  | 0, h => by simp
  | n + 1, h => by
    have hψ : (KLRAlgebra.ψw (List.range' q (n + 1)).reverse : KLRAlgebra k Q' μ) =
        KLRAlgebra.ψ (q + n) * KLRAlgebra.ψw (List.range' q n).reverse := by
      rw [← List.range'_append_1, List.reverse_append, KLRAlgebra.ψw_append]
      simp
    have hx := KLRAlgebra.x_succ_mul_ψ (k := k) (Q := Q') (ν := μ) (q + n) (by omega)
    have hterm : ∀ c : Fin n,
        (KLRAlgebra.ψ (q + n) *
            (KLRAlgebra.ψw (List.range' (q + 1 + c.val) (n - 1 - c.val)).reverse *
              KLRAlgebra.eqIdem (q + c.val) (by omega) *
              KLRAlgebra.ψw (List.range' q c.val).reverse) : KLRAlgebra k Q' μ) =
          KLRAlgebra.ψw (List.range' (q + 1 + c.val) (n + 1 - 1 - c.val)).reverse *
            KLRAlgebra.eqIdem (q + c.val) (by omega) *
            KLRAlgebra.ψw (List.range' q c.val).reverse := by
      intro c
      have hc := c.2
      rw [show n + 1 - 1 - c.val = (n - 1 - c.val) + 1 by omega, ← List.range'_append_1,
        List.reverse_append, KLRAlgebra.ψw_append,
        show q + 1 + c.val + (n - 1 - c.val) = q + n by omega]
      simp only [List.range'_one, List.reverse_singleton, KLRAlgebra.ψw_cons, KLRAlgebra.ψw_nil,
        mul_one, mul_assoc]
    have hlast : (List.range' (q + 1 + n) (n + 1 - 1 - n)) = [] := by
      rw [show n + 1 - 1 - n = 0 by omega]; rfl
    rw [hψ, ← mul_assoc, show (⟨q + (n + 1), h⟩ : Fin (Multiset.card μ)) = ⟨q + n + 1, h⟩ from
      rfl, hx, sub_mul, mul_assoc, x_passing_mul_underLeft q n (by omega), mul_sub,
      Finset.mul_sum, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, hterm, hlast, List.reverse_nil, KLRAlgebra.ψw_nil,
      one_mul]
    rw [← mul_assoc]
    abel

theorem pow_mul_eq_of_cut {A : Type*} [Ring A] {e y z : A} (h : y * e = z * e)
    (hz : Commute z e) (n : ℕ) : y ^ n * e = z ^ n * e := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_assoc, h, hz.eq, ← mul_assoc, ih, mul_assoc, ← hz.eq, ← mul_assoc,
      ← pow_succ]

/-- Two pairs of elements which agree after an idempotent `e` commuting with them evaluate every
polynomial alike after `e`. -/
theorem ncEval_two_mul_of_cut {A : Type*} [Ring A] [Algebra k A] {e : A} (y z : Fin 2 → A)
    (hy : ∀ a, y a * e = z a * e) (hze : ∀ a, Commute (z a) e)
    (P : MvPolynomial (Fin 2) k) : ncEval y P * e = ncEval z P * e := by
  unfold ncEval
  rw [Finsupp.sum, Finsupp.sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, mul_assoc,
    Fin.succ_zero_eq_one]
  congr 1
  rw [pow_mul_eq_of_cut (hy 1) (hze 1), ((hze 1).pow_left _).eq, ← mul_assoc,
    pow_mul_eq_of_cut (hy 0) (hze 0), mul_assoc, ← ((hze 1).pow_left _).eq]

theorem ncEval_X_pow_fin_two {A : Type*} [Ring A] [Algebra k A] (y : Fin 2 → A) (c : Fin 2)
    (n : ℕ) : ncEval y (MvPolynomial.X c ^ n : MvPolynomial (Fin 2) k) = y c ^ n := by
  rw [MvPolynomial.X_pow_eq_monomial]
  unfold ncEval
  change (Finsupp.single _ _).sum _ = _
  rw [Finsupp.sum_single_index (by simp), map_one, one_mul]
  fin_cases c <;> simp [List.ofFn_succ, Finsupp.single_apply]

theorem ncEval_zero' {A : Type*} [Ring A] [Algebra k A] {n : ℕ} (y : Fin n → A) :
    ncEval y (0 : MvPolynomial (Fin n) k) = 0 := by
  simp [ncEval]

end Generic

section Square

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "Eat" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "μ" => midMapKLR j hj Q Λ Λc ν ν₀

/-- **The quadratic relation of `λ⁺` on two old strands**, below the window at `n`: the old
strands `p, p + 1` of `s` sit at `c, c + 1`. -/
theorem ψ_sq_mul_eSum_insertSet (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) {p c : ℕ}
    (hp : p + 1 < m) (hc : (p + 1 < n ∧ c = p) ∨ (n ≤ p ∧ c = p + N)) (hcM : c + 1 < M) :
    (KLRAlgebra.ψ c * KLRAlgebra.ψ c * Eat s n hn : Rp) =
      if s.lbl ⟨p, by omega⟩ = s.lbl ⟨p + 1, hp⟩ then 0 else
        ncEval ![KLRAlgebra.x ⟨c, by omega⟩, KLRAlgebra.x ⟨c + 1, hcM⟩]
          (stendhalQ Q Λ (s.lbl ⟨p, by omega⟩) (s.lbl ⟨p + 1, hp⟩)) * Eat s n hn := by
  rw [eSum_insertSet, Finset.mul_sum]
  have hl : ∀ w : Seq (stendhalWeight 2 ν₀),
      (insertSeq s n hn (Seq.map (cupColour j hj) w)).lbl ⟨c, by omega⟩ =
          oldColour j hj (s.lbl ⟨p, by omega⟩) ∧
        (insertSeq s n hn (Seq.map (cupColour j hj) w)).lbl ⟨c + 1, hcM⟩ =
          oldColour j hj (s.lbl ⟨p + 1, hp⟩) := by
    intro w
    rcases hc with ⟨hp', rfl⟩ | ⟨hp', rfl⟩
    · exact ⟨insertSeq_lbl_lt s hn _ _ (by dsimp only; omega) rfl,
        insertSeq_lbl_lt s hn _ _ (by dsimp only; omega) rfl⟩
    · exact ⟨insertSeq_lbl_ge s hn _ _ (by dsimp only; omega) rfl,
        insertSeq_lbl_ge s hn _ _ (by dsimp only; omega) (by dsimp only; omega)⟩
  split_ifs with heq
  · refine Finset.sum_eq_zero fun w _ => ?_
    rw [KLRAlgebra.ψ_sq c hcM, (hl w).1, (hl w).2, heq]
    simp
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hne := (oldColour_injective j hj).ne heq
    rw [KLRAlgebra.ψ_sq c hcM, (hl w).1, (hl w).2]
    simp only [hne, ↓reduceIte]
    rw [stendhalQ_oldColour]

omit [DecidableEq I] in
theorem crossPos_add_one_lt {n p : ℕ} (hp : p + 1 < m) :
    crossPos n N p + 1 < M := by
  have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  unfold crossPos; split_ifs <;> omega

/-- A dot outside the window carries the exit diagrams along. -/
theorem x_mul_mem_exitSpan (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (a : Fin M)
    (ha : a.val < n ∨ n + N ≤ a.val) {y : Rp} (hy : y ∈ exitSpan Q Λ Λc j hj s n hn) :
    KLRAlgebra.x a * y ∈ exitSpan Q Λ Λc j hj s n hn := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, r, rfl⟩ := hy
    rw [← mul_assoc, (commute_x_insertMap s hn a ha z).eq, mul_assoc]
    exact mem_exitSpan _ hn hz _
  | zero => rw [mul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
  | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h

/-- **Dots on the passing strand slide down a passage** to the left of the maximum, modulo
diagrams in which a strand leaves the window at the top. -/
theorem passing_x_pow_mem (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) (a : ℕ) :
    Eat s q (Nat.le_of_succ_le hq) *
        (KLRAlgebra.x ⟨q + N, add_N_lt_M_of_succ_le hq⟩ ^ a * underLeft N q -
          underLeft N q * KLRAlgebra.x ⟨q, lt_M_of_succ_le hq⟩ ^ a) *
        Eat s (q + 1) hq ∈ exitSpan Q Λ Λc j hj s q (Nat.le_of_succ_le hq) := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  set y : Rp := KLRAlgebra.x ⟨q + N, add_N_lt_M_of_succ_le hq⟩
  set z : Rp := KLRAlgebra.x ⟨q, lt_M_of_succ_le hq⟩
  have hy0 : Commute y (Eat s q (Nat.le_of_succ_le hq)) := commute_x_eSum _ _
  have hz1 : Commute z (Eat s (q + 1) hq) := commute_x_eSum _ _
  have h1 : Eat s q (Nat.le_of_succ_le hq) * (y * underLeft N q - underLeft N q * z) *
      Eat s (q + 1) hq ∈ exitSpan Q Λ Λc j hj s q (Nat.le_of_succ_le hq) := by
    have hp := (x_passing_mul_underLeft q N (by omega) :
      (KLRAlgebra.x ⟨q + N, by omega⟩ * KLRAlgebra.ψw (List.range' q N).reverse : Rp) = _)
    have hD : y * underLeft N q - underLeft N q * z =
        -∑ c : Fin N, KLRAlgebra.ψw (List.range' (q + 1 + c.val) (N - 1 - c.val)).reverse *
          KLRAlgebra.eqIdem (q + c.val) (by omega) *
          KLRAlgebra.ψw (List.range' q c.val).reverse := by
      rw [underLeft, hp]; abel
    rw [hD, mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    refine neg_mem (Submodule.sum_mem _ fun c _ => ?_)
    simpa only [mul_assoc] using exitTermLeft_mem (Q := Q) (Λ := Λ) (Λc := Λc) s hq c
  induction a with
  | zero => simp
  | succ a ih =>
    set E0 : Rp := Eat s q (Nat.le_of_succ_le hq)
    set E1 : Rp := Eat s (q + 1) hq
    set U : Rp := underLeft N q
    have e1 : y * E0 = E0 * y := hy0.eq
    have e2 : E1 * z ^ a = z ^ a * E1 := (hz1.pow_left a).eq.symm
    have : E0 * (y ^ (a + 1) * U - U * z ^ (a + 1)) * E1 =
        y * (E0 * (y ^ a * U - U * z ^ a) * E1) + E0 * (y * U - U * z) * E1 * z ^ a := by
      rw [show y * (E0 * (y ^ a * U - U * z ^ a) * E1) =
          y * E0 * (y ^ a * U - U * z ^ a) * E1 by noncomm_ring, e1,
        show E0 * (y * U - U * z) * E1 * z ^ a = E0 * (y * U - U * z) * (E1 * z ^ a) by
          noncomm_ring, e2, pow_succ', pow_succ']
      noncomm_ring
    rw [this]
    refine add_mem (x_mul_mem_exitSpan s _ _ (Or.inr (by dsimp only; omega)) ih)
      (exitSpan_mul_right s _ h1 _)

theorem midSlides_of_mem_midExit {y : Rp} (hy : y ∈ midExit j hj Q Λ Λc ν ν₀) :
    MidSlides j hj Q Λ Λc ν ν₀ y := fun w => by
  refine sub_mem (midExit_mul_right hy _) ?_
  refine Submodule.iSup_induction _ (motive := fun y => μ w * y ∈ midExit j hj Q Λ Λc ν ν₀) hy
    (fun s y hy => ?_) ?_ ?_
  · induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, r, rfl⟩ := hy
      rw [← mul_assoc, midMapKLR_mul_insertMap]
      exact mem_midExit s (mem_exitSpan s _ ((capNull Q Λc ν₀).mul_mem_left w z hz) _)
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  · rw [mul_zero]; exact zero_mem _
  · intro y y' h h'; rw [mul_add]; exact add_mem h h'

/-- A polynomial in the dots of `T̃^λ` on the loading `t` is the same polynomial in the dots of
`λ⁺` at their positions. -/
theorem ncEval_midDot_mul_eSum (t : Seq (stendhalWeight ℓ ν)) (a b : Fin m)
    (P : MvPolynomial (Fin 2) k) :
    ncEval ![midDot j hj Q Λ Λc ν ν₀ a, midDot j hj Q Λ Λc ν ν₀ b] P * E t =
      ncEval ![KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀)
          ⟨midPos j t, Nat.lt_succ_of_le (midPos_le j t)⟩ a),
        KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀)
          ⟨midPos j t, Nat.lt_succ_of_le (midPos_le j t)⟩ b)] P * E t := by
  refine ncEval_two_mul_of_cut _ _ (fun c => ?_) (fun c => ?_) P
  · fin_cases c <;> exact midDot_mul_eSum t _
  · fin_cases c <;> exact commute_x_eSum _ _

/-- Polynomials in dots at equal positions agree. -/
theorem ncEval_x_congr (a b a' b' : Fin M) (ha : a.val = a'.val) (hb : b.val = b'.val)
    (P : MvPolynomial (Fin 2) k) :
    ncEval ![(KLRAlgebra.x a : Rp), KLRAlgebra.x b] P =
      ncEval ![(KLRAlgebra.x a' : Rp), KLRAlgebra.x b'] P := by
  rw [Fin.ext ha, Fin.ext hb]

/-- The two crossings `ψ_p` of the square, on the loading `s`. -/
theorem midCross_mul_midCross_mul_midIdem (s : Seq (stendhalWeight ℓ ν)) (p : ℕ) :
    midCross j hj Q Λ Λc ν ν₀ p * midCross j hj Q Λ Λc ν ν₀ p * midIdem j hj Q Λ Λc ν ν₀ s =
      midCrossAt j hj Q Λ Λc ν ν₀ (sadj m p • s) p * midCrossAt j hj Q Λ Λc ν ν₀ s p := by
  rw [midIdem, mul_assoc, midCross_mul_eSum]
  conv_lhs => rw [← eSum_mul_midCrossAt s p, ← mul_assoc, midCross_mul_eSum]

/-- The crossing `ψ_p` on the loading `t`, away from `λ_{j+1}`. -/
theorem midCrossAt_of_far (t : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (h1 : p + 1 ≠ midPos j t) (h2 : p ≠ midPos j t) :
    midCrossAt j hj Q Λ Λc ν ν₀ t p = KLRAlgebra.ψ (crossPos (midPos j t) N p) * E t := by
  unfold midCrossAt
  split_ifs
  rfl

/-- The crossing `ψ_p` on the loading `t`, of a black strand with `λ_{j+1}` on its right. -/
theorem midCrossAt_of_left (t : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p + 1 = midPos j t) {i₀ : I} (ht : t.lbl ⟨p, by omega⟩ = .inl i₀) :
    midCrossAt j hj Q Λ Λc ν ν₀ t p = KLRAlgebra.ψ (p + N) * underLeft N p * E t := by
  unfold midCrossAt
  split_ifs
  all_goals first | omega | rw [ht]

theorem midCrossAt_of_left_red (t : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p + 1 = midPos j t) {r : Fin ℓ} (ht : t.lbl ⟨p, by omega⟩ = .inr r) :
    midCrossAt j hj Q Λ Λc ν ν₀ t p = 0 := by
  unfold midCrossAt
  split_ifs
  all_goals first | omega | rw [ht]

/-- The crossing `ψ_p` on the loading `t`, of `λ_{j+1}` with a black strand on its right. -/
theorem midCrossAt_of_right (t : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p = midPos j t) {i₀ : I} (ht : t.lbl ⟨p + 1, hp⟩ = .inl i₀) :
    midCrossAt j hj Q Λ Λc ν ν₀ t p = Ring.inverse (cupScalar Q ν₀ i₀) •
      (underRight N p * KLRAlgebra.ψ (p + N) * E t) := by
  unfold midCrossAt
  split_ifs
  all_goals first | omega | rw [ht]

theorem midCrossAt_of_right_red (t : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p = midPos j t) {r : Fin ℓ} (ht : t.lbl ⟨p + 1, hp⟩ = .inr r) :
    midCrossAt j hj Q Λ Λc ν ν₀ t p = 0 := by
  unfold midCrossAt
  split_ifs
  all_goals first | omega | rw [ht]

/-- **The square of a crossing away from `λ_{j+1}`** is the quadratic relation of `λ⁺`. -/
theorem midCrossAt_sq_far (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hf : p + 1 < midPos j s ∨ midPos j s + 1 ≤ p) :
    midCrossAt j hj Q Λ Λc ν ν₀ (sadj m p • s) p * midCrossAt j hj Q Λ Λc ν ν₀ s p =
      if s.lbl ⟨p, by omega⟩ = s.lbl ⟨p + 1, hp⟩ then 0 else
        ncEval ![midDot j hj Q Λ Λc ν ν₀ ⟨p, by omega⟩, midDot j hj Q Λ Λc ν ν₀ ⟨p + 1, hp⟩]
          (stendhalQ Q Λ (s.lbl ⟨p, by omega⟩) (s.lbl ⟨p + 1, hp⟩)) *
          midIdem j hj Q Λ Λc ν ν₀ s := by
  have hm := midPos_sadj_of_far j s hp hf
  have hcp : (p + 1 < midPos j s ∧ crossPos (midPos j s) N p = p) ∨
      (midPos j s ≤ p ∧ crossPos (midPos j s) N p = p + N) := by
    unfold crossPos; split_ifs <;> omega
  rw [midCrossAt_of_far (sadj m p • s) hp (by omega) (by omega), mul_assoc,
    eSum_mul_midCrossAt, hm, midCrossAt_of_far s hp (by omega) (by omega), ← mul_assoc,
    ψ_sq_mul_eSum_insertSet s (midPos_le j s) hp hcp (crossPos_add_one_lt hp), midIdem]
  split_ifs
  · rfl
  · rw [ncEval_midDot_mul_eSum]
    congr 1
    refine ncEval_x_congr _ _ _ _ ?_ ?_ _ <;> rw [dotPos_val'] <;> dsimp only <;>
      unfold crossPos <;> split_ifs <;> omega

end Square

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Model

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Eat" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "E" s:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s))
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "σ" => midStendhal j hj Q Λ Λc ν ν₀
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

/-- Diagrams acting alike on the elements `e Z ⊗ v` act alike on the model. -/
theorem MidRel.of_tmul {Y Y' : Rp}
    (h : ∀ (Z : Tp) (v : L), (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot Y * σ 1 * Z)) v :
        MidModel j hj Q Λ Λc ν ν₀ L) = Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot Y' * σ 1 * Z)) v) :
    MidRel j hj Q Λ Λc ν ν₀ L hL Y Y' := fun hY hY' => Ind.ext fun z v => by
  have hz : z = midGen j hj Q Λ Λc ν ν₀ z.1.unop := Subtype.ext (by
    change z.1 = op (σ 1 * z.1.unop)
    rw [op_mul, op_unop]
    have h2 : z.1 * op (σ 1) = z.1 := z.2
    exact h2.symm)
  rw [hz, midEnd_tmul, midEnd_tmul, h]

theorem tmul_midGen_smul (c : k) (Z : Tp) (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (c • Z)) v : MidModel j hj Q Λ Λc ν ν₀ L) =
      c • Ind.tmul (midGen j hj Q Λ Λc ν ν₀ Z) v := by
  rw [midModel_algebraMap_smul, Ind.smul_tmul, MulOpposite.algebraMap_apply, op_smul_midGen,
    ← Algebra.commutes, ← Algebra.smul_def]

theorem tmul_midGen_mul (A B : Tp) (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (A * B)) v : MidModel j hj Q Λ Λc ν ν₀ L) =
      (op B : Tpᵐᵒᵖ) • Ind.tmul (midGen j hj Q Λ Λc ν ν₀ A) v := by
  rw [Ind.smul_tmul, op_smul_midGen]

theorem tmul_op_algebraMap (y : Corner (midOp j hj Q Λ Λc ν ν₀)) (c : k) (v : L) :
    (Ind.tmul y (op (algebraMap k (StendhalAlgebra k Q Λc ν₀) c) • v) :
        MidModel j hj Q Λ Λc ν ν₀ L) = c • Ind.tmul y v := by
  rw [← Ind.op_smul_tmul, midModel_algebraMap_smul, Ind.smul_tmul]
  congr 1
  apply Subtype.ext
  change y.1 * op (σ (algebraMap k _ c)) = algebraMap k Tpᵐᵒᵖ c * y.1
  have hy : y.1 * op (σ 1) = y.1 := y.2
  rw [Algebra.algebraMap_eq_smul_one, map_smul, op_smul, mul_smul_comm, hy]
  exact Algebra.smul_def (A := Tpᵐᵒᵖ) c y.1

/-- **The square of the crossing of a black strand of colour `i₀` with `λ_{j+1}` on its
left**, from (max2) in the model: the dots `x_{p+N}^a` of the quadratic relation of `λ⁺` slide
down along the passage, and the loop under the maximum is the scalar `κ_{i₀}`. -/
theorem midRel_crossAt_sq_left (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hPL : PullOffLeft k Q Λc ν₀ L) (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (h : p + 1 < m)
    (hc : p + 1 = midPos j s) {i₀ : I} (hs : s.lbl ⟨p, by omega⟩ = .inl i₀) {r : Fin ℓ}
    (hr : s.lbl ⟨p + 1, h⟩ = .inr r) :
    MidRel j hj Q Λ Λc ν ν₀ L hL
      (midCrossAt j hj Q Λ Λc ν ν₀ (sadj m p • s) p * midCrossAt j hj Q Λ Λc ν ν₀ s p)
      (KLRAlgebra.x ⟨p, lt_M_of_succ_le h.le⟩ ^ Λ r i₀ * E s) := by
  have hq : p + 1 ≤ m := h.le
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  set κ := cupScalar Q ν₀ i₀
  set a := Λ r i₀
  set E0 : Rp := Eat s p (Nat.le_of_succ_le hq)
  set E1 : Rp := Eat s (p + 1) hq
  set y : Rp := KLRAlgebra.x ⟨p + N, add_N_lt_M_of_succ_le hq⟩
  set z : Rp := KLRAlgebra.x ⟨p, lt_M_of_succ_le hq⟩
  have hE : (E s : Rp) = E1 :=
    congrArg (KLRAlgebra.eSum _) (insertSet_congr' s (midPos_le j s) hq hc.symm)
  have hE1 : E1 * E1 = E1 := (KLRAlgebra.eSum_idem _).eq
  have hL1 : underLeft N p * E1 = E0 * underLeft N p := underLeft_mul_eSum s hq
  have hL2 : underLeft N p * E1 = E0 * (underLeft N p * E1) := by
    conv_lhs => rw [← hE1, ← mul_assoc, hL1]
    rw [mul_assoc]
  have hR : underRight N p * E0 = E1 * underRight N p := underRight_mul_eSum Q Λ Λc s hq
  have hy0 : y ^ a * E0 = E0 * y ^ a := ((commute_x_eSum _ _).pow_left a).eq
  have hz : z ^ a * E1 = E1 * z ^ a := ((commute_x_eSum _ _).pow_left a).eq
  have key : ∀ X : Rp, KLRAlgebra.ψ (p + N) * (KLRAlgebra.ψ (p + N) * (E0 * X)) =
      y ^ a * (E0 * X) := fun X => by
    have h2 := ψ_sq_mul_eSum_insertSet (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) s
      (Nat.le_of_succ_le hq) h (c := p + N) (Or.inr ⟨le_rfl, rfl⟩) (by omega)
    rw [hs, hr] at h2
    simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inl_inr, ncEval_X_pow_fin_two,
      Matrix.cons_val_zero] at h2
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, h2, mul_assoc]
  have hY : midCrossAt j hj Q Λ Λc ν ν₀ (sadj m p • s) p * midCrossAt j hj Q Λ Λc ν ν₀ s p =
      Ring.inverse κ • (underRight N p * (y ^ a * (E0 * (underLeft N p * E1)))) := by
    have hm' := midPos_sadj_left j s h hc
    have hs' : (sadj m p • s).lbl ⟨p + 1, h⟩ = .inl i₀ :=
      (lbl_sadj_of_swapNat s h _ ⟨p, by omega⟩ (by simp [swapNat])).trans hs
    rw [midCrossAt_of_right (sadj m p • s) h hm'.symm hs', smul_mul_assoc, mul_assoc,
      eSum_mul_midCrossAt, midCrossAt_of_left s h hc hs, hE]
    congr 1
    simp only [mul_assoc]
    nth_rewrite 1 [hL2]
    rw [key]
  have hD := passing_x_pow_mem (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀)
    s hq a
  have hsub : Ring.inverse κ • (underRight N p * (y ^ a * (E0 * (underLeft N p * E1)))) -
      Ring.inverse κ • (underRight N p * (E0 * (underLeft N p * (z ^ a * E1)))) ∈
        midExit j hj Q Λ Λc ν ν₀ := by
    have h1 := Submodule.smul_mem _ (Ring.inverse κ) (underRight_mul_mem Q Λ Λc s hq hD)
    rw [exitSpan_congr' s hq (midPos_le j s) hc] at h1
    refine mem_midExit s ?_
    convert h1 using 1
    rw [← smul_sub, ← mul_sub, ← mul_assoc (y ^ a) E0, hy0]
    congr 2
    noncomm_ring
  have hYs := (midSlides_midCrossAt (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
    (ν := ν) (ν₀ := ν₀) (sadj m p • s) p).mul (midSlides_midCrossAt s p)
  rw [hY] at hYs
  have hW : MidSlides j hj Q Λ Λc ν ν₀
      (Ring.inverse κ • (underRight N p * (E0 * (underLeft N p * (z ^ a * E1))))) := by
    have h' := hYs.add ((midSlides_of_mem_midExit hsub).smul (-1 : k))
    rwa [neg_one_smul, ← sub_eq_add_neg, sub_sub_cancel] at h'
  rw [hY]
  refine MidRel.trans hW (MidRel.of_sub_mem hsub) (MidRel.of_tmul fun Z v => ?_)
  have hWf : underRight N p * (E0 * (underLeft N p * (z ^ a * E1))) =
      E1 * (underRight N p * underLeft N p) * E1 * (z ^ a * E1) := by
    rw [← mul_assoc (underRight N p) E0, hR, hz]
    simp only [mul_assoc]
    rw [← mul_assoc E1 E1, hE1]
  have hB : E1 * (z ^ a * E1) = z ^ a * E1 := by rw [hz, ← mul_assoc, hE1]
  have e1 : bot (Ring.inverse κ • (E1 * (underRight N p * underLeft N p) * E1 * (z ^ a * E1))) *
      σ 1 * Z = Ring.inverse κ • (bot (E1 * (underRight N p * underLeft N p) * E1) *
        (bot (z ^ a * E1) * σ 1 * Z)) := by
    rw [map_smul, map_mul, smul_mul_assoc, smul_mul_assoc,
      mul_assoc (bot (E1 * (underRight N p * underLeft N p) * E1)),
      mul_assoc (bot (E1 * (underRight N p * underLeft N p) * E1))]
  have hfin : bot E1 * (bot (z ^ a * E1) * σ 1 * Z) = bot (z ^ a * E1) * σ 1 * Z := by
    rw [← mul_assoc, ← mul_assoc, ← map_mul, hB]
  rw [hWf, e1, tmul_midGen_smul, tmul_midGen_mul,
    leftLoop_midModel Q Λ Λc L hPL i₀ s hq hc hs, ← tmul_midGen_mul, tmul_op_algebraMap,
    smul_smul, Ring.inverse_mul_cancel _ (hκ i₀), one_smul, hfin, hE]

/-- **The square of the crossing of `λ_{j+1}` with a black strand of colour `i₀` on its
right**, from the pull-off identity of Lemma 7.16 in the model: the loop under the maximum is
the scalar `κ_{i₀}`, and what remains is the quadratic relation of `λ⁺`. -/
theorem midRel_crossAt_sq_right (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i))
    (hP : PullOff k Q Λc ν₀ L) (s : Seq (stendhalWeight ℓ ν)) (h : midPos j s + 1 < m)
    {i₀ : I} (hs : s.lbl ⟨midPos j s + 1, h⟩ = .inl i₀) :
    MidRel j hj Q Λ Λc ν ν₀ L hL
      (midCrossAt j hj Q Λ Λc ν ν₀ (sadj m (midPos j s) • s) (midPos j s) *
        midCrossAt j hj Q Λ Λc ν ν₀ s (midPos j s))
      (KLRAlgebra.ψ (midPos j s + N) * KLRAlgebra.ψ (midPos j s + N) * E s) := by
  set κ := cupScalar Q ν₀ i₀
  have hm' := midPos_sadj_right j s h rfl
  have hs' := lbl_sadj_midPos s h hs
  have hψE := ψ_crossPos_mul_eSum (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
    (ν₀ := ν₀) s (midPos_le j s) (p := midPos j s) (Or.inr le_rfl)
  rw [crossPos_self] at hψE
  have hab : Eat (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s) *
      (KLRAlgebra.ψ (midPos j s + N) * E s) = KLRAlgebra.ψ (midPos j s + N) * E s := by
    rw [hψE, ← mul_assoc, (KLRAlgebra.eSum_idem _).eq]
  have hY : midCrossAt j hj Q Λ Λc ν ν₀ (sadj m (midPos j s) • s) (midPos j s) *
        midCrossAt j hj Q Λ Λc ν ν₀ s (midPos j s) =
      Ring.inverse κ • (KLRAlgebra.ψ (midPos j s + N) *
        (underLeft N (midPos j s) * underRight N (midPos j s)) *
        Eat (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s) *
        (KLRAlgebra.ψ (midPos j s + N) * E s)) := by
    rw [midCrossAt_of_left (sadj m (midPos j s) • s) h hm'.symm hs', mul_assoc,
      eSum_mul_midCrossAt, midCrossAt_of_right s h rfl hs, mul_smul_comm]
    congr 1
    simp only [mul_assoc]
    rw [hab]
  rw [hY]
  refine MidRel.of_tmul fun Z v => ?_
  have e1 : bot (Ring.inverse κ • (KLRAlgebra.ψ (midPos j s + N) *
        (underLeft N (midPos j s) * underRight N (midPos j s)) *
        Eat (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s) *
        (KLRAlgebra.ψ (midPos j s + N) * E s))) * σ 1 * Z =
      Ring.inverse κ • (bot (KLRAlgebra.ψ (midPos j s + N) *
        (underLeft N (midPos j s) * underRight N (midPos j s)) *
        Eat (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s)) *
        (bot (KLRAlgebra.ψ (midPos j s + N) * E s) * σ 1 * Z)) := by
    rw [map_smul, map_mul, smul_mul_assoc, smul_mul_assoc]
    simp only [mul_assoc]
  have hfin : bot (KLRAlgebra.ψ (midPos j s + N) *
        Eat (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s)) *
        (bot (KLRAlgebra.ψ (midPos j s + N) * E s) * σ 1 * Z) =
      bot (KLRAlgebra.ψ (midPos j s + N) * KLRAlgebra.ψ (midPos j s + N) * E s) * σ 1 * Z := by
    rw [← mul_assoc, ← mul_assoc, ← map_mul, mul_assoc (KLRAlgebra.ψ _), hab, ← mul_assoc]
  rw [e1, tmul_midGen_smul, tmul_midGen_mul, rightLoop_midModel Q Λ Λc L hP i₀ s h hs,
    ← tmul_midGen_mul, tmul_op_algebraMap, smul_smul, Ring.inverse_mul_cancel _ (hκ i₀),
    one_smul, hfin]

/-- **The quadratic relation on the model of a cap after `λ_j`** (Webster, arXiv:1309.3796v3,
proof of Lemma 7.17): the square of the crossing `ψ_p` of `T̃^λ` acts on the model as
`Q_{i_p i_{p+1}}(x_p, x_{p+1}) e(i)`, and as `0` on equal labels. -/
theorem midRel_cross_sq (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hP : PullOff k Q Λc ν₀ L)
    (hPL : PullOffLeft k Q Λc ν₀ L) (p : ℕ) (h : p + 1 < m) (i : Seq (stendhalWeight ℓ ν)) :
    MidRel j hj Q Λ Λc ν ν₀ L hL
      (midCross j hj Q Λ Λc ν ν₀ p * midCross j hj Q Λ Λc ν ν₀ p * midIdem j hj Q Λ Λc ν ν₀ i)
      (if i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 1, h⟩ then 0 else
        ncEval ![midDot j hj Q Λ Λc ν ν₀ ⟨p, by omega⟩, midDot j hj Q Λ Λc ν ν₀ ⟨p + 1, h⟩]
          (stendhalQ Q Λ (i.lbl ⟨p, by omega⟩) (i.lbl ⟨p + 1, h⟩)) *
          midIdem j hj Q Λ Λc ν ν₀ i) := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  rw [midCross_mul_midCross_mul_midIdem]
  by_cases h1 : p + 1 = midPos j i
  · have hjl := lt_of_midPos_lt j (s := i) (p := p + 1) h h1.ge
    obtain ⟨b, hb, hlb⟩ := midPos_of_lt j i hjl
    have hred : i.lbl ⟨p + 1, h⟩ = .inr ⟨j, hjl⟩ := by
      rw [show (⟨p + 1, h⟩ : Fin m) = b from Fin.ext (by rw [hb]; exact h1)]; exact hlb
    rcases hl : i.lbl ⟨p, by omega⟩ with i₀ | r
    · have hd : dotPos (j := j) (hj := hj) (ν₀ := ν₀)
          ⟨midPos j i, Nat.lt_succ_of_le (midPos_le j i)⟩ ⟨p, by omega⟩ =
            ⟨p, lt_M_of_succ_le h.le⟩ :=
        Fin.ext (by rw [dotPos_val']; dsimp only; split_ifs <;> omega)
      rw [hred]
      simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inl_inr]
      rw [midIdem, ncEval_midDot_mul_eSum, ncEval_X_pow_fin_two, Matrix.cons_val_zero, hd]
      exact midRel_crossAt_sq_left hκ hPL i h h1 hl hred
    · rw [midCrossAt_of_left_red i h h1 hl, mul_zero, hred]
      refine MidRel.of_eq ?_
      split_ifs
      · rfl
      · rw [show stendhalQ Q Λ (.inr r) (.inr ⟨j, hjl⟩) = 0 from rfl, ncEval_zero', zero_mul]
  by_cases h2 : p = midPos j i
  · subst h2
    have hjl := lt_of_midPos_lt j (s := i) (p := midPos j i) (by omega) le_rfl
    obtain ⟨b, hb, hlb⟩ := midPos_of_lt j i hjl
    have hred : i.lbl ⟨midPos j i, by omega⟩ = .inr ⟨j, hjl⟩ := by
      rw [show (⟨midPos j i, by omega⟩ : Fin m) = b from Fin.ext hb.symm]; exact hlb
    rcases hl : i.lbl ⟨midPos j i + 1, h⟩ with i₀ | r
    · convert midRel_crossAt_sq_right hκ hP i h hl using 1
      rw [ψ_sq_mul_eSum_insertSet (j := j) (hj := hj) i (midPos_le j i) h
        (c := midPos j i + N) (Or.inr ⟨le_rfl, rfl⟩) (by omega), hl, midIdem]
      split_ifs
      · rfl
      · rw [ncEval_midDot_mul_eSum]
        congr 1
        refine ncEval_x_congr _ _ _ _ ?_ ?_ _ <;> rw [dotPos_val'] <;> dsimp only <;>
          split_ifs <;> omega
    · rw [midCrossAt_of_right_red i h rfl hl, mul_zero, hred]
      refine MidRel.of_eq ?_
      split_ifs
      · rfl
      · rw [show stendhalQ Q Λ (.inr ⟨j, hjl⟩) (.inr r) = 0 from rfl, ncEval_zero', zero_mul]
  exact MidRel.of_eq (midCrossAt_sq_far i h (by omega))

end Model

end Categorification.Stendhal.CupCap
