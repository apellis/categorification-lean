/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapModelMap

/-!
# Strands passing under the maximum of the cap to the right

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. This is the mirror of
`CupCap.slides`: a strand left of the maximum of the cap passes under it to the right
(`underLeft N q`, the strand at the bottom position `q` moving to the top position `q + N`). The
passage carries the bottom loadings with window at `q + 1` to those with window at `q`
(`underLeft_mul_e_insertSeq`).

A diagram `z` at the maximum slides through the passage up to diagrams in which a strand leaves the
window at its top left end: `ι_q(z) · underLeft N q - underLeft N q · ι_{q+1}(z)` lies in
`exitSpan` at the window `q` (`CupCap.slidesLeft`). A dot moved through the passage leaves a term
in which a window strand of the colour of the passing strand is pulled out to the left end of the
window, and such a strand is black; a crossing leaves a braid defect of the same kind.

## Main results

* `CupCap.x_mul_underLeft`, `CupCap.ψ_mul_underLeft`: the KLR identities behind the sliding.
* `CupCap.slidesLeft`: every diagram at the maximum slides through a passage to the right modulo
  `exitSpan`.
* `CupCap.underLeft_mul_mem`: errors at the bottom of such a passage are errors at its top.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MvPolynomial

section Generic

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

theorem range'_split_reverse (q : ℕ) {c n : ℕ} (hc : c < n) :
    (List.range' q n).reverse = (List.range' (q + 1 + c) (n - 1 - c)).reverse ++
      (q + c) :: (List.range' q c).reverse := by
  rw [range'_split q hc]; simp

/-- A dot on a passing window strand, moved down through the passage `underLeft`: the error term
has the strand at the crossing joined to the passing strand. -/
theorem x_mul_underLeft {μ : Multiset I} {Q' : I → I → MvPolynomial (Fin 2) k} {q c n : ℕ}
    (hc : c < n) (h : q + n < Multiset.card μ) :
    (KLRAlgebra.x ⟨q + c, by omega⟩ * KLRAlgebra.ψw (List.range' q n).reverse :
        KLRAlgebra k Q' μ) =
      KLRAlgebra.ψw (List.range' q n).reverse * KLRAlgebra.x ⟨q + 1 + c, by omega⟩ +
        KLRAlgebra.ψw (List.range' (q + 1 + c) (n - 1 - c)).reverse *
          KLRAlgebra.eqIdem (q + c) (by omega) * KLRAlgebra.ψw (List.range' q c).reverse := by
  rw [range'_split_reverse q hc, KLRAlgebra.ψw_append, KLRAlgebra.ψw_cons]
  have h1 : Commute (KLRAlgebra.x ⟨q + c, by omega⟩ : KLRAlgebra k Q' μ)
      (KLRAlgebra.ψw (List.range' (q + 1 + c) (n - 1 - c)).reverse) :=
    KLRAlgebra.commute_x_ψw fun p hp => by
      rw [List.mem_reverse, List.mem_range'_1] at hp; dsimp only; omega
  have h2 : Commute (KLRAlgebra.x ⟨q + 1 + c, by omega⟩ : KLRAlgebra k Q' μ)
      (KLRAlgebra.ψw (List.range' q c).reverse) :=
    KLRAlgebra.commute_x_ψw fun p hp => by
      rw [List.mem_reverse, List.mem_range'_1] at hp; dsimp only; omega
  have h3 := KLRAlgebra.x_mul_ψ_self (k := k) (Q := Q') (ν := μ) (q + c) (by omega)
  rw [show (⟨q + c + 1, _⟩ : Fin (Multiset.card μ)) = ⟨q + 1 + c, by omega⟩ from
    Fin.ext (by simp; omega)] at h3
  rw [← mul_assoc, h1.eq, mul_assoc, ← mul_assoc _ (KLRAlgebra.ψ _), h3, add_mul,
    mul_assoc (KLRAlgebra.ψ _), h2.eq]
  noncomm_ring

theorem range'_split2_reverse (q : ℕ) {r n : ℕ} (hr : r + 1 < n) :
    (List.range' q n).reverse = (List.range' (q + 1 + (r + 1)) (n - 1 - (r + 1))).reverse ++
      (q + r + 1) :: (q + r) :: (List.range' q r).reverse := by
  rw [range'_split2 q hr]; simp

/-- A crossing of two passing window strands, moved down through the passage `underLeft`: the
error is a braid defect. -/
theorem ψ_mul_underLeft {μ : Multiset I} {Q' : I → I → MvPolynomial (Fin 2) k} {q r n : ℕ}
    (hr : r + 1 < n) :
    (KLRAlgebra.ψ (q + r) * KLRAlgebra.ψw (List.range' q n).reverse : KLRAlgebra k Q' μ) =
      KLRAlgebra.ψw (List.range' q n).reverse * KLRAlgebra.ψ (q + r + 1) +
        KLRAlgebra.ψw (List.range' (q + 1 + (r + 1)) (n - 1 - (r + 1))).reverse *
          (KLRAlgebra.ψ (q + r) * KLRAlgebra.ψ (q + r + 1) * KLRAlgebra.ψ (q + r) -
            KLRAlgebra.ψ (q + r + 1) * KLRAlgebra.ψ (q + r) * KLRAlgebra.ψ (q + r + 1)) *
          KLRAlgebra.ψw (List.range' q r).reverse := by
  rw [range'_split2_reverse q hr, KLRAlgebra.ψw_append, KLRAlgebra.ψw_cons, KLRAlgebra.ψw_cons]
  have h1 : Commute (KLRAlgebra.ψ (q + r) : KLRAlgebra k Q' μ)
      (KLRAlgebra.ψw (List.range' (q + 1 + (r + 1)) (n - 1 - (r + 1))).reverse) :=
    KLRAlgebra.commute_ψ_ψw fun p hp => by
      rw [List.mem_reverse, List.mem_range'_1] at hp; omega
  have h2 : Commute (KLRAlgebra.ψ (q + r + 1) : KLRAlgebra k Q' μ)
      (KLRAlgebra.ψw (List.range' q r).reverse) :=
    KLRAlgebra.commute_ψ_ψw fun p hp => by
      rw [List.mem_reverse, List.mem_range'_1] at hp; omega
  rw [← mul_assoc, h1.eq]
  simp only [mul_assoc, mul_sub, sub_mul]
  rw [← h2.eq]
  noncomm_ring

end Generic

section SlidingLeft

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)

/-! ### Strands leaving the window at its left end -/

omit [DecidableEq I] in
/-- The labels after the strand at `c` has moved to the front. -/
theorem lbl_exitLeft (w : Seq (stendhalWeight 2 ν₀)) {c : ℕ} (hc : c < N) :
    ((wordProd N (List.range' 0 c).reverse)⁻¹ • w).lbl ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le c) hc⟩ =
      w.lbl ⟨c, hc⟩ := by
  rw [← wordProd_reverse, List.reverse_reverse]
  exact KL2.lbl_range'_smul (by omega) w _ _ (by simp [KL2.rfun])

/-- A black strand at the maximum moved to the left end: the bottom loading is not of the form
`μ ⋯ μ*`. -/
theorem e_mul_exitLeft_mem_capNull (w : Seq (stendhalWeight 2 ν₀)) {c : ℕ} (hc : c < N)
    (hb : (w.lbl ⟨c, hc⟩).isLeft) :
    (KLRAlgebra.e w * KLRAlgebra.ψw (List.range' 0 c).reverse : Rc) ∈
      capNull (k := k) Q Λc ν₀ := by
  rw [KLRAlgebra.e_mul_ψw]
  refine TwoSidedIdeal.mul_mem_left _ _ _ (e_mem_capNull ?_)
  intro h
  have h2 : w.lbl ⟨c, hc⟩ = .inr 0 := (lbl_exitLeft w hc).symm.trans h.1
  simp [h2] at hb

theorem e_insertSeq_mul_exitLeft (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (w : Seq (stendhalWeight 2 ν₀)) {c : ℕ} (hc : c < N) :
    (KLRAlgebra.e (insertSeq s n hn (Seq.map (cupColour j hj) w)) *
        KLRAlgebra.ψw (List.range' n c).reverse : Rp) =
      ι s n hn (KLRAlgebra.e w * KLRAlgebra.ψw (List.range' 0 c).reverse) := by
  rw [insertMap_mul, insertMap_e, insertMap_ψw s hn _ (fun p hp => by
      rw [List.mem_reverse, List.mem_range'_1] at hp; omega),
    ← mul_assoc, e_insertSeq_mul_eSum, List.map_reverse, List.map_add_range', add_zero]

variable (Q Λ Λc j hj) in
/-- **Sliding through a passage to the right**: `ι_{s,q}(x) · underLeft N q ≡ underLeft N q ·
ι_{s,q+1}(x)` modulo diagrams in which a strand leaves the window at the top. -/
def SlidesLeft (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) (x : Rc) : Prop :=
  ι s q (Nat.le_of_succ_le hq) x * underLeft N q - underLeft N q * ι s (q + 1) hq x ∈
    exitSpan Q Λ Λc j hj s q (Nat.le_of_succ_le hq)

theorem slidesLeft_add (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) {x y : Rc}
    (hx : SlidesLeft Q Λ Λc j hj s hq x) (hy : SlidesLeft Q Λ Λc j hj s hq y) :
    SlidesLeft Q Λ Λc j hj s hq (x + y) := by
  unfold SlidesLeft
  rw [insertMap_add, insertMap_add]
  convert add_mem hx hy using 1
  noncomm_ring

theorem slidesLeft_mul (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) {x y : Rc}
    (hx : SlidesLeft Q Λ Λc j hj s hq x) (hy : SlidesLeft Q Λ Λc j hj s hq y) :
    SlidesLeft Q Λ Λc j hj s hq (x * y) := by
  unfold SlidesLeft
  rw [insertMap_mul, insertMap_mul]
  convert add_mem (insertMap_mul_mem_exitSpan s (Nat.le_of_succ_le hq) x hy)
    (exitSpan_mul_right s (Nat.le_of_succ_le hq) hx (ι s (q + 1) hq y)) using 1
  noncomm_ring

theorem slidesLeft_algebraMap (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) (c : k) :
    SlidesLeft Q Λ Λc j hj s hq (algebraMap k Rc c) := by
  unfold SlidesLeft
  rw [insertMap_algebraMap, insertMap_algebraMap, smul_mul_assoc, mul_smul_comm,
    underLeft_mul_eSum s hq, sub_self]
  exact zero_mem _

theorem slidesLeft_e (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m)
    (w : Seq (stendhalWeight 2 ν₀)) : SlidesLeft Q Λ Λc j hj s hq (KLRAlgebra.e w) := by
  unfold SlidesLeft
  rw [insertMap_e, insertMap_e, underLeft_mul_e_insertSeq Q Λ Λc s _ hq, sub_self]
  exact zero_mem _

/-- The errors of a passage to the right are fixed by the top window idempotent. -/
theorem eSum_mul_slidesLeftDiff (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m)
    (x : Rc) :
    E s q (Nat.le_of_succ_le hq) * (ι s q (Nat.le_of_succ_le hq) x * underLeft N q -
        underLeft N q * ι s (q + 1) hq x) =
      ι s q (Nat.le_of_succ_le hq) x * underLeft N q - underLeft N q * ι s (q + 1) hq x := by
  rw [mul_sub, ← mul_assoc, eSum_mul_insertMap, ← mul_assoc, ← underLeft_mul_eSum s hq,
    mul_assoc, eSum_mul_insertMap]

/-! ### The dot generators -/

/-- **The error terms of a dot sliding through a passage to the right** are diagrams in which a
strand leaves the window at its top left end. -/
theorem exitTermLeft_mem (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) (b : Fin N) :
    (E s q (Nat.le_of_succ_le hq) *
        (KLRAlgebra.ψw (List.range' (q + 1 + b.val) (N - 1 - b.val)).reverse *
        KLRAlgebra.eqIdem (q + b.val) (by have := add_lt_M (ν₀ := ν₀) hq b; omega) *
        KLRAlgebra.ψw (List.range' q b.val).reverse * E s (q + 1) hq) : Rp) ∈
      exitSpan Q Λ Λc j hj s q (Nat.le_of_succ_le hq) := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hb := b.2
  rw [eSum_insertSet, Finset.sum_mul]
  refine Submodule.sum_mem _ fun w _ => ?_
  simp only [← mul_assoc]
  rw [KLRAlgebra.e_mul_ψw, mul_assoc (KLRAlgebra.ψw _) (KLRAlgebra.e _), e_mul_eqIdem]
  split_ifs with hcond
  · rw [← KLRAlgebra.e_mul_ψw, mul_assoc (KLRAlgebra.e _) (KLRAlgebra.ψw _),
      (KLRAlgebra.commute_ψw_ψw fun p hp p' hp' => by
        rw [List.mem_reverse, List.mem_range'_1] at hp hp'; omega).eq, ← mul_assoc,
      e_insertSeq_mul_exitLeft s (Nat.le_of_succ_le hq) w b.2, mul_assoc]
    refine mem_exitSpan s _ (e_mul_exitLeft_mem_capNull w b.2 ?_) _
    rw [← wordProd_reverse, List.reverse_reverse] at hcond
    have e1 := KL2.lbl_range'_smul (q := q + 1 + b.val) (l := N - 1 - b.val) (by omega)
      (insertSeq s q (Nat.le_of_succ_le hq) (Seq.map (cupColour j hj) w)) ⟨q + b.val, by omega⟩
      ⟨q + b.val, by omega⟩ (by unfold KL2.rfun; dsimp only; split_ifs <;> omega)
    have e2 := KL2.lbl_range'_smul (q := q + 1 + b.val) (l := N - 1 - b.val) (by omega)
      (insertSeq s q (Nat.le_of_succ_le hq) (Seq.map (cupColour j hj) w))
      ⟨q + b.val + 1, by omega⟩ ⟨q + N, by omega⟩
      (by unfold KL2.rfun; dsimp only; split_ifs <;> omega)
    have h3 := e1.symm.trans (hcond.trans e2)
    rw [insertSeq_lbl_win s _ _ ⟨b.val, by rw [Multiset.card_map]; exact b.2⟩
        (by dsimp only), insertSeq_lbl_ge s _ _ ⟨q, by omega⟩ le_rfl rfl, Seq.map_lbl] at h3
    rcases hw : w.lbl ⟨b.val, b.2⟩ with i | r
    · rfl
    · exact absurd (hw ▸ h3).symm (oldColour_ne_cupColour_inr _ _)
  · rw [mul_zero, zero_mul, zero_mul]
    exact zero_mem _

/-- **The dot generators slide through a passage to the right.** -/
theorem slidesLeft_x (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) (b : Fin N) :
    SlidesLeft Q Λ Λc j hj s hq (KLRAlgebra.x b) := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hqN : q + N < M := by omega
  have hb := b.2
  unfold SlidesLeft
  rw [← eSum_mul_slidesLeftDiff]
  have hD : (ι s q (Nat.le_of_succ_le hq) (KLRAlgebra.x b) * underLeft N q -
        underLeft N q * ι s (q + 1) hq (KLRAlgebra.x b) : Rp) =
      KLRAlgebra.ψw (List.range' (q + 1 + b.val) (N - 1 - b.val)).reverse *
        KLRAlgebra.eqIdem (q + b.val) (by omega) *
        KLRAlgebra.ψw (List.range' q b.val).reverse * E s (q + 1) hq := by
    rw [insertMap_x, insertMap_x, mul_assoc, ← underLeft_mul_eSum s hq]
    simp only [← mul_assoc]
    rw [underLeft, x_mul_underLeft b.2 hqN]
    noncomm_ring
  rw [hD]
  exact exitTermLeft_mem s hq b

/-! ### The crossing generators -/

local notation "Uψ" q:max r:max =>
  (KLRAlgebra.ψw (List.reverse (List.range' (q + 1 + (r + 1)) (N - 1 - (r + 1)))) : Rp)

local notation "Dψ" q:max r:max => (KLRAlgebra.ψw (List.reverse (List.range' q r)) : Rp)

local notation "Bv" s:max q:max hq:max w:max =>
  KLRAlgebra.e (insertSeq s (q + 1) hq (Seq.map (cupColour j hj) w))

/-- The braid defect with no dots: the window strand that leaves the passage at the bottom left
is black, so the diagram lies in `exitSpan`. -/
theorem crossBaseLeft_mem (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) {r : ℕ}
    (hr : r + 1 < N) (w : Seq (stendhalWeight 2 ν₀)) :
    E s q (Nat.le_of_succ_le hq) * (Uψ q r * (Dψ q r * Bv s q hq w)) ∈
      exitSpan Q Λ Λc j hj s q (Nat.le_of_succ_le hq) := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hUD : Commute (Uψ q r) (Dψ q r) :=
    KLRAlgebra.commute_ψw_ψw fun p hp p' hp' => by
      rw [List.mem_reverse, List.mem_range'_1] at hp hp'; omega
  rw [eSum_insertSet, Finset.sum_mul]
  refine Submodule.sum_mem _ fun w' _ => ?_
  by_cases hb : (w'.lbl ⟨r, by omega⟩).isLeft
  · rw [← mul_assoc (KLRAlgebra.ψw _), hUD.eq, mul_assoc, ← mul_assoc (KLRAlgebra.e _),
      e_insertSeq_mul_exitLeft s _ w' (by omega : r < N)]
    exact mem_exitSpan s _ (e_mul_exitLeft_mem_capNull w' (by omega) hb) _
  · rw [← mul_assoc (KLRAlgebra.ψw _), ← KLRAlgebra.ψw_append, ← mul_assoc, KLRAlgebra.e_mul_ψw,
      mul_assoc, KLRAlgebra.e_mul_e]
    split_ifs with heq
    swap
    · rw [mul_zero]; exact zero_mem _
    exfalso
    have h1 := congrArg (fun t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) =>
      t.lbl ⟨q + r, by omega⟩) (inv_smul_eq_iff.mp heq)
    rw [insertSeq_lbl_win s _ _ ⟨r, by rw [Multiset.card_map]; omega⟩ rfl, Seq.map_lbl,
      wordProd_append, mul_smul,
      KL2.lbl_range'_reverse_smul (by omega) _ _ ⟨q + r, by omega⟩
        (by unfold KL2.lfun; dsimp only; split_ifs <;> omega),
      KL2.lbl_range'_reverse_smul (by omega) _ _ ⟨q, by omega⟩
        (by unfold KL2.lfun; dsimp only; split_ifs <;> omega),
      insertSeq_lbl_lt s _ _ ⟨q, by omega⟩ (by dsimp only; omega) rfl] at h1
    rcases hw : w'.lbl ⟨r, by omega⟩ with i | r'
    · simp [hw] at hb
    · exact oldColour_ne_cupColour_inr _ _ (hw ▸ h1).symm

theorem crossStepDownLeft (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) {r : ℕ}
    (w : Seq (stendhalWeight 2 ν₀)) (g : Rp) (b : Fin M)
    (hb : ∀ p ∈ (List.range' q r).reverse, (b : ℕ) ≠ p ∧ (b : ℕ) ≠ p + 1)
    (hg : E s q (Nat.le_of_succ_le hq) * (Uψ q r * (g * (Dψ q r * Bv s q hq w))) ∈
      exitSpan Q Λ Λc j hj s q (Nat.le_of_succ_le hq)) :
    E s q (Nat.le_of_succ_le hq) * (Uψ q r * (g * KLRAlgebra.x b * (Dψ q r * Bv s q hq w))) ∈
      exitSpan Q Λ Λc j hj s q (Nat.le_of_succ_le hq) := by
  have : (KLRAlgebra.x b * (Dψ q r * Bv s q hq w) : Rp) =
      Dψ q r * Bv s q hq w * KLRAlgebra.x b := by
    rw [← mul_assoc, (KLRAlgebra.commute_x_ψw hb).eq, mul_assoc, KLRAlgebra.x_mul_e, mul_assoc]
  rw [mul_assoc g, this]
  convert exitSpan_mul_right s _ hg (KLRAlgebra.x b) using 1
  simp only [mul_assoc]

theorem crossStepUpLeft (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) {r : ℕ}
    (hr : r + 1 < N) (w : Seq (stendhalWeight 2 ν₀)) (f : MvPolynomial (Fin M) k)
    (hg : E s q (Nat.le_of_succ_le hq) * (Uψ q r * (KLRAlgebra.pol f * (Dψ q r * Bv s q hq w))) ∈
      exitSpan Q Λ Λc j hj s q (Nat.le_of_succ_le hq)) :
    E s q (Nat.le_of_succ_le hq) * (Uψ q r * (KLRAlgebra.pol f * KLRAlgebra.x ⟨q + r,
        add_lt_M (Nat.le_of_succ_le hq) ⟨r, by omega⟩⟩ * (Dψ q r * Bv s q hq w))) ∈
      exitSpan Q Λ Λc j hj s q (Nat.le_of_succ_le hq) := by
  have hc : Commute (KLRAlgebra.pol f : Rp) (KLRAlgebra.x ⟨q + r,
      add_lt_M (Nat.le_of_succ_le hq) ⟨r, by omega⟩⟩) := by
    rw [← KLRAlgebra.pol_X, Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have hA : Commute (KLRAlgebra.x ⟨q + r, add_lt_M (ν₀ := ν₀) (Nat.le_of_succ_le hq)
      ⟨r, by omega⟩⟩ : Rp) (Uψ q r) :=
    KLRAlgebra.commute_x_ψw fun p hp => by
      rw [List.mem_reverse, List.mem_range'_1] at hp; dsimp only; omega
  rw [hc.eq, mul_assoc, ← mul_assoc (Uψ q r), ← hA.eq, mul_assoc,
    ← mul_assoc (E s q (Nat.le_of_succ_le hq)), ← KLRAlgebra.pol_X, ← KLRAlgebra.pol_mul_eSum,
    KLRAlgebra.pol_X,
    show (KLRAlgebra.x ⟨q + r, add_lt_M (ν₀ := ν₀) (Nat.le_of_succ_le hq) ⟨r, by omega⟩⟩ *
        E s q (Nat.le_of_succ_le hq) : Rp) =
      ι s q (Nat.le_of_succ_le hq) (KLRAlgebra.x ⟨r, by omega⟩) from
        (insertMap_x Q Λ Λc s (Nat.le_of_succ_le hq) ⟨r, by omega⟩).symm,
    ← mul_one (KLRAlgebra.x ⟨r, by omega⟩ : Rc), insertMap_mul, insertMap_one, mul_assoc]
  exact insertMap_mul_mem_exitSpan s _ _ hg

/-- The braid defect with dots on the three strands at the crossing lies in `exitSpan`: a dot on
the left strand slides up to the top of the window, dots on the two right strands slide down past
the exit. -/
theorem crossTermLeft_mem (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) {r : ℕ}
    (hr : r + 1 < N) (w : Seq (stendhalWeight 2 ν₀)) (p : MvPolynomial (Fin 3) k) :
    E s q (Nat.le_of_succ_le hq) * (Uψ q r * (KLRAlgebra.pol (MvPolynomial.rename
        ![⟨q + r, add_lt_M (ν₀ := ν₀) (Nat.le_of_succ_le hq) ⟨r, by omega⟩⟩,
          ⟨q + r + 1, by have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega⟩,
          ⟨q + r + 2, by have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega⟩] p) *
        (Dψ q r * Bv s q hq w))) ∈
      exitSpan Q Λ Λc j hj s q (Nat.le_of_succ_le hq) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.rename_C, MvPolynomial.algHom_C, ← Algebra.smul_def, mul_smul_comm,
      mul_smul_comm]
    exact Submodule.smul_mem _ c (crossBaseLeft_mem s hq hr w)
  | add p p' hp hp' =>
    rw [map_add, map_add, add_mul, mul_add, mul_add]
    exact add_mem hp hp'
  | mul_X p n hp =>
    rw [map_mul, MvPolynomial.rename_X, map_mul, KLRAlgebra.pol_X]
    fin_cases n
    · exact crossStepUpLeft s hq hr w _ hp
    · exact crossStepDownLeft (b := ⟨q + r + 1, by
          have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega⟩) s hq w _
        (fun p' hp' => by rw [List.mem_reverse, List.mem_range'_1] at hp'; dsimp only; omega) hp
    · exact crossStepDownLeft (b := ⟨q + r + 2, by
          have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega⟩) s hq w _
        (fun p' hp' => by rw [List.mem_reverse, List.mem_range'_1] at hp'; dsimp only; omega) hp

/-- **The crossing generators slide through a passage to the right.** -/
theorem slidesLeft_ψ (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) {r : ℕ}
    (hr : r + 1 < N) : SlidesLeft Q Λ Λc j hj s hq (KLRAlgebra.ψ r : Rc) := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  unfold SlidesLeft
  rw [← eSum_mul_slidesLeftDiff]
  have hD : (ι s q (Nat.le_of_succ_le hq) (KLRAlgebra.ψ r) * underLeft N q -
        underLeft N q * ι s (q + 1) hq (KLRAlgebra.ψ r) : Rp) =
      Uψ q r * ((KLRAlgebra.ψ (q + r) * KLRAlgebra.ψ (q + r + 1) * KLRAlgebra.ψ (q + r) -
            KLRAlgebra.ψ (q + r + 1) * KLRAlgebra.ψ (q + r) * KLRAlgebra.ψ (q + r + 1)) *
          (Dψ q r * E s (q + 1) hq)) := by
    rw [insertMap_ψ s _ hr, insertMap_ψ s hq hr, mul_assoc, ← underLeft_mul_eSum s hq,
      ← mul_assoc, underLeft, ψ_mul_underLeft (n := N) hr, show q + 1 + r = q + r + 1 by omega]
    noncomm_ring
  rw [hD]
  rw [eSum_insertSet Q Λ Λc s (n := q + 1), Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum]
  refine Submodule.sum_mem _ fun w _ => ?_
  rw [KLRAlgebra.ψw_mul_e, ← mul_assoc (_ - _), KLRAlgebra.braid (q + r) (by omega)]
  split_ifs
  · rw [mul_assoc (ncEval _ _), ← KLRAlgebra.ψw_mul_e, ncEval_x_three]
    exact crossTermLeft_mem s hq hr w _
  · rw [zero_mul, mul_zero, mul_zero]
    exact zero_mem _

/-- **Every diagram at the maximum slides through a passage to the right**, modulo diagrams in
which a strand leaves the window at the top. -/
theorem slidesLeft (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) (z : Rc) :
    SlidesLeft Q Λ Λc j hj s hq z := by
  induction z using KLRAlgebra.klr_induction with
  | hadd u v hu hv => exact slidesLeft_add s hq hu hv
  | hmul u v hu hv => exact slidesLeft_mul s hq hu hv
  | hr c => exact slidesLeft_algebraMap s hq c
  | he w => exact slidesLeft_e s hq w
  | hx b => exact slidesLeft_x s hq b
  | hψ r =>
    by_cases hr : r + 1 < N
    · exact slidesLeft_ψ s hq hr
    · rw [KLRAlgebra.ψ_eq_zero r (by omega), ← map_zero (algebraMap k Rc)]
      exact slidesLeft_algebraMap s hq 0

/-- **Errors at the bottom of a passage to the right are errors at its top.** -/
theorem underLeft_mul_mem (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) {y : Rp}
    (hy : y ∈ exitSpan Q Λ Λc j hj s (q + 1) hq) :
    underLeft N q * y ∈ exitSpan Q Λ Λc j hj s q (Nat.le_of_succ_le hq) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, r, rfl⟩ := hy
    have hD := slidesLeft (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) s hq z
    unfold SlidesLeft at hD
    have : underLeft N q * (ι s (q + 1) hq z * r) =
        ι s q (Nat.le_of_succ_le hq) z * (underLeft N q * r) -
          (ι s q (Nat.le_of_succ_le hq) z * underLeft N q - underLeft N q * ι s (q + 1) hq z) *
            r := by
      noncomm_ring
    rw [this]
    exact sub_mem (mem_exitSpan s _ hz _) (exitSpan_mul_right s _ hD r)
  | zero => rw [mul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
  | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h

end SlidingLeft

end Categorification.Stendhal.CupCap
