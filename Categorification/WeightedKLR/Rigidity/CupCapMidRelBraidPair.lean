/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapPairPassage
import Categorification.WeightedKLR.Rigidity.CupCapSlidingLeft
import Categorification.KLR.InductionFree
import Categorification.KLR.Symmetries

/-!
# A crossing of two strands passing under the maximum from the left

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. Two adjacent strands at `q, q + 1` of a
loading of `λ`, left of the maximum of the cap, pass under the maximum to its right
(`underLeft N q * underLeft N (q + 1)`). A crossing of the two strands slides through the
passage, modulo diagrams in which a strand leaves the window of the maximum at the top
(`CupCap.slides_passing_ψ_left`). This is the mirror image of `CupCap.slides_passing_ψ`: each
braid defect forces a window strand to have the colour of a passing strand, so the passing strand
which stays in the window at the defect is black and leaves the window at the top.

## Main results

* `CupCap.rowsL_mul_ψ`: a crossing moved up through two rows of crossings, with its braid
  defects.
* `CupCap.slides_passing_ψ_left`: a crossing of two passing strands slides through the passage.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

section Generic

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {μ : Multiset I}
  {Q' : I → I → MvPolynomial (Fin 2) k}

/-- Two rows of crossings: the strands at `q, q + 1` pass to `q + n, q + n + 1`, going up. -/
def rowsL (q n : ℕ) : KLRAlgebra k Q' μ :=
  KLRAlgebra.ψw (List.range' q n).reverse * KLRAlgebra.ψw (List.range' (q + 1) n).reverse

theorem hflip_rows (q n : ℕ) :
    KLRAlgebra.hflip (rows q n : KLRAlgebra k Q' μ) = rowsL q n := by
  rw [rows, KLRAlgebra.hflip_mul, KLRAlgebra.hflip_ψw, KLRAlgebra.hflip_ψw, rowsL]

theorem hflip_braidDefect (a : ℕ) :
    KLRAlgebra.hflip (braidDefect a : KLRAlgebra k Q' μ) = braidDefect a := by
  simp only [braidDefect, KLRAlgebra.hflip_sub, KLRAlgebra.hflip_mul, KLRAlgebra.hflip_ψ,
    mul_assoc]

/-- **A crossing moved up through two rows of crossings**: the errors are braid defects. -/
theorem rowsL_mul_ψ (n q : ℕ) :
    (rowsL q n * KLRAlgebra.ψ q : KLRAlgebra k Q' μ) = KLRAlgebra.ψ (q + n) * rowsL q n +
      ∑ c : Fin n, rowsL (q + c.val + 1) (n - 1 - c.val) * braidDefect (q + c.val) *
        rowsL q c.val := by
  have h := congrArg KLRAlgebra.hflip (ψ_mul_rows (k := k) (Q' := Q') (μ := μ) n q)
  simp only [KLRAlgebra.hflip_mul, KLRAlgebra.hflip_add, KLRAlgebra.hflip_sum,
    KLRAlgebra.hflip_ψ, hflip_rows, hflip_braidDefect] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mul_assoc]

end Generic

section PairPassageLeft

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

/-- The row of the left passing strand, moving it to the window position `c`. -/
local notation "X" q:max c:max => (KLRAlgebra.ψw (List.reverse (List.range' q c)) : Rp)

theorem commute_rowsL_exitLeft (q c : ℕ) :
    Commute (rowsL (q + c + 1) (N - 1 - c) : Rp) (X q c) := by
  refine Commute.mul_left ?_ ?_ <;>
    exact KLRAlgebra.commute_ψw_ψw fun p hp p' hp' => by
      rw [List.mem_reverse, List.mem_range'_1] at hp hp'; omega

/-- The braid defect without dots: the passing strand at the defect has the colour of a window
strand, so it is black and leaves the window at the top. -/
theorem pairBaseLeft_mem (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 2 ≤ m) (c : Fin N)
    (t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (ht : t.lbl (pairPos hq c 0) = t.lbl (pairPos hq c 2)) :
    E s q (by omega) * (rowsL (q + c.val + 1) (N - 1 - c.val) * KLRAlgebra.e t * X q c.val) ∈
      exitSpan Q Λ Λc j hj s q (by omega) := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hc := c.2
  rw [eSum_insertSet, Finset.sum_mul]
  refine Submodule.sum_mem _ fun w _ => ?_
  by_cases hb : (w.lbl c).isLeft
  · rw [mul_assoc (rowsL _ _) (KLRAlgebra.e t), KLRAlgebra.e_mul_ψw,
      ← mul_assoc (rowsL _ _), (commute_rowsL_exitLeft q c.val).eq, mul_assoc (X q c.val),
      ← mul_assoc (KLRAlgebra.e _), e_insertSeq_mul_exitLeft s _ w c.2]
    exact mem_exitSpan s _ (e_mul_exitLeft_mem_capNull w c.2 hb) _
  · rw [rowsL, ← KLRAlgebra.ψw_append, ← mul_assoc, ← mul_assoc, KLRAlgebra.e_mul_ψw,
      mul_assoc (KLRAlgebra.ψw _), KLRAlgebra.e_mul_e]
    split_ifs with heq
    swap
    · rw [mul_zero, zero_mul]; exact zero_mem _
    exfalso
    have hinv := inv_smul_eq_iff.mp heq
    have h1 := congrArg (fun u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) =>
      u.lbl ⟨q + c.val, by omega⟩) hinv
    have h2 := congrArg (fun u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) =>
      u.lbl ⟨q + N + 1, by omega⟩) hinv
    rw [wordProd_append, mul_smul,
      KL2.lbl_range'_reverse_smul (by omega) _ _ ⟨q + c.val, by omega⟩
        (by unfold KL2.lfun; dsimp only; split_ifs <;> omega),
      KL2.lbl_range'_reverse_smul (by omega) _ _ (pairPos hq c 0)
        (by unfold KL2.lfun pairPos; dsimp only; split_ifs <;> omega),
      insertSeq_lbl_win s _ _ ⟨c.val, by rw [Multiset.card_map]; exact c.2⟩
        (by dsimp only), Seq.map_lbl] at h1
    rw [wordProd_append, mul_smul,
      KL2.lbl_range'_reverse_smul (by omega) _ _ ⟨q + N + 1, by omega⟩
        (by unfold KL2.lfun; dsimp only; split_ifs <;> omega),
      KL2.lbl_range'_reverse_smul (by omega) _ _ (pairPos hq c 2)
        (by unfold KL2.lfun pairPos; dsimp only; split_ifs <;> omega),
      insertSeq_lbl_ge s _ _ ⟨q + 1, by omega⟩ (by dsimp only; omega)
        (by dsimp only; omega)] at h2
    have h3 := h2.trans (ht.symm.trans h1.symm)
    rcases hw : w.lbl c with i | r
    · simp [hw] at hb
    · simp only [Fin.cast_mk, Fin.eta, hw] at h3
      exact oldColour_ne_cupColour_inr _ _ h3

/-- The braid defect with dots on its three strands: dots on the two right strands move down past
the row of the left strand, a dot on the left strand moves up into the window. -/
theorem pairDefectLeft_mem (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 2 ≤ m) (c : Fin N)
    (t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (ht : t.lbl (pairPos hq c 0) = t.lbl (pairPos hq c 2)) (p : MvPolynomial (Fin 3) k) :
    E s q (by omega) * (rowsL (q + c.val + 1) (N - 1 - c.val) *
        (KLRAlgebra.pol (MvPolynomial.rename (pairPos hq c) p) * KLRAlgebra.e t) * X q c.val) ∈
      exitSpan Q Λ Λc j hj s q (by omega) := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hc := c.2
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C, MvPolynomial.algHom_C, ← Algebra.smul_def, mul_smul_comm,
      smul_mul_assoc, mul_smul_comm]
    exact Submodule.smul_mem _ a (pairBaseLeft_mem s hq c t ht)
  | add p p' hp hp' =>
    rw [map_add, map_add, add_mul, mul_add, add_mul, mul_add]
    exact add_mem hp hp'
  | mul_X p n hp =>
    rw [map_mul, MvPolynomial.rename_X, map_mul, KLRAlgebra.pol_X]
    have hpx : Commute (KLRAlgebra.pol (MvPolynomial.rename (pairPos hq c) p) : Rp)
        (KLRAlgebra.x (pairPos hq c n)) := by
      rw [← KLRAlgebra.pol_X, Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
    have hn3 := n.2
    by_cases hn : n.val = 0
    swap
    · have hX : Commute (KLRAlgebra.x (pairPos hq c n) : Rp) (X q c.val) :=
        KLRAlgebra.commute_x_ψw fun p hp => by
          rw [List.mem_reverse, List.mem_range'_1] at hp; simp only [pairPos]; omega
      have h : (rowsL (q + c.val + 1) (N - 1 - c.val) *
            (KLRAlgebra.pol (MvPolynomial.rename (pairPos hq c) p) *
            KLRAlgebra.x (pairPos hq c n) * KLRAlgebra.e t) * X q c.val : Rp) =
          rowsL (q + c.val + 1) (N - 1 - c.val) *
            (KLRAlgebra.pol (MvPolynomial.rename (pairPos hq c) p) *
            KLRAlgebra.e t) * X q c.val * KLRAlgebra.x (pairPos hq c n) := by
        simp only [mul_assoc]
        rw [← mul_assoc (KLRAlgebra.x _) (KLRAlgebra.e t), KLRAlgebra.x_mul_e, mul_assoc, hX.eq]
      rw [h, ← mul_assoc]
      exact exitSpan_mul_right s _ hp _
    obtain rfl : n = 0 := Fin.ext hn
    have hrx : Commute (rowsL (q + c.val + 1) (N - 1 - c.val) : Rp)
        (KLRAlgebra.x (pairPos hq c 0)) := by
      refine Commute.mul_left ?_ ?_ <;>
        exact (KLRAlgebra.commute_x_ψw fun p hp => by
          rw [List.mem_reverse, List.mem_range'_1] at hp; simp only [pairPos]; omega).symm
    have hx : (KLRAlgebra.x (pairPos hq c 0) : Rp) * E s q (by omega) =
        ι s q (by omega) (KLRAlgebra.x c) := by
      rw [insertMap_x]; congr 2
    have hxE : ι s q (by omega) (KLRAlgebra.x c) = ι s q (by omega) (KLRAlgebra.x c) *
        E s q (by omega) := by
      rw [← insertMap_one Q Λ Λc s (by omega), ← insertMap_mul, mul_one]
    have h : (rowsL (q + c.val + 1) (N - 1 - c.val) *
          (KLRAlgebra.pol (MvPolynomial.rename (pairPos hq c) p) *
          KLRAlgebra.x (pairPos hq c 0) * KLRAlgebra.e t) * X q c.val : Rp) =
        KLRAlgebra.x (pairPos hq c 0) * (rowsL (q + c.val + 1) (N - 1 - c.val) *
          (KLRAlgebra.pol (MvPolynomial.rename (pairPos hq c) p) * KLRAlgebra.e t) *
            X q c.val) := by
      rw [hpx.eq, mul_assoc (KLRAlgebra.x _), ← mul_assoc (rowsL _ _), hrx.eq]
      simp only [mul_assoc]
    rw [h, ← mul_assoc, ← (commute_x_eSum (Q' := stendhalQ Q (plusLabels Λ Λc j hj))
      (pairPos hq c 0) (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s q (by omega))).eq, hx, hxE,
      mul_assoc]
    exact insertMap_mul_mem_exitSpan s _ _ hp

/-- **A crossing of two strands passing under the maximum from the left slides through the
passage**, modulo diagrams in which a strand leaves the window at the top. -/
theorem slides_passing_ψ_left (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 2 ≤ m) :
    E s q (by omega) * (underLeft N q * underLeft N (q + 1) * KLRAlgebra.ψ q -
        KLRAlgebra.ψ (q + N) * (underLeft N q * underLeft N (q + 1)) : Rp) ∈
      exitSpan Q Λ Λc j hj s q (by omega) := by
  have hP : (underLeft N q * underLeft N (q + 1) : Rp) = rowsL q N := rfl
  rw [hP, rowsL_mul_ψ N q, add_sub_cancel_left, Finset.mul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  have hsplit : (rowsL (q + c.val + 1) (N - 1 - c.val) * braidDefect (q + c.val) *
        rowsL q c.val : Rp) = ∑ t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)),
      rowsL (q + c.val + 1) (N - 1 - c.val) * (braidDefect (q + c.val) * KLRAlgebra.e t) *
        X q c.val * KLRAlgebra.ψw (List.range' (q + 1) c.val).reverse := by
    conv_lhs => rw [← mul_one (braidDefect (q + c.val)), ← KLRAlgebra.sum_e]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [rowsL, mul_assoc]
  rw [hsplit, Finset.mul_sum]
  refine Submodule.sum_mem _ fun t _ => ?_
  rw [← mul_assoc]
  refine exitSpan_mul_right s _ ?_ _
  rw [braidDefect, KLRAlgebra.braid (q + c.val) (pair_lt_M hq c) t]
  split_ifs with hcond
  · rw [ncEval_x_three, show (![⟨q + c.val, _⟩, ⟨q + c.val + 1, _⟩, ⟨q + c.val + 2, _⟩] :
        Fin 3 → Fin M) = pairPos hq c from funext fun i => by fin_cases i <;> rfl]
    exact pairDefectLeft_mem s hq c t hcond.1 _
  · simp only [mul_zero, zero_mul]
    exact zero_mem _

end PairPassageLeft

end Categorification.Stendhal.CupCap
