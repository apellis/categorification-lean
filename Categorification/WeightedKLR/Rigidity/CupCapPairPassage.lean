/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapPassage

/-!
# A crossing of two strands passing under the maximum of the cap

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. Two adjacent strands at `q, q + 1` of a
loading of `λ`, right of the maximum of the cap, pass under the maximum (`passU q 2`). A crossing
of the two strands slides through the passage, modulo diagrams in which a strand leaves the window
of the maximum at the top (`CupCap.slides_passing_ψ`): each braid defect forces the window strand
at the crossing to have the colour of a passing strand, hence to be black.

## Main results

* `CupCap.ψ_mul_rows`: a crossing moved through two rows of crossings, with its braid defects.
* `CupCap.slides_passing_ψ`: a crossing of two passing strands slides through the passage.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

section Generic

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {μ : Multiset I}
  {Q' : I → I → MvPolynomial (Fin 2) k}

/-- Two rows of crossings: the strands at `q, q + 1` pass to `q + n, q + n + 1`. -/
def rows (q n : ℕ) : KLRAlgebra k Q' μ :=
  KLRAlgebra.ψw (List.range' (q + 1) n) * KLRAlgebra.ψw (List.range' q n)

/-- The braid defect at `a`. -/
def braidDefect (a : ℕ) : KLRAlgebra k Q' μ :=
  KLRAlgebra.ψ a * KLRAlgebra.ψ (a + 1) * KLRAlgebra.ψ a -
    KLRAlgebra.ψ (a + 1) * KLRAlgebra.ψ a * KLRAlgebra.ψ (a + 1)

theorem rows_zero (q : ℕ) : (rows q 0 : KLRAlgebra k Q' μ) = 1 := by
  simp [rows, KLRAlgebra.ψw]

theorem rows_succ (q n : ℕ) : (rows q (n + 1) : KLRAlgebra k Q' μ) =
    KLRAlgebra.ψ (q + 1) * KLRAlgebra.ψ q * rows (q + 1) n := by
  have h : Commute (KLRAlgebra.ψ q : KLRAlgebra k Q' μ) (KLRAlgebra.ψw (List.range' (q + 1 + 1) n)) :=
    KLRAlgebra.commute_ψ_ψw fun l hl => by rw [List.mem_range'_1] at hl; omega
  rw [rows, rows, List.range'_succ, List.range'_succ, KLRAlgebra.ψw_cons, KLRAlgebra.ψw_cons,
    mul_assoc, ← mul_assoc (KLRAlgebra.ψw _), ← h.eq]
  simp only [mul_assoc]

/-- **A crossing moved through two rows of crossings**: the errors are braid defects. -/
theorem ψ_mul_rows : ∀ (n q : ℕ),
    (KLRAlgebra.ψ q * rows q n : KLRAlgebra k Q' μ) = rows q n * KLRAlgebra.ψ (q + n) +
      ∑ c : Fin n, rows q c.val * braidDefect (q + c.val) * rows (q + c.val + 1) (n - 1 - c.val)
  | 0, q => by simp [rows_zero]
  | n + 1, q => by
    have IH := ψ_mul_rows n (q + 1)
    have hB : (KLRAlgebra.ψ q * KLRAlgebra.ψ (q + 1) * KLRAlgebra.ψ q : KLRAlgebra k Q' μ) =
        KLRAlgebra.ψ (q + 1) * KLRAlgebra.ψ q * KLRAlgebra.ψ (q + 1) + braidDefect q := by
      rw [braidDefect]; abel
    have hterm : ∀ c : Fin n,
        (rows q (c.succ : ℕ) * braidDefect (q + (c.succ : ℕ)) *
            rows (q + (c.succ : ℕ) + 1) (n + 1 - 1 - (c.succ : ℕ)) : KLRAlgebra k Q' μ) =
          KLRAlgebra.ψ (q + 1) * KLRAlgebra.ψ q * (rows (q + 1) c.val *
            braidDefect (q + 1 + c.val) * rows (q + 1 + c.val + 1) (n - 1 - c.val)) := by
      intro c
      rw [Fin.val_succ, rows_succ, show q + (c.val + 1) = q + 1 + c.val by omega,
        show n + 1 - 1 - (c.val + 1) = n - 1 - c.val by omega]
      simp only [mul_assoc]
    rw [Fin.sum_univ_succ, Finset.sum_congr rfl fun c _ => hterm c, ← Finset.mul_sum]
    simp only [Fin.val_zero, rows_zero, one_mul, Nat.add_zero, Nat.sub_zero,
      show n + 1 - 1 = n by omega]
    rw [rows_succ, ← mul_assoc, ← mul_assoc, hB, add_mul, mul_assoc _ (KLRAlgebra.ψ (q + 1)),
      IH, show q + 1 + n = q + (n + 1) by omega]
    simp only [mul_add, mul_assoc]
    abel

end Generic

section PairPositions

variable {I : Type*} {ℓ : ℕ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))

theorem pair_lt_M {q : ℕ} (hq : q + 2 ≤ m) (c : Fin N) : q + c.val + 2 < M := by
  have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); have := c.2; omega

/-- The three strands at a braid defect of the passage. -/
def pairPos {q : ℕ} (hq : q + 2 ≤ m) (c : Fin N) (i : Fin 3) : Fin M :=
  ⟨q + c.val + i.val, by have := pair_lt_M hq c; have := i.2; omega⟩

end PairPositions

section PairPassage

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

/-- The word moving the window strand `c` to the right end of a window at `q + 2`. -/
local notation "X" q:max c:max => (KLRAlgebra.ψw (List.range' (q + 2 + c) (N - 1 - c)) : Rp)

theorem commute_rows_exit (q c : ℕ) : Commute (rows q c : Rp) (X q c) := by
  refine Commute.mul_left ?_ ?_ <;>
    exact KLRAlgebra.commute_ψw_ψw fun p hp p' hp' => by rw [List.mem_range'_1] at hp hp'; omega

/-- The braid defect without dots: the window strand at the defect has the colour of a passing
strand, so it is black and leaves the window at the top. -/
theorem pairBase_mem (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 2 ≤ m) (c : Fin N)
    (t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (ht : t.lbl (pairPos hq c 0) = t.lbl (pairPos hq c 2)) :
    E s (q + 2) hq * (rows q c.val * KLRAlgebra.e t * X q c.val) ∈
      exitSpan Q Λ Λc j hj s (q + 2) hq := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hc := c.2
  rw [eSum_insertSet, Finset.sum_mul]
  refine Submodule.sum_mem _ fun w _ => ?_
  by_cases hb : (w.lbl c).isLeft
  · rw [mul_assoc (rows q c.val) (KLRAlgebra.e t), KLRAlgebra.e_mul_ψw,
      ← mul_assoc (rows q c.val), (commute_rows_exit q c.val).eq, mul_assoc (X q c.val),
      ← mul_assoc (KLRAlgebra.e _), e_insertSeq_mul_exit s hq w c.val]
    exact mem_exitSpan s hq (e_mul_exit_mem_capNull w c.2 hb) _
  · rw [rows, ← KLRAlgebra.ψw_append, ← mul_assoc, ← mul_assoc, KLRAlgebra.e_mul_ψw,
      mul_assoc (KLRAlgebra.ψw _), KLRAlgebra.e_mul_e]
    split_ifs with heq
    swap
    · rw [mul_zero, zero_mul]; exact zero_mem _
    exfalso
    have hinv := inv_smul_eq_iff.mp heq
    have h1 := congrArg (fun u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) =>
      u.lbl ⟨q, by omega⟩) hinv
    have h2 := congrArg (fun u : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)) =>
      u.lbl ⟨q + c.val + 2, by omega⟩) hinv
    rw [wordProd_append, mul_smul,
      KL2.lbl_range'_smul (by omega) _ _ ⟨q, by omega⟩
        (by unfold KL2.rfun; dsimp only; split_ifs <;> omega),
      KL2.lbl_range'_smul (by omega) _ _ (pairPos hq c 0)
        (by unfold KL2.rfun pairPos; dsimp only; split_ifs <;> omega),
      insertSeq_lbl_lt s hq _ ⟨q, by omega⟩ (by dsimp only; omega) rfl] at h1
    rw [wordProd_append, mul_smul,
      KL2.lbl_range'_smul (by omega) _ _ ⟨q + c.val + 2, by omega⟩
        (by unfold KL2.rfun; dsimp only; split_ifs <;> omega),
      KL2.lbl_range'_smul (by omega) _ _ (pairPos hq c 2)
        (by unfold KL2.rfun pairPos; dsimp only; split_ifs <;> omega),
      insertSeq_lbl_win s hq _ ⟨c.val, by rw [Multiset.card_map]; exact c.2⟩
        (by dsimp only; omega), Seq.map_lbl] at h2
    have h3 := h1.trans (ht.trans h2.symm)
    rcases hw : w.lbl c with i | r
    · simp [hw] at hb
    · simp only [Fin.cast_mk, Fin.eta, hw] at h3
      exact oldColour_ne_cupColour_inr _ _ h3

/-- The braid defect with dots on its three strands: dots on the two left strands move down past
the exit, a dot on the right strand moves up to the top of the window. -/
theorem pairDefect_mem (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 2 ≤ m) (c : Fin N)
    (t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)))
    (ht : t.lbl (pairPos hq c 0) = t.lbl (pairPos hq c 2)) (p : MvPolynomial (Fin 3) k) :
    E s (q + 2) hq * (rows q c.val * (KLRAlgebra.pol (MvPolynomial.rename (pairPos hq c) p) *
        KLRAlgebra.e t) * X q c.val) ∈ exitSpan Q Λ Λc j hj s (q + 2) hq := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hc := c.2
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C, MvPolynomial.algHom_C, ← Algebra.smul_def, mul_smul_comm,
      smul_mul_assoc, mul_smul_comm]
    exact Submodule.smul_mem _ a (pairBase_mem s hq c t ht)
  | add p p' hp hp' =>
    rw [map_add, map_add, add_mul, mul_add, add_mul, mul_add]
    exact add_mem hp hp'
  | mul_X p n hp =>
    rw [map_mul, MvPolynomial.rename_X, map_mul, KLRAlgebra.pol_X]
    have hpx : Commute (KLRAlgebra.pol (MvPolynomial.rename (pairPos hq c) p) : Rp)
        (KLRAlgebra.x (pairPos hq c n)) := by
      rw [← KLRAlgebra.pol_X, Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
    have hn3 := n.2
    by_cases hn : n.val = 2
    swap
    · have hX : Commute (KLRAlgebra.x (pairPos hq c n) : Rp) (X q c.val) :=
        KLRAlgebra.commute_x_ψw fun p hp => by
          rw [List.mem_range'_1] at hp; simp only [pairPos]; omega
      have h : (rows q c.val * (KLRAlgebra.pol (MvPolynomial.rename (pairPos hq c) p) *
            KLRAlgebra.x (pairPos hq c n) * KLRAlgebra.e t) * X q c.val : Rp) =
          rows q c.val * (KLRAlgebra.pol (MvPolynomial.rename (pairPos hq c) p) *
            KLRAlgebra.e t) * X q c.val * KLRAlgebra.x (pairPos hq c n) := by
        simp only [mul_assoc]
        rw [← mul_assoc (KLRAlgebra.x _) (KLRAlgebra.e t), KLRAlgebra.x_mul_e, mul_assoc, hX.eq]
      rw [h, ← mul_assoc]
      exact exitSpan_mul_right s hq hp _
    obtain rfl : n = 2 := Fin.ext hn
    have hrx : Commute (rows q c.val : Rp) (KLRAlgebra.x (pairPos hq c 2)) := by
      refine Commute.mul_left ?_ ?_ <;>
        exact (KLRAlgebra.commute_x_ψw fun p hp => by
          rw [List.mem_range'_1] at hp; simp only [pairPos]; omega).symm
    have hx : (KLRAlgebra.x (pairPos hq c 2) : Rp) * E s (q + 2) hq =
        ι s (q + 2) hq (KLRAlgebra.x c) := by
      rw [insertMap_x]; congr 2; exact Fin.ext (by simp only [pairPos]; omega)
    have hxE : ι s (q + 2) hq (KLRAlgebra.x c) = ι s (q + 2) hq (KLRAlgebra.x c) *
        E s (q + 2) hq := by
      rw [← insertMap_one Q Λ Λc s hq, ← insertMap_mul, mul_one]
    have h : (rows q c.val * (KLRAlgebra.pol (MvPolynomial.rename (pairPos hq c) p) *
          KLRAlgebra.x (pairPos hq c 2) * KLRAlgebra.e t) * X q c.val : Rp) =
        KLRAlgebra.x (pairPos hq c 2) * (rows q c.val *
          (KLRAlgebra.pol (MvPolynomial.rename (pairPos hq c) p) * KLRAlgebra.e t) *
            X q c.val) := by
      rw [hpx.eq, mul_assoc (KLRAlgebra.x _), ← mul_assoc (rows q c.val), hrx.eq]
      simp only [mul_assoc]
    rw [h, ← mul_assoc, ← (commute_x_eSum (Q' := stendhalQ Q (plusLabels Λ Λc j hj))
      (pairPos hq c 2) (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (q + 2) hq)).eq, hx, hxE,
      mul_assoc]
    exact insertMap_mul_mem_exitSpan s hq _ hp

/-- **A crossing of two strands passing under the maximum slides through the passage**, modulo
diagrams in which a strand leaves the window at the top. -/
theorem slides_passing_ψ (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 2 ≤ m) :
    E s (q + 2) hq * (KLRAlgebra.ψ q * passU Q Λ Λc j hj ν ν₀ q 2 -
        passU Q Λ Λc j hj ν ν₀ q 2 * KLRAlgebra.ψ (q + N) : Rp) ∈
      exitSpan Q Λ Λc j hj s (q + 2) hq := by
  have hP : passU Q Λ Λc j hj ν ν₀ q 2 = (rows q N : Rp) := by
    rw [passU_succ, passU_succ, passU_zero, mul_one]; rfl
  rw [hP, ψ_mul_rows N q, add_sub_cancel_left, Finset.mul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  have hsplit : (rows q c.val * braidDefect (q + c.val) * rows (q + c.val + 1) (N - 1 - c.val) :
        Rp) = ∑ t : Seq (stendhalWeight (ℓ + 2) (ν + ν₀)),
      rows q c.val * (braidDefect (q + c.val) * KLRAlgebra.e t) * X q c.val *
        KLRAlgebra.ψw (List.range' (q + c.val + 1) (N - 1 - c.val)) := by
    conv_lhs => rw [← mul_one (rows q c.val * braidDefect (q + c.val)), ← KLRAlgebra.sum_e]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hr : (rows (q + c.val + 1) (N - 1 - c.val) : Rp) =
        X q c.val * KLRAlgebra.ψw (List.range' (q + c.val + 1) (N - 1 - c.val)) := by
      rw [rows, show q + c.val + 1 + 1 = q + 2 + c.val by omega]
    rw [hr]
    simp only [mul_assoc]
  rw [hsplit, Finset.mul_sum]
  refine Submodule.sum_mem _ fun t _ => ?_
  rw [← mul_assoc]
  refine exitSpan_mul_right s hq ?_ _
  rw [braidDefect, KLRAlgebra.braid (q + c.val) (pair_lt_M hq c) t]
  split_ifs with hcond
  · rw [ncEval_x_three, show (![⟨q + c.val, _⟩, ⟨q + c.val + 1, _⟩, ⟨q + c.val + 2, _⟩] :
        Fin 3 → Fin M) = pairPos hq c from funext fun i => by fin_cases i <;> rfl]
    exact pairDefect_mem s hq c t hcond.1 _
  · simp only [mul_zero, zero_mul]
    exact zero_mem _

end PairPassage

end Categorification.Stendhal.CupCap
