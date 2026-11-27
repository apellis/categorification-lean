/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapSliding

/-!
# Several strands passing under the maximum of the cap

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. The strands at positions `q, …, q + d - 1`
of a loading of `λ`, right of the maximum of the cap, pass one after the other under the maximum
to its left (`CupCap.passU q d = underRight N (q + d - 1) ⋯ underRight N q`). This moves the window
of the strands at the maximum from `q` (at the bottom) to `q + d` (at the top). Diagrams at the
maximum slide through the whole passage, modulo diagrams in which a strand leaves the window at the
top (`CupCap.slides_passU`); the errors themselves are carried to the top (`CupCap.passU_mul_mem`).

## Main definitions

* `CupCap.passU`: the passage of `d` strands under the maximum.

## Main results

* `CupCap.passU_mul_eSum`: the passage moves the window idempotents.
* `CupCap.passU_mul_mem`: errors at the bottom of a passage are errors at its top.
* `CupCap.slides_passU`: diagrams at the maximum slide through a passage.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

section Generic

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

/-- **A dot on the passing strand**, moved along the passage `underRight`: the errors are the
diagrams in which the crossing with the window strand `c` is replaced by the idempotent of equal
colours. -/
theorem x_passing_mul_ψw {μ : Multiset I} {Q' : I → I → MvPolynomial (Fin 2) k} (q : ℕ) :
    ∀ (n : ℕ) (h : q + n < Multiset.card μ),
      (KLRAlgebra.x ⟨q, by omega⟩ * KLRAlgebra.ψw (List.range' q n) : KLRAlgebra k Q' μ) =
        KLRAlgebra.ψw (List.range' q n) * KLRAlgebra.x ⟨q + n, h⟩ +
          ∑ c : Fin n, KLRAlgebra.ψw (List.range' q c.val) *
            KLRAlgebra.eqIdem (q + c.val) (by omega) *
            KLRAlgebra.ψw (List.range' (q + 1 + c.val) (n - 1 - c.val))
  | 0, h => by simp
  | n + 1, h => by
    rw [← List.range'_append_1, KLRAlgebra.ψw_append, ← mul_assoc,
      x_passing_mul_ψw q n (by omega), add_mul, mul_assoc, List.range'_one, KLRAlgebra.ψw_cons, KLRAlgebra.ψw_nil,
      mul_one, x_mul_ψ_self (q + n) h, Fin.sum_univ_castSucc, Finset.sum_mul]
    simp only [Fin.val_castSucc, Fin.val_last, mul_add, ← mul_assoc]
    have hlast : (List.range' (q + 1 + n) (n + 1 - 1 - n)) = [] := by
      rw [show n + 1 - 1 - n = 0 by omega]; rfl
    rw [hlast, KLRAlgebra.ψw_nil, mul_one]
    have hterm : ∀ c : Fin n,
        (KLRAlgebra.ψw (List.range' q c.val) * KLRAlgebra.eqIdem (q + c.val) (by omega) *
            KLRAlgebra.ψw (List.range' (q + 1 + c.val) (n - 1 - c.val)) * KLRAlgebra.ψ (q + n) :
          KLRAlgebra k Q' μ) =
        KLRAlgebra.ψw (List.range' q c.val) * KLRAlgebra.eqIdem (q + c.val) (by omega) *
          KLRAlgebra.ψw (List.range' (q + 1 + c.val) (n + 1 - 1 - c.val)) := by
      intro c
      have hc := c.2
      rw [show n + 1 - 1 - c.val = (n - 1 - c.val) + 1 by omega, ← List.range'_append_1,
        KLRAlgebra.ψw_append, List.range'_one, KLRAlgebra.ψw_cons, KLRAlgebra.ψw_nil, mul_one,
        show q + 1 + c.val + (n - 1 - c.val) = q + n by omega, mul_assoc]
    simp only [hterm]
    have hx : (⟨q + n + 1, h⟩ : Fin (Multiset.card μ)) = ⟨q + (n + 1), h⟩ := Fin.ext (by simp; omega)
    rw [hx]
    abel

end Generic

section Passage

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)

variable (j hj ν ν₀) in
/-- **The passage of `d` strands under the maximum**: the strands at `q, …, q + d - 1` pass under
the window one after the other, `underRight N (q + d - 1) ⋯ underRight N q`. -/
def passU (q : ℕ) : ℕ → Rp
  | 0 => 1
  | d + 1 => underRight N (q + d) * passU q d

@[simp] theorem passU_zero (q : ℕ) : passU Q Λ Λc j hj ν ν₀ q 0 = 1 := rfl

theorem passU_succ (q d : ℕ) :
    passU Q Λ Λc j hj ν ν₀ q (d + 1) = underRight N (q + d) * passU Q Λ Λc j hj ν ν₀ q d := rfl

/-- The passage moves the window idempotent from the bottom to the top. -/
theorem passU_mul_eSum (s : Seq (stendhalWeight ℓ ν)) (q : ℕ) :
    ∀ (d : ℕ) (h : q + d ≤ m),
      (passU Q Λ Λc j hj ν ν₀ q d * E s q (by omega) : Rp) = E s (q + d) h * passU Q Λ Λc j hj ν ν₀ q d
  | 0, h => by rw [passU_zero, one_mul, mul_one]; rfl
  | d + 1, h => by
    rw [passU_succ, mul_assoc, passU_mul_eSum s q d (by omega), ← mul_assoc,
      underRight_mul_eSum Q Λ Λc s (q := q + d) h, mul_assoc]
    rfl

/-- One passage carries an error at its bottom to an error at its top. -/
theorem underRight_mul_mem (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 ≤ m) {y : Rp}
    (hy : y ∈ exitSpan Q Λ Λc j hj s p (by omega)) :
    underRight N p * y ∈ exitSpan Q Λ Λc j hj s (p + 1) hp := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, r, rfl⟩ := hy
    have hD := slides (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) s hp z
    unfold Slides at hD
    have : underRight N p * (ι s p (by omega) z * r) =
        ι s (p + 1) hp z * (underRight N p * r) -
          (ι s (p + 1) hp z * underRight N p - underRight N p * ι s p (by omega) z) * r := by
      noncomm_ring
    rw [this]
    exact sub_mem (mem_exitSpan s hp hz _) (exitSpan_mul_right s hp hD r)
  | zero => rw [mul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
  | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h

/-- **Errors at the bottom of a passage are errors at its top.** -/
theorem passU_mul_mem (s : Seq (stendhalWeight ℓ ν)) (q : ℕ) :
    ∀ (d : ℕ) (h : q + d ≤ m) {y : Rp}, y ∈ exitSpan Q Λ Λc j hj s q (by omega) →
      passU Q Λ Λc j hj ν ν₀ q d * y ∈ exitSpan Q Λ Λc j hj s (q + d) h
  | 0, h, y, hy => by rw [passU_zero, one_mul]; exact hy
  | d + 1, h, y, hy => by
    rw [passU_succ, mul_assoc]
    exact underRight_mul_mem Q Λ Λc s h (passU_mul_mem s q d (by omega) hy)

/-- **Diagrams at the maximum slide through a passage**, modulo diagrams in which a strand leaves
the window at the top. -/
theorem slides_passU (s : Seq (stendhalWeight ℓ ν)) (q : ℕ) (x : Rc) :
    ∀ (d : ℕ) (h : q + d ≤ m),
      ι s (q + d) h x * passU Q Λ Λc j hj ν ν₀ q d -
          passU Q Λ Λc j hj ν ν₀ q d * ι s q (by omega) x ∈ exitSpan Q Λ Λc j hj s (q + d) h
  | 0, h => by
    have : ι s (q + 0) h x = ι s q (by omega) x := rfl
    rw [passU_zero, one_mul, mul_one, this, sub_self]; exact zero_mem _
  | d + 1, h => by
    have hD := slides (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) s (q := q + d) h x
    unfold Slides at hD
    have IH := slides_passU s q x d (by omega)
    have : ι s (q + d + 1) h x * passU Q Λ Λc j hj ν ν₀ q (d + 1) -
        passU Q Λ Λc j hj ν ν₀ q (d + 1) * ι s q (by omega) x =
        (ι s (q + d + 1) h x * underRight N (q + d) -
            underRight N (q + d) * ι s (q + d) (by omega) x) * passU Q Λ Λc j hj ν ν₀ q d +
          underRight N (q + d) * (ι s (q + d) (by omega) x * passU Q Λ Λc j hj ν ν₀ q d -
            passU Q Λ Λc j hj ν ν₀ q d * ι s q (by omega) x) := by
      rw [passU_succ]; noncomm_ring
    change _ ∈ exitSpan Q Λ Λc j hj s (q + d + 1) h
    change ι s (q + d + 1) h x * _ - _ ∈ _
    rw [this]
    exact add_mem (exitSpan_mul_right s h hD _) (underRight_mul_mem Q Λ Λc s h IH)

theorem commute_x_eSum {μ : Multiset (I ⊕ Fin (ℓ + 2))} {Q' : I ⊕ Fin (ℓ + 2) → I ⊕ Fin (ℓ + 2) →
    MvPolynomial (Fin 2) k} (a : Fin (Multiset.card μ)) (T : Finset (Seq μ)) :
    Commute (KLRAlgebra.x a : KLRAlgebra k Q' μ) (KLRAlgebra.eSum Q' T) :=
  Commute.sum_right _ _ _ fun t _ => KLRAlgebra.x_mul_e a t

omit [DecidableEq I] in
theorem lt_M_of_succ_le {q : ℕ} (hq : q + 1 ≤ m) : q < Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)) := by
  have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega

omit [DecidableEq I] in
theorem add_N_lt_M_of_succ_le {q : ℕ} (hq : q + 1 ≤ m) :
    q + N < Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)) := by
  have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega

/-- **A dot on the passing strand slides along the passage**, modulo diagrams in which a strand
leaves the window at the top. -/
theorem slides_passing_x (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) :
    E s (q + 1) hq * (KLRAlgebra.x ⟨q, lt_M_of_succ_le hq⟩ * underRight N q -
        underRight N q * KLRAlgebra.x ⟨q + N, add_N_lt_M_of_succ_le hq⟩ : Rp) ∈
      exitSpan Q Λ Λc j hj s (q + 1) hq := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  set D : Rp := KLRAlgebra.x ⟨q, by omega⟩ * underRight N q -
    underRight N q * KLRAlgebra.x ⟨q + N, by omega⟩ with hDdef
  have hE : E s (q + 1) hq * D = E s (q + 1) hq * (D * E s q (by omega)) := by
    have h1 := underRight_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s hq
    have hc1 := (commute_x_eSum (Q' := stendhalQ Q (plusLabels Λ Λc j hj))
      ⟨q, by omega⟩ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (q + 1) hq)).eq
    have hc2 := (commute_x_eSum (Q' := stendhalQ Q (plusLabels Λ Λc j hj))
      ⟨q + N, by omega⟩ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s q (by omega))).eq
    have hEE := (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj))
      (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (q + 1) hq)).eq
    have hA : (KLRAlgebra.x ⟨q, lt_M_of_succ_le hq⟩ * underRight N q *
        E s q (by omega) : Rp) = E s (q + 1) hq * (KLRAlgebra.x ⟨q, lt_M_of_succ_le hq⟩ *
          underRight N q) := by
      rw [mul_assoc, h1, ← mul_assoc, hc1, mul_assoc]
    have hB : (underRight N q * KLRAlgebra.x ⟨q + N, add_N_lt_M_of_succ_le hq⟩ *
        E s q (by omega) : Rp) = E s (q + 1) hq * (underRight N q *
          KLRAlgebra.x ⟨q + N, add_N_lt_M_of_succ_le hq⟩) := by
      rw [mul_assoc, hc2, ← mul_assoc, h1, mul_assoc]
    rw [hDdef, sub_mul, hA, hB, ← mul_sub, ← mul_assoc, hEE]
  have hsum := x_passing_mul_ψw (k := k) (μ := stendhalWeight (ℓ + 2) (ν + ν₀))
    (Q' := stendhalQ Q (plusLabels Λ Λc j hj)) q N (by omega)
  have hD : D = ∑ c : Fin N, KLRAlgebra.ψw (List.range' q c.val) *
      KLRAlgebra.eqIdem (q + c.val) (by omega) *
      KLRAlgebra.ψw (List.range' (q + 1 + c.val) (N - 1 - c.val)) := by
    rw [hDdef, underRight, hsum]; abel
  change E s (q + 1) hq * D ∈ _
  rw [hE, hD, Finset.sum_mul, Finset.mul_sum]
  exact Submodule.sum_mem _ fun c _ => exitTerm_mem s hq c

end Passage

end Categorification.Stendhal.CupCap
