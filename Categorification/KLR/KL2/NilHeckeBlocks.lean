/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL2.NilHeckeFamily

/-!
# Computations in the nilHecke ring, on blocks of strands of `R(ν)` (KL II)

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups II*,
arXiv:0804.2080v1, §3, "Computations in the nilHecke ring" (TeX lines ~480–660).

"When this box is part of a diagram for an element of `R(ν)`, it denotes the corresponding
element of `R(n i) ⊂ R(ν)`." We transport the identities of
`Categorification.KLR.KL2.NilHeckeFamily` to a block `[q, q + n)` of strands carrying equal
labels in a sequence `t` (`IsConstOn t q n`), for arbitrary parameters `Q` and any commutative
ring `k`. All identities hold after right multiplication by `1_t = e t`. The box `e_{i,n}` on
the block is `blockElt q n` (so `blockElt q n * e t` is `KLRAlgebra.blockIdem t q n`), and

* `chainL q l = ψ_q ψ_{q+1} ⋯ ψ_{q+l-1}` : the strand at the bottom position `q + l` moves to the
  top position `q`;
* `chainR q l = ψ_{q+l-1} ⋯ ψ_{q+1} ψ_q` : the strand at the bottom position `q` moves to the
  top position `q + l`.

## Main results

* `KL2.lemma5`, `KL2.lemma5'` : **KL II, Lemma 5**, `∂(n) e_{i,n} = ∂(n)`.
* `KL2.chainL_mul_chainL_mul_e`, `KL2.chainR_mul_chainR_mul_e` : two braid-move identities for
  crossings inside a block of equal labels.
* `KL2.blockElt_mul_blockElt_left`, `KL2.blockElt_mul_blockElt_right` : **KL II (10)**.
* `KL2.blockElt_mul_chainR_mul_blockElt`, `KL2.blockElt_mul_chainL_mul_blockElt` :
  **KL II (11)**.
* `KL2.blockElt_mul_x_pow_mul_chainL` : **KL II (12)**.
* `KL2.blockElt_mul_x_pow_mul_chainR` : **KL II (13)**.
* `KL2.blockElt_mul_ψ_mul_e` : `e_{i,n} ψ_j = 0` for a crossing `ψ_j` inside the block.
-/

namespace Categorification.KLR.KL2

open MvPolynomial KLRAlgebra NH Categorification.NilHecke

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

/-- `ψ_q ψ_{q+1} ⋯ ψ_{q+l-1}`: the strand at the bottom position `q + l` moves to the top
position `q`. -/
noncomputable def chainL (q l : ℕ) : A := ψw (List.range' q l)

/-- `ψ_{q+l-1} ⋯ ψ_{q+1} ψ_q`: the strand at the bottom position `q` moves to the top position
`q + l`. -/
noncomputable def chainR (q l : ℕ) : A := ψw (List.range' q l).reverse

@[simp] theorem chainL_zero (q : ℕ) : (chainL q 0 : A) = 1 := by simp [chainL]

@[simp] theorem chainR_zero (q : ℕ) : (chainR q 0 : A) = 1 := by simp [chainR]

theorem chainL_succ (q l : ℕ) : (chainL q (l + 1) : A) = ψ q * chainL (q + 1) l := by
  rw [chainL, List.range'_succ, ψw_cons]; rfl

theorem chainL_succ' (q l : ℕ) : (chainL q (l + 1) : A) = chainL q l * ψ (q + l) := by
  rw [chainL, List.range'_concat, ψw_append, ψw_cons, ψw_nil, mul_one, one_mul]; rfl

theorem chainR_succ (q l : ℕ) : (chainR q (l + 1) : A) = chainR (q + 1) l * ψ q := by
  rw [chainR, List.range'_succ, List.reverse_cons, ψw_append, ψw_cons, ψw_nil, mul_one]; rfl

theorem chainR_succ' (q l : ℕ) : (chainR q (l + 1) : A) = ψ (q + l) * chainR q l := by
  rw [chainR, List.range'_concat, List.reverse_append, ψw_append, List.reverse_singleton,
    ψw_cons, ψw_nil, mul_one, one_mul]; rfl

theorem chainL_one (q : ℕ) : (chainL q 1 : A) = ψ q := by
  rw [chainL_succ, chainL_zero, mul_one]

theorem chainR_one (q : ℕ) : (chainR q 1 : A) = ψ q := by
  rw [chainR_succ, chainR_zero, one_mul]

/-! ### The transport -/

section transport

variable {t : Seq ν} {q N : ℕ} (hqN : q + N ≤ Multiset.card ν) (hc : IsConstOn t q N)

include hc in
theorem val_wp {ρ : List ℕ} (hρ : ∀ j ∈ ρ, j + 1 < N) :
    (wp (cψ (k := k) (Q := Q) t hqN hc) ρ).1 = ψw (ρ.map (q + ·)) := by
  have := wp_map (Subring.centralizer ({(e t : A)} : Set A)).subtype (cψ (k := k) (Q := Q) t hqN hc) ρ
  rw [Subring.coe_subtype] at this
  change _ = (Subring.centralizer ({(e t : A)} : Set A)).subtype (wp (cψ (k := k) (Q := Q) t hqN hc) ρ) at this
  rw [Subring.coe_subtype] at this
  rw [← this, wp, ψw, List.map_map]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  exact cψ_val_of_lt hqN hc (hρ j hj)

theorem val_xN {a : ℕ} (ha : a < N) : (xN (cx (k := k) (Q := Q) t hqN) a).1 = x ⟨q + a, by omega⟩ := by
  rw [xN, dif_pos ha]; rfl

theorem val_Δb {s n : ℕ} (h : s + n ≤ N) : (Δb (cx (k := k) (Q := Q) t hqN) s n).1 = pol (blockDelta (q + s) n) := by
  have := Δb_map (Subring.centralizer ({(e t : A)} : Set A)).subtype (cx (k := k) (Q := Q) t hqN) s n
  change _ = (Subring.centralizer ({(e t : A)} : Set A)).subtype (Δb (cx (k := k) (Q := Q) t hqN) s n) at this
  rw [Subring.coe_subtype] at this
  rw [← this, pol_blockDelta_eq, Δb]
  congr 2; funext a
  rw [xN, dif_pos (show s + (a : ℕ) < N by omega), dif_pos (show q + s + (a : ℕ) < m by omega),
    map_pow, pol_X, Function.comp_apply, cx_val]
  congr 2
  exact Fin.ext (by simp only; omega)

include hc in
theorem val_Wb {s n : ℕ} (h : s + n ≤ N) : (Wb (cψ (k := k) (Q := Q) t hqN hc) s n).1 = ψw (blockWord (q + s) n) := by
  rw [Wb, val_wp hqN hc (fun j hj => by have := mem_w0Word_map hj; omega), blockWord,
    List.map_map]
  congr 2; funext j; simp only [Function.comp_apply]; omega

include hc in
theorem val_Eb {s n : ℕ} (h : s + n ≤ N) : (Eb (cx (k := k) (Q := Q) t hqN) (cψ (k := k) (Q := Q) t hqN hc) s n).1 = blockElt (q + s) n := by
  rw [Eb, Subring.coe_mul, val_Δb hqN h, val_Wb hqN hc h, blockElt]

include hc in
theorem val_chL {s l : ℕ} (h : s + l + 1 ≤ N) : (chL (cψ (k := k) (Q := Q) t hqN hc) s l).1 = chainL (q + s) l := by
  rw [chL, val_wp hqN hc (fun j hj => by rw [List.mem_range'_1] at hj; omega), chainL,
    List.map_add_range']

include hc in
theorem val_chR {s l : ℕ} (h : s + l + 1 ≤ N) : (chR (cψ (k := k) (Q := Q) t hqN hc) s l).1 = chainR (q + s) l := by
  rw [chR, val_wp hqN hc (fun j hj => by rw [List.mem_reverse, List.mem_range'_1] at hj; omega),
    chainR, List.map_reverse, List.map_add_range']

include hc in
theorem val_D {j : ℕ} (h : j + 1 < N) : ((cψ (k := k) (Q := Q) t hqN hc) j).1 = ψ (q + j) := cψ_val_of_lt hqN hc h

/-- The block family in the corner ring `1_t R(ν) 1_t`, with its dots and crossings written as
images of elements of the centraliser of `1_t`. -/
theorem blockFamily :
    NilHecke.IsNilHeckeFamily N (toCorner (e_mul_self t) ∘ (cx (k := k) (Q := Q) t hqN))
      (toCorner (e_mul_self t) ∘ (cψ (k := k) (Q := Q) t hqN hc)) :=
  isNilHeckeFamily_block hqN hc

theorem toCorner_eq {y z : Subring.centralizer ({(e t : A)} : Set A)}
    (h : toCorner (e_mul_self t) y = toCorner (e_mul_self t) z) : y.1 * e t = z.1 * e t :=
  (toCorner_eq_iff (e_mul_self t)).1 h

end transport

/-! ### KL II, Lemma 5 and (10)–(13) in `R(ν)` -/

section identities

variable {t : Seq ν} {q n : ℕ}

/-- **KL II, Lemma 5**: `∂(n) e_{i,n} = ∂(n)` on a block `[q, q + n)` of equal labels, i.e.
`ψ_{w_0} x^δ ψ_{w_0} 1_t = ψ_{w_0} 1_t`. -/
theorem lemma5 (h : q + n ≤ m) (hc : IsConstOn t q n) :
    (ψw (blockWord q n) * pol (blockDelta q n) * ψw (blockWord q n) * e t : A) =
      ψw (blockWord q n) * e t := by
  have H := wb_mul_Δb_mul_wb (blockFamily (k := k) (Q := Q) h hc) (s := 0) (n := n) (by omega)
  simp only [wb_map, Δb_map, ← map_mul] at H
  have := toCorner_eq H
  simp only [Subring.coe_mul, val_Wb h hc (s := 0) (n := n) (by omega),
    val_Δb h (s := 0) (n := n) (by omega), add_zero] at this
  exact this

/-- **KL II, Lemma 5** in the pictured form: `∂(n)` on top of the box `e_{i,n}` equals `∂(n)`. -/
theorem lemma5' (h : q + n ≤ m) (hc : IsConstOn t q n) :
    (ψw (blockWord q n) * blockIdem t q n : A) = ψw (blockWord q n) * e t := by
  rw [blockIdem, blockElt, ← mul_assoc, ← mul_assoc, lemma5 h hc]

/-- `1_{i,n} ψ_j 1_t = 0` for a crossing `ψ_j` inside the block. -/
theorem blockElt_mul_ψ_mul_e (h : q + n ≤ m) (hc : IsConstOn t q n) {j : ℕ} (h₁ : q ≤ j)
    (h₂ : j + 1 < q + n) : (blockElt q n * ψ j * e t : A) = 0 := by
  have H := eb_mul_d (blockFamily (k := k) (Q := Q) h hc) (s := 0) (n := n) (j := j - q)
    (by omega) (by omega)
  simp only [eb_map, Function.comp_apply, ← map_mul] at H
  rw [← map_zero (toCorner (e_mul_self t))] at H
  have := toCorner_eq H
  simp only [Subring.coe_mul, val_Eb h hc (s := 0) (n := n) (by omega),
    val_D h hc (j := j - q) (by omega), add_zero, ZeroMemClass.coe_zero, zero_mul,
    show q + (j - q) = j by omega] at this
  exact this

/-- **KL II (10)**, left: `e_{i,n+1} (e_{i,n} ⊗ 1) = e_{i,n+1}`. -/
theorem blockElt_mul_blockElt_left (h : q + (n + 1) ≤ m) (hc : IsConstOn t q (n + 1)) :
    (blockElt q (n + 1) * blockElt q n * e t : A) = blockElt q (n + 1) * e t := by
  have H := eb_mul_eb_left (blockFamily (k := k) (Q := Q) h hc) (s := 0) (n := n) (by omega)
  simp only [eb_map, ← map_mul] at H
  have := toCorner_eq H
  simp only [Subring.coe_mul, val_Eb h hc (s := 0) (n := n + 1) (by omega),
    val_Eb h hc (s := 0) (n := n) (by omega), add_zero] at this
  exact this

/-- **KL II (10)**, right: `e_{i,n+1} (1 ⊗ e_{i,n}) = e_{i,n+1}`. -/
theorem blockElt_mul_blockElt_right (h : q + (n + 1) ≤ m) (hc : IsConstOn t q (n + 1)) :
    (blockElt q (n + 1) * blockElt (q + 1) n * e t : A) = blockElt q (n + 1) * e t := by
  have H := eb_mul_eb_right (blockFamily (k := k) (Q := Q) h hc) (s := 0) (n := n) (by omega)
  simp only [eb_map, ← map_mul] at H
  have := toCorner_eq H
  simp only [Subring.coe_mul, val_Eb h hc (s := 0) (n := n + 1) (by omega),
    val_Eb h hc (s := 0 + 1) (n := n) (by omega), add_zero, zero_add] at this
  exact this

/-- **KL II (11)**, left: `(e_{i,n} ⊗ 1) ψ_{q+n-1} ⋯ ψ_q e_{i,n+1} = (e_{i,n} ⊗ 1) ψ_{q+n-1} ⋯ ψ_q`
(the strand at the bottom position `q` moves to the top position `q + n`). -/
theorem blockElt_mul_chainR_mul_blockElt (h : q + (n + 1) ≤ m) (hc : IsConstOn t q (n + 1)) :
    (blockElt q n * chainR q n * blockElt q (n + 1) * e t : A) =
      blockElt q n * chainR q n * e t := by
  have H := eb_mul_chR_mul_eb (blockFamily (k := k) (Q := Q) h hc) (s := 0) (n := n) (by omega)
  simp only [eb_map, chR_map, ← map_mul] at H
  have := toCorner_eq H
  simp only [Subring.coe_mul, val_Eb h hc (s := 0) (n := n + 1) (by omega),
    val_Eb h hc (s := 0) (n := n) (by omega), val_chR h hc (s := 0) (l := n) (by omega),
    add_zero] at this
  exact this

/-- **KL II (11)**, right: `(1 ⊗ e_{i,n}) ψ_q ⋯ ψ_{q+n-1} e_{i,n+1} = (1 ⊗ e_{i,n}) ψ_q ⋯ ψ_{q+n-1}`
(the strand at the bottom position `q + n` moves to the top position `q`). -/
theorem blockElt_mul_chainL_mul_blockElt (h : q + (n + 1) ≤ m) (hc : IsConstOn t q (n + 1)) :
    (blockElt (q + 1) n * chainL q n * blockElt q (n + 1) * e t : A) =
      blockElt (q + 1) n * chainL q n * e t := by
  have H := eb_mul_chL_mul_eb (blockFamily (k := k) (Q := Q) h hc) (s := 0) (n := n) (by omega)
  simp only [eb_map, chL_map, ← map_mul] at H
  have := toCorner_eq H
  simp only [Subring.coe_mul, val_Eb h hc (s := 0) (n := n + 1) (by omega),
    val_Eb h hc (s := 0 + 1) (n := n) (by omega), val_chL h hc (s := 0) (l := n) (by omega),
    add_zero, zero_add] at this
  exact this

/-- **KL II (12)**: `e_{i,n+1} x_q^a ψ_q ⋯ ψ_{q+n-1} 1_t` is `0` for `a < n` and `e_{i,n+1} 1_t`
for `a = n` (the strand at the bottom position `q + n` carries `a` dots at its top end and
moves to the top position `q`). -/
theorem blockElt_mul_x_pow_mul_chainL (h : q + (n + 1) ≤ m) (hc : IsConstOn t q (n + 1)) {a : ℕ}
    (ha : a ≤ n) :
    (blockElt q (n + 1) * x ⟨q, by omega⟩ ^ a * chainL q n * e t : A) =
      if a = n then blockElt q (n + 1) * e t else 0 := by
  have H := eb_mul_x_pow_mul_chL (blockFamily (k := k) (Q := Q) h hc) (s := 0) (n := n)
    (by omega) ha
  simp only [eb_map, chL_map, xN_map, ← map_pow, ← map_mul] at H
  have hx := val_xN (k := k) (Q := Q) (t := t) h (a := 0) (by omega)
  simp only [add_zero] at hx
  split_ifs at H ⊢ with haN
  · have := toCorner_eq H
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, val_Eb h hc (s := 0) (n := n + 1)
      (by omega), val_chL h hc (s := 0) (l := n) (by omega), hx, add_zero] at this
    exact this
  · rw [← map_zero (toCorner (e_mul_self t))] at H
    have := toCorner_eq H
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, val_Eb h hc (s := 0) (n := n + 1)
      (by omega), val_chL h hc (s := 0) (l := n) (by omega), hx, add_zero,
      ZeroMemClass.coe_zero, zero_mul] at this
    exact this

/-- **KL II (13)**: `e_{i,n+1} x_{q+n}^a ψ_{q+n-1} ⋯ ψ_q 1_t` is `0` for `a < n` and
`(-1)^n e_{i,n+1} 1_t` for `a = n` (the strand at the bottom position `q` carries `a` dots at
its top end and moves to the top position `q + n`). -/
theorem blockElt_mul_x_pow_mul_chainR (h : q + (n + 1) ≤ m) (hc : IsConstOn t q (n + 1)) {a : ℕ}
    (ha : a ≤ n) :
    (blockElt q (n + 1) * x ⟨q + n, by omega⟩ ^ a * chainR q n * e t : A) =
      if a = n then (-1) ^ n * (blockElt q (n + 1) * e t) else 0 := by
  have H := eb_mul_x_pow_mul_chR (blockFamily (k := k) (Q := Q) h hc) (s := 0) (n := n)
    (by omega) ha
  simp only [eb_map, chR_map, xN_map, ← map_pow, ← map_mul] at H
  have hx := val_xN (k := k) (Q := Q) (t := t) h (a := 0 + n) (by omega)
  simp only [zero_add] at hx
  split_ifs at H ⊢ with haN
  · rw [← map_one (toCorner (e_mul_self t)), ← RingHom.map_neg, ← map_pow, ← map_mul] at H
    have := toCorner_eq H
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, val_Eb h hc (s := 0) (n := n + 1)
      (by omega), val_chR h hc (s := 0) (l := n) (by omega), hx, add_zero, zero_add,
      NegMemClass.coe_neg, OneMemClass.coe_one] at this
    rw [this, mul_assoc]
  · rw [← map_zero (toCorner (e_mul_self t))] at H
    have := toCorner_eq H
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, val_Eb h hc (s := 0) (n := n + 1)
      (by omega), val_chR h hc (s := 0) (l := n) (by omega), hx, add_zero, zero_add,
      ZeroMemClass.coe_zero, zero_mul] at this
    exact this

/-- `L(q, q + l + 1) L(q, q + l) = L(q + 1, q + l + 1) L(q, q + l + 1)` on a block
`[q, q + l + 2)` of equal labels. -/
theorem chainL_mul_chainL_mul_e {l : ℕ} (h : q + (l + 2) ≤ m) (hc : IsConstOn t q (l + 2)) :
    (chainL q (l + 1) * chainL q l * e t : A) = chainL (q + 1) l * chainL q (l + 1) * e t := by
  have H := chL_mul_chL (blockFamily (k := k) (Q := Q) h hc) 0 l
  simp only [chL_map, ← map_mul] at H
  have := toCorner_eq H
  simp only [Subring.coe_mul, val_chL h hc (s := 0) (l := l + 1) (by omega),
    val_chL h hc (s := 0) (l := l) (by omega), val_chL h hc (s := 0 + 1) (l := l) (by omega),
    add_zero, zero_add] at this
  exact this

/-- `R(q, q + l) R(q, q + l + 1) = R(q, q + l + 1) R(q + 1, q + l + 1)` on a block
`[q, q + l + 2)` of equal labels. -/
theorem chainR_mul_chainR_mul_e {l : ℕ} (h : q + (l + 2) ≤ m) (hc : IsConstOn t q (l + 2)) :
    (chainR q l * chainR q (l + 1) * e t : A) = chainR q (l + 1) * chainR (q + 1) l * e t := by
  have H := chR_mul_chR (blockFamily (k := k) (Q := Q) h hc) 0 l
  simp only [chR_map, ← map_mul] at H
  have := toCorner_eq H
  simp only [Subring.coe_mul, val_chR h hc (s := 0) (l := l + 1) (by omega),
    val_chR h hc (s := 0) (l := l) (by omega), val_chR h hc (s := 0 + 1) (l := l) (by omega),
    add_zero, zero_add] at this
  exact this

end identities

end Categorification.KLR.KL2
