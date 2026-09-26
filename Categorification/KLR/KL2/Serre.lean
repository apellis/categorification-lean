/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL2.SerreMaps
import Categorification.KLR.KL2.OrthSum
import Categorification.KLR.Prop213

/-!
# KL II, Proposition 6 and Corollary 7: the categorified quantum Serre relations

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups II*,
arXiv:0804.2080v1, §3, **Proposition 6** (TeX label `serre-right`) and **Corollary 7**
(`serre-left`).

**Proposition 6.** For each `i, j ∈ I`, `i ≠ j`, there are isomorphisms of graded right projective
modules `⊕_{a=0}^{⌊(d+1)/2⌋} ₍…i^{(2a)} j i^{(d+1-2a)}…₎P ≅ ⊕_{a=0}^{⌊d/2⌋} ₍…i^{(2a+1)} j i^{(d-2a)}…₎P`,
`d = d_ij`. **Corollary 7** is the same statement for the left projectives `P_{…}`.

We work in `R(ν) = R2 k C ν` for a Cartan datum `C`, over any commutative ring `k`. Positions are
zero-indexed; the window `[p, p + N]` (`N = d + 1`) of a sequence `t = …j i^N…` (context `…`
arbitrary, with divided-power blocks `bs` outside the window) carries the sequences
`S n = serreSeq t p n = …i^n j i^{N-n}…`, and

* `serreIdem n = 1_{…i^{(n)} j i^{(N-n)}…}` (`serreIdem_eq_divIdem`),
* `serreAp n = α^+_{(n, N-n)}` and `serreAm n = α^-_{(n, N-n)}` (the paper's maps, KL II (19),
  (23): `α^±_{n,N-n}` composed with the inclusion of `₍…i^{(n)} j i^{(N-n)}…₎P`),
* `serreEven = ∑_{n even} serreIdem n`, `serreOdd = ∑_{n odd} serreIdem n` (sums of orthogonal
  idempotents, `isOrthFamily_serreIdem`), whose right ideals are the direct sums in
  Proposition 6 (`Categorification.rIdealSumEquiv`),
* `serreAlpha' = ∑_{n even} (α^+_{(n)} + α^-_{(n)})` and `serreAlpha'' = ∑_{n odd} (α^-_{(n)} - α^+_{(n)})`
  (the paper's `α'`, `α''`).

## Main results

* `prop6` : **KL II, Proposition 6** (idempotent form): `(α'', α')` exhibits the idempotents
  `serreEven` and `serreOdd` as equivalent: `α'' α' = serreEven`, `α' α'' = serreOdd`.
* `prop6_rIdealEquiv` : `⊕_{n even} 1_{S(n)} R(ν) ≅ ⊕_{n odd} 1_{S(n)} R(ν)` (right projectives,
  ungraded; `y ↦ α' y`).
* `cor7_lIdealEquiv` : **KL II, Corollary 7**: `⊕_{n even} R(ν) ψ(1_{S(n)}) ≅ ⊕_{n odd} R(ν) ψ(1_{S(n)})`
  (left projectives, via the antiinvolution `ψ = hflip`).
* `prop6_fixSubEquiv` : `⊕_{n even} 1_{S(n)} M ≅ ⊕_{n odd} 1_{S(n)} M` for every left `R(ν)`-module `M`
  (the analogue of KL I, Corollary 2.14).
* `serreAp_mem_grade`, `serreAm_mem_grade` : the degrees of `α^±` for the KL II grading, and
  `serreAp_degree_eq_shift`, `serreAm_degree_eq_shift` : they are the differences of the grading
  shifts `⟨…⟩`, so that `α'`, `α''` are grading preserving between the shifted projectives
  `₍…₎P = 1_{…} R(ν) {-⟨…⟩}`; `serreIdem_mem_grade` : the idempotents have degree `0`.

The module isomorphisms are ungraded (graded module categories are not used here); the grading
statement is the homogeneity of the maps recorded above.

The case `i · j = 0` is included (`d = 0`, `N = 1`: `₍…ji…₎P ≅ ₍…ij…₎P` via the crossing).
-/

namespace Categorification.KLR.KL2

open Equiv MvPolynomial KLRAlgebra TypeA QuantumGroup

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {C : CartanDatum I}
  {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => R2 k C ν

section grading

theorem chainL_mul_e_mem_grade {s : Seq ν} {q l : ℕ} {c : I} (h : q + l < m)
    (hc : IsConstOn s q (l + 1)) (hs : s.lbl ⟨q, by omega⟩ = c) :
    (chainL q l * e s : A) ∈ (klGradingDatum2 k C).grade ν (-(l : ℤ) * C.dot c c) := by
  have := (klGradingDatum2 k C).ψw_mul_pol_mul_e_mem_grade (List.range' q l) s
    (isWeightedHomogeneous_one k _)
  rw [map_one, mul_one, add_zero, degW_of_forall (klGradingDatum2 k C) (c := c)
    (fun j hj => by rw [List.mem_range'_1] at hj; omega) (fun j hj hj' => by
      rw [List.mem_range'_1] at hj
      exact ⟨(hc _ _ (by simp only; omega) (by simp only; omega) le_rfl (by simp only; omega)).trans
        hs, (hc _ _ (by simp only; omega) (by simp only; omega) le_rfl
          (by simp only; omega)).trans hs⟩), List.length_range'] at this
  exact this

theorem chainR_mul_e_mem_grade {s : Seq ν} {q l : ℕ} {c : I} (h : q + l < m)
    (hc : IsConstOn s q (l + 1)) (hs : s.lbl ⟨q, by omega⟩ = c) :
    (chainR q l * e s : A) ∈ (klGradingDatum2 k C).grade ν (-(l : ℤ) * C.dot c c) := by
  have := (klGradingDatum2 k C).ψw_mul_pol_mul_e_mem_grade (List.range' q l).reverse s
    (isWeightedHomogeneous_one k _)
  rw [map_one, mul_one, add_zero, degW_of_forall (klGradingDatum2 k C) (c := c)
    (fun j hj => by rw [List.mem_reverse, List.mem_range'_1] at hj; omega) (fun j hj hj' => by
      rw [List.mem_reverse, List.mem_range'_1] at hj
      exact ⟨(hc _ _ (by simp only; omega) (by simp only; omega) le_rfl (by simp only; omega)).trans
        hs, (hc _ _ (by simp only; omega) (by simp only; omega) le_rfl
          (by simp only; omega)).trans hs⟩), List.length_reverse, List.length_range'] at this
  exact this

end grading

section serre

variable (t : Seq ν) (p N : ℕ) (bs : List (ℕ × ℕ))

/-- The idempotent `1_{…i^{(n)} j i^{(N-n)}…}` (with the context blocks `bs`). -/
noncomputable def serreIdem (n : ℕ) : A := blocksElt bs * etop t p N n

/-- The map `α^+_{(n, N-n)}` of KL II (19), as the element `α^+_{n,N-n} 1_{…i^{(n)} j i^{(N-n)}…}`
(zero unless `n + 1 ≤ N`). -/
noncomputable def serreAp (n : ℕ) : A :=
  if n + 1 ≤ N then blocksElt bs * aplus t p N n * etop t p N n else 0

/-- The map `α^-_{(n, N-n)}` of KL II (23), as the element `α^-_{n,N-n} 1_{…i^{(n)} j i^{(N-n)}…}`
(zero unless `1 ≤ n ≤ N`). -/
noncomputable def serreAm (n : ℕ) : A :=
  if 1 ≤ n ∧ n ≤ N then blocksElt bs * aminus t p N n * etop t p N n else 0

/-- The even positions `{0, 2, 4, …} ∩ [0, N]`. -/
def serreEvens : Finset ℕ := (Finset.range (N + 1)).filter Even

/-- The odd positions `{1, 3, 5, …} ∩ [0, N]`. -/
def serreOdds : Finset ℕ := (Finset.range (N + 1)).filter Odd

/-- `∑_{n even} 1_{…i^{(n)} j i^{(N-n)}…}`: its right ideal is `⊕_{a} ₍…i^{(2a)} j i^{(N-2a)}…₎P`. -/
noncomputable def serreEven : A := ∑ n ∈ serreEvens N, serreIdem t p N bs n

/-- `∑_{n odd} 1_{…i^{(n)} j i^{(N-n)}…}`: its right ideal is `⊕_{a} ₍…i^{(2a+1)} j i^{(N-2a-1)}…₎P`. -/
noncomputable def serreOdd : A := ∑ n ∈ serreOdds N, serreIdem t p N bs n

/-- The paper's `α' = ∑_{n even} (α^+_{(n)} + α^-_{(n)})`. -/
noncomputable def serreAlpha' : A :=
  ∑ n ∈ serreEvens N, (serreAp t p N bs n + serreAm t p N bs n)

/-- The paper's `α'' = ∑_{n odd} (α^-_{(n)} - α^+_{(n)})`. -/
noncomputable def serreAlpha'' : A :=
  ∑ n ∈ serreOdds N, (serreAm t p N bs n - serreAp t p N bs n)

variable {t p N bs} {i j : I} (hpN : p + N < Multiset.card ν)
  (ht₀ : ∀ r : Fin (Multiset.card ν), (r : ℕ) = p → t.lbl r = j)
  (ht : ∀ r : Fin (Multiset.card ν), p < r → (r : ℕ) ≤ p + N → t.lbl r = i)
  (hb : IsBlocks t bs) (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ p ∨ p + N + 1 ≤ b.1)

local notation "S" => serreSeq t p

/-! ### The context blocks -/

include hpN ht₀ ht hb hbs in
theorem isBlocks_serreSeq {n : ℕ} (hn : n ≤ N) : IsBlocks (S n) bs := by
  refine ⟨hb.le, fun b hb' r r' h1 h2 h3 h4 => ?_, hb.disj⟩
  have := hbs b hb'
  rw [serreSeq_lbl_of_lt hpN ht₀ ht hn r (by omega), serreSeq_lbl_of_lt hpN ht₀ ht hn r' (by omega)]
  exact hb.const b hb' r r' h1 h2 h3 h4

include hbs in
theorem commute_blocksElt_blockElt_window {c n : ℕ} (hc : p ≤ c) (hn : c + n ≤ p + N + 1) :
    Commute (blocksElt bs : A) (blockElt c n) :=
  commute_blocksElt fun b hb => commute_blockElt_blockElt (by have := hbs b hb; omega)

include hbs in
theorem commute_blocksElt_ψ_window {q : ℕ} (hq : p ≤ q) (hq' : q + 1 ≤ p + N) :
    Commute (blocksElt bs : A) (ψ q) :=
  commute_blocksElt fun b hb => (commute_ψ_blockElt (by have := hbs b hb; omega)).symm

include hbs in
theorem commute_blocksElt_ψw_window {ρ : List ℕ} (hρ : ∀ q ∈ ρ, p ≤ q ∧ q + 1 ≤ p + N) :
    Commute (blocksElt bs : A) (ψw ρ) := by
  rw [ψw]
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
  exact commute_blocksElt_ψ_window hbs (hρ q hq).1 (hρ q hq).2

include hbs in
theorem commute_blocksElt_chainL {q l : ℕ} (hq : p ≤ q) (hl : q + l ≤ p + N) :
    Commute (blocksElt bs : A) (chainL q l) :=
  commute_blocksElt_ψw_window hbs fun q' hq' => by rw [List.mem_range'_1] at hq'; omega

include hbs in
theorem commute_blocksElt_chainR {q l : ℕ} (hq : p ≤ q) (hl : q + l ≤ p + N) :
    Commute (blocksElt bs : A) (chainR q l) :=
  commute_blocksElt_ψw_window hbs fun q' hq' => by
    rw [List.mem_reverse, List.mem_range'_1] at hq'; omega

include hpN ht₀ ht hb hbs in
theorem commute_blocksElt_e {n : ℕ} (hn : n ≤ N) : Commute (blocksElt bs : A) (e (S n)) :=
  blocksElt_mul_e (isBlocks_serreSeq hpN ht₀ ht hb hbs hn).const

include hpN ht₀ ht hb hbs in
theorem commute_blocksElt_etop {n : ℕ} (hn : n ≤ N) :
    Commute (blocksElt bs : A) (etop t p N n) :=
  ((commute_blocksElt_blockElt_window hbs le_rfl (by omega)).mul_right
    (commute_blocksElt_blockElt_window hbs (by omega) (by omega))).mul_right
    (commute_blocksElt_e hpN ht₀ ht hb hbs hn)

include hpN ht₀ ht hb hbs in
theorem commute_blocksElt_aplus {n : ℕ} (hn : n + 1 ≤ N) :
    Commute (blocksElt bs : A) (aplus t p N n) :=
  (((commute_blocksElt_blockElt_window hbs le_rfl (by omega)).mul_right
    (commute_blocksElt_blockElt_window hbs (by omega) (by omega))).mul_right
    (commute_blocksElt_chainL hbs (by omega) (by omega))).mul_right
    (commute_blocksElt_e hpN ht₀ ht hb hbs (by omega))

include hpN ht₀ ht hb hbs in
theorem commute_blocksElt_aminus {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ N) :
    Commute (blocksElt bs : A) (aminus t p N n) :=
  (((commute_blocksElt_blockElt_window hbs le_rfl (by omega)).mul_right
    (commute_blocksElt_blockElt_window hbs (by omega) (by omega))).mul_right
    (commute_blocksElt_chainR hbs le_rfl (by omega))).mul_right
    (commute_blocksElt_e hpN ht₀ ht hb hbs hn)

/-! ### The idempotents `1_{…i^{(n)} j i^{(N-n)}…}` -/

include hpN ht₀ ht in
theorem isBlocks_etop {n : ℕ} (hn : n ≤ N) :
    IsBlocks (S n) [(p, n), (p + n + 1, N - n)] := by
  refine ⟨fun b hb => ?_, fun b hb => ?_, ?_⟩
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp only <;> omega
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact isConstOn_serreSeq_left hpN ht₀ ht hn le_rfl le_rfl
    · exact isConstOn_serreSeq_right hpN ht₀ ht hn (by omega) (by omega)
  · simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
    omega

theorem etop_eq_divIdem (n : ℕ) :
    (etop t p N n : A) = divIdem (S n) [(p, n), (p + n + 1, N - n)] := by
  simp [divIdem, blocksElt, etop, mul_assoc]

include hpN ht₀ ht in
theorem isIdempotentElem_etop {n : ℕ} (hn : n ≤ N) : IsIdempotentElem (etop t p N n : A) := by
  rw [etop_eq_divIdem]
  exact isIdempotentElem_divIdem (isBlocks_etop hpN ht₀ ht hn)

include hbs in
/-- `serreIdem n` is the idempotent `1_{…i^{(n)} j i^{(N-n)}…}` of KL I §2.5 / KL II §3, i.e.
`divIdem` of the expansion `S n = …i^n j i^{N-n}…` with the divided-power blocks `[p, p + n)`,
`[p + n + 1, p + N + 1)` and the context blocks `bs`. -/
theorem serreIdem_eq_divIdem {n : ℕ} (hn : n ≤ N) :
    (serreIdem t p N bs n : A) = divIdem (S n) ((p, n) :: (p + n + 1, N - n) :: bs) := by
  have h1 := commute_blocksElt_blockElt_window (k := k) (C := C) (ν := ν) hbs (p := p)
    (c := p) (n := n) le_rfl (by omega)
  have h2 := commute_blocksElt_blockElt_window (k := k) (C := C) (ν := ν) hbs (p := p)
    (c := p + n + 1) (n := N - n) (by omega) (by omega)
  simp only [serreIdem, etop, divIdem, blocksElt_cons]
  rw [← mul_assoc, ← mul_assoc, h1.eq, mul_assoc (blockElt p n), h2.eq]

include hpN ht₀ ht hb hbs in
theorem serreIdem_mul_serreIdem {n n' : ℕ} (hn : n ≤ N) (hn' : n' ≤ N) (hij : i ≠ j) :
    (serreIdem t p N bs n * serreIdem t p N bs n' : A) =
      if n = n' then serreIdem t p N bs n else 0 := by
  have hc := commute_blocksElt_etop (k := k) (C := C) hpN ht₀ ht hb hbs hn
  split_ifs with hnn
  · subst hnn
    rw [serreIdem, mul_assoc, ← mul_assoc (etop t p N n), ← hc.eq, mul_assoc,
      (isIdempotentElem_etop hpN ht₀ ht hn).eq, ← mul_assoc]
    rw [etop, ← mul_assoc, mul_assoc (blocksElt bs * blocksElt bs),
      blocksElt_sq_mul_of_commute (isBlocks_serreSeq hpN ht₀ ht hb hbs hn)
      ((commute_blocksElt_blockElt_window (p := p) (N := N) hbs le_rfl (by omega)).mul_right
        (commute_blocksElt_blockElt_window (p := p) (N := N) hbs (by omega) (by omega)))]
  · -- different sequences: `1_{S n} 1_{S n'} = 0`
    have hne : S n ≠ S n' := by
      intro h
      have := congrArg (fun s : Seq ν => s.lbl ⟨p + n, by omega⟩) h
      simp only at this
      rw [serreSeq_lbl_eq_j hpN ht₀ ht hn _ rfl,
        serreSeq_lbl_eq_i hpN ht₀ ht hn' _ (by simp) (by simp only; omega)
          (by simp only; omega)] at this
      exact hij this.symm
    have h' : (etop t p N n' : A) = e (S n') * (blockElt p n' * blockElt (p + n' + 1) (N - n')) := by
      rw [etop, mul_assoc, ← ((commute_blockElt_left_e hpN ht₀ ht hn' le_rfl le_rfl).mul_left
        (commute_blockElt_right_e hpN ht₀ ht hn' (by omega) (by omega))).eq, ← mul_assoc]
    have hF := commute_blocksElt_e (k := k) (C := C) hpN ht₀ ht hb hbs hn
    rw [serreIdem, serreIdem, h', etop]
    simp only [mul_assoc]
    rw [hF.symm.left_comm, ← mul_assoc (e (S n)) (e (S n')), e_mul_e, if_neg hne]
    simp

include hpN ht₀ ht hb hbs in
theorem isOrthFamily_serreIdem (hij : i ≠ j) :
    IsOrthFamily (Finset.range (N + 1)) (serreIdem t p N bs : ℕ → A) := by
  intro n hn n' hn'
  rw [Finset.mem_range] at hn hn'
  exact serreIdem_mul_serreIdem hpN ht₀ ht hb hbs (by omega) (by omega) hij

/-! ### The maps `α^±_{(n)}` -/

include hpN ht₀ ht hb hbs in
theorem blocksElt_mul_blocksElt_mul {n : ℕ} (hn : n ≤ N) {Y : A} (hY : Commute (blocksElt bs) Y)
    (hYe : Y * e (S n) = Y) : blocksElt bs * (blocksElt bs * Y) = blocksElt bs * Y := by
  rw [← hYe, ← mul_assoc, blocksElt_sq_mul_of_commute (isBlocks_serreSeq hpN ht₀ ht hb hbs hn) hY]

theorem etop_mul_e (n : ℕ) : (etop t p N n * e (S n) : A) = etop t p N n := by
  rw [etop, mul_assoc, e_mul_self]

include hpN ht₀ ht in
theorem etop_mul_aplus {n : ℕ} (hn : n + 1 ≤ N) :
    (etop t p N (n + 1) * aplus t p N n : A) = aplus t p N n := by
  rw [aplus_eq hpN ht₀ ht hn, ← mul_assoc, (isIdempotentElem_etop hpN ht₀ ht hn).eq]

include hpN ht₀ ht in
theorem etop_mul_aminus {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ N) :
    (etop t p N (n - 1) * aminus t p N n : A) = aminus t p N n := by
  rw [aminus_eq hpN ht₀ ht hn1 hn, ← mul_assoc,
    (isIdempotentElem_etop hpN ht₀ ht (by omega)).eq]

include hpN ht₀ ht hb hbs in
/-- Composition of two maps `F X 1_{(a)}` and `F Y 1_{(b)}` with `1_{(a)} Y = Y`. -/
theorem compose_maps {a b : ℕ} (ha : a ≤ N) (hb' : b ≤ N) {X Y : A}
    (hX : Commute (blocksElt bs) X) (hY : Commute (blocksElt bs) Y)
    (hYtop : etop t p N a * Y = Y) :
    (blocksElt bs * X * etop t p N a * (blocksElt bs * Y * etop t p N b) : A) =
      blocksElt bs * (X * Y * etop t p N b) := by
  have hEa := commute_blocksElt_etop (k := k) (C := C) hpN ht₀ ht hb hbs ha
  have hZ : Commute (blocksElt bs : A) (X * (etop t p N a * (Y * etop t p N b))) :=
    hX.mul_right (hEa.mul_right (hY.mul_right
      (commute_blocksElt_etop hpN ht₀ ht hb hbs hb')))
  simp only [mul_assoc]
  rw [← hEa.left_comm, ← hX.left_comm, blocksElt_mul_blocksElt_mul hpN ht₀ ht hb hbs hb' hZ
    (by simp only [mul_assoc, etop_mul_e]), ← mul_assoc (etop t p N a), hYtop]

include hpN ht₀ ht hb hbs in
/-- Right absorption: `(F X 1_{(a)}) (F 1_{(a)}) = F X 1_{(a)}`. -/
theorem map_mul_idem {a : ℕ} (ha : a ≤ N) {X : A} (hX : Commute (blocksElt bs) X) :
    (blocksElt bs * X * etop t p N a * serreIdem t p N bs a : A) =
      blocksElt bs * X * etop t p N a := by
  have hEa := commute_blocksElt_etop (k := k) (C := C) hpN ht₀ ht hb hbs ha
  have hZ : Commute (blocksElt bs : A) (X * (etop t p N a * etop t p N a)) :=
    hX.mul_right (hEa.mul_right hEa)
  rw [serreIdem]
  simp only [mul_assoc]
  rw [← hEa.left_comm, ← hX.left_comm, blocksElt_mul_blocksElt_mul hpN ht₀ ht hb hbs ha hZ
    (by simp only [mul_assoc, etop_mul_e]), (isIdempotentElem_etop hpN ht₀ ht ha).eq]

include hpN ht₀ ht hb hbs in
/-- Left absorption: `(F 1_{(a)}) (F Y 1_{(b)}) = F Y 1_{(b)}` if `1_{(a)} Y = Y`. -/
theorem idem_mul_map {a b : ℕ} (ha : a ≤ N) (hb' : b ≤ N) {Y : A}
    (hY : Commute (blocksElt bs) Y) (hYtop : etop t p N a * Y = Y) :
    (serreIdem t p N bs a * (blocksElt bs * Y * etop t p N b) : A) =
      blocksElt bs * Y * etop t p N b := by
  have hEa := commute_blocksElt_etop (k := k) (C := C) hpN ht₀ ht hb hbs ha
  have hZ : Commute (blocksElt bs : A) (etop t p N a * (Y * etop t p N b)) :=
    hEa.mul_right (hY.mul_right (commute_blocksElt_etop hpN ht₀ ht hb hbs hb'))
  rw [serreIdem]
  simp only [mul_assoc]
  rw [← hEa.left_comm, blocksElt_mul_blocksElt_mul hpN ht₀ ht hb hbs hb' hZ
    (by simp only [mul_assoc, etop_mul_e]), ← mul_assoc (etop t p N a), hYtop]

include hpN ht₀ ht hb hbs in
theorem serreAp_mul_serreIdem (n : ℕ) :
    (serreAp t p N bs n * serreIdem t p N bs n : A) = serreAp t p N bs n := by
  unfold serreAp
  split_ifs with hn
  · exact map_mul_idem hpN ht₀ ht hb hbs (by omega) (commute_blocksElt_aplus hpN ht₀ ht hb hbs hn)
  · rw [zero_mul]

include hpN ht₀ ht hb hbs in
theorem serreAm_mul_serreIdem (n : ℕ) :
    (serreAm t p N bs n * serreIdem t p N bs n : A) = serreAm t p N bs n := by
  unfold serreAm
  split_ifs with hn
  · exact map_mul_idem hpN ht₀ ht hb hbs hn.2
      (commute_blocksElt_aminus hpN ht₀ ht hb hbs hn.1 hn.2)
  · rw [zero_mul]

include hpN ht₀ ht hb hbs in
theorem serreIdem_mul_serreAp (n : ℕ) :
    (serreIdem t p N bs (n + 1) * serreAp t p N bs n : A) = serreAp t p N bs n := by
  unfold serreAp
  split_ifs with hn
  · exact idem_mul_map hpN ht₀ ht hb hbs hn (by omega)
      (commute_blocksElt_aplus hpN ht₀ ht hb hbs hn) (etop_mul_aplus hpN ht₀ ht hn)
  · rw [mul_zero]

include hpN ht₀ ht hb hbs in
theorem serreIdem_mul_serreAm (n : ℕ) :
    (serreIdem t p N bs (n - 1) * serreAm t p N bs n : A) = serreAm t p N bs n := by
  unfold serreAm
  split_ifs with hn
  · exact idem_mul_map hpN ht₀ ht hb hbs (by omega) hn.2
      (commute_blocksElt_aminus hpN ht₀ ht hb hbs hn.1 hn.2)
      (etop_mul_aminus hpN ht₀ ht hn.1 hn.2)
  · rw [mul_zero]

theorem serreAm_of_not {n : ℕ} (h : ¬ (1 ≤ n ∧ n ≤ N)) : (serreAm t p N bs n : A) = 0 := by
  rw [serreAm, if_neg h]

theorem serreAp_of_not {n : ℕ} (h : ¬ n + 1 ≤ N) : (serreAp t p N bs n : A) = 0 := by
  rw [serreAp, if_neg h]

include hpN ht₀ ht hb hbs in
theorem serreAm_mul_serreAp {n : ℕ} (hn : n + 1 ≤ N) :
    (serreAm t p N bs (n + 1) * serreAp t p N bs n : A) =
      blocksElt bs * (aminus t p N (n + 1) * aplus t p N n * etop t p N n) := by
  rw [serreAm, if_pos ⟨by omega, hn⟩, serreAp, if_pos hn]
  exact compose_maps hpN ht₀ ht hb hbs hn (by omega)
    (commute_blocksElt_aminus hpN ht₀ ht hb hbs (by omega) hn)
    (commute_blocksElt_aplus hpN ht₀ ht hb hbs hn) (etop_mul_aplus hpN ht₀ ht hn)

include hpN ht₀ ht hb hbs in
theorem serreAp_mul_serreAm {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ N) :
    (serreAp t p N bs (n - 1) * serreAm t p N bs n : A) =
      blocksElt bs * (aplus t p N (n - 1) * aminus t p N n * etop t p N n) := by
  rw [serreAm, if_pos ⟨hn1, hn⟩, serreAp, if_pos (by omega)]
  exact compose_maps hpN ht₀ ht hb hbs (by omega) hn
    (commute_blocksElt_aplus hpN ht₀ ht hb hbs (by omega))
    (commute_blocksElt_aminus hpN ht₀ ht hb hbs hn1 hn) (etop_mul_aminus hpN ht₀ ht hn1 hn)

include hpN ht₀ ht hb hbs in
/-- **KL II, §3**: `α^-_{(n+1)} α^+_{(n)} - α^+_{(n-1)} α^-_{(n)} = (-1)^n Id` on
`₍…i^{(n)} j i^{(N-n)}…₎P`, including the boundary cases `n = 0` (`α^-_{(1,d)} α^+_{(0,d+1)} = Id`)
and `n = N` (`α^+_{(d,1)} α^-_{(d+1,0)} = (-1)^d Id`). -/
theorem serre_rel (hij : i ≠ j) (hN : N = C.dij i j + 1) {n : ℕ} (hn : n ≤ N) :
    (serreAm t p N bs (n + 1) * serreAp t p N bs n - serreAp t p N bs (n - 1) * serreAm t p N bs n
      : A) = (-1) ^ n * serreIdem t p N bs n := by
  have hE := (isIdempotentElem_etop (k := k) (C := C) hpN ht₀ ht hn).eq
  have hc : ∀ y : A, Commute ((-1 : A) ^ n) y := fun y => (Commute.neg_one_left y).pow_left n
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [serreAm_mul_serreAp hpN ht₀ ht hb hbs (by omega), show serreAm t p N bs 0 = (0 : A) by
      rw [serreAm, if_neg (by omega)], mul_zero, sub_zero, zero_add,
      serre_B hpN ht₀ ht hij hN, hE, pow_zero, one_mul, serreIdem]
  have hP : (-1 : A) ^ n = -(-1) ^ (n - 1) := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_neg_one]
  have hc' : Commute ((-1 : A) ^ (n - 1)) (blocksElt bs) :=
    (Commute.neg_one_left _).pow_left (n - 1)
  rcases Nat.lt_or_ge n N with hnN | hnN
  · rw [serreAm_mul_serreAp hpN ht₀ ht hb hbs (by omega),
      serreAp_mul_serreAm hpN ht₀ ht hb hbs hn0 hn, ← mul_sub, ← sub_mul,
      ← neg_sub, serre_A hpN ht₀ ht hij (by
        intro h; rw [(C.dij_eq_zero_iff hij).2 h] at hN; omega) hN hn0 (by omega),
      neg_mul, mul_assoc, hE, serreIdem, hP, neg_mul, hc'.left_comm, mul_neg]
  · have hnN' : n = N := by omega
    rw [serreAm_of_not (by omega), zero_mul, zero_sub,
      serreAp_mul_serreAm hpN ht₀ ht hb hbs hn0 hn]
    rw [hnN'] at hE hP hc' ⊢
    rw [serre_C hpN ht₀ ht hij hN, mul_assoc, hE, serreIdem, hP, neg_mul, hc'.left_comm]

include hpN ht₀ ht hb hbs in
theorem serreAp_succ_mul_serreAp (hij : i ≠ j) (n : ℕ) :
    (serreAp t p N bs (n + 1) * serreAp t p N bs n : A) = 0 := by
  by_cases hn : n + 2 ≤ N
  · rw [serreAp, if_pos (by omega), serreAp, if_pos (by omega),
      compose_maps hpN ht₀ ht hb hbs (by omega) (by omega)
        (commute_blocksElt_aplus hpN ht₀ ht hb hbs (by omega))
        (commute_blocksElt_aplus hpN ht₀ ht hb hbs (by omega))
        (etop_mul_aplus hpN ht₀ ht (by omega)),
      serre_Dplus hpN ht₀ ht hij hn, zero_mul, mul_zero]
  · rw [serreAp, if_neg (by omega), zero_mul]

include hpN ht₀ ht hb hbs in
theorem serreAm_pred_mul_serreAm (hij : i ≠ j) (n : ℕ) :
    (serreAm t p N bs (n - 1) * serreAm t p N bs n : A) = 0 := by
  by_cases hn : 2 ≤ n ∧ n ≤ N
  · rw [serreAm, if_pos (by omega), serreAm, if_pos (by omega),
      compose_maps hpN ht₀ ht hb hbs (by omega) (by omega)
        (commute_blocksElt_aminus hpN ht₀ ht hb hbs (by omega) (by omega))
        (commute_blocksElt_aminus hpN ht₀ ht hb hbs (by omega) (by omega))
        (etop_mul_aminus hpN ht₀ ht (by omega) (by omega)),
      serre_Dminus hpN ht₀ ht hij hn.1 hn.2, zero_mul, mul_zero]
  · by_cases hn0 : n ≤ 1
    · rw [serreAm_of_not (n := n - 1) (by omega), zero_mul]
    · rw [serreAm_of_not (n := n) (by omega), mul_zero]

/-! ### Proposition 6 -/

theorem mem_serreEvens {n : ℕ} : n ∈ serreEvens N ↔ n ≤ N ∧ n % 2 = 0 := by
  rw [serreEvens, Finset.mem_filter, Finset.mem_range, Nat.even_iff]; omega

theorem mem_serreOdds {n : ℕ} : n ∈ serreOdds N ↔ n ≤ N ∧ n % 2 = 1 := by
  rw [serreOdds, Finset.mem_filter, Finset.mem_range, Nat.odd_iff]; omega

include hpN ht₀ ht hb hbs in
theorem isOrthFamily_sub (hij : i ≠ j) {s : Finset ℕ} (hs : ∀ n ∈ s, n ≤ N) :
    IsOrthFamily s (serreIdem t p N bs : ℕ → A) := fun a ha b hb' =>
  serreIdem_mul_serreIdem hpN ht₀ ht hb hbs (hs a ha) (hs b hb') hij

include hpN ht₀ ht hb hbs in
/-- A sum `∑_{a ∈ s} X_a` of elements with `X_a = X_a 1_{(a)}`, times `1_{(n)}`. -/
theorem sum_mul_serreIdem (hij : i ≠ j) {s : Finset ℕ} (hs : ∀ n ∈ s, n ≤ N) (X : ℕ → A)
    (hX : ∀ a ∈ s, X a * serreIdem t p N bs a = X a) {n : ℕ} (hn : n ≤ N) :
    (∑ a ∈ s, X a) * serreIdem t p N bs n = if n ∈ s then X n else 0 := by
  rw [Finset.sum_mul]
  have : ∀ a ∈ s, X a * serreIdem t p N bs n = if n = a then X a else 0 := by
    intro a ha
    rw [← hX a ha, mul_assoc, serreIdem_mul_serreIdem hpN ht₀ ht hb hbs (hs a ha) hn hij]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [mul_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]

include hpN ht₀ ht hb hbs in
theorem alpha'_mul_serreIdem (hij : i ≠ j) {n : ℕ} (hn : n ≤ N) :
    (serreAlpha' t p N bs * serreIdem t p N bs n : A) =
      if n ∈ serreEvens N then serreAp t p N bs n + serreAm t p N bs n else 0 :=
  sum_mul_serreIdem hpN ht₀ ht hb hbs hij (fun a ha => (mem_serreEvens.1 ha).1) _
    (fun a _ => by rw [add_mul, serreAp_mul_serreIdem hpN ht₀ ht hb hbs,
      serreAm_mul_serreIdem hpN ht₀ ht hb hbs]) hn

include hpN ht₀ ht hb hbs in
theorem alpha''_mul_serreIdem (hij : i ≠ j) {n : ℕ} (hn : n ≤ N) :
    (serreAlpha'' t p N bs * serreIdem t p N bs n : A) =
      if n ∈ serreOdds N then serreAm t p N bs n - serreAp t p N bs n else 0 :=
  sum_mul_serreIdem hpN ht₀ ht hb hbs hij (fun a ha => (mem_serreOdds.1 ha).1) _
    (fun a _ => by rw [sub_mul, serreAp_mul_serreIdem hpN ht₀ ht hb hbs,
      serreAm_mul_serreIdem hpN ht₀ ht hb hbs]) hn

include hpN ht₀ ht hb hbs in
theorem alpha'_mul_serreEven (hij : i ≠ j) :
    (serreAlpha' t p N bs * serreEven t p N bs : A) = serreAlpha' t p N bs := by
  rw [serreEven, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [alpha'_mul_serreIdem hpN ht₀ ht hb hbs hij (mem_serreEvens.1 hn).1, if_pos hn]

include hpN ht₀ ht hb hbs in
theorem alpha''_mul_serreOdd (hij : i ≠ j) :
    (serreAlpha'' t p N bs * serreOdd t p N bs : A) = serreAlpha'' t p N bs := by
  rw [serreOdd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [alpha''_mul_serreIdem hpN ht₀ ht hb hbs hij (mem_serreOdds.1 hn).1, if_pos hn]

include hpN ht₀ ht hb hbs in
/-- `serreEven α'' = α''`: the target of `α''` is `⊕_{n even} ₍…₎P`. -/
theorem serreEven_mul_alpha'' (hij : i ≠ j) :
    (serreEven t p N bs * serreAlpha'' t p N bs : A) = serreAlpha'' t p N bs := by
  have hO := isOrthFamily_sub (k := k) (C := C) hpN ht₀ ht hb hbs hij (s := serreEvens N)
    (fun a ha => (mem_serreEvens.1 ha).1)
  rw [serreAlpha'', Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb' => ?_
  rw [mem_serreOdds] at hb'
  rw [mul_sub]
  congr 1
  · rw [← serreIdem_mul_serreAm hpN ht₀ ht hb hbs b, ← mul_assoc, serreEven,
      hO.sum_mul (mem_serreEvens.2 ⟨by omega, by omega⟩)]
  · by_cases hb1 : b + 1 ≤ N
    · rw [← serreIdem_mul_serreAp hpN ht₀ ht hb hbs b, ← mul_assoc, serreEven,
        hO.sum_mul (mem_serreEvens.2 ⟨by omega, by omega⟩)]
    · rw [serreAp_of_not hb1, mul_zero]

include hpN ht₀ ht hb hbs in
/-- `serreOdd α' = α'`: the target of `α'` is `⊕_{n odd} ₍…₎P`. -/
theorem serreOdd_mul_alpha' (hij : i ≠ j) :
    (serreOdd t p N bs * serreAlpha' t p N bs : A) = serreAlpha' t p N bs := by
  have hO := isOrthFamily_sub (k := k) (C := C) hpN ht₀ ht hb hbs hij (s := serreOdds N)
    (fun a ha => (mem_serreOdds.1 ha).1)
  rw [serreAlpha', Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [mem_serreEvens] at ha
  rw [mul_add]
  congr 1
  · by_cases ha1 : a + 1 ≤ N
    · rw [← serreIdem_mul_serreAp hpN ht₀ ht hb hbs a, ← mul_assoc, serreOdd,
        hO.sum_mul (mem_serreOdds.2 ⟨by omega, by omega⟩)]
    · rw [serreAp_of_not ha1, mul_zero]
  · by_cases ha1 : 1 ≤ a
    · rw [← serreIdem_mul_serreAm hpN ht₀ ht hb hbs a, ← mul_assoc, serreOdd,
        hO.sum_mul (mem_serreOdds.2 ⟨by omega, by omega⟩)]
    · rw [serreAm_of_not (by omega), mul_zero]

include hpN ht₀ ht hb hbs in
theorem alpha''_mul_alpha' (hij : i ≠ j) (hN : N = C.dij i j + 1) :
    (serreAlpha'' t p N bs * serreAlpha' t p N bs : A) = serreEven t p N bs := by
  rw [← alpha'_mul_serreEven hpN ht₀ ht hb hbs hij, ← mul_assoc, serreEven, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' := mem_serreEvens.1 ha
  rw [mul_assoc, alpha'_mul_serreIdem hpN ht₀ ht hb hbs hij ha'.1, if_pos ha, mul_add]
  have e1 : (serreAlpha'' t p N bs * serreAp t p N bs a : A) =
      serreAm t p N bs (a + 1) * serreAp t p N bs a := by
    by_cases ha1 : a + 1 ≤ N
    · rw [← serreIdem_mul_serreAp hpN ht₀ ht hb hbs a, ← mul_assoc,
        alpha''_mul_serreIdem hpN ht₀ ht hb hbs hij ha1,
        if_pos (mem_serreOdds.2 ⟨ha1, by omega⟩), sub_mul,
        serreAp_succ_mul_serreAp hpN ht₀ ht hb hbs hij, sub_zero, serreIdem_mul_serreAp hpN ht₀ ht
        hb hbs]
    · rw [serreAp_of_not ha1, mul_zero, mul_zero]
  have e2 : (serreAlpha'' t p N bs * serreAm t p N bs a : A) =
      -(serreAp t p N bs (a - 1) * serreAm t p N bs a) := by
    by_cases ha1 : 1 ≤ a
    · rw [← serreIdem_mul_serreAm hpN ht₀ ht hb hbs a, ← mul_assoc,
        alpha''_mul_serreIdem hpN ht₀ ht hb hbs hij (by omega),
        if_pos (mem_serreOdds.2 ⟨by omega, by omega⟩), sub_mul,
        serreAm_pred_mul_serreAm hpN ht₀ ht hb hbs hij, zero_sub, serreIdem_mul_serreAm hpN ht₀ ht
        hb hbs]
    · rw [serreAm_of_not (by omega), mul_zero, mul_zero, neg_zero]
  rw [e1, e2, ← sub_eq_add_neg, serre_rel hpN ht₀ ht hb hbs hij hN ha'.1,
    Even.neg_one_pow (Nat.even_iff.2 ha'.2), one_mul]

include hpN ht₀ ht hb hbs in
theorem alpha'_mul_alpha'' (hij : i ≠ j) (hN : N = C.dij i j + 1) :
    (serreAlpha' t p N bs * serreAlpha'' t p N bs : A) = serreOdd t p N bs := by
  rw [← alpha''_mul_serreOdd hpN ht₀ ht hb hbs hij, ← mul_assoc, serreOdd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb' => ?_
  have hb'' := mem_serreOdds.1 hb'
  rw [mul_assoc, alpha''_mul_serreIdem hpN ht₀ ht hb hbs hij hb''.1, if_pos hb', mul_sub]
  have e1 : (serreAlpha' t p N bs * serreAm t p N bs b : A) =
      serreAp t p N bs (b - 1) * serreAm t p N bs b := by
    rw [← serreIdem_mul_serreAm hpN ht₀ ht hb hbs b, ← mul_assoc,
      alpha'_mul_serreIdem hpN ht₀ ht hb hbs hij (by omega),
      if_pos (mem_serreEvens.2 ⟨by omega, by omega⟩), add_mul,
      serreAm_pred_mul_serreAm hpN ht₀ ht hb hbs hij, add_zero,
      serreIdem_mul_serreAm hpN ht₀ ht hb hbs]
  have e2 : (serreAlpha' t p N bs * serreAp t p N bs b : A) =
      serreAm t p N bs (b + 1) * serreAp t p N bs b := by
    by_cases hb1 : b + 1 ≤ N
    · rw [← serreIdem_mul_serreAp hpN ht₀ ht hb hbs b, ← mul_assoc,
        alpha'_mul_serreIdem hpN ht₀ ht hb hbs hij hb1,
        if_pos (mem_serreEvens.2 ⟨hb1, by omega⟩), add_mul,
        serreAp_succ_mul_serreAp hpN ht₀ ht hb hbs hij, zero_add,
        serreIdem_mul_serreAp hpN ht₀ ht hb hbs]
    · rw [serreAp_of_not hb1, mul_zero, mul_zero]
  rw [e1, e2, ← neg_sub, serre_rel hpN ht₀ ht hb hbs hij hN hb''.1,
    Odd.neg_one_pow (Nat.odd_iff.2 hb''.2), neg_one_mul, neg_neg]

include hpN ht₀ ht hb hbs in
/-- **KL II, Proposition 6** (idempotent form). For labels `i ≠ j`, `d = d_ij`, `N = d + 1`, a
sequence `t = …j i^N…` with the window at position `p`, and context blocks `bs` (divided powers of
`t` away from the window): `(α'', α')` exhibits the idempotents
`serreEven = ∑_{a} 1_{…i^{(2a)} j i^{(d+1-2a)}…}` and `serreOdd = ∑_{a} 1_{…i^{(2a+1)} j i^{(d-2a)}…}`
as equivalent: `α'' α' = serreEven`, `α' α'' = serreOdd`, `α'' α' α'' = α''`, `α' α'' α' = α'`. -/
theorem prop6 (hij : i ≠ j) (hN : N = C.dij i j + 1) :
    IsEquivPair (serreAlpha'' t p N bs : A) (serreAlpha' t p N bs) (serreEven t p N bs)
      (serreOdd t p N bs) :=
  IsEquivPair.of_mul_left (alpha''_mul_alpha' hpN ht₀ ht hb hbs hij hN)
    (alpha'_mul_alpha'' hpN ht₀ ht hb hbs hij hN) (serreEven_mul_alpha'' hpN ht₀ ht hb hbs hij)
    (alpha'_mul_serreEven hpN ht₀ ht hb hbs hij)

/-! ### Projective modules: Proposition 6 and Corollary 7 -/

/-- The antiinvolution `ψ` (`hflip`) of `R(ν)` commutes with finite sums. -/
theorem hflip_sum (s : Finset ℕ) (f : ℕ → A) : hflip (∑ n ∈ s, f n) = ∑ n ∈ s, hflip (f n) :=
  map_sum (AddMonoidHom.mk' (hflip : A → A) hflip_add) f s

include hpN ht₀ ht hb hbs in
/-- **KL II, Proposition 6** (right projectives, ungraded):
`⊕_{n even} ₍…i^{(n)} j i^{(N-n)}…₎P ≅ ⊕_{n odd} ₍…i^{(n)} j i^{(N-n)}…₎P` as right `R(ν)`-modules
(`₍…₎P = 1_{…} R(ν)`); the map is left multiplication by `α'`. -/
noncomputable def prop6_rIdealEquiv (hij : i ≠ j) (hN : N = C.dij i j + 1) :
    ((n : serreEvens N) → rIdeal (serreIdem t p N bs n : A)) ≃ₗ[Aᵐᵒᵖ]
      ((n : serreOdds N) → rIdeal (serreIdem t p N bs n : A)) :=
  have hE := isOrthFamily_sub (k := k) (C := C) hpN ht₀ ht hb hbs hij (s := serreEvens N)
    fun _ ha => (mem_serreEvens.1 ha).1
  have hO := isOrthFamily_sub (k := k) (C := C) hpN ht₀ ht hb hbs hij (s := serreOdds N)
    fun _ ha => (mem_serreOdds.1 ha).1
  have hP := prop6 (k := k) (C := C) hpN ht₀ ht hb hbs hij hN
  (rIdealSumEquiv hE).symm.trans (hP.rIdealEquiv.trans (rIdealSumEquiv hO))

include hpN ht₀ ht hb hbs in
/-- **KL II, Corollary 7** (left projectives, ungraded):
`⊕_{n even} P_{…i^{(n)} j i^{(N-n)}…} ≅ ⊕_{n odd} P_{…i^{(n)} j i^{(N-n)}…}` as left `R(ν)`-modules,
`P_{…} = R(ν) ψ(1_{…})`, `ψ = hflip` the antiinvolution; the map is right multiplication by
`ψ(α'')`. -/
noncomputable def cor7_lIdealEquiv (hij : i ≠ j) (hN : N = C.dij i j + 1) :
    ((n : serreEvens N) → lIdeal (hflip (serreIdem t p N bs n : A))) ≃ₗ[A]
      ((n : serreOdds N) → lIdeal (hflip (serreIdem t p N bs n : A))) :=
  have hE := (isOrthFamily_sub (k := k) (C := C) hpN ht₀ ht hb hbs hij (s := serreEvens N)
    fun a ha => (mem_serreEvens.1 ha).1).map_anti hflip hflip_add hflip_mul
  have hO := (isOrthFamily_sub (k := k) (C := C) hpN ht₀ ht hb hbs hij (s := serreOdds N)
    fun a ha => (mem_serreOdds.1 ha).1).map_anti hflip hflip_add hflip_mul
  have hP : IsEquivPair (hflip (serreAlpha' t p N bs : A)) (hflip (serreAlpha'' t p N bs))
      (∑ n ∈ serreEvens N, hflip (serreIdem t p N bs n : A))
      (∑ n ∈ serreOdds N, hflip (serreIdem t p N bs n : A)) := by
    have := (prop6 (k := k) (C := C) hpN ht₀ ht hb hbs hij hN).map_anti hflip hflip_mul
    rwa [serreEven, serreOdd, hflip_sum, hflip_sum] at this
  (lIdealSumEquiv hE).symm.trans (hP.lIdealEquiv.trans (lIdealSumEquiv hO))

include hpN ht₀ ht hb hbs in
/-- KL II §3, the analogue of KL I, Corollary 2.14 (ungraded): for every left `R(ν)`-module `M`,
`⊕_{n even} 1_{…i^{(n)} j i^{(N-n)}…} M ≅ ⊕_{n odd} 1_{…i^{(n)} j i^{(N-n)}…} M`. -/
noncomputable def prop6_fixSubEquiv (M : Type*) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] (hij : i ≠ j) (hN : N = C.dij i j + 1) :
    ((n : serreEvens N) → fixSub k M (serreIdem t p N bs n : A)) ≃ₗ[k]
      ((n : serreOdds N) → fixSub k M (serreIdem t p N bs n : A)) :=
  have hE := isOrthFamily_sub (k := k) (C := C) hpN ht₀ ht hb hbs hij (s := serreEvens N)
    fun _ ha => (mem_serreEvens.1 ha).1
  have hO := isOrthFamily_sub (k := k) (C := C) hpN ht₀ ht hb hbs hij (s := serreOdds N)
    fun _ ha => (mem_serreOdds.1 ha).1
  have hP := prop6 (k := k) (C := C) hpN ht₀ ht hb hbs hij hN
  (fixSubSumEquiv hE k M).symm.trans (hP.fixSubEquiv.trans (fixSubSumEquiv hO k M))

/-! ### Degrees (KL II grading) -/

include hpN ht₀ ht in
theorem e_mul_etop {n : ℕ} (hn : n ≤ N) : (e (S n) * etop t p N n : A) = etop t p N n := by
  rw [etop, ← mul_assoc, ← mul_assoc, ← (commute_blockElt_left_e hpN ht₀ ht hn le_rfl le_rfl).eq,
    mul_assoc (blockElt p n), ← (commute_blockElt_right_e hpN ht₀ ht hn (by omega)
      (by omega)).eq, ← mul_assoc, mul_assoc _ (e _) (e _), e_mul_self]

include hpN ht₀ ht in
theorem etop_mem_grade {n : ℕ} (hn : n ≤ N) :
    (etop t p N n : A) ∈ (klGradingDatum2 k C).grade ν 0 := by
  rw [etop_eq_divIdem]
  exact divIdem_mem_grade _ (isBlocks_etop hpN ht₀ ht hn)

include hpN ht₀ ht hb hbs in
theorem serreIdem_mem_grade {n : ℕ} (hn : n ≤ N) :
    (serreIdem t p N bs n : A) ∈ (klGradingDatum2 k C).grade ν 0 := by
  rw [serreIdem_eq_divIdem hbs hn]
  refine divIdem_mem_grade _ ⟨fun b hb' => ?_, fun b hb' => ?_, ?_⟩
  · rcases List.mem_cons.1 hb' with rfl | hb'
    · simp only; omega
    rcases List.mem_cons.1 hb' with rfl | hb'
    · simp only; omega
    exact hb.le b hb'
  · rcases List.mem_cons.1 hb' with rfl | hb'
    · exact isConstOn_serreSeq_left hpN ht₀ ht hn le_rfl le_rfl
    rcases List.mem_cons.1 hb' with rfl | hb'
    · exact isConstOn_serreSeq_right hpN ht₀ ht hn (by omega) (by omega)
    exact (isBlocks_serreSeq hpN ht₀ ht hb hbs hn).const b hb'
  · refine List.Pairwise.cons (fun c hc => ?_) (List.Pairwise.cons (fun c hc => ?_) hb.disj)
    · rcases List.mem_cons.1 hc with rfl | hc
      · simp only; omega
      · have := hbs c hc; simp only; omega
    · have := hbs c hc; simp only; omega

include hpN ht₀ ht hb hbs in
/-- The map `α^+_{(n)}` is homogeneous of degree `-(N - n - 1) (i · i) - i · j` (one crossing of the
`j` and `N - n - 1` crossings of strands `i`); see `serreAp_degree_eq_shift`. -/
theorem serreAp_mem_grade {n : ℕ} (hn : n + 1 ≤ N) :
    (serreAp t p N bs n : A) ∈
      (klGradingDatum2 k C).grade ν (-((N - n - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j) := by
  have heq : (serreAp t p N bs n : A) = serreIdem t p N bs (n + 1) *
      ((ψ (p + n) * e (S n)) * (chainL (p + n + 1) (N - n - 1) * e (S n))) * etop t p N n := by
    have hL' : Commute (chainL (p + n + 1) (N - n - 1) : A) (e (S n)) :=
      commute_chainL_right_e hpN ht₀ ht (by omega) (by omega) (by omega)
    have key : (ψ (p + n) * (e (S n) * (chainL (p + n + 1) (N - n - 1) * (e (S n) *
        etop t p N n))) : A) = ψ (p + n) * (chainL (p + n + 1) (N - n - 1) * etop t p N n) := by
      rw [e_mul_etop hpN ht₀ ht (by omega), hL'.symm.left_comm, e_mul_etop hpN ht₀ ht (by omega)]
    rw [serreAp, if_pos hn, aplus_eq hpN ht₀ ht hn, chainL_eq_ψ_mul (by omega)]
    simp only [serreIdem, mul_assoc]
    rw [key]
  rw [heq, show -((N - n - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j =
    0 + (-C.dot i j + -((N - n - 1 : ℕ) : ℤ) * C.dot i i) + 0 by ring]
  refine SetLike.mul_mem_graded (SetLike.mul_mem_graded
    (serreIdem_mem_grade hpN ht₀ ht hb hbs (by omega))
    (SetLike.mul_mem_graded ?_ ?_)) (etop_mem_grade hpN ht₀ ht (by omega))
  · have := (klGradingDatum2 k C).ψ_mul_e_mem_grade (j := p + n) (by omega) (S n)
    rw [serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ rfl, serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _
      (by simp only; omega) (by simp only; omega) (by simp only; omega)] at this
    have h2 : (klGradingDatum2 k C).degΨ j i = -C.dot i j := by
      show -C.dot j i = -C.dot i j
      rw [C.symm]
    rwa [h2] at this
  · exact chainL_mul_e_mem_grade (by omega)
      (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega))
      (serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega) (by simp only; omega)
        (by simp only; omega))

include hpN ht₀ ht hb hbs in
/-- The map `α^-_{(n)}` is homogeneous of degree `-(n - 1) (i · i) - i · j` (`n - 1` crossings of
strands `i` and one crossing of the `j`); see `serreAm_degree_eq_shift`. -/
theorem serreAm_mem_grade {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ N) :
    (serreAm t p N bs n : A) ∈
      (klGradingDatum2 k C).grade ν (-((n - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j) := by
  have heq : (serreAm t p N bs n : A) = serreIdem t p N bs (n - 1) *
      ((ψ (p + n - 1) * e (S n)) * (chainR p (n - 1) * e (S n))) * etop t p N n := by
    have hR' : Commute (chainR p (n - 1) : A) (e (S n)) :=
      commute_chainR_left_e hpN ht₀ ht hn le_rfl (by omega)
    have key : (ψ (p + n - 1) * (e (S n) * (chainR p (n - 1) * (e (S n) *
        etop t p N n))) : A) = ψ (p + n - 1) * (chainR p (n - 1) * etop t p N n) := by
      rw [e_mul_etop hpN ht₀ ht hn, hR'.symm.left_comm, e_mul_etop hpN ht₀ ht hn]
    rw [serreAm, if_pos ⟨hn1, hn⟩, aminus_eq hpN ht₀ ht hn1 hn, chainR_eq_ψ_mul hn1]
    simp only [serreIdem, mul_assoc]
    rw [key]
  rw [heq, show -((n - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j =
    0 + (-C.dot i j + -((n - 1 : ℕ) : ℤ) * C.dot i i) + 0 by ring]
  refine SetLike.mul_mem_graded (SetLike.mul_mem_graded
    (serreIdem_mem_grade hpN ht₀ ht hb hbs (by omega))
    (SetLike.mul_mem_graded ?_ ?_)) (etop_mem_grade hpN ht₀ ht hn)
  · have := (klGradingDatum2 k C).ψ_mul_e_mem_grade (j := p + n - 1) (by omega) (S n)
    rw [serreSeq_lbl_eq_i hpN ht₀ ht hn _ (by simp only; omega) (by simp only; omega)
      (by simp only; omega), serreSeq_lbl_eq_j hpN ht₀ ht hn _ (by simp only; omega)] at this
    exact this
  · exact chainR_mul_e_mem_grade (by omega) (isConstOn_serreSeq_left hpN ht₀ ht hn le_rfl
      (by omega)) (serreSeq_lbl_eq_i hpN ht₀ ht hn _ le_rfl (by simp only; omega)
        (by simp only; omega))

omit [DecidableEq I] in
/-- The degree of `α^+_{(n)}` is the difference of the grading shifts: with
`⟨…i^{(a)} j i^{(b)}…⟩ = (a(a-1)/2 + b(b-1)/2) (i · i)/2` (KL II §3), `⟨S (n+1)⟩ - ⟨S n⟩ =
(2n + 1 - N)(i · i)/2`, and `2 (-(N - n - 1)(i · i) - i · j) = (2n + 1 - N)(i · i)`. -/
theorem serreAp_degree_eq_shift (hij : i ≠ j) (hN : N = C.dij i j + 1) {n : ℕ} (hn : n + 1 ≤ N) :
    2 * (-((N - n - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j) =
      (2 * (n : ℤ) + 1 - N) * C.dot i i := by
  have h := C.dij_mul hij
  have hN' : (N : ℤ) = C.dij i j + 1 := by exact_mod_cast hN
  have : ((N - n - 1 : ℕ) : ℤ) = N - n - 1 := by omega
  rw [this]; linear_combination (-1 : ℤ) * h + (-C.dot i i) * hN'

omit [DecidableEq I] in
/-- The degree of `α^-_{(n)}` is the difference of the grading shifts:
`⟨S (n-1)⟩ - ⟨S n⟩ = (N + 1 - 2n)(i · i)/2` and `2 (-(n - 1)(i · i) - i · j) = (N + 1 - 2n)(i · i)`. -/
theorem serreAm_degree_eq_shift (hij : i ≠ j) (hN : N = C.dij i j + 1) {n : ℕ} (hn1 : 1 ≤ n) :
    2 * (-((n - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j) =
      ((N : ℤ) + 1 - 2 * n) * C.dot i i := by
  have h := C.dij_mul hij
  have hN' : (N : ℤ) = C.dij i j + 1 := by exact_mod_cast hN
  have : ((n - 1 : ℕ) : ℤ) = n - 1 := by omega
  rw [this]; linear_combination (-1 : ℤ) * h + (-C.dot i i) * hN'

end serre

end Categorification.KLR.KL2
