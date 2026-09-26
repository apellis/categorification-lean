/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.KL2.Serre
import Categorification.KLR.DividedPowerK0

/-!
# Divided powers and the quantum Serre relations in `K₀(R(ν))` for KL II

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups II*,
arXiv:0804.2080v1, §3 (the paragraph before Proposition 6, and Proposition 6 / Corollary 7,
TeX labels `serre-right`, `serre-left`), and §2.5 of KL I (arXiv:0803.4121v2) "for an arbitrary
Cartan datum".

For a Cartan datum `C` and the KL II grading (`deg x_{a,i} = i_a · i_a`,
`deg ψ_{k,i} = - i_k · i_{k+1}`, `klGradingDatum2`), over any commutative ring `k`, and a
divided-power expression `i = i_1^{(n_1)} ⋯ i_r^{(n_r)}` (the list `d` of pairs `(i_a, n_a)`),
we use the graded projective left module

  `P_i = R(ν) ψ(1_i) {-⟨i⟩}`,   `⟨i⟩ = ∑_a (i_a · i_a)/2 · n_a (n_a - 1)/2`   (`projDiv2`),

the KL II analogue of KL I's `projDiv` (with `ψ = hflip`, as in `KL2.cor7_lIdealEquiv`). In
`K₀(R(ν))` (a `ℤ[q, q⁻¹]`-module, `q^a [P] = [P{a}]`) we prove:

* `K0_projSeq2_expandDiv` : **`[P_î] = i! [P_i]`**, with `i! = ∏_a [n_a]_{q_{i_a}}^!`, where
  `q_c = q^{(c · c)/2}` (`tUnit`): the quantum integers are those of `v_i = v^{(i·i)/2}`.
* `K0_serre_window` : **the categorified quantum Serre relation in `K₀`**, from KL II
  Proposition 6: for `i ≠ j`, `N = d_ij + 1` and the window data of `Categorification.KLR.KL2`
  (`t = …j i^N…`, the idempotents `serreIdem t p N bs n = 1_{…i^{(n)} j i^{(N-n)}…}`),
  `∑_{n=0}^{N} (-1)^n q^{-s_n} [R(ν) ψ(1_{…i^{(n)} j i^{(N-n)}…})] = 0` for any grading
  shifts `s_n` with `s_{n+1} - s_n = deg α^+_{(n)}`, e.g. the shifts `⟨…⟩` (`serreAp_degree_eq_shift`).
  The divided-power form `∑_{n even} [P_{…i^{(n)} j i^{(N-n)}…}] = ∑_{n odd} [P_{…}]` in the
  total `K₀(R) = ⊕_ν K₀(R(ν))` is `KL2Gamma.clsDiv2_serre` (`Categorification.KLR.KL2.Gamma2`).

## The argument for the Serre relation

Proposition 6 is proved in `Categorification.KLR.KL2.Serre` via the relations
`α^-_{(n+1)} α^+_{(n)} - α^+_{(n-1)} α^-_{(n)} = (-1)^n 1_{(n)}` (`serre_rel`),
`α^+ α^+ = 0`, `α^- α^- = 0`. Hence `1_{(n)} = G^+_n + G^-_n` with orthogonal idempotents
`G^+_n = (-1)^n α^-_{(n+1)} α^+_{(n)}` and `G^-_n = -(-1)^n α^+_{(n-1)} α^-_{(n)}`, and
`G^+_n = x y`, `G^-_{n+1} = y x` with `x = (-1)^n α^-_{(n+1)}`, `y = α^+_{(n)}` homogeneous of
opposite degrees. In `K₀` this gives `[1_{(n)}] = [G^+_n] + [G^-_n]` and
`[G^+_n] = q^{-deg α^+_{(n)}} [G^-_{n+1}]`, and the alternating sum telescopes
(`Graded.K0.sum_neg_one_pow_smul_of_zigzag`, a general statement about graded algebras). This
avoids constructing the matrix isomorphism `⊕_{n even} P_{(n)} ≅ ⊕_{n odd} P_{(n)}` with
shifts, which is not needed for the relation in `K₀`.
-/

noncomputable section

namespace Categorification

open Categorification.Graded Categorification.KLR Categorification.KLR.KLRAlgebra
  LaurentPolynomial Categorification.QuantumGroup Finset

/-! ### A telescoping lemma in `K₀` -/

namespace Graded.K0

universe u v

variable {k : Type v} [CommRing k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
  [GradedAlgebra 𝒜]

theorem of_ofIdempotent_zero (h : IsIdempotentElem (0 : A)) (h0 : (0 : A) ∈ 𝒜 0) :
    of (GProj.ofIdempotent (0 : A) h h0) = 0 := by
  have := of_ofIdempotent_add (𝒜 := 𝒜) (add_zero (0 : A)) h h (mul_zero 0) (mul_zero 0) h h0
    h0 h0
  simpa using this

/-- **A telescoping relation in `K₀`.** Let `E_n` (`n ≤ N`) be idempotents of degree `0` which
split as `E_n = G^+_n + G^-_n` into orthogonal pieces (with `G^±_n E_n = G^±_n`), such that
`G^-_0 = 0`, `G^+_N = 0` and, for `n < N`, `G^+_n = x y` and `G^-_{n+1} = y x` with `x`, `y`
homogeneous of degrees `d_n`, `-d_n`. If `s_{n+1} = s_n + d_n`, then
`∑_{n=0}^{N} (-1)^n q^{-s_n} [A E_n] = 0`. -/
theorem sum_neg_one_pow_smul_of_zigzag {N : ℕ} {E Gp Gm : ℕ → A} {dg sh : ℕ → ℤ}
    (hE : ∀ n, n ≤ N → IsIdempotentElem (E n)) (hE0 : ∀ n, n ≤ N → E n ∈ 𝒜 0)
    (hsum : ∀ n, n ≤ N → Gp n + Gm n = E n)
    (hpm : ∀ n, n ≤ N → Gp n * Gm n = 0) (hmp : ∀ n, n ≤ N → Gm n * Gp n = 0)
    (hpE : ∀ n, n ≤ N → Gp n * E n = Gp n) (hmE : ∀ n, n ≤ N → Gm n * E n = Gm n)
    (hxy : ∀ n, n < N → ∃ x y : A, x ∈ 𝒜 (dg n) ∧ y ∈ 𝒜 (-dg n) ∧ x * y = Gp n ∧
      y * x = Gm (n + 1))
    (hGm : Gm 0 = 0) (hGp : Gp N = 0) (hsh : ∀ n, n < N → sh (n + 1) = sh n + dg n)
    (P : ℕ → K0 𝒜)
    (hP : ∀ n (hn : n ≤ N), P n = of (GProj.ofIdempotent (E n) (hE n hn) (hE0 n hn))) :
    ∑ n ∈ range (N + 1), ((-1 : LaurentPolynomial ℤ) ^ n * T (-sh n)) • P n = 0 := by
  have hpI : ∀ n, n ≤ N → IsIdempotentElem (Gp n) := fun n hn => by
    unfold IsIdempotentElem
    calc Gp n * Gp n = Gp n * (Gp n + Gm n) := by rw [mul_add, hpm n hn, add_zero]
      _ = Gp n := by rw [hsum n hn, hpE n hn]
  have hmI : ∀ n, n ≤ N → IsIdempotentElem (Gm n) := fun n hn => by
    unfold IsIdempotentElem
    calc Gm n * Gm n = Gm n * (Gp n + Gm n) := by rw [mul_add, hmp n hn, zero_add]
      _ = Gm n := by rw [hsum n hn, hmE n hn]
  have hp0 : ∀ n, n ≤ N → Gp n ∈ 𝒜 0 := fun n hn => by
    rcases Nat.lt_or_ge n N with h | h
    · obtain ⟨x, y, hx, hy, h1, -⟩ := hxy n h
      rw [← h1]; exact mem_zero_of_mul hx hy
    · rw [show n = N by omega, hGp]; exact zero_mem _
  have hm0 : ∀ n, n ≤ N → Gm n ∈ 𝒜 0 := fun n hn => by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rw [hGm]; exact zero_mem _
    · obtain ⟨x, y, hx, hy, -, h2⟩ := hxy (n - 1) (by omega)
      rw [show n = n - 1 + 1 by omega, ← h2]
      have := mem_zero_of_mul hy (show x ∈ 𝒜 (-(-dg (n - 1))) by rwa [neg_neg])
      exact this
  let Qp : ℕ → K0 𝒜 := fun n =>
    if h : n ≤ N then of (GProj.ofIdempotent (Gp n) (hpI n h) (hp0 n h)) else 0
  let Qm : ℕ → K0 𝒜 := fun n =>
    if h : n ≤ N then of (GProj.ofIdempotent (Gm n) (hmI n h) (hm0 n h)) else 0
  have hPQ : ∀ n, n ≤ N → P n = Qp n + Qm n := fun n hn => by
    simp only [Qp, Qm, dif_pos hn]
    rw [hP n hn]
    exact of_ofIdempotent_add (hsum n hn) _ _ (hpm n hn) (hmp n hn) _ _ _ _
  have hQ : ∀ n, n < N → Qp n = T (-dg n) • Qm (n + 1) := fun n hn => by
    obtain ⟨x, y, hx, hy, h1, h2⟩ := hxy n hn
    simp only [Qp, Qm, dif_pos hn.le, dif_pos (show n + 1 ≤ N by omega)]
    exact of_ofIdempotent_eq_T_smul hx hy h1 h2 _ _ _ _
  have hQm0 : Qm 0 = 0 := by
    simp only [Qm, dif_pos (Nat.zero_le N)]
    rw [of_ofIdempotent_congr hGm _ (by simp [IsIdempotentElem]) _ (zero_mem _),
      of_ofIdempotent_zero]
  have hQpN : Qp N = 0 := by
    simp only [Qp, dif_pos le_rfl]
    rw [of_ofIdempotent_congr hGp _ (by simp [IsIdempotentElem]) _ (zero_mem _),
      of_ofIdempotent_zero]
  set c : ℕ → LaurentPolynomial ℤ := fun n => (-1 : LaurentPolynomial ℤ) ^ n * T (-sh n)
  have hc : ∀ n, n < N → c n * T (-dg n) = -c (n + 1) := fun n hn => by
    simp only [c]
    rw [hsh n hn, mul_assoc, ← T_add, pow_succ]
    ring_nf
  calc ∑ n ∈ range (N + 1), c n • P n
      = ∑ n ∈ range (N + 1), c n • Qp n + ∑ n ∈ range (N + 1), c n • Qm n := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun n hn => ?_
        rw [hPQ n (by rw [mem_range] at hn; omega), smul_add]
    _ = ∑ n ∈ range N, -(c (n + 1) • Qm (n + 1)) + ∑ n ∈ range N, c (n + 1) • Qm (n + 1) := by
        rw [sum_range_succ, hQpN, smul_zero, add_zero, sum_range_succ', hQm0, smul_zero,
          add_zero]
        congr 1
        refine sum_congr rfl fun n hn => ?_
        rw [mem_range] at hn
        rw [hQ n hn, smul_smul, hc n hn, neg_smul]
    _ = 0 := by rw [sum_neg_distrib, neg_add_cancel]

end Graded.K0

namespace KLR.KL2

/-! ### Quantum integers `[n]_{q^h}` in `ℤ[q, q⁻¹]` -/

section QInt

/-- The unit `q^h ∈ ℤ[q, q⁻¹]` (for `h = (i · i)/2` this is `q_i`, the image of `v_i⁻¹`). -/
def tUnit (h : ℤ) : (LaurentPolynomial ℤ)ˣ := qUnitLP ^ h

theorem val_tUnit_zpow (h z : ℤ) :
    ((tUnit h ^ z : (LaurentPolynomial ℤ)ˣ) : LaurentPolynomial ℤ) = T (h * z) := by
  rw [tUnit, ← zpow_mul, val_qUnitLP_zpow]

theorem qint_tUnit (h : ℤ) (n : ℕ) :
    qint (tUnit h) n = ∑ j ∈ range n, (T (h * ((n : ℤ) - 1 - 2 * j)) : LaurentPolynomial ℤ) := by
  rw [qint_eq_sum]
  exact sum_congr rfl fun j _ => val_tUnit_zpow _ _

theorem sum_T_mul_sub (h : ℤ) (n : ℕ) :
    ∑ j : Fin (n + 1), (T (-(2 * h * ((n : ℤ) - j))) : LaurentPolynomial ℤ) =
      T (-(h * n)) * qint (tUnit h) (n + 1) := by
  rw [qint_tUnit, mul_sum, Fin.sum_univ_eq_sum_range (fun j => (T (-(2 * h * ((n : ℤ) - j))) :
    LaurentPolynomial ℤ)) (n + 1), ← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [← T_add]
  congr 1
  push_cast [Nat.cast_sub (show j ≤ n by omega)]
  ring

/-- The factor `q^{-h n(n-1)/2} [n]_{q^h}^!` of a divided power `i^{(n)}`, `h = (i · i)/2`. -/
def blockFactor2 (h : ℤ) (n : ℕ) : LaurentPolynomial ℤ :=
  T (-(h * (n.choose 2 : ℤ))) * qfact (tUnit h) n

theorem blockFactor2_zero (h : ℤ) : blockFactor2 h 0 = 1 := by simp [blockFactor2]

theorem blockFactor2_succ (h : ℤ) (n : ℕ) :
    blockFactor2 h (n + 1) = blockFactor2 h n * (T (-(h * n)) * qint (tUnit h) (n + 1)) := by
  rw [blockFactor2, blockFactor2, qfact_succ, NilHecke.choose_two_succ,
    show (-(h * (((n.choose 2 + n : ℕ)) : ℤ))) = -(h * (n.choose 2 : ℤ)) + -(h * n) by
      push_cast; ring, T_add]
  ring

end QInt

/-! ### The projectives `P_i` for the KL II grading -/

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {C : CartanDatum I}
  {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => R2 k C ν

omit [DecidableEq I] in
theorem klGradingDatum2_degΨ_symm (a b : I) :
    (klGradingDatum2 k C).degΨ a b = (klGradingDatum2 k C).degΨ b a := by
  show -C.dot a b = -C.dot b a
  rw [C.symm]

/-- **KL II**: the antiinvolution `ψ` of `R(ν)` preserves degrees. -/
theorem hflip_mem_grade2 {d : ℤ} {a : A} (ha : a ∈ (klGradingDatum2 k C).grade ν d) :
    hflip a ∈ (klGradingDatum2 k C).grade ν d :=
  (klGradingDatum2 k C).hflip_mem_grade klGradingDatum2_degΨ_symm ha

/-- `hflip` as an additive map of `R(ν)` (KL II). -/
def hflipAddKL2 : A →+ A := AddMonoidHom.mk' hflip hflip_add

@[simp] theorem hflipAddKL2_apply (a : A) : hflipAddKL2 a = hflip a := rfl

theorem hflip_zsmul (c : ℤ) (a : A) : hflip (c • a) = c • hflip a :=
  map_zsmul (hflipAddKL2 (k := k) (C := C) (ν := ν)) c a

theorem hflip_neg' (a : A) : hflip (-a) = -hflip a :=
  map_neg (hflipAddKL2 (k := k) (C := C) (ν := ν)) a

variable (k C) in
/-- The graded projective module `P_t = R(ν) 1_t` of a sequence `t` (KL II grading). -/
def projSeq2 (t : Seq ν) : GProj ((klGradingDatum2 k C).grade ν) :=
  GProj.ofIdempotent (e t : A) (e_mul_self t) ((klGradingDatum2 k C).e_mem_grade t)

variable (k C) in
/-- The graded projective module `R(ν) ψ(1_t^{bs})` for a sequence `t` with divided-power blocks
`bs` (without grading shift), KL II grading. -/
def projFlip2 (t : Seq ν) (bs : List (ℕ × ℕ)) (h : IsBlocks t bs) :
    GProj ((klGradingDatum2 k C).grade ν) :=
  GProj.ofIdempotent (hflip (divIdem t bs : A)) (isIdempotentElem_hflip_divIdem h)
    (hflip_mem_grade2 (divIdem_mem_grade _ h))

variable (C) in
/-- The KL II grading shift `⟨i⟩ = ∑_a (i_a · i_a)/2 · n_a (n_a - 1)/2` of a divided-power
expression `i = i_1^{(n_1)} ⋯ i_r^{(n_r)}` (for the KL I datum this is `divAngle`). -/
def divAngle2 (d : List (I × ℕ)) : ℤ := (d.map fun q => C.dot q.1 q.1 / 2 * (q.2.choose 2 : ℤ)).sum

omit [DecidableEq I] in
theorem divAngle2_append (d₁ d₂ : List (I × ℕ)) :
    divAngle2 C (d₁ ++ d₂) = divAngle2 C d₁ + divAngle2 C d₂ := by
  simp [divAngle2]

variable (k C) in
/-- **The projective `P_i = R(ν) ψ(1_i) {-⟨i⟩}`** of a divided-power expression `i` for the KL II
grading. -/
def projDiv2 (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    GProj ((klGradingDatum2 k C).grade ν) :=
  (projFlip2 k C _ _ (isBlocks_ofList d h)).shift (-divAngle2 C d)

theorem K0_of_projFlip2_congr {t t' : Seq ν} {bs bs' : List (ℕ × ℕ)} (h : IsBlocks t bs)
    (h' : IsBlocks t' bs') (he : (divIdem t bs : A) = divIdem t' bs') :
    K0.of (projFlip2 k C t bs h) = K0.of (projFlip2 k C t' bs' h') :=
  K0.of_ofIdempotent_congr (congrArg hflip he) _ _ _ _

/-! ### `[P_î] = i! [P_i]` -/

/-- **Splitting a divided power, `K₀` form (KL II)**: if the labels of the block `[p, p + n + 1)`
have `i · i = 2h`, then
`[R(ν) ψ(1_{…i^{(n)} i…})] = q^{-h n} [n+1]_{q^h} [R(ν) ψ(1_{…i^{(n+1)}…})]`. -/
theorem K0_projFlip2_succ {i : Seq ν} {p n : ℕ} {bs : List (ℕ × ℕ)}
    (h : IsBlocks i ((p, n + 1) :: bs)) {hh : ℤ}
    (hdeg : ∀ a : Fin m, p ≤ a → (a : ℕ) < p + (n + 1) → C.dot (i.lbl a) (i.lbl a) = 2 * hh) :
    K0.of (projFlip2 k C i ((p, n) :: bs) (h.cons_mono (Nat.le_succ n))) =
      (T (-(hh * n)) * qint (tUnit hh) (n + 1)) • K0.of (projFlip2 k C i ((p, n + 1) :: bs) h) := by
  have hpn := h.le _ List.mem_cons_self
  have hc := h.const _ List.mem_cons_self
  simp only at hpn
  have hcl : ∀ a : Fin (Multiset.card ν), p ≤ a → (a : ℕ) < p + (n + 1) →
      i.lbl a = i.lbl ⟨p, by omega⟩ := fun a h1 h2 => hc a _ h1 h2 le_rfl (by simp only; omega)
  have hc2 : (klGradingDatum2 k C).degX (i.lbl ⟨p, by omega⟩) = 2 * hh :=
    hdeg ⟨p, by omega⟩ le_rfl (by simp only; omega)
  have S := (isSplitting_divIdem_succ (k := k) (Q := klQ2 k C) h).map_anti hflipAddKL2 hflip_mul
  simp only [hflipAddKL2_apply] at S
  rw [projFlip2, projFlip2, K0.of_ofIdempotent_eq_sum_of_isSplitting (dg := fun j : Fin (n + 1) =>
    (klGradingDatum2 k C).degX (i.lbl ⟨p, by omega⟩) * ((n : ℤ) - j)) S (fun j => ?_)
    (fun j => ?_) _ (fun _ => _) _ (fun _ => _), hc2, ← sum_T_mul_sub, sum_smul]
  · exact hflip_mem_grade2 (blockB_mem_grade (klGradingDatum2 k C) hpn hcl hc
      (show (j : ℕ) ≤ n by omega))
  · refine hflip_mem_grade2 ?_
    have := SetLike.mul_mem_graded (divIdem_mem_grade (klGradingDatum2 k C) h.tail)
      (blockA_mem_grade (klGradingDatum2 k C) hpn hcl hc j)
    convert this using 2
    ring

/-- **A divided power in a context, `K₀` form (KL II)**: if the labels of `[p, p + n)` have
`i · i = 2h`, `[R(ν) ψ(1_{…i⋯i…})] = q^{-h n(n-1)/2} [n]_{q^h}^! [R(ν) ψ(1_{…i^{(n)}…})]`. -/
theorem K0_projFlip2_block {i : Seq ν} {p : ℕ} {bs : List (ℕ × ℕ)} (hbs : IsBlocks i bs)
    {hh : ℤ} :
    ∀ {n : ℕ} (h : IsBlocks i ((p, n) :: bs))
      (_hdeg : ∀ a : Fin m, p ≤ a → (a : ℕ) < p + n → C.dot (i.lbl a) (i.lbl a) = 2 * hh),
      K0.of (projFlip2 k C i bs hbs) = blockFactor2 hh n • K0.of (projFlip2 k C i ((p, n) :: bs) h)
  | 0, h, _ => by
    rw [blockFactor2_zero, one_smul]
    refine K0_of_projFlip2_congr _ _ ?_
    rw [divIdem, divIdem, blocksElt_cons]
    simp only
    rw [blockElt_zero, one_mul]
  | n + 1, h, hdeg => by
    rw [K0_projFlip2_block hbs (h.cons_mono (Nat.le_succ n))
      (fun a h1 h2 => hdeg a h1 (by omega)), K0_projFlip2_succ h hdeg, ← mul_smul,
      blockFactor2_succ]

/-- Iterating over all blocks (KL II): if the labels of each block `b` have `i · i = 2 h(b.1)`,
`[R(ν) 1_t] = ∏_b q^{-h n_b(n_b-1)/2} [n_b]_{q^h}^! · [R(ν) ψ(1_t^{bs})]`. -/
theorem K0_projSeq2_eq_prod_smul {t : Seq ν} (hh : ℕ → ℤ) :
    ∀ {bs : List (ℕ × ℕ)} (h : IsBlocks t bs)
      (_hdeg : ∀ b ∈ bs, ∀ a : Fin m, b.1 ≤ a → (a : ℕ) < b.1 + b.2 →
        C.dot (t.lbl a) (t.lbl a) = 2 * hh b.1),
      K0.of (projSeq2 k C t) =
        (bs.map fun b => blockFactor2 (hh b.1) b.2).prod • K0.of (projFlip2 k C t bs h)
  | [], h, _ => by
    rw [List.map_nil, List.prod_nil, one_smul]
    exact K0.of_ofIdempotent_congr (e := (e t : A)) (e' := hflip (divIdem t [] : A))
      (by rw [divIdem_nil, hflip_e]) _ _ _ _
  | b :: bs, h, hdeg => by
    rw [K0_projSeq2_eq_prod_smul hh h.tail (fun b' hb' => hdeg b' (List.mem_cons_of_mem _ hb')),
      K0_projFlip2_block (p := b.1) (n := b.2) h.tail h (hdeg b List.mem_cons_self),
      List.map_cons, List.prod_cons, ← mul_smul, mul_comm]

variable (C) in
/-- The half-degree `(c · c)/2` of the label `c = L_p` at position `p` of a list (`0` out of
range). -/
def labHalf (L : List I) (p : ℕ) : ℤ := (L[p]?).elim 0 fun c => C.dot c c / 2

omit [DecidableEq I] in
theorem labHalf_of_lt (L : List I) {p : ℕ} (hp : p < L.length) :
    labHalf C L p = C.dot L[p] L[p] / 2 := by
  simp [labHalf, List.getElem?_eq_getElem hp]

variable (C) in
/-- `i! = [n_1]_{q_{i_1}}^! ⋯ [n_r]_{q_{i_r}}^!` in `ℤ[q, q⁻¹]` (`q_c = q^{(c·c)/2}`). -/
def divQFact2 (d : List (I × ℕ)) : LaurentPolynomial ℤ :=
  (d.map fun q => qfact (tUnit (C.dot q.1 q.1 / 2)) q.2).prod

omit [DecidableEq I] in
theorem divQFact2_append (d d' : List (I × ℕ)) :
    divQFact2 C (d ++ d') = divQFact2 C d * divQFact2 C d' := by
  simp [divQFact2]

omit [DecidableEq I] in
theorem prod_blockFactor2_blocksDiv (d : List (I × ℕ)) (pre : List I) :
    ((blocksDiv d pre.length).map fun b =>
        blockFactor2 (labHalf C (pre ++ expandDiv d) b.1) b.2).prod =
      T (-divAngle2 C d) * divQFact2 C d := by
  induction d generalizing pre with
  | nil => simp [blocksDiv, divAngle2, divQFact2]
  | cons q d ih =>
    have hL : pre ++ expandDiv (q :: d) = (pre ++ List.replicate q.2 q.1) ++ expandDiv d := by
      simp [expandDiv, List.flatMap_cons]
    have ih' := ih (pre ++ List.replicate q.2 q.1)
    rw [List.length_append, List.length_replicate, ← hL] at ih'
    have hq : blockFactor2 (labHalf C (pre ++ expandDiv (q :: d)) pre.length) q.2 =
        blockFactor2 (C.dot q.1 q.1 / 2) q.2 := by
      rcases Nat.eq_zero_or_pos q.2 with h0 | h0
      · rw [h0, blockFactor2_zero, blockFactor2_zero]
      · have hget : ((pre ++ List.replicate q.2 q.1) ++ expandDiv d)[pre.length]'(by
            simp; omega) = q.1 := by
          rw [List.getElem_append_left (by simp; omega), List.getElem_append_right le_rfl]
          simp
        rw [hL, labHalf_of_lt _ (by simp; omega), hget]
    simp only [blocksDiv, List.map_cons, List.prod_cons, ih', hq, divAngle2, divQFact2,
      List.sum_cons]
    rw [blockFactor2, show -(C.dot q.1 q.1 / 2 * (q.2.choose 2 : ℤ) +
      (d.map fun q => C.dot q.1 q.1 / 2 * (q.2.choose 2 : ℤ)).sum) =
      -(C.dot q.1 q.1 / 2 * (q.2.choose 2 : ℤ)) +
        -(d.map fun q => C.dot q.1 q.1 / 2 * (q.2.choose 2 : ℤ)).sum by ring, T_add]
    ring

/-- **KL I §2.5 for KL II, `P_î ≅ P_i^{i!}` in `K₀`**: `[P_î] = i! [P_i]` for a divided-power
expression `i` with expansion `î`, where `i! = ∏_a [n_a]_{q_{i_a}}^!` and `q_c = q^{(c·c)/2}`
(`P_î = R(ν) 1_î`, `P_i = R(ν) ψ(1_i) {-⟨i⟩}`). -/
theorem K0_projSeq2_expandDiv (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    K0.of (projSeq2 k C (Seq.ofList (expandDiv d) h)) =
      divQFact2 C d • K0.of (projDiv2 k C d h) := by
  have hdeg : ∀ b ∈ blocksDiv d 0, ∀ a : Fin m, b.1 ≤ a → (a : ℕ) < b.1 + b.2 →
      C.dot ((Seq.ofList (expandDiv d) h).lbl a) ((Seq.ofList (expandDiv d) h).lbl a) =
        2 * labHalf C (expandDiv d) b.1 := by
    intro b hb a h1 h2
    have hm : (expandDiv d).length = m := by rw [← Multiset.coe_card, h]
    have hb1 : b.1 < m := lt_of_le_of_lt h1 a.2
    have hc := (isBlocks_ofList d h).const b hb a ⟨b.1, hb1⟩ h1 h2 le_rfl (by simp only; omega)
    rw [hc, Seq.ofList_lbl, labHalf_of_lt _ (by rw [hm]; exact hb1)]
    obtain ⟨r, hr⟩ := C.dot_self_even ((expandDiv d)[b.1]'(by rw [hm]; exact hb1))
    simp only [Fin.val_mk]
    omega
  rw [K0_projSeq2_eq_prod_smul _ (isBlocks_ofList d h) hdeg]
  have := prod_blockFactor2_blocksDiv (C := C) d []
  simp only [List.length_nil, List.nil_append] at this
  rw [this, projDiv2, ← K0.T_smul_of, ← mul_smul, mul_comm]

/-! ### The quantum Serre relation in `K₀` (KL II, Proposition 6) -/

section serre

variable {t : Seq ν} {p N : ℕ} {bs : List (ℕ × ℕ)} {i j : I} (hpN : p + N < Multiset.card ν)
  (ht₀ : ∀ r : Fin (Multiset.card ν), (r : ℕ) = p → t.lbl r = j)
  (ht : ∀ r : Fin (Multiset.card ν), p < r → (r : ℕ) ≤ p + N → t.lbl r = i)
  (hb : IsBlocks t bs) (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ p ∨ p + N + 1 ≤ b.1)

include hpN ht₀ ht hb hbs in
theorem isIdempotentElem_hflip_serreIdem (hij : i ≠ j) {n : ℕ} (hn : n ≤ N) :
    IsIdempotentElem (hflip (serreIdem t p N bs n : A)) := by
  have := serreIdem_mul_serreIdem (k := k) (C := C) hpN ht₀ ht hb hbs hn hn hij
  rw [if_pos rfl] at this
  unfold IsIdempotentElem
  rw [← hflip_mul, this]

include hpN ht₀ ht hb hbs in
theorem hflip_serreIdem_mem_grade {n : ℕ} (hn : n ≤ N) :
    hflip (serreIdem t p N bs n : A) ∈ (klGradingDatum2 k C).grade ν 0 :=
  hflip_mem_grade2 (serreIdem_mem_grade hpN ht₀ ht hb hbs hn)

theorem neg_one_zpow_smul_mul (n : ℕ) (x : A) : ((-1 : A) ^ n * x) = ((-1 : ℤ) ^ n) • x := by
  rw [zsmul_eq_mul]; push_cast; rfl

theorem neg_one_zpow_mul_self (n : ℕ) : ((-1 : ℤ) ^ n) * (-1) ^ n = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

include hpN ht₀ ht hb hbs in
/-- **The categorified quantum Serre relation in `K₀(R(ν))`** (KL II, Proposition 6 /
Corollary 7, for left projectives `R(ν) ψ(1_{…})`). For labels `i ≠ j`, `N = d_ij + 1`, the window
data `t = …j i^N…` at position `p` with context blocks `bs`, and grading shifts `s_n` with
`s_{n+1} = s_n + deg α^+_{(n)}` (`deg α^+_{(n)} = -(N - n - 1)(i · i) - i · j`,
`serreAp_mem_grade`), we have
`∑_{n=0}^{N} (-1)^n q^{-s_n} [R(ν) ψ(1_{…i^{(n)} j i^{(N-n)}…})] = 0`.
Here `P n` is any family with `P n = [R(ν) ψ(serreIdem n)]` for `n ≤ N`. -/
theorem K0_serre_window (hij : i ≠ j) (hN : N = C.dij i j + 1) (sh : ℕ → ℤ)
    (hsh : ∀ n, n < N → sh (n + 1) = sh n + (-((N - n - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j))
    (P : ℕ → K0 ((klGradingDatum2 k C).grade ν))
    (hP : ∀ n (hn : n ≤ N), P n = K0.of (GProj.ofIdempotent (hflip (serreIdem t p N bs n : A))
      (isIdempotentElem_hflip_serreIdem hpN ht₀ ht hb hbs hij hn)
      (hflip_serreIdem_mem_grade hpN ht₀ ht hb hbs hn))) :
    ∑ n ∈ range (N + 1), ((-1 : LaurentPolynomial ℤ) ^ n * T (-sh n)) • P n = 0 := by
  set Ap : ℕ → A := serreAp t p N bs with hAp
  set Am : ℕ → A := serreAm t p N bs with hAm
  set E : ℕ → A := serreIdem t p N bs with hE
  set X : ℕ → A := fun n => ((-1 : ℤ) ^ n) • (Am (n + 1) * Ap n) with hX
  set Y : ℕ → A := fun n => -(((-1 : ℤ) ^ n) • (Ap (n - 1) * Am n)) with hY
  have hAm0 : Am 0 = 0 := serreAm_of_not (by omega)
  have hAmN : Am (N + 1) = 0 := serreAm_of_not (by omega)
  have hY0 : Y 0 = 0 := by simp only [hY, hAm0, mul_zero, smul_zero, neg_zero]
  have hsum : ∀ n, n ≤ N → X n + Y n = E n := fun n hn => by
    have h := serre_rel (k := k) (C := C) hpN ht₀ ht hb hbs hij hN hn
    simp only [hX, hY, ← sub_eq_add_neg, ← smul_sub]
    rw [h, neg_one_zpow_smul_mul, smul_smul, neg_one_zpow_mul_self, one_smul]
  have hAA : ∀ n, Am n * Am (n + 1) = 0 := fun n => by
    simpa using serreAm_pred_mul_serreAm (k := k) (C := C) hpN ht₀ ht hb hbs hij (n + 1)
  have hPP : ∀ n, 1 ≤ n → Ap n * Ap (n - 1) = 0 := fun n hn => by
    have := serreAp_succ_mul_serreAp (k := k) (C := C) hpN ht₀ ht hb hbs hij (n - 1)
    rwa [show n - 1 + 1 = n by omega] at this
  have hYX : ∀ n, Y n * X n = 0 := fun n => by
    simp only [hX, hY, neg_mul, smul_mul_smul_comm, mul_assoc, ← mul_assoc (Am n), hAA,
      zero_mul, mul_zero, smul_zero, neg_zero]
  have hXY : ∀ n, X n * Y n = 0 := fun n => by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; rw [hY0, mul_zero]
    · simp only [hX, hY, mul_neg, smul_mul_smul_comm, mul_assoc, ← mul_assoc (Ap n),
        hPP n h0, zero_mul, mul_zero, smul_zero, neg_zero]
  have hEX : ∀ n, E n * X n = X n := fun n => by
    have h1 : E n * Am (n + 1) = Am (n + 1) := by
      simpa using serreIdem_mul_serreAm (k := k) (C := C) hpN ht₀ ht hb hbs (n + 1)
    simp only [hX, mul_smul_comm, ← mul_assoc, h1]
  have hEY : ∀ n, E n * Y n = Y n := fun n => by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; rw [hY0, mul_zero]
    · have h1 : E n * Ap (n - 1) = Ap (n - 1) := by
        have := serreIdem_mul_serreAp (k := k) (C := C) hpN ht₀ ht hb hbs (n - 1)
        rwa [show n - 1 + 1 = n by omega] at this
      simp only [hY, mul_neg, mul_smul_comm, ← mul_assoc, h1]
  refine Graded.K0.sum_neg_one_pow_smul_of_zigzag (E := fun n => hflip (E n))
    (Gp := fun n => hflip (X n)) (Gm := fun n => hflip (Y n))
    (dg := fun n => -((N - n - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j)
    (fun n hn => isIdempotentElem_hflip_serreIdem hpN ht₀ ht hb hbs hij hn)
    (fun n hn => hflip_serreIdem_mem_grade hpN ht₀ ht hb hbs hn)
    (fun n hn => by simp only; rw [← hflip_add, hsum n hn])
    (fun n _ => by simp only; rw [← hflip_mul, hYX, hflip_zero])
    (fun n _ => by simp only; rw [← hflip_mul, hXY, hflip_zero])
    (fun n _ => by simp only; rw [← hflip_mul, hEX])
    (fun n _ => by simp only; rw [← hflip_mul, hEY])
    (fun n hn => ?_) (by simp only; rw [hY0, hflip_zero])
    (by simp only [hX, hAmN, zero_mul, smul_zero, hflip_zero]) hsh P hP
  refine ⟨((-1 : ℤ) ^ n) • hflip (Ap n), hflip (Am (n + 1)), zsmul_mem (hflip_mem_grade2
    (serreAp_mem_grade hpN ht₀ ht hb hbs (show n + 1 ≤ N by omega))) _, ?_, ?_, ?_⟩
  · refine hflip_mem_grade2 ?_
    have := serreAm_mem_grade (k := k) (C := C) hpN ht₀ ht hb hbs (n := n + 1) (by omega) (by omega)
    convert this using 2
    have h := C.dij_mul hij
    have hN' : (N : ℤ) = C.dij i j + 1 := by exact_mod_cast hN
    have e1 : ((N - n - 1 : ℕ) : ℤ) = N - n - 1 := by omega
    have e2 : ((n + 1 - 1 : ℕ) : ℤ) = n := by omega
    simp only
    rw [e1, e2]
    linear_combination h + (C.dot i i) * hN'
  · simp only [hX]
    rw [hflip_zsmul, hflip_mul, smul_mul_assoc]
  · simp only [hY]
    rw [hflip_neg', hflip_zsmul, hflip_mul, mul_smul_comm, show n + 1 - 1 = n by omega,
      pow_succ, mul_neg_one, neg_smul, neg_neg]

end serre

end KLR.KL2

end Categorification
