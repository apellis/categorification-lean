/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.DividedPowers
import Categorification.KLR.KL2.Serre

/-!
# The categorified Serre relations in `U̇` (KL III Proposition 3.24, upward strands)

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.5,
Proposition 3.24 (TeX label `serre-isoms`), first display: for `i ≠ j`, `d = d_ij = -⟨i, j_X⟩`,

  `⊕_{a=0}^{⌊(d+1)/2⌋} E_{…+i^{(2a)} +j +i^{(d+1-2a)}…} 1_λ ≅
    ⊕_{a=0}^{⌊d/2⌋} E_{…+i^{(2a+1)} +j +i^{(d-2a)}…} 1_λ`.

KL III's proof: "These isomorphisms follow from categorified quantum Serre relations
[KL1, Proposition 2.13] and [KL2, Proposition 6] between idempotents in rings `R(ν)`, via
homomorphisms `ϕ_{ν,λ}`." We give exactly this argument: KL II Proposition 6
(`Categorification.KLR.KL2.prop6`) exhibits `∑_{n even} 1_{…i^{(n)} j i^{(N-n)}…}` and
`∑_{n odd} 1_{…i^{(n)} j i^{(N-n)}…}` (`N = d + 1`) as equivalent idempotents via `α''`, `α'`,
whose blocks `α^±` have degrees equal to the differences of the grading shifts
(`serreAp_mem_grade`, `serreAm_mem_grade`); `kFamilyIso` turns this into an isomorphism of
direct sums in `U̇` (`Categorification.Diagrams.KL3.KaroubiKLR`).

## Conventions

The context `…` is a sequence `t ∈ Seq ν` with `t = …j i^N…` on the window `[p, p + N]` and
divided-power blocks `bs` away from the window (as in `Categorification.KLR.KL2.Serre`); the
summand for `n` is the 1-morphism `(E_{S n} 1_μ, ϕ(1_{…i^{(n)} j i^{(N-n)}…}))` with
`S n = …i^n j i^{N-n}…` (`serreSeq t p n`), shifted by
`c - ((n choose 2) + ((N - n) choose 2)) d_i`, where `c` is arbitrary (for KL III's objects,
`c` is the total shift `∑_{b ∈ bs} -(b choose 2) d_{i_b}` of the context blocks; the shifts
`-(n choose 2) d_i` and `-((N-n) choose 2) d_i` are those of `E_{+i^{(n)}}` and `E_{+i^{(N-n)}}`,
KL III (3.54)).

KL III (3.56) defines `E_i 1_λ := (E_î 1_λ, e_i)` for a divided-power sequence without writing
a grading shift; this conflicts with (3.54) for `i = (+i^{(m)})`, and without the shifts of
(3.54) the maps `α^±` are not of degree `0` (so the isomorphism of Proposition 3.24 could not hold
in `U̇`, whose 2-morphisms have degree `0`). We use the shifts of (3.54) for every divided power,
as above.

Only the first display (upward strands) is proved; the second (downward strands) needs
`ϕ_{-ν,λ}`, which is not constructed here.

## Main results

* `serreCorner`: the idempotent `1_{…i^{(n)} j i^{(N-n)}…}` as a `CornerIdem`.
* `prop324`: **KL III Proposition 3.24, first display**.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits StringDiagrams QuantumGroup UDot Presentation
  Categorification.GradedBicat KLR KLR.KLRAlgebra KLR.Diagram KLR.KL2

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k] [DecidableEq I]

/-! ## Arithmetic of the shifts -/

theorem two_mul_choose_two (n : ℕ) : (2 : ℤ) * ((n.choose 2 : ℕ) : ℤ) = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linear_combination ih

/-- The shift `-((n choose 2) + ((N - n) choose 2)) d` of `E_{…i^{(n)} j i^{(N-n)}…}` is
`d n (N - n) - (N choose 2) d`. -/
theorem serreShift_eq (d : ℤ) {n N : ℕ} (hn : n ≤ N) :
    -(((n.choose 2 : ℕ) : ℤ) + (((N - n).choose 2 : ℕ) : ℤ)) * d =
      d * ((n : ℤ) * ((N : ℤ) - n)) - ((N.choose 2 : ℕ) : ℤ) * d := by
  have hA := two_mul_choose_two n
  have hB := two_mul_choose_two (N - n)
  have hM := two_mul_choose_two N
  have hc : ((N - n : ℕ) : ℤ) = (N : ℤ) - n := by omega
  rw [hc] at hB
  apply mul_left_cancel₀ (two_ne_zero' ℤ)
  linear_combination (-d) * hA + (-d) * hB + d * hM

section Serre

variable {ν : Multiset I} {t : Seq ν} {p N : ℕ} {bs : List (ℕ × ℕ)} {i j : I}
  (hpN : p + N < Multiset.card ν)
  (ht₀ : ∀ r : Fin (Multiset.card ν), (r : ℕ) = p → t.lbl r = j)
  (ht : ∀ r : Fin (Multiset.card ν), p < r → (r : ℕ) ≤ p + N → t.lbl r = i)
  (hb : IsBlocks t bs) (hbs : ∀ b ∈ bs, b.1 + b.2 ≤ p ∨ p + N + 1 ≤ b.1) (hij : i ≠ j)

include hpN ht₀ ht hb hbs hij

variable (C) in
/-- The idempotent `1_{…i^{(n)} j i^{(N-n)}…}` of the Serre relation, in the corner of the
sequence `S n = …i^n j i^{N-n}…`. -/
def serreCorner (n : ℕ) (hn : n ≤ N) : CornerIdem C k (serreSeq t p n) where
  f := serreIdem t p N bs n
  deg0 := serreIdem_mem_grade hpN ht₀ ht hb hbs hn
  idem := by
    have := serreIdem_mul_serreIdem (k := k) (C := C) hpN ht₀ ht hb hbs hn hn hij
    rwa [if_pos rfl] at this
  left := by
    rw [serreIdem, ← mul_assoc, ← (commute_blocksElt_e hpN ht₀ ht hb hbs hn).eq, mul_assoc,
      e_mul_etop hpN ht₀ ht hn]

omit hij in
theorem serreIdem_mul_serreAp' {n' m : ℕ} (hn' : n' ≤ N) (hij : i ≠ j) :
    (serreIdem t p N bs n' * serreAp t p N bs m : R2 k C ν) =
      if n' = m + 1 then serreAp t p N bs m else 0 := by
  split_ifs with h
  · subst h; exact serreIdem_mul_serreAp hpN ht₀ ht hb hbs m
  · by_cases hm : m + 1 ≤ N
    · rw [← serreIdem_mul_serreAp hpN ht₀ ht hb hbs m, ← mul_assoc,
        serreIdem_mul_serreIdem hpN ht₀ ht hb hbs hn' hm hij, if_neg h, zero_mul]
    · rw [serreAp_of_not hm, mul_zero]

omit hij in
theorem serreIdem_mul_serreAm' {n' m : ℕ} (hn' : n' ≤ N) (hij : i ≠ j) :
    (serreIdem t p N bs n' * serreAm t p N bs m : R2 k C ν) =
      if n' = m - 1 then serreAm t p N bs m else 0 := by
  split_ifs with h
  · subst h; exact serreIdem_mul_serreAm hpN ht₀ ht hb hbs m
  · by_cases hm : 1 ≤ m ∧ m ≤ N
    · rw [← serreIdem_mul_serreAm hpN ht₀ ht hb hbs m, ← mul_assoc,
        serreIdem_mul_serreIdem hpN ht₀ ht hb hbs hn' (by omega) hij, if_neg h, zero_mul]
    · rw [serreAm_of_not hm, mul_zero]

omit [DecidableEq I] hpN ht₀ ht hb hbs hij in
theorem degAp_eq (hij : i ≠ j) (hN : N = C.dij i j + 1) (c : ℤ) {m : ℕ} (hm : m + 1 ≤ N) :
    -((N - m - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j =
      (c - (((m.choose 2 : ℕ) : ℤ) + (((N - m).choose 2 : ℕ) : ℤ)) * di C i) -
        (c - ((((m + 1).choose 2 : ℕ) : ℤ) + (((N - (m + 1)).choose 2 : ℕ) : ℤ)) * di C i) := by
  have h1 := serreShift_eq (di C i) (show m ≤ N by omega)
  have h2 := serreShift_eq (di C i) hm
  rw [sub_eq_add_neg c, sub_eq_add_neg c, ← neg_mul, ← neg_mul, h1, h2]
  have hd := C.dij_mul hij
  have h3 := two_mul_di C i
  have hN' : (N : ℤ) = C.dij i j + 1 := by exact_mod_cast hN
  have e1 : ((N - m - 1 : ℕ) : ℤ) = N - m - 1 := by omega
  rw [← h3] at hd
  have hij' : C.dot i j = -(C.dij i j * di C i) := by linarith
  rw [e1, ← h3, hij', hN']
  push_cast
  ring

omit [DecidableEq I] hpN ht₀ ht hb hbs hij in
theorem degAm_eq (hij : i ≠ j) (hN : N = C.dij i j + 1) (c : ℤ) {m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ N) :
    -((m - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j =
      (c - (((m.choose 2 : ℕ) : ℤ) + (((N - m).choose 2 : ℕ) : ℤ)) * di C i) -
        (c - ((((m - 1).choose 2 : ℕ) : ℤ) + (((N - (m - 1)).choose 2 : ℕ) : ℤ)) * di C i) := by
  have h1 := serreShift_eq (di C i) hm
  have h2 := serreShift_eq (di C i) (show m - 1 ≤ N by omega)
  rw [sub_eq_add_neg c, sub_eq_add_neg c, ← neg_mul, ← neg_mul, h1, h2]
  have hd := C.dij_mul hij
  have h3 := two_mul_di C i
  have hN' : (N : ℤ) = C.dij i j + 1 := by exact_mod_cast hN
  have e1 : ((m - 1 : ℕ) : ℤ) = m - 1 := by omega
  rw [← h3] at hd
  have hij' : C.dot i j = -(C.dij i j * di C i) := by linarith
  rw [e1, ← h3, hij', hN']
  ring

/-- **KL III Proposition 3.24, first display** (upward strands): for `i ≠ j` and `N = d_ij + 1`,
in `U̇`,
`⊕_{n ≤ N even} (E_{S n} 1_μ, 1_{…i^{(n)} j i^{(N-n)}…}) {c - ((n choose 2) + ((N-n) choose 2)) d_i}
 ≅ ⊕_{n ≤ N odd} (E_{S n} 1_μ, 1_{…i^{(n)} j i^{(N-n)}…}) {c - ((n choose 2) + ((N-n) choose 2)) d_i}`,
i.e. `⊕_a E_{…+i^{(2a)} +j +i^{(d+1-2a)}…} 1_μ ≅ ⊕_a E_{…+i^{(2a+1)} +j +i^{(d-2a)}…} 1_μ`. -/
def prop324 (hN : N = C.dij i j + 1) (μ : X) (c : ℤ) :
    (⨁ fun n : {n // n ∈ serreEvens N} =>
        kobj RD μ (serreCorner C k hpN ht₀ ht hb hbs hij n.1 (mem_serreEvens.1 n.2).1)
          (c - (((n.1.choose 2 : ℕ) : ℤ) + (((N - n.1).choose 2 : ℕ) : ℤ)) * di C i)) ≅
      ⨁ fun n : {n // n ∈ serreOdds N} =>
        kobj RD μ (serreCorner C k hpN ht₀ ht hb hbs hij n.1 (mem_serreOdds.1 n.2).1)
          (c - (((n.1.choose 2 : ℕ) : ℤ) + (((N - n.1).choose 2 : ℕ) : ℤ)) * di C i) :=
  kFamilyIso (α := serreAlpha' t p N bs) (β := serreAlpha'' t p N bs) _ _ _ _
    (fun m m' h => by
      show serreIdem t p N bs m.1 * serreIdem t p N bs m'.1 = 0
      rw [serreIdem_mul_serreIdem hpN ht₀ ht hb hbs (mem_serreEvens.1 m.2).1
        (mem_serreEvens.1 m'.2).1 hij, if_neg (fun h' => h (Subtype.ext h'))])
    (fun n n' h => by
      show serreIdem t p N bs n.1 * serreIdem t p N bs n'.1 = 0
      rw [serreIdem_mul_serreIdem hpN ht₀ ht hb hbs (mem_serreOdds.1 n.2).1
        (mem_serreOdds.1 n'.2).1 hij, if_neg (fun h' => h (Subtype.ext h'))])
    (by
      have h6 := prop6 (k := k) hpN ht₀ ht hb hbs hij hN
      rw [serreEven, serreOdd, ← Finset.sum_coe_sort (serreEvens N),
        ← Finset.sum_coe_sort (serreOdds N)] at h6
      exact h6)
    (fun m n => by
      show serreIdem t p N bs n.1 * serreAlpha' t p N bs * serreIdem t p N bs m.1 ∈ _
      have hm := mem_serreEvens.1 m.2
      have hn := mem_serreOdds.1 n.2
      rw [mul_assoc, alpha'_mul_serreIdem hpN ht₀ ht hb hbs hij hm.1, if_pos m.2, mul_add,
        serreIdem_mul_serreAp' (k := k) hpN ht₀ ht hb hbs hn.1 hij,
        serreIdem_mul_serreAm' (k := k) hpN ht₀ ht hb hbs hn.1 hij]
      refine Submodule.add_mem _ ?_ ?_
      · split_ifs with h
        · by_cases hm1 : m.1 + 1 ≤ N
          · have := serreAp_mem_grade (k := k) (C := C) hpN ht₀ ht hb hbs hm1
            rwa [degAp_eq hij hN c hm1, ← h] at this
          · rw [serreAp_of_not hm1]; exact Submodule.zero_mem _
        · exact Submodule.zero_mem _
      · split_ifs with h
        · by_cases hm1 : 1 ≤ m.1
          · have := serreAm_mem_grade (k := k) (C := C) hpN ht₀ ht hb hbs hm1 hm.1
            rwa [degAm_eq hij hN c hm1 hm.1, ← h] at this
          · rw [serreAm_of_not (by omega)]; exact Submodule.zero_mem _
        · exact Submodule.zero_mem _)
    (fun n m => by
      show serreIdem t p N bs m.1 * serreAlpha'' t p N bs * serreIdem t p N bs n.1 ∈ _
      have hm := mem_serreEvens.1 m.2
      have hn := mem_serreOdds.1 n.2
      rw [mul_assoc, alpha''_mul_serreIdem hpN ht₀ ht hb hbs hij hn.1, if_pos n.2, mul_sub,
        serreIdem_mul_serreAp' (k := k) hpN ht₀ ht hb hbs hm.1 hij,
        serreIdem_mul_serreAm' (k := k) hpN ht₀ ht hb hbs hm.1 hij]
      refine Submodule.sub_mem _ ?_ ?_
      · split_ifs with h
        · by_cases hn1 : 1 ≤ n.1
          · have := serreAm_mem_grade (k := k) (C := C) hpN ht₀ ht hb hbs hn1 hn.1
            rwa [degAm_eq hij hN c hn1 hn.1, ← h] at this
          · rw [serreAm_of_not (by omega)]; exact Submodule.zero_mem _
        · exact Submodule.zero_mem _
      · split_ifs with h
        · by_cases hn1 : n.1 + 1 ≤ N
          · have := serreAp_mem_grade (k := k) (C := C) hpN ht₀ ht hb hbs hn1
            rwa [degAp_eq hij hN c hn1, ← h] at this
          · rw [serreAp_of_not hn1]; exact Submodule.zero_mem _
        · exact Submodule.zero_mem _)

end Serre

end Categorification.KL3.Diagram
