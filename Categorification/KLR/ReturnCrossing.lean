/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.InductionFree
import Categorification.TypeA.Inversions
import Categorification.TypeA.GapSort

/-!
# Crossings that every path back must undo

Let `j + 1 < m` and let `s` be a sequence with `ψ_j² e(s) = 0`, and write `s'' = s_j s`.
Suppose that every permutation `w` with `w s'' = t` has a right descent at `j`, i.e.
`w(j + 1) < w(j)`. Then every element of `e(t) R(μ) e(s'')` ends with a crossing at `j`, so
`e(t) r ψ_j e(s) = 0` for every `r ∈ R(μ)` (`KLRAlgebra.e_mul_mul_ψ_mul_e_eq_zero`).

This is the vanishing used in Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, §5.1, to let the tensor product algebra act on the induced model of a
standard module: when the two strands at `j` are red strands of distinct labels, `Q` vanishes on
them, and a black-strand diagram from `s_j s` to an ordered sequence `t` must recross them.
The proof uses the basis theorem with dots on top (`KLRAlgebra.lbasis`, KL I Thm 2.5) for a
choice of reduced words ending in `j` at every right descent at `j` (`TypeA.descentWord`).

A dot on a strand whose label occurs only once in `s` passes through crossings without
correction terms (`KLRAlgebra.ψw_mul_x_mul_e_of_unique`), so `r x_a e(s)` is a combination of
elements `e(t) x_b z` with a dot at the top of the same strand
(`KLRAlgebra.mul_x_mul_e_mem_span_of_unique`). In the same model this lets red dots, which vanish
at the top, vanish everywhere.
-/

namespace Categorification

open Equiv MvPolynomial

namespace TypeA

variable {m j : ℕ} (hj : j + 1 < m)

/-- Reduced words for the permutations of `Fin m` that end in `j` whenever `w` has a right
descent at `j`. -/
noncomputable def descentWord (w : Perm (Fin m)) : List ℕ :=
  if w ⟨j + 1, hj⟩ < w ⟨j, Nat.lt_of_succ_lt hj⟩ then
    (exists_reduced m (w * sadj m j)).choose ++ [j]
  else (exists_reduced m w).choose

theorem descentWord_spec (w : Perm (Fin m)) :
    IsReduced m (descentWord hj w) ∧ wordProd m (descentWord hj w) = w := by
  unfold descentWord
  split_ifs with h
  · obtain ⟨h1, h2⟩ := (exists_reduced m (w * sadj m j)).choose_spec
    have hw : wordProd m ((exists_reduced m (w * sadj m j)).choose ++ [j]) = w := by
      rw [wordProd_append, h2, wordProd_singleton, mul_assoc, sadj_mul_self, mul_one]
    have hj1 : IsReduced m [j] :=
      ⟨by simp [ValidWord]; omega, by rw [wordProd_singleton, length_sadj hj]; rfl⟩
    refine ⟨h1.append_of_length_eq hj1 ?_, hw⟩
    rw [hw, h2, wordProd_singleton, length_sadj hj, length_mul_sadj_of_gt hj h]
  · exact (exists_reduced m w).choose_spec

theorem exists_descentWord_eq_append (w : Perm (Fin m))
    (h : w ⟨j + 1, hj⟩ < w ⟨j, Nat.lt_of_succ_lt hj⟩) :
    ∃ α, descentWord hj w = α ++ [j] := by
  simp only [descentWord, h, ite_true]
  exact ⟨_, rfl⟩

end TypeA

namespace KLR

open TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {μ : Multiset I}

namespace KLRAlgebra

local notation "m" => Multiset.card μ

/-- **Return crossings vanish.** If `ψ_j² e(s) = 0` and every `w` with `w (s_j s) = t` has a
right descent at `j`, then `e(t) r ψ_j e(s) = 0` for all `r`. -/
theorem e_mul_mul_ψ_mul_e_eq_zero (hsym : KLRSymm Q) {j : ℕ} (hj : j + 1 < m) {s t : Seq μ}
    (hsq : (ψ j * ψ j * e s : KLRAlgebra k Q μ) = 0)
    (hdesc : ∀ w : Perm (Fin m), w • (sadj m j • s) = t →
      w ⟨j + 1, hj⟩ < w ⟨j, Nat.lt_of_succ_lt hj⟩)
    (r : KLRAlgebra k Q μ) : e t * r * ψ j * e s = 0 := by
  set B := lbasis hsym (descentWord hj) (descentWord_spec hj)
  let L : KLRAlgebra k Q μ →ₗ[k] KLRAlgebra k Q μ :=
    (LinearMap.mulRight k (ψ j * e s)).comp (LinearMap.mulLeft k (e t))
  have hL : ∀ y, L y = e t * y * ψ j * e s := fun y => by
    simp [L, mul_assoc]
  have hB : L = 0 := by
    refine B.ext fun b => ?_
    obtain ⟨s', w, d⟩ := b
    rw [hL, LinearMap.zero_apply, lbasis_apply, mul_assoc (e t * _), ψ_mul_e, ← mul_assoc]
    simp only
    rw [mul_assoc (e t), mul_assoc _ (e s'), e_mul_e]
    split_ifs with hs
    · subst hs
      by_cases ht : w • (sadj m j • s) = t
      · obtain ⟨α, hα⟩ := exists_descentWord_eq_append hj w (hdesc w ht)
        have hψ : (e (sadj m j • s) * ψ j : KLRAlgebra k Q μ) = ψ j * e s :=
          (ψ_mul_e j s).symm
        rw [hα, ψw_append, ψw_cons, ψw_nil, mul_one]
        calc (e t * (pol (monomial d (1 : k)) * (ψw α * ψ j) * e (sadj m j • s)) * ψ j :
              KLRAlgebra k Q μ)
            = e t * (pol (monomial d 1) * ψw α) * (ψ j * (e (sadj m j • s) * ψ j)) := by
              noncomm_ring
          _ = 0 := by rw [hψ, ← mul_assoc (ψ j), hsq, mul_zero]
      · rw [← e_mul_pol_ψw_e, (descentWord_spec hj w).2, ← mul_assoc, e_mul_e,
          ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm ht)), zero_mul, zero_mul]
    · simp
  have := congrArg (fun f => f r) hB
  simpa [hL] using this


/-! ### Dots on a strand with a unique label -/

/-- A dot on a strand whose label occurs only once slides through a crossing without
correction terms: `ψ_j x_a e(i) = x_{s_j a} ψ_j e(i)`. -/
theorem ψ_mul_x_mul_e_of_unique (j : ℕ) {a : Fin m} {i : Seq μ}
    (hu : ∀ b, i.lbl b = i.lbl a → b = a) :
    (ψ j * x a * e i : KLRAlgebra k Q μ) = x (sadj m j a) * ψ j * e i := by
  by_cases h : j + 1 < m
  · by_cases ha : a.val = j
    · obtain ⟨a, ha0⟩ := a
      simp only at ha
      subst ha
      rw [sadj_apply_left h]
      have hne : i.lbl ⟨a, ha0⟩ ≠ i.lbl ⟨a + 1, h⟩ := fun hl => by
        have := hu _ hl.symm
        simp [Fin.ext_iff] at this
      have := dot_cross_right (Q := Q) a h i
      rw [ite_eq_right_of_eq_false _ _ (eq_false hne), sub_mul, sub_eq_zero] at this
      exact this
    by_cases ha' : a.val = j + 1
    · obtain ⟨a, ha0⟩ := a
      simp only at ha'
      subst ha'
      rw [sadj_apply_right h]
      have hne : i.lbl ⟨j, by omega⟩ ≠ i.lbl ⟨j + 1, h⟩ := fun hl => by
        have := hu _ hl
        simp [Fin.ext_iff] at this
      have := dot_cross_left (Q := Q) j h i
      rw [ite_eq_right_of_eq_false _ _ (eq_false hne), sub_mul, sub_eq_zero] at this
      exact this.symm
    · rw [sadj_apply_of_ne a ha ha', x_mul_ψ a j ha ha']
  · rw [ψ_eq_zero j (by omega), zero_mul, mul_zero, zero_mul]

/-- A dot on a strand whose label occurs only once slides through a product of crossings:
`ψ_σ x_a e(i) = x_{w a} ψ_σ e(i)`, `w = wordProd σ`. -/
theorem ψw_mul_x_mul_e_of_unique (σ : List ℕ) {a : Fin m} {i : Seq μ}
    (hu : ∀ b, i.lbl b = i.lbl a → b = a) :
    (ψw σ * x a * e i : KLRAlgebra k Q μ) = x (wordProd m σ a) * ψw σ * e i := by
  induction σ with
  | nil => simp [wordProd]
  | cons j σ ih =>
    have hu' : ∀ b, (wordProd m σ • i).lbl b = (wordProd m σ • i).lbl (wordProd m σ a) →
        b = wordProd m σ a := fun b hb => by
      change i.1 ((wordProd m σ).symm b) = i.1 ((wordProd m σ).symm (wordProd m σ a)) at hb
      rw [Equiv.symm_apply_apply] at hb
      rw [← hu _ hb, Equiv.apply_symm_apply]
    calc (ψw (j :: σ) * x a * e i : KLRAlgebra k Q μ)
        = ψ j * (ψw σ * x a * e i) := by rw [ψw_cons]; noncomm_ring
      _ = ψ j * x (wordProd m σ a) * e (wordProd m σ • i) * ψw σ := by
          rw [ih, mul_assoc _ (ψw σ), ψw_mul_e]; noncomm_ring
      _ = x (wordProd m (j :: σ) a) * ψw (j :: σ) * e i := by
          rw [ψ_mul_x_mul_e_of_unique j hu', mul_assoc _ (e _), ← ψw_mul_e, wordProd_cons,
            Perm.mul_apply, ψw_cons]
          noncomm_ring

/-- A dot at the bottom of a strand whose label occurs only once moves to the top of the
diagram: `r x_a e(s)` is a combination of elements `e(t) x_b z` with `t_b = s_a`. -/
theorem mul_x_mul_e_mem_span_of_unique (hsym : KLRSymm Q) (r : KLRAlgebra k Q μ) {a : Fin m}
    {s : Seq μ} (hu : ∀ b, s.lbl b = s.lbl a → b = a) :
    r * x a * e s ∈ Submodule.span k
      {y | ∃ (t : Seq μ) (b : Fin m) (z : KLRAlgebra k Q μ),
        t.lbl b = s.lbl a ∧ y = e t * x b * z} := by
  set ρ : Perm (Fin m) → List ℕ := fun w => (exists_reduced m w).choose
  have hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w :=
    fun w => (exists_reduced m w).choose_spec
  set B := lbasis hsym ρ hρ
  have hr : r ∈ Submodule.span k (Set.range B) := by rw [B.span_eq]; trivial
  induction hr using Submodule.span_induction with
  | zero => simp
  | add u v _ _ hu' hv' => rw [add_mul, add_mul]; exact Submodule.add_mem _ hu' hv'
  | smul c u _ hu' => rw [smul_mul_assoc, smul_mul_assoc]; exact Submodule.smul_mem _ c hu'
  | mem u hu' =>
    obtain ⟨⟨s', w, d⟩, rfl⟩ := hu'
    rw [lbasis_apply, mul_assoc _ (x a), x_mul_e, ← mul_assoc, mul_assoc _ (e s'), e_mul_e]
    simp only
    split_ifs with hs
    · subst hs
      have hw := (hρ w).2
      have key : (pol (monomial d (1 : k)) * ψw (ρ w) * e s' * x a : KLRAlgebra k Q μ) =
          e (w • s') * x (w a) * (pol (monomial d 1) * ψw (ρ w) * e s') := by
        calc (pol (monomial d (1 : k)) * ψw (ρ w) * e s' * x a : KLRAlgebra k Q μ)
            = pol (monomial d 1) * (ψw (ρ w) * x a * e s') := by
              rw [mul_assoc _ (e s'), ← x_mul_e]; noncomm_ring
          _ = pol (monomial d 1) * x (w a) * (ψw (ρ w) * e s') := by
              rw [ψw_mul_x_mul_e_of_unique _ hu, hw]; noncomm_ring
          _ = x (w a) * (pol (monomial d 1) * ψw (ρ w) * e s') := by
              rw [← pol_X, ← map_mul, mul_comm, map_mul]; noncomm_ring
          _ = e (w • s') * x (w a) * (pol (monomial d 1) * ψw (ρ w) * e s') := by
              have he := e_mul_pol_ψw_e (Q := Q) (monomial d (1 : k)) (ρ w) s'
              rw [hw] at he
              rw [← x_mul_e, mul_assoc (x _), he]
      rw [key]
      exact Submodule.subset_span ⟨w • s', w a, _, by simp [Seq.lbl], rfl⟩
    · simp

end KLRAlgebra

end KLR

end Categorification
