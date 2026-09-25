/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Filtration
import Categorification.TypeA.Matsumoto

/-!
# Spanning set of `R(ν)`

The spanning half of KL I, Theorem 2.5 (arXiv:0803.4121v2, §2.3): for any choice of
reduced words `ρ w` (`w ∈ S_m`), the elements `ψ_{ρ w} x^u e_i` span `R(ν)` over `k`,
and those with `w • i = j` span the corner `e_j R(ν) e_i`. Here `ψ_{ρ w} x^u e_i` is
`ψw (ρ w) * pol (monomial u 1) * e i`.

The proof is by induction on the crossing filtration `KLRAlgebra.filt`: a valid word `σ` is
either reduced, hence (Matsumoto) braid-equivalent to `ρ (wordProd σ)`, or braid-equivalent
to a word with a repeated letter; in both cases `KLRAlgebra.sub_mem_of_braidEquiv` and
`KLRAlgebra.mul_mem_of_hasRepeat` reduce to lower filtration degree.

The two combinatorial inputs — Matsumoto's theorem and the fact that a non-reduced valid
word is braid-equivalent to a word with a repeated letter — are taken as explicit
hypotheses `hMats` and `hRep` here; they are statements about words only, independent of
`R(ν)`.

## Main results

* `KLRAlgebra.filt_eq_span` : `filt k Q ν n` is spanned by the `ψ_{ρ w} x^u e_i` with
  `length w ≤ n`.
* `KLRAlgebra.span_eq_top` : the `ψ_{ρ w} x^u e_i` span `R(ν)`.
* `KLRAlgebra.mem_span_corner` : an element `r` with `e j * r * e i = r` is a `k`-linear
  combination of the `ψ_{ρ w} x^u e_i` with `w • i = j`.

All results hold over an arbitrary commutative ring `k` and arbitrary data `Q`.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "𝓕" => filt k Q ν

private theorem length_one_eq_zero (n : ℕ) : length n 1 = 0 := by
  unfold length
  classical
  exact Nat.eq_zero_of_le_zero
    (Nat.find_min' _ ⟨[], by simp [ValidWord], by simp [wordProd], rfl⟩)

/- The combinatorial hypotheses: Matsumoto's theorem and reduction of non-reduced words to
words with a repeated letter (both for words in `S_m`, `m = card ν`), and a choice of a
reduced word `ρ w` for every `w ∈ S_m`. -/
variable
  (hMats : ∀ ρ σ : List ℕ, IsReduced (Multiset.card ν) ρ → IsReduced (Multiset.card ν) σ →
    wordProd (Multiset.card ν) ρ = wordProd (Multiset.card ν) σ → BraidEquiv ρ σ)
  (hRep : ∀ ρ : List ℕ, ValidWord (Multiset.card ν) ρ → ¬ IsReduced (Multiset.card ν) ρ →
    ∃ σ, BraidEquiv ρ σ ∧ HasRepeat σ)

variable (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (hρ : ∀ w : Perm (Fin (Multiset.card ν)),
    IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)

include hρ in
/-- The chosen spanning elements with `length w ≤ n` lie in `filt k Q ν n`. -/
theorem span_le_filt (n : ℕ) :
    Submodule.span k {r : KLRAlgebra k Q ν | ∃ (w : Perm (Fin m)) (u : Fin m →₀ ℕ)
      (i : Seq ν), length m w ≤ n ∧ ψw (ρ w) * pol (monomial u 1) * e i = r} ≤ 𝓕 n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨w, u, i, hw, rfl⟩
  refine mem_filt (hρ w).1.1 ?_ _ i
  rw [(hρ w).1.2, (hρ w).2]
  exact hw

include hMats hRep hρ in
/-- `filt k Q ν n` is contained in the span of the chosen spanning elements with
`length w ≤ n`. -/
theorem filt_le_span (n : ℕ) :
    𝓕 n ≤ Submodule.span k {r : KLRAlgebra k Q ν | ∃ (w : Perm (Fin m)) (u : Fin m →₀ ℕ)
      (i : Seq ν), length m w ≤ n ∧ ψw (ρ w) * pol (monomial u 1) * e i = r} := by
  set B : ℕ → Submodule k (KLRAlgebra k Q ν) := fun n => Submodule.span k
    {r | ∃ (w : Perm (Fin m)) (u : Fin m →₀ ℕ) (i : Seq ν),
      length m w ≤ n ∧ ψw (ρ w) * pol (monomial u 1) * e i = r} with hB
  have Bmono : ∀ {a b}, a ≤ b → B a ≤ B b := fun hab => Submodule.span_mono
    fun _ ⟨w, u, i, hw, hr⟩ => ⟨w, u, i, hw.trans hab, hr⟩
  have basis_mem : ∀ w u i n, length m w ≤ n →
      ψw (ρ w) * (pol (monomial u 1) * e i) ∈ B n := fun w u i n hw =>
    Submodule.subset_span ⟨w, u, i, hw, by rw [mul_assoc]⟩
  show 𝓕 n ≤ B n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  refine Submodule.span_le.2 ?_
  rintro _ ⟨σ, p, i, hv, hl, rfl⟩
  suffices H : ∀ u, ψw σ * pol (monomial u 1) * e i ∈ B n by
    induction p using MvPolynomial.induction_on' with
    | monomial u c =>
      rw [show monomial u c = c • monomial u (1 : k) by rw [smul_monomial, smul_eq_mul, mul_one],
        map_smul, mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ c (H u)
    | add p q hp hq => rw [map_add, mul_add, add_mul]; exact add_mem hp hq
  intro u
  have hy : (pol (monomial u 1) * e i : KLRAlgebra k Q ν) ∈ 𝓕 0 := pol_mul_e_mem _ i 0
  rw [mul_assoc]
  set y := (pol (monomial u 1) * e i : KLRAlgebra k Q ν)
  rcases n with _ | n
  · -- `σ` is the empty word, and so is `ρ 1`.
    have hσ : σ = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h1 : ρ 1 = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [(hρ 1).1.2, (hρ 1).2, length_one_eq_zero]
    have := basis_mem 1 u i 0 (by rw [length_one_eq_zero])
    rw [h1] at this
    rw [hσ]
    exact this
  -- It suffices to show membership in `𝓕 n`.
  suffices H : ψw σ * y ∈ 𝓕 n ∨ ∃ w, length m w ≤ n + 1 ∧ ψw σ * y - ψw (ρ w) * y ∈ 𝓕 n by
    rcases H with H | ⟨w, hw, H⟩
    · exact Bmono (Nat.le_succ n) (ih n (Nat.lt_succ_self n) H)
    · have := add_mem (Bmono (Nat.le_succ n) (ih n (Nat.lt_succ_self n) H))
        (basis_mem w u i (n + 1) hw)
      rwa [sub_add_cancel] at this
  by_cases hle : σ.length ≤ n
  · left
    rw [← mul_assoc]
    exact mem_filt hv hle _ i
  have hlen : σ.length = n + 1 := by omega
  by_cases hred : IsReduced m σ
  · -- Matsumoto: `σ` is braid-equivalent to the chosen reduced word.
    right
    refine ⟨wordProd m σ, ?_, ?_⟩
    · rw [← hred.2]; exact hl
    · have hE := hMats σ (ρ (wordProd m σ)) hred (hρ _).1 (hρ _).2.symm
      have := sub_mem_of_braidEquiv hE hy
      rwa [hlen, Nat.add_sub_cancel, Nat.add_zero] at this
  · -- A non-reduced word is braid-equivalent to one with a repeated letter.
    left
    obtain ⟨τ, hE, hrep⟩ := hRep σ hv hred
    have h₁ := sub_mem_of_braidEquiv hE hy
    have h₂ := mul_mem_of_hasRepeat hrep hy
    rw [← length_eq_of_braidEquiv hE] at h₂
    rw [hlen, Nat.add_sub_cancel, Nat.add_zero] at h₁ h₂
    have := add_mem h₁ h₂
    rwa [sub_add_cancel] at this

include hMats hRep hρ in
/-- **KL I, Theorem 2.5 (spanning, filtered).** For any choice of reduced words `ρ w`, the
crossing filtration step `filt k Q ν n` is spanned by the elements `ψ_{ρ w} x^u e_i` with
`length w ≤ n`. -/
theorem filt_eq_span (n : ℕ) :
    𝓕 n = Submodule.span k {r : KLRAlgebra k Q ν | ∃ (w : Perm (Fin m)) (u : Fin m →₀ ℕ)
      (i : Seq ν), length m w ≤ n ∧ ψw (ρ w) * pol (monomial u 1) * e i = r} :=
  le_antisymm (filt_le_span hMats hRep ρ hρ n) (span_le_filt ρ hρ n)

include hMats hRep hρ in
/-- **KL I, Theorem 2.5 (spanning).** For any choice of reduced words `ρ w`, the elements
`ψ_{ρ w} x^u e_i` (`w ∈ S_m`, `u ∈ ℕ^m`, `i ∈ Seq ν`) span `R(ν)` over `k`. -/
theorem span_eq_top :
    Submodule.span k {r : KLRAlgebra k Q ν | ∃ (w : Perm (Fin m)) (u : Fin m →₀ ℕ)
      (i : Seq ν), ψw (ρ w) * pol (monomial u 1) * e i = r} = ⊤ := by
  refine eq_top_iff.2 fun r _ => ?_
  obtain ⟨n, hn⟩ := exists_mem_filt r
  rw [filt_eq_span hMats hRep ρ hρ n] at hn
  refine Submodule.span_mono ?_ hn
  rintro _ ⟨w, u, i, _, hr⟩
  exact ⟨w, u, i, hr⟩

include hMats hRep hρ in
/-- **KL I, Theorem 2.5 (spanning, corners).** For any choice of reduced words `ρ w`, every
`r ∈ e_j R(ν) e_i` (i.e. `e j * r * e i = r`) is a `k`-linear combination of the elements
`ψ_{ρ w} x^u e_i` with `w • i = j`. -/
theorem mem_span_corner (i j : Seq ν) {r : KLRAlgebra k Q ν} (hr : e j * r * e i = r) :
    r ∈ Submodule.span k {b : KLRAlgebra k Q ν | ∃ (w : Perm (Fin m)) (u : Fin m →₀ ℕ),
      w • i = j ∧ ψw (ρ w) * pol (monomial u 1) * e i = b} := by
  set C := Submodule.span k {b : KLRAlgebra k Q ν | ∃ (w : Perm (Fin m)) (u : Fin m →₀ ℕ),
      w • i = j ∧ ψw (ρ w) * pol (monomial u 1) * e i = b}
  let L : KLRAlgebra k Q ν →ₗ[k] KLRAlgebra k Q ν :=
    (LinearMap.mulLeft k (e j)).comp (LinearMap.mulRight k (e i))
  have hle : Submodule.span k {r : KLRAlgebra k Q ν | ∃ (w : Perm (Fin m))
      (u : Fin m →₀ ℕ) (i : Seq ν), ψw (ρ w) * pol (monomial u 1) * e i = r} ≤
      C.comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, u, i', rfl⟩
    show e j * (ψw (ρ w) * pol (monomial u 1) * e i' * e i) ∈ C
    rw [gen_mul_e]
    split_ifs with h
    · subst h
      rw [e_mul_gen, (hρ w).2]
      split_ifs with h'
      · exact Submodule.subset_span ⟨w, u, by rw [← h', smul_inv_smul], rfl⟩
      · exact zero_mem _
    · rw [mul_zero]; exact zero_mem _
  have hmem : L r ∈ C := hle (by rw [span_eq_top hMats hRep ρ hρ]; trivial)
  rw [← hr, mul_assoc]
  exact hmem

/-! ### Unconditional forms

The combinatorial hypotheses are discharged by Matsumoto's theorem for `S_m`
(`TypeA.braidEquiv_of_isReduced`) and `TypeA.exists_braidEquiv_hasRepeat_of_not_isReduced`. -/

section Unconditional

include hρ in
/-- **KL I, Theorem 2.5 (spanning), unconditional.** -/
theorem span_eq_top' :
    Submodule.span k {r : KLRAlgebra k Q ν | ∃ (w : Perm (Fin m)) (u : Fin m →₀ ℕ)
      (i : Seq ν), ψw (ρ w) * pol (monomial u 1) * e i = r} = ⊤ :=
  span_eq_top (fun _ _ => TypeA.braidEquiv_of_isReduced)
    (fun _ => TypeA.exists_braidEquiv_hasRepeat_of_not_isReduced) ρ hρ

include hρ in
/-- **KL I, Theorem 2.5 (spanning of `_jR(ν)_i`), unconditional.** -/
theorem mem_span_corner' (i j : Seq ν) {r : KLRAlgebra k Q ν} (hr : e j * r * e i = r) :
    r ∈ Submodule.span k {b : KLRAlgebra k Q ν | ∃ (w : Perm (Fin m)) (u : Fin m →₀ ℕ),
      w • i = j ∧ ψw (ρ w) * pol (monomial u 1) * e i = b} :=
  mem_span_corner (fun _ _ => TypeA.braidEquiv_of_isReduced)
    (fun _ => TypeA.exists_braidEquiv_hasRepeat_of_not_isReduced) ρ hρ i j hr

end Unconditional

end KLRAlgebra

end Categorification.KLR
