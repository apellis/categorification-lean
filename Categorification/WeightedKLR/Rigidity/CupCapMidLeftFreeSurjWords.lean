/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.SpanCornerDotsTop

/-!
# Descents and the crossing filtration

Word combinatorics for the surjectivity of the comparison map over the block shuffles
(Webster, arXiv:1309.3796v3, §7.3, a cap after `λ_j`), stated for an arbitrary KLR algebra
`R(ν)` over a commutative ring and arbitrary data `Q`, following the spanning half of
KL I, Theorem 2.5 (arXiv:0803.4121v2, §2.3).

## Main results

* `KLRAlgebra.hflip_mem_filt`: the horizontal flip preserves the crossing filtration.
* `KLRAlgebra.mem_span_dotsTop_of_mem_filt`: the filtration step `filt n` is spanned by the
  elements `x^u ψ_{ρ w} e(i)` with dots on top and `length w ≤ n`.
* `KLRAlgebra.ψw_sub_ψ_mul_mem_filt`: at a left descent `a` of `w`,
  `ψ_{ρ w} y ≡ ψ_a ψ_{ρ (s_a w)} y` modulo lower filtration degree.
* `KLRAlgebra.exists_ψw_range_sub_mem_filt`: a strand that crosses the `K` strands to its right
  at the top splits off as `ψ_c ψ_{c+1} ⋯ ψ_{c+K-1}`, modulo lower filtration degree.
* `TypeA.exists_lt_of_not_strictMono`: an injective sequence that is not increasing has an
  adjacent descent.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "𝓕" => filt k Q ν

/-- The horizontal flip preserves each step of the crossing filtration. -/
theorem hflip_mem_filt {n : ℕ} {r : KLRAlgebra k Q ν} (hr : r ∈ 𝓕 n) : hflip r ∈ 𝓕 n := by
  induction hr using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ρ, p, i, hv, hl, rfl⟩ := hy
    rw [hflip_mul, hflip_mul, hflip_e, hflip_pol, hflip_ψw]
    rw [← mul_assoc, (e_commute_pol i p).eq, mul_assoc, e_mul_ψw]
    have h := mem_filt (Q := Q) (validWord_reverse.2 hv) (n := n) (by simpa using hl) 1
      ((wordProd m ρ.reverse)⁻¹ • i)
    rw [map_one, mul_one] at h
    exact pol_mul_mem p h
  | zero => rw [hflip_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [hflip_add]; exact add_mem h h'
  | smul c y _ h => rw [hflip_smul]; exact Submodule.smul_mem _ c h

variable (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (hρ : ∀ w : Perm (Fin (Multiset.card ν)),
    IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)

include hρ in
/-- **KL I, Theorem 2.5 (spanning, filtered), dots on top**: for any choice of reduced words
`ρ w`, the filtration step `filt n` lies in the span of the elements `x^u ψ_{ρ w} e(i)` with
`length w ≤ n`. -/
theorem mem_span_dotsTop_of_mem_filt {n : ℕ} {r : KLRAlgebra k Q ν} (hr : r ∈ 𝓕 n) :
    r ∈ Submodule.span k {b : KLRAlgebra k Q ν | ∃ (w : Perm (Fin m)) (u : Fin m →₀ ℕ)
      (i : Seq ν), length m w ≤ n ∧ pol (monomial u 1) * ψw (ρ w) * e i = b} := by
  have h := hflip_mem_filt hr
  rw [filt_eq_span (fun _ _ => TypeA.braidEquiv_of_isReduced)
    (fun _ => TypeA.exists_braidEquiv_hasRepeat_of_not_isReduced) (revWord ρ)
    (revWord_spec ρ hρ) n] at h
  have himg := Submodule.mem_map_of_mem (f := (hflipEquiv k Q ν).toLinearMap) h
  rw [Submodule.map_span] at himg
  simp only [LinearEquiv.coe_coe, hflipEquiv_apply, hflip_hflip] at himg
  refine Submodule.span_mono ?_ himg
  rintro _ ⟨_, ⟨w, u, i, hw, rfl⟩, rfl⟩
  refine ⟨w⁻¹, u, w • i, by rwa [length_inv], ?_⟩
  rw [hflipEquiv_apply, hflip_mul, hflip_mul, hflip_e, hflip_pol, hflip_ψw, revWord,
    List.reverse_reverse, ← mul_assoc (e i), (e_commute_pol _ _).eq, mul_assoc (pol _) (e i),
    e_mul_ψw, (hρ _).2, inv_inv, mul_assoc]

include hρ in
/-- **A left descent splits off**: if the strands at the top positions `a` and `a + 1` of `w`
cross (`w⁻¹ (a + 1) < w⁻¹ a`), then `ψ_{ρ w} y ≡ ψ_a ψ_{ρ (s_a w)} y` modulo terms of lower
filtration degree. -/
theorem ψw_sub_ψ_mul_mem_filt {w : Perm (Fin m)} {a : ℕ} (ha : a + 1 < m)
    (hgt : w⁻¹ ⟨a + 1, ha⟩ < w⁻¹ ⟨a, by omega⟩) {n : ℕ} {y : KLRAlgebra k Q ν}
    (hy : y ∈ 𝓕 n) :
    ψw (ρ w) * y - ψ a * (ψw (ρ (sadj m a * w)) * y) ∈ 𝓕 (length m w - 1 + n) := by
  have hl := length_sadj_mul_of_gt ha hgt
  have hw : wordProd m (a :: ρ (sadj m a * w)) = w := by
    rw [wordProd_cons', (hρ _).2, ← mul_assoc, sadj_mul_self, one_mul]
  have hred : IsReduced m (a :: ρ (sadj m a * w)) := by
    refine ⟨validWord_cons.2 ⟨ha, (hρ _).1.1⟩, ?_⟩
    rw [hw, List.length_cons, (hρ _).1.length_eq, (hρ _).2, hl]
  have h := sub_mem_of_braidEquiv (braidEquiv_of_isReduced (hρ w).1 hred
    (by rw [(hρ w).2, hw])) hy
  rwa [ψw_cons, mul_assoc, (hρ w).1.length_eq, (hρ w).2] at h

include hρ in
/-- **A strand crossing a block on its right splits off**: if the strand at the top position `c`
of `u` crosses each of the `K` strands at the top positions `c + 1, …, c + K`, then
`ψ_{ρ u} y ≡ ψ_c ψ_{c+1} ⋯ ψ_{c+K-1} ψ_{ρ u'} y` modulo terms of lower filtration degree, for a
permutation `u'` of length `length u - K`. -/
theorem exists_ψw_range_sub_mem_filt : ∀ (K c : ℕ) (u : Perm (Fin m)) (hK : c + K < m),
    (∀ q (hq : q < K), u⁻¹ ⟨c + 1 + q, by omega⟩ < u⁻¹ ⟨c, by omega⟩) →
    ∀ {n : ℕ} {y : KLRAlgebra k Q ν}, y ∈ 𝓕 n →
    ∃ u' : Perm (Fin m), length m u' + K = length m u ∧
      ψw (ρ u) * y - ψw (List.range' c K) * (ψw (ρ u') * y) ∈ 𝓕 (length m u - 1 + n)
  | 0, c, u, _, _, n, y, _ => ⟨u, rfl, by simp⟩
  | K + 1, c, u, hK, hinv, n, y, hy => by
    have hc : c + 1 < m := by omega
    have h0 := hinv 0 (by omega)
    simp only [add_zero] at h0
    have hd := ψw_sub_ψ_mul_mem_filt ρ hρ hc h0 hy
    have hl := length_sadj_mul_of_gt hc h0
    set u₂ := sadj m c * u
    by_cases hK0 : K = 0
    · subst hK0
      refine ⟨u₂, by omega, ?_⟩
      simpa [List.range'_succ] using hd
    have hinv' : ∀ q (hq : q < K), u₂⁻¹ ⟨c + 1 + 1 + q, by omega⟩ < u₂⁻¹ ⟨c + 1, by omega⟩ := by
      intro q hq
      have h := hinv (q + 1) (by omega)
      rw [show u₂⁻¹ = u⁻¹ * sadj m c by simp [u₂], Perm.mul_apply, Perm.mul_apply]
      rw [sadj_apply_of_ne _ (by simp; omega) (by simp; omega), sadj_apply_right hc]
      convert h using 3
      all_goals omega
    obtain ⟨u', hu', hd'⟩ := exists_ψw_range_sub_mem_filt K (c + 1) u₂ (by omega) hinv' hy
    refine ⟨u', by omega, ?_⟩
    have h2 := ψ_mul_mem c hd'
    have : ψw (ρ u) * y - ψw (List.range' c (K + 1)) * (ψw (ρ u') * y) =
        (ψw (ρ u) * y - ψ c * (ψw (ρ u₂) * y)) +
          ψ c * (ψw (ρ u₂) * y - ψw (List.range' (c + 1) K) * (ψw (ρ u') * y)) := by
      rw [List.range'_succ, ψw_cons, mul_sub, mul_assoc]; abel
    rw [this]
    exact add_mem hd (filt_mono (by omega) h2)

end KLRAlgebra

end Categorification.KLR

namespace Categorification.TypeA

/-- An injective sequence that is not strictly increasing has an adjacent descent. -/
theorem exists_lt_of_not_strictMono {α : Type*} [LinearOrder α] {n : ℕ} {f : Fin n → α}
    (hf : Function.Injective f) (h : ¬ StrictMono f) :
    ∃ q, ∃ hq : q + 1 < n, f ⟨q + 1, hq⟩ < f ⟨q, by omega⟩ := by
  by_contra hc
  push Not at hc
  apply h
  cases n with
  | zero => exact fun a => a.elim0
  | succ n =>
    refine Fin.strictMono_iff_lt_succ.2 fun q => lt_of_le_of_ne ?_ ?_
    · exact hc q.val (by omega)
    · exact fun he => (Fin.castSucc_lt_succ (i := q)).ne (hf he)

end Categorification.TypeA
