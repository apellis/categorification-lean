/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicProjective

/-!
# The mirror coset decomposition `R(n + 1) = ∑_a R(n, 1) τ_n ⋯ τ_a`

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4: the proofs of Proposition 3.4
(`R(n) ⊗_{R(n-1)} R(n) ⊕ R(n, 1) ≅ R(n + 1)`) and of Theorem 5.1 use
`R(n + 1) = ∑_{a = 1}^{n + 1} R(n, 1) τ_n ⋯ τ_a`, the mirror image of the decomposition
`R(n + 1) = ∑_a (k[x_1] ⊗ R^1(n)) τ_1 ⋯ τ_a` (`spTau_eq_top`). We deduce it from `spTau_eq_top`
by the vertical flip `σ` (`KLRAlgebra.sigma`, which needs the symmetry `KLRSymm Q`):

* `sigma_mem_subR0`: `σ(k[x_1] ⊗ R^1(β)) ⊆ R(β) ⊗ k[x_m]`;
* `sigma_tauProd`: `σ(ψ_0 ⋯ ψ_{a-1}) = δ ψ_{n-1} ⋯ ψ_{n-a}` with `δ` a combination of idempotents;
* `spTauR_eq_top`: `R(ν) = ∑_{a ≤ n} (R(β) ⊗ k[x_m]) ψ_{n-1} ⋯ ψ_{n-a}` (zero-indexed, `m = n + 1`).
-/

namespace Categorification.KLR

open Equiv TypeA PolyRep

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

/-- `ψ_{n-1} ψ_{n-2} ⋯ ψ_{n-a}`. -/
noncomputable def tauRev (n a : ℕ) : A := ψw ((List.range a).map fun l => n - 1 - l)

theorem tauRev_zero (n : ℕ) : (tauRev n 0 : A) = 1 := by
  simp [tauRev, ψw_nil]

theorem tauRev_succ (n a : ℕ) : (tauRev n (a + 1) : A) = tauRev n a * ψ (n - 1 - a) := by
  rw [tauRev, tauRev, List.range_succ, List.map_append, ψw_append]
  simp [ψw_cons, ψw_nil]

theorem ψw_mul_eSub {δ : A} (hδ : δ ∈ eSub (k := k) (Q := Q) ν) (ρ : List ℕ) :
    ∃ δ' ∈ eSub (k := k) (Q := Q) ν, ψw ρ * δ = δ' * ψw ρ := by
  induction ρ generalizing δ with
  | nil => exact ⟨δ, hδ, by rw [ψw_nil, one_mul, mul_one]⟩
  | cons l ρ ih =>
    obtain ⟨δ₁, hδ₁, h₁⟩ := ih hδ
    obtain ⟨δ₂, hδ₂, h₂⟩ := exists_ψ_mul_eSub hδ₁ l
    exact ⟨δ₂, hδ₂, by rw [ψw_cons, mul_assoc, h₁, ← mul_assoc, h₂, mul_assoc]⟩

variable (hQ : KLRSymm Q)

theorem sgnE_mem_eSub (j : ℕ) : (sgnE Q j : A) ∈ eSub (k := k) (Q := Q) ν :=
  Subalgebra.sum_mem _ fun _ _ => Subalgebra.smul_mem _ (e_mem_eSub _) _

theorem sigma_mem_subR0 {u : A} (hu : u ∈ subR1 (k := k) (Q := Q) ν) :
    sigma hQ u ∈ subR0 (k := k) (Q := Q) ν := by
  induction hu using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with (⟨b, rfl⟩ | ⟨t, rfl⟩) | ⟨j, hj, rfl⟩
    · rw [sigma_x]; exact x_mem_subR0 _
    · rw [sigma_e]; exact e_mem_subR0 _
    · by_cases h : j + 1 < m
      · rw [sigma_apply, sigmaHom_ψ, sigmaψ_of_lt h]
        exact Subalgebra.mul_mem _ (ψ_mem_subR0 (by omega)) (eSub_le_subR0 (sgnE_mem_eSub j))
      · rw [sigma_ψ_of_le hQ (by omega)]; exact Subalgebra.zero_mem _
  | algebraMap c => rw [AlgEquiv.commutes]; exact Subalgebra.algebraMap_mem _ c
  | add y z _ _ hy hz => rw [map_add]; exact Subalgebra.add_mem _ hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact Subalgebra.mul_mem _ hy hz

theorem sigma_tauProd (n : ℕ) (hn : n + 1 = m) (a : ℕ) :
    ∃ δ ∈ eSub (k := k) (Q := Q) ν, sigma hQ (tauProd a : A) = δ * tauRev n a := by
  induction a with
  | zero => exact ⟨1, Subalgebra.one_mem _, by rw [tauProd_zero, map_one, tauRev_zero, one_mul]⟩
  | succ a ih =>
    obtain ⟨δ, hδ, h⟩ := ih
    by_cases ha : a + 1 < m
    · obtain ⟨δ', hδ', h'⟩ := ψw_mul_eSub (sgnE_mem_eSub (k := k) (Q := Q) (ν := ν) a)
        ((List.range (a + 1)).map fun l => n - 1 - l)
      refine ⟨δ * δ', Subalgebra.mul_mem _ hδ hδ', ?_⟩
      rw [tauProd_succ, map_mul, h, sigma_apply, sigmaHom_ψ, sigmaψ_of_lt ha,
        show m - 2 - a = n - 1 - a by omega, mul_assoc, ← mul_assoc (tauRev n a),
        ← tauRev_succ, tauRev, h', ← mul_assoc]
    · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
      rw [tauProd_succ, map_mul, sigma_ψ_of_le hQ (by omega), mul_zero, zero_mul]

variable (ν) in
/-- `∑_{a ≤ c} (R(β) ⊗ k[x_m]) ψ_{n-1} ⋯ ψ_{n-a}` as a `k`-submodule. -/
noncomputable def spTauR (n c : ℕ) : Submodule k A :=
  Submodule.span k {y | ∃ u ∈ subR0 (k := k) (Q := Q) ν, ∃ a ≤ c, y = u * tauRev n a}

include hQ in
/-- **The mirror coset decomposition** `R(n + 1) = ∑_a R(n, 1) τ_n ⋯ τ_a` (KK, proofs of
Proposition 3.4 and Theorem 5.1), zero-indexed. -/
theorem spTauR_eq_top (n : ℕ) (hn : n + 1 = m) : spTauR (k := k) (Q := Q) ν n n = ⊤ := by
  have key : ∀ r' : A, sigma hQ r' ∈ spTauR (k := k) (Q := Q) ν n n := by
    intro r'
    have hr' : r' ∈ spTau (k := k) (Q := Q) ν n := by rw [spTau_eq_top n hn]; trivial
    induction hr' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, a, ha, rfl⟩ := hy
      obtain ⟨δ, hδ, h⟩ := sigma_tauProd hQ n hn a
      rw [map_mul, h, ← mul_assoc]
      exact Submodule.subset_span ⟨_, Subalgebra.mul_mem _ (sigma_mem_subR0 hQ hu)
        (eSub_le_subR0 hδ), a, ha, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy
  refine eq_top_iff.2 fun r _ => ?_
  rw [← sigma_sigma hQ r]
  exact key _

end KLRAlgebra

end Categorification.KLR
