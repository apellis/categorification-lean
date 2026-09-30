/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Linear algebra for the nondegeneracy argument

Auxiliary material for Khovanov–Lauda III (arXiv:0807.3250v1), §6.4 (TeX `sln-2008-ArXiv.tex`
l. 9598–9790): "for each `M ∈ ℕ` there exists some large `N` such that … act by linearly
independent operators".

* `exists_finset_separating`: finitely many linearly independent linear maps are already
  linearly independent on finitely many vectors of a spanning family.
* `coeff_rename_inl_mul_monomial_inr`: in `k[σ ⊕ τ]`, the coefficients of
  `q(x_σ) · y^m` (a polynomial in the first set of variables times a monomial in the second).
-/

noncomputable section

namespace Categorification.Flag.Indep

open MvPolynomial

/-- **Finitely many test vectors suffice.** If `g₁, …, g_r : V → W` are linearly independent and
the `v a` span `V`, there is a finite set `A` of indices such that the only `c` with
`∑_b c_b g_b (v a) = 0` for all `a ∈ A` is `c = 0`. -/
theorem exists_finset_separating {K V W ι α : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype ι] (g : ι → V →ₗ[K] W) (hg : LinearIndependent K g)
    (v : α → V) (hv : Submodule.span K (Set.range v) = ⊤) :
    ∃ A : Finset α, ∀ c : ι → K, (∀ a ∈ A, ∑ b, c b • g b (v a) = 0) → c = 0 := by
  classical
  let ker : Finset α → Submodule K (ι → K) := fun A =>
    { carrier := {c | ∀ a ∈ A, ∑ b, c b • g b (v a) = 0}
      add_mem' := fun {c c'} hc hc' a ha => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hc a ha, hc' a ha, add_zero]
      zero_mem' := fun a _ => by simp
      smul_mem' := fun r c hc a ha => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, hc a ha, smul_zero] }
  have hex : ∃ n, ∃ A : Finset α, Module.finrank K (ker A) = n := ⟨_, ∅, rfl⟩
  obtain ⟨A, hA⟩ := Nat.find_spec hex
  have hmin : ∀ B : Finset α, Nat.find hex ≤ Module.finrank K (ker B) :=
    fun B => Nat.find_min' hex ⟨B, rfl⟩
  refine ⟨A, fun c hc => ?_⟩
  by_contra hc0
  have hsum : ∑ b, c b • g b ≠ 0 := by
    intro h
    exact hc0 (funext fun b => (linearIndependent_iff'.1 hg) Finset.univ c h b (Finset.mem_univ b))
  obtain ⟨a, ha⟩ : ∃ a, ∑ b, c b • g b (v a) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hsum
    have : ∀ x ∈ Submodule.span K (Set.range v), (∑ b, c b • g b) x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        rw [LinearMap.coe_sum, Finset.sum_apply]
        simpa using hall a
      | zero => exact map_zero _
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul r x _ hx => rw [map_smul, hx, smul_zero]
    exact LinearMap.ext fun x => this x (hv ▸ Submodule.mem_top)
  have hle : ker (insert a A) < ker A := by
    refine lt_of_le_of_ne (fun c' hc' a' ha' => hc' a' (Finset.mem_insert_of_mem ha')) ?_
    intro heq
    have : c ∈ ker (insert a A) := heq ▸ hc
    exact ha (this a (Finset.mem_insert_self a A))
  have := Submodule.finrank_lt_finrank_of_lt (K := K) hle
  have := hmin (insert a A)
  omega

/-- The coefficients of `q(x_σ) · y^m` in `k[σ ⊕ τ]`. -/
theorem coeff_rename_inl_mul_monomial_inr {k σ τ : Type*} [CommRing k] [DecidableEq τ] (q : MvPolynomial σ k)
    (m : τ →₀ ℕ) (e : σ →₀ ℕ) (m' : τ →₀ ℕ) :
    (rename Sum.inl q * monomial (Finsupp.mapDomain Sum.inr m) 1).coeff (Finsupp.sumElim e m') =
      if m = m' then q.coeff e else 0 := by
  have hinr : ∀ (m : τ →₀ ℕ) (t : τ), Finsupp.mapDomain Sum.inr m (Sum.inr t : σ ⊕ τ) = m t :=
    fun m t => Finsupp.mapDomain_apply_of_injective Sum.inr_injective m t
  have hinl : ∀ (m : τ →₀ ℕ) (s : σ), Finsupp.mapDomain Sum.inr m (Sum.inl s : σ ⊕ τ) = 0 :=
    fun m s => Finsupp.mapDomain_of_notMem_range _ _ (by simp)
  rw [coeff_mul_monomial']
  by_cases hmm : m = m'
  · subst hmm
    have hle : Finsupp.mapDomain Sum.inr m ≤ Finsupp.sumElim e m := by
      intro x
      rcases x with s | t
      · rw [hinl]; exact Nat.zero_le _
      · rw [hinr]; simp
    have hd : Finsupp.sumElim e m - Finsupp.mapDomain Sum.inr m = Finsupp.mapDomain Sum.inl e := by
      ext x
      rcases x with s | t
      · rw [Finsupp.tsub_apply, hinl, Finsupp.mapDomain_apply_of_injective Sum.inl_injective]; simp
      · rw [Finsupp.tsub_apply, hinr, Finsupp.mapDomain_of_notMem_range _ _ (by simp)]; simp
    rw [ite_eq_left hle, hd, coeff_rename_mapDomain _ Sum.inl_injective, mul_one, ite_eq_left rfl]
  · rw [ite_eq_right hmm]
    split_ifs with hle
    · rw [mul_one]
      apply coeff_rename_eq_zero
      intro u hu
      exfalso
      apply hmm
      ext t
      have h1 := congrArg (fun d : σ ⊕ τ →₀ ℕ => d (Sum.inr t)) hu
      simp only [Finsupp.tsub_apply, Finsupp.mapDomain_of_notMem_range _ _ (by simp : Sum.inr t ∉
        Set.range (Sum.inl : σ → σ ⊕ τ)), hinr, Finsupp.sumElim_apply, Sum.elim_inr] at h1
      have h2 := hle (Sum.inr t)
      rw [hinr] at h2
      simp only [Finsupp.sumElim_apply, Sum.elim_inr] at h2
      omega
    · rfl

end Categorification.Flag.Indep

end
