/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Partial fractions and the bubbles with inverted dots

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`. On the generating object, the bubbles of a colour are
computed from the dual-basis property of Rouquier's isomorphism. When labels of both signs occur,
the computation also needs the dot with the factors `x - z_c` inverted, for the labels `z_c` of
the other sign. This file is the commutative algebra behind that step.

Let `x` be an element of a commutative `L`-algebra `A`, let `w c` be inverses of `x - z_c` for
distinct `z_c ∈ L`, and let `Ψ : A → R` be `L`-linear. Suppose `Ψ (x ^ t) = δ_{t+1, N}` for `t < N`
and `Ψ (w c ^ j) = δ_{N, 0} δ_{j, 1}` for `1 ≤ j ≤ μ_c`. Then
`Ψ (x ^ t ∏_c w_c ^ μ_c) = δ_{t+1, N + ∑ μ}` for `t < N + ∑_c μ_c`
(`map_pow_mul_prod_pow_eq`). The proof writes the polynomials of degree `< N + ∑ μ` in the
basis `P X^s` (`s < N`) together with the partial fractions `P / (X - z_c)^j`, where
`P = ∏_c (X - z_c)^{μ_c}` (`mem_span_pfSet`).

## Main definitions

* `rootProd z μ`: the polynomial `∏_c (X - z_c)^{μ_c}`.
* `pfPoly z μ c j`: the polynomial `∏_c (X - z_c)^{μ_c} / (X - z_c)^j`.

## Main results

* `mem_span_pfSet`: polynomials of degree `< ∑ μ` are combinations of the `pfPoly z μ c j`,
  `1 ≤ j ≤ μ_c`.
* `map_pow_mul_prod_pow_eq`: the values above.
-/

open Polynomial

namespace Categorification.KLR.Unfurling

variable {L : Type*} [Field L] {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- The polynomial `∏_c (X - z_c)^{μ_c}`. -/
noncomputable def rootProd (z : Γ → L) (μ : Γ → ℕ) : L[X] := ∏ c, (X - C (z c)) ^ μ c

omit [DecidableEq Γ] in
theorem rootProd_monic (z : Γ → L) (μ : Γ → ℕ) : (rootProd z μ).Monic :=
  monic_prod_of_monic _ _ fun c _ => (monic_X_sub_C (z c)).pow (μ c)

omit [DecidableEq Γ] in
theorem natDegree_rootProd (z : Γ → L) (μ : Γ → ℕ) : (rootProd z μ).natDegree = ∑ c, μ c := by
  rw [rootProd, natDegree_prod_of_monic _ _ fun c _ => (monic_X_sub_C (z c)).pow (μ c)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [(monic_X_sub_C (z c)).natDegree_pow, natDegree_X_sub_C, mul_one]

omit [Fintype Γ] in
theorem sum_update_add {μ : Γ → ℕ} (s : Finset Γ) {c₀ : Γ} (h : c₀ ∈ s) (m : ℕ) :
    ∑ c ∈ s, Function.update μ c₀ m c + μ c₀ = ∑ c ∈ s, μ c + m := by
  have h1 := Finset.sum_update_of_mem h μ m
  have h2 := Finset.sum_update_of_mem h μ (μ c₀)
  rw [Function.update_eq_self] at h2
  omega

theorem rootProd_split (z : Γ → L) (ν : Γ → ℕ) (c₀ : Γ) :
    rootProd z ν = (X - C (z c₀)) ^ ν c₀ *
      ∏ c ∈ Finset.univ.erase c₀, (X - C (z c)) ^ ν c :=
  (Finset.mul_prod_erase _ (fun c => (X - C (z c)) ^ ν c) (Finset.mem_univ c₀)).symm

theorem X_sub_C_mul_rootProd (z : Γ → L) (ν : Γ → ℕ) (c₀ : Γ) (h : 1 ≤ ν c₀) :
    (X - C (z c₀)) * rootProd z (Function.update ν c₀ (ν c₀ - 1)) = rootProd z ν := by
  rw [rootProd_split z _ c₀, rootProd_split z ν c₀, Function.update_self, ← mul_assoc,
    ← pow_succ', Nat.sub_add_cancel h]
  congr 1
  refine Finset.prod_congr rfl fun c hc => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hc)]

/-- The partial fraction `∏_c (X - z_c)^{μ_c} / (X - z_{c₀})^j`. -/
noncomputable def pfPoly (z : Γ → L) (μ : Γ → ℕ) (c₀ : Γ) (j : ℕ) : L[X] :=
  rootProd z (Function.update μ c₀ (μ c₀ - j))

/-- The partial fractions `pfPoly z μ c j`, `1 ≤ j ≤ μ_c`. -/
def pfSet (z : Γ → L) (μ : Γ → ℕ) : Set L[X] :=
  {p | ∃ c j, 1 ≤ j ∧ j ≤ μ c ∧ p = pfPoly z μ c j}

theorem mul_pfSet_subset (z : Γ → L) (μ : Γ → ℕ) (c₀ : Γ) (h : 1 ≤ μ c₀) :
    (fun p => (X - C (z c₀)) * p) '' pfSet z (Function.update μ c₀ (μ c₀ - 1)) ⊆
      pfSet z μ := by
  rintro _ ⟨_, ⟨c, j, hj1, hj, rfl⟩, rfl⟩
  by_cases hc : c = c₀
  · subst hc
    rw [Function.update_self] at hj
    refine ⟨c, j, hj1, by omega, ?_⟩
    have h1 : 1 ≤ Function.update μ c (μ c - j) c := by rw [Function.update_self]; omega
    beta_reduce
    simp only [pfPoly]
    rw [← X_sub_C_mul_rootProd z _ c h1]
    simp only [Function.update_self, Function.update_idem]
    congr 3
    omega
  · rw [Function.update_of_ne hc] at hj
    refine ⟨c, j, hj1, hj, ?_⟩
    have h1 : 1 ≤ Function.update μ c (μ c - j) c₀ := by
      rw [Function.update_of_ne (Ne.symm hc)]; exact h
    beta_reduce
    simp only [pfPoly]
    rw [← X_sub_C_mul_rootProd z _ c₀ h1, Function.update_of_ne hc,
      Function.update_of_ne (Ne.symm hc), Function.update_comm hc]

/-- **Partial fractions.** For distinct `z_c`, every polynomial of degree `< ∑_c μ_c` is a
combination of the `∏_c (X - z_c)^{μ_c} / (X - z_{c₀})^j`, `1 ≤ j ≤ μ_{c₀}`. -/
theorem mem_span_pfSet {z : Γ → L} (hz : Function.Injective z) :
    ∀ (n : ℕ) (μ : Γ → ℕ), ∑ c, μ c = n → ∀ f : L[X], f.degree < n →
      f ∈ Submodule.span L (pfSet z μ) := by
  intro n
  induction n with
  | zero =>
    intro μ _ f hf
    rw [Nat.cast_zero] at hf
    by_cases hf0 : f = 0
    · rw [hf0]; exact Submodule.zero_mem _
    · exact absurd hf (not_lt.mpr (zero_le_degree_iff.mpr hf0))
  | succ k ih =>
    intro μ hμ f hf
    obtain ⟨c₀, -, hc₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := μ)
      (by omega)
    have hc₀' : 1 ≤ μ c₀ := Nat.one_le_iff_ne_zero.mpr hc₀
    have hRa : (pfPoly z μ c₀ (μ c₀)).eval (z c₀) ≠ 0 := by
      rw [pfPoly, rootProd, eval_prod, Finset.prod_ne_zero_iff]
      intro c _
      by_cases hc : c = c₀
      · subst hc; simp
      · rw [Function.update_of_ne hc, eval_pow, eval_sub, eval_X, eval_C]
        exact pow_ne_zero _ (sub_ne_zero.mpr fun h => hc (hz h).symm)
    have hRdeg : (pfPoly z μ c₀ (μ c₀)).degree < (k + 1 : ℕ) := by
      have hsum := sum_update_add (μ := μ) Finset.univ (Finset.mem_univ c₀) 0
      rw [pfPoly, Nat.sub_self, degree_eq_natDegree (rootProd_monic _ _).ne_zero,
        natDegree_rootProd]
      exact_mod_cast (by omega : ∑ c, Function.update μ c₀ 0 c < k + 1)
    set κ := f.eval (z c₀) / (pfPoly z μ c₀ (μ c₀)).eval (z c₀)
    set g := f - κ • pfPoly z μ c₀ (μ c₀) with hg
    have hga : g.IsRoot (z c₀) := by
      simp only [hg, IsRoot, eval_sub, eval_smul, smul_eq_mul, κ, div_mul_cancel₀ _ hRa,
        sub_self]
    have hgdeg : g.degree < (k + 1 : ℕ) :=
      (degree_sub_le _ _).trans_lt (max_lt hf ((degree_smul_le _ _).trans_lt hRdeg))
    set s := g /ₘ (X - C (z c₀))
    have hgs : (X - C (z c₀)) * s = g := mul_divByMonic_eq_iff_isRoot.mpr hga
    have hsdeg : s.degree < k := by
      by_cases hs : s = 0
      · rw [hs, degree_zero]; exact WithBot.bot_lt_coe _
      · have hg0 : g ≠ 0 := by rw [← hgs]; exact mul_ne_zero (X_sub_C_ne_zero _) hs
        have hmul := natDegree_mul (X_sub_C_ne_zero (z c₀)) hs
        rw [hgs, natDegree_X_sub_C] at hmul
        have hgn : g.natDegree < k + 1 := by
          rw [degree_eq_natDegree hg0] at hgdeg; exact_mod_cast hgdeg
        rw [degree_eq_natDegree hs]
        exact_mod_cast (by omega : s.natDegree < k)
    have hμ' : ∑ c, Function.update μ c₀ (μ c₀ - 1) c = k := by
      have := sum_update_add (μ := μ) Finset.univ (Finset.mem_univ c₀) (μ c₀ - 1)
      omega
    have hs := ih _ hμ' s hsdeg
    have hmap : (X - C (z c₀)) * s ∈ Submodule.span L (pfSet z μ) := by
      have := Submodule.mem_map_of_mem (f := LinearMap.mulLeft L (X - C (z c₀))) hs
      rw [Submodule.map_span] at this
      exact Submodule.span_mono (mul_pfSet_subset z μ c₀ hc₀') this
    have hf' : f = κ • pfPoly z μ c₀ (μ c₀) + (X - C (z c₀)) * s := by
      rw [hgs, hg]; abel
    rw [hf']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _
      (Submodule.subset_span ⟨c₀, μ c₀, hc₀', le_rfl, rfl⟩)) hmap

theorem coeff_monic_of_le {p : L[X]} (hp : p.Monic) {d : ℕ} (h : p.natDegree ≤ d) :
    p.coeff d = if d = p.natDegree then 1 else 0 := by
  split_ifs with hd
  · rw [hd]; exact hp.coeff_natDegree
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne h (Ne.symm hd))

theorem prod_pow_update_mul {A : Type*} [CommRing A] (a w : Γ → A) (haw : ∀ c, a c * w c = 1)
    (μ : Γ → ℕ) (c₀ : Γ) {m : ℕ} (hm : m ≤ μ c₀) :
    (∏ c, a c ^ Function.update μ c₀ m c) * ∏ c, w c ^ μ c = w c₀ ^ (μ c₀ - m) := by
  rw [← Finset.mul_prod_erase _ (fun c => a c ^ Function.update μ c₀ m c) (Finset.mem_univ c₀),
    ← Finset.mul_prod_erase _ (fun c => w c ^ μ c) (Finset.mem_univ c₀)]
  rw [Function.update_self]
  have hE : ∏ c ∈ Finset.univ.erase c₀, a c ^ Function.update μ c₀ m c =
      ∏ c ∈ Finset.univ.erase c₀, a c ^ μ c :=
    Finset.prod_congr rfl fun c hc => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hc)]
  have hEF : (∏ c ∈ Finset.univ.erase c₀, a c ^ μ c) *
      ∏ c ∈ Finset.univ.erase c₀, w c ^ μ c = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun c _ => by rw [← mul_pow, haw, one_pow]
  have hsplit : w c₀ ^ μ c₀ = w c₀ ^ m * w c₀ ^ (μ c₀ - m) := by
    rw [← pow_add, Nat.add_sub_cancel' hm]
  rw [hE, hsplit]
  calc a c₀ ^ m * (∏ c ∈ Finset.univ.erase c₀, a c ^ μ c) *
        (w c₀ ^ m * w c₀ ^ (μ c₀ - m) * ∏ c ∈ Finset.univ.erase c₀, w c ^ μ c)
      = (a c₀ * w c₀) ^ m * ((∏ c ∈ Finset.univ.erase c₀, a c ^ μ c) *
          ∏ c ∈ Finset.univ.erase c₀, w c ^ μ c) * w c₀ ^ (μ c₀ - m) := by ring
    _ = w c₀ ^ (μ c₀ - m) := by rw [haw, hEF, one_pow, one_mul, one_mul]

/-- **The values with inverted dots.** Let `w c` be inverses of `x - z_c` for distinct `z_c`,
and let `Ψ` be `L`-linear with `Ψ (x ^ t) = δ_{t+1, N}` for `t < N` and
`Ψ (w c ^ j) = δ_{N, 0} δ_{j, 1}` for `1 ≤ j ≤ μ_c`. Then
`Ψ (x ^ t ∏_c w_c ^ μ_c) = δ_{t+1, N + ∑ μ}` for `t < N + ∑_c μ_c`. -/
theorem map_pow_mul_prod_pow_eq {A R : Type*} [CommRing A] [Algebra L A] [Ring R]
    [Algebra L R] (Ψ : A →ₗ[L] R) (x : A) {z : Γ → L} (hz : Function.Injective z) (w : Γ → A)
    (hw : ∀ c, (x - algebraMap L A (z c)) * w c = 1) (μ : Γ → ℕ) (N : ℕ)
    (hx : ∀ t < N, Ψ (x ^ t) = if t + 1 = N then 1 else 0)
    (hwj : ∀ c j, 1 ≤ j → j ≤ μ c → Ψ (w c ^ j) = if N = 0 ∧ j = 1 then 1 else 0)
    (t : ℕ) (ht : t < N + ∑ c, μ c) :
    Ψ (x ^ t * ∏ c, w c ^ μ c) = if t + 1 = N + ∑ c, μ c then 1 else 0 := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, ∑ c, μ c = n := ⟨_, rfl⟩
  rw [hn] at ht ⊢
  let φ : L[X] →ₗ[L] R :=
    Ψ ∘ₗ LinearMap.mulRight L (∏ c, w c ^ μ c) ∘ₗ (aeval x).toLinearMap
  let ψ : L[X] →ₗ[L] R := Algebra.linearMap L R ∘ₗ lcoeff L (N + n - 1)
  have hφ : ∀ f, φ f = Ψ (aeval x f * ∏ c, w c ^ μ c) := fun f => rfl
  have hψ : ∀ f, ψ f = algebraMap L R (f.coeff (N + n - 1)) := fun f => rfl
  have haeval : ∀ ν : Γ → ℕ,
      aeval x (rootProd z ν) = ∏ c, (x - algebraMap L A (z c)) ^ ν c := by
    intro ν; simp [rootProd, map_prod, map_pow, map_sub, aeval_X, aeval_C]
  have hPW : aeval x (rootProd z μ) * ∏ c, w c ^ μ c = 1 := by
    rw [haeval, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun c _ => by rw [← mul_pow, hw, one_pow]
  let S : Set L[X] := {p | ∃ s < N, p = rootProd z μ * X ^ s} ∪ pfSet z μ
  have hS : Set.EqOn φ ψ S := by
    rintro p (⟨s, hs, rfl⟩ | ⟨c, j, hj1, hj, rfl⟩)
    · have hval : aeval x (rootProd z μ * X ^ s) * ∏ c, w c ^ μ c = x ^ s := by
        rw [map_mul, map_pow, aeval_X]
        linear_combination (x ^ s) * hPW
      rw [hφ, hψ, hval, hx s hs, coeff_mul_X_pow',
        coeff_monic_of_le (rootProd_monic z μ) (by rw [natDegree_rootProd]; omega),
        natDegree_rootProd, hn]
      split_ifs <;> first | omega | simp
    · have hμc : μ c ≤ n := hn ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c)
      have hdeg : (pfPoly z μ c j).natDegree = n - j := by
        have := sum_update_add (μ := μ) Finset.univ (Finset.mem_univ c) (μ c - j)
        rw [pfPoly, natDegree_rootProd]
        omega
      have hval : aeval x (pfPoly z μ c j) * ∏ c, w c ^ μ c = w c ^ j := by
        rw [pfPoly, haeval, prod_pow_update_mul (fun c => x - algebraMap L A (z c)) w hw μ c
          (by omega : μ c - j ≤ μ c), Nat.sub_sub_self hj]
      rw [hφ, hψ, hval, hwj c j hj1 hj,
        coeff_monic_of_le (p := pfPoly z μ c j) (rootProd_monic _ _) (d := N + n - 1)
          (by rw [hdeg]; omega),
        hdeg]
      split_ifs <;> first | omega | simp
  have hspan : ∀ f : L[X], f.degree < (N + n : ℕ) → f ∈ Submodule.span L S := by
    intro f hf
    rw [← modByMonic_add_div f (rootProd z μ)]
    refine Submodule.add_mem _ (Submodule.span_mono Set.subset_union_right
      (mem_span_pfSet hz n μ hn _ ?_)) ?_
    · have := degree_modByMonic_lt f (rootProd_monic z μ)
      rwa [degree_eq_natDegree (rootProd_monic z μ).ne_zero, natDegree_rootProd, hn] at this
    · have hq : f /ₘ rootProd z μ ∈ degreeLT L N := by
        rw [mem_degreeLT]
        by_cases h0 : f /ₘ rootProd z μ = 0
        · rw [h0, degree_zero]; exact WithBot.bot_lt_coe _
        · have hf0 : f ≠ 0 := by rintro rfl; simp at h0
          have hge : n ≤ f.natDegree := by
            by_contra hlt
            refine h0 ((divByMonic_eq_zero_iff (rootProd_monic z μ)).mpr ?_)
            rw [degree_eq_natDegree (rootProd_monic z μ).ne_zero, natDegree_rootProd, hn,
              degree_eq_natDegree hf0]
            exact_mod_cast (by omega : f.natDegree < n)
          have hfn : f.natDegree < N + n := by
            rw [degree_eq_natDegree hf0] at hf; exact_mod_cast hf
          rw [degree_eq_natDegree h0, natDegree_divByMonic f (rootProd_monic z μ),
            natDegree_rootProd, hn]
          exact_mod_cast (by omega : f.natDegree - n < N)
      rw [degreeLT_eq_span_X_pow] at hq
      have hle : Submodule.span L ↑(Finset.image (fun s => (X : L[X]) ^ s) (Finset.range N)) ≤
          (Submodule.span L S).comap (LinearMap.mulLeft L (rootProd z μ)) := by
        rw [Submodule.span_le]
        intro p hp
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hp
        obtain ⟨s, hs, rfl⟩ := hp
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
        exact Submodule.subset_span (Or.inl ⟨s, hs, rfl⟩)
      exact Submodule.mem_comap.mp (hle hq)
  have hEq := LinearMap.eqOn_span' hS (hspan (X ^ t) (by rw [degree_X_pow]; exact_mod_cast ht))
  rw [hφ, hψ, map_pow, aeval_X, coeff_X_pow] at hEq
  rw [hEq]
  split_ifs <;> first | omega | simp

end Categorification.KLR.Unfurling
