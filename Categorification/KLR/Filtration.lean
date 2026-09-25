/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Basic

/-!
# The crossing filtration of `R(ν)`

Following the spanning half of the proof of KL I, Theorem 2.5 (arXiv:0803.4121v2, §2.3),
we filter the KLR algebra `R(ν)` by the number of crossings:
`filt k Q ν n` is the `k`-span of the elements `ψw ρ * pol p * e i` with `ρ` a valid word
of length at most `n`, `p` a polynomial in the dots and `i` a sequence.

## Main results

* `KLRAlgebra.ψw_mul_e` : `ψw ρ * e i = e (wordProd ρ • i) * ψw ρ`.
* `KLRAlgebra.e_mul_mem`, `KLRAlgebra.x_mul_mem`, `KLRAlgebra.pol_mul_mem`,
  `KLRAlgebra.ψ_mul_mem`, `KLRAlgebra.ψw_mul_mem` : left multiplication by idempotents
  and polynomials preserves each filtration step; a crossing raises it by one.
* `KLRAlgebra.exists_mem_filt`, `KLRAlgebra.iSup_filt` : the filtration is exhaustive.
* `KLRAlgebra.sub_mem_of_braidEquiv` : braid-equivalent words agree modulo lower terms.
* `KLRAlgebra.mul_mem_of_hasRepeat` : a word with two equal adjacent letters lies in
  lower filtration degree.

All results hold over an arbitrary commutative ring `k` and arbitrary data `Q`.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν

/-! ### Words of crossings -/

@[simp] theorem ψw_nil : (ψw [] : KLRAlgebra k Q ν) = 1 := by simp [ψw]

@[simp] theorem ψw_cons (j : ℕ) (ρ : List ℕ) :
    (ψw (j :: ρ) : KLRAlgebra k Q ν) = ψ j * ψw ρ := by simp [ψw]

@[simp] theorem ψw_append (ρ σ : List ℕ) :
    (ψw (ρ ++ σ) : KLRAlgebra k Q ν) = ψw ρ * ψw σ := by simp [ψw]

omit [DecidableEq I] in
theorem wordProd_cons' (j : ℕ) (ρ : List ℕ) :
    wordProd m (j :: ρ) = sadj m j * wordProd m ρ := by simp [wordProd]

/-- A product of crossings carries the idempotent `e i` to `e (w • i)`,
`w = wordProd ρ`. -/
theorem ψw_mul_e (ρ : List ℕ) (i : Seq ν) :
    (ψw ρ * e i : KLRAlgebra k Q ν) = e (wordProd m ρ • i) * ψw ρ := by
  induction ρ generalizing i with
  | nil => simp [wordProd]
  | cons j ρ ih =>
    rw [ψw_cons, mul_assoc, ih, ← mul_assoc, ψ_mul_e, mul_assoc, wordProd_cons', mul_smul]

theorem e_mul_ψw (ρ : List ℕ) (j : Seq ν) :
    (e j * ψw ρ : KLRAlgebra k Q ν) = ψw ρ * e ((wordProd m ρ)⁻¹ • j) := by
  rw [ψw_mul_e, smul_inv_smul]

/-- `e j` applied to a spanning element. -/
theorem e_mul_gen (j : Seq ν) (ρ : List ℕ) (p : MvPolynomial (Fin m) k) (i : Seq ν) :
    (e j * (ψw ρ * pol p * e i) : KLRAlgebra k Q ν) =
      if (wordProd m ρ)⁻¹ • j = i then ψw ρ * pol p * e i else 0 := by
  have : (e j * (ψw ρ * pol p * e i) : KLRAlgebra k Q ν) =
      ψw ρ * pol p * (e ((wordProd m ρ)⁻¹ • j) * e i) := by
    rw [← mul_assoc, ← mul_assoc, e_mul_ψw, mul_assoc (ψw ρ) (e _) (pol p),
      (e_commute_pol _ p).eq]
    simp only [mul_assoc]
  rw [this, e_mul_e]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

/-- A spanning element followed by `e i'`. -/
theorem gen_mul_e (ρ : List ℕ) (p : MvPolynomial (Fin m) k) (i i' : Seq ν) :
    (ψw ρ * pol p * e i * e i' : KLRAlgebra k Q ν) =
      if i = i' then ψw ρ * pol p * e i else 0 := by
  rw [mul_assoc _ (e i), e_mul_e]
  split_ifs <;> simp

/-! ### The filtration -/

variable (k Q ν) in
/-- The crossing filtration: `filt k Q ν n` is the `k`-span of the elements
`ψw ρ * pol p * e i` with `ρ` a valid word of length at most `n`. -/
noncomputable def filt (n : ℕ) : Submodule k (KLRAlgebra k Q ν) :=
  Submodule.span k {r | ∃ (ρ : List ℕ) (p : MvPolynomial (Fin (Multiset.card ν)) k)
    (i : Seq ν), ValidWord (Multiset.card ν) ρ ∧ ρ.length ≤ n ∧ ψw ρ * pol p * e i = r}

local notation "𝓕" => filt k Q ν

theorem mem_filt {ρ : List ℕ} (hρ : ValidWord m ρ) {n : ℕ} (hn : ρ.length ≤ n)
    (p : MvPolynomial (Fin m) k) (i : Seq ν) : ψw ρ * pol p * e i ∈ 𝓕 n :=
  Submodule.subset_span ⟨ρ, p, i, hρ, hn, rfl⟩

theorem pol_mul_e_mem (p : MvPolynomial (Fin m) k) (i : Seq ν) (n : ℕ) :
    (pol p * e i : KLRAlgebra k Q ν) ∈ 𝓕 n := by
  simpa using mem_filt (Q := Q) (ρ := []) (by simp [ValidWord]) (Nat.zero_le n) p i

theorem filt_mono {n n' : ℕ} (h : n ≤ n') : 𝓕 n ≤ 𝓕 n' :=
  Submodule.span_mono fun _ ⟨ρ, p, i, hv, hl, hr⟩ => ⟨ρ, p, i, hv, hl.trans h, hr⟩

theorem one_mem_filt (n : ℕ) : (1 : KLRAlgebra k Q ν) ∈ 𝓕 n := by
  rw [← sum_e]
  exact Submodule.sum_mem _ fun i _ => by simpa using pol_mul_e_mem (Q := Q) 1 i n

/-- To check that left multiplication by `a` maps `𝓕 n` into `𝓕 n'` it suffices to check
it on spanning elements. -/
theorem mul_mem_filt_of_gen {a : KLRAlgebra k Q ν} {n n' : ℕ}
    (h : ∀ ρ p i, ValidWord m ρ → ρ.length ≤ n → a * (ψw ρ * pol p * e i) ∈ 𝓕 n')
    {y : KLRAlgebra k Q ν} (hy : y ∈ 𝓕 n) : a * y ∈ 𝓕 n' := by
  have : 𝓕 n ≤ (𝓕 n').comap (LinearMap.mulLeft k a) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ρ, p, i, hv, hl, rfl⟩
    exact h ρ p i hv hl
  exact this hy

/-! ### Stability under left multiplication -/

theorem e_mul_mem (j : Seq ν) {n : ℕ} {y : KLRAlgebra k Q ν} (hy : y ∈ 𝓕 n) :
    e j * y ∈ 𝓕 n := by
  refine mul_mem_filt_of_gen (fun ρ p i hv hl => ?_) hy
  rw [e_mul_gen]
  split_ifs
  · exact mem_filt hv hl p i
  · exact zero_mem _

/-- If `T * e i` is a scalar multiple of `e i` for every `i`, then left multiplication by
`T` preserves each filtration step. -/
theorem mul_mem_of_mul_e_eq_smul {T : KLRAlgebra k Q ν}
    (hT : ∀ i, ∃ c : k, T * e i = c • e i) {n : ℕ} {y : KLRAlgebra k Q ν}
    (hy : y ∈ 𝓕 n) : T * y ∈ 𝓕 n := by
  choose c hc using hT
  have : T * y = ∑ i, c i • (e i * y) := by
    calc T * y = T * ((∑ i, e i) * y) := by rw [sum_e, one_mul]
      _ = ∑ i, (T * e i) * y := by rw [Finset.sum_mul, Finset.mul_sum]; simp only [mul_assoc]
      _ = ∑ i, c i • (e i * y) := by simp only [hc, smul_mul_assoc]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (e_mul_mem i hy)

theorem ψ_mul_mem (j : ℕ) {n : ℕ} {y : KLRAlgebra k Q ν} (hy : y ∈ 𝓕 n) :
    ψ j * y ∈ 𝓕 (n + 1) := by
  refine mul_mem_filt_of_gen (fun ρ p i hv hl => ?_) hy
  by_cases hj : j + 1 < m
  · rw [← mul_assoc, ← mul_assoc, ← ψw_cons]
    exact mem_filt (List.forall_mem_cons.2 ⟨hj, hv⟩) (by simp; omega) p i
  · rw [ψ_eq_zero j (by omega), zero_mul]
    exact zero_mem _

theorem ψw_mul_mem (α : List ℕ) {n : ℕ} {y : KLRAlgebra k Q ν} (hy : y ∈ 𝓕 n) :
    ψw α * y ∈ 𝓕 (α.length + n) := by
  induction α with
  | nil => simpa using hy
  | cons j α ih =>
    rw [ψw_cons, mul_assoc]
    exact filt_mono (by simp; omega) (ψ_mul_mem j ih)

/-- A dot times a spanning element lies in the same filtration degree. -/
theorem x_mul_gen_mem (ρ : List ℕ) (hv : ValidWord m ρ) (a : Fin m)
    (p : MvPolynomial (Fin m) k) (i : Seq ν) :
    (x a * (ψw ρ * pol p * e i) : KLRAlgebra k Q ν) ∈ 𝓕 ρ.length := by
  induction ρ generalizing a with
  | nil =>
    have := mem_filt (Q := Q) (ρ := []) (by simp [ValidWord]) le_rfl (X a * p) i
    simpa [mul_assoc] using this
  | cons j ρ ih =>
    have hv' : ValidWord m ρ := fun b hb => hv b (List.mem_cons_of_mem _ hb)
    have hj : j + 1 < m := hv j (by simp)
    have hz := mem_filt (Q := Q) hv' le_rfl p i
    have eq : (ψw (j :: ρ) * pol p * e i : KLRAlgebra k Q ν) =
        ψ j * (ψw ρ * pol p * e i) := by
      rw [ψw_cons]; simp only [mul_assoc]
    rw [eq]
    set z := (ψw ρ * pol p * e i : KLRAlgebra k Q ν)
    obtain ⟨a, ha⟩ := a
    have hlen : ρ.length ≤ (j :: ρ).length := by simp
    by_cases h1 : a = j
    · subst h1
      set T := (x ⟨a, ha⟩ * ψ a - ψ a * x ⟨a + 1, hj⟩ : KLRAlgebra k Q ν)
      have hT : ∀ i, ∃ c : k, T * e i = c • e i := fun i => by
        refine ⟨if i.lbl ⟨a, ha⟩ = i.lbl ⟨a + 1, hj⟩ then 1 else 0, ?_⟩
        rw [dot_cross_left a hj i]
        split_ifs <;> simp
      have : x ⟨a, ha⟩ * (ψ a * z) = ψ a * (x ⟨a + 1, hj⟩ * z) + T * z := by
        simp only [T, sub_mul, mul_assoc]; abel
      rw [this]
      exact add_mem (ψ_mul_mem a (ih hv' _)) (filt_mono hlen (mul_mem_of_mul_e_eq_smul hT hz))
    by_cases h2 : a = j + 1
    · subst h2
      set T := (ψ j * x ⟨j, by omega⟩ - x ⟨j + 1, ha⟩ * ψ j : KLRAlgebra k Q ν)
      have hT : ∀ i, ∃ c : k, T * e i = c • e i := fun i => by
        refine ⟨if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, ha⟩ then 1 else 0, ?_⟩
        rw [dot_cross_right j ha i]
        split_ifs <;> simp
      have : x ⟨j + 1, ha⟩ * (ψ j * z) = ψ j * (x ⟨j, by omega⟩ * z) - T * z := by
        simp only [T, sub_mul, mul_assoc]; abel
      rw [this]
      exact sub_mem (ψ_mul_mem j (ih hv' _)) (filt_mono hlen (mul_mem_of_mul_e_eq_smul hT hz))
    · rw [← mul_assoc, x_mul_ψ ⟨a, ha⟩ j h1 h2, mul_assoc]
      exact ψ_mul_mem j (ih hv' _)

/-- Left multiplication by a dot preserves each filtration step. -/
theorem x_mul_mem (a : Fin m) {n : ℕ} {y : KLRAlgebra k Q ν} (hy : y ∈ 𝓕 n) :
    x a * y ∈ 𝓕 n :=
  mul_mem_filt_of_gen (fun ρ p i hv hl => filt_mono hl (x_mul_gen_mem ρ hv a p i)) hy

/-- Left multiplication by a polynomial in the dots preserves each filtration step. -/
theorem pol_mul_mem (q : MvPolynomial (Fin m) k) {n : ℕ} {y : KLRAlgebra k Q ν}
    (hy : y ∈ 𝓕 n) : pol q * y ∈ 𝓕 n := by
  induction q using MvPolynomial.induction_on with
  | C c => rw [algHom_C, ← Algebra.smul_def]; exact Submodule.smul_mem _ c hy
  | add p q hp hq => rw [map_add, add_mul]; exact add_mem hp hq
  | mul_X p a hp => rw [mul_comm, map_mul, pol_X, mul_assoc]; exact x_mul_mem a hp

/-- If `T * e i = pol (q i) * e i` for every `i`, then left multiplication by `T`
preserves each filtration step. -/
theorem mul_mem_of_mul_e_eq_pol {T : KLRAlgebra k Q ν}
    (hT : ∀ i, ∃ q : MvPolynomial (Fin m) k, T * e i = pol q * e i) {n : ℕ}
    {y : KLRAlgebra k Q ν} (hy : y ∈ 𝓕 n) : T * y ∈ 𝓕 n := by
  choose q hq using hT
  have : T * y = ∑ i, pol (q i) * (e i * y) := by
    calc T * y = T * ((∑ i, e i) * y) := by rw [sum_e, one_mul]
      _ = ∑ i, (T * e i) * y := by rw [Finset.sum_mul, Finset.mul_sum]; simp only [mul_assoc]
      _ = ∑ i, pol (q i) * (e i * y) := by simp only [hq, mul_assoc]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => pol_mul_mem _ (e_mul_mem i hy)

/-! ### Exhaustiveness -/

/-- Every element of `R(ν)` lies in some step of the crossing filtration. -/
theorem exists_mem_filt (r : KLRAlgebra k Q ν) : ∃ n, r ∈ 𝓕 n := by
  have hadd : ∀ a b : KLRAlgebra k Q ν, (∃ n, a ∈ 𝓕 n) → (∃ n, b ∈ 𝓕 n) →
      ∃ n, a + b ∈ 𝓕 n := by
    rintro a b ⟨n₁, h₁⟩ ⟨n₂, h₂⟩
    exact ⟨max n₁ n₂, add_mem (filt_mono (le_max_left _ _) h₁)
      (filt_mono (le_max_right _ _) h₂)⟩
  have key : ∀ f : FreeAlgebra k (Gen ν), ∀ y : KLRAlgebra k Q ν, (∃ n, y ∈ 𝓕 n) →
      ∃ n, mk k Q ν f * y ∈ 𝓕 n := by
    intro f
    induction f using FreeAlgebra.induction with
    | grade0 c =>
      rintro y ⟨n, hy⟩
      refine ⟨n, ?_⟩
      rw [AlgHom.commutes, ← Algebra.smul_def]
      exact Submodule.smul_mem _ c hy
    | grade1 g =>
      rintro y ⟨n, hy⟩
      cases g with
      | idem i => exact ⟨n, e_mul_mem i hy⟩
      | dot a => exact ⟨n, x_mul_mem a hy⟩
      | cross j => exact ⟨n + 1, ψ_mul_mem j hy⟩
    | mul a b ha hb =>
      intro y hy
      rw [map_mul, mul_assoc]
      exact ha _ (hb y hy)
    | add a b ha hb =>
      intro y hy
      rw [map_add, add_mul]
      exact hadd _ _ (ha y hy) (hb y hy)
  obtain ⟨f, rfl⟩ := mk_surjective (Q := Q) r
  simpa using key f 1 ⟨0, one_mem_filt 0⟩

/-- The crossing filtration is exhaustive. -/
theorem iSup_filt : ⨆ n, 𝓕 n = ⊤ :=
  eq_top_iff.2 fun r _ => by
    obtain ⟨n, h⟩ := exists_mem_filt r
    exact Submodule.mem_iSup_of_mem n h

/-! ### Braid moves and repeated letters modulo lower terms -/

theorem ncEval_x₂ (a b : Fin m) (P : MvPolynomial (Fin 2) k) :
    ncEval ![(x a : KLRAlgebra k Q ν), x b] P = pol (rename ![a, b] P) := by
  rw [← ncEval_eq_pol]
  congr 1
  funext t
  fin_cases t <;> rfl

theorem ncEval_x₃ (a b c : Fin m) (P : MvPolynomial (Fin 3) k) :
    ncEval ![(x a : KLRAlgebra k Q ν), x b, x c] P = pol (rename ![a, b, c] P) := by
  rw [← ncEval_eq_pol]
  congr 1
  funext t
  fin_cases t <;> rfl

/-- `ψ_j²` (a polynomial in the dots on each `e i`) preserves each filtration step. -/
theorem ψ_sq_mul_mem (j : ℕ) {n : ℕ} {y : KLRAlgebra k Q ν} (hy : y ∈ 𝓕 n) :
    ψ j * ψ j * y ∈ 𝓕 n := by
  by_cases h : j + 1 < m
  · refine mul_mem_of_mul_e_eq_pol (fun i => ?_) hy
    rw [ψ_sq j h i]
    split_ifs
    · exact ⟨0, by simp⟩
    · exact ⟨_, by rw [ncEval_x₂]⟩
  · rw [ψ_eq_zero j (by omega), zero_mul, zero_mul]
    exact zero_mem _

/-- The difference of the two sides of the braid relation (a polynomial in the dots on
each `e i`) preserves each filtration step. -/
theorem braidDiff_mul_mem (j : ℕ) {n : ℕ} {y : KLRAlgebra k Q ν} (hy : y ∈ 𝓕 n) :
    (ψ j * ψ (j + 1) * ψ j - ψ (j + 1) * ψ j * ψ (j + 1)) * y ∈ 𝓕 n := by
  by_cases h : j + 2 < m
  · refine mul_mem_of_mul_e_eq_pol (fun i => ?_) hy
    rw [braid j h i]
    split_ifs
    · exact ⟨_, by rw [ncEval_x₃]⟩
    · exact ⟨0, by simp⟩
  · rw [ψ_eq_zero (j + 1) (by omega)]
    simp

theorem length_eq_of_braidStep {ρ σ : List ℕ} (h : BraidStep ρ σ) :
    ρ.length = σ.length := by
  cases h <;> simp

theorem length_eq_of_braidEquiv {ρ σ : List ℕ} (h : BraidEquiv ρ σ) :
    ρ.length = σ.length := by
  induction h with
  | rel _ _ h => exact length_eq_of_braidStep h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A single braid move changes `ψw ρ * y` only by terms of lower filtration degree. -/
theorem sub_mem_of_braidStep {ρ σ : List ℕ} (h : BraidStep ρ σ) {n : ℕ}
    {y : KLRAlgebra k Q ν} (hy : y ∈ 𝓕 n) :
    ψw ρ * y - ψw σ * y ∈ 𝓕 (ρ.length - 1 + n) := by
  cases h with
  | comm α β hab =>
    simp only [ψw_append, ψw_cons, ψw_nil, mul_one]
    rw [ψ_mul_ψ _ _ hab, sub_self]
    exact zero_mem _
  | braid α β a =>
    have : ψw (α ++ [a, a + 1, a] ++ β) * y - ψw (α ++ [a + 1, a, a + 1] ++ β) * y =
        ψw α * ((ψ a * ψ (a + 1) * ψ a - ψ (a + 1) * ψ a * ψ (a + 1)) * (ψw β * y)) := by
      simp only [ψw_append, ψw_cons, ψw_nil, mul_one, mul_sub, sub_mul, mul_assoc]
    rw [this]
    exact filt_mono (by simp; omega) (ψw_mul_mem α (braidDiff_mul_mem a (ψw_mul_mem β hy)))

/-- Braid-equivalent words agree modulo terms of lower filtration degree. -/
theorem sub_mem_of_braidEquiv {ρ σ : List ℕ} (h : BraidEquiv ρ σ) {n : ℕ}
    {y : KLRAlgebra k Q ν} (hy : y ∈ 𝓕 n) :
    ψw ρ * y - ψw σ * y ∈ 𝓕 (ρ.length - 1 + n) := by
  induction h with
  | rel _ _ h => exact sub_mem_of_braidStep h hy
  | refl => rw [sub_self]; exact zero_mem _
  | symm _ _ h ih =>
    rw [← length_eq_of_braidEquiv h, ← neg_sub]
    exact neg_mem ih
  | trans _ _ _ h₁ _ ih₁ ih₂ =>
    rw [← length_eq_of_braidEquiv h₁] at ih₂
    have := add_mem ih₁ ih₂
    rwa [sub_add_sub_cancel] at this

/-- A word with two equal adjacent letters lies in lower filtration degree. -/
theorem mul_mem_of_hasRepeat {ρ : List ℕ} (h : HasRepeat ρ) {n : ℕ}
    {y : KLRAlgebra k Q ν} (hy : y ∈ 𝓕 n) : ψw ρ * y ∈ 𝓕 (ρ.length - 1 + n) := by
  obtain ⟨α, β, a, rfl⟩ := h
  have : ψw (α ++ [a, a] ++ β) * y = ψw α * (ψ a * ψ a * (ψw β * y)) := by
    simp only [ψw_append, ψw_cons, ψw_nil, mul_one, mul_assoc]
  rw [this]
  exact filt_mono (by simp; omega) (ψw_mul_mem α (ψ_sq_mul_mem a (ψw_mul_mem β hy)))

/-- Braid-equivalent words give the same spanning elements modulo lower filtration
degree. -/
theorem sub_mul_mem_of_braidEquiv {ρ σ : List ℕ} (h : BraidEquiv ρ σ)
    (p : MvPolynomial (Fin m) k) (i : Seq ν) :
    (ψw ρ - ψw σ) * pol p * e i ∈ 𝓕 (ρ.length - 1) := by
  have := sub_mem_of_braidEquiv h (pol_mul_e_mem (Q := Q) p i 0)
  simpa [sub_mul, mul_assoc] using this

/-- A spanning element whose word has a repeated letter lies in lower filtration
degree. -/
theorem gen_mem_of_hasRepeat {ρ : List ℕ} (h : HasRepeat ρ) (p : MvPolynomial (Fin m) k)
    (i : Seq ν) : (ψw ρ * pol p * e i : KLRAlgebra k Q ν) ∈ 𝓕 (ρ.length - 1) := by
  have := mul_mem_of_hasRepeat h (pol_mul_e_mem (Q := Q) p i 0)
  simpa [mul_assoc] using this

end KLRAlgebra

end Categorification.KLR
