/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.InductionFree
import Categorification.KLR.KL1Basis
import Categorification.TypeA.DoubleCoset

/-!
# The Mackey filtration of `_{ν,ν'}R_{ν'',ν'''}`

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, **Proposition 2.18**: for weights with
`ν + ν' = ν'' + ν'''`, the `(R(ν) ⊗ R(ν'), R(ν'') ⊗ R(ν'''))`-bimodule
`_{ν,ν'}R_{ν'',ν'''} = 1_{ν,ν'} R(ν + ν') 1_{ν'',ν'''}`
has a filtration by sub-bimodules indexed by the data `λ` of the double cosets
`(S_n × S_{n'}) \ S_m / (S_{n''} × S_{n'''})`, `λ` being the weight of the strands going from
the second bottom block (`ν'''`) to the first top block (`ν`).

## Strategy

We filter by `|λ|` (for fixed weights, `λ` is determined by the double coset and the double
cosets are linearly ordered by `|λ|`, see `TypeA.crossCount`). The filtration step
`mackeyFilt n n'' c` is the `k`-span of the diagrams `ψ_γ x^p 1_i` all of whose *subwords*
`δ ⊆ γ` satisfy `crossCount (wordProd δ) ≤ c`. This is designed so that

* it is visibly stable under left multiplication by the generators of `R(ν) ⊗ R(ν')` and right
  multiplication by the generators of `R(ν'') ⊗ R(ν''')` (`crossCount` is invariant under the
  corresponding parabolic subgroups, and dots only delete letters), and
* it has the explicit `k`-basis `ψ_{ρ w} x^u 1_i`, `crossCount w ≤ c`, for *any* choice `ρ` of
  reduced words (`mackeyFilt_eq_stdSpan`).

The second point is a *subword-refined spanning theorem* (`gen_mem_stdSpan`): rewriting a
product of crossings `ψ_γ` in terms of the basis only produces basis elements `ψ_{ρ w}` with
`w` a subword product of `γ`. Its proof follows the spanning half of KL I, Theorem 2.5
(`KLRAlgebra.filt_le_span`), keeping track of subwords instead of lengths; the set of subword
products is a braid invariant (`TypeA.BraidEquiv.subProds_eq`). The converse inclusion uses
the subword property of the rank function (`TypeA.crossCount_le_of_mem_subProds`).

## Main results

Throughout, `h : ν'' + ν''' = ν + ν'`; the ambient algebra is `R(ν + ν')`, the left action is
`concat Q ν ν'` (= `ι_{ν,ν'}`) and the right action is `botConcat Q h` (= `ι_{ν'',ν'''}`
transported along `h`). `n = card ν`, `n'' = card ν''`.

* `KLRAlgebra.gen_mem_stdSpan` — subword-refined spanning (any commutative ring `k`).
* `KLRAlgebra.mackeyFilt_eq_stdSpan` — for any reduced words `ρ`, `mackeyFilt n n'' c` is spanned
  by the standard elements `ψ_{ρ w} x^u 1_i` with `crossCount n n'' w ≤ c`.
* `KLRAlgebra.bimod` — the bimodule `_{ν,ν'}R_{ν'',ν'''} = 1_{ν,ν'} R(ν + ν') 1_{ν'',ν'''}`;
  `KLRAlgebra.mackeyBimodFilt h c = bimod ⊓ mackeyFilt n n'' c` — its Mackey filtration.
* `KLRAlgebra.concat_mul_mem_mackeyBimodFilt`, `KLRAlgebra.mul_botConcat_mem_mackeyBimodFilt`
  — the steps are sub-bimodules; `mackeyBimodFilt_mono`, `mackeyBimodFilt_eq_bimod`
  (exhaustive at `c = n`), `mackeyBimodFilt_eq_bot` (zero for `c < n - n''`).
* `KLRAlgebra.mackeyBimodFilt_eq_span` — **basis form of Prop. 2.18**: for any reduced words `ρ`,
  the `c`-th step is spanned by the standard elements of `_{ν,ν'}R_{ν'',ν'''}` with `|λ| ≤ c`;
  `KLRAlgebra.mackeyBasis` (a `k`-basis of each step) and `KLRAlgebra.mackeySubquotBasis`
  (a `k`-basis of each subquotient `F_{c+1} / F_c`, indexed by the standard elements with
  `|λ| = c + 1`, `mem_mackeyIdx_diff`), under the hypotheses of the basis theorem.
* `KLRAlgebra.stdElt_mackeyWord` — with the Mackey-adapted reduced words
  `ρ₁(a) (n + ρ₂(b)) σ(d) ρ₃(y) (n'' + ρ₄(y'))` of `w = (a × b) d (y × y')`, every standard
  element of `_{ν,ν'}R_{ν'',ν'''}` is `ι(ψ_a 1_i ⊗ ψ_b 1_j) · ψ_{σ(d)} · ι''(ψ_y x^{u₁} 1_{s₁} ⊗
  ψ_{y'} x^{u₂} 1_{s₂})` with `d` the minimal double coset representative of `w`.
* `KLRAlgebra.mackeyBimodFilt_eq_span_crossings` — over any `k`, the `c`-th step is spanned by
  `ι(t) ψ_d ι''(t')` over the minimal double coset representatives `d` with `|λ| ≤ c`
  (the paper's generators of the subquotients).
* `KL1.mackeyBasis`, `KL1.mackeySubquotBasis` — the specialisation to KL I (simple graph `Γ`,
  `klQ Γ`, over `ℤ` or any integral domain).

## Relation to the paper and what is not covered

The paper indexes the filtration by the weight `λ`; for fixed weights the double cosets are
determined by `|λ|` (`TypeA.crossCount_eq_iff_mem_doubleCoset`,
`TypeA.exists_isDoubleShuffle_iff`), and we index by `c = |λ|`. (Informally, the subquotient of
index `c` collects the paper's subquotients for all weights `λ` with `|λ| = c`, the weight of
the crossing strands depending on the sequences; this splitting by weights is not formalized.)
The identification of the subquotients with the balanced tensor products
`(_{ν}R_{ν-λ,λ} ⊗ _{ν'}R_{ν'+λ-ν''',ν'''-λ}) ⊗_{R'} (_{ν-λ,ν''+λ-ν}R_{ν''} ⊗ _{λ,ν'''-λ}R_{ν'''})`
as bimodules, and the grading shift `{-λ·(ν'+λ-ν''')}`, are not formalized here; the crossing
pairs of `ψ_d` (whose degree gives that shift) are described by
`TypeA.IsDoubleShuffle.mem_invSet_iff`.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {μ : Multiset I}

local notation "m" => Multiset.card μ

/-! ### Spans of subwords -/

section SubSpan

variable (k Q μ) in
/-- `subSpan γ` is the `k`-span of the diagrams `ψ_δ x^p 1_i` with `δ` a subword of `γ`. -/
noncomputable def subSpan (γ : List ℕ) : Submodule k (KLRAlgebra k Q μ) :=
  Submodule.span k {r | ∃ (δ : List ℕ) (p : MvPolynomial (Fin (Multiset.card μ)) k)
    (i : Seq μ), δ.Sublist γ ∧ ψw δ * pol p * e i = r}

local notation "𝓢" => subSpan k Q μ

theorem mem_subSpan {δ γ : List ℕ} (h : δ.Sublist γ) (p : MvPolynomial (Fin m) k)
    (i : Seq μ) : ψw δ * pol p * e i ∈ 𝓢 γ :=
  Submodule.subset_span ⟨δ, p, i, h, rfl⟩

theorem subSpan_mono {δ γ : List ℕ} (h : δ.Sublist γ) : 𝓢 δ ≤ 𝓢 γ :=
  Submodule.span_mono fun _ ⟨δ', p, i, h', hr⟩ => ⟨δ', p, i, h'.trans h, hr⟩

theorem pol_mul_e_mem_subSpan (p : MvPolynomial (Fin m) k) (i : Seq μ) (γ : List ℕ) :
    (pol p * e i : KLRAlgebra k Q μ) ∈ 𝓢 γ := by
  simpa using mem_subSpan (Q := Q) (List.nil_sublist γ) p i

theorem mul_mem_subSpan_of_gen {a : KLRAlgebra k Q μ} {γ γ' : List ℕ}
    (h : ∀ δ p i, δ.Sublist γ → a * (ψw δ * pol p * e i) ∈ 𝓢 γ')
    {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓢 γ) : a * y ∈ 𝓢 γ' := by
  have : 𝓢 γ ≤ (𝓢 γ').comap (LinearMap.mulLeft k a) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨δ, p, i, hδ, rfl⟩
    exact h δ p i hδ
  exact this hy

theorem e_mul_mem_subSpan (j : Seq μ) {γ : List ℕ} {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓢 γ) :
    e j * y ∈ 𝓢 γ := by
  refine mul_mem_subSpan_of_gen (fun δ p i hδ => ?_) hy
  rw [e_mul_gen]
  split_ifs
  · exact mem_subSpan hδ p i
  · exact zero_mem _

theorem ψ_mul_mem_subSpan (j : ℕ) {γ : List ℕ} {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓢 γ) :
    ψ j * y ∈ 𝓢 (j :: γ) := by
  refine mul_mem_subSpan_of_gen (fun δ p i hδ => ?_) hy
  rw [← mul_assoc, ← mul_assoc, ← ψw_cons]
  exact mem_subSpan (hδ.cons_cons j) p i

theorem ψw_mul_mem_subSpan (α : List ℕ) {γ : List ℕ} {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓢 γ) :
    ψw α * y ∈ 𝓢 (α ++ γ) := by
  induction α with
  | nil => simpa using hy
  | cons j α ih =>
    rw [ψw_cons, mul_assoc]
    exact ψ_mul_mem_subSpan j ih

theorem mul_mem_subSpan_of_mul_e_eq_smul {T : KLRAlgebra k Q μ}
    (hT : ∀ i, ∃ c : k, T * e i = c • e i) {γ : List ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ 𝓢 γ) : T * y ∈ 𝓢 γ := by
  choose c hc using hT
  have : T * y = ∑ i, c i • (e i * y) := by
    calc T * y = T * ((∑ i, e i) * y) := by rw [sum_e, one_mul]
      _ = ∑ i, (T * e i) * y := by rw [Finset.sum_mul, Finset.mul_sum]; simp only [mul_assoc]
      _ = ∑ i, c i • (e i * y) := by simp only [hc, smul_mul_assoc]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (e_mul_mem_subSpan i hy)

/-- A dot times `ψ_γ x^p 1_i` is a combination of diagrams `ψ_δ x^q 1_i`, `δ ⊆ γ`. -/
theorem x_mul_gen_mem_subSpan (γ : List ℕ) (a : Fin m) (p : MvPolynomial (Fin m) k)
    (i : Seq μ) : (x a * (ψw γ * pol p * e i) : KLRAlgebra k Q μ) ∈ 𝓢 γ := by
  induction γ generalizing a with
  | nil =>
    have := mem_subSpan (Q := Q) (List.Sublist.refl []) (X a * p) i
    simpa [mul_assoc] using this
  | cons j ρ ih =>
    have hz := mem_subSpan (Q := Q) (List.Sublist.refl ρ) p i
    have hsub : 𝓢 ρ ≤ 𝓢 (j :: ρ) := subSpan_mono (List.sublist_cons_self j ρ)
    have eq : (ψw (j :: ρ) * pol p * e i : KLRAlgebra k Q μ) =
        ψ j * (ψw ρ * pol p * e i) := by
      rw [ψw_cons]; simp only [mul_assoc]
    rw [eq]
    set z := (ψw ρ * pol p * e i : KLRAlgebra k Q μ)
    by_cases hj : j + 1 < m
    swap
    · rw [ψ_eq_zero j (by omega), zero_mul, mul_zero]
      exact zero_mem _
    obtain ⟨a, ha⟩ := a
    by_cases h1 : a = j
    · subst h1
      set T := (x ⟨a, ha⟩ * ψ a - ψ a * x ⟨a + 1, hj⟩ : KLRAlgebra k Q μ)
      have hT : ∀ i, ∃ c : k, T * e i = c • e i := fun i => by
        refine ⟨if i.lbl ⟨a, ha⟩ = i.lbl ⟨a + 1, hj⟩ then 1 else 0, ?_⟩
        rw [dot_cross_left a hj i]
        split_ifs <;> simp
      have : x ⟨a, ha⟩ * (ψ a * z) = ψ a * (x ⟨a + 1, hj⟩ * z) + T * z := by
        simp only [T, sub_mul, mul_assoc]; abel
      rw [this]
      exact add_mem (ψ_mul_mem_subSpan a (ih _)) (hsub (mul_mem_subSpan_of_mul_e_eq_smul hT hz))
    by_cases h2 : a = j + 1
    · subst h2
      set T := (ψ j * x ⟨j, by omega⟩ - x ⟨j + 1, ha⟩ * ψ j : KLRAlgebra k Q μ)
      have hT : ∀ i, ∃ c : k, T * e i = c • e i := fun i => by
        refine ⟨if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, ha⟩ then 1 else 0, ?_⟩
        rw [dot_cross_right j ha i]
        split_ifs <;> simp
      have : x ⟨j + 1, ha⟩ * (ψ j * z) = ψ j * (x ⟨j, by omega⟩ * z) - T * z := by
        simp only [T, sub_mul, mul_assoc]; abel
      rw [this]
      exact sub_mem (ψ_mul_mem_subSpan j (ih _)) (hsub (mul_mem_subSpan_of_mul_e_eq_smul hT hz))
    · rw [← mul_assoc, x_mul_ψ ⟨a, ha⟩ j h1 h2, mul_assoc]
      exact ψ_mul_mem_subSpan j (ih _)

theorem x_mul_mem_subSpan (a : Fin m) {γ : List ℕ} {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓢 γ) :
    x a * y ∈ 𝓢 γ :=
  mul_mem_subSpan_of_gen (fun δ p i hδ => subSpan_mono hδ (x_mul_gen_mem_subSpan δ a p i)) hy

theorem pol_mul_mem_subSpan (q : MvPolynomial (Fin m) k) {γ : List ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ 𝓢 γ) : pol q * y ∈ 𝓢 γ := by
  induction q using MvPolynomial.induction_on with
  | C c => rw [algHom_C, ← Algebra.smul_def]; exact Submodule.smul_mem _ c hy
  | add p q hp hq => rw [map_add, add_mul]; exact add_mem hp hq
  | mul_X p a hp => rw [mul_comm, map_mul, pol_X, mul_assoc]; exact x_mul_mem_subSpan a hp

theorem mul_mem_subSpan_of_mul_e_eq_pol {T : KLRAlgebra k Q μ}
    (hT : ∀ i, ∃ q : MvPolynomial (Fin m) k, T * e i = pol q * e i) {γ : List ℕ}
    {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓢 γ) : T * y ∈ 𝓢 γ := by
  choose q hq using hT
  have : T * y = ∑ i, pol (q i) * (e i * y) := by
    calc T * y = T * ((∑ i, e i) * y) := by rw [sum_e, one_mul]
      _ = ∑ i, (T * e i) * y := by rw [Finset.sum_mul, Finset.mul_sum]; simp only [mul_assoc]
      _ = ∑ i, pol (q i) * (e i * y) := by simp only [hq, mul_assoc]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => pol_mul_mem_subSpan _ (e_mul_mem_subSpan i hy)

theorem ψ_sq_mul_mem_subSpan (j : ℕ) {γ : List ℕ} {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓢 γ) :
    ψ j * ψ j * y ∈ 𝓢 γ := by
  by_cases h : j + 1 < m
  · refine mul_mem_subSpan_of_mul_e_eq_pol (fun i => ?_) hy
    rw [ψ_sq j h i]
    split_ifs
    · exact ⟨0, by simp⟩
    · exact ⟨_, by rw [ncEval_x₂]⟩
  · rw [ψ_eq_zero j (by omega), zero_mul, zero_mul]
    exact zero_mem _

theorem braidDiff_mul_mem_subSpan (j : ℕ) {γ : List ℕ} {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓢 γ) :
    (ψ j * ψ (j + 1) * ψ j - ψ (j + 1) * ψ j * ψ (j + 1)) * y ∈ 𝓢 γ := by
  by_cases h : j + 2 < m
  · refine mul_mem_subSpan_of_mul_e_eq_pol (fun i => ?_) hy
    rw [braid j h i]
    split_ifs
    · exact ⟨_, by rw [ncEval_x₃]⟩
    · exact ⟨0, by simp⟩
  · rw [ψ_eq_zero (j + 1) (by omega)]
    simp

end SubSpan

/-! ### The subword-refined spanning theorem -/

section StdSpan

variable (ρ : Perm (Fin (Multiset.card μ)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card μ) (ρ w) ∧ wordProd (Multiset.card μ) (ρ w) = w)

variable (Q) in
/-- The span of the standard basis elements `ψ_{ρ w} x^u 1_i` with `w ∈ X`. -/
noncomputable def stdSpan (X : Set (Perm (Fin m))) : Submodule k (KLRAlgebra k Q μ) :=
  Submodule.span k (stdElt ρ '' {b | b.2.1 ∈ X})

theorem stdSpan_mono {X Y : Set (Perm (Fin m))} (h : X ⊆ Y) :
    stdSpan Q ρ X ≤ stdSpan Q ρ Y :=
  Submodule.span_mono (Set.image_subset _ fun _ hb => h hb)

theorem std_mem_stdSpan {X : Set (Perm (Fin m))} {w : Perm (Fin m)} (hw : w ∈ X)
    (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    (ψw (ρ w) * pol p * e i : KLRAlgebra k Q μ) ∈ stdSpan Q ρ X := by
  induction p using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [show monomial u c = c • monomial u (1 : k) by rw [smul_monomial, smul_eq_mul, mul_one],
      map_smul, mul_smul_comm, smul_mul_assoc]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨(i, w, u), hw, rfl⟩)
  | add p q hp hq => rw [map_add, mul_add, add_mul]; exact add_mem hp hq

include hρ in
/-- **Subword-refined spanning.** For a valid word `γ`, the diagram `ψ_γ x^p 1_i` is a
`k`-linear combination of standard elements `ψ_{ρ w} x^u 1_i` with `w` the product of a
subword of `γ`. -/
theorem gen_mem_stdSpan (γ : List ℕ) (hγ : ValidWord m γ) (p : MvPolynomial (Fin m) k)
    (i : Seq μ) : (ψw γ * pol p * e i : KLRAlgebra k Q μ) ∈ stdSpan Q ρ (subProds m γ) := by
  induction hn : γ.length using Nat.strong_induction_on generalizing γ p i with
  | _ n ih =>
  have hsub : ∀ τ : List ℕ, τ.length < n → ValidWord m τ →
      subSpan k Q μ τ ≤ stdSpan Q ρ (subProds m τ) := by
    intro τ hτ hv
    refine Submodule.span_le.2 ?_
    rintro _ ⟨δ, q, j, hδ, rfl⟩
    exact stdSpan_mono ρ (subProds_mono hδ)
      (ih δ.length (lt_of_le_of_lt hδ.length_le hτ) δ (hv.sublist hδ) q j rfl)
  set S := subProds m γ
  set y := (pol p * e i : KLRAlgebra k Q μ)
  have hy : ∀ β : List ℕ, ψw β * y ∈ subSpan k Q μ β := fun β => by
    simpa only [y, mul_assoc] using mem_subSpan (Q := Q) (List.Sublist.refl β) p i
  -- Braid moves change `ψ_γ y` only by lower terms, which lie in `stdSpan S`.
  have hchain : ∀ ρ₁ σ₁ : List ℕ, BraidEquiv ρ₁ σ₁ → ValidWord m ρ₁ → ρ₁.length = n →
      subProds m ρ₁ ⊆ S → ψw ρ₁ * y - ψw σ₁ * y ∈ stdSpan Q ρ S := by
    intro ρ₁ σ₁ hE
    induction hE with
    | rel ρ₁ σ₁ hstep =>
      intro hv hl hS
      cases hstep with
      | comm α β hab =>
        simp only [ψw_append, ψw_cons, ψw_nil, mul_one]
        rw [ψ_mul_ψ _ _ hab, sub_self]
        exact zero_mem _
      | braid α β a =>
        have heq : ψw (α ++ [a, a + 1, a] ++ β) * y - ψw (α ++ [a + 1, a, a + 1] ++ β) * y =
            ψw α * ((ψ a * ψ (a + 1) * ψ a - ψ (a + 1) * ψ a * ψ (a + 1)) * (ψw β * y)) := by
          simp only [ψw_append, ψw_cons, ψw_nil, mul_one, mul_sub, sub_mul, mul_assoc]
        rw [heq]
        have hsl : (α ++ β).Sublist (α ++ [a, a + 1, a] ++ β) := by
          rw [List.append_assoc]
          exact (List.sublist_append_right _ _).append_left α
        have hmem := ψw_mul_mem_subSpan (Q := Q) α (braidDiff_mul_mem_subSpan a (hy β))
        refine stdSpan_mono ρ ((subProds_mono hsl).trans hS) (hsub _ ?_ (hv.sublist hsl) hmem)
        rw [← hl]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    | refl => intros; rw [sub_self]; exact zero_mem _
    | symm x₁ y₁ h ih =>
      intro hv hl hS
      have hv' : ValidWord m x₁ := (BraidEquiv.validWord_iff h).2 hv
      have := ih hv' (by rw [← hl, BraidEquiv.length_eq h]) (by
        rw [BraidEquiv.subProds_eq h hv']; exact hS)
      rw [← neg_sub]
      exact neg_mem this
    | trans ρ₁ σ₁ τ₁ h₁ _ ih₁ ih₂ =>
      intro hv hl hS
      have hv' : ValidWord m σ₁ := (BraidEquiv.validWord_iff h₁).1 hv
      have := add_mem (ih₁ hv hl hS) (ih₂ hv' (by rw [← hl, BraidEquiv.length_eq h₁]) (by
        rw [← BraidEquiv.subProds_eq h₁ hv]; exact hS))
      rwa [sub_add_sub_cancel] at this
  by_cases hred : IsReduced m γ
  · -- Matsumoto: `γ` is braid-equivalent to the chosen reduced word.
    have hE := braidEquiv_of_isReduced hred (hρ (wordProd m γ)).1 (hρ _).2.symm
    have h1 := hchain γ _ hE hγ hn subset_rfl
    have h2 := std_mem_stdSpan (Q := Q) ρ (@wordProd_mem_subProds (Multiset.card μ) γ) p i
    have := add_mem h1 h2
    rwa [mul_assoc (ψw (ρ _)), sub_add_cancel, ← mul_assoc] at this
  · -- A non-reduced word is braid-equivalent to one with a repeated letter.
    obtain ⟨τ, hE, hrep⟩ := exists_braidEquiv_hasRepeat_of_not_isReduced hγ hred
    have h1 := hchain γ τ hE hγ hn subset_rfl
    have hvτ : ValidWord m τ := (BraidEquiv.validWord_iff hE).1 hγ
    have hSτ : subProds m τ = S := (BraidEquiv.subProds_eq hE hγ).symm
    obtain ⟨α, β, a, rfl⟩ := hrep
    have heq : ψw (α ++ [a, a] ++ β) * y = ψw α * (ψ a * ψ a * (ψw β * y)) := by
      simp only [ψw_append, ψw_cons, ψw_nil, mul_one, mul_assoc]
    have hsl : (α ++ β).Sublist (α ++ [a, a] ++ β) := by
      rw [List.append_assoc]
      exact (List.sublist_append_right _ _).append_left α
    have hmem := ψw_mul_mem_subSpan (Q := Q) α (ψ_sq_mul_mem_subSpan a (hy β))
    have h2 : ψw (α ++ [a, a] ++ β) * y ∈ stdSpan Q ρ S := by
      rw [heq, ← hSτ]
      refine stdSpan_mono ρ (subProds_mono hsl) (hsub _ ?_ (hvτ.sublist hsl) hmem)
      rw [← hn, BraidEquiv.length_eq hE]
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    have := add_mem h1 h2
    rwa [sub_add_cancel, ← mul_assoc] at this

include hρ in
theorem subSpan_le_stdSpan {γ : List ℕ} (hγ : ValidWord m γ) :
    subSpan k Q μ γ ≤ stdSpan Q ρ (subProds m γ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨δ, q, j, hδ, rfl⟩
  exact stdSpan_mono ρ (subProds_mono hδ) (gen_mem_stdSpan ρ hρ δ (hγ.sublist hδ) q j)

end StdSpan

/-! ### The Mackey filtration of `R(μ)` -/

section Filtration

variable (n n'' : ℕ)

variable (k Q μ) in
/-- The Mackey filtration step `mackeyFilt n n'' c`: the `k`-span of the diagrams `ψ_γ x^p 1_i`
(`γ` a valid word) all of whose subword products `v` have `crossCount n n'' v ≤ c`, i.e. at
most `c` strands going from the bottom positions `≥ n''` to the top positions `< n`. -/
noncomputable def mackeyFilt (c : ℕ) : Submodule k (KLRAlgebra k Q μ) :=
  Submodule.span k {r | ∃ (γ : List ℕ) (p : MvPolynomial (Fin (Multiset.card μ)) k)
    (i : Seq μ), ValidWord (Multiset.card μ) γ ∧
      (∀ v ∈ subProds (Multiset.card μ) γ, crossCount n n'' v ≤ c) ∧ ψw γ * pol p * e i = r}

local notation "𝓜" => mackeyFilt k Q μ n n''

variable {n n''}

theorem mem_mackeyFilt {γ : List ℕ} (hγ : ValidWord m γ) {c : ℕ}
    (h : ∀ v ∈ subProds m γ, crossCount n n'' v ≤ c) (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    ψw γ * pol p * e i ∈ 𝓜 c :=
  Submodule.subset_span ⟨γ, p, i, hγ, h, rfl⟩

theorem mackeyFilt_mono {c c' : ℕ} (h : c ≤ c') : 𝓜 c ≤ 𝓜 c' :=
  Submodule.span_mono fun _ ⟨γ, p, i, hv, hc, hr⟩ =>
    ⟨γ, p, i, hv, fun v hv' => (hc v hv').trans h, hr⟩

theorem subSpan_le_mackeyFilt {γ : List ℕ} (hγ : ValidWord m γ) {c : ℕ}
    (h : ∀ v ∈ subProds m γ, crossCount n n'' v ≤ c) : subSpan k Q μ γ ≤ 𝓜 c := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨δ, p, i, hδ, rfl⟩
  exact mem_mackeyFilt (hγ.sublist hδ) (fun v hv => h v (subProds_mono hδ hv)) p i

/-- **The filtration steps have standard bases.** For any choice of reduced words `ρ`,
`mackeyFilt n n'' c` is spanned by the standard basis elements `ψ_{ρ w} x^u 1_i` with
`crossCount n n'' w ≤ c`. -/
theorem mackeyFilt_eq_stdSpan (hn : n ≤ m) (hn'' : n'' ≤ m)
    (ρ : Perm (Fin (Multiset.card μ)) → List ℕ)
    (hρ : ∀ w, IsReduced (Multiset.card μ) (ρ w) ∧ wordProd (Multiset.card μ) (ρ w) = w)
    (c : ℕ) : 𝓜 c = stdSpan Q ρ {w | crossCount n n'' w ≤ c} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨γ, p, i, hv, hc, rfl⟩
    exact stdSpan_mono ρ hc (gen_mem_stdSpan ρ hρ γ hv p i)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨i, w, u⟩, hw, rfl⟩
    refine mem_mackeyFilt (hρ w).1.1 (fun v hv => ?_) _ i
    have := crossCount_le_of_mem_subProds hn hn'' (hρ w).1 hv
    rw [(hρ w).2] at this
    exact this.trans hw

/-! #### Left multiplication by the top parabolic generators -/

theorem mul_mem_mackeyFilt_of_gen {a : KLRAlgebra k Q μ} {c : ℕ}
    (h : ∀ γ p i, ValidWord m γ → (∀ v ∈ subProds m γ, crossCount n n'' v ≤ c) →
      a * (ψw γ * pol p * e i) ∈ 𝓜 c)
    {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓜 c) : a * y ∈ 𝓜 c := by
  have : 𝓜 c ≤ (𝓜 c).comap (LinearMap.mulLeft k a) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨γ, p, i, hv, hc, rfl⟩
    exact h γ p i hv hc
  exact this hy

theorem e_mul_mem_mackeyFilt (j : Seq μ) {c : ℕ} {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓜 c) :
    e j * y ∈ 𝓜 c :=
  mul_mem_mackeyFilt_of_gen (fun γ p i hv hc => subSpan_le_mackeyFilt hv hc
    (e_mul_mem_subSpan j (mem_subSpan (List.Sublist.refl γ) p i))) hy

theorem eSum_mul_mem_mackeyFilt (T : Finset (Seq μ)) {c : ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ 𝓜 c) : eSum Q T * y ∈ 𝓜 c := by
  rw [eSum, Finset.sum_mul]
  exact Submodule.sum_mem _ fun j _ => e_mul_mem_mackeyFilt j hy

theorem pol_mul_mem_mackeyFilt (q : MvPolynomial (Fin m) k) {c : ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ 𝓜 c) : pol q * y ∈ 𝓜 c :=
  mul_mem_mackeyFilt_of_gen (fun γ p i hv hc => subSpan_le_mackeyFilt hv hc
    (pol_mul_mem_subSpan q (mem_subSpan (List.Sublist.refl γ) p i))) hy

/-- Left multiplication by a crossing inside one of the top blocks `[0, n)`, `[n, m)`. -/
theorem ψ_mul_mem_mackeyFilt {j : ℕ} (hj : j + 1 < n ∨ n ≤ j) {c : ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ 𝓜 c) : ψ j * y ∈ 𝓜 c := by
  refine mul_mem_mackeyFilt_of_gen (fun γ p i hv hc => ?_) hy
  by_cases hjm : j + 1 < m
  · rw [← mul_assoc, ← mul_assoc, ← ψw_cons]
    refine mem_mackeyFilt (validWord_cons.2 ⟨hjm, hv⟩) (fun v hv' => ?_) p i
    rcases mem_subProds_cons.1 hv' with h1 | ⟨v', h2, rfl⟩
    · exact hc v h1
    · rw [crossCount_sadj_mul hj]; exact hc v' h2
  · rw [ψ_eq_zero j (by omega), zero_mul]; exact zero_mem _

theorem ψw_mul_mem_mackeyFilt {α : List ℕ} (hα : ∀ j ∈ α, j + 1 < n ∨ n ≤ j) {c : ℕ}
    {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓜 c) : ψw α * y ∈ 𝓜 c := by
  induction α with
  | nil => simpa using hy
  | cons j α ih =>
    rw [ψw_cons, mul_assoc]
    exact ψ_mul_mem_mackeyFilt (hα j (by simp))
      (ih fun j' hj' => hα j' (List.mem_cons_of_mem _ hj'))

/-! #### Right multiplication by the bottom parabolic generators -/

theorem mul_mem_mackeyFilt_of_gen_right {a : KLRAlgebra k Q μ} {c : ℕ}
    (h : ∀ γ p i, ValidWord m γ → (∀ v ∈ subProds m γ, crossCount n n'' v ≤ c) →
      ψw γ * pol p * e i * a ∈ 𝓜 c)
    {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓜 c) : y * a ∈ 𝓜 c := by
  have : 𝓜 c ≤ (𝓜 c).comap (LinearMap.mulRight k a) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨γ, p, i, hv, hc, rfl⟩
    exact h γ p i hv hc
  exact this hy

theorem mul_e_mem_mackeyFilt (j : Seq μ) {c : ℕ} {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓜 c) :
    y * e j ∈ 𝓜 c := by
  refine mul_mem_mackeyFilt_of_gen_right (fun γ p i hv hc => ?_) hy
  rw [gen_mul_e]
  split_ifs
  · exact mem_mackeyFilt hv hc p i
  · exact zero_mem _

theorem mul_eSum_mem_mackeyFilt (T : Finset (Seq μ)) {c : ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ 𝓜 c) : y * eSum Q T ∈ 𝓜 c := by
  rw [eSum, Finset.mul_sum]
  exact Submodule.sum_mem _ fun j _ => mul_e_mem_mackeyFilt j hy

theorem mul_pol_mem_mackeyFilt (q : MvPolynomial (Fin m) k) {c : ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ 𝓜 c) : y * pol q ∈ 𝓜 c := by
  refine mul_mem_mackeyFilt_of_gen_right (fun γ p i hv hc => ?_) hy
  rw [mul_assoc, (e_commute_pol i q).eq, ← mul_assoc, mul_assoc (ψw γ), ← map_mul]
  exact mem_mackeyFilt hv hc _ i

/-- Right multiplication by a crossing inside one of the bottom blocks `[0, n'')`, `[n'', m)`. -/
theorem mul_ψ_mem_mackeyFilt {j : ℕ} (hj : j + 1 < n'' ∨ n'' ≤ j) {c : ℕ}
    {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓜 c) : y * ψ j ∈ 𝓜 c := by
  refine mul_mem_mackeyFilt_of_gen_right (fun γ p i hv hc => ?_) hy
  by_cases hjm : j + 1 < m
  · have he : (e i * ψ j : KLRAlgebra k Q μ) = ψ j * e (sadj m j • i) := by
      rw [ψ_mul_e, sadj_smul_smul]
    have hmem : ψw γ * (pol p * (ψw [j] * pol 1 * e (sadj m j • i))) ∈
        subSpan k Q μ (γ ++ [j]) :=
      ψw_mul_mem_subSpan γ (pol_mul_mem_subSpan p (mem_subSpan (List.Sublist.refl _) 1 _))
    have heq : (ψw γ * pol p * e i * ψ j : KLRAlgebra k Q μ) =
        ψw γ * (pol p * (ψw [j] * pol 1 * e (sadj m j • i))) := by
      simp only [ψw_cons, ψw_nil, mul_one, map_one, mul_assoc, he]
    rw [heq]
    refine subSpan_le_mackeyFilt (validWord_append.2 ⟨hv, by simp [hjm]⟩) (fun v hv' => ?_) hmem
    obtain ⟨u, hu, v', h1, rfl⟩ := mem_subProds_append.1 hv'
    rcases mem_subProds_cons.1 h1 with h2 | ⟨v'', h3, rfl⟩
    · rw [mem_subProds_nil.1 h2, mul_one]; exact hc u hu
    · rw [mem_subProds_nil.1 h3, mul_one, crossCount_mul_sadj hj]; exact hc u hu
  · rw [ψ_eq_zero j (by omega), mul_zero]; exact zero_mem _

theorem mul_ψw_mem_mackeyFilt {β : List ℕ} (hβ : ∀ j ∈ β, j + 1 < n'' ∨ n'' ≤ j) {c : ℕ}
    {y : KLRAlgebra k Q μ} (hy : y ∈ 𝓜 c) : y * ψw β ∈ 𝓜 c := by
  induction β generalizing y with
  | nil => simpa using hy
  | cons j β ih =>
    rw [ψw_cons, ← mul_assoc]
    exact ih (fun j' hj' => hβ j' (List.mem_cons_of_mem _ hj'))
      (mul_ψ_mem_mackeyFilt (hβ j (by simp)) hy)

end Filtration

/-! ### Transport along an equality of weights -/

section Cast

variable {μ₁ μ₂ : Multiset I}

/-- Sequences of weight `μ₁` as sequences of weight `μ₂`, for `μ₁ = μ₂`. -/
def seqCast (h : μ₁ = μ₂) (s : Seq μ₁) : Seq μ₂ := h ▸ s

omit [DecidableEq I] in
theorem seqCast_injective (h : μ₁ = μ₂) : Function.Injective (seqCast h) := by
  subst h; exact fun _ _ h => h

variable (Q) in
/-- The identification `R(μ₁) ≅ R(μ₂)` for `μ₁ = μ₂`. -/
noncomputable def castAlg (h : μ₁ = μ₂) : KLRAlgebra k Q μ₁ ≃ₐ[k] KLRAlgebra k Q μ₂ := by
  subst h; exact AlgEquiv.refl

theorem castAlg_ψw (h : μ₁ = μ₂) (α : List ℕ) :
    castAlg Q h (ψw α : KLRAlgebra k Q μ₁) = ψw α := by
  subst h; rfl

theorem castAlg_e (h : μ₁ = μ₂) (s : Seq μ₁) :
    castAlg Q h (e s : KLRAlgebra k Q μ₁) = e (seqCast h s) := by
  subst h; rfl

theorem castAlg_pol (h : μ₁ = μ₂) (p : MvPolynomial (Fin (Multiset.card μ₁)) k) :
    ∃ q, castAlg Q h (pol p : KLRAlgebra k Q μ₁) = pol q := by
  subst h; exact ⟨p, rfl⟩

theorem castAlg_eSum (h : μ₁ = μ₂) (T : Finset (Seq μ₁)) :
    castAlg Q h (eSum Q T) = eSum Q (T.image (seqCast h)) := by
  rw [eSum, map_sum, eSum, Finset.sum_image fun a _ b _ hab => seqCast_injective h hab]
  simp only [castAlg_e]

end Cast

/-! ### Generators of `R(ν) ⊗ R(ν')` -/

section Generators

variable {ν ν' : Multiset I}

theorem mem_span_gen (a : KLRAlgebra k Q ν) :
    a ∈ Submodule.span k {r | ∃ (α : List ℕ) (p : MvPolynomial (Fin (Multiset.card ν)) k)
      (i : Seq ν), ValidWord (Multiset.card ν) α ∧ ψw α * pol p * e i = r} := by
  have h := span_eq_top' (k := k) (Q := Q) (ν := ν) (canWord _)
    (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩)
  have ha : a ∈ Submodule.span k {r : KLRAlgebra k Q ν | ∃ (w : Perm (Fin (Multiset.card ν)))
      (u : Fin (Multiset.card ν) →₀ ℕ) (i : Seq ν),
      ψw (canWord _ w) * pol (monomial u 1) * e i = r} := by rw [h]; trivial
  refine Submodule.span_mono ?_ ha
  rintro _ ⟨w, u, i, rfl⟩
  exact ⟨_, _, i, validWord_canWord _ w, rfl⟩

/-- A `k`-linear map out of `R(ν) ⊗ R(ν')` lands in a submodule `F` as soon as the images of
the tensors of generators `ψ_α x^p 1_i` do. -/
theorem tensor_mem_of_gen {M : Type*} [AddCommGroup M] [Module k M]
    (Φ : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν' →ₗ[k] M) (F : Submodule k M)
    (hg : ∀ α p i α' p' i', ValidWord (Multiset.card ν) α → ValidWord (Multiset.card ν') α' →
      Φ ((ψw α * pol p * e i) ⊗ₜ (ψw α' * pol p' * e i')) ∈ F)
    (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') : Φ t ∈ F := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add s t hs ht => rw [map_add]; exact add_mem hs ht
  | tmul a b =>
    induction mem_span_gen (Q := Q) a using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨α, p, i, hα, rfl⟩ := hx
      induction mem_span_gen (Q := Q) b using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨α', p', i', hα', rfl⟩ := hy
        exact hg α p i α' p' i' hα hα'
      | zero => rw [TensorProduct.tmul_zero, map_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [TensorProduct.tmul_add, map_add]; exact add_mem hy hz
      | smul c y _ hy => rw [TensorProduct.tmul_smul, map_smul]; exact F.smul_mem c hy
    | zero => rw [TensorProduct.zero_tmul, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.add_tmul, map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [← TensorProduct.smul_tmul', map_smul]; exact F.smul_mem c hx

/-- `ι(ψ_α x^p 1_i ⊗ ψ_{α'} x^{p'} 1_{i'}) = ψ_{α (n + α')} x^{p p'} 1_{i i'}`. -/
theorem concat_ψw_pol_e {α α' : List ℕ} (hα : ValidWord (Multiset.card ν) α)
    (hα' : ValidWord (Multiset.card ν') α') (p : MvPolynomial (Fin (Multiset.card ν)) k)
    (p' : MvPolynomial (Fin (Multiset.card ν')) k) (i : Seq ν) (i' : Seq ν') :
    concat Q ν ν' ((ψw α * pol p * e i) ⊗ₜ (ψw α' * pol p' * e i')) =
      ψw (α ++ shiftWord (Multiset.card ν) α') *
        pol (rename (Seq.posL ν') p * rename (Seq.posR ν) p') * e (i.append i') := by
  rw [← Algebra.TensorProduct.tmul_mul_tmul, ← Algebra.TensorProduct.tmul_mul_tmul, concat_mul,
    concat_mul, concat_ψw_tmul_ψw hα hα', concat_pol_tmul_pol, concat_e_tmul_e, oneConcat]
  have h1 : (eSum Q (concatSet ν ν') * e (i.append i') : KLRAlgebra k Q (ν + ν')) =
      e (i.append i') := by rw [eSum_mul_e, if_pos (append_mem_concatSet i i')]
  simp only [mul_assoc]
  rw [h1, ← mul_assoc (eSum Q _), ← pol_mul_eSum, mul_assoc, h1]

end Generators

/-! ### The bimodule `_{ν,ν'}R_{ν'',ν'''}` and its Mackey filtration -/

section Bimodule

variable {ν ν' ν'' ν''' : Multiset I} (h : ν'' + ν''' = ν + ν')

variable (Q) in
/-- The right action `ι_{ν'',ν'''} : R(ν'') ⊗ R(ν''') → R(ν'' + ν''') = R(ν + ν')`. -/
noncomputable def botConcat :
    KLRAlgebra k Q ν'' ⊗[k] KLRAlgebra k Q ν''' →ₗ[k] KLRAlgebra k Q (ν + ν') :=
  (castAlg Q h).toLinearMap ∘ₗ concat Q ν'' ν'''

theorem botConcat_apply (t : KLRAlgebra k Q ν'' ⊗[k] KLRAlgebra k Q ν''') :
    botConcat Q h t = castAlg Q h (concat Q ν'' ν''' t) := rfl

theorem botConcat_mul (s t : KLRAlgebra k Q ν'' ⊗[k] KLRAlgebra k Q ν''') :
    botConcat Q h (s * t) = botConcat Q h s * botConcat Q h t := by
  simp only [botConcat_apply, concat_mul, map_mul]

/-- The sequences `s₁ s₂`, `s₁ ∈ Seq ν''`, `s₂ ∈ Seq ν'''`, as sequences of weight `ν + ν'`. -/
noncomputable def botSet : Finset (Seq (ν + ν')) := (concatSet ν'' ν''').image (seqCast h)

variable (Q) in
/-- The idempotent `1_{ν'',ν'''}` of `R(ν + ν')`. -/
noncomputable def botOne : KLRAlgebra k Q (ν + ν') := eSum Q (botSet h)

theorem botConcat_one : botConcat Q h 1 = botOne Q h := by
  rw [botConcat_apply, concat_one, oneConcat, castAlg_eSum]; rfl

theorem botConcat_mul_botOne (t : KLRAlgebra k Q ν'' ⊗[k] KLRAlgebra k Q ν''') :
    botConcat Q h t * botOne Q h = botConcat Q h t := by
  rw [← botConcat_one, ← botConcat_mul, mul_one]

theorem botOne_mul_botConcat (t : KLRAlgebra k Q ν'' ⊗[k] KLRAlgebra k Q ν''') :
    botOne Q h * botConcat Q h t = botConcat Q h t := by
  rw [← botConcat_one, ← botConcat_mul, one_mul]

theorem botOne_idem : IsIdempotentElem (botOne Q h) := eSum_idem _

variable (Q) in
/-- **The bimodule** `_{ν,ν'}R_{ν'',ν'''} = 1_{ν,ν'} R(ν + ν') 1_{ν'',ν'''}`. -/
noncomputable def bimod : Submodule k (KLRAlgebra k Q (ν + ν')) :=
  LinearMap.range ((LinearMap.mulLeft k (oneConcat Q ν ν')).comp
    (LinearMap.mulRight k (botOne Q h)))

theorem mem_bimod {r : KLRAlgebra k Q (ν + ν')} :
    r ∈ bimod Q h ↔ oneConcat Q ν ν' * r * botOne Q h = r := by
  constructor
  · rintro ⟨s, rfl⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, ← mul_assoc, oneConcat_idem.eq]
    rw [mul_assoc _ (botOne Q h), (botOne_idem h).eq]
  · intro hr; exact ⟨r, by simpa [mul_assoc] using hr⟩

theorem concat_mul_mem_bimod (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν')
    {r : KLRAlgebra k Q (ν + ν')} (hr : r ∈ bimod Q h) : concat Q ν ν' t * r ∈ bimod Q h := by
  rw [mem_bimod] at hr ⊢
  have hr' : r * botOne Q h = r := by rw [← hr, mul_assoc, (botOne_idem h).eq]
  rw [← mul_assoc, oneConcat_mul_concat, mul_assoc, hr']

theorem mul_botConcat_mem_bimod (t : KLRAlgebra k Q ν'' ⊗[k] KLRAlgebra k Q ν''')
    {r : KLRAlgebra k Q (ν + ν')} (hr : r ∈ bimod Q h) : r * botConcat Q h t ∈ bimod Q h := by
  rw [mem_bimod] at hr ⊢
  have hr' : oneConcat Q ν ν' * r = r := by
    rw [← hr, ← mul_assoc, ← mul_assoc, oneConcat_idem.eq]
  rw [mul_assoc, mul_assoc, botConcat_mul_botOne, ← mul_assoc, hr']

end Bimodule

/-! ### The filtration of the bimodule -/

section BimodFilt

variable {ν ν' ν'' ν''' : Multiset I} (h : ν'' + ν''' = ν + ν')

omit [DecidableEq I] in
theorem card_le_card_add_left (ν ν' : Multiset I) :
    Multiset.card ν ≤ Multiset.card (ν + ν') := by
  rw [Multiset.card_add]; exact Nat.le_add_right _ _

omit [DecidableEq I] in
include h in
theorem card_le_card_of_add_eq : Multiset.card ν'' ≤ Multiset.card (ν + ν') := by
  rw [← h, Multiset.card_add]; exact Nat.le_add_right _ _

/-- **Left action**: `ι_{ν,ν'}(R(ν) ⊗ R(ν'))` preserves each step of the Mackey filtration. -/
theorem concat_mul_mem_mackeyFilt (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') {n'' c : ℕ}
    {r : KLRAlgebra k Q (ν + ν')}
    (hr : r ∈ mackeyFilt k Q (ν + ν') (Multiset.card ν) n'' c) :
    concat Q ν ν' t * r ∈ mackeyFilt k Q (ν + ν') (Multiset.card ν) n'' c := by
  refine tensor_mem_of_gen ((LinearMap.mulRight k r) ∘ₗ concat Q ν ν') _
    (fun α p i α' p' i' hα hα' => ?_) t
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply]
  rw [concat_ψw_pol_e hα hα', mul_assoc, mul_assoc]
  refine ψw_mul_mem_mackeyFilt (fun j hj => ?_)
    (pol_mul_mem_mackeyFilt _ (e_mul_mem_mackeyFilt _ hr))
  rcases List.mem_append.1 hj with hj | hj
  · exact Or.inl (hα j hj)
  · simp only [shiftWord, List.mem_map] at hj
    obtain ⟨j', -, rfl⟩ := hj
    exact Or.inr (Nat.le_add_right _ _)

/-- **Right action**: `ι_{ν'',ν'''}(R(ν'') ⊗ R(ν'''))` preserves each step of the Mackey
filtration. -/
theorem mul_botConcat_mem_mackeyFilt (t : KLRAlgebra k Q ν'' ⊗[k] KLRAlgebra k Q ν''')
    {n c : ℕ} {r : KLRAlgebra k Q (ν + ν')}
    (hr : r ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν'') c) :
    r * botConcat Q h t ∈ mackeyFilt k Q (ν + ν') n (Multiset.card ν'') c := by
  refine tensor_mem_of_gen ((LinearMap.mulLeft k r) ∘ₗ botConcat Q h) _
    (fun α p i α' p' i' hα hα' => ?_) t
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, botConcat_apply]
  rw [concat_ψw_pol_e hα hα', map_mul, map_mul, castAlg_ψw, castAlg_e]
  obtain ⟨q, hq⟩ := castAlg_pol (Q := Q) h
    (rename (Seq.posL ν''') p * rename (Seq.posR ν'') p')
  rw [hq, ← mul_assoc, ← mul_assoc]
  refine mul_e_mem_mackeyFilt _ (mul_pol_mem_mackeyFilt _ (mul_ψw_mem_mackeyFilt
    (fun j hj => ?_) hr))
  rcases List.mem_append.1 hj with hj | hj
  · exact Or.inl (hα j hj)
  · simp only [shiftWord, List.mem_map] at hj
    obtain ⟨j', -, rfl⟩ := hj
    exact Or.inr (Nat.le_add_right _ _)

variable (Q) in
/-- **The Mackey filtration of `_{ν,ν'}R_{ν'',ν'''}`** (KL I, Proposition 2.18): the `c`-th step
is spanned by the diagrams with at most `c = |λ|` strands going from the `ν'''`-block at the
bottom to the `ν`-block at the top. -/
noncomputable def mackeyBimodFilt (c : ℕ) : Submodule k (KLRAlgebra k Q (ν + ν')) :=
  bimod Q h ⊓ mackeyFilt k Q (ν + ν') (Multiset.card ν) (Multiset.card ν'') c

theorem mackeyBimodFilt_le_bimod (c : ℕ) : mackeyBimodFilt Q h c ≤ bimod Q h := inf_le_left

theorem mackeyBimodFilt_mono {c c' : ℕ} (hc : c ≤ c') :
    mackeyBimodFilt Q h c ≤ mackeyBimodFilt Q h c' :=
  inf_le_inf_left _ (mackeyFilt_mono hc)

/-- The steps of the filtration are sub-bimodules: stable under the left action of
`R(ν) ⊗ R(ν')`. -/
theorem concat_mul_mem_mackeyBimodFilt (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') {c : ℕ}
    {r : KLRAlgebra k Q (ν + ν')} (hr : r ∈ mackeyBimodFilt Q h c) :
    concat Q ν ν' t * r ∈ mackeyBimodFilt Q h c :=
  ⟨concat_mul_mem_bimod h t hr.1, concat_mul_mem_mackeyFilt t hr.2⟩

/-- The steps of the filtration are sub-bimodules: stable under the right action of
`R(ν'') ⊗ R(ν''')`. -/
theorem mul_botConcat_mem_mackeyBimodFilt (t : KLRAlgebra k Q ν'' ⊗[k] KLRAlgebra k Q ν''')
    {c : ℕ} {r : KLRAlgebra k Q (ν + ν')} (hr : r ∈ mackeyBimodFilt Q h c) :
    r * botConcat Q h t ∈ mackeyBimodFilt Q h c :=
  ⟨mul_botConcat_mem_bimod h t hr.1, mul_botConcat_mem_mackeyFilt h t hr.2⟩

/-- The filtration is exhaustive: its step `c = card ν` is the whole bimodule. -/
theorem mackeyBimodFilt_eq_bimod {c : ℕ} (hc : Multiset.card ν ≤ c) :
    mackeyBimodFilt Q h c = bimod Q h := by
  refine le_antisymm inf_le_left fun r hr => ⟨hr, ?_⟩
  have htop : mackeyFilt k Q (ν + ν') (Multiset.card ν) (Multiset.card ν'') c = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    refine Submodule.span_mono ?_ (mem_span_gen (Q := Q) a)
    rintro _ ⟨α, p, i, hα, rfl⟩
    exact ⟨α, p, i, hα, fun v _ => (crossCount_le v (card_le_card_add_left ν ν')).trans hc, rfl⟩
  rw [htop]; trivial

/-- The filtration starts at `c = card ν - card ν''`: below, it is zero. -/
theorem mackeyBimodFilt_eq_bot {c : ℕ} (hc : c + Multiset.card ν'' < Multiset.card ν) :
    mackeyBimodFilt Q h c = ⊥ := by
  refine eq_bot_iff.2 fun r hr => ?_
  have : mackeyFilt k Q (ν + ν') (Multiset.card ν) (Multiset.card ν'') c = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨γ, p, i, -, hγ, rfl⟩
    have h1 := hγ 1 (one_mem_subProds γ)
    have h2 := le_crossCount (n := Multiset.card ν) (n'' := Multiset.card ν'') 1
      (card_le_card_add_left ν ν') (card_le_card_of_add_eq h)
    omega
  have := hr.2
  rwa [‹mackeyFilt k Q (ν + ν') _ _ c = ⊥›] at this

end BimodFilt

/-! ### Subquotients of filtrations spanned by parts of a basis -/

section Subquot

variable {ι E : Type*} [AddCommGroup E] [Module k E]

/-- If `V = span (b '' t)` and `W = span (b '' s)` for a linearly independent family `b` and
`s ⊆ t`, then `V / W` has a basis indexed by `t \ s` (the images of the `b x`, `x ∈ t \ s`). -/
noncomputable def quotBasis {b : ι → E} (hli : LinearIndependent k b) {s t : Set ι}
    (hst : s ⊆ t) (V W : Submodule k E) (hV : V = Submodule.span k (b '' t))
    (hW : W = Submodule.span k (b '' s)) :
    Basis ↥(t \ s) k (↥V ⧸ W.comap V.subtype) := by
  subst hV hW
  have hqV : Submodule.span k (b '' (t \ s)) ≤ Submodule.span k (b '' t) :=
    Submodule.span_mono (Set.image_subset _ Set.diff_subset)
  have hc : IsCompl ((Submodule.span k (b '' s)).comap (Submodule.span k (b '' t)).subtype)
      ((Submodule.span k (b '' (t \ s))).comap (Submodule.span k (b '' t)).subtype) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx hx'
      have := (hli.disjoint_span_image (Set.disjoint_sdiff_right (s := s) (t := t))).le_bot
        ⟨hx, hx'⟩
      exact Subtype.ext (by simpa using this)
    · rw [codisjoint_iff, eq_top_iff]
      rintro ⟨x, hx⟩ -
      have hx' : x ∈ Submodule.span k (b '' s) ⊔ Submodule.span k (b '' (t \ s)) := by
        rwa [← Submodule.span_union, ← Set.image_union, Set.union_diff_cancel hst]
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
      have hyV : y ∈ Submodule.span k (b '' t) :=
        Submodule.span_mono (Set.image_subset _ hst) hy
      have hzV : z ∈ Submodule.span k (b '' t) := hqV hz
      have : (⟨y + z, hx⟩ : Submodule.span k (b '' t)) = ⟨y, hyV⟩ + ⟨z, hzV⟩ := rfl
      rw [this]
      exact Submodule.add_mem_sup hy hz
  have hli' : LinearIndependent k (fun x : ↥(t \ s) => b x) := hli.comp _ Subtype.val_injective
  exact ((Basis.span hli').map
    (LinearEquiv.ofEq _ _ (congrArg (Submodule.span k) (Set.image_eq_range _ _).symm))).map
    ((Submodule.comapSubtypeEquivOfLe hqV).symm.trans
      (Submodule.quotientEquivOfIsCompl _ _ hc).symm)

theorem quotBasis_apply {b : ι → E} (hli : LinearIndependent k b) {s t : Set ι}
    (hst : s ⊆ t) (x : ↥(t \ s)) :
    quotBasis hli hst _ _ rfl rfl x =
      Submodule.Quotient.mk ⟨b x, Submodule.subset_span ⟨x, x.2.1, rfl⟩⟩ := by
  simp only [quotBasis, Basis.map_apply, LinearEquiv.trans_apply,
    Submodule.quotientEquivOfIsCompl_symm_apply]
  congr 1
  ext
  simp [Basis.span_apply]

theorem quotBasis_apply' {b : ι → E} (hli : LinearIndependent k b) {s t : Set ι}
    (hst : s ⊆ t) (V W : Submodule k E) (hV : V = Submodule.span k (b '' t))
    (hW : W = Submodule.span k (b '' s)) (x : ↥(t \ s)) :
    quotBasis hli hst V W hV hW x = Submodule.Quotient.mk
      ⟨b x, by rw [hV]; exact Submodule.subset_span ⟨x, x.2.1, rfl⟩⟩ := by
  subst hV hW
  exact quotBasis_apply hli hst x

end Subquot

/-! ### Bases adapted to the filtration -/

section StdIdx

variable {ν ν' ν'' ν''' : Multiset I} (h : ν'' + ν''' = ν + ν')

/-- Indices `(s, w, u)` of the standard elements `ψ_{ρ w} x^u 1_s` of `R(μ)`. -/
abbrev StdIdx (μ : Multiset I) : Type _ :=
  Seq μ × Perm (Fin (Multiset.card μ)) × (Fin (Multiset.card μ) →₀ ℕ)

/-- Indices of the standard elements lying in `_{ν,ν'}R_{ν'',ν'''}` (bottom sequence in
`Seq(ν'') Seq(ν''')`, top sequence in `Seq(ν) Seq(ν')`) with `|λ| ≤ c`. -/
def mackeyIdx (c : ℕ) : Set (StdIdx (ν + ν')) :=
  {b | b.1 ∈ botSet h ∧ b.2.1 • b.1 ∈ concatSet ν ν' ∧
    crossCount (Multiset.card ν) (Multiset.card ν'') b.2.1 ≤ c}

theorem mackeyIdx_mono {c c' : ℕ} (hc : c ≤ c') : mackeyIdx h c ⊆ mackeyIdx h c' :=
  fun _ hb => ⟨hb.1, hb.2.1, hb.2.2.trans hc⟩

theorem mem_mackeyIdx_diff {c : ℕ} {b : StdIdx (ν + ν')} :
    b ∈ mackeyIdx h (c + 1) \ mackeyIdx h c ↔ b.1 ∈ botSet h ∧ b.2.1 • b.1 ∈ concatSet ν ν' ∧
      crossCount (Multiset.card ν) (Multiset.card ν'') b.2.1 = c + 1 := by
  simp only [mackeyIdx, Set.mem_diff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨h1, h2, le_antisymm h3 (Nat.succ_le_of_lt (not_le.1 fun h => h4 ⟨h1, h2, h⟩))⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2, h3.le⟩, fun h => by omega⟩

variable {μ : Multiset I} (ρ : Perm (Fin (Multiset.card μ)) → List ℕ)

theorem eSum_mul_stdElt (T : Finset (Seq μ)) (b : StdIdx μ) :
    eSum Q T * stdElt ρ b =
      if wordProd (Multiset.card μ) (ρ b.2.1) • b.1 ∈ T then stdElt ρ b else 0 := by
  have hb : stdElt (Q := Q) ρ b = e (wordProd (Multiset.card μ) (ρ b.2.1) • b.1) * stdElt ρ b := by
    rw [stdElt, e_mul_gen, if_pos (inv_smul_smul _ _)]
  conv_lhs => rw [hb, ← mul_assoc, eSum_mul_e]
  split_ifs
  · exact hb.symm
  · rw [zero_mul]

theorem stdElt_mul_eSum (T : Finset (Seq μ)) (b : StdIdx μ) :
    stdElt (Q := Q) ρ b * eSum Q T = if b.1 ∈ T then stdElt ρ b else 0 := by
  rw [stdElt, mul_assoc, e_mul_eSum]
  split_ifs <;> simp

end StdIdx

section BasisSec

variable {ν ν' ν'' ν''' : Multiset I} (h : ν'' + ν''' = ν + ν')
  (ρ : Perm (Fin (Multiset.card (ν + ν'))) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card (ν + ν')) (ρ w) ∧
    wordProd (Multiset.card (ν + ν')) (ρ w) = w)

include hρ in
/-- **KL I, Proposition 2.18 (basis form).** For any choice `ρ` of reduced words, the `c`-th
step of the Mackey filtration of `_{ν,ν'}R_{ν'',ν'''}` is spanned by the standard elements
`ψ_{ρ w} x^u 1_s` lying in `_{ν,ν'}R_{ν'',ν'''}` with at most `c` strands from the
`ν'''`-block to the `ν`-block. -/
theorem mackeyBimodFilt_eq_span (c : ℕ) :
    mackeyBimodFilt Q h c = Submodule.span k (stdElt ρ '' mackeyIdx h c) := by
  have hF := mackeyFilt_eq_stdSpan (k := k) (Q := Q) (card_le_card_add_left ν ν')
    (card_le_card_of_add_eq h) ρ hρ c
  apply le_antisymm
  · rintro r ⟨hr1, hr2⟩
    rw [hF] at hr2
    rw [← (mem_bimod h).1 hr1]
    let L : KLRAlgebra k Q (ν + ν') →ₗ[k] KLRAlgebra k Q (ν + ν') :=
      (LinearMap.mulLeft k (oneConcat Q ν ν')).comp (LinearMap.mulRight k (botOne Q h))
    have hle : stdSpan Q ρ {w | crossCount (Multiset.card ν) (Multiset.card ν'') w ≤ c} ≤
        (Submodule.span k (stdElt ρ '' mackeyIdx h c)).comap L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      simp only [L, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      rw [botOne, stdElt_mul_eSum, oneConcat]
      split_ifs with h1
      · rw [eSum_mul_stdElt, (hρ b.2.1).2]
        split_ifs with h2
        · exact Submodule.subset_span ⟨b, ⟨h1, h2, hb⟩, rfl⟩
        · exact zero_mem _
      · rw [mul_zero]; exact zero_mem _
    have := hle hr2
    simpa [L, mul_assoc] using this
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, ⟨h1, h2, h3⟩, rfl⟩
    refine ⟨(mem_bimod h).2 ?_, ?_⟩
    · rw [botOne, mul_assoc, stdElt_mul_eSum, if_pos h1, oneConcat, eSum_mul_stdElt,
        (hρ b.2.1).2, if_pos h2]
    · rw [hF]
      exact Submodule.subset_span ⟨b, h3, rfl⟩

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

/-- **KL I, Proposition 2.18 (basis of the filtration steps).** A `k`-basis of the `c`-th step
of the Mackey filtration of `_{ν,ν'}R_{ν'',ν'''}`, by standard elements `ψ_{ρ w} x^u 1_s`. -/
noncomputable def mackeyBasis (c : ℕ) : Basis (mackeyIdx h c) k (mackeyBimodFilt Q h c) :=
  (Basis.span ((linearIndependent_stdElt hPQ hP ρ hρ).comp _ Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ ((congrArg (Submodule.span k) (Set.image_eq_range _ _).symm).trans
      (mackeyBimodFilt_eq_span h ρ hρ c).symm))

theorem mackeyBasis_apply (c : ℕ) (b : mackeyIdx h c) :
    (mackeyBasis h ρ hρ hPQ hP c b : KLRAlgebra k Q (ν + ν')) = stdElt ρ b.1 := by
  simp [mackeyBasis, Basis.span_apply]

/-- **KL I, Proposition 2.18 (subquotients).** The subquotient
`F_{c+1} / F_c` of the Mackey filtration of `_{ν,ν'}R_{ν'',ν'''}` has a `k`-basis given by the
classes of the standard elements `ψ_{ρ w} x^u 1_s` of `_{ν,ν'}R_{ν'',ν'''}` with exactly
`|λ| = c + 1` strands from the `ν'''`-block to the `ν`-block (`mem_mackeyIdx_diff`). -/
noncomputable def mackeySubquotBasis (c : ℕ) :
    Basis ↥(mackeyIdx h (c + 1) \ mackeyIdx h c) k
      (↥(mackeyBimodFilt Q h (c + 1)) ⧸
        (mackeyBimodFilt Q h c).comap (mackeyBimodFilt Q h (c + 1)).subtype) :=
  quotBasis (linearIndependent_stdElt hPQ hP ρ hρ) (mackeyIdx_mono h (Nat.le_succ c)) _ _
    (mackeyBimodFilt_eq_span h ρ hρ (c + 1)) (mackeyBimodFilt_eq_span h ρ hρ c)

theorem mackeySubquotBasis_apply (c : ℕ) (b : ↥(mackeyIdx h (c + 1) \ mackeyIdx h c)) :
    ∃ hb, mackeySubquotBasis h ρ hρ hPQ hP c b =
      Submodule.Quotient.mk (⟨stdElt ρ b.1, hb⟩ : mackeyBimodFilt Q h (c + 1)) :=
  ⟨_, quotBasis_apply' _ _ _ _ _ _ b⟩

end BasisSec

/-! ### Mackey-adapted reduced words: the basis elements `ι(b ⊗ b') ψ_d ι(c ⊗ c')` -/

section MackeyWords

variable {ν ν' ν'' ν''' : Multiset I} (h : ν'' + ν''' = ν + ν')

omit [DecidableEq I] in
include h in
theorem card_add_bot : Multiset.card ν'' + Multiset.card ν''' = Multiset.card (ν + ν') :=
  (Seq.card_add' ν'' ν''').trans (congrArg Multiset.card h)

theorem castAlg_pol_monomial {μ₁ μ₂ : Multiset I} (h : μ₁ = μ₂)
    (u : Fin (Multiset.card μ₂) →₀ ℕ) :
    ∃ u' : Fin (Multiset.card μ₁) →₀ ℕ,
      castAlg Q h (pol (monomial u' 1) : KLRAlgebra k Q μ₁) = pol (monomial u 1) := by
  subst h; exact ⟨u, rfl⟩

omit [DecidableEq I] in
theorem exists_mackeyFactor (w : Perm (Fin (Multiset.card (ν + ν')))) :
    ∃ x : Perm (Fin (Multiset.card ν)) × Perm (Fin (Multiset.card ν')) ×
        Perm (Fin (Multiset.card (ν + ν'))) × Perm (Fin (Multiset.card ν'')) ×
        Perm (Fin (Multiset.card ν''')),
      IsDoubleShuffle (Seq.card_add' ν ν') (card_add_bot h) x.2.2.1 ∧
      w = blockPerm (Seq.card_add' ν ν') x.1 x.2.1 * x.2.2.1 *
        blockPerm (card_add_bot h) x.2.2.2.1 x.2.2.2.2 ∧
      length _ w = length _ x.1 + length _ x.2.1 + length _ x.2.2.1 +
        (length _ x.2.2.2.1 + length _ x.2.2.2.2) := by
  obtain ⟨a, b, d, y, y', h1, h2, h3⟩ :=
    mackey_factorisation (Seq.card_add' ν ν') (card_add_bot h) w
  exact ⟨(a, b, d, y, y'), h1, h2, h3⟩

/-- A chosen Mackey factorisation `w = (a × b) d (y × y')` (`TypeA.mackey_factorisation`). -/
noncomputable def mackeyFactor (w : Perm (Fin (Multiset.card (ν + ν')))) :
    Perm (Fin (Multiset.card ν)) × Perm (Fin (Multiset.card ν')) ×
      Perm (Fin (Multiset.card (ν + ν'))) × Perm (Fin (Multiset.card ν'')) ×
      Perm (Fin (Multiset.card ν''')) :=
  Classical.choose (exists_mackeyFactor (ν := ν) (ν' := ν') h w)

omit [DecidableEq I] in
theorem mackeyFactor_spec (w : Perm (Fin (Multiset.card (ν + ν')))) :
    IsDoubleShuffle (Seq.card_add' ν ν') (card_add_bot h) (mackeyFactor h w).2.2.1 ∧
      w = blockPerm (Seq.card_add' ν ν') (mackeyFactor h w).1 (mackeyFactor h w).2.1 *
        (mackeyFactor h w).2.2.1 *
        blockPerm (card_add_bot h) (mackeyFactor h w).2.2.2.1 (mackeyFactor h w).2.2.2.2 ∧
      length _ w = length _ (mackeyFactor h w).1 + length _ (mackeyFactor h w).2.1 +
        length _ (mackeyFactor h w).2.2.1 +
        (length _ (mackeyFactor h w).2.2.2.1 + length _ (mackeyFactor h w).2.2.2.2) :=
  Classical.choose_spec (exists_mackeyFactor (ν := ν) (ν' := ν') h w)

variable (ρ₁ : Perm (Fin (Multiset.card ν)) → List ℕ) (ρ₂ : Perm (Fin (Multiset.card ν')) → List ℕ)
  (σ : Perm (Fin (Multiset.card (ν + ν'))) → List ℕ)
  (ρ₃ : Perm (Fin (Multiset.card ν'')) → List ℕ) (ρ₄ : Perm (Fin (Multiset.card ν''')) → List ℕ)

/-- The Mackey-adapted reduced word `ρ₁(a) (n + ρ₂(b)) σ(d) ρ₃(y) (n'' + ρ₄(y'))` of
`w = (a × b) d (y × y')`. -/
noncomputable def mackeyWord (w : Perm (Fin (Multiset.card (ν + ν')))) : List ℕ :=
  ρ₁ (mackeyFactor h w).1 ++ shiftWord (Multiset.card ν) (ρ₂ (mackeyFactor h w).2.1) ++
    σ (mackeyFactor h w).2.2.1 ++
    (ρ₃ (mackeyFactor h w).2.2.2.1 ++
      shiftWord (Multiset.card ν'') (ρ₄ (mackeyFactor h w).2.2.2.2))

variable
  (hρ₁ : ∀ a, IsReduced (Multiset.card ν) (ρ₁ a) ∧ wordProd (Multiset.card ν) (ρ₁ a) = a)
  (hρ₂ : ∀ b, IsReduced (Multiset.card ν') (ρ₂ b) ∧ wordProd (Multiset.card ν') (ρ₂ b) = b)
  (hσ : ∀ d, IsReduced (Multiset.card (ν + ν')) (σ d) ∧
    wordProd (Multiset.card (ν + ν')) (σ d) = d)
  (hρ₃ : ∀ y, IsReduced (Multiset.card ν'') (ρ₃ y) ∧ wordProd (Multiset.card ν'') (ρ₃ y) = y)
  (hρ₄ : ∀ y, IsReduced (Multiset.card ν''') (ρ₄ y) ∧ wordProd (Multiset.card ν''') (ρ₄ y) = y)

omit [DecidableEq I] in
include hρ₁ hρ₂ hσ hρ₃ hρ₄ in
theorem mackeyWord_spec (w : Perm (Fin (Multiset.card (ν + ν')))) :
    IsReduced (Multiset.card (ν + ν')) (mackeyWord h ρ₁ ρ₂ σ ρ₃ ρ₄ w) ∧
      wordProd (Multiset.card (ν + ν')) (mackeyWord h ρ₁ ρ₂ σ ρ₃ ρ₄ w) = w := by
  obtain ⟨-, hw, hl⟩ := mackeyFactor_spec h w
  have hJ := Seq.card_add' ν ν'
  have hK := card_add_bot h
  have hv : ValidWord (Multiset.card (ν + ν')) (mackeyWord h ρ₁ ρ₂ σ ρ₃ ρ₄ w) := by
    simp only [mackeyWord, validWord_append]
    refine ⟨⟨⟨(hρ₁ _).1.1.of_le (by omega), (hρ₂ _).1.1.shiftWord hJ⟩, (hσ _).1.1⟩,
      (hρ₃ _).1.1.of_le (by omega), (hρ₄ _).1.1.shiftWord hK⟩
  have hprod : wordProd (Multiset.card (ν + ν')) (mackeyWord h ρ₁ ρ₂ σ ρ₃ ρ₄ w) = w := by
    simp only [mackeyWord, wordProd_append]
    rw [← wordProd_append, wordProd_append_shiftWord hJ (hρ₁ _).1.1 (hρ₂ _).1.1,
      ← wordProd_append, wordProd_append_shiftWord hK (hρ₃ _).1.1 (hρ₄ _).1.1,
      (hρ₁ _).2, (hρ₂ _).2, (hσ _).2, (hρ₃ _).2, (hρ₄ _).2, ← hw]
  refine ⟨(isReduced_iff_length_le hv).2 ?_, hprod⟩
  rw [hprod, hl]
  simp only [mackeyWord, List.length_append, length_shiftWord, (hρ₁ _).1.2, (hρ₂ _).1.2,
    (hσ _).1.2, (hρ₃ _).1.2, (hρ₄ _).1.2, (hρ₁ _).2, (hρ₂ _).2, (hσ _).2, (hρ₃ _).2,
    (hρ₄ _).2]
  omega

include hρ₁ hρ₂ hσ hρ₃ hρ₄ in
/-- **Explicit form of the basis of KL I, Proposition 2.18.** With the Mackey-adapted reduced
words, every standard basis element `ψ_w x^u 1_s` of `_{ν,ν'}R_{ν'',ν'''}` is of the form
`ι(ψ_a 1_i ⊗ ψ_b 1_j) · ψ_d · ι''(ψ_y x^{u₁} 1_{s₁} ⊗ ψ_{y'} x^{u₂} 1_{s₂})`
with `d` a minimal double coset representative having the same `|λ|` as `w`. -/
theorem stdElt_mackeyWord (b : StdIdx (ν + ν')) (hb1 : b.1 ∈ botSet h)
    (hb2 : b.2.1 • b.1 ∈ concatSet ν ν') :
    ∃ (a : Perm (Fin (Multiset.card ν))) (b' : Perm (Fin (Multiset.card ν')))
      (d : Perm (Fin (Multiset.card (ν + ν')))) (y : Perm (Fin (Multiset.card ν'')))
      (y' : Perm (Fin (Multiset.card ν'''))) (i : Seq ν) (j : Seq ν') (s₁ : Seq ν'')
      (s₂ : Seq ν''') (u₁ : Fin (Multiset.card ν'') →₀ ℕ) (u₂ : Fin (Multiset.card ν''') →₀ ℕ),
      IsDoubleShuffle (Seq.card_add' ν ν') (card_add_bot h) d ∧
      crossCount (Multiset.card ν) (Multiset.card ν'') d =
        crossCount (Multiset.card ν) (Multiset.card ν'') b.2.1 ∧
      stdElt (Q := Q) (mackeyWord h ρ₁ ρ₂ σ ρ₃ ρ₄) b =
        concat Q ν ν' ((ψw (ρ₁ a) * e i) ⊗ₜ (ψw (ρ₂ b') * e j)) * ψw (σ d) *
          botConcat Q h ((ψw (ρ₃ y) * pol (monomial u₁ 1) * e s₁) ⊗ₜ
            (ψw (ρ₄ y') * pol (monomial u₂ 1) * e s₂)) := by
  obtain ⟨s, w, u⟩ := b
  obtain ⟨hds, hw, -⟩ := mackeyFactor_spec h w
  set x := mackeyFactor h w with hx
  obtain ⟨a, b', d, y, y'⟩ := x
  have hJ := Seq.card_add' ν ν'
  have hK := card_add_bot h
  -- the bottom sequence
  obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.1 hb1
  obtain ⟨s₁, s₂, rfl⟩ := mem_concatSet.1 hs₀
  -- the bottom dots
  obtain ⟨u', hu'⟩ := castAlg_pol_monomial (Q := Q) h u
  obtain ⟨⟨u₁, u₂⟩, rfl⟩ := (expEquiv ν'' ν''').surjective u'
  -- the top sequences
  obtain ⟨i₀, j₀, hij⟩ := mem_concatSet.1 hb2
  refine ⟨a, b', d, y, y', a⁻¹ • i₀, b'⁻¹ • j₀, s₁, s₂, u₁, u₂, hds, ?_, ?_⟩
  · simp only at hw ⊢
    rw [hw, crossCount_mul_blockPerm, crossCount_blockPerm_mul]
  have ht : (a⁻¹ • i₀).append (b'⁻¹ • j₀) =
      (d * blockPerm hK y y') • seqCast h (s₁.append s₂) := by
    simp only at hw hij ⊢
    rw [← Seq.blockPerm_smul_append, ← blockPerm_inv, hij, hw, ← mul_smul]
    simp only [mul_assoc, inv_mul_cancel_left]
  have htop : concat Q ν ν' ((ψw (ρ₁ a) * e (a⁻¹ • i₀)) ⊗ₜ (ψw (ρ₂ b') * e (b'⁻¹ • j₀))) =
      ψw (ρ₁ a ++ shiftWord (Multiset.card ν) (ρ₂ b')) * e ((a⁻¹ • i₀).append (b'⁻¹ • j₀)) := by
    have := concat_ψw_pol_e (Q := Q) (hρ₁ a).1.1 (hρ₂ b').1.1 1 1 (a⁻¹ • i₀) (b'⁻¹ • j₀)
    simpa only [map_one, mul_one] using this
  have hbot : botConcat Q h ((ψw (ρ₃ y) * pol (monomial u₁ 1) * e s₁) ⊗ₜ
      (ψw (ρ₄ y') * pol (monomial u₂ 1) * e s₂)) =
      ψw (ρ₃ y ++ shiftWord (Multiset.card ν'') (ρ₄ y')) * pol (monomial u 1) *
        e (seqCast h (s₁.append s₂)) := by
    rw [botConcat_apply, concat_ψw_pol_e (hρ₃ y).1.1 (hρ₄ y').1.1, ← monomial_expEquiv,
      map_mul, map_mul, castAlg_ψw, castAlg_e, hu']
  rw [htop, hbot, stdElt]
  simp only [mackeyWord, ← hx]
  have hwd : wordProd (Multiset.card (ν + ν')) (σ d ++ (ρ₃ y ++ shiftWord (Multiset.card ν'')
      (ρ₄ y'))) = d * blockPerm hK y y' := by
    rw [wordProd_append, wordProd_append_shiftWord hK (hρ₃ y).1.1 (hρ₄ y').1.1, (hσ d).2,
      (hρ₃ y).2, (hρ₄ y').2]
  have hmid := e_mul_gen (Q := Q) ((a⁻¹ • i₀).append (b'⁻¹ • j₀))
    (σ d ++ (ρ₃ y ++ shiftWord (Multiset.card ν'') (ρ₄ y'))) (monomial u 1)
    (seqCast h (s₁.append s₂))
  rw [if_pos (by rw [hwd, ht, inv_smul_smul])] at hmid
  simp only [ψw_append, mul_assoc] at hmid ⊢
  rw [hmid]

end MackeyWords

/-! ### The filtration steps are generated by the crossing diagrams `ψ_d` -/

section Crossings

variable {ν ν' ν'' ν''' : Multiset I} (h : ν'' + ν''' = ν + ν')
  (σ : Perm (Fin (Multiset.card (ν + ν'))) → List ℕ)
  (hσ : ∀ d, IsReduced (Multiset.card (ν + ν')) (σ d) ∧
    wordProd (Multiset.card (ν + ν')) (σ d) = d)

include h hσ in
/-- The crossing diagram `ψ_d` of a permutation `d` lies in the `crossCount d`-th step of the
Mackey filtration of `R(ν + ν')`. -/
theorem ψw_mem_mackeyFilt (d : Perm (Fin (Multiset.card (ν + ν')))) {c : ℕ}
    (hc : crossCount (Multiset.card ν) (Multiset.card ν'') d ≤ c) :
    (ψw (σ d) : KLRAlgebra k Q (ν + ν')) ∈
      mackeyFilt k Q (ν + ν') (Multiset.card ν) (Multiset.card ν'') c := by
  have : (ψw (σ d) : KLRAlgebra k Q (ν + ν')) = ∑ i, ψw (σ d) * pol 1 * e i := by
    rw [← Finset.mul_sum, sum_e, map_one, mul_one, mul_one]
  rw [this]
  refine Submodule.sum_mem _ fun i _ => mem_mackeyFilt (hσ d).1.1 (fun v hv => ?_) 1 i
  have := crossCount_le_of_mem_subProds (card_le_card_add_left ν ν')
    (card_le_card_of_add_eq h) (hσ d).1 hv
  rw [(hσ d).2] at this
  exact this.trans hc

include hσ in
/-- **KL I, Proposition 2.18 (generators).** Over any commutative ring, the `c`-th step of the
Mackey filtration of `_{ν,ν'}R_{ν'',ν'''}` is spanned by the diagrams
`ι_{ν,ν'}(t) · ψ_d · ι_{ν'',ν'''}(t')`, `d` running over the minimal double coset
representatives with `|λ| ≤ c`. By `TypeA.IsDoubleShuffle.eq_of_crossCount_eq` there is at
most one such `d` for each value of `|λ|`; so the subquotient of index `c` is generated as a
bimodule by the image of the single crossing diagram `ψ_{d_c}` (the diagram of the proof of
Proposition 2.18). -/
theorem mackeyBimodFilt_eq_span_crossings (c : ℕ) :
    mackeyBimodFilt Q h c = Submodule.span k {r | ∃ (d : Perm (Fin (Multiset.card (ν + ν'))))
      (t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν')
      (t' : KLRAlgebra k Q ν'' ⊗[k] KLRAlgebra k Q ν'''),
      IsDoubleShuffle (Seq.card_add' ν ν') (card_add_bot h) d ∧
      crossCount (Multiset.card ν) (Multiset.card ν'') d ≤ c ∧
      concat Q ν ν' t * ψw (σ d) * botConcat Q h t' = r} := by
  have hc1 : ∀ n (w : Perm (Fin n)), IsReduced n (canWord n w) ∧ wordProd n (canWord n w) = w :=
    fun n w => ⟨isReduced_canWord n w, wordProd_canWord n w⟩
  apply le_antisymm
  · rw [mackeyBimodFilt_eq_span h _ (mackeyWord_spec h (canWord _) (canWord _) σ (canWord _)
      (canWord _) (hc1 _) (hc1 _) hσ (hc1 _) (hc1 _))]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, ⟨h1, h2, h3⟩, rfl⟩
    obtain ⟨a, b', d, y, y', i, j, s₁, s₂, u₁, u₂, hd, hcd, heq⟩ := stdElt_mackeyWord (Q := Q) h
      (canWord _) (canWord _) σ (canWord _) (canWord _) (hc1 _) (hc1 _) hσ (hc1 _) (hc1 _) b h1 h2
    exact Submodule.subset_span ⟨d, _, _, hd, hcd ▸ h3, heq.symm⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨d, t, t', -, hdc, rfl⟩
    refine ⟨(mem_bimod h).2 ?_, ?_⟩
    · rw [← mul_assoc, ← mul_assoc, oneConcat_mul_concat, mul_assoc _ (botConcat Q h t'),
        botConcat_mul_botOne]
    · exact mul_botConcat_mem_mackeyFilt h t' (concat_mul_mem_mackeyFilt t
        (ψw_mem_mackeyFilt h σ hσ d hdc))

end Crossings

end KLRAlgebra

/-! ### The case of KL I -/

namespace KL1

open KLRAlgebra

variable {Γ : SimpleGraph I} [DecidableRel Γ.Adj] [IsDomain k] {ν ν' ν'' ν''' : Multiset I}
  (h : ν'' + ν''' = ν + ν')
  (ρ : Perm (Fin (Multiset.card (ν + ν'))) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card (ν + ν')) (ρ w) ∧
    wordProd (Multiset.card (ν + ν')) (ρ w) = w)

/-- **KL I, Proposition 2.18** for the rings `R(ν)` of a simple graph `Γ` (over `ℤ`, or any
integral domain): the subquotient `F_{c+1} / F_c` of the Mackey filtration of
`_{ν,ν'}R_{ν'',ν'''}` has the basis of classes of the standard elements `ψ_{ρ w} x^u 1_s` of
`_{ν,ν'}R_{ν'',ν'''}` with `|λ| = c + 1`. -/
noncomputable def mackeySubquotBasis (c : ℕ) :
    Basis ↥(mackeyIdx h (c + 1) \ mackeyIdx h c) k
      (↥(mackeyBimodFilt (klQ (k := k) Γ) h (c + 1)) ⧸
        (mackeyBimodFilt (klQ (k := k) Γ) h c).comap
          (mackeyBimodFilt (klQ (k := k) Γ) h (c + 1)).subtype) :=
  KLRAlgebra.mackeySubquotBasis h ρ hρ (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b) c

/-- **KL I, Proposition 2.18** (the filtration steps) for the rings `R(ν)` of a simple graph. -/
noncomputable def mackeyBasis (c : ℕ) :
    Basis (mackeyIdx h c) k (mackeyBimodFilt (klQ (k := k) Γ) h c) :=
  KLRAlgebra.mackeyBasis h ρ hρ (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b) c

end KL1

end Categorification.KLR
