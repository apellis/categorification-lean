/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.PolyRep.Defs
import Categorification.Algebra.PermExpansion

/-!
# Linear independence of the operators `ψ̂_w x^u 1_i` on `Pol_ν`

This file proves the independence half of KL I (arXiv:0803.4121v2), Theorem 2.5 at the
level of the polynomial representation: for an integral domain `k`, polynomials
`P i j ≠ 0` (`i ≠ j`), and any choice `ρ w` of reduced words for the permutations `w`,
the operators

  `ψ_{ρ w} ∘ x^u ∘ 1_i`, `i ∈ Seq ν`, `w ∈ S_m`, `u ∈ ℕ^m`

acting on `Pol_ν` are linearly independent over `k` (`linearIndependent_opΨw`).

## Method

Every operator involved maps the component `Pol_i` to a single component, and the
component maps have expansions `∑_v g v · v` in the skew group ring `Frac(k[x]) ⋊ S_m`
(`Categorification.PermExpansion`): the crossing `ψ_j` on `Pol_t` has expansion
`(x_j - x_{j+1})⁻¹ (1 - s_j)` if `t_j = t_{j+1}` and `P(x_j, x_{j+1}) s_j` otherwise
(`hasExp_crossComp`). For a word `ρ` the expansion `wordExp P ρ i` of the component of
`ψ_ρ` is supported on `{wordProd ρ} ∪ {v | ℓ(v) < |ρ|}` (`wordExp_support`), and if `ρ` is
reduced its coefficient at `wordProd ρ` is nonzero (`wordExp_top_ne_zero`). Expansions
are unique (Dedekind), so in a vanishing linear combination the coefficient at a
permutation `w₀` of maximal length only involves the terms with `w = w₀`, which forces
their coefficients to vanish.

## Main definitions

* `opΨw P ρ` : the operator `ψ_{ρ₀} ∘ ψ_{ρ₁} ∘ ⋯` of a word `ρ`.
* `mulMono u` : multiplication by the monomial `x^u` in every component.
* `wordComp P ρ i` : the component `Pol_i → Pol_{wordProd ρ • i}` of `opΨw P ρ`.
* `crossExp`, `wordExp` : expansions of `crossComp` and `wordComp`.

## Main results

* `opΨw_single` : `opΨw P ρ` maps `Pol_i` to `Pol_{wordProd ρ • i}` via `wordComp`.
* `hasExp_crossComp`, `hasExp_wordComp` : the expansions.
* `wordExp_support`, `wordExp_top_ne_zero` : triangularity.
* `opΨw_family_coeff_eq_zero`, `linearIndependent_opΨw` : linear independence.
-/

namespace Categorification.KLR.PolyRep

open MvPolynomial TypeA Equiv PermExpansion

/-! ### Auxiliary facts about lengths of permutations -/

namespace Indep

theorem exists_word_length (n : ℕ) (w : Perm (Fin n)) :
    ∃ ρ, ValidWord n ρ ∧ wordProd n ρ = w ∧ ρ.length = length n w := by
  classical
  unfold length
  exact Nat.find_spec
    (p := fun l => ∃ ρ, ValidWord n ρ ∧ wordProd n ρ = w ∧ ρ.length = l) _

theorem length_le_of_valid {n : ℕ} {ρ : List ℕ} (hv : ValidWord n ρ) :
    length n (wordProd n ρ) ≤ ρ.length := by
  classical
  unfold length
  exact Nat.find_min' _ ⟨ρ, hv, rfl, rfl⟩

theorem wordProd_cons' (n j : ℕ) (ρ : List ℕ) :
    wordProd n (j :: ρ) = sadj n j * wordProd n ρ := by
  simp [wordProd]

theorem sadj_eq_one {n j : ℕ} (h : ¬ j + 1 < n) : sadj n j = 1 := by
  simp [sadj, h]

theorem sadj_eq_swap {n j : ℕ} (h : j + 1 < n) :
    sadj n j = swap ⟨j, by omega⟩ ⟨j + 1, h⟩ := by
  simp [sadj, h]

theorem sadj_sq (n j : ℕ) : sadj n j * sadj n j = 1 := by
  by_cases h : j + 1 < n
  · rw [sadj_eq_swap h, swap_mul_self]
  · rw [sadj_eq_one h, one_mul]

theorem sadj_ne_one {n j : ℕ} (h : j + 1 < n) : sadj n j ≠ 1 := by
  rw [sadj_eq_swap h, Ne, swap_eq_one_iff, Fin.ext_iff]
  simp

/-- `ℓ(s_j w) ≤ ℓ(w) + 1`. -/
theorem length_sadj_mul_le (n j : ℕ) (w : Perm (Fin n)) :
    length n (sadj n j * w) ≤ length n w + 1 := by
  obtain ⟨ρ, hv, hw, hl⟩ := exists_word_length n w
  by_cases h : j + 1 < n
  · have hv' : ValidWord n (j :: ρ) := by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      exacts [h, hv x hx]
    have := length_le_of_valid hv'
    rw [wordProd_cons', hw] at this
    simpa [hl] using this
  · rw [sadj_eq_one h, one_mul]; omega

/-- `ℓ(wordProd ρ) ≤ |ρ|` for every word `ρ`. -/
theorem length_wordProd_le (n : ℕ) (ρ : List ℕ) : length n (wordProd n ρ) ≤ ρ.length := by
  induction ρ with
  | nil => exact length_le_of_valid (ρ := []) (by simp [ValidWord])
  | cons j ρ ih =>
    rw [wordProd_cons']
    have := length_sadj_mul_le n j (wordProd n ρ)
    simp only [List.length_cons]
    omega

/-- The tail of a reduced word is reduced, and the head letter increases the length. -/
theorem isReduced_tail {n j : ℕ} {ρ : List ℕ} (h : IsReduced n (j :: ρ)) :
    IsReduced n ρ ∧ length n (sadj n j * wordProd n ρ) = ρ.length + 1 := by
  have hl := h.2
  rw [wordProd_cons', List.length_cons] at hl
  have hv : ValidWord n ρ := fun x hx => h.1 x (List.mem_cons_of_mem _ hx)
  have h1 := length_le_of_valid hv
  have h2 := length_sadj_mul_le n j (wordProd n ρ)
  exact ⟨⟨hv, by omega⟩, hl.symm⟩

end Indep

open Indep

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ν : Multiset I}

local notation "m" => Multiset.card ν

/-! ### Word operators and their components -/

/-- The operator `ψ_{ρ₀} ∘ ψ_{ρ₁} ∘ ⋯ ∘ ψ_{ρ_{r-1}}` of a word `ρ` (the leftmost letter is
applied last). -/
noncomputable def opΨw (P : I → I → MvPolynomial (Fin 2) k) (ρ : List ℕ) :
    Module.End k (Pol k ν) :=
  (ρ.map (opΨ P)).prod

/-- Multiplication by the monomial `x^u` in every component. -/
noncomputable def mulMono (u : Fin m →₀ ℕ) : Module.End k (Pol k ν) :=
  LinearMap.pi fun j => (LinearMap.mulLeft k (monomial u (1 : k))).comp (LinearMap.proj j)

omit [DecidableEq I] in
@[simp] theorem mulMono_apply (u : Fin m →₀ ℕ) (f : Pol k ν) (t : Seq ν) :
    mulMono u f t = monomial u 1 * f t := rfl

theorem opΨw_nil (P : I → I → MvPolynomial (Fin 2) k) : opΨw (ν := ν) P [] = 1 := rfl

theorem opΨw_cons (P : I → I → MvPolynomial (Fin 2) k) (j : ℕ) (ρ : List ℕ) :
    opΨw (ν := ν) P (j :: ρ) = opΨ P j * opΨw P ρ := by
  simp [opΨw]

/-- The component of `opΨw P ρ` from `Pol_i` to `Pol_{wordProd ρ • i}`. -/
noncomputable def wordComp (P : I → I → MvPolynomial (Fin 2) k) :
    List ℕ → Seq ν → (MvPolynomial (Fin m) k →ₗ[k] MvPolynomial (Fin m) k)
  | [], _ => LinearMap.id
  | j :: ρ, i =>
    if h : j + 1 < m then (crossComp P j h (wordProd m ρ • i)).comp (wordComp P ρ i) else 0

/-- `opΨw P ρ` maps the component `Pol_i` to `Pol_{wordProd ρ • i}` by `wordComp P ρ i`. -/
theorem opΨw_single (P : I → I → MvPolynomial (Fin 2) k) (ρ : List ℕ) (i : Seq ν)
    (f : MvPolynomial (Fin m) k) :
    opΨw P ρ (Pi.single i f) = Pi.single (wordProd m ρ • i) (wordComp P ρ i f) := by
  induction ρ with
  | nil => simp [opΨw_nil, wordComp, wordProd]
  | cons j ρ ih =>
    rw [opΨw_cons, Module.End.mul_apply, ih, wordProd_cons', mul_smul]
    by_cases h : j + 1 < m
    · simp only [wordComp, dif_pos h, LinearMap.comp_apply]
      funext t
      rw [opΨ_apply P j h]
      by_cases ht : t = sadj m j • wordProd m ρ • i
      · subst ht
        rw [smul_smul, sadj_sq, one_smul]
        simp
      · have : sadj m j • t ≠ wordProd m ρ • i := fun h' =>
          ht (by rw [← h', smul_smul, sadj_sq, one_smul])
        simp [Pi.single_apply, ht, this]
    · simp [wordComp, dif_neg h, opΨ, h]

/-! ### Expansions -/

section Expansion

variable [IsDomain k]

local notation "R" => MvPolynomial (Fin m) k
local notation "K" => FractionRing (MvPolynomial (Fin m) k)

/-- The expansion of `crossComp P j h t` in `Frac(k[x]) ⋊ S_m`:
`(x_j - x_{j+1})⁻¹ (1 - s_j)` if `t_j = t_{j+1}`, and `P(x_j, x_{j+1}) s_j` otherwise. -/
noncomputable def crossExp (P : I → I → MvPolynomial (Fin 2) k) (j : ℕ) (h : j + 1 < m)
    (t : Seq ν) : Perm (Fin m) → K :=
  if t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, h⟩ then
    Pi.single 1 (algebraMap R K (X ⟨j, by omega⟩ - X ⟨j + 1, h⟩))⁻¹ +
      Pi.single (sadj m j) (-(algebraMap R K (X ⟨j, by omega⟩ - X ⟨j + 1, h⟩))⁻¹)
  else
    Pi.single (sadj m j) (algebraMap R K (rename ![(⟨j, by omega⟩ : Fin m), ⟨j + 1, h⟩]
      (P (t.lbl ⟨j, by omega⟩) (t.lbl ⟨j + 1, h⟩))))

theorem hasExp_crossComp (P : I → I → MvPolynomial (Fin 2) k) (j : ℕ) (h : j + 1 < m)
    (t : Seq ν) : HasExp (k := k) (crossComp P j h t) (crossExp P j h t) := by
  have hne : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, h⟩ := by simp [Fin.ext_iff]
  unfold crossComp crossExp
  split_ifs with hl
  · rw [sadj_eq_swap h]
    exact hasExp_ddiffLike hne (fun f => ddiff_spec hne f)
  · exact (hasExp_mul_rename _ _).congr fun f => rfl

theorem crossExp_support (P : I → I → MvPolynomial (Fin 2) k) (j : ℕ) (h : j + 1 < m)
    (t : Seq ν) (v : Perm (Fin m)) (hv : crossExp P j h t v ≠ 0) : v = 1 ∨ v = sadj m j := by
  by_contra hc
  push_neg at hc
  apply hv
  unfold crossExp
  split_ifs <;> simp [Pi.single_apply, hc.1, hc.2]

theorem crossExp_sadj_ne_zero {P : I → I → MvPolynomial (Fin 2) k}
    (hP : ∀ a b, a ≠ b → P a b ≠ 0) (j : ℕ) (h : j + 1 < m) (t : Seq ν) :
    crossExp P j h t (sadj m j) ≠ 0 := by
  have hs : sadj m j ≠ 1 := sadj_ne_one h
  have hne : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, h⟩ := by simp [Fin.ext_iff]
  unfold crossExp
  split_ifs with hl
  · simp only [Pi.add_apply, Pi.single_apply, if_neg hs, if_true, zero_add, ne_eq,
      neg_eq_zero, inv_eq_zero]
    exact algebraMap_ne_zero (k := k) (sub_ne_zero.mpr fun e => hne (X_injective e))
  · simp only [Pi.single_eq_same]
    have hinj : Function.Injective ![(⟨j, by omega⟩ : Fin m), ⟨j + 1, h⟩] := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all
    refine algebraMap_ne_zero (k := k) fun e => hP _ _ hl (rename_injective _ hinj ?_)
    rw [e, map_zero]

/-- The expansion of `wordComp P ρ i`. -/
noncomputable def wordExp (P : I → I → MvPolynomial (Fin 2) k) :
    List ℕ → Seq ν → Perm (Fin m) → K
  | [], _ => Pi.single 1 1
  | j :: ρ, i =>
    if h : j + 1 < m then conv (crossExp P j h (wordProd m ρ • i)) (wordExp P ρ i) else 0

theorem hasExp_wordComp (P : I → I → MvPolynomial (Fin 2) k) (ρ : List ℕ) (i : Seq ν) :
    HasExp (k := k) (wordComp P ρ i) (wordExp P ρ i) := by
  induction ρ with
  | nil => exact hasExp_id.congr fun f => rfl
  | cons j ρ ih =>
    by_cases h : j + 1 < m
    · simp only [wordComp, wordExp, dif_pos h]
      exact ((hasExp_crossComp P j h _).comp ih).congr fun f => rfl
    · simp only [wordComp, wordExp, dif_neg h]
      exact HasExp.zero.congr fun f => rfl

/-- Triangularity: the expansion of `wordComp P ρ i` is supported on `wordProd ρ` and
permutations of length `< |ρ|`. -/
theorem wordExp_support (P : I → I → MvPolynomial (Fin 2) k) (ρ : List ℕ) (i : Seq ν)
    {v : Perm (Fin m)} (hv : wordExp P ρ i v ≠ 0) :
    v = wordProd m ρ ∨ length m v < ρ.length := by
  induction ρ generalizing v with
  | nil =>
    left
    by_contra hc
    simp only [wordProd, List.map_nil, List.prod_nil] at hc
    exact hv (by simp [wordExp, Pi.single_apply, hc])
  | cons j ρ ih =>
    by_cases h : j + 1 < m
    · simp only [wordExp, dif_pos h] at hv
      obtain ⟨u, v', hu, hv', rfl⟩ := conv_ne_zero hv
      have hlen := length_wordProd_le m ρ
      rw [wordProd_cons', List.length_cons]
      rcases crossExp_support P j h _ u hu with rfl | rfl <;> rcases ih hv' with rfl | h'
      · right; rw [one_mul]; omega
      · right; rw [one_mul]; omega
      · left; rfl
      · right; have := length_sadj_mul_le m j v'; omega
    · simp [wordExp, dif_neg h] at hv

/-- For a reduced word `ρ`, the coefficient of `wordProd ρ` in the expansion of
`wordComp P ρ i` is nonzero. -/
theorem wordExp_top_ne_zero {P : I → I → MvPolynomial (Fin 2) k}
    (hP : ∀ a b, a ≠ b → P a b ≠ 0) {ρ : List ℕ} (hρ : IsReduced m ρ) (i : Seq ν) :
    wordExp P ρ i (wordProd m ρ) ≠ 0 := by
  induction ρ with
  | nil => simp [wordExp, wordProd]
  | cons j ρ ih =>
    obtain ⟨hρ', hlen⟩ := isReduced_tail hρ
    have h : j + 1 < m := hρ.1 j List.mem_cons_self
    rw [wordProd_cons']
    simp only [wordExp, dif_pos h]
    have hz : wordExp P ρ i (sadj m j * wordProd m ρ) = 0 := by
      by_contra hne
      rcases wordExp_support P ρ i hne with h1 | h1
      · exact sadj_ne_one h (mul_right_cancel (h1.trans (one_mul _).symm))
      · omega
    rw [conv_top (crossExp_support P j h _) hz]
    exact mul_ne_zero (crossExp_sadj_ne_zero hP j h _) (act_ne_zero _ (ih hρ'))

/-! ### Linear independence -/

/-- Expansion of the component `t` of `opΨw P ρ ∘ x^u ∘ 1_i` on inputs in `Pol_{i₀}`. -/
theorem hasExp_family (P : I → I → MvPolynomial (Fin 2) k) (ρ : List ℕ) (i i₀ t : Seq ν)
    (u : Fin m →₀ ℕ) :
    HasExp (fun f => (opΨw P ρ ∘ₗ mulMono u ∘ₗ opE i) (Pi.single i₀ f) t)
      (if i = i₀ ∧ wordProd m ρ • i₀ = t then
        fun v => wordExp P ρ i₀ v * act k v (algebraMap R K (monomial u 1))
      else 0) := by
  have e1 : ∀ f, (opΨw P ρ ∘ₗ mulMono u ∘ₗ opE i) (Pi.single i₀ f) t =
      if i = i₀ ∧ wordProd m ρ • i₀ = t then wordComp P ρ i₀ (monomial u 1 * f) else 0 := by
    intro f
    by_cases hi : i = i₀
    · subst hi
      have h1 : opE i (Pi.single i f) = Pi.single i f := by
        funext s; rw [opE_apply]; simp only [Pi.single_apply]; split_ifs <;> simp_all
      have h2 : mulMono u (Pi.single i f) = Pi.single i (monomial u 1 * f) := by
        funext s; rw [mulMono_apply]; simp only [Pi.single_apply]; split_ifs <;> simp
      simp only [LinearMap.comp_apply, h1, h2, opΨw_single, Pi.single_apply, true_and]
      by_cases ht : wordProd m ρ • i = t
      · simp [ht]
      · simp [ht, Ne.symm ht]
    · have h1 : opE i (Pi.single i₀ f) = 0 := by
        funext s; rw [opE_apply]; by_cases hs : s = i <;> simp [hs, Ne.symm hi]
      simp [h1, hi]
  split_ifs with hc
  · exact ((hasExp_wordComp P ρ i₀).comp_mul (monomial u 1)).congr fun f => by
      rw [e1, if_pos hc]
  · exact HasExp.zero.congr fun f => by rw [e1, if_neg hc]

/-- **Linear independence, coefficient form.** If a finite `k`-linear combination of the
operators `ψ_{ρ w} ∘ x^u ∘ 1_i` vanishes on `Pol_ν`, then all its coefficients vanish. -/
theorem opΨw_family_coeff_eq_zero {P : I → I → MvPolynomial (Fin 2) k}
    (hP : ∀ a b, a ≠ b → P a b ≠ 0) (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    (s : Finset (Seq ν × Perm (Fin m) × (Fin m →₀ ℕ)))
    (g : Seq ν × Perm (Fin m) × (Fin m →₀ ℕ) → k)
    (hsum : ∑ x ∈ s, g x • (opΨw P (ρ x.2.1) ∘ₗ mulMono x.2.2 ∘ₗ opE x.1) = 0) :
    ∀ x ∈ s, g x = 0 := by
  classical
  by_contra hne
  push_neg at hne
  obtain ⟨⟨i₀, w₁, u₁⟩, hx₁s, hx₁⟩ := hne
  set S := s.filter (fun x => x.1 = i₀ ∧ g x ≠ 0) with hS
  obtain ⟨⟨i', w₀, u₀⟩, hx₀S, hmax⟩ :=
    S.exists_max_image (fun x => length m x.2.1) ⟨(i₀, w₁, u₁), by simp [S, hx₁s, hx₁]⟩
  simp only [S, Finset.mem_filter] at hx₀S
  obtain ⟨hx₀s, rfl, hx₀g⟩ := hx₀S
  -- the combined expansion of the output component `w₀ • i'` on inputs in `Pol_{i'}`
  let Φ : Seq ν × Perm (Fin m) × (Fin m →₀ ℕ) → Perm (Fin m) → K := fun x =>
    if x.1 = i' ∧ wordProd m (ρ x.2.1) • i' = w₀ • i' then
      fun v => wordExp P (ρ x.2.1) i' v * act k v (algebraMap R K (monomial x.2.2 1))
    else 0
  have hexp : HasExp
      (fun f => ∑ x ∈ s, g x • (opΨw P (ρ x.2.1) ∘ₗ mulMono x.2.2 ∘ₗ opE x.1)
        (Pi.single i' f) (w₀ • i'))
      (fun v => ∑ x ∈ s, algebraMap R K (C (g x)) * Φ x v) :=
    HasExp.sum s fun x _ =>
      (hasExp_family P (ρ x.2.1) x.1 i' (w₀ • i') x.2.2).smul (g x)
  have hzero := congrFun (hexp.eq_zero_of_forall fun f => by
    have := congrArg (fun T : Module.End k (Pol k ν) => T (Pi.single i' f) (w₀ • i')) hsum
    simpa only [LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
      LinearMap.zero_apply, Pi.zero_apply] using this) w₀
  -- only the terms with `x = (i', w₀, _)` contribute at `w₀`
  have hterm : ∀ x ∈ s, algebraMap R K (C (g x)) * Φ x w₀ =
      if x.1 = i' ∧ x.2.1 = w₀ then
        wordExp P (ρ w₀) i' w₀ * act k w₀ (algebraMap R K (C (g x) * monomial x.2.2 1))
      else 0 := by
    rintro ⟨i, w, u⟩ hx
    by_cases hg0 : g (i, w, u) = 0
    · simp [hg0]
    by_cases hx' : i = i' ∧ w = w₀
    · obtain ⟨rfl, rfl⟩ := hx'
      simp only [Φ, (hρ w).2, and_self, if_true, map_mul, act_algebraMap, rename_C]
      ring
    · rw [if_neg hx']
      by_cases hi : i = i'
      · subst hi
        have hw : w ≠ w₀ := fun e => hx' ⟨rfl, e⟩
        have hE : wordExp P (ρ w) i w₀ = 0 := by
          refine Classical.byContradiction fun hE => ?_
          have hl : length m w ≤ length m w₀ :=
            hmax (i, w, u) (by simp [S, hx, hg0])
          rcases wordExp_support P (ρ w) i hE with h1 | h1
          · exact hw (h1.trans (hρ w).2).symm
          · rw [(hρ w).1.2, (hρ w).2] at h1; omega
        simp only [Φ]
        split_ifs <;> simp [hE]
      · simp [Φ, hi]
  simp only [Finset.sum_apply, Pi.zero_apply] at hzero
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.mul_sum,
    ← act_sum, ← map_sum (algebraMap R K)] at hzero
  have hp : ∑ x ∈ s.filter (fun x => x.1 = i' ∧ x.2.1 = w₀), C (g x) * monomial x.2.2 1 = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · have ht := wordExp_top_ne_zero hP (hρ w₀).1 i'
      rw [(hρ w₀).2] at ht
      exact absurd h ht
    · have := act_eq_zero h
      exact (map_eq_zero_iff _ (IsFractionRing.injective R K)).mp this
  have hc := congrArg (coeff u₀) hp
  rw [coeff_sum, Finset.sum_eq_single_of_mem (i', w₀, u₀) (by simp [hx₀s])] at hc
  · simp [coeff_C_mul] at hc
    exact hx₀g hc
  · rintro ⟨i, w, u⟩ hx hne
    simp only [Finset.mem_filter] at hx
    obtain ⟨-, rfl, rfl⟩ := hx
    have hu : u ≠ u₀ := fun e => hne (by rw [e])
    simp [coeff_C_mul, coeff_monomial, hu]

/-- **Linear independence (KL I, Theorem 2.5, polynomial representation).** For an
integral domain `k`, polynomials `P a b ≠ 0` for `a ≠ b`, and any choice `ρ w` of reduced
words, the operators `ψ_{ρ w} ∘ x^u ∘ 1_i` on `Pol_ν` are linearly independent over `k`. -/
theorem linearIndependent_opΨw {P : I → I → MvPolynomial (Fin 2) k}
    (hP : ∀ a b, a ≠ b → P a b ≠ 0) (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w) :
    LinearIndependent k (fun x : Seq ν × Perm (Fin m) × (Fin m →₀ ℕ) =>
      opΨw P (ρ x.2.1) ∘ₗ mulMono x.2.2 ∘ₗ opE x.1) :=
  linearIndependent_iff'.mpr fun s g hsum => opΨw_family_coeff_eq_zero hP ρ hρ s g hsum

end Expansion

end Categorification.KLR.PolyRep
