/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Mackey

/-!
# The crossing diagram `ψ_d` of the Mackey filtration intertwines modulo lower terms

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, proof of **Proposition 2.18** (TeX lines
1784–1817). Let `d` be the minimal double coset representative of
`(S_n × S_{n'}) \ S_m / (S_{n''} × S_{n'''})` with `c = |λ|` crossing strands
(`TypeA.IsDoubleShuffle`, `c = crossCount n n'' d`), and let `ψ_d = ψ_{σ(d)}` for a reduced word
`σ(d)`. The four blocks of strands of `d` (of sizes `n - c`, `n'' - n + c`, `c`, `n''' - c`, the
paper's `ν - λ`, `ν'' + λ - ν`, `λ`, `ν''' - λ`) go up in parallel, and `ψ_d` intertwines the
two embeddings of `R(ν - λ) ⊗ R(λ) ⊗ R(ν' + λ - ν''') ⊗ R(ν''' - λ)` into `R(m)`, **modulo the
lower step `F_{c-1}` of the Mackey filtration**. This file proves the three basic cases:

* `KLRAlgebra.e_mul_ψD` : `1_s ψ_d = ψ_d 1_{d⁻¹ s}` (exactly);
* `KLRAlgebra.x_mul_ψD_sub_mem` : `x_{d(p)} ψ_d - ψ_d x_p ∈ F_{c-1}`, for every position `p`;
* `KLRAlgebra.ψ_mul_ψD_sub_mem` : `ψ_{d(j)} ψ_d - ψ_d ψ_j ∈ F_{c-1}` whenever `j, j + 1` lie in the
  same one of the four bottom blocks,

and their consequences for words and polynomials (`ψw_map_mul_ψD_sub_mem`,
`pol_rename_mul_ψD_sub_mem`). Here `F_{c-1}` is `KLRAlgebra.mackeyLower c` (`= ⊥` for `c = 0`).

The error terms are handled by two facts:

* `TypeA.IsDoubleShuffle.length_le_of_crossCount_eq` : every permutation with the same `|λ|` as
  `d` is at least as long as `d`; so the diagrams `ψ_τ x^p 1_i` whose subword products all have
  `crossCount ≤ c` and which have fewer than `ℓ(d)` crossings lie in `F_{c-1}`
  (`lowSpan_le_mackeyLower`);
* sliding a dot through `ψ_γ` only produces diagrams on proper subwords of `γ`
  (`x_mul_gen_sub_mem_strictSpan`), and a braid move changes `ψ_γ` by diagrams on subwords with
  three letters fewer (`braidEquiv_sub_mem_lowSpan`).
-/

namespace Categorification.TypeA

open Equiv

variable {m n n' n'' n''' : ℕ} (hJ : n + n' = m) (hK : n'' + n''' = m)

/-- **Minimality of the double coset representative**: a permutation with the same number of
crossing strands `|λ|` as the minimal representative `d` is at least as long as `d`. -/
theorem IsDoubleShuffle.length_le_of_crossCount_eq {d v : Perm (Fin m)}
    (hd : IsDoubleShuffle hJ hK d) (hc : crossCount n n'' v = crossCount n n'' d) :
    length m d ≤ length m v := by
  obtain ⟨a, b, d', y, y', hd', rfl, hl⟩ := mackey_factorisation hJ hK v
  rw [crossCount_mul_blockPerm, crossCount_blockPerm_mul] at hc
  obtain rfl := hd.eq_of_crossCount_eq hJ hK hd' hc.symm
  rw [hl]; omega

/-- **The explicit form of the minimal double coset representative** with `c` crossing strands:
it is the identity on the first `n - c` and the last `n''' - c` positions, shifts the positions
`[n - c, n'')` up by `c`, and the positions `[n'', n'' + c)` down to `[n - c, n)`. -/
theorem IsDoubleShuffle.val_eq_ite {d : Perm (Fin m)} (hd : IsDoubleShuffle hJ hK d) (p : Fin m) :
    (d p).val = if p.val < n - crossCount n n'' d then p.val
      else if p.val < n'' then p.val + crossCount n n'' d
      else if p.val < n'' + crossCount n n'' d then p.val + n - n'' - crossCount n n'' d
      else p.val := by
  have e := hd.val_eq hJ hK p
  have l := hd.val_lt_iff hJ hK p
  have hc1 : crossCount n n'' d ≤ n := crossCount_le d (by omega)
  have hc2 : n ≤ crossCount n n'' d + n'' := le_crossCount d (by omega) (by omega)
  have hp := p.2
  have hdp := (d p).2
  split_ifs with h1 h2 h3
  · exact e.1 (by omega) (by rw [if_pos (by omega)] at l; exact l.2 (by omega))
  · rw [if_pos h2] at l
    exact e.2.1 h2 (by by_contra hc; exact absurd (l.1 (by omega)) (by omega))
  · rw [if_neg h2] at l
    have := e.2.2.2 (by omega) (l.2 h3)
    omega
  · rw [if_neg h2] at l
    exact e.2.2.1 (by omega) (by by_contra hc; exact h3 (l.1 (by omega)))

/-- `j` and `j + 1` lie in the same one of the four blocks `[0, n - c)`, `[n - c, n'')`,
`[n'', n'' + c)`, `[n'' + c, m)` of the minimal double coset representative with `c` crossing
strands. -/
def SameBlock (n n'' c j : ℕ) : Prop :=
  j + 1 < n - c ∨ (n - c ≤ j ∧ j + 1 < n'') ∨ (n'' ≤ j ∧ j + 1 < n'' + c) ∨ n'' + c ≤ j

variable {hJ hK}

theorem IsDoubleShuffle.val_succ {d : Perm (Fin m)} (hd : IsDoubleShuffle hJ hK d) {j : ℕ}
    (hj : j + 1 < m) (hb : SameBlock n n'' (crossCount n n'' d) j) :
    (d ⟨j + 1, hj⟩).val = (d ⟨j, by omega⟩).val + 1 := by
  rw [hd.val_eq_ite hJ hK, hd.val_eq_ite hJ hK]
  simp only [SameBlock] at hb
  simp only [Fin.val_mk]
  have hc1 : crossCount n n'' d ≤ n := crossCount_le d (by omega)
  have hc2 : n ≤ crossCount n n'' d + n'' := le_crossCount d (by omega) (by omega)
  split_ifs <;> omega

theorem IsDoubleShuffle.mul_sadj {d : Perm (Fin m)} (hd : IsDoubleShuffle hJ hK d) {j : ℕ}
    (hj : j + 1 < m) (hb : SameBlock n n'' (crossCount n n'' d) j) :
    d * sadj m j = sadj m (d ⟨j, by omega⟩).val * d := by
  have hs := hd.val_succ hj hb
  have hdj : (d ⟨j, by omega⟩).val + 1 < m := by rw [← hs]; exact (d _).2
  ext ⟨p, hp⟩
  simp only [Perm.mul_apply]
  by_cases h1 : p = j
  · subst h1
    rw [sadj_apply_left hj, sadj_apply_left hdj]
    exact congrArg Fin.val (Fin.ext hs)
  by_cases h2 : p = j + 1
  · subst h2
    rw [sadj_apply_right hj]
    have : d ⟨j + 1, hj⟩ = ⟨(d ⟨j, by omega⟩).val + 1, hdj⟩ := Fin.ext hs
    rw [this, sadj_apply_right hdj]
  · rw [sadj_apply_of_ne ⟨p, hp⟩ h1 h2, sadj_apply_of_ne]
    · intro h
      exact h1 (congrArg Fin.val (d.injective (Fin.ext h)))
    · intro h
      rw [← hs] at h
      exact h2 (congrArg Fin.val (d.injective (Fin.ext h)))

theorem IsDoubleShuffle.length_sadj_mul {d : Perm (Fin m)} (hd : IsDoubleShuffle hJ hK d)
    {j : ℕ} (hj : j + 1 < m) (hb : SameBlock n n'' (crossCount n n'' d) j) :
    length m (sadj m (d ⟨j, by omega⟩).val * d) = length m d + 1 := by
  have hs := hd.val_succ hj hb
  have hdj : (d ⟨j, by omega⟩).val + 1 < m := by rw [← hs]; exact (d _).2
  refine length_sadj_mul_of_lt hdj ?_
  have e1 : d⁻¹ ⟨(d ⟨j, by omega⟩).val, by omega⟩ = ⟨j, by omega⟩ := by
    rw [Perm.inv_eq_iff_eq]
  have e2 : d⁻¹ ⟨(d ⟨j, by omega⟩).val + 1, hdj⟩ = ⟨j + 1, hj⟩ := by
    rw [Perm.inv_eq_iff_eq]; exact Fin.ext hs.symm
  rw [e1, e2]
  simp [Fin.lt_iff_val_lt_val]

/-- The image `d(j)` of a letter `j` of a bottom block lies in a top block together with
`d(j) + 1`. -/
theorem IsDoubleShuffle.top_of_sameBlock {d : Perm (Fin m)} (hd : IsDoubleShuffle hJ hK d)
    {j : ℕ} (hj : j + 1 < m) (hb : SameBlock n n'' (crossCount n n'' d) j) :
    (d ⟨j, by omega⟩).val + 1 < n ∨ n ≤ (d ⟨j, by omega⟩).val := by
  rw [hd.val_eq_ite hJ hK]
  simp only [SameBlock] at hb
  simp only [Fin.val_mk]
  have hc1 : crossCount n n'' d ≤ n := crossCount_le d (by omega)
  have hc2 : n ≤ crossCount n n'' d + n'' := le_crossCount d (by omega) (by omega)
  split_ifs <;> omega

theorem bot_of_sameBlock {c j : ℕ} (hb : SameBlock n n'' c j) (hc : n ≤ c + n'') :
    j + 1 < n'' ∨ n'' ≤ j := by
  simp only [SameBlock] at hb
  omega

end Categorification.TypeA

namespace Categorification.KLR

open Equiv MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} {k : Type*} [CommRing k] [DecidableEq I]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {μ : Multiset I}

local notation "m" => Multiset.card μ

/-! ### The lower step of the filtration -/

section Lower

variable (k Q μ) in
/-- The step `F_{c-1}` below `F_c = mackeyFilt k Q μ n n'' c` (and `⊥` for `c = 0`). -/
noncomputable def mackeyLower (n n'' : ℕ) : ℕ → Submodule k (KLRAlgebra k Q μ)
  | 0 => ⊥
  | c + 1 => mackeyFilt k Q μ n n'' c

variable {n n'' : ℕ}

@[simp] theorem mackeyLower_zero : mackeyLower k Q μ n n'' 0 = ⊥ := rfl

@[simp] theorem mackeyLower_succ (c : ℕ) :
    mackeyLower k Q μ n n'' (c + 1) = mackeyFilt k Q μ n n'' c := rfl

theorem mackeyLower_le (c : ℕ) : mackeyLower k Q μ n n'' c ≤ mackeyFilt k Q μ n n'' c := by
  cases c with
  | zero => exact bot_le
  | succ c => exact mackeyFilt_mono (Nat.le_succ c)

theorem mackeyLower_mul_mem {a : KLRAlgebra k Q μ}
    (h : ∀ c y, y ∈ mackeyFilt k Q μ n n'' c → a * y ∈ mackeyFilt k Q μ n n'' c) {c : ℕ}
    {y : KLRAlgebra k Q μ} (hy : y ∈ mackeyLower k Q μ n n'' c) :
    a * y ∈ mackeyLower k Q μ n n'' c := by
  cases c with
  | zero => rw [mackeyLower_zero, Submodule.mem_bot] at hy ⊢; rw [hy, mul_zero]
  | succ c => exact h c y hy

theorem mul_mackeyLower_mem {a : KLRAlgebra k Q μ}
    (h : ∀ c y, y ∈ mackeyFilt k Q μ n n'' c → y * a ∈ mackeyFilt k Q μ n n'' c) {c : ℕ}
    {y : KLRAlgebra k Q μ} (hy : y ∈ mackeyLower k Q μ n n'' c) :
    y * a ∈ mackeyLower k Q μ n n'' c := by
  cases c with
  | zero => rw [mackeyLower_zero, Submodule.mem_bot] at hy ⊢; rw [hy, zero_mul]
  | succ c => exact h c y hy

end Lower

/-! ### Diagrams on proper subwords -/

section Strict

variable (k Q μ) in
/-- `strictSpan γ`: the span of the diagrams `ψ_δ x^p 1_i` with `δ` a proper subword of `γ`. -/
noncomputable def strictSpan (γ : List ℕ) : Submodule k (KLRAlgebra k Q μ) :=
  Submodule.span k {r | ∃ (δ : List ℕ) (p : MvPolynomial (Fin (Multiset.card μ)) k)
    (i : Seq μ), δ.Sublist γ ∧ δ.length < γ.length ∧ ψw δ * pol p * e i = r}

theorem subSpan_le_strictSpan_cons (j : ℕ) (ρ : List ℕ) :
    subSpan k Q μ ρ ≤ strictSpan k Q μ (j :: ρ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨δ, p, i, hδ, rfl⟩
  refine Submodule.subset_span ⟨δ, p, i, hδ.trans (List.sublist_cons_self j ρ), ?_, rfl⟩
  have := hδ.length_le
  simp only [List.length_cons]; omega

theorem ψ_mul_mem_strictSpan (j : ℕ) {ρ : List ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ strictSpan k Q μ ρ) : ψ j * y ∈ strictSpan k Q μ (j :: ρ) := by
  have : strictSpan k Q μ ρ ≤ (strictSpan k Q μ (j :: ρ)).comap (LinearMap.mulLeft k (ψ j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨δ, p, i, hδ, hl, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply, ← mul_assoc, ← mul_assoc,
      ← ψw_cons]
    exact Submodule.subset_span ⟨j :: δ, p, i, hδ.cons_cons j, by simpa using hl, rfl⟩
  exact this hy

/-- A dot slid to the top of a crossing: `x_a ψ_j = ψ_j x_{s_j a} + (terms without ψ_j)`. -/
theorem x_mul_ψ_mul_gen (a : Fin m) (j : ℕ) (hj : j + 1 < m) (ρ : List ℕ)
    (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    (x a * (ψ j * (ψw ρ * pol p * e i)) : KLRAlgebra k Q μ) -
      ψ j * (x (sadj m j a) * (ψw ρ * pol p * e i)) ∈ subSpan k Q μ ρ := by
  set z := (ψw ρ * pol p * e i : KLRAlgebra k Q μ)
  have hz : z ∈ subSpan k Q μ ρ := mem_subSpan (List.Sublist.refl ρ) p i
  obtain ⟨a, ha⟩ := a
  by_cases h1 : a = j
  · subst h1
    rw [sadj_apply_left hj]
    set T := (x ⟨a, ha⟩ * ψ a - ψ a * x ⟨a + 1, hj⟩ : KLRAlgebra k Q μ)
    have hT : ∀ i, ∃ c : k, T * e i = c • e i := fun i => by
      refine ⟨if i.lbl ⟨a, ha⟩ = i.lbl ⟨a + 1, hj⟩ then 1 else 0, ?_⟩
      rw [dot_cross_left a hj i]
      split_ifs <;> simp
    have : x ⟨a, ha⟩ * (ψ a * z) - ψ a * (x ⟨a + 1, hj⟩ * z) = T * z := by
      simp only [T, sub_mul, mul_assoc]
    rw [this]
    exact mul_mem_subSpan_of_mul_e_eq_smul hT hz
  by_cases h2 : a = j + 1
  · subst h2
    rw [show (⟨j + 1, ha⟩ : Fin m) = ⟨j + 1, hj⟩ from rfl, sadj_apply_right hj]
    set T := (ψ j * x ⟨j, by omega⟩ - x ⟨j + 1, ha⟩ * ψ j : KLRAlgebra k Q μ)
    have hT : ∀ i, ∃ c : k, T * e i = c • e i := fun i => by
      refine ⟨if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, ha⟩ then 1 else 0, ?_⟩
      rw [dot_cross_right j ha i]
      split_ifs <;> simp
    have : x ⟨j + 1, ha⟩ * (ψ j * z) - ψ j * (x ⟨j, by omega⟩ * z) = -(T * z) := by
      simp only [T, sub_mul, mul_assoc]; abel
    rw [this]
    exact neg_mem (mul_mem_subSpan_of_mul_e_eq_smul hT hz)
  · rw [sadj_apply_of_ne _ h1 h2, ← mul_assoc, x_mul_ψ ⟨a, ha⟩ j h1 h2, mul_assoc, sub_self]
    exact zero_mem _

/-- **Sliding a dot through `ψ_γ`**: `x_a ψ_γ x^p 1_i ≡ ψ_γ x_{w⁻¹ a} x^p 1_i` modulo diagrams on
proper subwords of `γ`, where `w = wordProd γ`. -/
theorem x_mul_gen_sub_mem_strictSpan (γ : List ℕ) (a : Fin m) (p : MvPolynomial (Fin m) k)
    (i : Seq μ) :
    (x a * (ψw γ * pol p * e i) : KLRAlgebra k Q μ) -
      ψw γ * pol (X ((wordProd m γ)⁻¹ a) * p) * e i ∈ strictSpan k Q μ γ := by
  induction γ generalizing a with
  | nil =>
    simp only [ψw_nil, one_mul, wordProd, List.map_nil, List.prod_nil, inv_one, Perm.one_apply,
      map_mul, pol_X]
    rw [← mul_assoc, sub_self]; exact zero_mem _
  | cons j ρ ih =>
    by_cases hj : j + 1 < m
    swap
    · rw [ψw_cons, ψ_eq_zero j (by omega)]; simp
    have eq1 : (ψw (j :: ρ) * pol p * e i : KLRAlgebra k Q μ) = ψ j * (ψw ρ * pol p * e i) := by
      rw [ψw_cons]; simp only [mul_assoc]
    have eq2 : (ψw (j :: ρ) * pol (X ((wordProd m (j :: ρ))⁻¹ a) * p) * e i :
        KLRAlgebra k Q μ) =
        ψ j * (ψw ρ * pol (X ((wordProd m ρ)⁻¹ (sadj m j a)) * p) * e i) := by
      rw [ψw_cons, wordProd_cons, mul_inv_rev, sadj_inv, Perm.mul_apply]; simp only [mul_assoc]
    rw [eq1, eq2]
    have h1 := x_mul_ψ_mul_gen (Q := Q) a j hj ρ p i
    have h2 := ψ_mul_mem_strictSpan j (ih (sadj m j a))
    have := add_mem (subSpan_le_strictSpan_cons j ρ h1) h2
    convert this using 1
    rw [mul_sub]; abel

theorem strictSpan_le_subSpan (γ : List ℕ) : strictSpan k Q μ γ ≤ subSpan k Q μ γ :=
  Submodule.span_mono fun _ ⟨δ, p, i, hδ, _, hr⟩ => ⟨δ, p, i, hδ, hr⟩

end Strict

/-! ### Diagrams on short subwords -/

section Low

variable (k Q μ) in
/-- `lowSpan S L`: the span of the diagrams `ψ_τ x^p 1_i`, `τ` a valid word with fewer than `L`
letters all of whose subword products lie in `S`. -/
noncomputable def lowSpan (S : Set (Perm (Fin (Multiset.card μ)))) (L : ℕ) :
    Submodule k (KLRAlgebra k Q μ) :=
  Submodule.span k {r | ∃ (τ : List ℕ) (p : MvPolynomial (Fin (Multiset.card μ)) k)
    (i : Seq μ), ValidWord (Multiset.card μ) τ ∧ subProds (Multiset.card μ) τ ⊆ S ∧
      τ.length < L ∧ ψw τ * pol p * e i = r}

theorem subSpan_le_lowSpan {τ : List ℕ} (hv : ValidWord m τ) {S : Set (Perm (Fin m))}
    (hS : subProds m τ ⊆ S) {L : ℕ} (hL : τ.length < L) :
    subSpan k Q μ τ ≤ lowSpan k Q μ S L := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨δ, p, i, hδ, rfl⟩
  exact Submodule.subset_span ⟨δ, p, i, hv.sublist hδ, (subProds_mono hδ).trans hS,
    lt_of_le_of_lt hδ.length_le hL, rfl⟩

theorem strictSpan_le_lowSpan {γ : List ℕ} (hv : ValidWord m γ) :
    strictSpan k Q μ γ ≤ lowSpan k Q μ (subProds m γ) γ.length := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨δ, p, i, hδ, hl, rfl⟩
  exact Submodule.subset_span ⟨δ, p, i, hv.sublist hδ, subProds_mono hδ, hl, rfl⟩

/-- **Braid moves change `ψ_γ` by diagrams on subwords with three letters fewer.** -/
theorem braidEquiv_sub_mem_lowSpan {ρ₁ σ₁ : List ℕ} (hE : BraidEquiv ρ₁ σ₁)
    (hv : ValidWord m ρ₁) (p : MvPolynomial (Fin m) k) (i : Seq μ) :
    (ψw ρ₁ * pol p * e i : KLRAlgebra k Q μ) - ψw σ₁ * pol p * e i ∈
      lowSpan k Q μ (subProds m ρ₁) (ρ₁.length - 2) := by
  set S := subProds m ρ₁
  set n₀ := ρ₁.length
  set y := (pol p * e i : KLRAlgebra k Q μ)
  have hy : ∀ β : List ℕ, ψw β * y ∈ subSpan k Q μ β := fun β => by
    simpa only [y, mul_assoc] using mem_subSpan (Q := Q) (List.Sublist.refl β) p i
  have key : ∀ ρ₂ σ₂ : List ℕ, BraidEquiv ρ₂ σ₂ → ValidWord m ρ₂ → ρ₂.length = n₀ →
      subProds m ρ₂ ⊆ S → ψw ρ₂ * y - ψw σ₂ * y ∈ lowSpan k Q μ S (n₀ - 2) := by
    intro ρ₂ σ₂ hE
    induction hE with
    | rel ρ₂ σ₂ hstep =>
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
        refine subSpan_le_lowSpan (hv.sublist hsl) ((subProds_mono hsl).trans hS) ?_ hmem
        rw [← hl]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    | refl => intros; rw [sub_self]; exact zero_mem _
    | symm x₁ y₁ h ih =>
      intro hv hl hS
      have hv' : ValidWord m x₁ := (BraidEquiv.validWord_iff h).2 hv
      have := ih hv' (by rw [← hl, BraidEquiv.length_eq h]) (by
        rw [BraidEquiv.subProds_eq h hv']; exact hS)
      rw [← neg_sub]
      exact neg_mem this
    | trans ρ₃ σ₃ τ₃ h₁ _ ih₁ ih₂ =>
      intro hv hl hS
      have hv' : ValidWord m σ₃ := (BraidEquiv.validWord_iff h₁).1 hv
      have := add_mem (ih₁ hv hl hS) (ih₂ hv' (by rw [← hl, BraidEquiv.length_eq h₁]) (by
        rw [← BraidEquiv.subProds_eq h₁ hv]; exact hS))
      rwa [sub_add_sub_cancel] at this
  have := key ρ₁ σ₁ hE hv rfl subset_rfl
  simpa only [y, mul_assoc] using this

variable {n n' n'' n''' : ℕ} (hJ : n + n' = Multiset.card μ) (hK : n'' + n''' = Multiset.card μ)

include hJ hK in
/-- **Short diagrams lie in the lower step.** If all subword products `v ∈ S` have at most
`c = crossCount d` crossing strands and `L ≤ ℓ(d)`, then `lowSpan S L ⊆ F_{c-1}`: a subword
product with exactly `c` crossing strands would be at least as long as `d`. -/
theorem lowSpan_le_mackeyLower {d : Perm (Fin m)} (hd : IsDoubleShuffle hJ hK d)
    {S : Set (Perm (Fin m))} (hS : ∀ v ∈ S, crossCount n n'' v ≤ crossCount n n'' d) {L : ℕ}
    (hL : L ≤ length m d) :
    lowSpan k Q μ S L ≤ mackeyLower k Q μ n n'' (crossCount n n'' d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨τ, p, i, hv, hτS, hτL, rfl⟩
  have hlt : ∀ v ∈ subProds m τ, crossCount n n'' v < crossCount n n'' d := by
    intro v hv'
    refine lt_of_le_of_ne (hS v (hτS hv')) fun hc => ?_
    have h1 := hd.length_le_of_crossCount_eq hJ hK hc
    obtain ⟨δ, hδ, rfl⟩ := hv'
    have h2 := length_wordProd_le (hv.sublist hδ)
    have h3 := hδ.length_le
    omega
  generalize hc : crossCount n n'' d = c at hlt
  cases c with
  | zero => exact absurd (hlt 1 (one_mem_subProds τ)) (Nat.not_lt_zero _)
  | succ c =>
    exact mem_mackeyFilt hv (fun v hv' => Nat.lt_succ_iff.1 (hlt v hv')) p i

end Low

/-! ### Intertwining by `ψ_d` -/

section Intertwine

variable {n n' n'' n''' : ℕ} {hJ : n + n' = Multiset.card μ} {hK : n'' + n''' = Multiset.card μ}
  {d : Perm (Fin (Multiset.card μ))} (hd : IsDoubleShuffle hJ hK d)

local notation "ψD" => (ψw (canWord (Multiset.card μ) d) : KLRAlgebra k Q μ)
local notation "L" => mackeyLower k Q μ n n'' (crossCount n n'' d)

theorem e_mul_ψD (s : Seq μ) : e s * ψD = ψD * e (d⁻¹ • s) := by
  rw [e_mul_ψw, wordProd_canWord]

theorem ψD_mul_e (s : Seq μ) : ψD * e s = e (d • s) * ψD := by
  rw [ψw_mul_e, wordProd_canWord]

theorem ψD_eq_sum : ψD = ∑ i, ψw (canWord m d) * pol 1 * e i := by
  rw [← Finset.mul_sum, sum_e, map_one, mul_one, mul_one]

include hd in
/-- **Dots**: `x_{d(p)} ψ_d - ψ_d x_p ∈ F_{c-1}`. -/
theorem x_mul_ψD_sub_mem (p : Fin m) : x (d p) * ψD - ψD * x p ∈ L := by
  have hred := isReduced_canWord m d
  have hle : strictSpan k Q μ (canWord m d) ≤ L := by
    refine (strictSpan_le_lowSpan hred.1).trans (lowSpan_le_mackeyLower hJ hK hd (fun v hv => ?_)
      (by rw [length_canWord]))
    have := crossCount_le_of_mem_subProds (n := n) (n'' := n'') (by omega) (by omega) hred hv
    rwa [wordProd_canWord] at this
  have : x (d p) * ψD - ψD * x p = ∑ i, (x (d p) * (ψw (canWord m d) * pol 1 * e i) -
      ψw (canWord m d) * pol (X ((wordProd m (canWord m d))⁻¹ (d p)) * 1) * e i) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← ψD_eq_sum]
    simp only [wordProd_canWord, Perm.inv_apply_self, mul_one, pol_X]
    congr 1
    rw [← Finset.mul_sum, sum_e, mul_one]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => hle (x_mul_gen_sub_mem_strictSpan _ _ _ _)

include hd in
/-- **Crossings inside a block**: `ψ_{d(j)} ψ_d - ψ_d ψ_j ∈ F_{c-1}` if `j, j + 1` lie in the same
bottom block. -/
theorem ψ_mul_ψD_sub_mem {j : ℕ} (hj : j + 1 < m) (hb : SameBlock n n'' (crossCount n n'' d) j) :
    ψ (d ⟨j, by omega⟩).val * ψD - ψD * ψ j ∈ L := by
  have hred := isReduced_canWord m d
  set σ := canWord m d
  set j' := (d ⟨j, by omega⟩).val
  have hlen := hd.length_sadj_mul hj hb
  have hs := hd.val_succ hj hb
  have hj' : j' + 1 < m := by rw [← hs]; exact (d _).2
  have hv1 : ValidWord m (j' :: σ) := validWord_cons.2 ⟨hj', hred.1⟩
  have hv2 : ValidWord m (σ ++ [j]) := validWord_append.2 ⟨hred.1, by simp [ValidWord, hj]⟩
  have hw1 : wordProd m (j' :: σ) = sadj m j' * d := by rw [wordProd_cons, wordProd_canWord]
  have hw2 : wordProd m (σ ++ [j]) = sadj m j' * d := by
    rw [wordProd_append, wordProd_canWord, wordProd_singleton, hd.mul_sadj hj hb]
  have hr1 : IsReduced m (j' :: σ) := by
    rw [isReduced_iff_length_le hv1, hw1, hlen, List.length_cons, length_canWord]
  have hr2 : IsReduced m (σ ++ [j]) := by
    rw [isReduced_iff_length_le hv2, hw2, hlen, List.length_append, length_canWord]; simp
  have hE := braidEquiv_of_isReduced hr1 hr2 (by rw [hw1, hw2])
  have hle : lowSpan k Q μ (subProds m (j' :: σ)) ((j' :: σ).length - 2) ≤ L := by
    refine lowSpan_le_mackeyLower hJ hK hd (fun v hv => ?_) (by
      rw [List.length_cons, length_canWord]; omega)
    have := crossCount_le_of_mem_subProds (n := n) (n'' := n'') (by omega) (by omega) hr1 hv
    rwa [hw1, crossCount_sadj_mul (hd.top_of_sameBlock hj hb)] at this
  have : ψ j' * ψD - ψD * ψ j = ∑ i, (ψw (j' :: σ) * pol 1 * e i - ψw (σ ++ [j]) * pol 1 * e i) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_e, map_one, mul_one,
      mul_one, mul_one, ψw_cons, ψw_append, ψw_cons, ψw_nil, mul_one, mul_one]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => hle (braidEquiv_sub_mem_lowSpan hE hv1 1 i)

/-- The shift of a letter by `d`. -/
def dShift (d : Perm (Fin m)) (j : ℕ) : ℕ := if h : j < m then (d ⟨j, h⟩).val else j

theorem mackeyLower_ψ_mul {j : ℕ} (hj : j + 1 < n ∨ n ≤ j) {c : ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ mackeyLower k Q μ n n'' c) : ψ j * y ∈ mackeyLower k Q μ n n'' c :=
  mackeyLower_mul_mem (fun _ _ h => ψ_mul_mem_mackeyFilt hj h) hy

theorem mackeyLower_mul_ψ {j : ℕ} (hj : j + 1 < n'' ∨ n'' ≤ j) {c : ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ mackeyLower k Q μ n n'' c) : y * ψ j ∈ mackeyLower k Q μ n n'' c :=
  mul_mackeyLower_mem (fun _ _ h => mul_ψ_mem_mackeyFilt hj h) hy

theorem mackeyLower_pol_mul (q : MvPolynomial (Fin m) k) {c : ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ mackeyLower k Q μ n n'' c) : pol q * y ∈ mackeyLower k Q μ n n'' c :=
  mackeyLower_mul_mem (fun _ _ h => pol_mul_mem_mackeyFilt q h) hy

theorem mackeyLower_mul_pol (q : MvPolynomial (Fin m) k) {c : ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ mackeyLower k Q μ n n'' c) : y * pol q ∈ mackeyLower k Q μ n n'' c :=
  mul_mackeyLower_mem (fun _ _ h => mul_pol_mem_mackeyFilt q h) hy

theorem mackeyLower_eSum_mul (T : Finset (Seq μ)) {c : ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ mackeyLower k Q μ n n'' c) : eSum Q T * y ∈ mackeyLower k Q μ n n'' c :=
  mackeyLower_mul_mem (fun _ _ h => eSum_mul_mem_mackeyFilt T h) hy

theorem mackeyLower_mul_eSum (T : Finset (Seq μ)) {c : ℕ} {y : KLRAlgebra k Q μ}
    (hy : y ∈ mackeyLower k Q μ n n'' c) : y * eSum Q T ∈ mackeyLower k Q μ n n'' c :=
  mul_mackeyLower_mem (fun _ _ h => mul_eSum_mem_mackeyFilt T h) hy

theorem mackeyLower_mul_ψw {β : List ℕ} (hβ : ∀ j ∈ β, j + 1 < n'' ∨ n'' ≤ j) {c : ℕ}
    {y : KLRAlgebra k Q μ} (hy : y ∈ mackeyLower k Q μ n n'' c) :
    y * ψw β ∈ mackeyLower k Q μ n n'' c :=
  mul_mackeyLower_mem (fun _ _ h => mul_ψw_mem_mackeyFilt hβ h) hy

include hd in
/-- **Words of crossings inside the bottom blocks**: `ψ_{d(β)} ψ_d - ψ_d ψ_β ∈ F_{c-1}`, where
`d(β)` is the word `β` with each letter `j` replaced by `d(j)`. -/
theorem ψw_map_mul_ψD_sub_mem {β : List ℕ} (hβ : ∀ j ∈ β, j + 1 < m ∧
    SameBlock n n'' (crossCount n n'' d) j) :
    ψw (β.map (dShift d)) * ψD - ψD * ψw β ∈ L := by
  have hc : n ≤ crossCount n n'' d + n'' := le_crossCount d (by omega) (by omega)
  induction β with
  | nil => simp
  | cons j β ih =>
    obtain ⟨hj, hb⟩ := hβ j (by simp)
    have ih := ih fun j' hj' => hβ j' (List.mem_cons_of_mem _ hj')
    have hdj : dShift d j = (d ⟨j, by omega⟩).val := dif_pos (by omega)
    rw [List.map_cons, ψw_cons, ψw_cons, hdj]
    have h1 := mackeyLower_ψ_mul (hd.top_of_sameBlock hj hb) ih
    have h2 := mackeyLower_mul_ψw (k := k) (Q := Q) (μ := μ) (β := β)
      (fun j' hj' => bot_of_sameBlock (hβ j' (List.mem_cons_of_mem _ hj')).2 hc)
      (ψ_mul_ψD_sub_mem hd hj hb)
    have := add_mem h1 h2
    convert this using 1
    simp only [mul_assoc, mul_sub, sub_mul]
    abel

include hd in
/-- **Polynomials**: `f(x_{d(1)}, …, x_{d(m)}) ψ_d - ψ_d f(x_1, …, x_m) ∈ F_{c-1}`. -/
theorem pol_rename_mul_ψD_sub_mem (f : MvPolynomial (Fin m) k) :
    pol (rename d f) * ψD - ψD * pol f ∈ L := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [rename_C, algHom_C, Algebra.commutes, sub_self]; exact zero_mem _
  | add f g hf hg =>
    rw [map_add, map_add, map_add, add_mul, mul_add]
    convert add_mem hf hg using 1; abel
  | mul_X f p hf =>
    rw [map_mul, map_mul, map_mul, rename_X, pol_X, pol_X]
    have h1 := mackeyLower_pol_mul (rename d f) (x_mul_ψD_sub_mem (Q := Q) hd p)
    have h2 := mackeyLower_mul_pol (X p) hf
    rw [pol_X] at h2
    have := add_mem h1 h2
    convert this using 1
    simp only [map_mul, pol_X, mul_assoc, mul_sub, sub_mul]
    abel

end Intertwine

end KLRAlgebra

end Categorification.KLR
