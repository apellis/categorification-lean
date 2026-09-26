/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.Thm317
import Categorification.KLR.Crystal.IndNilpotent
import Categorification.KLR.KL2.OrthSum

/-!
# KL I, Lemma 3.9: the head of `Ind (N ⊠ L(i^n))`

Khovanov–Lauda I (arXiv:0803.4121v2), §3.2, **Lemma 3.9** (`lemma_515`, TeX lines 2150–2156;
Kleshchev's book, Lemma 5.1.5):

> Let `N ∈ R(ν)-mod` be irreducible and `M = Ind_{ν,ni} N ⊠ L(i^n)`. Then `hd M` is irreducible,
> `ε_i(hd M) = ε_i(N) + n`, and all other composition factors `L` of `M` have
> `ε_i(L) < ε_i(N) + n`.

We work ungraded, over any field, for finite-dimensional `N` with nilpotent dots (e.g. graded
simple modules), for `Q` satisfying the hypotheses of the basis theorem.

## Proof

Let `ε = ε_i(N)`, `m = ε + n`, write `ν = μ' + εi`, and let `N' = HW(Δ_{i^ε} N)` (irreducible,
`Δ_{i^ε} N ≅ N' ⊠ L(i^ε)` by Lemma 3.8). For the idempotent `E = ι(1_{μ',εi} ⊗ 1)`, the subspace
`E X = Δ_{i^m} X` of an `R(ν + ni)`-module `X` is exact in `X`, and `E X ≠ 0` iff `ε_i(X) ≥ m`.

* **Simple quotients** (`lemma_3_6`): every simple quotient `L` of `M` receives
  `N ⊠ L(i^n) ↪ Δ_{i^n} L`, so `ε_i(L) = m`.
* **Top identification** (`nonempty_hwSpace_equiv_of_embedding`): for such `L`,
  `HW(Δ_{i^m} L) ≅ N'`. Indeed `Δ_{i^m} L ≅ HW(Δ_{i^m} L) ⊠ L(i^m)` (Lemma 3.8) is isotypic as an
  `R(μ')`-module, and it contains the image of `N' ⊗ [1] ⊆ N ⊠ L(i^n)`. Hence
  `dim E L = dim N' · m!`.
* **Dimension bound** (`finrank_fixSub_E_ind_le`): `dim E M ≤ dim N' · m!`, from the Shuffle Lemma:
  a shuffle `u` contributes to `1_{j i^m} M` only if its `n` right positions lie among the last
  `m` positions (`shuffle_posR_ge`), there are at most `binom(m, n)` such shuffles, and
  `binom(m, n) · ε! · n! = m!`.
* Hence `E P = 0` for every maximal submodule `P` of `M`; two distinct maximal submodules would
  give `E M = 0`. Every composition factor below the head is killed by `E`, so has `ε_i < m`.

This is Kleshchev's argument, except that the multiplicity-one statement (Kleshchev uses the
Shuffle Lemma to see that `K ⊠ L(i^{ε+n})` occurs once in `Δ_{i^{ε+n}} M`) is obtained from the
dimension bound together with the top identification, which avoids the associativity of induction
and the structure of `Ind L(i^ε) ⊠ L(i^n)`.

## Main results

* `KLRAlgebra.nonempty_hwSpace_equiv_of_embedding` : the top identification above.
* `KLRAlgebra.lemma_3_9` (**KL I, Lemma 3.9**).
-/

noncomputable section

namespace Categorification.KLR

open Equiv MvPolynomial TypeA MulOpposite Categorification.NilHecke
open scoped TensorProduct

variable {I : Type*} [DecidableEq I]

namespace KLRAlgebra

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}

/-! ### `R(μ)`-isotypic components of `V ⊠ W` -/

section Isotypic

variable {A B : Type*} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
  {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  {W : Type*} [AddCommGroup W] [Module K W] [Module B W] [IsScalarTower K B W]

omit [DecidableEq I] in
/-- The `b`-th coordinate `V ⊠ W → V` for a basis of `W`. -/
theorem exists_coord_extTensor {ι : Type*} (𝒷 : Basis ι K W) :
    ∃ π : ι → (ExtTensor K V W →ₗ[K] V),
      (∀ b (a : A) y, π b (((a ⊗ₜ[K] (1 : B)) : A ⊗[K] B) • y) = a • π b y) ∧
      ∀ y, (∀ b, π b y = 0) → y = 0 := by
  classical
  let E := TensorProduct.equivFinsuppOfBasisRight (M := V) 𝒷
  refine ⟨fun b => (Finsupp.lapply b) ∘ₗ E.toLinearMap ∘ₗ
    (ExtTensor.equivTensor (k := K) (P := V) (Q := W)).toLinearMap, fun b a y => ?_, fun y hy => ?_⟩
  · induction y using ExtTensor.induction_on with
    | zero => simp
    | tmul p q =>
      rw [ExtTensor.smul_tmul, one_smul]
      show E ((a • p) ⊗ₜ[K] q) b = a • E (p ⊗ₜ[K] q) b
      rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, smul_comm]
    | add y y' hy hy' => rw [smul_add, map_add, hy, hy', map_add, smul_add]
  · have : E (ExtTensor.equivTensor y) = 0 := Finsupp.ext fun b => hy b
    exact (ExtTensor.equivTensor (k := K) (P := V) (Q := W)).injective
      (E.injective (this.trans (map_zero E).symm) |>.trans (map_zero _).symm)

end Isotypic

/-! ### Combinatorics of shuffles -/

section Comb

variable {μ ν' : Multiset I} {i : I}

/-- **Right positions of a shuffle**: if `s` has only letters `i` in positions `≥ A`,
`u s = j j'` for a shuffle `u`, and `j` has fewer than `card μ - A + 1` final letters `i`, then all
right positions `u⁻¹(posR y)` of `u` are `≥ A`. -/
theorem shuffle_posR_ge (u : Shuffle (Seq.card_add' μ ν')) {s : Seq (μ + ν')} {j : Seq μ}
    {j' : Seq ν'} (h : u.1 • s = j.append j') {A : ℕ} (hA : A ≤ Multiset.card μ)
    (hs : ∀ p : Fin (Multiset.card (μ + ν')), A ≤ p.val → s.1 p = i)
    (hj : Seq.tailLen i j + A ≤ Multiset.card μ) (y : Fin (Multiset.card ν')) :
    A ≤ (u.1⁻¹ (Seq.posR μ y)).val := by
  classical
  by_contra hy
  push_neg at hy
  have hA1 : 1 ≤ A := by omega
  set ℓ : Fin (Multiset.card μ) → Fin (Multiset.card (μ + ν')) :=
    fun x => u.1⁻¹ (Seq.posL ν' x) with hℓ
  have hℓm : StrictMono ℓ := shuffle_inv_posL_mono u
  have hℓρ : ∀ x, ℓ x ≠ u.1⁻¹ (Seq.posR μ y) := fun x hxy => by
    have := u.1⁻¹.injective hxy
    simp only [Seq.posL, Seq.posR] at this
    exact Sum.inl_ne_inr ((blockEquiv _).injective this)
  -- `ℓ (A - 1) ≥ A` by pigeonhole
  have hlast : A ≤ (ℓ ⟨A - 1, by omega⟩).val := by
    by_contra hlt
    push_neg at hlt
    have hall : ∀ x : Fin (Multiset.card μ), x.val ≤ A - 1 → (ℓ x).val < A := fun x hx =>
      lt_of_le_of_lt (hℓm.monotone (Fin.mk_le_mk.2 hx)) hlt
    let g : Fin (A + 1) → Fin A := fun x =>
      if hx : x.val < A then ⟨(ℓ ⟨x.val, by omega⟩).val, hall _ (by simp only; omega)⟩
      else ⟨(u.1⁻¹ (Seq.posR μ y)).val, hy⟩
    have hg : Function.Injective g := by
      intro x x' hxx
      simp only [g] at hxx
      by_cases hx : x.val < A <;> by_cases hx' : x'.val < A
      · rw [dif_pos hx, dif_pos hx'] at hxx
        have := hℓm.injective (Fin.ext (Fin.mk.inj_iff.1 hxx))
        exact Fin.ext (Fin.mk.inj_iff.1 this)
      · rw [dif_pos hx, dif_neg hx'] at hxx
        exact absurd (Fin.ext (Fin.mk.inj_iff.1 hxx)) (hℓρ _)
      · rw [dif_neg hx, dif_pos hx'] at hxx
        exact absurd (Fin.ext (Fin.mk.inj_iff.1 hxx)).symm (hℓρ _)
      · exact Fin.ext (by omega)
    have := Fintype.card_le_of_injective g hg
    simp only [Fintype.card_fin] at this
    omega
  -- hence `j` ends with `card μ - A + 1` letters `i`
  have htail : Seq.HasTail i j (Multiset.card μ - A + 1) := by
    refine ⟨by omega, fun x hx => ?_⟩
    have hxA : A ≤ (ℓ x).val :=
      hlast.trans (hℓm.monotone (Fin.mk_le_mk.2 (by omega)))
    have := hs _ hxA
    rwa [hℓ, smul_seq_apply_inv, h, Seq.append_posL] at this
  have := Seq.le_tailLen htail
  omega

omit [DecidableEq I] in
theorem range_inv_posL_eq_compl (u : Shuffle (Seq.card_add' μ ν')) :
    Set.range (fun x => u.1⁻¹ (Seq.posL ν' x)) = (Set.range fun y => u.1⁻¹ (Seq.posR μ y))ᶜ := by
  ext p
  simp only [Set.mem_range, Set.mem_compl_iff, not_exists]
  obtain ⟨q, rfl⟩ := u.1⁻¹.surjective p
  obtain ⟨c, rfl⟩ := (blockEquiv (Seq.card_add' μ ν')).surjective q
  constructor
  · rintro ⟨x, hx⟩ y hy
    have := u.1⁻¹.injective (hx.trans hy.symm)
    simp only [Seq.posL, Seq.posR] at this
    exact Sum.inl_ne_inr ((blockEquiv _).injective this)
  · intro h
    cases c with
    | inl x => exact ⟨x, rfl⟩
    | inr y => exact absurd rfl (h y)

omit [DecidableEq I] in
/-- **Counting shuffles**: there are at most `binom(card(μ + ν') - A, card ν')` shuffles all of
whose right positions are `≥ A`. -/
theorem card_shuffle_posR_ge_le (A : ℕ) :
    Fintype.card {u : Shuffle (Seq.card_add' μ ν') //
        ∀ y, A ≤ (u.1⁻¹ (Seq.posR μ y)).val} ≤
      (Multiset.card (μ + ν') - A).choose (Multiset.card ν') := by
  classical
  rw [← Fintype.card_fin (Multiset.card (μ + ν') - A), ← Fintype.card_finset_len]
  let F : {u : Shuffle (Seq.card_add' μ ν') // ∀ y, A ≤ (u.1⁻¹ (Seq.posR μ y)).val} →
      {S : Finset (Fin (Multiset.card (μ + ν') - A)) // S.card = Multiset.card ν'} := fun u =>
    ⟨Finset.univ.image fun y => ⟨(u.1.1⁻¹ (Seq.posR μ y)).val - A, by
        have := (u.1.1⁻¹ (Seq.posR μ y)).2; have := u.2 y; omega⟩, by
      rw [Finset.card_image_of_injective _ (fun y y' hyy => ?_), Finset.card_univ,
        Fintype.card_fin]
      have h1 := congrArg Fin.val hyy
      simp only at h1
      have := u.2 y; have := u.2 y'
      exact (shuffle_inv_posR_mono u.1).injective (Fin.ext (by omega))⟩
  refine Fintype.card_le_of_injective F fun u u' huu => ?_
  have himg := congrArg Subtype.val huu
  simp only [F] at himg
  -- equal right positions
  have hR : (fun y => u.1.1⁻¹ (Seq.posR μ y)) = fun y => u'.1.1⁻¹ (Seq.posR μ y) := by
    rw [← StrictMono.range_inj (shuffle_inv_posR_mono u.1) (shuffle_inv_posR_mono u'.1)]
    have key : ∀ (v v' : {u : Shuffle (Seq.card_add' μ ν') //
        ∀ y, A ≤ (u.1⁻¹ (Seq.posR μ y)).val}),
        (Finset.univ.image fun y => (⟨(v.1.1⁻¹ (Seq.posR μ y)).val - A, by
          have := (v.1.1⁻¹ (Seq.posR μ y)).2; have := v.2 y; omega⟩ :
            Fin (Multiset.card (μ + ν') - A))) =
        (Finset.univ.image fun y => (⟨(v'.1.1⁻¹ (Seq.posR μ y)).val - A, by
          have := (v'.1.1⁻¹ (Seq.posR μ y)).2; have := v'.2 y; omega⟩ :
            Fin (Multiset.card (μ + ν') - A))) →
        Set.range (fun y => v.1.1⁻¹ (Seq.posR μ y)) ⊆
          Set.range (fun y => v'.1.1⁻¹ (Seq.posR μ y)) := by
      rintro v v' hvv _ ⟨y, rfl⟩
      have hm : (⟨(v.1.1⁻¹ (Seq.posR μ y)).val - A, by
          have := (v.1.1⁻¹ (Seq.posR μ y)).2; have := v.2 y; omega⟩ :
            Fin (Multiset.card (μ + ν') - A)) ∈ Finset.univ.image fun y => (⟨(v'.1.1⁻¹
              (Seq.posR μ y)).val - A, by
          have := (v'.1.1⁻¹ (Seq.posR μ y)).2; have := v'.2 y; omega⟩ :
            Fin (Multiset.card (μ + ν') - A)) := by
        rw [← hvv]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      obtain ⟨y', -, hy'⟩ := Finset.mem_image.1 hm
      refine ⟨y', Fin.ext ?_⟩
      have h1 := Fin.mk.inj_iff.1 hy'
      have := v.2 y; have := v'.2 y'
      show (v'.1.1⁻¹ (Seq.posR μ y')).val = (v.1.1⁻¹ (Seq.posR μ y)).val
      omega
    exact Set.Subset.antisymm (key u u' himg) (key u' u himg.symm)
  have hL : (fun x => u.1.1⁻¹ (Seq.posL ν' x)) = fun x => u'.1.1⁻¹ (Seq.posL ν' x) := by
    rw [← StrictMono.range_inj (shuffle_inv_posL_mono u.1) (shuffle_inv_posL_mono u'.1),
      range_inv_posL_eq_compl, range_inv_posL_eq_compl, hR]
  have hinv : u.1.1⁻¹ = u'.1.1⁻¹ := by
    ext q
    obtain ⟨c, rfl⟩ := (blockEquiv (Seq.card_add' μ ν')).surjective q
    cases c with
    | inl x => exact congrArg Fin.val (congrFun hL x)
    | inr y => exact congrArg Fin.val (congrFun hR y)
  exact Subtype.ext (Subtype.ext (inv_injective hinv))

end Comb

/-! ### Idempotent sums -/

section Sums

variable {ν : Multiset I}

theorem isOrthFamily_e (T : Finset (Seq ν)) :
    IsOrthFamily T (fun t => (e t : KLRAlgebra K Q ν)) := fun a _ b _ => e_mul_e a b

theorem finrank_fixSub_eSum (X : Type*) [AddCommGroup X] [Module K X]
    [Module (KLRAlgebra K Q ν) X] [IsScalarTower K (KLRAlgebra K Q ν) X] [FiniteDimensional K X]
    (T : Finset (Seq ν)) :
    Module.finrank K (fixSub K X (eSum Q T)) =
      ∑ t ∈ T, Module.finrank K (fixSub K X (e t : KLRAlgebra K Q ν)) := by
  rw [eSum, (fixSubSumEquiv (isOrthFamily_e T) K X).finrank_eq, Module.finrank_pi_fintype]
  exact Finset.sum_coe_sort T (fun t => Module.finrank K (fixSub K X (e t : KLRAlgebra K Q ν)))

omit [DecidableEq I] in
theorem fixSub_zero {A : Type*} [Ring A] [Algebra K A] (X : Type*) [AddCommGroup X] [Module K X]
    [Module A X] [IsScalarTower K A X] : fixSub K X (0 : A) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [mem_fixSub, zero_smul] at hv
  rw [← hv]; exact zero_mem _

omit [DecidableEq I] in
theorem finrank_klrRep {ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i) :
    Module.finrank K (KLRRep hν' Q) = (Multiset.card ν').factorial :=
  (KLRRep.of hν' Q).symm.finrank_eq.trans (finrank_coinv _)

end Sums

/-! ### The dimension bound -/

section Bound

variable {μ' ν'' ν' : Multiset I} {i : I} (hν'' : ∀ a ∈ ν'', a = i) (hν' : ∀ a ∈ ν', a = i)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

variable (Q μ' ν'' ν') in
/-- The idempotent `E = ι(1_{μ',ν''} ⊗ 1)` of `R((μ' + ν'') + ν')`; for `ν''`, `ν'` of all labels
`i`, `E X = Δ_{i^{ε + n}} X`. -/
def topIdem : KLRAlgebra K Q ((μ' + ν'') + ν') :=
  concat Q (μ' + ν'') ν' (oneConcat Q μ' ν'' ⊗ₜ[K] 1)

theorem topIdem_idem : IsIdempotentElem (topIdem Q μ' ν'' ν') := by
  rw [IsIdempotentElem, topIdem, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
    oneConcat_idem.eq, one_mul]

include hν' in
theorem topIdem_eq_sum :
    topIdem Q μ' ν'' ν' = ∑ t ∈ concatSet μ' ν'', e (t.append (Seq.constSeq hν')) := by
  rw [topIdem, oneConcat, eSum, TensorProduct.sum_tmul, map_sum]
  exact Finset.sum_congr rfl fun t _ => concat_e_tmul_one_const hν' t

theorem isOrthFamily_append (c : Seq ν') :
    IsOrthFamily (concatSet μ' ν'')
      (fun t : Seq (μ' + ν'') => (e (t.append c) : KLRAlgebra K Q ((μ' + ν'') + ν'))) := by
  intro a _ b _
  rw [e_mul_e]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (fun h' => h (Seq.append_inj.1 h').1), if_neg h]

variable {N : Type*} [AddCommGroup N] [Module K N] [Module (KLRAlgebra K Q (μ' + ν'')) N]
  [IsScalarTower K (KLRAlgebra K Q (μ' + ν'')) N] [FiniteDimensional K N]

include hν'' hν' in
/-- The contribution of one shuffle `u` and one sequence `t i^n`, `t ∈ Seq(μ') i^ε`, to
`dim E Ind (N ⊠ L(i^n))` (Shuffle Lemma). -/
theorem finrank_fixSub_concatIdem_le (hεN : epsI Q (μ' + ν'') i N ≤ Multiset.card ν'')
    (u : Shuffle (Seq.card_add' (μ' + ν'') ν')) {t : Seq (μ' + ν'')}
    (ht : t ∈ concatSet μ' ν'') :
    Module.finrank K (fixSub K (ExtTensor K N (KLRRep hν' Q))
        (concatIdem (Q := Q) (u.1 • t.append (Seq.constSeq hν')))) ≤
      if ∀ y, Multiset.card μ' ≤ (u.1⁻¹ (Seq.posR (μ' + ν'') y)).val then
        ∑ j ∈ concatSet μ' ν'', if u.1 • t.append (Seq.constSeq hν') = j.append (Seq.constSeq hν')
          then (Multiset.card ν').factorial *
            Module.finrank K (fixSub K N (e j : KLRAlgebra K Q (μ' + ν''))) else 0
      else 0 := by
  classical
  set c' := Seq.constSeq hν'
  by_cases hmem : u.1 • t.append c' ∈ concatSet (μ' + ν'') ν'
  · obtain ⟨j1, j2, hj⟩ := mem_concatSet.1 hmem
    have hF : Module.finrank K (fixSub K (ExtTensor K N (KLRRep hν' Q))
        (concatIdem (Q := Q) (u.1 • t.append c'))) =
        Module.finrank K (fixSub K N (e j1 : KLRAlgebra K Q (μ' + ν''))) *
          Module.finrank K (fixSub K (KLRRep hν' Q) (e j2 : KLRAlgebra K Q ν')) := by
      rw [← hj, concatIdem_append,
        finrank_fixSub_extTensor (K := K) (e_mul_self j1) (e_mul_self j2)]
    rw [hF]
    by_cases hd : fixSub K N (e j1 : KLRAlgebra K Q (μ' + ν'')) = ⊥
    · rw [hd, finrank_bot, zero_mul]; exact Nat.zero_le _
    have hc := Multiset.card_add μ' ν''
    have hc' := Multiset.card_add (μ' + ν'') ν'
    have h1 : Seq.tailLen i j1 ≤ Multiset.card ν'' := (tailLen_le_epsI hd).trans hεN
    have h2 : Multiset.card ν'' + Multiset.card ν' ≤ Seq.tailLen i (t.append c') :=
      le_trans (Nat.add_le_add_right (Seq.le_tailLen ((mem_concatSet_iff_hasTail hν'').1 ht)) _)
        (Seq.le_tailLen_append_const hν' t)
    have h3 := tailLen_le_of_shuffle (i := i) u hj.symm
    have hj1 : j1 ∈ concatSet μ' ν'' :=
      (mem_concatSet_iff_hasTail hν'').2 (Seq.hasTail_iff.2 (by omega))
    have hPu : ∀ y, Multiset.card μ' ≤ (u.1⁻¹ (Seq.posR (μ' + ν'') y)).val := by
      refine shuffle_posR_ge (i := i) u hj.symm (A := Multiset.card μ') (by omega)
        (fun p hp => ?_) (by omega)
      exact Seq.apply_eq_of_le_tailLen (by omega)
    have hj2 : j2 = c' := Seq.eq_constSeq hν' j2
    rw [if_pos hPu]
    calc Module.finrank K (fixSub K N (e j1 : KLRAlgebra K Q (μ' + ν''))) *
          Module.finrank K (fixSub K (KLRRep hν' Q) (e j2 : KLRAlgebra K Q ν'))
        ≤ Module.finrank K (fixSub K N (e j1 : KLRAlgebra K Q (μ' + ν''))) *
          (Multiset.card ν').factorial :=
          Nat.mul_le_mul_left _ ((Submodule.finrank_le _).trans (finrank_klrRep hν').le)
      _ = if u.1 • t.append c' = j1.append c' then
            (Multiset.card ν').factorial *
              Module.finrank K (fixSub K N (e j1 : KLRAlgebra K Q (μ' + ν''))) else 0 := by
          rw [if_pos (by rw [← hj, hj2]), mul_comm]
      _ ≤ _ := Finset.single_le_sum (f := fun j => if u.1 • t.append c' = j.append c' then
            (Multiset.card ν').factorial *
              Module.finrank K (fixSub K N (e j : KLRAlgebra K Q (μ' + ν''))) else 0)
            (fun j _ => Nat.zero_le _) hj1
  · rw [concatIdem_of_not_mem hmem, fixSub_zero, finrank_bot]
    exact Nat.zero_le _

set_option maxHeartbeats 400000 in
include hν'' hν' hPQ hP in
/-- **The dimension bound**: `dim E Ind (N ⊠ L(i^n)) ≤ binom(ε + n, n) · dim Δ_{i^ε} N · n!`
for `ε_i(N) ≤ ε = card ν''`. -/
theorem finrank_fixSub_topIdem_ind_le (hεN : epsI Q (μ' + ν'') i N ≤ Multiset.card ν'') :
    Module.finrank K (fixSub K (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)))
        (topIdem Q μ' ν'' ν')) ≤
      (Multiset.card ν'' + Multiset.card ν').choose (Multiset.card ν') *
        ((Multiset.card ν').factorial * Module.finrank K (ResSub Q μ' ν'' N)) := by
  classical
  set c' := Seq.constSeq hν'
  set D := Module.finrank K (ResSub Q μ' ν'' N)
  have hD : D = ∑ j ∈ concatSet μ' ν'',
      Module.finrank K (fixSub K N (e j : KLRAlgebra K Q (μ' + ν''))) :=
    finrank_fixSub_eSum N _
  haveI : FiniteDimensional K (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q))) :=
    finiteDimensional_ind hPQ hP _
  haveI : ∀ t : concatSet μ' ν'', Module.Free K (fixSub K
      (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)))
      (e ((t : Seq (μ' + ν'')).append c') : KLRAlgebra K Q ((μ' + ν'') + ν'))) :=
    fun _ => Module.Free.of_divisionRing K _
  haveI : ∀ t : concatSet μ' ν'', Module.Finite K (fixSub K
      (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)))
      (e ((t : Seq (μ' + ν'')).append c') : KLRAlgebra K Q ((μ' + ν'') + ν'))) :=
    fun _ => inferInstance
  rw [topIdem_eq_sum hν', (fixSubSumEquiv (isOrthFamily_append c') K _).finrank_eq,
    Module.finrank_pi_fintype]
  rw [Finset.sum_coe_sort (concatSet μ' ν'') (fun t => Module.finrank K (fixSub K
    (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)))
      (e (t.append c') : KLRAlgebra K Q ((μ' + ν'') + ν'))))]
  simp_rw [finrank_fixSub_ind hPQ hP (ExtTensor K N (KLRRep hν' Q))]
  rw [Finset.sum_comm]
  -- the bound for one shuffle
  have key : ∀ u : Shuffle (Seq.card_add' (μ' + ν'') ν'),
      ∑ t ∈ concatSet μ' ν'', Module.finrank K (fixSub K (ExtTensor K N (KLRRep hν' Q))
        (concatIdem (Q := Q) (u.1 • t.append c'))) ≤
      if ∀ y, Multiset.card μ' ≤ (u.1⁻¹ (Seq.posR (μ' + ν'') y)).val then
        (Multiset.card ν').factorial * D else 0 := by
    intro u
    refine (Finset.sum_le_sum fun t ht => finrank_fixSub_concatIdem_le hν'' hν' hεN u ht).trans ?_
    split_ifs with hu
    · rw [Finset.sum_comm, hD, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      have hcard : (Finset.filter (fun t => u.1 • t.append c' = j.append c')
          (concatSet μ' ν'')).card ≤ 1 := by
        refine Finset.card_le_one.2 fun t ht t' ht' => ?_
        have h := (Finset.mem_filter.1 ht).2.trans (Finset.mem_filter.1 ht').2.symm
        exact (Seq.append_inj.1 ((smul_left_cancel_iff u.1).1 h)).1
      calc _ ≤ 1 * ((Multiset.card ν').factorial *
            Module.finrank K (fixSub K N (e j : KLRAlgebra K Q (μ' + ν'')))) :=
            Nat.mul_le_mul_right _ hcard
        _ = _ := one_mul _
    · simp
  calc _ ≤ ∑ u : Shuffle (Seq.card_add' (μ' + ν'') ν'),
        (if ∀ y, Multiset.card μ' ≤ (u.1⁻¹ (Seq.posR (μ' + ν'') y)).val then
          (Multiset.card ν').factorial * D else 0) := Finset.sum_le_sum fun u _ => key u
    _ = (Finset.univ.filter fun u : Shuffle (Seq.card_add' (μ' + ν'') ν') =>
          ∀ y, Multiset.card μ' ≤ (u.1⁻¹ (Seq.posR (μ' + ν'') y)).val).card *
          ((Multiset.card ν').factorial * D) := by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    _ ≤ _ := by
      refine Nat.mul_le_mul_right _ ?_
      rw [← Fintype.card_subtype]
      refine (card_shuffle_posR_ge_le _).trans (le_of_eq ?_)
      rw [Multiset.card_add, Multiset.card_add]
      congr 1
      omega

end Bound

/-! ### Top identification -/

section Top

variable {μ' ν'' ν' : Multiset I} {i : I} (hν'' : ∀ a ∈ ν'', a = i) (hν' : ∀ a ∈ ν', a = i)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {L : Type*} [AddCommGroup L] [Module K L] [Module (KLRAlgebra K Q ((μ' + ν'') + ν')) L]
  [IsScalarTower K (KLRAlgebra K Q ((μ' + ν'') + ν')) L]
  {N : Type*} [AddCommGroup N] [Module K N] [Module (KLRAlgebra K Q (μ' + ν'')) N]
  [IsScalarTower K (KLRAlgebra K Q (μ' + ν'')) N]
  (f : ExtTensor K N (KLRRep hν' Q) →ₗ[TensorKLR Q (μ' + ν'') ν'] ResSub Q (μ' + ν'') ν' L)

include hν'' in
theorem topMap_mem (w : HWSpace Q μ' ν'' (ResSub Q μ' ν'' N)) :
    CastMod.of (h := (add_assoc μ' ν'' ν').symm)
      ((f (ExtTensor.tmul (((w : ResSub Q μ' ν'' N)) : N) (lMk hν' Q 1)) :
        ResSub Q (μ' + ν'') ν' L) : L) ∈
      fixSub K (MAssoc μ' ν'' ν' L) (oneConcat Q μ' (ν'' + ν')) := by
  rw [mem_fixSub, oneConcat_smul_mAssoc hν'' hν']
  congr 1
  rw [← coe_resSub_smul, ← map_smul, ExtTensor.smul_tmul, one_smul,
    mem_fixSub.1 (w : ResSub Q μ' ν'' N).2]

include hν'' in
/-- The map `N' = HW(Δ_{i^ε} N) → Δ_{i^m} L`, `w ↦ f(w ⊗ [1])`. -/
def topMap : HWSpace Q μ' ν'' (ResSub Q μ' ν'' N) →ₗ[K]
    ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' L) where
  toFun w := ⟨CastMod.of (h := (add_assoc μ' ν'' ν').symm)
      ((f (ExtTensor.tmul (((w : ResSub Q μ' ν'' N)) : N) (lMk hν' Q 1)) :
        ResSub Q (μ' + ν'') ν' L) : L), topMap_mem hν'' hν' f w⟩
  map_add' w w' := Subtype.ext (by
    simp only [Submodule.coe_add, ExtTensor.add_tmul, map_add]
    rfl)
  map_smul' c w := Subtype.ext (by
    simp only [Submodule.coe_smul_of_tower, ← ExtTensor.smul_tmul', LinearMap.map_smul_of_tower,
      RingHom.id_apply]
    rfl)

include hν'' in
theorem coe_topMap (w : HWSpace Q μ' ν'' (ResSub Q μ' ν'' N)) :
    CastMod.val ((topMap hν'' hν' f w : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' L)) :
      MAssoc μ' ν'' ν' L) =
      ((f (ExtTensor.tmul (((w : ResSub Q μ' ν'' N)) : N) (lMk hν' Q 1)) :
        ResSub Q (μ' + ν'') ν' L) : L) := rfl

include hν'' in
theorem topMap_smul (a : KLRAlgebra K Q μ') (w : HWSpace Q μ' ν'' (ResSub Q μ' ν'' N)) :
    topMap hν'' hν' f (a • w) = (a ⊗ₜ[K] 1 : TensorKLR Q μ' (ν'' + ν')) • topMap hν'' hν' f w := by
  apply Subtype.ext
  show CastMod.val ((topMap hν'' hν' f (a • w) : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' L)) :
      MAssoc μ' ν'' ν' L) = CastMod.val (((a ⊗ₜ[K] 1 : TensorKLR Q μ' (ν'' + ν')) •
        topMap hν'' hν' f w : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' L)) : MAssoc μ' ν'' ν' L)
  rw [concat_tmul_one_smul_mAssoc hν'' hν', coe_topMap, coe_topMap, coe_hw_smul, coe_resSub_smul,
    ← one_smul (KLRAlgebra K Q ν') (lMk hν' Q 1), ← ExtTensor.smul_tmul, map_smul, coe_resSub_smul,
    one_smul]

set_option maxHeartbeats 400000 in
include hν'' hPQ hP in
/-- **Top identification**: let `L` be simple with `ε_i(L) = ε + n` (`ε = card ν''`,
`n = card ν'`) and `N` simple with `ε_i(N) = ε` (finite-dimensional, nilpotent dots), and let
`N ⊠ L(i^n) ↪ Δ_{i^n} L`. Then `HW(Δ_{i^ε} N) ≅ HW(Δ_{i^{ε+n}} L)` (as `R(μ')`-modules),
i.e. `ẽ_i^{ε} N ≅ ẽ_i^{ε+n} L` at the top level. -/
theorem nonempty_hwSpace_equiv_of_embedding [FiniteDimensional K L]
    [IsSimpleModule (KLRAlgebra K Q ((μ' + ν'') + ν')) L]
    (hnilL : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q ((μ' + ν'') + ν')) L)
    (hεL : epsI Q ((μ' + ν'') + ν') i L = Multiset.card ν'' + Multiset.card ν')
    [FiniteDimensional K N] [IsSimpleModule (KLRAlgebra K Q (μ' + ν'')) N]
    (hnilN : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ' + ν'')) N)
    (hεN : epsI Q (μ' + ν'') i N = Multiset.card ν'') (hf : Function.Injective f) :
    Nonempty (HWSpace Q μ' ν'' (ResSub Q μ' ν'' N) ≃ₗ[KLRAlgebra K Q μ']
      HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' L))) := by
  have hνε := forall_add_of_forall hν'' hν'
  haveI := isSimpleModule_castMod (Q := Q) (add_assoc μ' ν'' ν').symm L
  have hε' : epsI Q (μ' + (ν'' + ν')) i (MAssoc μ' ν'' ν' L) = Multiset.card (ν'' + ν') := by
    rw [epsI_castMod, hεL, Multiset.card_add]
  have hnilM := smulNilpotent_mAssoc (Q := Q) (μ' := μ') (ν'' := ν'') (ν' := ν') hnilL
  obtain ⟨h1, h2, -⟩ := lemma_3_8 hνε hPQ hP hnilM hε'
  obtain ⟨-, h2N, -⟩ := lemma_3_8 hν'' hPQ hP hnilN hεN
  have hnilΔ : ∀ b, SmulNilpotent ((1 : KLRAlgebra K Q μ') ⊗ₜ[K] x b :
      TensorKLR Q μ' (ν'' + ν')) (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' L)) :=
    fun b => smulNilpotent_resSub b (hnilM _)
  let Φ := hwEquiv hνε hPQ hP hnilΔ
  obtain ⟨π, hπ, hπ0⟩ := exists_coord_extTensor
    (V := HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' L)))
    (A := KLRAlgebra K Q μ') (B := KLRAlgebra K Q (ν'' + ν'))
    (Module.finBasis K (KLRRep hνε Q))
  haveI : Nontrivial (HWSpace Q μ' ν'' (ResSub Q μ' ν'' N)) :=
    IsSimpleModule.nontrivial (KLRAlgebra K Q μ') _
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : HWSpace Q μ' ν'' (ResSub Q μ' ν'' N))
  have hθ0 : Φ.symm (topMap hν'' hν' f w₀) ≠ 0 := by
    rw [ne_eq, LinearEquiv.map_eq_zero_iff]
    intro h0
    have h1 := congrArg (fun z : ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' L) =>
      CastMod.val (z : MAssoc μ' ν'' ν' L)) h0
    simp only [coe_topMap] at h1
    have h2 : f (ExtTensor.tmul (((w₀ : ResSub Q μ' ν'' N)) : N) (lMk hν' Q 1)) = 0 :=
      Subtype.ext h1
    rw [← map_zero f] at h2
    refine extTensor_tmul_ne_zero (K := K) (A := KLRAlgebra K Q (μ' + ν''))
      (B := KLRAlgebra K Q ν') ?_ (lMk_one_ne_zero (K := K) (Q := Q) hν') (hf h2)
    exact fun h => hw₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨b, hb⟩ : ∃ b, π b (Φ.symm (topMap hν'' hν' f w₀)) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hθ0 (hπ0 _ h)
  let g : HWSpace Q μ' ν'' (ResSub Q μ' ν'' N) →ₗ[KLRAlgebra K Q μ']
      HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' L)) :=
    { toFun := fun w => π b (Φ.symm (topMap hν'' hν' f w))
      map_add' := fun w w' => by simp only [map_add]
      map_smul' := fun a w => by
        show π b (Φ.symm (topMap hν'' hν' f (a • w))) = a • π b (Φ.symm (topMap hν'' hν' f w))
        rw [topMap_smul, LinearEquiv.map_smul]
        exact hπ b a _ }
  have hg0 : g ≠ 0 := fun h => hb (LinearMap.congr_fun h w₀)
  exact ⟨LinearEquiv.ofBijective g (LinearMap.bijective_of_ne_zero hg0)⟩

end Top

/-! ### Auxiliary facts -/

section Aux

omit [DecidableEq I] in
theorem smulNilpotent_quotient {A : Type*} [Ring A] {X : Type*} [AddCommGroup X] [Module A X]
    {a : A} (S : Submodule A X) (h : SmulNilpotent a X) : SmulNilpotent a (X ⧸ S) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun v => ?_⟩
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [← Submodule.Quotient.mk_smul, hm, Submodule.Quotient.mk_zero]

/-- The dots act nilpotently on `L(i^n)`. -/
theorem smulNilpotent_klrRep {ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i)
    (b : Fin (Multiset.card ν')) : SmulNilpotent (x b : KLRAlgebra K Q ν') (KLRRep hν' Q) := by
  refine ⟨(Multiset.card ν').choose 2 + 1, fun ℓ => ?_⟩
  have h := prod_x_mem_coinvIdeal (K := K) (List.replicate ((Multiset.card ν').choose 2 + 1) b)
    (by rw [List.length_replicate]; omega)
  rw [List.map_replicate, List.prod_replicate] at h
  rw [← pol_X (k := K) (Q := Q), ← map_pow]
  exact pol_smul_eq_zero hν' h ℓ

variable {μ' ν'' ν' : Multiset I} {i : I} (hν'' : ∀ a ∈ ν'', a = i) (hν' : ∀ a ∈ ν', a = i)
  {X : Type*} [AddCommGroup X] [Module K X] [Module (KLRAlgebra K Q ((μ' + ν'') + ν')) X]
  [IsScalarTower K (KLRAlgebra K Q ((μ' + ν'') + ν')) X]

include hν'' hν' in
/-- `E X = Δ_{i^{ε+n}} X` (`X` viewed over `R(μ' + (ν'' + ν'))`). -/
def fixSubTopIdemEquiv : fixSub K X (topIdem Q μ' ν'' ν') ≃ₗ[K]
    ResSub Q μ' (ν'' + ν') (MAssoc μ' ν'' ν' X) where
  toFun v := ⟨CastMod.of (v : X), by
    rw [mem_fixSub, oneConcat_smul_mAssoc hν'' hν']
    exact congrArg CastMod.of (mem_fixSub.1 v.2)⟩
  invFun w := ⟨CastMod.val (w : MAssoc μ' ν'' ν' X), by
    have h := mem_fixSub.1 w.2
    rw [← show CastMod.of (h := (add_assoc μ' ν'' ν').symm) (CastMod.val
      (w : MAssoc μ' ν'' ν' X)) = (w : MAssoc μ' ν'' ν' X) from rfl,
      oneConcat_smul_mAssoc hν'' hν'] at h
    exact h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [IsScalarTower K (KLRAlgebra K Q ((μ' + ν'') + ν')) X] in
include hν'' hν' in
/-- `E X ≠ 0 ⟺ ε_i(X) ≥ ε + n` (for `X ≠ 0`). -/
theorem fixSub_topIdem_ne_bot_iff [IsScalarTower K (KLRAlgebra K Q ((μ' + ν'') + ν')) X]
    [Nontrivial X] :
    fixSub K X (topIdem Q μ' ν'' ν') ≠ ⊥ ↔
      Multiset.card ν'' + Multiset.card ν' ≤ epsI Q ((μ' + ν'') + ν') i X := by
  haveI : Nontrivial (MAssoc μ' ν'' ν' X) := inferInstanceAs (Nontrivial X)
  rw [← Submodule.nontrivial_iff_ne_bot, (fixSubTopIdemEquiv hν'' hν').nontrivial_congr,
    nontrivial_resSub_iff (forall_add_of_forall hν'' hν'), epsI_castMod, Multiset.card_add]

end Aux

/-! ### Maximal submodules and an idempotent -/

section Generic

variable {A : Type*} [Ring A] [Algebra K A] {X : Type*} [AddCommGroup X] [Module K X]
  [Module A X] [IsScalarTower K A X] {E : A}

omit [DecidableEq I] in
theorem smul_eq_zero_of_fixSub_eq_bot' (hE : IsIdempotentElem E) {S : Submodule A X}
    (h : fixSub K S E = ⊥) {v : X} (hv : v ∈ S) : E • v = 0 := by
  have hmem : (⟨E • v, S.smul_mem E hv⟩ : S) ∈ fixSub K S E := by
    rw [mem_fixSub]
    exact Subtype.ext (by rw [Submodule.coe_smul, smul_smul, hE.eq])
  rw [h, Submodule.mem_bot] at hmem
  exact congrArg Subtype.val hmem

omit [DecidableEq I] in
/-- If `dim E (X / P) ≥ dim E X` then `E P = 0` (exactness of `X ↦ E X`). -/
theorem fixSub_eq_bot_of_finrank_le [FiniteDimensional K X] (hE : IsIdempotentElem E)
    (P : Submodule A X)
    (hle : Module.finrank K (fixSub K X E) ≤ Module.finrank K (fixSub K (X ⧸ P) E)) :
    fixSub K P E = ⊥ := by
  let g : fixSub K X E →ₗ[K] fixSub K (X ⧸ P) E :=
    { toFun := fun v => ⟨P.mkQ v, by rw [mem_fixSub, ← map_smul, mem_fixSub.1 v.2]⟩
      map_add' := fun v w => Subtype.ext (map_add _ _ _)
      map_smul' := fun c v => Subtype.ext (LinearMap.map_smul_of_tower _ c _) }
  have hg : Function.Surjective g := fun w => by
    obtain ⟨v, hv⟩ := P.mkQ_surjective (w : X ⧸ P)
    refine ⟨⟨E • v, smul_mem_fixSub hE v⟩, Subtype.ext ?_⟩
    show P.mkQ (E • v) = w
    rw [map_smul, hv]
    exact w.2
  let ι : fixSub K P E →ₗ[K] fixSub K X E :=
    { toFun := fun v => ⟨((v : P) : X), by
        rw [mem_fixSub, ← Submodule.coe_smul, mem_fixSub.1 v.2]⟩
      map_add' := fun v w => rfl
      map_smul' := fun c v => rfl }
  have hι : Function.Injective ι := fun v w h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : fixSub K X E => (z : X)) h))
  have hrk : LinearMap.range ι ≤ LinearMap.ker g := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show P.mkQ ((v : P) : X) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (v : P).2
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.2 hg, finrank_top] at h1
  have h2 := Submodule.finrank_mono hrk
  rw [LinearMap.finrank_range_of_inj hι] at h2
  haveI : FiniteDimensional K P :=
    Module.Finite.of_injective (P.subtype.restrictScalars K) Subtype.val_injective
  rw [← Submodule.finrank_eq_zero]
  omega

omit [DecidableEq I] in
/-- Two maximal submodules `P`, `P'` with `E P = E P' = 0` and `E (X / P) ≠ 0` coincide. -/
theorem eq_of_isCoatom_of_fixSub_eq_bot (hE : IsIdempotentElem E) {P P' : Submodule A X}
    (hP : IsCoatom P) (hP' : IsCoatom P') (h0 : fixSub K P E = ⊥) (h0' : fixSub K P' E = ⊥)
    (hne : fixSub K (X ⧸ P) E ≠ ⊥) : P = P' := by
  by_contra hPP
  have htop := hP.sup_eq_top_of_ne hP' hPP
  apply hne
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hv : v ∈ P ⊔ P' := htop ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  rw [← mem_fixSub.1 hw, ← Submodule.Quotient.mk_smul, smul_add,
    smul_eq_zero_of_fixSub_eq_bot' hE h0 ha, smul_eq_zero_of_fixSub_eq_bot' hE h0' hb, add_zero,
    Submodule.Quotient.mk_zero]
  exact zero_mem _

omit [DecidableEq I] in
/-- If `E P = 0`, then `E` kills every subquotient of `P`. -/
theorem fixSub_subquot_eq_bot (hE : IsIdempotentElem E) {P : Submodule A X}
    (h0 : fixSub K P E = ⊥) (P₁ : Submodule A X) (h₁ : P₁ ≤ P) (P₂ : Submodule A P₁) :
    fixSub K (P₁ ⧸ P₂) E = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hEv : E • v = 0 := Subtype.ext (by
    rw [Submodule.coe_smul, ZeroMemClass.coe_zero]
    exact smul_eq_zero_of_fixSub_eq_bot' hE h0 (h₁ v.2))
  rw [← mem_fixSub.1 hw, ← Submodule.Quotient.mk_smul, hEv, Submodule.Quotient.mk_zero]
  exact zero_mem _

end Generic

/-! ### Lemma 3.9 -/

section Lemma39

variable {μ' ν'' ν' : Multiset I} {i : I} (hν'' : ∀ a ∈ ν'', a = i) (hν' : ∀ a ∈ ν', a = i)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {N : Type*} [AddCommGroup N] [Module K N] [Module (KLRAlgebra K Q (μ' + ν'')) N]
  [IsScalarTower K (KLRAlgebra K Q (μ' + ν'')) N] [FiniteDimensional K N]
  [IsSimpleModule (KLRAlgebra K Q (μ' + ν'')) N]
  (hnilN : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ' + ν'')) N)
  (hεN : epsI Q (μ' + ν'') i N = Multiset.card ν'')

include hν'' hν' hPQ hP hnilN hεN in
/-- `dim E M ≤ dim N' · (ε + n)!` for `M = Ind (N ⊠ L(i^n))`. -/
theorem finrank_fixSub_topIdem_ind_le' :
    Module.finrank K (fixSub K (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)))
        (topIdem Q μ' ν'' ν')) ≤
      Module.finrank K (HWSpace Q μ' ν'' (ResSub Q μ' ν'' N)) *
        (Multiset.card ν'' + Multiset.card ν').factorial := by
  obtain ⟨hΔN, -, -⟩ := lemma_3_8 hν'' hPQ hP hnilN hεN
  have hnilΔN : ∀ b, SmulNilpotent ((1 : KLRAlgebra K Q μ') ⊗ₜ[K] x b : TensorKLR Q μ' ν'')
      (ResSub Q μ' ν'' N) := fun b => smulNilpotent_resSub b (hnilN _)
  have hdimN : Module.finrank K (ResSub Q μ' ν'' N) =
      Module.finrank K (HWSpace Q μ' ν'' (ResSub Q μ' ν'' N)) * (Multiset.card ν'').factorial := by
    rw [← ((hwEquiv hν'' hPQ hP hnilΔN).restrictScalars K).finrank_eq,
      ExtTensor.equivTensor.finrank_eq, Module.finrank_tensorProduct, finrank_klrRep hν'']
  have h := finrank_fixSub_topIdem_ind_le hν'' hν' hPQ hP (N := N) hεN.le
  rw [hdimN] at h
  refine h.trans (le_of_eq ?_)
  rw [← Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left (Multiset.card ν')
    (Multiset.card ν'')), Nat.add_sub_cancel]
  ring

set_option maxHeartbeats 1000000 in
include hν'' hν' hPQ hP hnilN hεN in
/-- A simple quotient `M / P'` of `M = Ind (N ⊠ L(i^n))` has `ε_i(M / P') = ε + n` and
`dim E (M / P') = dim N' · (ε + n)!`. -/
theorem quot_facts (P' : Submodule (KLRAlgebra K Q ((μ' + ν'') + ν'))
      (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)))) (hP' : IsCoatom P') :
    epsI Q ((μ' + ν'') + ν') i (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ P') =
        Multiset.card ν'' + Multiset.card ν' ∧
      Module.finrank K (fixSub K (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ P')
          (topIdem Q μ' ν'' ν')) =
        Module.finrank K (HWSpace Q μ' ν'' (ResSub Q μ' ν'' N)) *
          (Multiset.card ν'' + Multiset.card ν').factorial := by
  haveI : FiniteDimensional K (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q))) :=
    finiteDimensional_ind hPQ hP _
  have hnilM : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q ((μ' + ν'') + ν'))
      (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q))) :=
    smulNilpotent_ind_extTensor hPQ hP hnilN (smulNilpotent_klrRep hν')
  haveI : Nontrivial N := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ' + ν'')) N
  haveI : IsSimpleModule (KLRAlgebra K Q ((μ' + ν'') + ν'))
      (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ P') :=
    isSimpleModule_iff_isCoatom.2 hP'
  have hnilQ := fun a => smulNilpotent_quotient P' (hnilM a)
  haveI := isSimpleModule_extTensor hν' (Q := Q) (μ := μ' + ν'') (V := N)
  let f : ExtTensor K N (KLRRep hν' Q) →ₗ[TensorKLR Q (μ' + ν'') ν']
      ResSub Q (μ' + ν'') ν' (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ P') :=
    indAdjFwd P'.mkQ
  have hf0 : f ≠ 0 := by
    intro h0
    apply hP'.1
    refine eq_top_of_tmul_oneConcat_mem fun y => ?_
    have h2 := congrArg Subtype.val (LinearMap.congr_fun h0 y)
    rw [coe_indAdjFwd_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at h2
    exact h2
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact (IsSimpleOrder.eq_bot_or_eq_top _).resolve_right fun h =>
      hf0 (LinearMap.ker_eq_top.1 h)
  have hε := lemma_3_6 hν' hPQ hP f hf
  have hεL : epsI Q ((μ' + ν'') + ν') i
      (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ P') =
        Multiset.card ν'' + Multiset.card ν' := by
    rw [← hε, hεN]
  obtain ⟨φ⟩ := nonempty_hwSpace_equiv_of_embedding hν'' hν' hPQ hP f hnilQ hεL hnilN hεN hf
  refine ⟨hεL, ?_⟩
  have hνε := forall_add_of_forall hν'' hν'
  haveI := isSimpleModule_castMod (Q := Q) (add_assoc μ' ν'' ν').symm
    (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ P')
  have hε' : epsI Q (μ' + (ν'' + ν')) i
      (MAssoc μ' ν'' ν' (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ P')) =
        Multiset.card (ν'' + ν') := by
    rw [epsI_castMod, hεL, Multiset.card_add]
  have hnilMA := smulNilpotent_mAssoc (Q := Q) (μ' := μ') (ν'' := ν'') (ν' := ν') hnilQ
  obtain ⟨h1, -, -⟩ := lemma_3_8 hνε hPQ hP hnilMA hε'
  have hnilΔ : ∀ b, SmulNilpotent ((1 : KLRAlgebra K Q μ') ⊗ₜ[K] x b :
      TensorKLR Q μ' (ν'' + ν')) (ResSub Q μ' (ν'' + ν')
        (MAssoc μ' ν'' ν' (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ P'))) :=
    fun b => smulNilpotent_resSub b (hnilMA _)
  haveI : Module.Free K (HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν')
      (MAssoc μ' ν'' ν' (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ P')))) :=
    Module.Free.of_divisionRing K _
  haveI : FiniteDimensional K (HWSpace Q μ' (ν'' + ν') (ResSub Q μ' (ν'' + ν')
      (MAssoc μ' ν'' ν' (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ P')))) :=
    inferInstance
  rw [(fixSubTopIdemEquiv hν'' hν').finrank_eq,
    ← ((hwEquiv hνε hPQ hP hnilΔ).restrictScalars K).finrank_eq,
    ExtTensor.equivTensor.finrank_eq, Module.finrank_tensorProduct, finrank_klrRep hνε,
    ← (φ.restrictScalars K).finrank_eq, Multiset.card_add]

include hν'' hν' hPQ hP hnilN hεN in
/-- `E P' = 0` for every maximal submodule `P'` of `M = Ind (N ⊠ L(i^n))`. -/
theorem fixSub_coatom_eq_bot (P' : Submodule (KLRAlgebra K Q ((μ' + ν'') + ν'))
      (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)))) (hP' : IsCoatom P') :
    fixSub K P' (topIdem Q μ' ν'' ν') = ⊥ := by
  haveI : FiniteDimensional K (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q))) :=
    finiteDimensional_ind hPQ hP _
  refine fixSub_eq_bot_of_finrank_le topIdem_idem P' ?_
  rw [(quot_facts hν'' hν' hPQ hP hnilN hεN P' hP').2]
  exact finrank_fixSub_topIdem_ind_le' hν'' hν' hPQ hP hnilN hεN

include hν'' hν' hPQ hP hnilN hεN in
/-- **KL I, Lemma 3.9** for `ν = μ' + εi`, `ε = card ν'' = ε_i(N)`. -/
theorem lemma_3_9_core :
    ∃ P' : Submodule (KLRAlgebra K Q ((μ' + ν'') + ν'))
        (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q))),
      IsCoatom P' ∧ (∀ P'' : Submodule (KLRAlgebra K Q ((μ' + ν'') + ν')) _, IsCoatom P'' →
        P'' = P') ∧
      epsI Q ((μ' + ν'') + ν') i (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ P') =
        Multiset.card ν'' + Multiset.card ν' ∧
      ∀ (P₁ : Submodule (KLRAlgebra K Q ((μ' + ν'') + ν'))
          (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)))) (_ : P₁ ≤ P')
        (P₂ : Submodule (KLRAlgebra K Q ((μ' + ν'') + ν')) P₁) [Nontrivial (P₁ ⧸ P₂)],
        epsI Q ((μ' + ν'') + ν') i (P₁ ⧸ P₂) < Multiset.card ν'' + Multiset.card ν' := by
  haveI : FiniteDimensional K (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q))) :=
    finiteDimensional_ind hPQ hP _
  haveI : Nontrivial N := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ' + ν'')) N
  -- `M ≠ 0`, so it has a maximal submodule
  haveI : Nontrivial (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q))) := by
    obtain ⟨w, hw⟩ := exists_ne (0 : N)
    have hy0 : ExtTensor.tmul w (lMk hν' Q 1) ≠ 0 :=
      extTensor_tmul_ne_zero (K := K) (A := KLRAlgebra K Q (μ' + ν''))
        (B := KLRAlgebra K Q ν') hw (lMk_one_ne_zero (K := K) (Q := Q) hν')
    refine ⟨⟨BalancedTensor.tmul oneConcatSubBimod (ExtTensor.tmul w (lMk hν' Q 1)), 0, ?_⟩⟩
    intro h0
    have := congrArg (indDecomp (ν := μ' + ν'') (ν' := ν') hPQ hP
      (ExtTensor K N (KLRRep hν' Q))) h0
    rw [indDecomp_tmul_oneConcat, LinearEquiv.map_zero] at this
    exact hy0 (by simpa using congrFun this shufOne)
  haveI : Module.Finite (KLRAlgebra K Q ((μ' + ν'') + ν'))
      (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q))) :=
    Module.Finite.of_restrictScalars_finite K _ _
  obtain ⟨P', hP', -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule
    (KLRAlgebra K Q ((μ' + ν'') + ν')) (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q))))).resolve_left
    bot_ne_top
  have hq := quot_facts hν'' hν' hPQ hP hnilN hεN P' hP'
  refine ⟨P', hP', fun P'' hP'' => ?_, hq.1, fun P₁ h₁ P₂ _ => ?_⟩
  · haveI : Nontrivial (Ind Q (μ' + ν'') ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ P'') :=
      Submodule.Quotient.nontrivial_of_lt_top _ hP''.1.lt_top
    exact eq_of_isCoatom_of_fixSub_eq_bot topIdem_idem hP'' hP'
      (fixSub_coatom_eq_bot hν'' hν' hPQ hP hnilN hεN P'' hP'')
      (fixSub_coatom_eq_bot hν'' hν' hPQ hP hnilN hεN P' hP')
      ((fixSub_topIdem_ne_bot_iff hν'' hν').2
        (quot_facts hν'' hν' hPQ hP hnilN hεN P'' hP'').1.ge)
  · by_contra hcon
    push_neg at hcon
    exact (fixSub_topIdem_ne_bot_iff hν'' hν').2 hcon (fixSub_subquot_eq_bot topIdem_idem
      (fixSub_coatom_eq_bot hν'' hν' hPQ hP hnilN hεN P' hP') P₁ h₁ P₂)

end Lemma39

section General

variable {μ ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i)
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  {N : Type*} [AddCommGroup N] [Module K N] [Module (KLRAlgebra K Q μ) N]
  [IsScalarTower K (KLRAlgebra K Q μ) N] [FiniteDimensional K N]
  [IsSimpleModule (KLRAlgebra K Q μ) N]
  (hnilN : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q μ) N)

include hν' hPQ hP hnilN in
/-- **KL I, Lemma 3.9** (Kleshchev, Lemma 5.1.5; ungraded): for `N` irreducible
(finite-dimensional, nilpotent dots) and `M = Ind (N ⊠ L(i^n))` (`n = card ν'`):
`M` has a unique maximal submodule `P'` (so `hd M = M / P'` is irreducible,
`isSimpleModule_iff_isCoatom`), `ε_i(hd M) = ε_i(N) + n`, and every nonzero subquotient of `P'`
(i.e. every composition factor of `M` other than `hd M`) has `ε_i < ε_i(N) + n`. -/
theorem lemma_3_9 :
    ∃ P' : Submodule (KLRAlgebra K Q (μ + ν')) (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))),
      IsCoatom P' ∧ (∀ P'' : Submodule (KLRAlgebra K Q (μ + ν')) _, IsCoatom P'' → P'' = P') ∧
      epsI Q (μ + ν') i (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q)) ⧸ P') =
        epsI Q μ i N + Multiset.card ν' ∧
      ∀ (P₁ : Submodule (KLRAlgebra K Q (μ + ν')) (Ind Q μ ν' (ExtTensor K N (KLRRep hν' Q))))
        (_ : P₁ ≤ P') (P₂ : Submodule (KLRAlgebra K Q (μ + ν')) P₁) [Nontrivial (P₁ ⧸ P₂)],
        epsI Q (μ + ν') i (P₁ ⧸ P₂) < epsI Q μ i N + Multiset.card ν' := by
  haveI : Nontrivial N := IsSimpleModule.nontrivial (KLRAlgebra K Q μ) N
  obtain ⟨s, -, hst⟩ := exists_tailLen_eq_epsI (Q := Q) (ν := μ) (i := i) (M := N)
  have hrep : Multiset.replicate (epsI Q μ i N) i ≤ μ :=
    replicate_le_of_hasTail (Seq.hasTail_iff.2 hst.ge)
  obtain ⟨μ', hμ⟩ := Multiset.le_iff_exists_add.1 hrep
  rw [add_comm] at hμ
  set ε := epsI Q μ i N with hε
  clear_value ε
  obtain ⟨ν'', hν''def⟩ : ∃ ν'', Multiset.replicate ε i = ν'' := ⟨_, rfl⟩
  rw [hν''def] at hμ
  subst hμ
  have hν'' : ∀ a ∈ ν'', a = i := fun a ha => Multiset.eq_of_mem_replicate (hν''def ▸ ha)
  have hcard : Multiset.card ν'' = ε := by rw [← hν''def, Multiset.card_replicate]
  have hεN : epsI Q (μ' + ν'') i N = Multiset.card ν'' := by rw [hcard, hε]
  rw [← hcard]
  exact lemma_3_9_core hν'' hν' hPQ hP hnilN hεN

end General

end KLRAlgebra

end Categorification.KLR
