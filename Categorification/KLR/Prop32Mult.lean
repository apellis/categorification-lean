/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Prop32
import Categorification.KLR.Gamma
import Categorification.QuantumGroup.CoproductWords

/-!
# KL I Proposition 3.2: `[Res]` is multiplicative on the image of `γ`, and `[Res] ∘ γ = (γ ⊗ γ) ∘ r`

Khovanov–Lauda I (arXiv:0803.4121v2), §3.1 (TeX lines ~1882–1960): with the twisted
multiplication (3.1) `(x₁ ⊗ x₂)(x₁' ⊗ x₂') = q^{-|x₂|·|x₁'|} x₁x₁' ⊗ x₂x₂'` on
`K₀(R) ⊗ K₀(R)`, **Proposition 3.2**: `[Res]` is an algebra homomorphism. Together with graded
Proposition 2.19 (`GradingDatum.resK0_projP`) this identifies `[Res] ∘ γ` with `(γ ⊗ γ) ∘ r` for
Lusztig's comultiplication `r` (KL's `q` is Lusztig's `v⁻¹`).

## Combinatorics of shuffles (KL I §2.6)

A shuffle `u ∈ ShuffleOf ν ν' s` (`u • s = i_u j_u`) is recorded by its *mask*
`b_u = TypeA.shuffleMask` (`true` at the positions of `s` whose letters go to `j_u`):

* `TypeA.mem_invSet_shuffle` : the inversions of a shuffle `u` are the pairs `a < c` with `a`
  going to the second block and `c` to the first;
* `TypeA.ofFn_inv_inl`, `TypeA.ofFn_inv_inr`, `TypeA.shuffle_eq_of_shuffleMask_eq`,
  `TypeA.exists_shuffle_of_card` : a shuffle is determined by its mask, and every mask with `n`
  entries `false` occurs;
* `KLRAlgebra.ShuffleOf.maskEquiv` : `ShuffleOf ν ν' s ≃ {masks b of s | |s|_{b=false}| = ν,
  |s|_{b=true}| = ν'}`, with `i_u = s|_{b_u=false}`, `j_u = s|_{b_u=true}`
  (`ShuffleOf.ofFn_split_fst`, `ShuffleOf.ofFn_split_snd`);
* `GradingDatum.degW_shuffleWord` : **`deg(ψ_{σ(u)} 1_s) = ∑_{a < c, b_u a, ¬ b_u c}
  degΨ(s_a, s_c)`** (`= PreF.maskInv degΨ s b_u`), via `degW_eq_sum_invSet`.

For a concatenation `st`, masks of `st` are pairs of masks of `s` and `t`
(`PreF.maskAppendEquiv`), the subwords concatenate (`PreF.maskWord_append`) and
(`PreF.maskInv_append`)
`inv(st, b b') = inv(s, b) + inv(t, b') + ∑_{a ∈ s|_{b=true}, c ∈ t|_{b'=false}} degΨ(a, c)`,
i.e. **`deg(u) = deg(u₁) + deg(u₂) - |j_{u₁}| · |i_{u₂}|`** for the KL I grading
(`degΨ(a, c) = -a·c`).

## `[Res]` and `r`

* `GradingDatum.resK0_projP_eq_sum_mask` :
  `[Res_{ν,ν'}] [P_s] = ∑_b q^{inv(s, b)} [P_{s|b=false}] ⊠ [P_{s|b=true}]`;
* `GradingDatum.realize` : `'f ⊗ 'f → K₀(R(ν) ⊗ R(ν'))`, `x ⊗ y ↦ [P_x] ⊠ [P_y]`
  (`(ν, ν')`-component), which is `⊠ ∘ (γ ⊗ γ)` (`GradingDatum.realize_tw`);
* `GradingDatum.resK0_projP_eq_realize` : `[Res_{ν,ν'}] [P_s] = realize (r θ_s)` for `r` with
  pairing `degΨ` and `v = q` (by the shuffle formula `PreF.r_ofFn`);
* `GradingDatum.gammaG` : `γ : 'f_{ℤ[q,q⁻¹]} → K₀(R)`, `θ_i ↦ [P_i]`, for any grading datum
  (`= KLGamma.gammaZ` for the KL I grading, `KLGamma.gammaG_klGradingDatum`);
* `GradingDatum.resComp` : the `(ν, ν')`-component `K₀(R) → K₀(R(ν) ⊗ R(ν'))` of `[Res]`;
* **`GradingDatum.resComp_gammaG`** : `[Res] ∘ γ = (γ ⊗ γ) ∘ r`;
* **`GradingDatum.resComp_gammaG_mul`** (Prop. 3.2 on the image of `γ`):
  `[Res] (γ(x) γ(y)) = (γ ⊗ γ)(r(x) · r(y))`, the product in the twisted tensor square;
* `GradingDatum.resComp_projP_mul_projP` : the explicit form on `[P_s] [P_t]`, the twisted product
  of the expansions of `[Res] [P_s]` and `[Res] [P_t]`;
* **`KLGamma.resComp_gammaZ`**, **`KLGamma.resComp_gammaZ_mul`** : the same for the KL I grading
  and `KLGamma.gammaZ`, with Lusztig's `r` for the Cartan pairing `i · j` and `v = q⁻¹`
  (`PreF.recast_r_neg`; `KLGamma.qToV_qUnitLP_inv` : `q⁻¹ ↦ v` under `qToV`).

## Not formalized here

The product on `⨁_{ν,ν'} K₀(R(ν) ⊗ R(ν'))` itself and the identification
`K₀(R(ν) ⊗ R(ν')) ≅ K₀(R(ν)) ⊗_{ℤ[q,q⁻¹]} K₀(R(ν'))` (which needs the indecomposable projectives
of `R(ν) ⊗ R(ν')` to be the `P_b ⊠ P_{b'}`, i.e. absolute indecomposability). Hence
Proposition 3.2 is proved on the image of `γ` (in particular on the `ℤ[q, q⁻¹]`-span of the
`[P_s]`), with the twisted product computed in `'f ⊗ 'f` and transported by `γ ⊗ γ`, not as an
algebra map on all of `K₀(R)`.
-/

noncomputable section

namespace Categorification

open Equiv

namespace TypeA

/-! ### Shuffles as masks -/

section Mask

variable {n n' m : ℕ} (h : n + n' = m)

/-- The mask of a permutation `u` of `Fin m`: `true` at the positions `a` with `u a` in the second
block `n, …, m - 1`. For a shuffle `u` this records which letters of `s` go to the second factor
of `u • s = i j`. -/
def shuffleMask (_h : n + n' = m) (u : Perm (Fin m)) : Fin m → Bool :=
  fun a => decide (n ≤ (u a : ℕ))

theorem exists_inl_of_lt {z : Fin m} (hz : (z : ℕ) < n) :
    ∃ x : Fin n, z = blockEquiv h (Sum.inl x) :=
  ⟨⟨z, hz⟩, Fin.ext (by simp)⟩

theorem exists_inr_of_le {z : Fin m} (hz : n ≤ (z : ℕ)) :
    ∃ y : Fin n', z = blockEquiv h (Sum.inr y) :=
  ⟨⟨z - n, by have := z.2; omega⟩, Fin.ext (by simp; omega)⟩

theorem shuffleMask_of_inl {u : Perm (Fin m)} {a : Fin m} {x : Fin n}
    (hx : u a = blockEquiv h (Sum.inl x)) : shuffleMask h u a = false := by
  simp [shuffleMask, hx, x.2]

theorem shuffleMask_of_inr {u : Perm (Fin m)} {a : Fin m} {y : Fin n'}
    (hy : u a = blockEquiv h (Sum.inr y)) : shuffleMask h u a = true := by
  simp [shuffleMask, hy]

theorem shuffleMask_eq_false_iff (u : Perm (Fin m)) (a : Fin m) :
    shuffleMask h u a = false ↔ ∃ x : Fin n, u a = blockEquiv h (Sum.inl x) := by
  constructor
  · intro ha
    simp only [shuffleMask, decide_eq_false_iff_not, not_le] at ha
    exact exists_inl_of_lt h ha
  · rintro ⟨x, hx⟩
    exact shuffleMask_of_inl h hx

theorem shuffleMask_eq_true_iff (u : Perm (Fin m)) (a : Fin m) :
    shuffleMask h u a = true ↔ ∃ y : Fin n', u a = blockEquiv h (Sum.inr y) := by
  constructor
  · intro ha
    simp only [shuffleMask, decide_eq_true_eq] at ha
    exact exists_inr_of_le h ha
  · rintro ⟨y, hy⟩
    exact shuffleMask_of_inr h hy

/-- **Inversions of a shuffle**: `(a, c)` with `a < c` is an inversion of the shuffle `u` iff
`a` goes to the second block and `c` to the first. -/
theorem mem_invSet_shuffle {u : Perm (Fin m)} (hu : IsShuffle h u) (a c : Fin m) :
    (a, c) ∈ invSet m u ↔ a < c ∧ shuffleMask h u a = true ∧ shuffleMask h u c = false := by
  rw [mem_invSet]
  simp only [shuffleMask, decide_eq_true_eq, decide_eq_false_iff_not, not_le]
  constructor
  · rintro ⟨hac, hlt⟩
    have hlt' := Fin.lt_iff_val_lt_val.1 hlt
    refine ⟨hac, ?_, ?_⟩
    · by_contra hna
      push_neg at hna
      obtain ⟨x, hx⟩ := exists_inl_of_lt h hna
      obtain ⟨x', hx'⟩ := exists_inl_of_lt h (lt_trans hlt' hna)
      have hxx : x' < x := by
        have := hlt; rw [hx, hx'] at this; exact (blockEquiv_inl_lt_inl h).1 this
      have := hu.1 hxx
      simp only [← hx, ← hx', Perm.inv_apply_self] at this
      exact absurd (hac.trans this) (lt_irrefl _)
    · by_contra hnc
      push_neg at hnc
      obtain ⟨y, hy⟩ := exists_inr_of_le h (hnc.trans hlt'.le)
      obtain ⟨y', hy'⟩ := exists_inr_of_le h hnc
      have hyy : y' < y := by
        have := hlt; rw [hy, hy'] at this; exact (blockEquiv_inr_lt_inr h).1 this
      have := hu.2 hyy
      simp only [← hy, ← hy', Perm.inv_apply_self] at this
      exact absurd (hac.trans this) (lt_irrefl _)
  · rintro ⟨hac, hna, hnc⟩
    exact ⟨hac, Fin.lt_iff_val_lt_val.2 (by omega)⟩

/-- For a shuffle `u`, the positions `u⁻¹(0) < ⋯ < u⁻¹(n - 1)` sent to the first block are the
positions with mask `false`, in increasing order. -/
theorem ofFn_inv_inl {u : Perm (Fin m)} (hu : IsShuffle h u) :
    List.ofFn (fun x : Fin n => u⁻¹ (blockEquiv h (Sum.inl x))) =
      (List.finRange m).filter fun a => shuffleMask h u a == false := by
  have hs₁ := List.sorted_lt_ofFn_iff.2 hu.1
  have hs₂ : ((List.finRange m).filter fun a => shuffleMask h u a == false).Sorted (· < ·) :=
    (List.pairwise_lt_finRange m).filter _
  refine List.eq_of_perm_of_sorted ?_ hs₁ hs₂
  rw [List.perm_ext_iff_of_nodup hs₁.nodup hs₂.nodup]
  intro a
  simp only [List.mem_ofFn, List.mem_filter, List.mem_finRange, true_and, beq_iff_eq,
    shuffleMask_eq_false_iff]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨x, by simp⟩
  · rintro ⟨x, hx⟩; exact ⟨x, by rw [← hx]; simp⟩

/-- For a shuffle `u`, the positions sent to the second block are the positions with mask
`true`, in increasing order. -/
theorem ofFn_inv_inr {u : Perm (Fin m)} (hu : IsShuffle h u) :
    List.ofFn (fun y : Fin n' => u⁻¹ (blockEquiv h (Sum.inr y))) =
      (List.finRange m).filter fun a => shuffleMask h u a == true := by
  have hs₁ := List.sorted_lt_ofFn_iff.2 hu.2
  have hs₂ : ((List.finRange m).filter fun a => shuffleMask h u a == true).Sorted (· < ·) :=
    (List.pairwise_lt_finRange m).filter _
  refine List.eq_of_perm_of_sorted ?_ hs₁ hs₂
  rw [List.perm_ext_iff_of_nodup hs₁.nodup hs₂.nodup]
  intro a
  simp only [List.mem_ofFn, List.mem_filter, List.mem_finRange, true_and, beq_iff_eq,
    shuffleMask_eq_true_iff]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, by simp⟩
  · rintro ⟨y, hy⟩; exact ⟨y, by rw [← hy]; simp⟩

/-- A shuffle is determined by its mask. -/
theorem shuffle_eq_of_shuffleMask_eq {u u' : Perm (Fin m)} (hu : IsShuffle h u)
    (hu' : IsShuffle h u') (he : shuffleMask h u = shuffleMask h u') : u = u' := by
  have h₁ := List.ofFn_injective ((ofFn_inv_inl h hu).trans (he ▸ (ofFn_inv_inl h hu').symm))
  have h₂ := List.ofFn_injective ((ofFn_inv_inr h hu).trans (he ▸ (ofFn_inv_inr h hu').symm))
  rw [← inv_inj]
  ext z
  obtain ⟨t, rfl⟩ := (blockEquiv h).surjective z
  cases t with
  | inl x => exact congrArg Fin.val (congrFun h₁ x)
  | inr y => exact congrArg Fin.val (congrFun h₂ y)

/-- Every mask with `n` entries `false` is the mask of a shuffle. -/
theorem exists_shuffle_of_card (b : Fin m → Bool)
    (hb : (Finset.univ.filter fun a => b a = false).card = n) :
    ∃ u : Perm (Fin m), IsShuffle h u ∧ shuffleMask h u = b := by
  classical
  have hcF : Fintype.card {a // b a = false} = n := by rw [Fintype.card_subtype, hb]
  have hcT : Fintype.card {a // ¬ b a = false} = n' := by
    rw [Fintype.card_subtype_compl, hcF, Fintype.card_fin]; omega
  let g : Fin m ≃ Fin n ⊕ Fin n' := (Equiv.sumCompl fun a => b a = false).symm.trans
    (Equiv.sumCongr (Fintype.equivFinOfCardEq hcF) (Fintype.equivFinOfCardEq hcT))
  obtain ⟨a₁, b₁, u, hu, hw⟩ := exists_blockPerm_mul h (g.trans (blockEquiv h))
  have hu' : u = (blockPerm h a₁ b₁)⁻¹ * g.trans (blockEquiv h) := by rw [← hw, inv_mul_cancel_left]
  refine ⟨u, hu, funext fun a => ?_⟩
  by_cases hba : b a = false
  · have hg : g a = Sum.inl (Fintype.equivFinOfCardEq hcF ⟨a, hba⟩) := by
      change Sum.map _ _ ((Equiv.sumCompl fun a => b a = false).symm a) = _
      rw [sumCompl_apply_symm_of_pos (fun a => b a = false) a hba]
      rfl
    rw [hba]
    refine shuffleMask_of_inl h (x := a₁⁻¹ (Fintype.equivFinOfCardEq hcF ⟨a, hba⟩)) ?_
    rw [hu', blockPerm_inv, Perm.mul_apply, Equiv.trans_apply, hg, blockPerm_inl]
  · have hg : g a = Sum.inr (Fintype.equivFinOfCardEq hcT ⟨a, hba⟩) := by
      change Sum.map _ _ ((Equiv.sumCompl fun a => b a = false).symm a) = _
      rw [sumCompl_apply_symm_of_neg (fun a => b a = false) a hba]
      rfl
    rw [show b a = true by simpa using hba]
    refine shuffleMask_of_inr h (y := b₁⁻¹ (Fintype.equivFinOfCardEq hcT ⟨a, hba⟩)) ?_
    rw [hu', blockPerm_inv, Perm.mul_apply, Equiv.trans_apply, hg, blockPerm_inr]

end Mask

end TypeA

namespace KLR

open TypeA QuantumGroup QuantumGroup.PreF Graded KLRAlgebra LaurentPolynomial MvPolynomial

variable {I : Type*} [DecidableEq I] {ν ν' : Multiset I}

/-! ### Sequences and lists -/

namespace KLRAlgebra.Seq

omit [DecidableEq I] in
theorem coe_ofFn (i : Seq ν) : ((List.ofFn i.1 : List I) : Multiset I) = ν := by
  rw [← Fin.univ_val_map]; exact i.2

omit [DecidableEq I] in
theorem ofList_ofFn (i : Seq ν) (h : ((List.ofFn i.1 : List I) : Multiset I) = ν) :
    Seq.ofList (List.ofFn i.1) h = i := by
  apply Subtype.ext
  funext a
  change (Seq.ofList (List.ofFn i.1) h).lbl a = _
  rw [Seq.ofList_lbl, List.getElem_ofFn]

omit [DecidableEq I] in
theorem ofList_eq_of_eq {l : List I} (h : (l : Multiset I) = ν) {i : Seq ν}
    (hl : l = List.ofFn i.1) : Seq.ofList l h = i := by
  subst hl
  exact ofList_ofFn i h

omit [DecidableEq I] in
theorem ofFn_ofList (l : List I) (h : (l : Multiset I) = ν) :
    List.ofFn (Seq.ofList l h).1 = l := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]; rw [← Multiset.coe_card, h]
  · intro a h₁ h₂
    rw [List.getElem_ofFn]
    exact Seq.ofList_lbl l h _

end KLRAlgebra.Seq

/-! ### Shuffles of a sequence as masks -/

namespace KLRAlgebra

/-- The mask of a shuffle `u` of `s` (`u • s = i j`): `true` at the positions of `s` whose
letters go to `j`. -/
abbrev ShuffleOf.mask {s : Seq (ν + ν')} (u : ShuffleOf ν ν' s) :
    Fin (Multiset.card (ν + ν')) → Bool :=
  shuffleMask (Seq.card_add' ν ν') u.1.1

theorem ShuffleOf.split_fst_apply {s : Seq (ν + ν')} (u : ShuffleOf ν ν' s)
    (x : Fin (Multiset.card ν)) :
    u.split.1.1 x = s.1 (u.1.1⁻¹ (blockEquiv (Seq.card_add' ν ν') (Sum.inl x))) := by
  have := congrArg (fun t : Seq (ν + ν') => t.1 (Seq.posL ν' x)) u.split_spec
  simp only [Seq.append_posL, Seq.smul_apply] at this
  rw [this, Perm.inv_def]
  rfl

theorem ShuffleOf.split_snd_apply {s : Seq (ν + ν')} (u : ShuffleOf ν ν' s)
    (y : Fin (Multiset.card ν')) :
    u.split.2.1 y = s.1 (u.1.1⁻¹ (blockEquiv (Seq.card_add' ν ν') (Sum.inr y))) := by
  have := congrArg (fun t : Seq (ν + ν') => t.1 (Seq.posR ν y)) u.split_spec
  simp only [Seq.append_posR, Seq.smul_apply] at this
  rw [this, Perm.inv_def]
  rfl

/-- `i_u` is the subword of `s` at the positions with mask `false`. -/
theorem ShuffleOf.ofFn_split_fst {s : Seq (ν + ν')} (u : ShuffleOf ν ν' s) :
    List.ofFn u.split.1.1 = FreeMonoid.toList (maskWord s.1 u.mask false) := by
  rw [toList_maskWord, ← ofFn_inv_inl _ u.1.2, List.map_ofFn]
  exact congrArg List.ofFn (funext u.split_fst_apply)

/-- `j_u` is the subword of `s` at the positions with mask `true`. -/
theorem ShuffleOf.ofFn_split_snd {s : Seq (ν + ν')} (u : ShuffleOf ν ν' s) :
    List.ofFn u.split.2.1 = FreeMonoid.toList (maskWord s.1 u.mask true) := by
  rw [toList_maskWord, ← ofFn_inv_inr _ u.1.2, List.map_ofFn]
  exact congrArg List.ofFn (funext u.split_snd_apply)

theorem ShuffleOf.wt_mask_false {s : Seq (ν + ν')} (u : ShuffleOf ν ν' s) :
    wt (maskWord s.1 u.mask false) = ν := by
  rw [wt, ← u.ofFn_split_fst, Seq.coe_ofFn]

theorem ShuffleOf.wt_mask_true {s : Seq (ν + ν')} (u : ShuffleOf ν ν' s) :
    wt (maskWord s.1 u.mask true) = ν' := by
  rw [wt, ← u.ofFn_split_snd, Seq.coe_ofFn]

theorem ShuffleOf.mask_injective (s : Seq (ν + ν')) :
    Function.Injective (fun u : ShuffleOf ν ν' s => u.mask) := fun u u' he =>
  Subtype.ext (Subtype.ext (shuffle_eq_of_shuffleMask_eq _ u.1.2 u'.1.2 he))

/-- A mask of `s` splitting it into subwords of weights `ν` and `ν'` is the mask of a shuffle
`u ∈ ShuffleOf ν ν' s`. -/
theorem ShuffleOf.exists_mask_eq {s : Seq (ν + ν')} (b : Fin (Multiset.card (ν + ν')) → Bool)
    (h₁ : wt (maskWord s.1 b false) = ν) (h₂ : wt (maskWord s.1 b true) = ν') :
    ∃ u : ShuffleOf ν ν' s, u.mask = b := by
  have hcard : (Finset.univ.filter fun a => b a = false).card = Multiset.card ν := by
    have := congrArg Multiset.card h₁
    rw [wt_maskWord, Multiset.card_map] at this
    exact this
  obtain ⟨u, hu, hb⟩ := exists_shuffle_of_card (Seq.card_add' ν ν') b hcard
  have hL₁ : List.ofFn (fun x => s.1 (u⁻¹ (blockEquiv (Seq.card_add' ν ν') (Sum.inl x)))) =
      FreeMonoid.toList (maskWord s.1 b false) := by
    rw [toList_maskWord, ← hb, ← ofFn_inv_inl _ hu, List.map_ofFn]; rfl
  have hL₂ : List.ofFn (fun y => s.1 (u⁻¹ (blockEquiv (Seq.card_add' ν ν') (Sum.inr y)))) =
      FreeMonoid.toList (maskWord s.1 b true) := by
    rw [toList_maskWord, ← hb, ← ofFn_inv_inr _ hu, List.map_ofFn]; rfl
  refine ⟨⟨⟨u, hu⟩, mem_concatSet.2
    ⟨⟨fun x => s.1 (u⁻¹ (blockEquiv (Seq.card_add' ν ν') (Sum.inl x))), ?_⟩,
      ⟨fun y => s.1 (u⁻¹ (blockEquiv (Seq.card_add' ν ν') (Sum.inr y))), ?_⟩, ?_⟩⟩, hb⟩
  · rw [Fin.univ_val_map, hL₁]; exact h₁
  · rw [Fin.univ_val_map, hL₂]; exact h₂
  · apply Subtype.ext
    funext z
    obtain ⟨t, rfl⟩ := (blockEquiv (Seq.card_add' ν ν')).surjective z
    cases t with
    | inl x =>
      rw [show blockEquiv (Seq.card_add' ν ν') (Sum.inl x) = Seq.posL ν' x from rfl,
        Seq.append_posL, Seq.smul_apply, ← Perm.inv_def]
      rfl
    | inr y =>
      rw [show blockEquiv (Seq.card_add' ν ν') (Sum.inr y) = Seq.posR ν y from rfl,
        Seq.append_posR, Seq.smul_apply, ← Perm.inv_def]
      rfl

/-- **Shuffles of `s` are masks of `s`**: `u ↦ b_u` identifies `ShuffleOf ν ν' s` with the masks
of `s` splitting it into subwords of weights `ν` and `ν'`; then `(i_u, j_u)` are the two subwords
(`ShuffleOf.ofFn_split_fst`, `ShuffleOf.ofFn_split_snd`). -/
noncomputable def ShuffleOf.maskEquiv (s : Seq (ν + ν')) :
    ShuffleOf ν ν' s ≃ {b : Fin (Multiset.card (ν + ν')) → Bool //
      wt (maskWord s.1 b false) = ν ∧ wt (maskWord s.1 b true) = ν'} :=
  Equiv.ofBijective (fun u => ⟨u.mask, u.wt_mask_false, u.wt_mask_true⟩)
    ⟨fun u u' he => ShuffleOf.mask_injective s (congrArg Subtype.val he),
     fun b => by
      obtain ⟨u, hu⟩ := ShuffleOf.exists_mask_eq b.1 b.2.1 b.2.2
      exact ⟨u, Subtype.ext hu⟩⟩

end KLRAlgebra

/-! ### `[Res] [P_s]` as `r(θ_s)` -/

namespace GradingDatum

variable {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k} (G : GradingDatum Q)

omit [DecidableEq I] in
/-- **The degree of the shuffle diagram `ψ_{σ(u)} 1_s`** (KL I §2.6, via
`degW_eq_sum_invSet`): it is `inv(s, b_u) = ∑_{a < c, b_u a = true, b_u c = false}
degΨ(s_a, s_c)`, the sum over the pairs of strands that cross, i.e. a letter of `j_u` to the left
of a letter of `i_u` in `s`. -/
theorem degW_shuffleWord (s : Seq (ν + ν')) (u : Shuffle (Seq.card_add' ν ν')) :
    G.degW (shuffleWord u) s = maskInv G.degΨ s.1 (shuffleMask (Seq.card_add' ν ν') u.1) := by
  rw [G.degW_eq_sum_invSet (shuffleWord_spec u).1, (shuffleWord_spec u).2, maskInv,
    ← Fintype.sum_prod_type', ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ⟨a, c⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_invSet_shuffle _ u.2 a c

variable {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

variable (ν ν') in
/-- `[P_x] ⊠ [P_y] ∈ K₀(R(ν) ⊗ R(ν'))` for words `x`, `y` of weights `ν`, `ν'`, and `0` for words
of other weights: the `(ν, ν')`-component of the class of `x ⊗ y ∈ K₀(R) ⊗ K₀(R)`. -/
def extWords (x y : FreeMonoid I) : K0 (tensorGrading (G.grade ν) (G.grade ν')) :=
  if h : wt x = ν ∧ wt y = ν' then
    K0.extTensor (G.grade ν) (G.grade ν')
      (K0.of (G.projP (Seq.ofList (FreeMonoid.toList x) h.1)))
      (K0.of (G.projP (Seq.ofList (FreeMonoid.toList y) h.2)))
  else 0

/-- **KL I, Proposition 2.19 in `K₀`, indexed by masks**:
`[Res_{ν,ν'}] [P_s] = ∑_b q^{inv(s, b)} [P_{s|b=false}] ⊠ [P_{s|b=true}]`, the sum over all masks
`b` of `s` (only those splitting `s` into subwords of weights `ν`, `ν'` contribute). -/
theorem resK0_projP_eq_sum_mask (s : Seq (ν + ν')) :
    G.resK0 ν ν' hPQ hP (K0.of (G.projP s)) =
      ∑ b : Fin (Multiset.card (ν + ν')) → Bool,
        (T (maskInv G.degΨ s.1 b) : LaurentPolynomial ℤ) •
          G.extWords ν ν' (maskWord s.1 b false) (maskWord s.1 b true) := by
  rw [G.resK0_projP hPQ hP]
  refine Fintype.sum_of_injective (fun u : ShuffleOf ν ν' s => u.mask)
    (ShuffleOf.mask_injective s) _ _ ?_ ?_
  · intro b hb
    rw [extWords, dif_neg, smul_zero]
    rintro ⟨h₁, h₂⟩
    obtain ⟨u, hu⟩ := ShuffleOf.exists_mask_eq b h₁ h₂
    exact hb ⟨u, hu⟩
  · intro u
    rw [G.degW_shuffleWord, extWords, dif_pos ⟨u.wt_mask_false, u.wt_mask_true⟩,
      Seq.ofList_eq_of_eq _ u.ofFn_split_fst.symm, Seq.ofList_eq_of_eq _ u.ofFn_split_snd.symm]

variable (ν ν') in
/-- The realisation map `'f ⊗ 'f → K₀(R(ν) ⊗ R(ν'))`, `x ⊗ y ↦ [P_x] ⊠ [P_y]` on words (the
`(ν, ν')`-component; words of other weights go to `0`), on the twisted tensor square for any
twisting cocycle. -/
def realize {σ : TwistCocycle (LaurentPolynomial ℤ) (FreeMonoid I × FreeMonoid I)} :
    TwistedMonoidAlgebra σ →ₗ[LaurentPolynomial ℤ] K0 (tensorGrading (G.grade ν) (G.grade ν')) :=
  TwistedMonoidAlgebra.lift fun p => G.extWords ν ν' p.1 p.2

theorem realize_single {σ : TwistCocycle (LaurentPolynomial ℤ) (FreeMonoid I × FreeMonoid I)}
    (x y : FreeMonoid I) (c : LaurentPolynomial ℤ) :
    G.realize ν ν' (TwistedMonoidAlgebra.single (σ := σ) (x, y) c) = c • G.extWords ν ν' x y :=
  TwistedMonoidAlgebra.lift_single _ _ _

/-- **KL I, Proposition 2.19 as Lusztig's `r`**: `[Res_{ν,ν'}] [P_s]` is the `(ν, ν')`-component of
the realisation of `r(θ_{s_1} ⋯ θ_{s_m}) ∈ 'f ⊗ 'f`, where `r` is taken for the pairing
`degΨ` and `v = q` (for the KL I grading `degΨ(i, j) = -i·j`; see `resK0_gammaZ` for Lusztig's
normalisation `v = q⁻¹`). -/
theorem resK0_projP_eq_realize (s : Seq (ν + ν')) :
    G.resK0 ν ν' hPQ hP (K0.of (G.projP s)) =
      G.realize ν ν' (r G.degΨ qUnitLP (word (FreeMonoid.ofList (List.ofFn s.1)))) := by
  rw [r_ofFn, map_sum, G.resK0_projP_eq_sum_mask hPQ hP]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [realize_single, val_qUnitLP_zpow]

/-! ### `γ : 'f → K₀(R)` for a general grading datum -/

/-- The class `[P_l] ∈ K₀(R(|l|)) ⊆ K₀(R)` of a sequence `l`. -/
def clsW (l : List I) : G.K0R :=
  DirectSum.of G.K0fam (l : Multiset I) (K0.of (G.projP (Seq.ofList l rfl)))

theorem clsW_eq {μ : Multiset I} (l : List I) (h : (l : Multiset I) = μ) :
    G.clsW l = DirectSum.of G.K0fam μ (K0.of (G.projP (Seq.ofList l h))) := by
  subst h; rfl

/-- `[P_l] [P_{l'}] = [P_{ll'}]` in `K₀(R)`. -/
theorem clsW_append (l l' : List I) : G.clsW (l ++ l') = G.clsW l * G.clsW l' := by
  rw [G.clsW_eq (l ++ l') (Multiset.coe_add l l').symm, KLGamma.seq_ofList_append, clsW, clsW,
    K0R_of_mul_of, G.indK0_projP]

/-- `[P_∅] = 1`. -/
theorem clsW_nil : G.clsW [] = 1 := by
  rw [G.K0R_one, clsW]
  congr 1
  rw [← K0.of_eq_of_iso GProj.ofIdempotentOneIso]
  refine K0.of_ofIdempotent_congr ?_ _ _ _ _
  have := sum_e (k := k) (Q := Q) (ν := 0)
  rwa [Fintype.sum_unique,
    ← Subsingleton.elim (α := Seq (0 : Multiset I)) (Seq.ofList [] rfl) default] at this

/-- `w ↦ [P_w]`, a monoid homomorphism `FreeMonoid I → K₀(R)`. -/
def clsWHom : FreeMonoid I →* G.K0R where
  toFun w := G.clsW (FreeMonoid.toList w)
  map_one' := G.clsW_nil
  map_mul' u w := by rw [FreeMonoid.toList_mul, clsW_append]

/-- **`γ : 'f_{ℤ[q,q⁻¹]} → K₀(R)`**, `θ_i ↦ [P_i]`, for a general grading datum (for the KL I
grading this is `KLGamma.gammaZ`, see `gammaG_klGradingDatum`). -/
def gammaG : PreF (LaurentPolynomial ℤ) I →ₐ[LaurentPolynomial ℤ] G.K0R :=
  MonoidAlgebra.lift (LaurentPolynomial ℤ) (FreeMonoid I) G.K0R G.clsWHom

theorem gammaG_word (w : FreeMonoid I) :
    G.gammaG (word w) = G.clsW (FreeMonoid.toList w) := by
  rw [gammaG, word, MonoidAlgebra.lift_single, one_smul]
  rfl

/-- The `μ`-component of `[P_l]`. -/
theorem component_clsW (μ : Multiset I) (l : List I) :
    DirectSum.component (LaurentPolynomial ℤ) (Multiset I) G.K0fam μ (G.clsW l) =
      if h : (l : Multiset I) = μ then K0.of (G.projP (Seq.ofList l h)) else 0 := by
  by_cases h : (l : Multiset I) = μ
  · subst h
    rw [dif_pos rfl, clsW, ← DirectSum.lof_eq_of (LaurentPolynomial ℤ),
      DirectSum.component.lof_self]
  · rw [dif_neg h, clsW, ← DirectSum.lof_eq_of (LaurentPolynomial ℤ),
      DirectSum.component.of, dif_neg h]

variable (ν ν') in
/-- The `(ν, ν')`-component `K₀(R) → K₀(R(ν) ⊗ R(ν'))` of `[Res]` (KL I §3.1): the projection to
`K₀(R(ν + ν'))` followed by `[Res_{ν,ν'}]`. -/
def resComp : G.K0R →ₗ[LaurentPolynomial ℤ] K0 (tensorGrading (G.grade ν) (G.grade ν')) :=
  G.resK0 ν ν' hPQ hP ∘ₗ DirectSum.component (LaurentPolynomial ℤ) (Multiset I) G.K0fam (ν + ν')

omit [DecidableEq I] in
private theorem wt_maskWord_add {m : ℕ} (w : Fin m → I) (b : Fin m → Bool) :
    wt (maskWord w b false) + wt (maskWord w b true) = ((List.ofFn w : List I) : Multiset I) := by
  rw [wt_maskWord, wt_maskWord, ← Multiset.map_add, ← Fin.univ_val_map, Finset.filter_val,
    Finset.filter_val]
  congr 1
  convert Multiset.filter_add_not (fun a => b a = false) Finset.univ.val using 3
  simp

/-- **`[Res] ∘ γ = (γ ⊗ γ) ∘ r`** (KL I §3.1, Proposition 3.2 and its proof), `(ν, ν')`-component,
for Lusztig's `r` with the pairing `degΨ` and `v = q`: for every `x ∈ 'f_{ℤ[q,q⁻¹]}`,
`[Res_{ν,ν'}] (γ x)_{ν + ν'} = (γ ⊗ γ)(r x)_{ν,ν'}`. -/
theorem resComp_gammaG (x : PreF (LaurentPolynomial ℤ) I) :
    G.resComp ν ν' hPQ hP (G.gammaG x) = G.realize ν ν' (r G.degΨ qUnitLP x) := by
  have key : G.resComp ν ν' hPQ hP ∘ₗ G.gammaG.toLinearMap =
      G.realize ν ν' ∘ₗ (r G.degΨ qUnitLP).toLinearMap := by
    refine PreF.lhom_ext fun w => ?_
    obtain ⟨m, f, rfl⟩ : ∃ (m : ℕ) (f : Fin m → I), FreeMonoid.ofList (List.ofFn f) = w :=
      ⟨_, (FreeMonoid.toList w).get, by rw [List.ofFn_get]; rfl⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
    rw [gammaG_word, FreeMonoid.toList_ofList, resComp, LinearMap.comp_apply, component_clsW]
    by_cases h : ((List.ofFn f : List I) : Multiset I) = ν + ν'
    · rw [dif_pos h, G.resK0_projP_eq_realize hPQ hP, Seq.ofFn_ofList]
    · rw [dif_neg h, map_zero, r_ofFn, map_sum]
      refine (Finset.sum_eq_zero fun b _ => ?_).symm
      rw [realize_single, extWords, dif_neg, smul_zero]
      rintro ⟨h₁, h₂⟩
      exact h (by rw [← wt_maskWord_add f b, h₁, h₂])
  exact LinearMap.congr_fun key x

/-- **KL I, Proposition 3.2 (on the image of `γ`)**: `[Res]` is multiplicative for the twisted
multiplication (3.1): for `x, y ∈ 'f_{ℤ[q,q⁻¹]}`,
`[Res_{ν,ν'}] (γ(x) γ(y))_{ν + ν'} = (γ ⊗ γ)(r(x) · r(y))_{ν,ν'}`, where `r(x) · r(y)` is the
product in the twisted tensor square
`(x₁ ⊗ x₂)(y₁ ⊗ y₂) = q^{|x₂| ⋄ |y₁|} x₁y₁ ⊗ x₂y₂`, `|x₂| ⋄ |y₁| = ∑ degΨ(a, b)` (for the KL I
grading, `q^{-|x₂|·|y₁|}`). -/
theorem resComp_gammaG_mul (x y : PreF (LaurentPolynomial ℤ) I) :
    G.resComp ν ν' hPQ hP (G.gammaG x * G.gammaG y) =
      G.realize ν ν' (r G.degΨ qUnitLP x * r G.degΨ qUnitLP y) := by
  rw [← map_mul, resComp_gammaG, map_mul]

/-- **KL I, Proposition 3.2 on `[P_s] [P_t]`, explicitly**: with the twisted multiplication (3.1),
`[Res_{ν,ν'}] ([P_s] [P_t]) = ∑_{b, b'} q^{inv(s, b) + inv(t, b') + |t|_{b'=false}| ⋄' |s|_{b=true}|}
[P_{s|b=false} t|b'=false}] ⊠ [P_{s|b=true} t|b'=true}]`, i.e. the product of
`[Res] [P_s] = ∑_b q^{inv(s, b)} [P_{s|b=false}] ⊗ [P_{s|b=true}]` and
`[Res] [P_t] = ∑_{b'} q^{inv(t, b')} [P_{t|b'=false}] ⊗ [P_{t|b'=true}]`
(`resK0_projP_eq_sum_mask`) in the twisted algebra, where the twist is
`wdot degΨ |x₂| |x₁'| = ∑_{a ∈ x₂, c ∈ x₁'} degΨ(a, c)`. -/
theorem resComp_clsW_mul_clsW {m m' : ℕ} (f : Fin m → I) (f' : Fin m' → I) :
    G.resComp ν ν' hPQ hP (G.clsW (List.ofFn f) * G.clsW (List.ofFn f')) =
      ∑ b : Fin m → Bool, ∑ b' : Fin m' → Bool,
        (T (maskInv G.degΨ f b + maskInv G.degΨ f' b' +
            wdot G.degΨ (wt (maskWord f b true)) (wt (maskWord f' b' false))) :
            LaurentPolynomial ℤ) •
          G.extWords ν ν' (maskWord f b false * maskWord f' b' false)
            (maskWord f b true * maskWord f' b' true) := by
  have h₁ := G.gammaG_word (FreeMonoid.ofList (List.ofFn f))
  have h₂ := G.gammaG_word (FreeMonoid.ofList (List.ofFn f'))
  rw [FreeMonoid.toList_ofList] at h₁ h₂
  rw [← h₁, ← h₂, resComp_gammaG_mul, r_ofFn, r_ofFn, Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [twSq_single_mul_single, realize_single]
  congr 1
  simp only [← Units.val_mul, ← zpow_add, val_qUnitLP_zpow, ← T_add]
  congr 1
  ring

theorem clsW_ofFn {μ : Multiset I} (s : Seq μ) :
    G.clsW (List.ofFn s.1) = DirectSum.of G.K0fam μ (K0.of (G.projP s)) := by
  rw [G.clsW_eq _ (Seq.coe_ofFn s), Seq.ofList_ofFn]

/-- **KL I, Proposition 3.2 on `[P_s] [P_t]`** (`s ∈ Seq μ`, `t ∈ Seq μ'`): the
`(ν, ν')`-component of `[Res] ([P_s] [P_t])` is the twisted product of
`[Res] [P_s] = ∑_b q^{inv(s, b)} [P_{s|b=false}] ⊗ [P_{s|b=true}]` and
`[Res] [P_t] = ∑_{b'} q^{inv(t, b')} [P_{t|b'=false}] ⊗ [P_{t|b'=true}]`
(`resK0_projP_eq_sum_mask`): the term `(b, b')` is
`q^{inv(s, b) + inv(t, b') + |s|_{b=true}| ⋄ |t|_{b'=false}|} [P_{s|b=false} t|b'=false}] ⊠
[P_{s|b=true} t|b'=true}]`. -/
theorem resComp_projP_mul_projP {μ μ' : Multiset I} (s : Seq μ) (t : Seq μ') :
    G.resComp ν ν' hPQ hP (DirectSum.of G.K0fam μ (K0.of (G.projP s)) *
        DirectSum.of G.K0fam μ' (K0.of (G.projP t))) =
      ∑ b : Fin (Multiset.card μ) → Bool, ∑ b' : Fin (Multiset.card μ') → Bool,
        (T (maskInv G.degΨ s.1 b + maskInv G.degΨ t.1 b' +
            wdot G.degΨ (wt (maskWord s.1 b true)) (wt (maskWord t.1 b' false))) :
            LaurentPolynomial ℤ) •
          G.extWords ν ν' (maskWord s.1 b false * maskWord t.1 b' false)
            (maskWord s.1 b true * maskWord t.1 b' true) := by
  rw [← clsW_ofFn, ← clsW_ofFn, resComp_clsW_mul_clsW]

/-- The realisation map is `⊠ ∘ (γ ⊗ γ)`: `x ⊗ y ↦ (γ x)_ν ⊠ (γ y)_{ν'}`. -/
theorem realize_tw {dot : I → I → ℤ} {v : (LaurentPolynomial ℤ)ˣ}
    (x y : PreF (LaurentPolynomial ℤ) I) :
    G.realize ν ν' (tw dot v x y) =
      K0.extTensor (G.grade ν) (G.grade ν')
        (DirectSum.component (LaurentPolynomial ℤ) (Multiset I) G.K0fam ν (G.gammaG x))
        (DirectSum.component (LaurentPolynomial ℤ) (Multiset I) G.K0fam ν' (G.gammaG y)) := by
  induction x using PreF.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [tw_add_left, map_add, hx, hx', LinearMap.add_apply]
  | smul_word u c =>
    induction y using PreF.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [tw_add_right, map_add, hy, hy']
    | smul_word w c' =>
      simp only [tw_smul_left, tw_smul_right, tw_word, map_smul, LinearMap.smul_apply,
        gammaG_word, component_clsW, realize_single, one_smul]
      rw [extWords]
      by_cases hu : ((FreeMonoid.toList u : List I) : Multiset I) = ν
      · by_cases hw : ((FreeMonoid.toList w : List I) : Multiset I) = ν'
        · rw [dif_pos ⟨hu, hw⟩, dif_pos hu, dif_pos hw]
        · rw [dif_neg (fun h => hw h.2), dif_neg hw, map_zero, smul_zero, smul_zero]
      · rw [dif_neg (fun h => hu h.1), dif_neg hu, map_zero, LinearMap.zero_apply, smul_zero,
          smul_zero]

/-- The realisation map does not see the twisting cocycle. -/
theorem realize_recast {σ σ' : TwistCocycle (LaurentPolynomial ℤ) (FreeMonoid I × FreeMonoid I)}
    (y : TwistedMonoidAlgebra σ) :
    G.realize ν ν' (TwistedMonoidAlgebra.recast σ σ' y) = G.realize ν ν' y := rfl

end GradingDatum

/-! ### The KL I grading: Lusztig's normalisation `v = q⁻¹` -/

namespace KLGamma

variable (k : Type*) [Field k] (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

local notation "Gkl" => klGradingDatum k Γ

/-- For the KL I grading, `γ` of a general grading datum is `KLGamma.gammaZ`. -/
theorem gammaG_klGradingDatum : (Gkl).gammaG = gammaZ k Γ :=
  MonoidAlgebra.algHom_ext fun w => by
    change (Gkl).gammaG (PreF.word w) = gammaZ k Γ (PreF.word w)
    rw [GradingDatum.gammaG_word, gammaZ_word]
    rfl

theorem degΨ_klGradingDatum : (Gkl).degΨ = fun a c => -(KL.C Γ).dot a c := rfl

omit [DecidableEq I] in
/-- The parameter `v = q⁻¹` of `resComp_gammaZ` goes to Lusztig's `v` under the base change
`qToV : ℤ[q, q⁻¹] → ℚ(v)`, `q ↦ v⁻¹`, used for `γ_{ℚ(q)}` (`KLGamma.gammaQ`). -/
theorem qToV_qUnitLP_inv :
    qToV ((qUnitLP⁻¹ : (LaurentPolynomial ℤ)ˣ) : LaurentPolynomial ℤ) = (vQ : RatFunc ℚ) := by
  change qToV (T (-1)) = _
  rw [qToV_T]
  simp

variable {Γ} {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → klQ Γ a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

/-- **KL I §3.1, `[Res] ∘ γ = (γ ⊗ γ) ∘ r`**, for the KL I grading and Lusztig's comultiplication
`r` with the Cartan pairing `i · j` and `v = q⁻¹` ("our `q` is Lusztig's `v⁻¹`"): for every
`x ∈ 'f_{ℤ[q,q⁻¹]}` and all `ν, ν'`,
`[Res_{ν,ν'}] (γ x)_{ν+ν'} = (γ ⊗ γ)(r x)_{ν,ν'}`, where `(γ ⊗ γ)(y ⊗ y')_{ν,ν'} =
(γ y)_ν ⊠ (γ y')_{ν'}` (`GradingDatum.realize_tw`). -/
theorem resComp_gammaZ (x : PreF (LaurentPolynomial ℤ) I) :
    (Gkl).resComp ν ν' hPQ hP (gammaZ k Γ x) =
      (Gkl).realize ν ν' (r (KL.C Γ).dot qUnitLP⁻¹ x) := by
  rw [← gammaG_klGradingDatum, GradingDatum.resComp_gammaG, degΨ_klGradingDatum,
    ← recast_r_neg, GradingDatum.realize_recast]

/-- **KL I, Proposition 3.2 (on the image of `γ`)**, KL I grading, Lusztig's normalisation: for
`x, y ∈ 'f_{ℤ[q,q⁻¹]}`,
`[Res_{ν,ν'}] (γ(x) γ(y))_{ν+ν'} = (γ ⊗ γ)(r(x) · r(y))_{ν,ν'}`, the product `r(x) · r(y)` taken
in the twisted tensor square `(x₁ ⊗ x₂)(y₁ ⊗ y₂) = v^{|x₂|·|y₁|} x₁y₁ ⊗ x₂y₂` with `v = q⁻¹`,
i.e. KL's `q^{-|x₂|·|y₁|}` (eq. (3.1)). -/
theorem resComp_gammaZ_mul (x y : PreF (LaurentPolynomial ℤ) I) :
    (Gkl).resComp ν ν' hPQ hP (gammaZ k Γ x * gammaZ k Γ y) =
      (Gkl).realize ν ν' (r (KL.C Γ).dot qUnitLP⁻¹ x * r (KL.C Γ).dot qUnitLP⁻¹ y) := by
  rw [← map_mul, resComp_gammaZ, map_mul]

end KLGamma

end KLR

end Categorification
