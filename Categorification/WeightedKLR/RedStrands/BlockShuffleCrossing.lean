/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.InductionFree
import Categorification.KLR.Spanning
import Categorification.TypeA.Matsumoto

/-!
# Right crossings and the shuffle filtration

For the calculation in Webster (arXiv:1309.3796v2), §6.1, Lemma 6.8, a
right crossing on a binary shuffle either extends it or acts inside one block
in the cases below. The comparison has a lower crossing-filtration error.
Coordinates in the free induction basis vanish when the shuffle length
exceeds the crossing-filtration degree.
-/

namespace Categorification.TypeA
open Equiv

variable {n r m : ℕ} (h : n + r = m) (u : Shuffle h)

private theorem sadj_preserves_lt {j : ℕ} (hj : j + 1 < m) {a b : Fin m}
    (hab : a < b) (hne : ¬ (a.val = j ∧ b.val = j+1)) :
    sadj m j a < sadj m j b := by
  change a.val < b.val at hab
  rw [Fin.lt_def, sadj_val_of_lt hj, sadj_val_of_lt hj]
  simp only [swapNat]
  split_ifs <;> omega

/-- Swapping adjacent letters from the first and second input blocks extends the shuffle. -/
theorem shuffle_right_ascent {j : ℕ} (hj : j + 1 < m) {x : Fin n} {y : Fin r}
    (hl : u.1 ⟨j, by omega⟩ = blockEquiv h (.inl x))
    (hr : u.1 ⟨j+1, hj⟩ = blockEquiv h (.inr y)) :
    IsShuffle h (u.1 * sadj m j) ∧ length m (u.1 * sadj m j) = length m u.1 + 1 := by
  refine ⟨?_, length_mul_sadj_of_lt hj (by rw [hl, hr]; exact blockEquiv_inl_lt_inr h x y)⟩
  constructor
  · intro a b hab
    simp only [mul_inv_rev, sadj_inv, Perm.mul_apply]
    apply sadj_preserves_lt hj (u.2.1 hab)
    rintro ⟨_, hpos⟩
    have he : u.1⁻¹ (blockEquiv h (.inl b)) = ⟨j+1,hj⟩ := Fin.ext hpos
    have hh := congrArg u.1 he
    rw [show ∀ v, u.1 (u.1⁻¹ v) = v from u.1.apply_symm_apply, hr] at hh
    cases (blockEquiv h).injective hh
  · intro a b hab
    simp only [mul_inv_rev, sadj_inv, Perm.mul_apply]
    apply sadj_preserves_lt hj (u.2.2 hab)
    rintro ⟨hpos, _⟩
    have he : u.1⁻¹ (blockEquiv h (.inr a)) = ⟨j,by omega⟩ := Fin.ext hpos
    have hh := congrArg u.1 he
    rw [show ∀ v, u.1 (u.1⁻¹ v) = v from u.1.apply_symm_apply, hl] at hh
    cases (blockEquiv h).injective hh

private theorem consecutive_of_consecutive_images {d m : ℕ} {g : Fin d → Fin m}
    (hg : StrictMono g) {a b : Fin d} (hpos : (g a).val + 1 = (g b).val) :
    a.val + 1 = b.val := by
  have hab : a < b := hg.lt_iff_lt.mp (show g a < g b from by rw [Fin.lt_def]; omega)
  by_contra hne
  let c : Fin d := ⟨a.val+1,by have := b.isLt; have := hab; change a.val < b.val at hab; omega⟩
  have hac : a < c := by change a.val < a.val + 1; omega
  have hcb : c < b := by change a.val + 1 < b.val; change a.val < b.val at hab; omega
  have h₁ := hg hac
  have h₂ := hg hcb
  change (g a).val < (g c).val at h₁
  change (g c).val < (g b).val at h₂
  omega

/-- Two adjacent positions of a shuffle from the same left block are adjacent in that block. -/
theorem shuffle_mul_sadj_left {j : ℕ} (hj : j + 1 < m) {x y : Fin n}
    (hx : u.1 ⟨j, by omega⟩ = blockEquiv h (.inl x))
    (hy : u.1 ⟨j+1, hj⟩ = blockEquiv h (.inl y)) :
    x.val + 1 = y.val ∧ u.1 * sadj m j = blockPerm h (sadj n x.val) 1 * u.1 := by
  have h₁ : u.1⁻¹ (blockEquiv h (.inl x)) = ⟨j,by omega⟩ :=
    u.1.symm_apply_eq.mpr hx.symm
  have h₂ : u.1⁻¹ (blockEquiv h (.inl y)) = ⟨j+1,hj⟩ :=
    u.1.symm_apply_eq.mpr hy.symm
  have adj : x.val + 1 = y.val := consecutive_of_consecutive_images u.2.1 (by rw [h₁,h₂])
  have hn : x.val+1 < n := adj ▸ y.isLt
  have hm : x.val+1 < m := by omega
  refine ⟨adj,?_⟩
  rw [sadj, dite_eq_left hj, Equiv.mul_swap_eq_swap_mul, hx, hy, ← sadj_eq_blockPerm_left h hn,
    sadj, dite_eq_left hm]
  congr 2
  apply Fin.ext
  exact (blockEquiv_inl_val h y).trans adj.symm

/-- Two adjacent positions of a shuffle from the same right block are adjacent in that block. -/
theorem shuffle_mul_sadj_right {j : ℕ} (hj : j + 1 < m) {x y : Fin r}
    (hx : u.1 ⟨j, by omega⟩ = blockEquiv h (.inr x))
    (hy : u.1 ⟨j+1, hj⟩ = blockEquiv h (.inr y)) :
    x.val + 1 = y.val ∧ u.1 * sadj m j = blockPerm h 1 (sadj r x.val) * u.1 := by
  have h₁ : u.1⁻¹ (blockEquiv h (.inr x)) = ⟨j,by omega⟩ :=
    u.1.symm_apply_eq.mpr hx.symm
  have h₂ : u.1⁻¹ (blockEquiv h (.inr y)) = ⟨j+1,hj⟩ :=
    u.1.symm_apply_eq.mpr hy.symm
  have adj : x.val + 1 = y.val := consecutive_of_consecutive_images u.2.2 (by rw [h₁,h₂])
  have hn : x.val+1 < r := adj ▸ y.isLt
  have hm : n+x.val+1 < m := by omega
  refine ⟨adj,?_⟩
  rw [sadj, dite_eq_left hj, Equiv.mul_swap_eq_swap_mul, hx, hy, ← sadj_eq_blockPerm_right h hn,
    sadj, dite_eq_left hm]
  congr 2
  apply Fin.ext
  rw [blockEquiv_inr_val]
  change n + y.val = n + x.val + 1
  omega

end Categorification.TypeA

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open TypeA Equiv

variable {I k : Type*} [DecidableEq I] [CommRing k]
    {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}
local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

omit [DecidableEq I] in
private theorem rightCrossing_reduced {u : Perm (Fin m)} {j : ℕ} (hj : j + 1 < m)
    (hlen : length m (u * sadj m j) = length m u + 1) :
    IsReduced m (canWord m u ++ [j]) := by
  refine ⟨validWord_append.2 ⟨validWord_canWord m u, ?_⟩, ?_⟩
  · intro z hz
    rcases List.mem_singleton.1 hz with rfl
    exact hj
  · rw [List.length_append, length_canWord, List.length_singleton,
      wordProd_append, wordProd_canWord, wordProd_singleton, hlen]

private theorem rightCrossing_error {u : Perm (Fin m)} {j : ℕ} (hj : j + 1 < m)
    (hlen : length m (u * sadj m j) = length m u + 1) {w : List ℕ}
    (hw : IsReduced m w) (he : wordProd m w = u * sadj m j) (s : Seq ν) :
    (ψw (canWord m u) * ψ j * e s - ψw w * e s : A) ∈ filt k Q ν (length m u - 2) := by
  have hρ := rightCrossing_reduced hj hlen
  have hprod : wordProd m (canWord m u ++ [j]) = wordProd m w := by
    rw [wordProd_append, wordProd_canWord, wordProd_singleton, he]
  have hs : (e s : A) ∈ filt k Q ν 0 := by
    simpa only [map_one, one_mul] using (pol_mul_e_mem (Q := Q) 1 s 0)
  have error := sub_mem_of_braidEquiv_drop_three (braidEquiv_of_isReduced hρ hw hprod) hs
  have hdegree : (canWord m u ++ [j]).length - 3 + 0 = length m u - 2 := by
    rw [List.length_append, length_canWord, List.length_singleton]
    omega
  simpa only [hdegree, ψw_append, ψw_cons, ψw_nil, mul_one] using error

/-- On an external ascent, the crossing extends the shuffle word. Its error has
crossing length at least two less than the incoming shuffle. -/
theorem shuffle_right_ascent_crossing {n r : ℕ} (h : n + r = m) (u : Shuffle h)
    {j : ℕ} (hj : j + 1 < m) {x : Fin n} {y : Fin r}
    (hl : u.1 ⟨j, by omega⟩ = blockEquiv h (.inl x))
    (hr : u.1 ⟨j+1, hj⟩ = blockEquiv h (.inr y)) (s : Seq ν) :
    IsShuffle h (u.1 * sadj m j) ∧
      (ψw (canWord m u.1) * ψ j * e s - ψw (canWord m (u.1 * sadj m j)) * e s : A) ∈
        filt k Q ν (length m u.1 - 2) := by
  obtain ⟨hu, hlen⟩ := shuffle_right_ascent h u hj hl hr
  exact ⟨hu, rightCrossing_error hj hlen (isReduced_canWord _ _) (wordProd_canWord _ _) s⟩

private theorem shuffle_internal_crossing {j a : ℕ} {u : Perm (Fin m)}
    (hj : j + 1 < m) (ha : a + 1 < m) (he : u * sadj m j = sadj m a * u)
    (hlen : length m (u * sadj m j) = length m u + 1) (s : Seq ν) :
    (ψw (canWord m u) * ψ j * e s - ψ a * ψw (canWord m u) * e s : A) ∈
      filt k Q ν (length m u - 2) := by
  have hword : wordProd m (a :: canWord m u) = u * sadj m j := by
    rw [wordProd_cons, wordProd_canWord, he]
  have hr : IsReduced m (a :: canWord m u) := by
    refine ⟨?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hh
      · exact ha
      · exact validWord_canWord m u _ hh
    · rw [hword, hlen, List.length_cons, length_canWord]
  simpa only [ψw_cons] using rightCrossing_error hj hlen hr hword s

/-- The right crossing on two strands of the left block becomes that block's crossing. -/
theorem shuffle_right_crossing_inside_left {n r : ℕ} (h : n + r = m) (u : Shuffle h)
    {j : ℕ} (hj : j + 1 < m) {x y : Fin n}
    (hx : u.1 ⟨j, by omega⟩ = blockEquiv h (.inl x))
    (hy : u.1 ⟨j+1, hj⟩ = blockEquiv h (.inl y)) (s : Seq ν) :
    (ψw (canWord m u.1) * ψ j * e s - ψ x.val * ψw (canWord m u.1) * e s : A) ∈
      filt k Q ν (length m u.1 - 2) := by
  obtain ⟨adj, he⟩ := shuffle_mul_sadj_left h u hj hx hy
  have hx' : x.val + 1 < n := adj ▸ y.isLt
  have hlen : length m (u.1 * sadj m j) = length m u.1 + 1 := by
    rw [he, length_blockPerm_mul h _ _ u.2, length_sadj hx', length_one, add_zero, add_comm]
  exact shuffle_internal_crossing hj (by omega)
    (he.trans (congrArg (· * u.1) (sadj_eq_blockPerm_left h hx').symm)) hlen s

/-- The right crossing on two strands of the right block becomes that block's crossing. -/
theorem shuffle_right_crossing_inside_right {n r : ℕ} (h : n + r = m) (u : Shuffle h)
    {j : ℕ} (hj : j + 1 < m) {x y : Fin r}
    (hx : u.1 ⟨j, by omega⟩ = blockEquiv h (.inr x))
    (hy : u.1 ⟨j+1, hj⟩ = blockEquiv h (.inr y)) (s : Seq ν) :
    (ψw (canWord m u.1) * ψ j * e s - ψ (n + x.val) * ψw (canWord m u.1) * e s : A) ∈
      filt k Q ν (length m u.1 - 2) := by
  obtain ⟨adj, he⟩ := shuffle_mul_sadj_right h u hj hx hy
  have hx' : x.val + 1 < r := adj ▸ y.isLt
  have hlen : length m (u.1 * sadj m j) = length m u.1 + 1 := by
    rw [he, length_blockPerm_mul h _ _ u.2, length_sadj hx', length_one, zero_add, add_comm]
  exact shuffle_internal_crossing hj (by omega)
    (he.trans (congrArg (· * u.1) (sadj_eq_blockPerm_right h hx').symm)) hlen s

end Categorification.KLR.KLRAlgebra

namespace Categorification.KLR.KLRAlgebra

open Equiv MvPolynomial TypeA

variable {I k : Type*} [DecidableEq I] [CommRing k]
variable {Q : I → I → MvPolynomial (Fin 2) k} {μ : Multiset I}

local notation "m" => Multiset.card μ

private theorem hflip_mem_filt {a : KLRAlgebra k Q μ} {n : ℕ}
    (ha : a ∈ filt k Q μ n) : hflip a ∈ filt k Q μ n := by
  rw [filt_eq_span (fun _ _ => braidEquiv_of_isReduced) (fun _ => exists_braidEquiv_hasRepeat_of_not_isReduced)
    (canWord m) (fun w => ⟨isReduced_canWord _ w, wordProd_canWord _ w⟩) n] at ha
  change hflipEquiv k Q μ a ∈ filt k Q μ n
  apply Submodule.span_induction (p := fun x _ => hflipEquiv k Q μ x ∈ filt k Q μ n)
    _ _ _ _ ha
  · rintro _ ⟨w, d, s, hw, rfl⟩
    simp only [hflipEquiv_apply, hflip_mul, hflip_e, hflip_pol, hflip_ψw]
    apply e_mul_mem
    apply pol_mul_mem
    have h := ψw_mul_mem (k := k) (Q := Q) (canWord m w).reverse
      (n := 0) (one_mem_filt (k := k) (Q := Q) (ν := μ) 0)
    rw [mul_one, Nat.add_zero, List.length_reverse, length_canWord] at h
    exact filt_mono hw h
  · simp
  · intro x y _ _ hx hy
    simpa only [map_add] using add_mem hx hy
  · intro c x _ hx
    simpa only [map_smul] using Submodule.smul_mem _ c hx

theorem mem_span_topPBW_of_mem_filt
    (ρ : Perm (Fin m) → List ℕ)
    (hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w)
    {a : KLRAlgebra k Q μ} {n : ℕ} (ha : a ∈ filt k Q μ n) :
    a ∈ Submodule.span k {r : KLRAlgebra k Q μ | ∃ (w : Perm (Fin m))
      (d : Fin m →₀ ℕ) (s : Seq μ),
      length m w ≤ n ∧ pol (monomial d 1) * ψw (ρ w) * e s = r} := by
  have hb := hflip_mem_filt ha
  rw [filt_eq_span (fun _ _ => braidEquiv_of_isReduced) (fun _ => exists_braidEquiv_hasRepeat_of_not_isReduced)
    (revWord ρ) (revWord_spec ρ hρ) n] at hb
  rw [← hflip_hflip a]
  change hflipEquiv k Q μ (hflip a) ∈ _
  apply Submodule.span_induction (p := fun x _ => hflipEquiv k Q μ x ∈ _) _ _ _ _ hb
  · rintro _ ⟨w, d, s, hw, rfl⟩
    apply Submodule.subset_span
    refine ⟨w⁻¹, d, w • s, by rwa [length_inv], ?_⟩
    simp only [hflipEquiv_apply, hflip_mul, hflip_e, hflip_pol, hflip_ψw, revWord,
      List.reverse_reverse]
    rw [← mul_assoc, (e_commute_pol _ _).eq, mul_assoc (pol _) (e _) (ψw _), e_mul_ψw, (hρ w⁻¹).2,
      inv_inv, mul_assoc]
  · simp
  · intro x y _ _ hx hy
    simpa only [map_add] using add_mem hx hy
  · intro c x _ hx
    simpa only [map_smul] using Submodule.smul_mem _ c hx

section Binary

open scoped TensorProduct

variable {ν ν' : Multiset I} (hsym : KLRSymm Q)
  (ρ₁ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (ρ₂ : Perm (Fin (Multiset.card ν')) → List ℕ)
  (σ : Shuffle (Seq.card_add' ν ν') → List ℕ)
  (hρ₁ : ∀ w, IsReduced _ (ρ₁ w) ∧ wordProd _ (ρ₁ w) = w)
  (hρ₂ : ∀ w, IsReduced _ (ρ₂ w) ∧ wordProd _ (ρ₂ w) = w)
  (hσ : ∀ u, IsReduced _ (σ u) ∧ wordProd _ (σ u) = u.1)

include hsym hρ₁ hρ₂ hσ in
/-- A filtered element can have nonzero coordinates only at shuffles of at most its
crossing filtration degree. -/
theorem freeBasis_coord_eq_zero_of_mem_filt
    {a : oneConcatSub (ν := ν) (ν' := ν') (k := k) Q} {n : ℕ}
    (ha : a.val ∈ filt k Q (ν + ν') n)
    (v : Shuffle (Seq.card_add' ν ν')) (hv : n < length _ v.1) :
    (freeBasis hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ).coord v a = 0 := by
  let B := freeBasis hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ
  let P : KLRAlgebra k Q (ν + ν') →ₗ[k] oneConcatSub (ν := ν) (ν' := ν') Q :=
    (LinearMap.mulLeft k (oneConcat Q ν ν')).rangeRestrict
  have hPa : P a.val = a := Subtype.ext (mem_oneConcatSub.1 a.property)
  rw [← hPa]
  change ((B.coord v).restrictScalars k ∘ₗ P) a.val = 0
  have hab := mem_span_topPBW_of_mem_filt (parWord ρ₁ ρ₂ σ)
    (parWord_spec ρ₁ ρ₂ σ hρ₁ hρ₂ hσ) ha
  apply (Submodule.span_le.2 ?_ hab : a.val ∈ LinearMap.ker ((B.coord v).restrictScalars k ∘ₗ P))
  rintro _ ⟨w, d, s, hw, rfl⟩
  change B.coord v (P (pol (monomial d 1) * ψw (parWord ρ₁ ρ₂ σ w) * e s)) = 0
  by_cases hs : w • s ∈ concatSet ν ν'
  · obtain ⟨x, hx⟩ := exists_indIdxMap (f := d) hs
    have hxw : blockPerm (Seq.card_add' ν ν') x.1.1.2.1 x.1.2.2.1 * x.2.1 = w :=
      congrArg (fun b : Idx (ν + ν') => b.2.1) hx
    have hlu := length_blockPerm_mul (Seq.card_add' ν ν') x.1.1.2.1 x.1.2.2.1 x.2.2
    rw [hxw] at hlu
    have hne : x.2 ≠ v := by
      intro hxv
      rw [hxv] at hlu
      omega
    have hP : P (pol (monomial d 1) * ψw (parWord ρ₁ ρ₂ σ w) * e s) =
        (lbasis hsym ρ₁ hρ₁ x.1.1 ⊗ₜ[k] lbasis hsym ρ₂ hρ₂ x.1.2) • B x.2 := by
      apply Subtype.ext
      change oneConcat Q ν ν' * _ = _
      rw [oneConcat_mul_pol_ψw_e, (parWord_spec ρ₁ ρ₂ σ hρ₁ hρ₂ hσ w).2, ite_eq_left hs,
        coe_tensor_smul, freeBasis_apply]
      rw [← indElt, indElt_eq hsym ρ₁ ρ₂ σ hρ₁ hρ₂ hσ, hx, lbasis_apply]
    rw [hP, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne hne.symm, smul_zero]
  · have hP : P (pol (monomial d 1) * ψw (parWord ρ₁ ρ₂ σ w) * e s) = 0 := by
      apply Subtype.ext
      change oneConcat Q ν ν' * _ = 0
      rw [oneConcat_mul_pol_ψw_e, (parWord_spec ρ₁ ρ₂ σ hρ₁ hρ₂ hσ w).2, ite_eq_right hs]
    rw [hP, map_zero]

end Binary

end Categorification.KLR.KLRAlgebra
