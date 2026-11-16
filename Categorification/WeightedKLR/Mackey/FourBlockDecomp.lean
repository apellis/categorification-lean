/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.FourBlockBalanced

/-!
# The shuffle element of the middle parabolic, chamber by chamber

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19. For the shuffle type `c` of the layouts `a b c d` and
`a c b d`, the four-block chambers are exactly the chambers `(A B)(C D)` with rank-ordered
`A, B, C, D`, and the shuffle element `ψ_c` of this type is the sum of the four-block shuffles of
these chambers; the four-block shuffle of `(A B)(C D)` runs from `(A B)(C D)` to `(A C)(B D)`.

## Main results

* `FullChamber.IsFourBlock.isSeparated_and`, `FullChamber.IsFourBlock.isSeparated_or`: a
  four-block chamber for `X` and `Z` is separated by `X ∧ Z` and by `X ∨ Z`.
* `Juxtapose.exists_eq_fourChamber_of_isFourBlock`: every four-block chamber for the middle
  parabolic is a chamber `(A B)(C D)` with rank-ordered `A, B, C, D`.
* `Juxtapose.typeShuffle_middleLeft`: `ψ_c` is the sum of the four-block shuffles of the chambers
  `(A B)(C D)`.
* `Juxtapose.typeShuffle_mul_e_fourChamber`, `Juxtapose.e_fourChamberSwap_mul_typeShuffle`:
  cutting `ψ_c` down at `(A B)(C D)` on the right, or at `(A C)(B D)` on the left, gives the
  four-block shuffle of `(A B)(C D)`.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace FullChamber

variable {ν : I →₀ ℕ}

omit [DecidableEq I] in
/-- A four-block chamber for `X` and `Z` is separated by `X ∧ Z`. -/
theorem IsFourBlock.isSeparated_and {X Z : Strand ν → Bool} {B : FullChamber Γ ν}
    (hB : IsFourBlock X Z B) : IsSeparated (fun t => X t && Z t) B := by
  intro h hh
  have e := congrArg (fun C : FullChamber Γ ν => C.1 h) hB.2
  simp only [shuffleBot_apply, shuffleTop_apply] at e
  beta_reduce at hh ⊢
  rw [← e]
  revert hh
  generalize X h.lo = x₁
  generalize X h.hi = x₂
  generalize Z h.lo = z₁
  generalize Z h.hi = z₂
  generalize B.1 h = c
  revert x₁ x₂ z₁ z₂ c
  decide

omit [DecidableEq I] in
/-- A four-block chamber for `X` and `Z` is separated by `X ∨ Z`. -/
theorem IsFourBlock.isSeparated_or {X Z : Strand ν → Bool} {B : FullChamber Γ ν}
    (hB : IsFourBlock X Z B) : IsSeparated (fun t => X t || Z t) B := by
  intro h hh
  have e := congrArg (fun C : FullChamber Γ ν => C.1 h) hB.2
  simp only [shuffleBot_apply, shuffleTop_apply] at e
  beta_reduce at hh ⊢
  rw [← e]
  revert hh
  generalize X h.lo = x₁
  generalize X h.hi = x₂
  generalize Z h.lo = z₁
  generalize Z h.hi = z₂
  generalize B.1 h = c
  revert x₁ x₂ z₁ z₂ c
  decide

end FullChamber

namespace Juxtapose

variable {a b c d : I →₀ ℕ}

omit [DecidableEq I] in
/-- On the strands of `a + b`, the strands of `a + b` in `middleLeft` are those of `a`. -/
theorem isLeft_and_middleLeft_inlStrand (s : Strand (a + b)) :
    (decide ((inlStrand (a + b) (c + d) s).IsLeft (a + b)) &&
      middleLeft a b c d (inlStrand (a + b) (c + d) s)) = decide (s.IsLeft a) := by
  obtain ⟨x | x, rfl⟩ := (strandEquiv a b).surjective s
  · show (decide _ && middleLeft a b c d (inlStrand _ _ (inlStrand a b x))) = _
    rw [middleLeft_inl_inl]
    simp [isLeft_inlStrand]
  · show (decide _ && middleLeft a b c d (inlStrand _ _ (inrStrand a b x))) = _
    rw [middleLeft_inl_inr]
    simp [not_isLeft_inrStrand]

omit [DecidableEq I] in
/-- On the strands of `c + d`, the strands of `a + b` or `middleLeft` are those of `c`. -/
theorem isLeft_or_middleLeft_inrStrand (s : Strand (c + d)) :
    (decide ((inrStrand (a + b) (c + d) s).IsLeft (a + b)) ||
      middleLeft a b c d (inrStrand (a + b) (c + d) s)) = decide (s.IsLeft c) := by
  obtain ⟨x | x, rfl⟩ := (strandEquiv c d).surjective s
  · show (decide _ || middleLeft a b c d (inrStrand _ _ (inlStrand c d x))) = _
    rw [middleLeft_inr_inl]
    simp [isLeft_inlStrand]
  · show (decide _ || middleLeft a b c d (inrStrand _ _ (inrStrand c d x))) = _
    rw [middleLeft_inr_inr]
    simp [not_isLeft_inrStrand]

omit [DecidableEq I] in
/-- **The four-block chambers of the middle parabolic.** A four-block chamber for the strands of
`a + b` and `middleLeft a b c d` is a chamber `(A B)(C D)`, necessarily with rank-ordered
`A, B, C, D`. -/
theorem exists_eq_fourChamber_of_isFourBlock {E : FullChamber Γ (a + b + (c + d))}
    (hE : IsFourBlock (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d) E) :
    ∃ q, (fourChamber a b c d q).IsRankOrdered ∧ E = fourChamber a b c d q := by
  have h₀ : E = chamber ((leftEmb (a + b) (c + d)).restrict E)
      ((rightEmb (a + b) (c + d)).restrict E) :=
    eq_chamber_of_isSeparated hE.isSeparated
  have h₁ := eq_chamber_of_isSeparated (ν' := a) (ν'' := b)
    (StrandEmbedding.isSeparated_restrict (j := leftEmb (a + b) (c + d)) hE.isSeparated_and
      isLeft_and_middleLeft_inlStrand)
  have h₂ := eq_chamber_of_isSeparated (ν' := c) (ν'' := d)
    (StrandEmbedding.isSeparated_restrict (j := rightEmb (a + b) (c + d)) hE.isSeparated_or
      isLeft_or_middleLeft_inrStrand)
  rw [h₁, h₂] at h₀
  refine ⟨(_, _, _, _), ?_, h₀⟩
  have hr := hE.1
  rw [h₀] at hr
  exact hr

end Juxtapose

namespace GalleryAlgebra

variable {ν : I →₀ ℕ}

/-- The four-block shuffle of `B` starts at `B` and ends at the rank-ordered relabelling
`ρ • shuffleTop Z B`, for any `ρ` making it rank-ordered. -/
theorem e_mul_fourShuffle (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (Z : Strand ν → Bool)
    (B : FullChamber Γ ν) {ρ : ColPerm ν} (hρ : (ρ • shuffleTop Z B).IsRankOrdered)
    (E : FullChamber Γ ν) :
    e E * fourShuffle k hD hZ Z B =
      if E = ρ • shuffleTop Z B then fourShuffle k hD hZ Z B else 0 := by
  obtain ⟨hw, hfw⟩ := (exists_goodWord hD hZ B (shuffleTop Z B)).choose_spec
  rw [fourShuffle_eq hD hZ Z B hρ hw hfw, ← mul_assoc, e_mul_r]
  split_ifs <;> simp

end GalleryAlgebra

namespace Juxtapose

variable {a b c d : I →₀ ℕ}

omit [DecidableEq I] in
theorem isRankOrdered_fourChamber_iff
    (q : FullChamber Γ a × FullChamber Γ b × FullChamber Γ c × FullChamber Γ d) :
    (fourChamber a b c d q).IsRankOrdered ↔ q.1.IsRankOrdered ∧ q.2.1.IsRankOrdered ∧
      q.2.2.1.IsRankOrdered ∧ q.2.2.2.IsRankOrdered := by
  simp only [fourChamber, isRankOrdered_chamber_iff, and_assoc]

omit [DecidableEq I] in
theorem isFourBlock_fourChamber_of_isRankOrdered
    {q : FullChamber Γ a × FullChamber Γ b × FullChamber Γ c × FullChamber Γ d}
    (hq : (fourChamber a b c d q).IsRankOrdered) :
    IsFourBlock (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d)
      (fourChamber a b c d q) := by
  obtain ⟨hA, hB, hC, hD⟩ := (isRankOrdered_fourChamber_iff q).1 hq
  exact isFourBlock_fourChamber hA hB hC hD

variable (k) in
/-- **The shuffle element of the middle parabolic, chamber by chamber.** The shuffle element of
the type `c` of the layouts `a b c d` and `a c b d` is the sum of the four-block shuffles of the
chambers `(A B)(C D)` with rank-ordered `A, B, C, D` (Webster, arXiv:1209.2463v4,
Theorem 2.19). -/
theorem typeShuffle_middleLeft (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) :
    typeShuffle k hD hZ (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d) =
      ∑ q ∈ Finset.univ.filter fun q => (fourChamber (Γ := Γ) a b c d q).IsRankOrdered,
        fourShuffle k hD hZ (middleLeft a b c d) (fourChamber a b c d q) := by
  classical
  rw [typeShuffle, ← Finset.sum_image fun q _ q' _ h => fourChamber_injective h]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext E
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hE
    obtain ⟨q, hq, rfl⟩ := exists_eq_fourChamber_of_isFourBlock hE
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact isFourBlock_fourChamber_of_isRankOrdered hq

/-- The four-block shuffle of `(A B)(C D)` ends at `(A C)(B D)`. -/
theorem e_mul_fourShuffle_fourChamber (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    {q : FullChamber Γ a × FullChamber Γ b × FullChamber Γ c × FullChamber Γ d}
    (hq : (fourChamber a b c d q).IsRankOrdered) (E : FullChamber Γ (a + b + (c + d))) :
    e E * fourShuffle k hD hZ (middleLeft a b c d) (fourChamber a b c d q) =
      if E = fourChamberSwap a b c d q then
        fourShuffle k hD hZ (middleLeft a b c d) (fourChamber a b c d q) else 0 := by
  obtain ⟨A, B, C, D⟩ := q
  have h := middleSwap_smul_shuffleTop a b c d A B C D
  have hρ : (middleSwap a b c d • shuffleTop (middleLeft a b c d)
      (fourChamber a b c d (A, B, C, D))).IsRankOrdered := by
    rw [fourChamber, h]
    exact (isRankOrdered_fourChamberSwap_iff (A, B, C, D)).2 hq
  rw [e_mul_fourShuffle hD hZ _ _ hρ, fourChamber, h]
  rfl

/-- Cutting the shuffle element of the middle parabolic down at `(A B)(C D)` on the right gives
the four-block shuffle of `(A B)(C D)`. -/
theorem typeShuffle_mul_e_fourChamber (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    {q : FullChamber Γ a × FullChamber Γ b × FullChamber Γ c × FullChamber Γ d}
    (hq : (fourChamber a b c d q).IsRankOrdered) :
    typeShuffle k hD hZ (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d) *
        e (fourChamber a b c d q) =
      fourShuffle k hD hZ (middleLeft a b c d) (fourChamber a b c d q) :=
  typeShuffle_mul_e hD hZ (isFourBlock_fourChamber_of_isRankOrdered hq)

/-- Cutting the shuffle element of the middle parabolic down at `(A C)(B D)` on the left gives
the four-block shuffle of `(A B)(C D)`. -/
theorem e_fourChamberSwap_mul_typeShuffle (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    {q : FullChamber Γ a × FullChamber Γ b × FullChamber Γ c × FullChamber Γ d}
    (hq : (fourChamber a b c d q).IsRankOrdered) :
    e (fourChamberSwap a b c d q) *
        typeShuffle k hD hZ (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d) =
      fourShuffle k hD hZ (middleLeft a b c d) (fourChamber a b c d q) := by
  classical
  rw [typeShuffle_middleLeft, Finset.mul_sum,
    Finset.sum_eq_single_of_mem q (Finset.mem_filter.2 ⟨Finset.mem_univ _, hq⟩)
      fun q' hq' hne => ?_, e_mul_fourShuffle_fourChamber hD hZ hq, ite_eq_left rfl]
  rw [e_mul_fourShuffle_fourChamber hD hZ (Finset.mem_filter.1 hq').2,
    ite_eq_right fun h => hne (fourChamberSwap_injective h).symm]

end Juxtapose

end Categorification.WeightedKLR
