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

end Categorification.WeightedKLR
