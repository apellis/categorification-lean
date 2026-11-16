/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.Intermediate
import Categorification.WeightedKLR.Mackey.Separated

/-!
# Minimal galleries through the shuffle

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). A basis element of type `μ` is factored through the
diagram exchanging two blocks of strands. On the level of chambers: let `X` be a set of strands
separating the chamber `C` at the bottom and `Y` a set of strands separating the chamber `E` at
the top. With `G = sep Y C C` (the strands of `Y` moved to the left, keeping their relative
position from `C`) and `F = sep X G G`, any minimal galleries `C → F`, `F → G` and `G → E`
concatenate to a minimal gallery `C → E` (`FullChamber.goodWord_shuffle`). The first crosses
only hyperplanes inside `X` or inside its complement, the last only hyperplanes inside `Y` or
inside its complement, and the middle one only hyperplanes joining a strand of `X` with a
strand outside `X` and a strand of `Y` with a strand outside `Y`, in the opposite order: it is
the shuffle.

## Main definitions

* `FullChamber.shuffleTop Y C`: the chamber `sep Y C C`.
* `FullChamber.shuffleBot X Y C`: the chamber `sep X (sep Y C C) (sep Y C C)`.

## Main results

* `FullChamber.goodWord_shuffle`: concatenation of minimal galleries through these chambers.
* `FullChamber.exists_goodWord_shuffle`: such a factorization of a minimal gallery exists.
* `FullChamber.mem_bot_shuffle`, `FullChamber.mem_mid_shuffle`, `FullChamber.mem_top_shuffle`:
  the hyperplanes crossed by the three pieces.
-/

namespace Categorification.WeightedKLR

namespace FullChamber

variable {I : Type*} {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-- The chamber `C` with the strands of `Y` moved to the left. -/
noncomputable def shuffleTop (Y : Strand ν → Bool) (C : FullChamber Γ ν) : FullChamber Γ ν :=
  sep Y C C

/-- The chamber `shuffleTop Y C` with the strands of `X` moved to the left. -/
noncomputable def shuffleBot (X Y : Strand ν → Bool) (C : FullChamber Γ ν) :
    FullChamber Γ ν :=
  sep X (shuffleTop Y C) (shuffleTop Y C)

variable {X Y : Strand ν → Bool} {C E : FullChamber Γ ν}

theorem shuffleTop_apply (Y : Strand ν → Bool) (C : FullChamber Γ ν) (x : Hyp Γ ν) :
    (shuffleTop Y C).1 x = if Y x.lo = Y x.hi then C.1 x else Y x.lo := by
  rw [shuffleTop, sep_apply]
  by_cases h : Y x.lo = Y x.hi
  · simp only [h, ↓reduceIte, ite_self]
  · simp only [h, ↓reduceIte]

theorem shuffleBot_apply (X Y : Strand ν → Bool) (C : FullChamber Γ ν) (x : Hyp Γ ν) :
    (shuffleBot X Y C).1 x = if X x.lo = X x.hi then (shuffleTop Y C).1 x else X x.lo := by
  rw [shuffleBot, sep_apply]
  by_cases h : X x.lo = X x.hi
  · simp only [h, ↓reduceIte, ite_self]
  · simp only [h, ↓reduceIte]

/-- `shuffleBot X Y C` lies between `C` and `shuffleTop Y C`. -/
theorem shuffleBot_between (hC : IsSeparated X C) (x : Hyp Γ ν)
    (hx : C.1 x = (shuffleTop Y C).1 x) : (shuffleBot X Y C).1 x = C.1 x := by
  rw [shuffleBot_apply]
  by_cases h : X x.lo = X x.hi
  · rw [ite_eq_left h, ← hx]
  · rw [ite_eq_right h, hC x h]

/-- `shuffleTop Y C` lies between `C` and `E`. -/
theorem shuffleTop_between (hE : IsSeparated Y E) (x : Hyp Γ ν) (hx : C.1 x = E.1 x) :
    (shuffleTop Y C).1 x = C.1 x := by
  rw [shuffleTop_apply]
  by_cases h : Y x.lo = Y x.hi
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, hx, hE x h]

variable [DecidableEq I]

/-- **Minimal galleries through the shuffle.** If `X` separates `C` and `Y` separates `E`, then
minimal galleries `a : C → shuffleBot X Y C`, `b : shuffleBot X Y C → shuffleTop Y C` and
`c : shuffleTop Y C → E` concatenate to a minimal gallery from `C` to `E`. -/
theorem goodWord_shuffle (hC : IsSeparated X C) (hE : IsSeparated Y E)
    {a b c : List (Hyp Γ ν)} (ha : GoodWord C.1 a) (hfa : C.flips a = shuffleBot X Y C)
    (hb : GoodWord (shuffleBot X Y C).1 b) (hfb : (shuffleBot X Y C).flips b = shuffleTop Y C)
    (hc : GoodWord (shuffleTop Y C).1 c) (hfc : (shuffleTop Y C).flips c = E) :
    GoodWord C.1 (a ++ b ++ c) ∧ C.flips (a ++ b ++ c) = E := by
  have hab : GoodWord C.1 (a ++ b) := by
    refine GoodWord.append_of_between ha (hfa ▸ hb) fun x hx => ?_
    rw [hfa, hfb] at hx
    rw [hfa]
    exact shuffleBot_between hC x hx
  have hfab : C.flips (a ++ b) = shuffleTop Y C := by rw [flips_append, hfa, hfb]
  refine ⟨GoodWord.append_of_between hab (hfab ▸ hc) fun x hx => ?_, ?_⟩
  · rw [hfab, hfc] at hx
    rw [hfab]
    exact shuffleTop_between hE x hx
  · rw [flips_append, hfab, hfc]

/-- A factorization of a minimal gallery from `C` to `E` through the shuffle exists. -/
theorem exists_goodWord_shuffle (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (X Y : Strand ν → Bool)
    (C E : FullChamber Γ ν) :
    ∃ a b c : List (Hyp Γ ν), GoodWord C.1 a ∧ C.flips a = shuffleBot X Y C ∧
      GoodWord (shuffleBot X Y C).1 b ∧ (shuffleBot X Y C).flips b = shuffleTop Y C ∧
      GoodWord (shuffleTop Y C).1 c ∧ (shuffleTop Y C).flips c = E := by
  obtain ⟨a, ha, hfa⟩ := exists_goodWord hD hZ C (shuffleBot X Y C)
  obtain ⟨b, hb, hfb⟩ := exists_goodWord hD hZ (shuffleBot X Y C) (shuffleTop Y C)
  obtain ⟨c, hc, hfc⟩ := exists_goodWord hD hZ (shuffleTop Y C) E
  exact ⟨a, b, c, ha, hfa, hb, hfb, hc, hfc⟩

/-- The bottom piece crosses only hyperplanes inside `X` or inside its complement, and only
hyperplanes between `Y` and its complement. -/
theorem mem_bot_shuffle (hC : IsSeparated X C) {a : List (Hyp Γ ν)} (ha : GoodWord C.1 a)
    (hfa : C.flips a = shuffleBot X Y C) {x : Hyp Γ ν} (hx : x ∈ a) :
    X x.lo = X x.hi ∧ Y x.lo ≠ Y x.hi := by
  have h := (ha.mem_iff x).1 hx
  rw [hfa, shuffleBot_apply] at h
  by_cases hX : X x.lo = X x.hi
  · rw [ite_eq_left hX, shuffleTop_apply] at h
    refine ⟨hX, fun hY => h ?_⟩
    rw [ite_eq_left hY]
  · rw [ite_eq_right hX, hC x hX] at h
    exact absurd rfl h

/-- The middle piece crosses only hyperplanes joining `X` to its complement and `Y` to its
complement, on which `X` and `Y` disagree about the first strand: it exchanges the strands of
`Y \ X` with those of `X \ Y`. -/
theorem mem_mid_shuffle (hC : IsSeparated X C) {b : List (Hyp Γ ν)}
    (hb : GoodWord (shuffleBot X Y C).1 b) (hfb : (shuffleBot X Y C).flips b = shuffleTop Y C)
    {x : Hyp Γ ν} (hx : x ∈ b) :
    X x.lo ≠ X x.hi ∧ Y x.lo ≠ Y x.hi ∧ Y x.lo ≠ X x.lo := by
  have h := (hb.mem_iff x).1 hx
  rw [hfb, shuffleBot_apply] at h
  by_cases hX : X x.lo = X x.hi
  · rw [ite_eq_left hX] at h
    exact absurd rfl h
  · rw [ite_eq_right hX, shuffleTop_apply] at h
    by_cases hY : Y x.lo = Y x.hi
    · rw [ite_eq_left hY, hC x hX] at h
      exact absurd rfl h
    · rw [ite_eq_right hY] at h
      exact ⟨hX, hY, h⟩

/-- The top piece crosses only hyperplanes inside `Y` or inside its complement. -/
theorem mem_top_shuffle (hE : IsSeparated Y E) {c : List (Hyp Γ ν)}
    (hc : GoodWord (shuffleTop Y C).1 c) (hfc : (shuffleTop Y C).flips c = E)
    {x : Hyp Γ ν} (hx : x ∈ c) : Y x.lo = Y x.hi := by
  have h := (hc.mem_iff x).1 hx
  rw [hfc, shuffleTop_apply] at h
  by_contra hY
  rw [ite_eq_right hY, hE x hY] at h
  exact h rfl

end FullChamber

end Categorification.WeightedKLR
