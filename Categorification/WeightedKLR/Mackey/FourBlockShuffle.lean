/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.ShufflePattern
import Categorification.WeightedKLR.Mackey.ShuffleExact

/-!
# The shuffle element of a four-block chamber

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). Webster's generator of a subquotient of the filtration is
built from the shuffle of the middle two blocks of a four-block chamber: a rank-ordered chamber
`B` of `ν = ν' + ν''` whose two blocks are each split, by a set `Z` of strands, into two
sub-blocks. Moving the strands of `Z` to the left gives the chamber `shuffleTop Z B`; the
shuffle element `fourShuffle Z B` is the gallery product from `B` to it followed by the
relabelling of `shuffleTop Z B` into rank order.

Both choices involved are immaterial (`GalleryAlgebra.fourShuffle_eq`): the relabelling, since
a relabelling between rank-ordered chambers is the identity, and the gallery, since `B` and
`shuffleTop Z B` differ only on hyperplanes joining a strand of `Z` to a strand outside `Z`
(`GalleryAlgebra.galList_eq_of_crossing`).

The shuffle element `ψ^W_g` of a relabelling `g` (`GalleryAlgebra.rankShuffleElt`) is of this
form: for `C` separated by the strands of `ν'`, its bottom end `rankShuffleBot g C` is a
four-block chamber for the set `Z` of strands sent into the first block of `ν₁`
(transported along the block sort), and `ψ^W_g = fourShuffle Z (rankShuffleBot g C)`
(`GalleryAlgebra.rankShuffleElt_eq_fourShuffle`). So `ψ^W_g` depends on `(g, C)` only through
its bottom end and `Z`.

## Main definitions

* `FullChamber.IsFourBlock X Z B`: `B` is rank-ordered, separated by `X`, and separated by `Z`
  inside each of the two blocks of `X`.
* `GalleryAlgebra.fourShuffle Z B`: the shuffle element of the four-block chamber `B`.

## Main results

* `FullChamber.sep_smul`: relabelling commutes with separating a set of strands.
* `GalleryAlgebra.fourShuffle_eq`: the shuffle element along any minimal gallery and any
  relabelling into rank order.
* `GalleryAlgebra.rankShuffleElt_eq_fourShuffle`: `ψ^W_g` is a four-block shuffle element.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment Pointwise GalleryAlgebra Juxtapose

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace FullChamber

omit [DecidableEq I] in
/-- **Relabelling commutes with separation.** -/
theorem sep_smul (Y : Strand ν → Bool) (P Q : FullChamber Γ ν) (v : ColPerm ν) :
    v • sep Y P Q = sep (fun t => Y (v.1⁻¹ t)) (v • P) (v • Q) := by
  apply Subtype.ext
  funext x
  rw [smul_apply, sep_apply, sep_apply, smul_apply, smul_apply]
  have hl := Hyp.lo_comap v x
  have hh := Hyp.hi_comap v x
  cases hr : x.reverses v
  · rw [hr] at hl hh
    simp only [Bool.false_eq_true, ↓reduceIte] at hl hh ⊢
    rw [hl, hh]
  · rw [hr] at hl hh
    simp only [↓reduceIte] at hl hh ⊢
    rw [hl, hh]
    cases Y (v.1⁻¹ x.lo) <;> cases Y (v.1⁻¹ x.hi) <;> simp

omit [DecidableEq I] in
theorem shuffleTop_smul (Y : Strand ν → Bool) (C : FullChamber Γ ν) (v : ColPerm ν) :
    v • shuffleTop Y C = shuffleTop (fun t => Y (v.1⁻¹ t)) (v • C) :=
  sep_smul Y C C v

omit [DecidableEq I] in
theorem shuffleBot_smul (X Y : Strand ν → Bool) (C : FullChamber Γ ν) (v : ColPerm ν) :
    v • shuffleBot X Y C =
      shuffleBot (fun t => X (v.1⁻¹ t)) (fun t => Y (v.1⁻¹ t)) (v • C) := by
  rw [shuffleBot, sep_smul, shuffleTop_smul]
  rfl

omit [DecidableEq I] in
/-- For `C` separated by `X`, moving the strands of `Y` to the left in `shuffleBot X Y C` gives
`shuffleTop Y C`. -/
theorem shuffleTop_shuffleBot {X : Strand ν → Bool} (Y : Strand ν → Bool) {C : FullChamber Γ ν}
    (hC : IsSeparated X C) : shuffleTop Y (shuffleBot X Y C) = shuffleTop Y C := by
  apply Subtype.ext
  funext x
  rw [shuffleTop_apply, shuffleTop_apply, shuffleBot_apply, shuffleTop_apply]
  by_cases hY : Y x.lo = Y x.hi
  · rw [ite_eq_left hY, ite_eq_left hY]
    by_cases hX : X x.lo = X x.hi
    · rw [ite_eq_left hX]
    · rw [ite_eq_right hX, hC x hX]
  · rw [ite_eq_right hY, ite_eq_right hY]

omit [DecidableEq I] in
/-- For `C` separated by `X`, the relabelled top end `v • shuffleTop Y C` is obtained from the
relabelled bottom end `v • shuffleBot X Y C` by moving the strands of `Y ∘ v⁻¹` to the left. -/
theorem smul_shuffleTop_eq {X : Strand ν → Bool} (Y : Strand ν → Bool) {C : FullChamber Γ ν}
    (hC : IsSeparated X C) (v : ColPerm ν) :
    v • shuffleTop Y C = shuffleTop (fun t => Y (v.1⁻¹ t)) (v • shuffleBot X Y C) := by
  rw [shuffleBot_smul, shuffleTop_shuffleBot _ (hC.smul v), shuffleTop_smul]

/-- `B` is a **four-block chamber** for the sets of strands `X` and `Z`: it is rank-ordered, and
moving first the strands of `Z` and then those of `X` to the left does not change it, that is,
`B` is separated by `X` and, inside each of the two blocks of `X`, by `Z`. -/
def IsFourBlock (X Z : Strand ν → Bool) (B : FullChamber Γ ν) : Prop :=
  B.IsRankOrdered ∧ shuffleBot X Z B = B

omit [DecidableEq I] in
/-- `shuffleTop Z B` differs from `B` only on hyperplanes joining `Z` to its complement. -/
theorem isCrossing_of_shuffleTop_ne_self (Z : Strand ν → Bool) (B : FullChamber Γ ν)
    {h : Hyp Γ ν} (hne : (shuffleTop Z B).1 h ≠ B.1 h) : h.IsCrossing Z := by
  intro hZ
  rw [shuffleTop_apply, ite_eq_left hZ] at hne
  exact hne rfl

end FullChamber

namespace GalleryAlgebra

variable (k) in
/-- **The four-block shuffle element.** The gallery product along a fixed minimal gallery from
`B` to `shuffleTop Z B` (the strands of `Z` moved to the left), followed by a relabelling of
`shuffleTop Z B` into rank order. For a four-block chamber `B` this exchanges the two middle
sub-blocks. -/
noncomputable def fourShuffle (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (Z : Strand ν → Bool)
    (B : FullChamber Γ ν) : GalleryAlgebra k Γ ν :=
  r (exists_smul_isRankOrdered (shuffleTop Z B)).choose (shuffleTop Z B) *
    galList k B (exists_goodWord hD hZ B (shuffleTop Z B)).choose

/-- **The four-block shuffle element does not depend on the choices.** It is
`r ρ (shuffleTop Z B) * galList B w` for every relabelling `ρ` of `shuffleTop Z B` into rank
order and every minimal gallery `w` from `B` to `shuffleTop Z B`. -/
theorem fourShuffle_eq (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (Z : Strand ν → Bool)
    (B : FullChamber Γ ν) {ρ : ColPerm ν} (hρ : (ρ • shuffleTop Z B).IsRankOrdered)
    {w : List (Hyp Γ ν)} (hw : GoodWord B.1 w) (hfw : B.flips w = shuffleTop Z B) :
    fourShuffle k hD hZ Z B = r ρ (shuffleTop Z B) * galList k B w := by
  set T := shuffleTop Z B
  have hc := (exists_smul_isRankOrdered T).choose_spec
  have hg := (exists_goodWord hD hZ B T).choose_spec
  set c := (exists_smul_isRankOrdered T).choose
  have h1 : ρ * c⁻¹ = 1 := by
    refine eq_one_of_isRankOrdered_smul hc ?_
    rwa [smul_smul, inv_mul_cancel_right]
  have hρc : ρ = c := (mul_inv_eq_one.1 h1)
  rw [fourShuffle, hρc]
  congr 1
  refine galList_eq_of_crossing hD hZ Z hg.1 hw (hg.2.trans hfw.symm) fun h hh => ?_
  rw [hg.2] at hh
  exact isCrossing_of_shuffleTop_ne_self Z B hh

theorem fourShuffle_mul_e (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (Z : Strand ν → Bool)
    (B : FullChamber Γ ν) : fourShuffle k hD hZ Z B * e B = fourShuffle k hD hZ Z B := by
  rw [fourShuffle, mul_assoc, galList_mul_e]

theorem fourShuffle_mul_e_of_ne (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (Z : Strand ν → Bool)
    {B B' : FullChamber Γ ν} (hB : B ≠ B') : fourShuffle k hD hZ Z B * e B' = 0 := by
  rw [← fourShuffle_mul_e, mul_assoc, e_mul_e, ite_eq_right hB, mul_zero]

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

/-- `ψ^W_g` as the relabelling `u g v⁻¹` of the relabelled top end after the relabelled minimal
gallery between the relabelled ends. -/
theorem rankShuffleElt_eq_r_mul_galList (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (g : ColPerm ν) (C : FullChamber Γ ν) :
    ∃ w : List (Hyp Γ ν), GoodWord (rankShuffleBot hν' ν₁ g C).1 w ∧
      (rankShuffleBot hν' ν₁ g C).flips w =
        blockSort hν' (shuffleBot (fun t => decide (t.IsLeft ν'))
          (fun t => decide ((g.1 t).IsLeft ν₁)) C) •
          shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C ∧
      rankShuffleElt k hν' hν₁ hD hZ g C =
        r (blockSort hν₁ (g • shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) * g *
            (blockSort hν' (shuffleBot (fun t => decide (t.IsLeft ν'))
              (fun t => decide ((g.1 t).IsLeft ν₁)) C))⁻¹)
          (blockSort hν' (shuffleBot (fun t => decide (t.IsLeft ν'))
              (fun t => decide ((g.1 t).IsLeft ν₁)) C) •
            shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) *
          galList k (rankShuffleBot hν' ν₁ g C) w := by
  set Y : Strand ν → Bool := fun t => decide ((g.1 t).IsLeft ν₁)
  set X : Strand ν → Bool := fun t => decide (t.IsLeft ν')
  set T := shuffleTop Y C
  set F := shuffleBot X Y C
  set u := blockSort hν₁ (g • T)
  set v := blockSort hν' F
  set w := shuffleWord hD hZ X Y C
  have hw := goodWord_shuffleWord hD hZ X Y C
  have hfw : F.flips w = T := flips_shuffleWord hD hZ X Y C
  obtain ⟨h1, h2, h3⟩ := goodWord_smul (k := k) v hw
  rw [hfw] at h2 h3
  have hT : e T * galList k F w = galList k F w := by
    conv_lhs => rw [← hfw]
    exact e_mul_galList _ _
  have h4 : galList k F w * r v⁻¹ (v • F) =
      r v⁻¹ (v • T) * galList k (v • F) (w.map (Hyp.comap v⁻¹)) := by
    have := congrArg (fun z => r v⁻¹ (v • T) * z * r v⁻¹ (v • F)) h3
    simp only [mul_assoc] at this
    rw [r_mul_r_eq v F v⁻¹ (v • F), ite_eq_left (inv_smul_smul v F).symm, mul_inv_cancel, r_one,
      galList_mul_e, ← mul_assoc (r v⁻¹ (v • T)) (r v T), r_mul_r_eq, ite_eq_left rfl,
      inv_mul_cancel, r_one, ← mul_assoc, hT] at this
    exact this.symm
  refine ⟨w.map (Hyp.comap v⁻¹), h1, h2, ?_⟩
  rw [rankShuffleElt, shuffleElt]
  change r u (g • T) * (r g T * galList k F w) * r v⁻¹ (v • F) = _
  rw [← mul_assoc, r_mul_r, mul_assoc, h4, ← mul_assoc, r_mul_r_eq,
    ite_eq_left (inv_smul_smul v T).symm]
  rfl

/-- The set of strands of the bottom end of `ψ^W_g` sent into the first block of `ν₁`: the
strands `t` with `g (v⁻¹ t)` in the first block, `v` the block sort of `shuffleBot X Y C`. -/
noncomputable def rankShuffleSet (hν' : ν' + ν'' = ν) (ν₁ : I →₀ ℕ) (g : ColPerm ν)
    (C : FullChamber Γ ν) : Strand ν → Bool :=
  fun t => decide ((g.1 ((blockSort hν' (shuffleBot (fun t => decide (t.IsLeft ν'))
    (fun t => decide ((g.1 t).IsLeft ν₁)) C)).1⁻¹ t)).IsLeft ν₁)

omit [DecidableEq I] in
/-- The top end of `ψ^W_g` before rank ordering is the bottom end with the strands of
`rankShuffleSet` moved to the left. -/
theorem smul_shuffleTop_eq_rankShuffleSet (hν' : ν' + ν'' = ν) (ν₁ : I →₀ ℕ) (g : ColPerm ν)
    {C : FullChamber Γ ν} (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C) :
    blockSort hν' (shuffleBot (fun t => decide (t.IsLeft ν'))
        (fun t => decide ((g.1 t).IsLeft ν₁)) C) •
      shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C =
      shuffleTop (rankShuffleSet hν' ν₁ g C) (rankShuffleBot hν' ν₁ g C) :=
  smul_shuffleTop_eq _ hCs _

/-- **`ψ^W_g` is a four-block shuffle element.** For `C` separated by the strands of `ν'`,
`ψ^W_g = fourShuffle Z B` with `B = rankShuffleBot g C` and `Z = rankShuffleSet g C`. In
particular `ψ^W_g` depends on `(g, C)` only through `B` and `Z`. -/
theorem rankShuffleElt_eq_fourShuffle (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (g : ColPerm ν) {C : FullChamber Γ ν}
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C) :
    rankShuffleElt k hν' hν₁ hD hZ g C =
      fourShuffle k hD hZ (rankShuffleSet hν' ν₁ g C) (rankShuffleBot hν' ν₁ g C) := by
  obtain ⟨w, hw, hfw, he⟩ := rankShuffleElt_eq_r_mul_galList (k := k) hν' hν₁ hD hZ g C
  have hT := smul_shuffleTop_eq_rankShuffleSet (Γ := Γ) hν' ν₁ g hCs
  rw [hT] at hfw he
  rw [he]
  refine (fourShuffle_eq hD hZ _ _ ?_ hw hfw).symm
  rw [← hT, smul_smul, inv_mul_cancel_right, mul_smul]
  exact isRankOrdered_rankShuffleTop (k := k) hν₁ g C

/-- The bottom end of `ψ^W_g` is a four-block chamber for the strands of `ν'` and
`rankShuffleSet`. -/
theorem isFourBlock_rankShuffleBot (hν' : ν' + ν'' = ν) (ν₁ : I →₀ ℕ) (g : ColPerm ν)
    {C : FullChamber Γ ν} (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C) :
    IsFourBlock (fun t => decide (t.IsLeft ν')) (rankShuffleSet hν' ν₁ g C)
      (rankShuffleBot hν' ν₁ g C) := by
  refine ⟨isRankOrdered_rankShuffleBot (k := k) hν' ν₁ g C, ?_⟩
  set X : Strand ν → Bool := fun t => decide (t.IsLeft ν')
  set Y : Strand ν → Bool := fun t => decide ((g.1 t).IsLeft ν₁)
  set v := blockSort hν' (shuffleBot X Y C)
  have hX : (fun t => X (v.1⁻¹ t)) = X := by
    funext t
    have hv := blockSort_mem_leftBlockStab (Γ := Γ) hν' (shuffleBot X Y C)
    simp only [X]
    have := (hv (v.1⁻¹ t))
    rw [show v.1 (v.1⁻¹ t) = t from v.1.apply_symm_apply t] at this
    exact decide_eq_decide.2 this.symm
  have hB : rankShuffleBot hν' ν₁ g C = v • shuffleBot X Y C := rfl
  have hT := smul_shuffleTop_eq_rankShuffleSet (Γ := Γ) hν' ν₁ g hCs
  change sep X (shuffleTop _ _) (shuffleTop _ _) = _
  rw [← hT, hB]
  conv_lhs => rw [← hX]
  rw [← sep_smul]
  rfl

end GalleryAlgebra

end Categorification.WeightedKLR
