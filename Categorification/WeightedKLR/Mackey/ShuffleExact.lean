/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.ShuffleElement
import Categorification.WeightedKLR.Mackey.CrossingGallery

/-!
# The shuffle element does not depend on the minimal gallery

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). The chambers `shuffleBot X Y C` and `shuffleTop Y C`
differ only on hyperplanes joining a strand of `X` to a strand outside `X`. By
`GalleryAlgebra.galList_eq_of_crossing`, all minimal galleries between them give the same
element of the gallery algebra. So the shuffle element `ψ_g` is the gallery product along
**any** minimal gallery from `shuffleBot X Y C` to `shuffleTop Y C`, followed by `g`
(`GalleryAlgebra.shuffleElt_eq`); the choice of `shuffleWord` plays no role, and the
congruence `GalleryAlgebra.shuffle_sub_shuffleWord_mem` is an equality.
-/

namespace Categorification.WeightedKLR

open FullChamber

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace FullChamber

omit [DecidableEq I] in
/-- A hyperplane on which `shuffleBot X Y C` and `shuffleTop Y C` differ is crossing for `X`. -/
theorem isCrossing_of_shuffleTop_ne (X Y : Strand ν → Bool) (C : FullChamber Γ ν)
    {h : Hyp Γ ν} (hne : (shuffleTop Y C).1 h ≠ (shuffleBot X Y C).1 h) : h.IsCrossing X := by
  intro hX
  rw [shuffleBot_apply, ite_eq_left hX] at hne
  exact hne rfl

end FullChamber

namespace GalleryAlgebra

/-- All minimal galleries from `shuffleBot X Y C` to `shuffleTop Y C` give the same element of
the gallery algebra. -/
theorem galList_eq_shuffleWord (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (X Y : Strand ν → Bool)
    (C : FullChamber Γ ν) {b : List (Hyp Γ ν)} (hb : GoodWord (shuffleBot X Y C).1 b)
    (hfb : (shuffleBot X Y C).flips b = shuffleTop Y C) :
    galList k (shuffleBot X Y C) b = galList k (shuffleBot X Y C) (shuffleWord hD hZ X Y C) :=
  galList_eq_of_crossing hD hZ X hb (goodWord_shuffleWord hD hZ X Y C)
    (hfb.trans (flips_shuffleWord hD hZ X Y C).symm)
    (fun h hh => isCrossing_of_shuffleTop_ne X Y C (by rwa [hfb] at hh))

/-- **The shuffle element along any minimal gallery.** `ψ_g = r g (shuffleTop Y C) * b` for every
minimal gallery `b` from `shuffleBot X Y C` to `shuffleTop Y C`, where `X t = t.IsLeft ν'` and
`Y t = (g t).IsLeft ν₁`. -/
theorem shuffleElt_eq (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (ν' ν₁ : I →₀ ℕ) (g : ColPerm ν)
    (C : FullChamber Γ ν) {b : List (Hyp Γ ν)}
    (hb : GoodWord (shuffleBot (fun t => decide (t.IsLeft ν'))
      (fun t => decide ((g.1 t).IsLeft ν₁)) C).1 b)
    (hfb : (shuffleBot (fun t => decide (t.IsLeft ν')) (fun t => decide ((g.1 t).IsLeft ν₁))
      C).flips b = shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) :
    shuffleElt k hD hZ ν' ν₁ g C =
      r g (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) *
        galList k (shuffleBot (fun t => decide (t.IsLeft ν'))
          (fun t => decide ((g.1 t).IsLeft ν₁)) C) b := by
  rw [shuffleElt, galList_eq_shuffleWord hD hZ _ _ C hb hfb]

end GalleryAlgebra

end Categorification.WeightedKLR
