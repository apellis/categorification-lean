/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.MinimalGallery
import Categorification.WeightedKLR.Mackey.ShuffleGallery

/-!
# Basis elements through the shuffle

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). Let `C` be a chamber in which the strands from the first
factor `ν'` lie to the left (`IsSeparated` for `Strand.IsLeft ν'`), and `D` one in which the
strands from `ν₁` lie to the left. For a relabelling `g`, the chamber `g⁻¹ • D` is separated by
the strands sent by `g` into the first block of `D` (`IsSeparated.smul`). The basis element
`b(g, m)` of `e D * A * e C` can therefore be computed, modulo shorter basis elements of the same
step of the filtration, along a minimal gallery that first rearranges the two blocks of `C`
separately, then performs the shuffle, then rearranges the two blocks of `g⁻¹ • D` separately
(`GalleryAlgebra.shuffle_sub_cornerBasis_mem`).

## Main results

* `Hyp.lo_comap`, `Hyp.hi_comap`: the strands of a hyperplane read before a relabelling.
* `FullChamber.IsSeparated.smul`: relabelling a separated chamber.
* `GalleryAlgebra.shuffle_sub_cornerBasis_mem`: the factorization of `b(g, m)` through the
  shuffle, modulo shorter basis elements of the same step of the filtration.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment Pointwise

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace Hyp

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem lo_comap (g : ColPerm ν) (x : Hyp Γ ν) :
    (x.comap g).lo = if x.reverses g then g.1⁻¹ x.hi else g.1⁻¹ x.lo := by
  rcases x with w | d
  · rfl
  · simp only [comap, reverses, lo, hi, Diag.comap]
    split_ifs <;> first | rfl | simp_all

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem hi_comap (g : ColPerm ν) (x : Hyp Γ ν) :
    (x.comap g).hi = if x.reverses g then g.1⁻¹ x.lo else g.1⁻¹ x.hi := by
  rcases x with w | d
  · rfl
  · simp only [comap, reverses, lo, hi, Diag.comap]
    split_ifs <;> first | rfl | simp_all

end Hyp

namespace FullChamber

omit [DecidableEq I] in
/-- Relabelling a chamber separated by `Z` gives a chamber separated by `Z ∘ g⁻¹`. -/
theorem IsSeparated.smul {Z : Strand ν → Bool} {D : FullChamber Γ ν} (hD : IsSeparated Z D)
    (g : ColPerm ν) : IsSeparated (fun t => Z (g.1⁻¹ t)) (g • D) := by
  intro x hx
  rw [smul_apply]
  have hl := Hyp.lo_comap g x
  have hh := Hyp.hi_comap g x
  cases hr : x.reverses g
  · rw [hr] at hl hh
    simp only [Bool.false_eq_true, ↓reduceIte] at hl hh ⊢
    rw [hD _ (by rw [hl, hh]; exact hx), hl]
  · rw [hr] at hl hh
    simp only [↓reduceIte] at hl hh ⊢
    rw [hD _ (by rw [hl, hh]; exact fun e => hx e.symm), hl]
    have hx' : Z (g.1⁻¹ x.lo) ≠ Z (g.1⁻¹ x.hi) := hx
    revert hx'
    cases Z (g.1⁻¹ x.lo) <;> cases Z (g.1⁻¹ x.hi) <;> simp

end FullChamber

namespace GalleryAlgebra

attribute [local instance] ColPerm.fintype

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- **Factorization through the shuffle.** Let `C`, `D` be rank-ordered, with the strands of
`ν'` to the left in `C` and those of `ν₁` to the left in `D`, and let `S` be a lower set of
shuffle types containing that of `g`. Put `X t = t.IsLeft ν'` and `Y t = (g t).IsLeft ν₁`. For
minimal galleries `a` from `C` to `shuffleBot X Y C`, `b` from there to `shuffleTop Y C` and `c`
from there to `g⁻¹ • D`, the element `r g (g⁻¹ • D) * c * b * a * y^m` differs from the basis
element `b(g, m)` by basis elements of shuffle type in `S` and shorter chosen gallery. The
gallery `a` crosses only hyperplanes inside the two blocks of `C`, `c` only hyperplanes inside the
preimages of the two blocks of `D`, and `b` is the shuffle (`mem_bot_shuffle`, `mem_top_shuffle`,
`mem_mid_shuffle`). -/
theorem shuffle_sub_cornerBasis_mem (ν' ν₁ : I →₀ ℕ) {D C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C)
    (hDs : IsSeparated (fun t => decide (t.IsLeft ν₁)) D) {S : Set (I → ℕ)} (hS : IsLowerSet S)
    {g : ColPerm ν} (hg : shuffleType ν' ν₁ g ∈ S) {a b c : List (Hyp Γ ν)}
    (ha : GoodWord C.1 a)
    (hfa : C.flips a = shuffleBot (fun t => decide (t.IsLeft ν'))
      (fun t => decide ((g.1 t).IsLeft ν₁)) C)
    (hb : GoodWord (shuffleBot (fun t => decide (t.IsLeft ν'))
      (fun t => decide ((g.1 t).IsLeft ν₁)) C).1 b)
    (hfb : (shuffleBot (fun t => decide (t.IsLeft ν')) (fun t => decide ((g.1 t).IsLeft ν₁))
      C).flips b = shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C)
    (hc : GoodWord (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C).1 c)
    (hfc : (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C).flips c = g⁻¹ • D)
    (m : Strand ν →₀ ℕ) :
    r g (g⁻¹ • D) * galList k (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) c *
        galList k (shuffleBot (fun t => decide (t.IsLeft ν'))
          (fun t => decide ((g.1 t).IsLeft ν₁)) C) b * galList k C a *
          poly (monomial m 1) -
        (cornerBasis hP hD hZ hΓ hW hL D C (g, m) : GalleryAlgebra k Γ ν) ∈
      Submodule.span k (Set.range fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
        shuffleType ν' ν₁ i.1 ∈ S ∧ segLength P C (i.1⁻¹ • D) < segLength P C (g⁻¹ • D)} =>
          (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν)) := by
  have hE : IsSeparated (fun t => decide ((g.1 t).IsLeft ν₁)) (g⁻¹ • D) := by
    have := hDs.smul g⁻¹
    simpa using this
  obtain ⟨hw, he⟩ := goodWord_shuffle hCs hE ha hfa hb hfb hc hfc
  have h := r_mul_galList_mul_sub_cornerBasis_mem hP hD hZ hΓ hW hL ν' ν₁ hC hD' hS hg hw he m
  rwa [galList_append, galList_append, hfa, flips_append, hfa, hfb, ← mul_assoc,
    ← mul_assoc] at h

end GalleryAlgebra

end Categorification.WeightedKLR
