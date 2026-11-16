/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.KLR.SpacedSurjective

/-!
# Galleries crossing only hyperplanes between two sets of strands

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). Let `X : Strand ν → Bool` split the strands in two sets.
A hyperplane is *crossing* for `X` if its two strands lie in different sets. If every hyperplane
separating two chambers `C` and `E` is crossing, then all minimal galleries from `C` to `E` give
the **same** element of the gallery algebra, not only the same element modulo shorter galleries
(`GalleryAlgebra.galList_eq_of_crossing`). Indeed a flip reverses the hyperplanes through a
flat of codimension two; three of them would lie on the three pairs of three strands, two of
which are in the same set, so every block has two hyperplanes and the flip is an exact square
relation.

This is the exactness used for the shuffle element of the four-block juxtaposition: its gallery
crosses only the hyperplanes between the second and third blocks.
-/

namespace Categorification.WeightedKLR

open Segment FullChamber

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace Hyp

/-- The hyperplane `h` is *crossing* for `X`: its two strands lie in different sets. -/
def IsCrossing (X : Strand ν → Bool) (h : Hyp Γ ν) : Prop := X h.lo ≠ X h.hi

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem IsPair.isCrossing_iff {X : Strand ν → Bool} {h : Hyp Γ ν} {a b : Strand ν}
    (hp : h.IsPair a b) : h.IsCrossing X ↔ X a ≠ X b := by
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [IsCrossing, h1, h2, ne_comm]

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Three hyperplanes on the three pairs of three strands are not all crossing. -/
theorem not_isCrossing_triangle {X : Strand ν → Bool} {h₁ h₂ h₃ : Hyp Γ ν} {u v w : Strand ν}
    (p₁ : h₁.IsPair u v) (p₂ : h₂.IsPair u w) (p₃ : h₃.IsPair v w) (c₁ : h₁.IsCrossing X)
    (c₂ : h₂.IsCrossing X) (c₃ : h₃.IsCrossing X) : False := by
  rw [p₁.isCrossing_iff] at c₁
  rw [p₂.isCrossing_iff] at c₂
  rw [p₃.isCrossing_iff] at c₃
  cases hu : X u <;> cases hv : X v <;> cases hw : X w <;> simp_all

end Hyp

namespace GalleryAlgebra

/-- A block of crossing hyperplanes through a flat of codimension two has exactly two
hyperplanes, and reversing it does not change the gallery. -/
theorem galList_block_eq_of_crossing (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (X : Strand ν → Bool)
    (E : FullChamber Γ ν) {B : List (Hyp Γ ν)} (hlen : 2 ≤ B.length) {x : Strand ν → 𝕜}
    (hx : ∀ h : Hyp Γ ν, h.val x = 0 ↔ h ∈ B)
    (hB : Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h => (hypAff h).linear) '' {h | h ∈ B})) = 2)
    (hc : ∀ h ∈ B, h.IsCrossing X) (hw : GoodWord E.1 B) (hw' : GoodWord E.1 B.reverse) :
    galList k E B = galList k E B.reverse := by
  have hle := block_length_le hD hZ hx hB hw.1
  have heq := flips_eq_of_perm hw hw' (List.reverse_perm B).symm
  match B, hlen, hle, hx, hB, hc, hw, hw', heq with
  | [h₁, h₂], _, _, hx, _, _, hw, hw', heq =>
    have hn : h₁ ≠ h₂ := by simpa using hw.1
    obtain ⟨-, a₁, hw₁⟩ := hw.cons
    obtain ⟨-, a₂, -⟩ := hw₁.cons
    obtain ⟨-, a₃, hw₃⟩ := hw'.cons
    obtain ⟨-, a₄, -⟩ := hw₃.cons
    have hD' : (E.flipH h₂).flipH h₁ = (E.flipH h₁).flipH h₂ := heq.symm
    rw [hD'] at a₄
    have := galList_square (k := k) hn (independent_of_pair hD hZ hx hn) a₁ a₂ a₃ a₄
    simpa using this
  | [h₁, h₂, h₃], _, _, hx, hB, hc, hw, _, _ =>
    have hn := hw.1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨⟨n₁₂, n₁₃⟩, n₂₃, -⟩ := hn
    obtain ⟨u, v, w, p₁, p₂, p₃⟩ := Hyp.triangle hD hZ hx hB (h₁ := h₁) (h₂ := h₂) (h₃ := h₃)
      (by simp) (by simp) (by simp) n₁₂ n₁₃ n₂₃
    exact (Hyp.not_isCrossing_triangle p₁ p₂ p₃ (hc _ (by simp)) (hc _ (by simp))
      (hc _ (by simp))).elim

/-- A flip of a word of crossing hyperplanes, all of whose prefixes are chambers, does not
change the gallery. -/
theorem galList_flip_eq_of_crossing (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (X : Strand ν → Bool)
    {C : FullChamber Γ ν} {w w' : List (Hyp Γ ν)} (hw : GoodWord C.1 w)
    (hc : ∀ h ∈ w, h.IsCrossing X) (hf : Flip (hypAff (Γ := Γ)) C.1 w w') :
    galList k C w = galList k C w' := by
  have hw' := hw.flip hf
  obtain ⟨a, B, c, rfl, rfl, hlen, ⟨x, hx, -⟩, hB⟩ := hf
  have g₁ : GoodWord C.1 (a ++ B) := hw.of_append
  have g₂ : GoodWord C.1 (a ++ B.reverse) := hw'.of_append
  have hend : C.flips (a ++ B) = C.flips (a ++ B.reverse) :=
    flips_eq_of_perm g₁ g₂ ((List.reverse_perm B).symm.append_left a)
  have hblock := galList_block_eq_of_crossing (k := k) hD hZ X (C.flips a) hlen (x := x)
    (fun h => hx h) hB (fun h hh => hc h (by simp [hh])) g₁.append g₂.append
  rw [galList_append C (a ++ B), galList_append C (a ++ B.reverse), galList_append C a B,
    galList_append C a B.reverse, hend, hblock]

/-- A chain of flips of a word of crossing hyperplanes, all of whose prefixes are chambers, does
not change the gallery. -/
theorem galList_reflTransGen_eq_of_crossing (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (X : Strand ν → Bool) {C : FullChamber Γ ν} {w w' : List (Hyp Γ ν)} (hw : GoodWord C.1 w)
    (hc : ∀ h ∈ w, h.IsCrossing X)
    (hr : Relation.ReflTransGen (Flip (hypAff (Γ := Γ)) C.1) w w') :
    galList k C w = galList k C w' := by
  induction hr with
  | refl => rfl
  | @tail w₁ w₂ hr hf ih =>
    have hp := reflTransGen_flip_perm hr
    rw [ih, galList_flip_eq_of_crossing (k := k) hD hZ X (hw.reflTransGen hr)
      (fun h hh => hc h (hp.symm.mem_iff.1 hh)) hf]

/-- **Exactness of galleries through crossing hyperplanes.** If every hyperplane on which the
chambers `C` and `E` differ is crossing for `X`, then any two minimal galleries from `C` to `E`
give the same element of the gallery algebra. -/
theorem galList_eq_of_crossing (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (X : Strand ν → Bool)
    {C : FullChamber Γ ν} {w w' : List (Hyp Γ ν)} (hw : GoodWord C.1 w) (hw' : GoodWord C.1 w')
    (he : C.flips w = C.flips w')
    (hc : ∀ h : Hyp Γ ν, (C.flips w).1 h ≠ C.1 h → h.IsCrossing X) :
    galList k C w = galList k C w' := by
  have hcw : ∀ h ∈ w, h.IsCrossing X := fun h hh => hc h ((hw.mem_iff h).1 hh)
  obtain ⟨p, q, hs, hp, hq, hr⟩ := exists_simple_of_goodWord hD hZ hw
  obtain ⟨p', q', hs', hp', hq', hr'⟩ := exists_simple_of_goodWord hD hZ hw'
  have hr₂ : Relation.ReflTransGen (Flip (hypAff (Γ := Γ)) C.1) (word (hypAff (Γ := Γ)) p q)
      (word (hypAff (Γ := Γ)) p' q') := by
    rw [← hp]
    exact reflTransGen_flip_of_simple (f := hypAff (Γ := Γ)) (hdist hD hZ) hs hs'
      (show fullSigns p' = fullSigns p by rw [hp, hp'])
      (show fullSigns q' = fullSigns q by rw [hq, hq', he])
  have l₁ := reflTransGen_flip_perm hr
  have l₂ := reflTransGen_flip_perm hr₂
  have l₃ := reflTransGen_flip_perm hr'
  have c₂ : ∀ h ∈ word (hypAff (Γ := Γ)) p q, h.IsCrossing X :=
    fun h hh => hcw h (l₁.symm.mem_iff.1 hh)
  have c₃ : ∀ h ∈ w', h.IsCrossing X :=
    fun h hh => c₂ h (l₂.symm.mem_iff.1 (l₃.mem_iff.1 hh))
  rw [galList_reflTransGen_eq_of_crossing (k := k) hD hZ X hw hcw hr,
    galList_reflTransGen_eq_of_crossing (k := k) hD hZ X (hw.reflTransGen hr) c₂ hr₂,
    galList_reflTransGen_eq_of_crossing (k := k) hD hZ X hw' c₃ hr']

end GalleryAlgebra

end Categorification.WeightedKLR
