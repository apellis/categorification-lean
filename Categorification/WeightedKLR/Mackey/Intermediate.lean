/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.KLR.SpacedSurjective
import Categorification.WeightedKLR.Induction.Embedding

/-!
# Minimal galleries through intermediate chambers

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). To factor a basis element of type `μ` through the diagram
exchanging two blocks of strands, its minimal gallery from `C` to `E` is chosen to pass through
intermediate chambers, and its pieces are recognized as images of galleries of smaller dimension
vectors.

A chamber `F` lies *between* `C` and `E` if it agrees with `C` (and `E`) on every hyperplane on
which `C` and `E` agree. Then two minimal galleries `C → F` and `F → E` concatenate to a minimal
gallery `C → E` (`GoodWord.append_of_between`). A chamber embedding maps minimal galleries to
minimal galleries (`ChamberEmbedding.goodWord_map`), and the image of the gallery of a minimal
gallery is the gallery of its image (`ChamberEmbedding.galleryHom_galList`).

## Main results

* `GoodWord.append_of_between`: concatenation of minimal galleries through a chamber between
  the two ends.
* `ChamberEmbedding.goodWord_map`, `ChamberEmbedding.flips_map`: images of minimal galleries.
* `ChamberEmbedding.galleryHom_galList`: images of galleries along minimal galleries.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

omit [IsStrictOrderedRing 𝕜] in
/-- **Concatenation through a chamber in between.** If `a` is a minimal gallery from `C` to `F`,
`b` a minimal gallery from `F` to `E`, and `F` agrees with `C` on every hyperplane on which `C`
and `E` agree, then `a ++ b` is a minimal gallery from `C` to `E`. -/
theorem GoodWord.append_of_between {C : FullChamber Γ ν} {a b : List (Hyp Γ ν)}
    (ha : GoodWord C.1 a) (hb : GoodWord (C.flips a).1 b)
    (hF : ∀ x, C.1 x = ((C.flips a).flips b).1 x → (C.flips a).1 x = C.1 x) :
    GoodWord C.1 (a ++ b) := by
  refine ha.append_of hb fun x hxa hxb => ?_
  have h1 := (ha.mem_iff x).1 hxa
  have h2 := (hb.mem_iff x).1 hxb
  refine h1 (hF x ?_)
  revert h1 h2
  cases C.1 x <;> cases (C.flips a).1 x <;> cases ((C.flips a).flips b).1 x <;> simp

namespace ChamberEmbedding

variable {ν₁ : I →₀ ℕ} (J : ChamberEmbedding Γ ν₁ ν)

theorem flipH_chamber {C : FullChamber Γ ν₁} {h : Hyp Γ ν₁} (hC : C.Adjacent (C.flipH h) h) :
    (J.chamber C).flipH (J.hyp h) = J.chamber (C.flipH h) :=
  flipH_eq_of_adjacent (J.adjacent_chamber hC)

/-- A chamber embedding maps minimal galleries to minimal galleries, and their ends to the ends
of the images. -/
theorem goodWord_map {C : FullChamber Γ ν₁} {w : List (Hyp Γ ν₁)} (hw : GoodWord C.1 w) :
    GoodWord (J.chamber C).1 (w.map J.hyp) ∧
      (J.chamber C).flips (w.map J.hyp) = J.chamber (C.flips w) := by
  induction w generalizing C with
  | nil => exact ⟨goodWord_nil _, rfl⟩
  | cons h w ih =>
    obtain ⟨-, hadj, hw'⟩ := hw.cons
    obtain ⟨ih₁, ih₂⟩ := ih hw'
    have hnm : J.hyp h ∉ w.map J.hyp := fun hm => by
      obtain ⟨h', hh', he⟩ := List.mem_map.1 hm
      exact (List.nodup_cons.1 hw.1).1 (J.hyp_injective he ▸ hh')
    rw [List.map_cons]
    refine ⟨GoodWord.of_cons (J.adjacent_chamber hadj) hnm ?_, ?_⟩
    · exact ih₁
    · rw [flips_cons, J.flipH_chamber hadj, ih₂, flips_cons]

theorem flips_map {C : FullChamber Γ ν₁} {w : List (Hyp Γ ν₁)} (hw : GoodWord C.1 w) :
    (J.chamber C).flips (w.map J.hyp) = J.chamber (C.flips w) :=
  (J.goodWord_map hw).2

/-- **Images of galleries.** The image under a chamber embedding of the gallery of a minimal
gallery `w` from `C` is the gallery of the image of `w` from the image of `C`. -/
theorem galleryHom_galList {C : FullChamber Γ ν₁} {w : List (Hyp Γ ν₁)} (hw : GoodWord C.1 w) :
    (J.galleryHom (galList k C w)).1 = galList k (J.chamber C) (w.map J.hyp) := by
  induction w generalizing C with
  | nil => exact J.galleryHom_e C
  | cons h w ih =>
    obtain ⟨-, hadj, hw'⟩ := hw.cons
    rw [galList_cons, map_mul, IsIdempotentElem.corner_val_mul, ih hw', galleryHom_t,
      List.map_cons, galList_cons, J.flipH_chamber hadj]

end ChamberEmbedding

end Categorification.WeightedKLR
