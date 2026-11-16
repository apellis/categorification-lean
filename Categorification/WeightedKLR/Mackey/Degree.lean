/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GalleryBasis.Graded

/-!
# The degree of a straight gallery

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.1 (degree
function) and Theorem 2.8. The gallery of the basis element of Theorem 2.8 attached to a pair of
chambers `C, E` follows a straight segment, which crosses each hyperplane separating `C` and `E`
exactly once. Its degree is therefore the sum of the degrees of these hyperplanes; it depends only
on `C` and `E`, not on the chosen segment. This is the input for the degree shift in the Mackey
filtration of §2.4 (proof of Theorem 2.19, citing Khovanov–Lauda, arXiv:0803.4121v2,
Proposition 2.18).

## Main results

* `GradingDatum.galDeg_of_goodWord`: along a good word the degree is the sum of the degrees of
  the hyperplanes of the word.
* `GradingDatum.segDeg_eq_sum`: the degree of the straight gallery from `C` to `E` is the sum of
  `hypDeg` over the hyperplanes on which `C` and `E` differ.
-/

namespace Categorification.WeightedKLR

open FullChamber Segment GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GradingDatum

variable (G : GradingDatum Γ)

omit [IsStrictOrderedRing 𝕜] in
/-- Along a good word the degree of the gallery is the sum of the degrees of its hyperplanes. -/
theorem galDeg_of_goodWord {C : FullChamber Γ ν} {w : List (Hyp Γ ν)} (hw : GoodWord C.1 w) :
    G.galDeg C w = (w.map G.hypDeg).sum := by
  induction w generalizing C with
  | nil => rfl
  | cons h w ih =>
    obtain ⟨-, hadj, hw'⟩ := hw.cons
    rw [galDeg, ih hw', G.stepDeg_of_adjacent hadj, List.map_cons, List.sum_cons, add_comm]

/-- **Degree of a straight gallery.** For a chamber segment from `C` to `E`, the degree of the
gallery along it is the sum of the degrees of the hyperplanes on which `C` and `E` differ. -/
theorem segDeg_eq_sum (P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜))
    {C E : FullChamber Γ ν} (hP : IsChamberSegment C E (P C E)) :
    G.segDeg P C E = ∑ h ∈ Finset.univ.filter (fun h => C.1 h ≠ E.1 h), G.hypDeg h := by
  obtain ⟨hs, hC, hE⟩ := hP
  have hw : GoodWord C.1 (word (hypAff (Γ := Γ)) (P C E).1 (P C E).2) := hC ▸ goodWord_word hs
  rw [segDeg, G.galDeg_of_goodWord hw, word, (List.perm_insertionSort _ _).map _ |>.sum_eq,
    Finset.sum_map_toList]
  refine Finset.sum_congr (Finset.filter_congr fun h _ => ?_) fun _ _ => rfl
  rw [← hC, ← hE]
  simp only [Separates, fullSigns, ne_eq, decide_eq_decide, eq_iff_iff]
  exact Iff.rfl

end GradingDatum

end Categorification.WeightedKLR
