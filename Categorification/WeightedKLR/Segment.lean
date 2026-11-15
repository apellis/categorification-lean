/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.Field.Basic

/-!
# Crossing orders of segments in an affine hyperplane arrangement

Let `f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜` be a finite family of affine functions on `𝕜^ι`, `𝕜` an ordered
field, defining an arrangement of hyperplanes `f h = 0`. A segment from a generic point `p` to a
generic point `q` crosses exactly the hyperplanes separating `p` and `q`, each once, at the time
`f h p / (f h p - f h q)`. When these times are distinct (a *simple* segment) the hyperplanes
crossed, in order, form the *word* of the segment.

This file records how words change: the words of two simple segments with endpoints in the same
chambers are related by *flips*, reversals of a block of hyperplanes through a common point
whose intersection has codimension two. This is the geometric input to the spanning part of the
basis theorem for weighted KLR algebras (B. Webster, arXiv:1209.2463v4, proof of
Theorem 2.13): two diagrams given by straight-line galleries are related by the local
relations at codimension-two flats.

## Main definitions

* `Segment.Generic f p`: `p` lies on no hyperplane.
* `Segment.signs f p`: the side of each hyperplane on which `p` lies.
* `Segment.crossTime f p q h`, `Segment.Separates f p q h`.
* `Segment.Simple f p q`: generic endpoints and distinct crossing times.
* `Segment.word f p q`: the hyperplanes crossed by the segment, in order.
* `Segment.Flip f w w'`: `w'` is obtained from `w` by reversing a block through a common point
  whose hyperplanes have a two-dimensional span of linear parts.
-/

namespace Categorification.WeightedKLR.Segment

variable {ι 𝕜 H : Type*} [Fintype ι] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Fintype H] [DecidableEq H] (f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜)

/-- A point on no hyperplane. -/
def Generic (p : ι → 𝕜) : Prop := ∀ h, f h p ≠ 0

/-- The side of each hyperplane on which a point lies. -/
def signs (p : ι → 𝕜) : H → Bool := fun h => decide (0 < f h p)

/-- The hyperplane `h` separates `p` and `q`. -/
def Separates (p q : ι → 𝕜) (h : H) : Prop := (0 < f h p) ≠ (0 < f h q)

instance (p q : ι → 𝕜) (h : H) : Decidable (Separates f p q h) := by
  unfold Separates; infer_instance

/-- The time at which the segment from `p` to `q` meets the hyperplane `h`. -/
def crossTime (p q : ι → 𝕜) (h : H) : 𝕜 := f h p / (f h p - f h q)

/-- A simple segment: generic endpoints and distinct crossing times. -/
def Simple (p q : ι → 𝕜) : Prop :=
  Generic f p ∧ Generic f q ∧ ∀ h g, Separates f p q h → Separates f p q g → h ≠ g →
    crossTime f p q h ≠ crossTime f p q g

/-- The hyperplanes crossed by the segment from `p` to `q`, ordered by crossing time. -/
noncomputable def word (p q : ι → 𝕜) : List H :=
  ((Finset.univ.filter (Separates f p q)).toList).insertionSort
    (fun h g => crossTime f p q h ≤ crossTime f p q g)

/-- The sign vector `σ` with the entries in `l` flipped. -/
def flipSigns (σ : H → Bool) (l : List H) : H → Bool := fun h => xor (σ h) (decide (h ∈ l))

/-- The point at time `t` of the segment from `p` to `q`. -/
def segPt (p q : ι → 𝕜) (t : 𝕜) : ι → 𝕜 := p + t • (q - p)

/-- `w'` is obtained from `w` by reversing a block `B` of at least two hyperplanes which are
exactly the hyperplanes through some point, and whose linear parts span a plane. -/
def Flip (w w' : List H) : Prop :=
  ∃ a B c : List H, w = a ++ B ++ c ∧ w' = a ++ B.reverse ++ c ∧ 2 ≤ B.length ∧
    (∃ x : ι → 𝕜, ∀ h, f h x = 0 ↔ h ∈ B) ∧
    Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h => (f h).linear) '' {h | h ∈ B})) = 2

end Categorification.WeightedKLR.Segment
