/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBubbleRelations
import Categorification.Diagrams.KL3.Lemma39

/-!
# Images of the bubble algebra at two weights

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, transports bubbles
across a red strand. By KL III, arXiv:0807.3250v1, (3.24)–(3.25) and
Proposition 3.6, transport of the normalized generators in both orientations
gives equality of the images of the entire bubble algebras.
-/

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v w z
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

/-- The element of the KL empty-boundary endomorphism algebra corresponding to a
normalized bubble in the physical orientation after reflection. -/
def normalizedEndBubble (η : X) (i : I) (o : BubbleOrientation) (d : ℕ) : EndOne RD k η :=
  EndOne.of ((pres RD k).lin (o.beforeReflectionExtended RD k η i (o.degreeZeroDots (ip RD i η) + d)))

private theorem bubGen_eq_normalized (η : X) (i : I) (d : ℕ) :
    EndOne.of (bubGen RD k η i d) =
      normalizedEndBubble RD k η i (if 0 ≤ ip RD i η then .counterclockwise else .clockwise) d := by
  unfold bubGen
  split <;> rfl

variable {A : Type z} [Semiring A] [Algebra k A] (ηL ηR : X)
  (FL : EndOne RD k ηL →ₐ[k] A) (FR : EndOne RD k ηR →ₐ[k] A)

/-- KL III Proposition 3.6. An algebra map's image lies in the image at another
weight if the two maps agree on the normalized bubbles in both orientations.
At each weight, (3.24) picks its own orientation. -/
theorem normalizedBubble_range_le
    (h : ∀ i o d, FL (normalizedEndBubble RD k ηL i o d) = FR (normalizedEndBubble RD k ηR i o d)) :
    FR.range ≤ FL.range := by
  classical
  rintro _ ⟨x, rfl⟩
  obtain ⟨p, rfl⟩ := prop36 (RD := RD) (k := k) ηR x
  change FR (bubMap RD k ηR p) ∈ FL.range
  induction p using MvPolynomial.induction_on with
  | C c => rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]; exact FL.range.algebraMap_mem c
  | add p q hp hq => simpa only [map_add] using FL.range.add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul, map_mul]
    apply FL.range.mul_mem hp
    rw [bubMap, MvPolynomial.aeval_X, bubGen_eq_normalized, ← h]
    exact ⟨_, rfl⟩

/-- In Webster v3, Lemma 4.29, equality of normalized bubbles on both sides of a red
strand gives equality of the image subalgebras of all empty-boundary black endomorphisms. -/
theorem normalizedBubble_range_eq
    (h : ∀ i o d, FL (normalizedEndBubble RD k ηL i o d) = FR (normalizedEndBubble RD k ηR i o d)) :
    FL.range = FR.range :=
  le_antisymm (normalizedBubble_range_le RD k ηR ηL FR FL fun i o d => (h i o d).symm)
    (normalizedBubble_range_le RD k ηL ηR FL FR h)

end Categorification.Stendhal.DoubleDiagram
