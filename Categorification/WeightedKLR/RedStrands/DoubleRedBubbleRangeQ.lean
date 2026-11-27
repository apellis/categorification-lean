/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBubbleRelations
import Categorification.Diagrams.KL3.Lemma39
import Categorification.Diagrams.CLQ.Lemma39

/-!
# Images of the bubble algebra at two weights

Webster, arXiv:1309.3796v2, §4.5, proof of Lemma 4.28, transports bubbles
across a red strand. By KL III, arXiv:0807.3250v1, (3.24)–(3.25) and
Proposition 3.6, transport of the normalized generators in both orientations
gives equality of the images of the entire bubble algebras.

This is the version of `DoubleRedBubbleRange` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v w z
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k)

/-- The element of the KL empty-boundary endomorphism algebra corresponding to a
normalized bubble in the physical orientation after reflection. -/
def normalizedEndBubbleQ (η : X) (i : I) (o : BubbleOrientation) (d : ℕ) : CLQ.EndOne RD k sc η :=
  CLQ.EndOne.of ((CLQ.pres RD k sc).lin (o.beforeReflectionExtended RD k η i (o.degreeZeroDots (ip RD i η) + d)))

private theorem bubGen_eq_normalizedQ (η : X) (i : I) (d : ℕ) :
    CLQ.EndOne.of (CLQ.bubGen RD k sc η i d) =
      normalizedEndBubbleQ RD k sc η i (if 0 ≤ ip RD i η then .counterclockwise else .clockwise) d := by
  unfold CLQ.bubGen
  split <;> rfl

variable {A : Type z} [Semiring A] [Algebra k A] (ηL ηR : X)
  (FL : CLQ.EndOne RD k sc ηL →ₐ[k] A) (FR : CLQ.EndOne RD k sc ηR →ₐ[k] A)

/-- KL III Proposition 3.6. An algebra map's image lies in the image at another
weight if the two maps agree on the normalized bubbles in both orientations.
At each weight, (3.24) picks its own orientation. -/
theorem normalizedBubble_range_leQ
    (h : ∀ i o d, FL (normalizedEndBubbleQ RD k sc ηL i o d) = FR (normalizedEndBubbleQ RD k sc ηR i o d)) :
    FR.range ≤ FL.range := by
  classical
  rintro _ ⟨x, rfl⟩
  obtain ⟨p, rfl⟩ := CLQ.prop36 (RD := RD) (k := k) ηR x
  change FR (CLQ.bubMap RD k sc ηR p) ∈ FL.range
  induction p using MvPolynomial.induction_on with
  | C c => rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]; exact FL.range.algebraMap_mem c
  | add p q hp hq => simpa only [map_add] using FL.range.add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul, map_mul]
    apply FL.range.mul_mem hp
    rw [CLQ.bubMap, MvPolynomial.aeval_X, bubGen_eq_normalizedQ, ← h]
    exact ⟨_, rfl⟩

/-- In Webster v2, Lemma 4.28, equality of normalized bubbles on both sides of a red
strand gives equality of the image subalgebras of all empty-boundary black endomorphisms. -/
theorem normalizedBubble_range_eqQ
    (h : ∀ i o d, FL (normalizedEndBubbleQ RD k sc ηL i o d) = FR (normalizedEndBubbleQ RD k sc ηR i o d)) :
    FL.range = FR.range :=
  le_antisymm (normalizedBubble_range_leQ RD k sc ηR ηL FR FL fun i o d => (h i o d).symm)
    (normalizedBubble_range_leQ RD k sc ηL ηR FL FR h)

end Categorification.Stendhal.DoubleDiagram
