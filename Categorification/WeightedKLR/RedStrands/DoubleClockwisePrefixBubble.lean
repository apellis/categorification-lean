/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleClockwiseRedBubble
import Categorification.WeightedKLR.RedStrands.DoubleViolatedCut

/-! # Bubbles beyond a prefix of red strands

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29.
Transporting a real clockwise bubble across a list of red strands adds
the sum of their multiplicities in the bubble colour to its dot count.
-/

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams
universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  (μ : X) (i : I)

local notation "Str" => DoubleStrand I ℓ

/-- A clockwise bubble at a specified cut of the horizontal word. -/
def cwBubbleAt {w : List Str} (L R : List Str) (h : L ++ R = w) (m : ℕ) :
    End (obj RD Λ μ w) :=
  Diagram.cast (blackDiagram RD Λ μ L R (ccwReal RD (endWeight RD Λ μ L) i m))
    (by simp [blackWord,h]) (by simp [blackWord,h])

variable {k : Type w} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (P : Presentation.{w, max u v} (signature RD Λ) k)
local notation "T" => addDownRelations RD Λ (affineCoverQ Q exponents)
  (addRedUpRelations RD Λ k (addRedCapRelations RD Λ (addRedCupRelations RD Λ P)))

local notation "S" => addBlackAdjunctionRelations RD Λ (T)

private theorem cwBubbleAt_step {w : List Str} (L : List Str) (r : Fin ℓ) (R : List Str)
    (h : L ++ [.inr r] ++ R = w) (m : ℕ) :
    (S).diag (cwBubbleAt RD Λ μ i (L ++ [.inr r]) R h m) =
      (S).diag (cwBubbleAt RD Λ μ i L (.inr r :: R) (by simpa [List.append_assoc] using h)
        (m + exponents r i)) := by
  subst w
  exact cwBubble_slide RD Λ μ L i r R Q exponents P m

/-- Webster v3, Lemma 4.29. A real clockwise bubble passes a red word
with the sum of its multiplicities as the change in dot count. -/
theorem cwBubble_redWord {w : List Str} (rs : List (Fin ℓ)) (L R : List Str)
    (h : L ++ rs.map Sum.inr ++ R = w) (m : ℕ) :
    (S).diag (cwBubbleAt RD Λ μ i (L ++ rs.map Sum.inr) R h m) =
      (S).diag (cwBubbleAt RD Λ μ i L (rs.map Sum.inr ++ R) (by simpa [List.append_assoc] using h)
        (m + (rs.map (fun r => exponents r i)).sum)) := by
  induction rs generalizing L m with
  | nil => simp only [List.map_nil, List.nil_append, List.append_nil, List.sum_nil, Nat.add_zero]
  | cons r rs ih =>
    have hh : L ++ [.inr r] ++ (rs.map Sum.inr ++ R) = w := by
      simpa only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append] using h
    have step := cwBubbleAt_step RD Λ μ i Q exponents P L r (rs.map Sum.inr ++ R) hh (m + (rs.map (fun r => exponents r i)).sum)
    have hh' : (L ++ [.inr r]) ++ rs.map Sum.inr ++ R = w := by
      simpa only [List.append_assoc] using hh
    have next := ih (L ++ [.inr r]) hh' m
    simpa only [List.map_cons, List.cons_append, List.append_assoc, List.nil_append,
      List.sum_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using next.trans step

section Violating

variable (weights : Fin ℓ → {x : X // ∀ j, 0 ≤ RD.pair (RD.iY j) x})
local notation "lab" => (Subtype.val ∘ weights)

private theorem cwBubbleAt_left_zero
    (B : Presentation.{w, max u v} (signature RD lab) k) {η : X}
    (b : BoundaryCategory B η) (m : ℕ) :
    (violatingFunctor B η).map (InducedCategory.homMk (X := b) (Y := b)
      (B.diag (cwBubbleAt RD lab 0 i [] b.val.word (List.nil_append _) m))) = 0 := by
  let d := cwBubbleAt RD lab 0 i [] b.val.word (List.nil_append _) m
  let L := layer RD lab 0 [] (.black (.cup (up i))) b.val.word
  have hf : ∃ ls, Diagram.layers d = L :: ls := by
    change ∃ ls, Diagram.layers (Diagram.cast _ _ _) = _
    rw [Diagram.layers_cast]
    have hl := realBubble_layers RD lab 0 [] b.val.word .clockwise i m
    exact ⟨_, hl⟩
  obtain ⟨ls, hls⟩ := hf
  have hc := Diagram.chain d
  rw [hls] at hc
  let f := Diagram.layer L hc.1 hc.2.1 rfl
  let g := Diagram.mk ls hc.2.2
  have he : d = f ≫ g := by
    apply Diagram.ext
    exact hls
  change (violatingFunctor B η).map (InducedCategory.homMk (X := b) (Y := b) (B.diag d)) = 0
  rw [he]
  apply diagram_eq_zero_of_black_at_cut
  refine ⟨up i, ?_⟩
  rw [show L.cod = obj RD lab 0 ([] ++ (Move.black (.cup (up i))).top ++ b.val.word)
    from layer_cod ..]
  simp [obj, forget_colours, Move.top]

local notation "U" B => addDownRelations RD lab (affineCoverQ Q exponents)
  (addRedUpRelations RD lab k (addRedCapRelations RD lab (addRedCupRelations RD lab B)))

local notation "V" B => addBlackAdjunctionRelations RD lab (U B)

/-- In the violating quotient the real clockwise bubbles immediately
after an initial red word vanish. Every natural dot count is allowed. The suffix may contain signed black strands. -/
theorem cwBubble_afterRedPrefix_zero
    (B : Presentation.{w, max u v} (signature RD lab) k) {η : X}
    (b : DoubleStendhalTriple RD weights 0 η)
    (rs : List (Fin ℓ)) (R : List Str) (h : rs.map Sum.inr ++ R = b.val.word) (m : ℕ) :
    (violatingFunctor (V B) η).map (InducedCategory.homMk (X := b) (Y := b)
      ((V B).diag (cwBubbleAt RD lab 0 i (rs.map Sum.inr) R h m))) = 0 := by
  have hs := cwBubble_redWord RD lab 0 i Q exponents B rs [] R (by simpa) m
  simp only [List.nil_append] at hs
  rw [hs]
  let n := m + (rs.map (fun r => exponents r i)).sum
  have he : cwBubbleAt RD lab 0 i [] (rs.map Sum.inr ++ R) (by simpa using h) n =
      cwBubbleAt RD lab 0 i [] b.val.word (List.nil_append _) n := by
    apply Diagram.ext
    simp only [cwBubbleAt, Diagram.layers_cast]
    exact congrArg (fun v : List Str => Diagram.layers (blackDiagram RD lab 0 [] v
      (ccwReal RD (endWeight RD lab 0 []) i n))) h
  rw [he]
  exact cwBubbleAt_left_zero RD i weights (V B) b n

end Violating

end Categorification.Stendhal.DoubleDiagram
