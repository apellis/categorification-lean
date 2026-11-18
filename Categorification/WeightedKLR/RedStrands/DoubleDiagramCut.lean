/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDiagram

/-!
# Horizontal cuts of double Stendhal diagrams

Webster, arXiv:1309.3796v2, Definitions 4.22–4.24 and 4.27. A horizontal cut
preserves the order of the red strands and both extreme region labels, even
when a cup has changed the number of black strands. Thus every cut in a
diagram starting at a double Stendhal triple is again a unique triple in
the same weight fibre.
-/

namespace Categorification.Stendhal.DoubleDiagram

open QuantumGroup QuantumGroup.UDot StringDiagrams CategoryTheory

variable {I X Y : Type*} {C : CartanDatum I} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X)

private theorem forget_colours (μ : X) (w : List (DoubleStrand I ℓ)) :
    (colours RD Λ μ w).map Prod.snd = w := by
  induction w generalizing μ with
  | nil => rfl
  | cons a w ih => simp [colours, ih]

private theorem recover_colours (μ : X) (w : List (X × DoubleStrand I ℓ))
    (h : (signature RD Λ).ok μ w) : colours RD Λ μ (w.map Prod.snd) = w := by
  induction w generalizing μ with
  | nil => rfl
  | cons c w ih =>
    obtain ⟨t, a⟩ := c
    obtain ⟨rfl, hw⟩ := h
    exact congrArg ((t, a) :: ·) (ih _ hw)

private def readReds (a : Obj (signature RD Λ)) : List (Fin ℓ) :=
  (a.word.map Prod.snd).filterMap DoubleStrand.redLabel

private theorem layer_redOrder (L : Layer (signature RD Λ)) :
    readReds RD Λ L.cod = readReds RD Λ L.dom := by
  let reds (v : List (X × DoubleStrand I ℓ)) := (v.map Prod.snd).filterMap DoubleStrand.redLabel
  have append (l r : List (X × DoubleStrand I ℓ)) : reds (l ++ r) = reds l ++ reds r := by
    simp [reds]
  let l : List (X × DoubleStrand I ℓ) := L.left
  let r : List (X × DoubleStrand I ℓ) := L.right
  change reds ((l ++ colours RD Λ L.gen.1 L.gen.2.top) ++ r) =
    reds ((l ++ colours RD Λ L.gen.1 L.gen.2.bottom) ++ r)
  simp only [append, reds, forget_colours, L.gen.2.top_reds]

private theorem chain_redOrder {a b : Obj (signature RD Λ)} {ls} (h : Chain a ls b) :
    readReds RD Λ b = readReds RD Λ a := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih => rw [ih h.2.2, layer_redOrder, h.2.1]

private theorem chain_ok {a b : Obj (signature RD Λ)} {ls} (h : Chain a ls b)
    (ha : (signature RD Λ).ok a.start a.word) : (signature RD Λ).ok b.start b.word := by
  induction ls generalizing a with
  | nil => cases h; exact ha
  | cons L ls ih =>
    apply ih h.2.2
    obtain ⟨hl, he, _, _, hc, he', hr⟩ := h.1
    simpa [Layer.cod, Signature.ok_append, he, he', hl, hc] using hr

variable {Λ} {μ ν : X} (weights : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x})
local notation "labels" => (Subtype.val ∘ weights)

/-- Every cut reached from a double Stendhal triple is the labelled object
of a unique triple with the same red labels and the same extreme weights. -/
theorem existsUnique_triple_at_cut (b : DoubleStendhalTriple RD weights μ ν)
    {a : Obj (signature RD labels)} (d : obj RD labels μ b.val.word ⟶ a) :
    ∃! t : DoubleStendhalTriple RD weights μ ν, obj RD labels μ t.val.word = a := by
  have h := Diagram.chain d
  have ha : a.start = μ := h.start_eq
  have hok := chain_ok RD labels h (colours_ok RD labels μ b.val.word)
  let w := a.word.map Prod.snd
  have hw : colours RD labels μ w = a.word := ha ▸ recover_colours RD labels a.start a.word hok
  have hred := chain_redOrder RD labels h
  change w.filterMap DoubleStrand.redLabel =
    ((colours RD labels μ b.val.word).map Prod.snd).filterMap DoubleStrand.redLabel at hred
  rw [forget_colours, b.val.redOrder] at hred
  let c : DoubleBoundary I ℓ := ⟨w, hred⟩
  have he : obj RD labels μ w = a := by
    exact Obj.ext ha.symm hw
  have hend := h.endR_eq
  rw [← he] at hend
  change (signature RD labels).endR μ (colours RD labels μ w) =
    (signature RD labels).endR μ (colours RD labels μ b.val.word) at hend
  rw [colours_endR, colours_endR] at hend
  let t : DoubleStendhalTriple RD weights μ ν := ⟨c, hend.trans b.property⟩
  refine ⟨t, he, ?_⟩
  intro t' ht'
  apply Subtype.ext
  apply DoubleBoundary.ext
  have hword := congrArg (fun x : Obj (signature RD labels) => x.word.map Prod.snd) (ht'.trans he.symm)
  simpa only [obj, forget_colours] using hword

end Categorification.Stendhal.DoubleDiagram
