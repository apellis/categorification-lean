/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDiagram
import StringDiagrams.Positional

/-!
# Rewriting signed Stendhal layers in context

Webster, arXiv:1309.3796v2, §4.5, Definitions 4.22 and 4.24.
A list of signed moves determines a diagram when its boundary words match.
The interchange law and local replacement act directly on these lists.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot

universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k]

/-- A signed generator with the words on its left and right. -/
abbrev SignedLayer (I : Type u) (ℓ : ℕ) :=
  List (DoubleStrand I ℓ) × Move I ℓ × List (DoubleStrand I ℓ)

/-- A list of signed moves whose boundary words match. -/
def signedChain (s : List (DoubleStrand I ℓ)) :
    List (SignedLayer I ℓ) → List (DoubleStrand I ℓ) → Prop
  | [], t => s = t
  | (L, g, R) :: ls, t =>
    s = L ++ g.bottom ++ R ∧ signedChain (L ++ g.top ++ R) ls t

/-- Concatenate matching lists of signed moves. -/
theorem signedChain.append {s t z : List (DoubleStrand I ℓ)} {A B : List (SignedLayer I ℓ)}
    (hA : signedChain s A t) (hB : signedChain t B z) : signedChain s (A ++ B) z := by
  induction A generalizing s with
  | nil => cases hA; exact hB
  | cons a ls ih => exact ⟨hA.1, ih hA.2⟩

/-- Insert the region labels in a list of signed moves. -/
def signedLayers (μ : X) (ls : List (SignedLayer I ℓ)) : List (Layer (signature RD Λ)) :=
  ls.map fun (L, g, R) => layer RD Λ μ L g R

/-- Matching signed words give a well-formed diagram with region labels. -/
theorem chain_signedLayers (μ : X) {s t : List (DoubleStrand I ℓ)}
    {ls : List (SignedLayer I ℓ)} (hl : signedChain s ls t) :
    Chain (obj RD Λ μ s) (signedLayers RD Λ μ ls) (obj RD Λ μ t) := by
  induction ls generalizing s with
  | nil => exact congrArg (obj RD Λ μ) hl
  | cons a ls ih =>
    obtain ⟨L, g, R⟩ := a
    refine ⟨layer_valid .., (layer_dom ..).trans (congrArg _ hl.1.symm), ?_⟩
    rw [layer_cod RD Λ μ L g R]
    exact ih hl.2

/-- The class of a signed diagram given by a list of moves in their contexts. -/
def signedDg (P : Presentation.{w, max u v} (signature RD Λ) k) (μ : X)
    (s t : List (DoubleStrand I ℓ)) (ls : List (SignedLayer I ℓ)) :
    P.obj (obj RD Λ μ s) ⟶ P.obj (obj RD Λ μ t) := by
  classical
  exact if h : signedChain s ls t then P.diag (Diagram.mk _ (chain_signedLayers RD Λ μ h)) else 0

/-- Evaluate a well-formed list of signed moves. -/
theorem signedDg_of (P : Presentation.{w, max u v} (signature RD Λ) k) (μ : X)
    {s t : List (DoubleStrand I ℓ)} {ls : List (SignedLayer I ℓ)} (hl : signedChain s ls t) :
    signedDg RD Λ P μ s t ls = P.diag (Diagram.mk _ (chain_signedLayers RD Λ μ hl)) := by
  simp [signedDg, hl]

/-- Identify a signed move list with a raw diagram having the same layers. -/
theorem signedDg_eq_diag_of_layers (P : Presentation.{w, max u v} (signature RD Λ) k) (μ : X)
    {s t : List (DoubleStrand I ℓ)} {ls : List (SignedLayer I ℓ)} (hl : signedChain s ls t)
    (d : obj RD Λ μ s ⟶ obj RD Λ μ t) (hd : Diagram.layers d = signedLayers RD Λ μ ls) :
    signedDg RD Λ P μ s t ls = P.diag d := by
  rw [signedDg_of RD Λ P μ hl]
  exact congrArg P.diag (Diagram.ext hd.symm)

/-- The empty list of moves is the identity. -/
theorem signedDg_nil (P : Presentation.{w, max u v} (signature RD Λ) k) (μ : X)
    (s : List (DoubleStrand I ℓ)) : signedDg RD Λ P μ s s [] = 𝟙 _ := by
  rw [signedDg_eq_diag_of_layers RD Λ P μ (show signedChain s [] s from rfl) (𝟙 _) rfl, P.diag_id]

/-- Read the concatenation of two signed move lists as a composite. -/
theorem signedDg_comp (P : Presentation.{w, max u v} (signature RD Λ) k) (μ : X)
    {s t z : List (DoubleStrand I ℓ)} {A B : List (SignedLayer I ℓ)}
    (hA : signedChain s A t) (hB : signedChain t B z) :
    signedDg RD Λ P μ s t A ≫ signedDg RD Λ P μ t z B = signedDg RD Λ P μ s z (A ++ B) := by
  rw [signedDg_of RD Λ P μ hA, signedDg_of RD Λ P μ hB, ← P.diag_comp,
    signedDg_of RD Λ P μ (hA.append hB)]
  apply congrArg P.diag
  apply Diagram.ext
  simp [signedLayers]

/-- Replace consecutive signed moves in a typed context. -/
theorem signedDg_replace (P : Presentation.{w, max u v} (signature RD Λ) k) (μ : X)
    {s a b t : List (DoubleStrand I ℓ)}
    (pre A B post : List (SignedLayer I ℓ))
    (hpre : signedChain s pre a) (hpost : signedChain b post t)
    (hA : signedChain a A b) (hB : signedChain a B b)
    (h : signedDg RD Λ P μ a b A = signedDg RD Λ P μ a b B) :
    signedDg RD Λ P μ s t (pre ++ A ++ post) = signedDg RD Λ P μ s t (pre ++ B ++ post) := by
  rw [← signedDg_comp RD Λ P μ (hpre.append hA) hpost, ← signedDg_comp RD Λ P μ (hpre.append hB) hpost,
    ← signedDg_comp RD Λ P μ hpre hA, ← signedDg_comp RD Λ P μ hpre hB, h]

/-- Exchange two disjoint signed moves. -/
theorem signedDg_swap (P : Presentation.{w, max u v} (signature RD Λ) k) (μ : X)
    (L M R : List (DoubleStrand I ℓ)) (g h : Move I ℓ)
    {s t : List (DoubleStrand I ℓ)}
    (hs : s = L ++ g.bottom ++ M ++ h.bottom ++ R)
    (ht : t = L ++ g.top ++ M ++ h.top ++ R) :
    signedDg RD Λ P μ s t [(L, g, M ++ h.bottom ++ R), (L ++ g.top ++ M, h, R)] =
      signedDg RD Λ P μ s t [(L ++ g.bottom ++ M, h, R), (L, g, M ++ h.top ++ R)] := by
  subst s t
  let η := endWeight RD Λ μ L
  let θ := endWeight RD Λ η g.bottom
  let ξ := endWeight RD Λ θ M
  let tail := colours RD Λ (endWeight RD Λ ξ h.bottom) R
  have w : endWeight RD Λ η g.top = θ := g.endWeight_top RD Λ η
  rw [signedDg_of RD Λ P μ (by simp [signedChain, List.append_assoc]),
    signedDg_of RD Λ P μ (by simp [signedChain, List.append_assoc])]
  apply P.diag_interchange_of_layers_of_even μ (colours RD Λ μ L)
    (colours RD Λ θ M) tail (η, g) (ξ, h) (Or.inl rfl)
  all_goals
    simp [signedLayers, layer, signature, η, θ, ξ, tail, colours_append, endWeight_append,
      g.endWeight_top, h.endWeight_top, List.append_assoc]

/-- Replace a segment of a signed move list at the given position. -/
theorem signedDg_replaceAt (P : Presentation.{w, max u v} (signature RD Λ) k) (μ : X)
    {s a b t : List (DoubleStrand I ℓ)} (ls : List (SignedLayer I ℓ)) (n : ℕ)
    {A B : List (SignedLayer I ℓ)}
    (eqv : signedDg RD Λ P μ a b A = signedDg RD Λ P μ a b B)
    (hpre : signedChain s (ls.take n) a) (hpost : signedChain b (ls.drop (n + A.length)) t)
    (hA : signedChain a A b) (hB : signedChain a B b)
    (hpart : (ls.drop n).take A.length = A) :
    signedDg RD Λ P μ s t ls = signedDg RD Λ P μ s t
      (ls.take n ++ B ++ ls.drop (n + A.length)) := by
  have he : ls.take n ++ A ++ ls.drop (n + A.length) = ls := by
    rw [List.append_assoc, ← List.drop_drop]
    exact congrArg (ls.take n ++ ·)
      ((congrArg (· ++ (ls.drop n).drop A.length) hpart.symm).trans
        (List.take_append_drop (i := A.length) ..)) |>.trans (List.take_append_drop ..)
  exact (congrArg (signedDg RD Λ P μ s t) he.symm).trans
    (signedDg_replace RD Λ P μ _ _ _ _ hpre hpost hA hB eqv)

/-- Replace a segment of a signed move list using the supplied local equality. -/
macro "signed_step " n:term:max " with " e:term:max : tactic => `(tactic|
  (refine Eq.trans (signedDg_replaceAt _ _ _ _ _ $n $e
    (by simp [signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [signedChain, Move.bottom, Move.top, List.append_assoc])
    (by simp [Move.bottom, Move.top, KL3.Diagram.Shape.dom, KL3.Diagram.Shape.cod, List.append_assoc])) ?_
   simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
     List.length_cons, List.length_nil, List.nil_append, List.cons_append, List.singleton_append,
     Move.bottom, Move.top, KL3.Diagram.Shape.dom, KL3.Diagram.Shape.cod, List.append_assoc]))

end Categorification.Stendhal.DoubleDiagram
