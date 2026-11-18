/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCrossingCapInduction

/-!
# A black cap over an arbitrary signed word

The sliding-cap block in the spanning argument of Webster,
arXiv:1309.3796v2, §4.5, Lemma 4.28 crosses one black cap leg past the
intervening strands. Equal orientations use a single black crossing, opposite
orientations its three-layer upward mate, and a red strand the actual red/black
crossing. Each contributes exactly one crossing to the filtration.
-/

set_option backward.isDefEq.respectTransparency false
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v
variable {I : Type u} {ℓ : ℕ}

local notation "B" => DoubleStrand I ℓ

/-- Cross a black leg left through one strand in signed boundary order. -/
def crossBlackLeft (L : List B) : B → Letter I → List B → List (SignedLayer I ℓ)
  | .inr r, l, R => [(L, .redBlack r l, R)]
  | .inl (true,i), (true,j), R => [(L, .black (.cross true i j), R)]
  | .inl (false,i), (false,j), R => [(L, .black (.cross false i j), R)]
  | .inl (true,i), (false,j), R => upwardMateLayers L i j R .EF
  | .inl (false,j), (true,i), R => upwardMateLayers L i j R .FE

theorem crossBlackLeft_chain (L : List B) (x : B) (l : Letter I) (R : List B) :
    signedChain (L ++ [x,.inl l] ++ R) (crossBlackLeft L x l R) (L ++ [.inl l,x] ++ R) := by
  cases x with
  | inr => simp [crossBlackLeft, signedChain, Move.bottom, Move.top]
  | inl x =>
    obtain ⟨ε,i⟩ := x; obtain ⟨δ,j⟩ := l
    cases ε <;> cases δ <;> simp [crossBlackLeft, upwardMateLayers, signedChain,
      Move.bottom, Move.top, Shape.dom, Shape.cod, Letter.dual, List.append_assoc]

/-- Move one black strand from the right side of the intervening word to its left. -/
def sweepBlackLeft (L : List B) : List B → Letter I → List B → List (SignedLayer I ℓ)
  | [], _, _ => []
  | x :: S, l, R => sweepBlackLeft (L ++ [x]) S l R ++ crossBlackLeft L x l (S ++ R)

theorem sweepBlackLeft_chain (L S : List B) (l : Letter I) (R : List B) :
    signedChain (L ++ S ++ [.inl l] ++ R) (sweepBlackLeft L S l R) (L ++ [.inl l] ++ S ++ R) := by
  induction S generalizing L with
  | nil => simp [sweepBlackLeft, signedChain]
  | cons x S ih =>
    simpa only [sweepBlackLeft, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
      (ih (L ++ [x])).append (by simpa only [List.append_assoc, List.singleton_append,
        List.cons_append, List.nil_append] using crossBlackLeft_chain L x l (S ++ R))

/-- Sweep the leg through the right subword and then the left subword. -/
theorem sweepBlackLeft_append (L U V : List B) (l : Letter I) (R : List B) :
    sweepBlackLeft L (U ++ V) l R = sweepBlackLeft (L ++ U) V l R ++
      sweepBlackLeft L U l (V ++ R) := by
  induction U generalizing L with
  | nil => simp [sweepBlackLeft]
  | cons x U ih =>
    simp only [List.cons_append, sweepBlackLeft, ih, List.append_assoc, List.nil_append]

/-- Dots on the left leg after the right leg has cleared the intervening word. -/
def capLegDots (L S : List B) (l : Letter I) (R : List B) (d : ℕ) :
    List (SignedLayer I ℓ) :=
  List.replicate d (L, .black (.dot l.dual), .inl l :: (S ++ R))

theorem capLegDots_chain (L S : List B) (l : Letter I) (R : List B) (d : ℕ) :
    signedChain (L ++ [.inl l.dual,.inl l] ++ S ++ R) (capLegDots L S l R d)
      (L ++ [.inl l.dual,.inl l] ++ S ++ R) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [capLegDots, List.replicate_succ] at ih ⊢
    exact ⟨by simp [Move.bottom, Shape.dom, List.append_assoc],
      by simpa only [Move.top, Shape.cod, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append, List.cons_append, List.nil_append] using ih⟩

/-- A dotted black cap over an intervening signed word, with specified exterior contexts. -/
def signedCapBlock (L S : List B) (l : Letter I) (R : List B) (d : ℕ) : List (SignedLayer I ℓ) :=
  sweepBlackLeft (L ++ [.inl l.dual]) S l R ++ capLegDots L S l R d ++ [(L,.black (.cap l),S ++ R)]

/-- Split an intervening word, exposing the sweep through its right segment. -/
theorem signedCapBlock_append (L U V : List B) (l : Letter I) (R : List B) (d : ℕ) :
    signedCapBlock L (U ++ V) l R d =
      sweepBlackLeft ((L ++ [.inl l.dual]) ++ U) V l R ++ signedCapBlock L U l (V ++ R) d := by
  simp only [signedCapBlock, sweepBlackLeft_append, capLegDots, List.append_assoc]

theorem signedCapBlock_chain (L S : List B) (l : Letter I) (R : List B) (d : ℕ) :
    signedChain (L ++ [.inl l.dual] ++ S ++ [.inl l] ++ R) (signedCapBlock L S l R d)
      (L ++ S ++ R) := by
  unfold signedCapBlock
  have h₁ := sweepBlackLeft_chain (L ++ [.inl l.dual]) S l R
  have h₂ := capLegDots_chain L S l R d
  have h₃ : signedChain (L ++ [.inl l.dual,.inl l] ++ S ++ R) [(L,.black (.cap l),S ++ R)]
      (L ++ S ++ R) := by simp [signedChain, Move.top, Move.bottom, List.append_assoc]
  apply signedChain.append _ h₃
  apply signedChain.append h₁
  simpa only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append] using h₂

/-- Crossing count on region-free layers, before applying `signedLayers`. -/
def signedCrossings (ls : List (SignedLayer I ℓ)) := ls.countP fun x => x.2.1.isCrossing

theorem signedCrossings_append (ls ms : List (SignedLayer I ℓ)) :
    signedCrossings (ls ++ ms) = signedCrossings ls + signedCrossings ms := List.countP_append

theorem crossBlackLeft_crossings (L : List B) (x : B) (l : Letter I) (R : List B) :
    signedCrossings (crossBlackLeft L x l R) = 1 := by
  cases x with
  | inr => rfl
  | inl x => obtain ⟨ε,i⟩ := x; obtain ⟨δ,j⟩ := l; cases ε <;> cases δ <;> rfl

theorem sweepBlackLeft_crossings (L S : List B) (l : Letter I) (R : List B) :
    signedCrossings (sweepBlackLeft L S l R) = S.length := by
  induction S generalizing L with
  | nil => rfl
  | cons x S ih => rw [sweepBlackLeft, signedCrossings_append, crossBlackLeft_crossings, ih, List.length_cons]

theorem signedCapBlock_crossings (L S : List B) (l : Letter I) (R : List B) (d : ℕ) :
    signedCrossings (signedCapBlock L S l R d) = S.length := by
  have hd : signedCrossings (capLegDots L S l R d) = 0 := by
    induction d with
    | zero => rfl
    | succ d ih => exact ih
  rw [signedCapBlock, signedCrossings_append, signedCrossings_append, hd, sweepBlackLeft_crossings]
  rfl

variable {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (Λ : Fin ℓ → X) (μ : X)

theorem crossingNumber_of_signedLayers {a b : Obj (signature RD Λ)} (g : a ⟶ b)
    (ls : List (SignedLayer I ℓ)) (hg : Diagram.layers g = signedLayers RD Λ μ ls) :
    crossingNumber g = signedCrossings ls := by
  simp only [crossingNumber, hg, signedLayers, List.countP_map, signedCrossings]
  rfl

end Categorification.Stendhal.DoubleDiagram
