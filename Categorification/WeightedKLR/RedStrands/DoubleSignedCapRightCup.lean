/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCupPitchfork
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapCup

/-!
# A creating cup at the moving endpoint of a signed cap

Webster, arXiv:1309.3796v2, §4.5, proof of Lemma 4.28. If the right cap
endpoint and an outside survivor are the two legs of a new cup, pass each
intervening strand in turn through the cup. The change at one strand is the
black pitchfork modulo zero crossings, or the exact red cup mate.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (L U : List (DoubleStrand I ℓ)) (l : Letter I) (R : List (DoubleStrand I ℓ))
local notation "bl(" b ")" => (Sum.inl b : DoubleStrand I ℓ)
local notation "Str" => DoubleStrand I ℓ

/-- The cup creating the moving cap endpoint and the strand which survives to its right. -/
def cupRightCapBlock (d : ℕ) : List (SignedLayer I ℓ) :=
  (L ++ [bl(l.dual)] ++ U, .black (.cup l), R) :: signedCapBlock L U l (bl(l.dual) :: R) d

theorem cupRightCapBlock_chain (d : ℕ) :
    signedChain (L ++ [bl(l.dual)] ++ U ++ R) (cupRightCapBlock L U l R d)
      (L ++ U ++ [bl(l.dual)] ++ R) := by
  have h := signedCapBlock_chain L U l (bl(l.dual) :: R) d
  simpa only [cupRightCapBlock,signedChain,Move.bottom,Move.top,Shape.dom,Shape.cod,
    List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append,true_and] using h

/-- The right-hand triangle over an empty interval is a straight dotted strand.
Here the stationary leg is the original strand, so its dots commute below the cup. -/
theorem signedCapBlock_cupRight_nil (d : ℕ) :
    let A := addBlackAdjunctionRelations RD Λ P
    let s := L ++ [bl(l.dual)] ++ R
    signedDg RD Λ A μ s s (cupRightCapBlock L [] l R d) =
      signedDg RD Λ A μ s s (List.replicate d (L, .black (.dot l.dual), R)) := by
  let A := addBlackAdjunctionRelations RD Λ P
  let s := L ++ [bl(l.dual)] ++ R
  let t := L ++ [bl(l.dual),bl(l),bl(l.dual)] ++ R
  let c : SignedLayer I ℓ := (L ++ [bl(l.dual)], .black (.cup l), R)
  let e : SignedLayer I ℓ := (L,.black (.cap l),bl(l.dual) :: R)
  let x : SignedLayer I ℓ := (L,.black (.dot l.dual),R)
  let y : SignedLayer I ℓ := (L,.black (.dot l.dual),bl(l) :: bl(l.dual) :: R)
  have hc : signedChain s [c] t := by simp [s,t,c,signedChain,Move.bottom,Move.top,List.append_assoc]
  have he : signedChain t [e] s := by simp [s,t,e,signedChain,Move.bottom,Move.top,List.append_assoc]
  have hx : signedChain s [x] s := by simp [s,x,signedChain,Move.bottom,Move.top,List.append_assoc]
  have hy : signedChain t [y] t := by simp [t,y,signedChain,Move.bottom,Move.top,List.append_assoc]
  have snake : signedDg RD Λ A μ s s ([c] ++ [e]) = 𝟙 _ := by
    have h := blackSnakeRight_eq RD Λ μ L l.dual R P
    apply Eq.trans _ h
    apply signedDg_eq_diag_of_layers RD Λ A μ (hc.append he)
    simp [c,e,blackSnakeRight,signedLayers,moveDiagram]
  have slide : signedDg RD Λ A μ s s [x] ≫ signedDg RD Λ A μ s t [c] = signedDg RD Λ A μ s t [c] ≫ signedDg RD Λ A μ t t [y] := by
    rw [signedDg_comp RD Λ A μ hx hc, signedDg_comp RD Λ A μ hc hy]
    have h := signedDg_swap RD Λ A μ L [] R (.black (.dot l.dual)) (.black (.cup l))
      (s := s) (t := t) (by simp [s,Move.bottom, List.append_assoc])
      (by simp [t,Move.top,List.append_assoc])
    simpa only [s,t,c,x,y,Move.bottom, Move.top,Shape.dom,Shape.cod,List.map_cons,List.map_nil,
      List.append_nil,List.cons_append,List.nil_append] using h
  have dots (n : ℕ) : signedChain s (List.replicate n x) s := by
    induction n with
    | zero => rfl
    | succ n ih => exact hx.append ih
  have midDots (n : ℕ) : signedChain t (List.replicate n y) t := by
    induction n with
    | zero => rfl
    | succ n ih => exact hy.append ih
  have loop (n : ℕ) : signedChain t (List.replicate n y ++ [e]) s := (midDots n).append he
  have reduced (n : ℕ) : signedDg RD Λ A μ s t [c] ≫ signedDg RD Λ A μ t s (List.replicate n y ++ [e]) = signedDg RD Λ A μ s s (List.replicate n x) := by
    induction n with
    | zero =>
      simp only [List.replicate_zero,List.nil_append]
      rw [signedDg_comp RD Λ A μ hc he, snake, signedDg_nil]
    | succ n ih =>
      rw [show List.replicate (n+1) y ++ [e] = [y] ++ (List.replicate n y ++ [e]) by
        simp [List.replicate_succ], show List.replicate (n+1) x = [x] ++ List.replicate n x by
        simp [List.replicate_succ]]
      rw [← signedDg_comp RD Λ A μ hy (loop n), ← Category.assoc, ← slide, Category.assoc, ih,
        signedDg_comp RD Λ A μ hx (dots n)]
  have h := reduced d
  rw [signedDg_comp RD Λ A μ hc (loop d)] at h
  simpa only [cupRightCapBlock,signedCapBlock,sweepBlackLeft,capLegDots,List.append_nil,List.nil_append,
    List.cons_append,c,e,x,y,s,t] using h

variable (x : DoubleStrand I ℓ)
include x
local notation "pre" => L ++ [bl(l.dual)] ++ U
local notation "src" => pre ++ [x] ++ R
local notation "dst" => (L ++ U) ++ [x,bl(l.dual)] ++ R
local notation "between" => pre ++ [bl(l),x,bl(l.dual)] ++ R
local notation "ev" => signedDg RD Λ P μ
local notation "cross" => signedCrossLayers (L ++ U) (bl(l.dual)) x R

private theorem rightCup_cross_chain :
    signedChain ((L ++ U) ++ [bl(l.dual),x] ++ R) cross dst :=
  signedCrossLayers_chain (L ++ U) (by cases x <;> trivial) R

private theorem rightCup_pull_cross (d : ℕ) :
    ev src dst (signedCupFromLeft pre x l R ++ signedCapBlock L U l (x :: bl(l.dual) :: R) d) =
      ev src dst (cupRightCapBlock L U l (x :: R) d ++ cross) := by
  let a := pre ++ [bl(l),bl(l.dual),x] ++ R
  let c : SignedLayer I ℓ := (pre,.black (.cup l),x :: R)
  have hx : CanCross (bl(l.dual)) x := by cases x <;> trivial
  have h₀ := signedCrossLayers_chain ([] : List Str) hx []
  have h := signedCapBlock_disjointRight RD Λ P μ L U l R h₀ d
  have e₁ : _ = a := show L ++ ([bl(l.dual)] ++ U ++ [bl(l)]) ++
      ([] ++ [bl(l.dual),x] ++ []) ++ R = a by simp [a,List.append_assoc]
  have e₂ : _ = dst := show L ++ U ++ ([] ++ [x,bl(l.dual)] ++ []) ++ R = dst by simp [List.append_assoc]
  rw [e₁,e₂] at h
  let B := signedCrossLayers (pre ++ [bl(l)]) (bl(l.dual)) x R ++
    signedCapBlock L U l (x :: bl(l.dual) :: R) d
  let G := signedCapBlock L U l (bl(l.dual) :: x :: R) d ++ cross
  have eqv : ev a dst B = ev a dst G := by
    simpa only [B,G,signedCrossLayers_whisk,List.append_assoc,List.nil_append,List.append_nil,
      List.cons_append] using h
  have hc : signedChain src [c] a := by simp [c,a,signedChain,Move.bottom,Move.top,Shape.cod,List.append_assoc]
  have hb : signedChain a B dst := by
    have u := signedCrossLayers_chain (pre ++ [bl(l)]) hx R
    have v := signedCapBlock_chain L U l (x :: bl(l.dual) :: R) d
    simp only [List.append_assoc,List.cons_append,List.nil_append] at u v
    simpa only [a,B,List.append_assoc,List.cons_append,List.nil_append] using u.append v
  have hg : signedChain a G dst := by
    have u := signedCapBlock_chain L U l (bl(l.dual) :: x :: R) d
    have v := rightCup_cross_chain L U l R x
    simp only [List.append_assoc,List.cons_append,List.nil_append] at u v
    simpa only [a,G,List.append_assoc,List.cons_append,List.nil_append] using u.append v
  have e := congrArg (fun f => ev src a [c] ≫ f) eqv
  rw [signedDg_comp RD Λ P μ hc hb,signedDg_comp RD Λ P μ hc hg] at e
  simpa only [signedCupFromLeft,cupRightCapBlock,c,B,G,List.append_assoc,List.cons_append,
    List.nil_append] using e

/-- Removing the last letter from the right-hand cup zigzag. A one-crossing
pitchfork error at that letter becomes a strictly lower crossing term after
the remaining cap block. Arbitrary red and black strands can occur in the prefix. -/
theorem signedCapBlock_cupRight_last (d : ℕ)
    (hp : ev src between (signedCupFromRight pre x l R) - ev src between (signedCupFromLeft pre x l R) ∈
      signedCrossingSpan RD Λ P μ src between 0) :
    ev src dst (cupRightCapBlock L (U ++ [x]) l R d) -
        ev src dst (cupRightCapBlock L U l (x :: R) d ++ cross) ∈
      signedCrossingSpan RD Λ P μ src dst U.length := by
  have hb : signedChain between (signedCapBlock L U l (x :: bl(l.dual) :: R) d) dst := by
    simpa only [List.append_assoc,List.nil_append,List.cons_append] using
      signedCapBlock_chain L U l (x :: bl(l.dual) :: R) d
  have h := signedDg_replace_span RD Λ P μ (show signedChain src [] src from rfl)
    (signedCupFromRight_chain pre x l R) (signedCupFromLeft_chain pre x l R) hb hp
  change _ ∈ signedCrossingSpan RD Λ P μ src dst (0 + 0 + signedCrossings _) at h
  rw [signedCapBlock_crossings, Nat.zero_add] at h
  have cut : cupRightCapBlock L (U ++ [x]) l R d =
      signedCupFromRight pre x l R ++ signedCapBlock L U l (x :: bl(l.dual) :: R) d := by
    simp only [cupRightCapBlock,signedCapBlock_append,sweepBlackLeft,signedCupFromRight,
      List.append_assoc,List.nil_append,List.cons_append]
  rw [cut,← rightCup_pull_cross RD Λ P μ L U l R x d]
  exact h

end Categorification.Stendhal.DoubleDiagram
