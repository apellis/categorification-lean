/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapInterleave

/-!
# Sliding a dot onto the stationary cap leg

For the dot position on the stationary leg of the cap block in the KL
spanning argument used by Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28,
the entire sweep is disjoint from the dot. Interchange moves the dot onto
the cap, incrementing its decoration even when the interior contains red
strands and sideways black crossings.
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

private theorem bareCap_chain (d : ℕ) :
    signedChain ([Sum.inl l.dual] ++ U ++ [Sum.inl l]) (signedCapBlock [] U l [] d) U := by
  simpa only [List.nil_append, List.append_nil] using signedCapBlock_chain [] U l [] d

/-- An arbitrary signed block on the left commutes from below the cap to above it. -/
theorem signedCapBlock_disjointLeft {a b : List (DoubleStrand I ℓ)} {F : List (SignedLayer I ℓ)}
    (hF : signedChain a F b) (d : ℕ) :
    signedDg RD Λ P μ (L ++ a ++ ([.inl l.dual] ++ U ++ [.inl l]) ++ R) (L ++ b ++ U ++ R)
      (signedWhisk L (([.inl l.dual] ++ U ++ [.inl l]) ++ R) F ++ signedCapBlock (L ++ b) U l R d) =
    signedDg RD Λ P μ (L ++ a ++ ([.inl l.dual] ++ U ++ [.inl l]) ++ R) (L ++ b ++ U ++ R)
      (signedCapBlock (L ++ a) U l R d ++ signedWhisk L (U ++ R) F) := by
  simpa only [signedCapBlock_whisk, List.append_nil, List.nil_append] using
    signedDg_interchange RD Λ P μ L R hF (bareCap_chain U l d)

/-- The same commutation with the moving signed block on the right. -/
theorem signedCapBlock_disjointRight {a b : List (DoubleStrand I ℓ)} {F : List (SignedLayer I ℓ)}
    (hF : signedChain a F b) (d : ℕ) :
    signedDg RD Λ P μ (L ++ ([.inl l.dual] ++ U ++ [.inl l]) ++ a ++ R) (L ++ U ++ b ++ R)
      (signedWhisk (L ++ ([.inl l.dual] ++ U ++ [.inl l])) R F ++ signedCapBlock L U l (b ++ R) d) =
    signedDg RD Λ P μ (L ++ ([.inl l.dual] ++ U ++ [.inl l]) ++ a ++ R) (L ++ U ++ b ++ R)
      (signedCapBlock L U l (a ++ R) d ++ signedWhisk (L ++ U) R F) := by
  simpa only [signedCapBlock_whisk, List.append_nil, List.nil_append] using
    (signedDg_interchange RD Λ P μ L R (bareCap_chain U l d) hF).symm

/-- A dot on the stationary leg of a cap with arbitrary intervening strands
becomes an additional dot on the cap. -/
theorem signedCapBlock_dotLeft (d : ℕ) :
    signedDg RD Λ P μ (L ++ [.inl l.dual] ++ U ++ [.inl l] ++ R) (L ++ U ++ R)
      ((L, .black (.dot l.dual), U ++ [.inl l] ++ R) :: signedCapBlock L U l R d) =
    signedDg RD Λ P μ (L ++ [.inl l.dual] ++ U ++ [.inl l] ++ R) (L ++ U ++ R)
      (signedCapBlock L U l R (d+1)) := by
  let a := L ++ [.inl l.dual] ++ U ++ [.inl l] ++ R
  let b := L ++ [.inl l.dual,.inl l] ++ U ++ R
  let sw := sweepBlackLeft (L ++ [.inl l.dual]) U l R
  let A : SignedLayer I ℓ := (L, .black (.dot l.dual), U ++ [.inl l] ++ R)
  let B : SignedLayer I ℓ := (L, .black (.dot l.dual), .inl l :: (U ++ R))
  let tail := capLegDots L U l R d ++ [(L, .black (.cap l), U ++ R)]
  have hd : signedChain (ℓ := ℓ) [.inl l.dual] [([], .black (.dot l.dual), [])] [.inl l.dual] := by
    simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod]
  have hs := sweepBlackLeft_chain ([] : List (DoubleStrand I ℓ)) U l []
  have ex : signedDg RD Λ P μ a b ([A] ++ sw) = signedDg RD Λ P μ a b (sw ++ [B]) := by
    have eqv := signedDg_interchange RD Λ P μ L R hd hs
    have e₁ : L ++ [.inl l.dual] ++ ([] ++ U ++ [.inl l] ++ []) ++ R = a := by
      simp [a, List.append_assoc]
    have e₂ : L ++ [.inl l.dual] ++ ([] ++ [.inl l] ++ U ++ []) ++ R = b := by
      simp [b, List.append_assoc]
    rw [e₁,e₂] at eqv
    simp only [sweepBlackLeft_whisk] at eqv
    simpa only [signedWhisk, List.map_cons, List.map_nil, List.nil_append, List.append_nil,
      List.append_assoc, List.cons_append, sw, A, B] using eqv
  have hs' : signedChain a sw b := by
    have he : (L ++ [.inl l.dual]) ++ [.inl l] ++ U ++ R = b := by simp [b,List.append_assoc]
    rw [← he]
    exact sweepBlackLeft_chain (L ++ [.inl l.dual]) U l R
  have hA : signedChain a [A] a := by
    simp [signedChain, a, A, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]
  have hB : signedChain b [B] b := by
    simp [signedChain, b, B, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]
  have ht : signedChain b tail (L ++ U ++ R) :=
    (capLegDots_chain L U l R d).append (by simp [signedChain, Move.bottom, Move.top, Shape.dom,
      Shape.cod, List.append_assoc])
  have h := congrArg (fun f => f ≫ signedDg RD Λ P μ b (L ++ U ++ R) tail) ex
  rw [signedDg_comp RD Λ P μ (hA.append hs') ht, signedDg_comp RD Λ P μ (hs'.append hB) ht] at h
  simpa only [a,b,A,B,sw,tail,signedCapBlock,capLegDots,List.replicate_succ,List.append_assoc,
    List.cons_append,List.nil_append] using h

end Categorification.Stendhal.DoubleDiagram
