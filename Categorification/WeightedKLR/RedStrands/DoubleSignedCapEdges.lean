/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCrossingBigon
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBare
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBlockInduction
import Categorification.Diagrams.KL3.SpanningSetBlock

/-!
# Crossing the moving cap leg or both cap legs

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28, and Khovanov–Lauda III,
arXiv:0807.3250v1, proof of Proposition 3.11. A preceding crossing between
the moving leg and the last strand of the cap block makes a bigon. A
crossing of the two legs against an empty block makes a black curl.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X)

local notation "B" => DoubleStrand I ℓ
local notation "S" => signature RD Λ
local notation "bl(" x ")" => (Sum.inl x : B)

/-- Insert a bounded diagram class between two fixed signed move lists. -/
theorem signedDg_mem_span_in_context {s a b t : List B}
    {pre A post : List (SignedLayer I ℓ)} (hp : signedChain s pre a) (hA : signedChain a A b)
    (hq : signedChain b post t) {n : ℕ}
    (hm : signedDg RD Λ P μ a b A ∈ signedCrossingSpan RD Λ P μ a b n) :
    signedDg RD Λ P μ s t (pre ++ A ++ post) ∈
      signedCrossingSpan RD Λ P μ s t (signedCrossings pre + n + signedCrossings post) := by
  let f := Diagram.mk _ (chain_signedLayers RD Λ μ hp)
  let g := Diagram.mk _ (chain_signedLayers RD Λ μ hq)
  have h := signedCrossingSpan_comp RD Λ P μ f g hm
  rw [crossingNumber_of_signedLayers RD Λ μ f pre rfl,
    crossingNumber_of_signedLayers RD Λ μ g post rfl, ← Category.assoc,
    ← signedDg_of RD Λ P μ hp, ← signedDg_of RD Λ P μ hq,
    signedDg_comp RD Λ P μ hp hA, signedDg_comp RD Λ P μ (hp.append hA) hq] at h
  exact h

section Common

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k)

local notation "capP" => signedCapKLPresentation RD Λ P Q exponents t

/-- A preceding crossing against the last strand of the block is a lower
crossing term. It forms a bigon with the first crossing of the sweep. -/
theorem signedCapKL_capBlock_crossLast (L U R : List B) (l : Letter I) (x : B) (d : ℕ) :
    let a := (L ++ [bl(l.dual)] ++ U) ++ [bl(l),x] ++ R
    let b := L ++ (U ++ [x]) ++ R
    signedDg RD Λ (capP) μ a b
        (signedCrossLayers (L ++ [bl(l.dual)] ++ U) bl(l) x R ++ signedCapBlock L (U ++ [x]) l R d) ∈
      signedCrossingSpan RD Λ (capP) μ a b (U.length + 1) := by
  let p := L ++ [bl(l.dual)] ++ U
  let a := p ++ [bl(l),x] ++ R
  let b := L ++ (U ++ [x]) ++ R
  have hcan : CanCross bl(l) x := by cases x <;> trivial
  let rest := signedCapBlock L U l (x :: R) d
  have hr : signedChain a rest b := by
    simpa only [a,b,p,rest,List.append_assoc,List.cons_append,List.nil_append] using
      signedCapBlock_chain L U l (x :: R) d
  have hm := signedCapKL_bigon RD Λ P μ p R Q exponents t bl(l) x hcan
  have hb := signedBigonLayers_chain p R hcan
  have hh := signedDg_mem_span_in_context RD Λ (capP) μ (show signedChain a [] a from rfl) hb hr hm
  have hnum : signedCrossings rest = U.length := signedCapBlock_crossings L U l (x :: R) d
  rw [hnum, show signedCrossings ([] : List (SignedLayer I ℓ)) = 0 from rfl] at hh
  dsimp only
  rw [← signedCapBlock_enterRight]
  simpa only [a, b, p, rest, signedBigonLayers, signedCrossLayers, List.nil_append, List.append_assoc,
    Nat.add_comm, Nat.zero_add] using hh

/-- A crossing of both cap legs is the dotted black curl and has a
zero-crossing expansion. Exterior signed strands are arbitrary. -/
theorem signedCapKL_capBlock_crossBoth (L R : List B) (l : Letter I) (d : ℕ) :
    let a := L ++ [bl(l),bl(l.dual)] ++ R
    signedDg RD Λ (capP) μ a (L ++ [] ++ R)
        (signedCrossLayers L bl(l) bl(l.dual) R ++ signedCapBlock L [] l R d) ∈
      signedCrossingSpan RD Λ (capP) μ a (L ++ [] ++ R) 0 := by
  classical
  let ν := endWeight RD Λ μ L
  let rawSource := [l.dual,l]
  let first := xLay l.dual l
  let tail := rawCapDotRight l.dual d
  let decorated := capBlk [] l.dual d
  have hWeight : endWeight RD Λ μ (L ++ blackWord rawSource) = endWeight RD Λ μ (L ++ blackWord []) := by
    obtain ⟨ε,i⟩ := l
    cases ε <;> simp [rawSource, blackWord, endWeight, DoubleStrand.weight, Letter.dual, add_comm]
  have hf : SChain rawSource first [l,l.dual] := sChain_xLay l.dual l
  have htail : SChain [l,l.dual] tail [] := by
    simpa [tail, Letter.dual_dual] using rawCapDotRight_chain l.dual d
  have hdecor : SChain [l,l.dual] decorated [] := by
    simpa [decorated, Letter.dual_dual] using sChain_capBlk ([] : List (Letter I)) l.dual d
  have he : dg RD k ν rawSource [] (first ++ tail) = dg RD k ν rawSource [] (first ++ decorated) := by
    rw [← dg_comp hf htail, ← dg_comp hf hdecor]
    exact congrArg (fun z => dg RD k ν rawSource [l,l.dual] first ≫ z) (by
      exact dg_rawCapDotRight (k := k) RD ν l d)
  have hm : dg RD k ν rawSource [] (first ++ tail) ∈ LeL RD k ν rawSource [] 0 := by
    rw [he]
    have h := capBlk_AB (RD := RD) (k := k) ν l.dual d
    rw [show [l.dual,l.dual.dual] = rawSource by simp [rawSource, Letter.dual_dual]] at h
    simpa only [first,decorated,Letter.dual_dual] using h
  let hP := signedCapKL_reflectedBlack RD Λ P Q exponents t
  have h := blackRectangleHom_mem_signedCrossingSpan RD Λ (capP) hP μ L R hWeight rfl hm
  rw [blackRectangleHom_dg RD Λ (capP) hP μ L R hWeight rfl (hf.append htail)] at h
  let a := L ++ [bl(l),bl(l.dual)] ++ R
  have hc : signedChain a (signedCrossLayers L bl(l) bl(l.dual) R ++ signedCapBlock L [] l R d)
      (L ++ [] ++ R) := by
    refine (signedCrossLayers_chain L (show CanCross bl(l) bl(l.dual) from trivial) R).append ?_
    simpa [List.append_assoc] using signedCapBlock_chain L [] l R d
  dsimp only
  rw [signedDg_eq_diag_of_layers RD Λ (capP) μ hc (blackDiagram RD Λ μ L R (mkD RD ν _ (hf.append htail)))]
  · exact h
  · rw [layers_blackDiagram_mkD]
    obtain ⟨ε,i⟩ := l
    cases ε <;> simp [first, tail, xLay, crosslL, crossrL, signedCrossLayers, crossBlackLeft,
      upwardMateLayers, rawCapDotRight, signedCapBlock, sweepBlackLeft, capLegDots,
      signedLayers, Sig.shape, blackWord, Letter.dual, List.map_replicate]

end Common

end Categorification.Stendhal.DoubleDiagram
