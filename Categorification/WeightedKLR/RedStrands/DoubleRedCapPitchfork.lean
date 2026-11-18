/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapPitchfork
import Categorification.WeightedKLR.RedStrands.DoubleCapPresentation

/-!
# The dotted cap pitchfork through a red strand

Webster, arXiv:1309.3796v2, §4.5, Definition 4.24 and the counit mate equation
in the proof of Theorem 4.25. In the cap sweep of Lemma 4.28, the same dots
on the left cap leg can be brought below either red crossing. They pass
through one crossing by red dot naturality and through the other by
interchange.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k]

private theorem replicate_layer_chain {s : List (DoubleStrand I ℓ)} {q : SignedLayer I ℓ}
    (h : signedChain s [q] s) (n : ℕ) : signedChain s (List.replicate n q) s := by
  induction n with
  | zero => rfl
  | succ n ih => exact h.append ih

private theorem capPitch_moveDots (T : Presentation.{w,max u v} (signature RD Λ) k) (μ : X)
    {s t z : List (DoubleStrand I ℓ)} {g cap p q : SignedLayer I ℓ}
    (hg : signedChain s [g] t) (hc : signedChain t [cap] z)
    (hp : signedChain s [p] s) (hq : signedChain t [q] t)
    (he : signedDg RD Λ T μ s t [g,q] = signedDg RD Λ T μ s t [p,g]) (n : ℕ) :
    signedDg RD Λ T μ s z ([g] ++ List.replicate n q ++ [cap]) =
      signedDg RD Λ T μ s s (List.replicate n p) ≫ signedDg RD Λ T μ s z [g,cap] := by
  induction n with
  | zero => simp [signedDg_nil]
  | succ n ih =>
    have ht := (replicate_layer_chain hq n).append hc
    calc
      _ = signedDg RD Λ T μ s t [g,q] ≫ signedDg RD Λ T μ t z (List.replicate n q ++ [cap]) := by
        exact (signedDg_comp RD Λ T μ (hg.append hq) ht).symm
      _ = signedDg RD Λ T μ s t [p,g] ≫ signedDg RD Λ T μ t z (List.replicate n q ++ [cap]) := by rw [he]
      _ = signedDg RD Λ T μ s s [p] ≫ signedDg RD Λ T μ s z ([g] ++ List.replicate n q ++ [cap]) := by
        have he' : signedDg RD Λ T μ s s [p] ≫ signedDg RD Λ T μ s t [g] =
            signedDg RD Λ T μ s t [p,g] := signedDg_comp RD Λ T μ hp hg
        rw [← he', Category.assoc]
        exact congrArg (_ ≫ ·) (signedDg_comp RD Λ T μ hg ht)
      _ = _ := by
        rw [ih, ← Category.assoc, signedDg_comp RD Λ T μ hp (replicate_layer_chain hp n)]
        rfl

variable (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (L : List (DoubleStrand I ℓ)) (l : Letter I) (R : List (DoubleStrand I ℓ))
  (d : ℕ) (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (t : I → I → k) (r : Fin ℓ)

local notation "B" => DoubleStrand I ℓ
local notation "bl(" x ")" => (Sum.inl x : B)
local notation "red" => (Sum.inr r : B)
local notation "braidP" => signedCapBraidPresentation RD Λ P Q exponents t
local notation "capP" => signedCapPassPresentation RD Λ P Q exponents
local notation "A" => signedCapKLPresentation RD Λ P Q exponents t

local notation "mates" => addRedCapRelations RD Λ (addRedCupRelations RD Λ P)
local notation "slides" => addRedUpSlideRelations RD Λ (mates)
local notation "inverse" => addRedUpRelations RD Λ k (slides)
local notation "mixed" => addMixedCupPitchforkRelations RD Λ (inverse) t
local notation "adj" => addBlackAdjunctionRelations RD Λ (mixed)

private theorem redDot_blackLeft (x : Letter I) :
    signedDg RD Λ (braidP) μ (L ++ [bl(x),red] ++ R) (L ++ [red,bl(x)] ++ R)
      [(L, .blackRed x r, R), (L ++ [red], .black (.dot x), R)] =
    signedDg RD Λ (braidP) μ (L ++ [bl(x),red] ++ R) (L ++ [red,bl(x)] ++ R)
      [(L, .black (.dot x), red :: R), (L, .blackRed x r, R)] := by
  have c₁ : signedChain (L ++ [bl(x),red] ++ R)
      [(L, .blackRed x r, R), (L ++ [red], .black (.dot x), R)] (L ++ [red,bl(x)] ++ R) := by
    simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]
  have c₂ : signedChain (L ++ [bl(x),red] ++ R)
      [(L, .black (.dot x), red :: R), (L, .blackRed x r, R)] (L ++ [red,bl(x)] ++ R) := by
    simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod, List.append_assoc]
  obtain ⟨b,i⟩ := x
  cases b
  · have e := redDown_dot_slide_blackLeft RD Λ Q exponents (adj) μ L r i R
    rw [← Presentation.diag_comp, ← Presentation.diag_comp] at e
    exact (signedDg_eq_diag_of_layers RD Λ (braidP) μ c₁ _ rfl).trans
      (e.trans (signedDg_eq_diag_of_layers RD Λ (braidP) μ c₂ _ rfl).symm)
  · have h := (redUp_slide_mirror RD Λ (mates) μ L r (.dot i) R).symm
    have e : (braidP).diag _ = (braidP).diag _ := diag_eq_addRels (adj) (diag_eq_addRels (mixed)
      (diag_eq_addRels (inverse) (diag_eq_addRels (slides) h)))
    let es : obj RD Λ μ (L ++ upBlackWord [i] ++ [red] ++ R) =
        obj RD Λ μ (L ++ [bl(up i),red] ++ R) := by simp [upBlackWord,List.append_assoc]
    let et : obj RD Λ μ (L ++ [red] ++ upBlackWord [i] ++ R) =
        obj RD Λ μ (L ++ [red,bl(up i)] ++ R) := by simp [upBlackWord,List.append_assoc]
    have ee := congrArg ((braidP).castHom es et) e
    rw [Presentation.castHom_diag, Presentation.castHom_diag] at ee
    refine (signedDg_eq_diag_of_layers RD Λ (braidP) μ c₁ _ ?_).trans
      (ee.trans (signedDg_eq_diag_of_layers RD Λ (braidP) μ c₂ _ ?_).symm)
    all_goals simp [redUpSlideMirror,upWordThroughRed,upBlackWord,upBlackMoveDiagram,
      UpBlackMove.shape,signedLayers,moveDiagram]

local notation "blA" => bl(l.dual)
local notation "blB" => bl(l)
local notation "source" => L ++ [blA,red,blB] ++ R
local notation "middleL" => L ++ [red,blA,blB] ++ R
local notation "middleR" => L ++ [blA,blB,red] ++ R
local notation "target" => L ++ [red] ++ R
local notation "crossL" => ((L, Move.blackRed l.dual r, blB :: R) : SignedLayer I ℓ)
local notation "crossR" => ((L ++ [blA], Move.redBlack r l, R) : SignedLayer I ℓ)
local notation "capL" => ((L ++ [red], Move.black (Shape.cap l), R) : SignedLayer I ℓ)
local notation "capR" => ((L, Move.black (Shape.cap l), red :: R) : SignedLayer I ℓ)
local notation "dot0" => ((L, Move.black (Shape.dot l.dual), red :: blB :: R) : SignedLayer I ℓ)
local notation "dotL" => ((L ++ [red], Move.black (Shape.dot l.dual), blB :: R) : SignedLayer I ℓ)
local notation "dotR" => ((L, Move.black (Shape.dot l.dual), blB :: red :: R) : SignedLayer I ℓ)
local notation "D" => signedDg RD Λ (A) μ

private theorem redCap_base : D source target [crossL,capL] = D source target [crossR,capR] := by
  let P₀ := addDownRelations RD Λ (affineCoverQ Q exponents) (addRedUpRelations RD Λ k P)
  have h := (redCap_slide RD Λ P₀ μ L l r R).symm
  let F := (capP).extension (A) (fun a b =>
    (signedCapPass_ideal_le RD Λ P Q exponents t a b).trans (signedCap_ideal_le_KL RD Λ P Q exponents t a b))
  have e : (A).diag (redCapRight RD Λ μ L l r R) = (A).diag (redCapLeft RD Λ μ L l r R) :=
    congrArg F.map h
  have hc₁ : signedChain source [crossL,capL] target := by
    simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod,List.append_assoc]
  have hc₂ : signedChain source [crossR,capR] target := by
    simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod,List.append_assoc]
  exact (signedDg_eq_diag_of_layers RD Λ (A) μ hc₁ _ rfl).trans
    (e.trans (signedDg_eq_diag_of_layers RD Λ (A) μ hc₂ _ rfl).symm)

/-- The dotted cap can take the red strand past either leg. The dot count
on the physical left cap leg agrees on both paths. -/
theorem signedCapPitch_red :
    D source target (signedCapPitchLeft L red l R d) =
      D source target (signedCapPitchRight L red l R d) := by
  have hL : signedChain source [crossL] middleL := by
    simp [signedChain, Move.bottom, Move.top, List.append_assoc]
  have hR : signedChain source [crossR] middleR := by
    simp [signedChain, Move.bottom, Move.top, List.append_assoc]
  have cL : signedChain middleL [capL] target := by
    simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod,List.append_assoc]
  have cR : signedChain middleR [capR] target := by
    simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod,List.append_assoc]
  have p : signedChain source [dot0] source := by
    simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod,List.append_assoc]
  have qL : signedChain middleL [dotL] middleL := by
    simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod,List.append_assoc]
  have qR : signedChain middleR [dotR] middleR := by
    simp [signedChain, Move.bottom, Move.top, Shape.dom, Shape.cod,List.append_assoc]
  have eL : D source middleL [crossL,dotL] = D source middleL [dot0,crossL] := by
    have h := redDot_blackLeft RD Λ P μ L (blB :: R) Q exponents t r l.dual
    rw [show L ++ [blA,red] ++ blB :: R = source by simp [List.append_assoc],
      show L ++ [red,blA] ++ blB :: R = middleL by simp [List.append_assoc]] at h
    exact signedDg_eq_of_ideal_le RD Λ (braidP) (A) (fun a b =>
      (signedCapBraid_ideal_le RD Λ P Q exponents t a b).trans (signedCap_ideal_le_KL RD Λ P Q exponents t a b))
      μ source middleL h
  have eR : D source middleR [crossR,dotR] = D source middleR [dot0,crossR] := by
    have he := signedDg_swap RD Λ (A) μ L [] R (.black (.dot l.dual)) (.redBlack r l)
      (s := source) (t := middleR)
      (by simp [Move.bottom,Shape.dom,List.append_assoc])
      (by simp [Move.top,Shape.cod,List.append_assoc])
    simpa [Move.bottom,Move.top,Shape.dom,Shape.cod,List.append_assoc] using he.symm
  have h := congrArg (fun f => D source source (List.replicate d dot0) ≫ f)
    (redCap_base RD Λ P μ L l R Q exponents t r)
  have nl := capPitch_moveDots RD Λ (A) μ hL cL p qL eL d
  have nr := capPitch_moveDots RD Λ (A) μ hR cR p qR eR d
  simpa [signedCapPitchLeft,signedCapPitchRight,signedCrossLayers,crossBlackLeft,
    signedCapBlock,sweepBlackLeft,capLegDots,List.append_assoc] using nl.trans (h.trans nr.symm)

end Categorification.Stendhal.DoubleDiagram
