/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBraidBlack
import Categorification.WeightedKLR.RedStrands.DoubleCapPresentation
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapDot

/-!
# Moving a black dot through a crossing of the cap sweep

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, using KL III Proposition 3.11.
For two black strands, the dot crosses modulo a term with no crossings, including
the equal-colour nilHecke correction. The signed exterior context is arbitrary.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (L R : List (DoubleStrand I ℓ))

/-- A single dot at a specified black strand in physical order. -/
def capSweepDot (L : List (DoubleStrand I ℓ)) (l : Letter I) (R : List (DoubleStrand I ℓ)) :
    List (SignedLayer I ℓ) := [(L,.black (.dot l),R)]

theorem capSweepDot_chain (L : List (DoubleStrand I ℓ)) (l : Letter I) (R : List (DoubleStrand I ℓ)) :
    signedChain (L ++ [.inl l] ++ R) (capSweepDot L l R) (L ++ [.inl l] ++ R) := ⟨rfl,rfl⟩

local notation "η" => endWeight RD Λ μ L
local notation "W" => fun s : List (Letter I) => endWeight RD Λ μ (L ++ blackWord s)

private theorem rectangle_dg {s t : List (Letter I)} {A : List (LayerData I)} (hA : SChain s A t)
    (hP : ∀ j : (pres RD k).Rel, P.lin (blackMirrorLinear RD Λ ((pres RD k).rel j)) = 0)
    (ht : (W) t = (W) s) {B : List (SignedLayer I ℓ)}
    (hB : signedChain (L ++ blackWord s ++ R) B (L ++ blackWord t ++ R))
    (he : A.map (fun x => layer RD Λ μ (L ++ blackWord x.2.2) (.black (Sig.shape x.2.1))
      (blackWord x.1 ++ R)) = signedLayers RD Λ μ B) :
    blackRectangleHom RD Λ μ L R s P hP t rfl ht (dg RD k η s t A) =
      signedDg RD Λ P μ (L ++ blackWord s ++ R) (L ++ blackWord t ++ R) B := by
  rw [dg_of hA, ← Presentation.lin_of, blackRectangleHom_lin, blackLinear_of, Presentation.lin_of]
  symm
  exact signedDg_eq_diag_of_layers RD Λ P μ hB _ ((layers_blackDiagram_mkD RD Λ μ L R A hA).trans he)

local notation "bx" => (Sum.inl (α := Letter I) (β := Fin ℓ))

/-- A dot on either leg crosses a black–black crossing modulo diagrams with no crossings. -/
theorem capSweepDot_cross_black
    (hP : ∀ j : (pres RD k).Rel, P.lin (blackMirrorLinear RD Λ ((pres RD k).rel j)) = 0)
    (x l : Letter I) (swept : Bool) :
    signedDg RD Λ P μ (L ++ [bx x,bx l] ++ R) (L ++ [bx l,bx x] ++ R)
      ((if swept then capSweepDot (L ++ [bx x]) l R else capSweepDot L x (bx l :: R)) ++
        crossBlackLeft L (bx x) l R) -
    signedDg RD Λ P μ (L ++ [bx x,bx l] ++ R) (L ++ [bx l,bx x] ++ R)
      (crossBlackLeft L (bx x) l R ++
        (if swept then capSweepDot L l (bx x :: R) else capSweepDot (L ++ [bx l]) x R)) ∈
      signedCrossingSpan RD Λ P μ (L ++ [bx x,bx l] ++ R) (L ++ [bx l,bx x] ++ R) 0 := by
  classical
  have ht : (W) [x,l] = (W) [l,x] := by simp [blackWord,endWeight,add_comm]
  let low : List (LayerData I) := if swept then [([], .dot l, [x])] else [([l], .dot x, [])]
  let high : List (LayerData I) := if swept then [([x], .dot l, [])] else [([], .dot x, [l])]
  have mod : dg RD k η [l,x] [x,l] (xLay l x ++ high) -
      dg RD k η [l,x] [x,l] (low ++ xLay l x) ∈ LeL RD k η [l,x] [x,l] 0 := by
    cases swept
    · exact ds0 η l x
    · exact ds1 η l x
  have h := blackRectangleHom_mem_signedCrossingSpan RD Λ P hP μ L R rfl ht mod
  rw [map_sub] at h
  let below := if swept then capSweepDot (L ++ [bx x]) l R else capSweepDot L x (bx l :: R)
  let above := if swept then capSweepDot L l (bx x :: R) else capSweepDot (L ++ [bx l]) x R
  let cross := crossBlackLeft L (bx x) l R
  have source : blackWord (ℓ := ℓ) [l,x] = [bx x,bx l] := rfl
  have target : blackWord (ℓ := ℓ) [x,l] = [bx l,bx x] := rfl
  have chain := crossBlackLeft_chain L (bx x) l R
  have hbelow : signedChain (L ++ [bx x,bx l] ++ R) below (L ++ [bx x,bx l] ++ R) := by
    cases swept <;> simp [below,capSweepDot,signedChain,Move.bottom,Move.top,Shape.dom,Shape.cod,List.append_assoc]
  have habove : signedChain (L ++ [bx l,bx x] ++ R) above (L ++ [bx l,bx x] ++ R) := by
    cases swept <;> simp [above,capSweepDot,signedChain,Move.bottom,Move.top,Shape.dom,Shape.cod,List.append_assoc]
  have hlow : SChain [l,x] low [l,x] := by cases swept <;> exact ⟨rfl,rfl⟩
  have hhigh : SChain [x,l] high [x,l] := by cases swept <;> exact ⟨rfl,rfl⟩
  have e₁ := rectangle_dg RD Λ P μ L R (hlow.append (sChain_xLay l x)) hP ht
    (B := below ++ cross) (hbelow.append chain) (by
      obtain ⟨a,i⟩ := x; obtain ⟨b,j⟩ := l
      cases swept <;> cases a <;> cases b <;> simp [low,below,cross,capSweepDot,xLay,crosslL,crossrL,
        crossBlackLeft,upwardMateLayers,signedLayers,blackWord,Sig.shape])
  have e₂ := rectangle_dg RD Λ P μ L R ((sChain_xLay l x).append hhigh) hP ht
    (B := cross ++ above) (chain.append habove) (by
      obtain ⟨a,i⟩ := x; obtain ⟨b,j⟩ := l
      cases swept <;> cases a <;> cases b <;> simp [high,above,cross,capSweepDot,xLay,crosslL,crossrL,
        crossBlackLeft,upwardMateLayers,signedLayers,blackWord,Sig.shape])
  rw [e₁, e₂] at h
  rw [source, target] at h
  simpa only [neg_sub] using Submodule.neg_mem _ h

section Red

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) (t : I → I → k)
local notation "mates" => addRedCapRelations RD Λ (addRedCupRelations RD Λ P)
local notation "slides" => addRedUpSlideRelations RD Λ (mates)
local notation "inverse" => addRedUpRelations RD Λ k (slides)
local notation "mixed" => addMixedCupPitchforkRelations RD Λ (inverse) t
local notation "adj" => addBlackAdjunctionRelations RD Λ (mixed)
local notation "braidP" => signedCapBraidPresentation RD Λ P Q exponents t
local notation "finalP" => signedCapKLPresentation RD Λ P Q exponents t

private theorem redDotRaw (r : Fin ℓ) (l : Letter I) :
    signedDg RD Λ (braidP) μ (L ++ [.inr r,bx l] ++ R) (L ++ [bx l,.inr r] ++ R)
      (capSweepDot (L ++ [.inr r]) l R ++ crossBlackLeft L (.inr r) l R) =
    signedDg RD Λ (braidP) μ (L ++ [.inr r,bx l] ++ R) (L ++ [bx l,.inr r] ++ R)
      (crossBlackLeft L (.inr r) l R ++ capSweepDot L l (.inr r :: R)) := by
  have c₁ : signedChain (L ++ [.inr r,bx l] ++ R)
      (capSweepDot (L ++ [.inr r]) l R ++ crossBlackLeft L (.inr r) l R) (L ++ [bx l,.inr r] ++ R) := by
    simp [capSweepDot,crossBlackLeft,signedChain,Move.top,Move.bottom,Shape.dom,Shape.cod,List.append_assoc]
  have c₂ : signedChain (L ++ [.inr r,bx l] ++ R)
      (crossBlackLeft L (.inr r) l R ++ capSweepDot L l (.inr r :: R)) (L ++ [bx l,.inr r] ++ R) := by
    simp [capSweepDot,crossBlackLeft,signedChain,Move.top,Move.bottom,Shape.dom,Shape.cod,List.append_assoc]
  obtain ⟨b,i⟩ := l
  cases b
  · have e := (redDown_dot_slide_redLeft RD Λ Q exponents (adj) μ L r i R).symm
    rw [← Presentation.diag_comp, ← Presentation.diag_comp] at e
    refine (signedDg_eq_diag_of_layers RD Λ (braidP) μ c₁ _ ?_).trans
      (e.trans (signedDg_eq_diag_of_layers RD Λ (braidP) μ c₂ _ ?_).symm)
    all_goals rfl
  · have h := redUp_slide RD Λ (mates) μ L r (.dot i) R
    have e : (braidP).diag _ = (braidP).diag _ := diag_eq_addRels (adj) (diag_eq_addRels (mixed)
      (diag_eq_addRels (inverse) (diag_eq_addRels (slides) h)))
    let es : obj RD Λ μ (L ++ [.inr r] ++ upBlackWord [i] ++ R) =
        obj RD Λ μ (L ++ [.inr r,bx (up i)] ++ R) := by simp [upBlackWord,List.append_assoc]
    let et : obj RD Λ μ (L ++ upBlackWord [i] ++ [.inr r] ++ R) =
        obj RD Λ μ (L ++ [bx (up i),.inr r] ++ R) := by simp [upBlackWord,List.append_assoc]
    have ee := congrArg ((braidP).castHom es et) e
    rw [Presentation.castHom_diag, Presentation.castHom_diag] at ee
    refine (signedDg_eq_diag_of_layers RD Λ (braidP) μ c₁ _ ?_).trans
      (ee.trans (signedDg_eq_diag_of_layers RD Λ (braidP) μ c₂ _ ?_).symm)
    all_goals simp [redUpSlide,redThroughUpWord,upBlackWord,upBlackMoveDiagram,
      UpBlackMove.shape,
      capSweepDot,crossBlackLeft,signedLayers,moveDiagram]

/-- The moving-leg dot crosses one arbitrary signed strand modulo crossing-free terms.
Across red the two dot positions agree exactly. -/
theorem capSweepDot_cross_moving (x : DoubleStrand I ℓ) (l : Letter I) :
    signedDg RD Λ (finalP) μ (L ++ [x,bx l] ++ R) (L ++ [bx l,x] ++ R)
      (capSweepDot (L ++ [x]) l R ++ crossBlackLeft L x l R) -
    signedDg RD Λ (finalP) μ (L ++ [x,bx l] ++ R) (L ++ [bx l,x] ++ R)
      (crossBlackLeft L x l R ++ capSweepDot L l (x :: R)) ∈
      signedCrossingSpan RD Λ (finalP) μ (L ++ [x,bx l] ++ R) (L ++ [bx l,x] ++ R) 0 := by
  cases x with
  | inl a => exact capSweepDot_cross_black RD Λ (finalP) μ L R (signedCapKL_reflectedBlack RD Λ P Q exponents t) a l true
  | inr r =>
    have h := signedDg_eq_of_ideal_le RD Λ (braidP) (finalP) (fun a b =>
      (signedCapBraid_ideal_le RD Λ P Q exponents t a b).trans (signedCap_ideal_le_KL RD Λ P Q exponents t a b))
      μ _ _ (redDotRaw RD Λ P μ L R Q exponents t r l)
    rw [h, sub_self]
    exact Submodule.zero_mem _

end Red

end Categorification.Stendhal.DoubleDiagram
