/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBraidBlack
import Categorification.WeightedKLR.RedStrands.DoubleRedCup

/-!
# Passing a signed strand through a black cup

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28. When pushing a cap toward
a preceding cup, a through-strand can cross either leg. The black pitchfork
modulo zero crossings uses the black rectangle for KL III, arXiv:0807.3250v1,
proof of Proposition 3.11. For red the cup mate is exact.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (hP : ∀ r : (pres RD k).Rel, P.lin (blackMirrorLinear RD Λ ((pres RD k).rel r)) = 0)
  (μ : X) (L : List (DoubleStrand I ℓ)) (x : DoubleStrand I ℓ) (l : Letter I)
  (R : List (DoubleStrand I ℓ))
local notation "bl(" b ")" => (Sum.inl b : DoubleStrand I ℓ)
local notation "η" => endWeight RD Λ μ L
local notation "rightWeight" => fun s : List (Letter I) => endWeight RD Λ μ (L ++ blackWord s)

/-- Create a pair on the right of the through-strand, then take its first leg left. -/
def signedCupFromRight : List (SignedLayer I ℓ) :=
  [(L ++ [x], .black (.cup l), R)] ++ crossBlackLeft L x l (bl(l.dual) :: R)

/-- Create a pair on the left of the through-strand, then take its second leg right. -/
def signedCupFromLeft : List (SignedLayer I ℓ) :=
  [(L, .black (.cup l), x :: R)] ++ signedCrossLayers (L ++ [bl(l)]) (bl(l.dual)) x R

theorem signedCupFromRight_chain :
    signedChain (L ++ [x] ++ R) (signedCupFromRight L x l R) (L ++ [bl(l),x,bl(l.dual)] ++ R) := by
  have h := crossBlackLeft_chain L x l (bl(l.dual) :: R)
  simpa only [signedCupFromRight, List.singleton_append, signedChain, Move.bottom, Move.top,
    Shape.dom, Shape.cod, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
    List.nil_append, true_and] using h

theorem signedCupFromLeft_chain :
    signedChain (L ++ [x] ++ R) (signedCupFromLeft L x l R) (L ++ [bl(l),x,bl(l.dual)] ++ R) := by
  have h := signedCrossLayers_chain (L ++ [bl(l)]) (show CanCross (bl(l.dual)) x by cases x <;> trivial) R
  simpa only [signedCupFromLeft, List.singleton_append, signedChain, Move.bottom, Move.top,
    Shape.dom, Shape.cod, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
    List.nil_append, true_and] using h

/-- The straddled red cup is precisely the pitchfork between the two signed
crossing lists, Webster, arXiv:1309.3796v2, §4.5, Definition 4.24. -/
theorem signedCup_red (r : Fin ℓ) :
    let T := addRedCupRelations RD Λ P
    let s := L ++ [.inr r] ++ R
    let t := L ++ [bl(l),.inr r,bl(l.dual)] ++ R
    signedDg RD Λ T μ s t (signedCupFromRight L (.inr r) l R) =
      signedDg RD Λ T μ s t (signedCupFromLeft L (.inr r) l R) := by
  let T := addRedCupRelations RD Λ P
  exact (signedDg_eq_diag_of_layers RD Λ T μ (signedCupFromRight_chain L (.inr r) l R)
    (redCupRight RD Λ μ L l r R) rfl).trans ((redCup_slide RD Λ P μ L l r R).symm.trans
    (signedDg_eq_diag_of_layers RD Λ T μ (signedCupFromLeft_chain L (.inr r) l R)
      (redCupLeft RD Λ μ L l r R) rfl).symm)

include hP

/-- The black pitchfork has a zero-crossing error in a signed exterior word when
the reflected KL III relations hold, by the cup pitchfork in the proof of KL III,
arXiv:0807.3250v1, Proposition 3.11. -/
theorem signedCup_black (m : Letter I) :
    let s := L ++ [bl(m)] ++ R
    let t := L ++ [bl(l),bl(m),bl(l.dual)] ++ R
    signedDg RD Λ P μ s t (signedCupFromRight L (bl(m)) l R) -
        signedDg RD Λ P μ s t (signedCupFromLeft L (bl(m)) l R) ∈
      signedCrossingSpan RD Λ P μ s t 0 := by
  classical
  let s := [m]
  let t := [l.dual,m,l]
  have ht : (rightWeight) t = (rightWeight) s := by
    obtain ⟨_ | _,i⟩ := l <;>
      simp [s,t,blackWord,endWeight,DoubleStrand.weight,Letter.dual,
        add_comm,add_left_comm]
  let F := blackRectangleHom RD Λ μ L R s P hP t rfl ht
  let a := [([], Shape.cup l.dual, [m])] ++ (xLay l m).map (whL [l.dual] [])
  let b := [([m], Shape.cup l.dual, [])] ++ (xLay m l.dual).map (whL [] [l])
  have ha : SChain s a t := by
    exact (show SChain s [([], .cup l.dual,[m])] [l.dual,l,m] by simp [s,SChain,Letter.dual_dual]).append
      (by simpa [t] using (sChain_xLay l m).whisk [l.dual] [])
  have hb : SChain s b t := by
    exact (show SChain s [([m], .cup l.dual,[])] [m,l.dual,l] by simp [s,SChain,Letter.dual_dual]).append
      (by simpa [t] using (sChain_xLay m l.dual).whisk [] [l])
  let D := signedDg RD Λ P μ (L ++ [bl(m)] ++ R) (L ++ [bl(l),bl(m),bl(l.dual)] ++ R)
  have e₁ : F (dg RD k η s t a) = D (signedCupFromRight L (bl(m)) l R) := by
    dsimp only [F]
    rw [dg_of ha, ← Presentation.lin_of, blackRectangleHom_lin, blackLinear_of, Presentation.lin_of]
    symm
    apply signedDg_eq_diag_of_layers RD Λ P μ (signedCupFromRight_chain L (bl(m)) l R)
    rw [layers_blackDiagram_mkD]
    obtain ⟨_ | _,i⟩ := l <;> obtain ⟨_ | _,j⟩ := m <;>
      simp [a, signedCupFromRight, xLay, whL, crosslL, crossrL, signedLayers, crossBlackLeft,
        upwardMateLayers, blackWord, Sig.shape, Letter.dual]
  have e₂ : F (dg RD k η s t b) = D (signedCupFromLeft L (bl(m)) l R) := by
    dsimp only [F]
    rw [dg_of hb, ← Presentation.lin_of, blackRectangleHom_lin, blackLinear_of, Presentation.lin_of]
    symm
    apply signedDg_eq_diag_of_layers RD Λ P μ (signedCupFromLeft_chain L (bl(m)) l R)
    rw [layers_blackDiagram_mkD]
    obtain ⟨_ | _,i⟩ := l <;> obtain ⟨_ | _,j⟩ := m <;>
      simp [b, signedCupFromLeft, xLay, whL, crosslL, crossrL, signedLayers, signedCrossLayers,
        crossBlackLeft, upwardMateLayers, blackWord, Sig.shape, Letter.dual, List.append_assoc]
  have h : dg RD k η s t a - dg RD k η s t b ∈ LeL RD k η s t 0 := by
    obtain ⟨_ | _,i⟩ := l <;> exact cupPF (RD := RD) (k := k) η _ m
  have hh := blackRectangleHom_mem_signedCrossingSpan RD Λ P hP μ L R rfl ht h
  change F (_ - _) ∈ _ at hh
  rw [map_sub, e₁, e₂] at hh
  exact hh

end Categorification.Stendhal.DoubleDiagram
