/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapEdges
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapPitchfork

/-!
# Crossing the stationary end of a signed cap block

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28, and Khovanov–Lauda III,
arXiv:0807.3250v1, proof of Proposition 3.11. Interchange first moves the
crossing of the two left strands past the tail of the cap sweep. The
remaining local step is a dotted cap pitchfork. In the first-strand
position the two left crossings then form a removable bigon.
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
local notation "bl(" x ")" => (Sum.inl x : B)

/-- Commute a crossing of two left strands with the sweep to their right. -/
private theorem crossing_sweep_interchange (L U R : List B) (x y : B) (l : Letter I)
    (hxy : CanCross x y) {t : List B} {post : List (SignedLayer I ℓ)}
    (hpost : signedChain (L ++ [y,x,bl(l)] ++ (U ++ R)) post t) :
    let s := L ++ [x,y] ++ U ++ [bl(l)] ++ R
    signedDg RD Λ P μ s t (signedCrossLayers L x y (U ++ [bl(l)] ++ R) ++
        sweepBlackLeft (L ++ [y,x]) U l R ++ post) =
      signedDg RD Λ P μ s t (sweepBlackLeft (L ++ [x,y]) U l R ++
        signedCrossLayers L x y (bl(l) :: (U ++ R)) ++ post) := by
  let s := L ++ [x,y] ++ U ++ [bl(l)] ++ R
  let b := L ++ [y,x,bl(l)] ++ (U ++ R)
  let F := signedCrossLayers L x y (U ++ [bl(l)] ++ R) ++ sweepBlackLeft (L ++ [y,x]) U l R
  let G := sweepBlackLeft (L ++ [x,y]) U l R ++ signedCrossLayers L x y (bl(l) :: (U ++ R))
  have he : signedDg RD Λ P μ s b F = signedDg RD Λ P μ s b G := by
    have h := signedDg_interchange RD Λ P μ L R (signedCrossLayers_chain [] hxy [])
      (sweepBlackLeft_chain [] U l [])
    have es : L ++ ([] ++ [x,y] ++ []) ++ ([] ++ U ++ [bl(l)] ++ []) ++ R = s := by simp [s,List.append_assoc]
    have et : L ++ ([] ++ [y,x] ++ []) ++ ([] ++ [bl(l)] ++ U ++ []) ++ R = b := by simp [b,List.append_assoc]
    rw [es,et] at h
    simpa only [F,G,signedCrossLayers_whisk,sweepBlackLeft_whisk,List.append_assoc,List.cons_append,
      List.nil_append,List.append_nil] using h
  have hF : signedChain s F b := by
    have e₁ := signedCrossLayers_chain L hxy (U ++ [bl(l)] ++ R)
    have e₂ := sweepBlackLeft_chain (L ++ [y,x]) U l R
    simp only [s,b,F,List.append_assoc,List.cons_append,List.nil_append] at e₁ e₂ ⊢
    exact e₁.append e₂
  have hG : signedChain s G b := by
    have e₁ := sweepBlackLeft_chain (L ++ [x,y]) U l R
    have e₂ := signedCrossLayers_chain L hxy (bl(l) :: (U ++ R))
    simp only [s,b,G,List.append_assoc,List.cons_append,List.nil_append] at e₁ e₂ ⊢
    exact e₁.append e₂
  have h := congrArg (fun f => f ≫ signedDg RD Λ P μ b t post) he
  rw [signedDg_comp RD Λ P μ hF hpost, signedDg_comp RD Λ P μ hG hpost] at h
  exact h

/-- The left entrance extends the cap block by the incoming strand. The
error is the dotted cap pitchfork with a fixed preceding sweep. -/
theorem signedCapBlock_enterLeft_of_pitch (L U R : List B) (x : B) (l : Letter I) (d : ℕ)
    (hpitch :
      let a := L ++ [bl(l.dual),x,bl(l)] ++ (U ++ R)
      let b := L ++ [x] ++ (U ++ R)
      signedDg RD Λ P μ a b (signedCapPitchLeft L x l (U ++ R) d) -
        signedDg RD Λ P μ a b (signedCapPitchRight L x l (U ++ R) d) ∈
          signedCrossingSpan RD Λ P μ a b 0) :
    let s := L ++ [bl(l.dual),x] ++ U ++ [bl(l)] ++ R
    let t := L ++ [x] ++ (U ++ R)
    signedDg RD Λ P μ s t (signedCrossLayers L bl(l.dual) x (U ++ [bl(l)] ++ R) ++
        signedCapBlock (L ++ [x]) U l R d) -
      signedDg RD Λ P μ s t (signedCapBlock L (x :: U) l R d) ∈
        signedCrossingSpan RD Λ P μ s t U.length := by
  let s := L ++ [bl(l.dual),x] ++ U ++ [bl(l)] ++ R
  let a := L ++ [bl(l.dual),x,bl(l)] ++ (U ++ R)
  let t := L ++ [x] ++ (U ++ R)
  let pre := sweepBlackLeft (L ++ [bl(l.dual),x]) U l R
  let post := signedCapBlock (L ++ [x]) [] l (U ++ R) d
  have hr : signedChain (L ++ [x,bl(l.dual),bl(l)] ++ (U ++ R)) post t := by
    simpa only [post,t,List.append_assoc,List.cons_append,List.nil_append] using
      signedCapBlock_chain (L ++ [x]) [] l (U ++ R) d
  have hcan : CanCross bl(l.dual) x := by cases x <;> trivial
  have he := crossing_sweep_interchange RD Λ P μ L U R bl(l.dual) x l hcan hr
  have e₁ : signedCapBlock (L ++ [x]) U l R d =
      sweepBlackLeft (L ++ [x,bl(l.dual)]) U l R ++ post := by
    have h := signedCapBlock_append (L ++ [x]) [] U l R d
    simpa only [post, List.append_assoc, List.cons_append, List.nil_append, List.append_nil] using h
  have e₂ : signedCapBlock L (x :: U) l R d = pre ++ signedCapPitchRight L x l (U ++ R) d := by
    have h := signedCapBlock_append L [x] U l R d
    have ep : signedCapBlock L [x] l (U ++ R) d = signedCapPitchRight L x l (U ++ R) d := by
      symm
      simpa [signedCapPitchRight] using signedCapBlock_enterRight L [] x l (U ++ R) d
    simpa [pre,ep,List.append_assoc] using h
  have hp : signedChain s pre a := by
    simpa only [s,pre,a,List.append_assoc,List.cons_append,List.nil_append] using
      sweepBlackLeft_chain (L ++ [bl(l.dual),x]) U l R
  have h := signedDg_replace_span RD Λ P μ hp (signedCapPitchLeft_chain L x l (U ++ R) d)
    (signedCapPitchRight_chain L x l (U ++ R) d) (show signedChain t [] t from rfl) hpitch
  rw [show signedCrossings pre = U.length from sweepBlackLeft_crossings ..,
    show signedCrossings ([] : List (SignedLayer I ℓ)) = 0 from rfl, Nat.add_zero] at h
  have e₁' : signedCrossLayers L bl(l.dual) x (U ++ [bl(l)] ++ R) ++ signedCapBlock (L ++ [x]) U l R d =
      signedCrossLayers L bl(l.dual) x (U ++ [bl(l)] ++ R) ++
      sweepBlackLeft (L ++ [x,bl(l.dual)]) U l R ++ post := by
    rw [e₁]
    exact (List.append_assoc _ _ _).symm
  dsimp only at he ⊢
  rw [e₁', he, e₂]
  simpa only [signedCapPitchLeft, pre, post, List.append_assoc, List.append_nil] using h

/-- The crossing of the first strand inside the block with its stationary
leg is a lower crossing term. The inverse left entrance joins the other
crossing into a bigon. -/
theorem signedCapBlock_crossFirst_of_pitch (L U R : List B) (x : B) (l : Letter I) (d : ℕ)
    (hpitch :
      let a := L ++ [bl(l.dual),x,bl(l)] ++ (U ++ R)
      let b := L ++ [x] ++ (U ++ R)
      signedDg RD Λ P μ a b (signedCapPitchLeft L x l (U ++ R) d) -
        signedDg RD Λ P μ a b (signedCapPitchRight L x l (U ++ R) d) ∈
          signedCrossingSpan RD Λ P μ a b 0)
    (hbigon :
      let a := L ++ [x,bl(l.dual)] ++ U ++ [bl(l)] ++ R
      signedDg RD Λ P μ a a (signedBigonLayers L (U ++ [bl(l)] ++ R) x bl(l.dual)) ∈
        signedCrossingSpan RD Λ P μ a a 1) :
    let s := L ++ [x,bl(l.dual)] ++ U ++ [bl(l)] ++ R
    let t := L ++ [x] ++ (U ++ R)
    signedDg RD Λ P μ s t
        (signedCrossLayers L x bl(l.dual) (U ++ [bl(l)] ++ R) ++ signedCapBlock L (x :: U) l R d) ∈
      signedCrossingSpan RD Λ P μ s t (U.length + 1) := by
  let s := L ++ [x,bl(l.dual)] ++ U ++ [bl(l)] ++ R
  let a := L ++ [bl(l.dual),x] ++ U ++ [bl(l)] ++ R
  let t := L ++ [x] ++ (U ++ R)
  let tail := signedCapBlock (L ++ [x]) U l R d
  let C := signedCrossLayers L x bl(l.dual) (U ++ [bl(l)] ++ R)
  let E := signedCrossLayers L bl(l.dual) x (U ++ [bl(l)] ++ R)
  let K := signedCapBlock L (x :: U) l R d
  have hcan : CanCross x bl(l.dual) := by cases x <;> trivial
  have htail : signedChain s tail t := by
    simpa only [s,t,tail,List.append_assoc,List.cons_append,List.nil_append] using
      signedCapBlock_chain (L ++ [x]) U l R d
  have hC : signedChain s C a := by
    simpa only [s,a,C,List.append_assoc] using signedCrossLayers_chain L hcan (U ++ [bl(l)] ++ R)
  have hE : signedChain a E s := by
    simpa only [s,a,E,List.append_assoc] using signedCrossLayers_chain L hcan.symm (U ++ [bl(l)] ++ R)
  have hK : signedChain a K t := by
    simpa only [a,t,K,List.append_assoc,List.cons_append,List.nil_append] using
      signedCapBlock_chain L (x :: U) l R d
  have h₁ := signedCapBlock_enterLeft_of_pitch RD Λ P μ L U R x l d hpitch
  have h₂ := signedDg_replace_span RD Λ P μ hC (hE.append htail) hK (show signedChain t [] t from rfl) h₁
  rw [show signedCrossings C = 1 from signedCrossLayers_crossings L hcan _,
    show signedCrossings ([] : List (SignedLayer I ℓ)) = 0 from rfl, Nat.add_zero, Nat.add_comm 1] at h₂
  have h₃ := signedDg_mem_span_in_context RD Λ P μ (show signedChain s [] s from rfl)
    (A := C ++ E) (hC.append hE) htail hbigon
  rw [show signedCrossings tail = U.length from signedCapBlock_crossings ..,
    show signedCrossings ([] : List (SignedLayer I ℓ)) = 0 from rfl, Nat.zero_add, Nat.add_comm 1] at h₃
  have h₄ : signedDg RD Λ P μ s t (C ++ E ++ tail) - signedDg RD Λ P μ s t (C ++ K) ∈
      signedCrossingSpan RD Λ P μ s t (U.length + 1) := by
    simpa only [List.append_assoc,List.append_nil] using h₂
  have h₅ : signedDg RD Λ P μ s t (C ++ E ++ tail) ∈ signedCrossingSpan RD Λ P μ s t (U.length + 1) := by
    simpa only [List.nil_append] using h₃
  simpa only [sub_sub_cancel] using
    Submodule.sub_mem (signedCrossingSpan RD Λ P μ s t (U.length + 1)) h₅ h₄

end Categorification.Stendhal.DoubleDiagram
