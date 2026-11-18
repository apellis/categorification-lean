/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBare
import Categorification.Diagrams.KL3.SpanningSetBlock

/-!
# The dotted cap pitchfork with a signed through-strand

Webster, arXiv:1309.3796v2, §4.5, Definition 4.24 and Lemma 4.28.
The local cap pitchfork compares the two crossings at a straddled cap.
The black case reflects the one-strand instance of the cap-block
calculation in KL III, arXiv:0807.3250v1, proof of Proposition 3.11.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (L : List (DoubleStrand I ℓ)) (x : DoubleStrand I ℓ) (l : Letter I)
  (R : List (DoubleStrand I ℓ)) (d : ℕ)

local notation "B" => DoubleStrand I ℓ
local notation "bl(" m ")" => (Sum.inl m : B)
local notation "A" => bl(l.dual)
local notation "Bleg" => bl(l)
local notation "η" => endWeight RD Λ μ L

/-- Move the through-strand to the left, then take the dotted cap. -/
def signedCapPitchLeft : List (SignedLayer I ℓ) :=
  signedCrossLayers L A x (Bleg :: R) ++ signedCapBlock (L ++ [x]) [] l R d

/-- Move the through-strand to the right, then take the dotted cap. -/
def signedCapPitchRight : List (SignedLayer I ℓ) :=
  crossBlackLeft (L ++ [A]) x l R ++ signedCapBlock L [] l (x :: R) d

theorem signedCapPitchLeft_chain :
    signedChain (L ++ [A,x,Bleg] ++ R) (signedCapPitchLeft L x l R d) (L ++ [x] ++ R) := by
  have hc := signedCrossLayers_chain L (show CanCross A x by cases x <;> trivial) (Bleg :: R)
  have hd := signedCapBlock_chain (L ++ [x]) [] l R d
  simp only [List.append_assoc,List.cons_append,List.nil_append] at hc hd ⊢
  exact hc.append hd

theorem signedCapPitchRight_chain :
    signedChain (L ++ [A,x,Bleg] ++ R) (signedCapPitchRight L x l R d) (L ++ [x] ++ R) := by
  have hc := crossBlackLeft_chain (L ++ [A]) x l R
  have hd := signedCapBlock_chain L [] l (x :: R) d
  simp only [List.append_assoc,List.cons_append,List.nil_append] at hc hd ⊢
  exact hc.append hd

private theorem dg_cap_right_whisk (ν : X) (u v : List (Letter I)) (m : Letter I) (d : ℕ) :
    dg RD k ν (u ++ [m,m.dual] ++ v) (u ++ v) ((rawCapDotRight m.dual d).map (whL u v)) =
      dg RD k ν (u ++ [m,m.dual] ++ v) (u ++ v) ((capBlk [] m.dual d).map (whL u v)) := by
  have h := congrArg (plcL RD k ν u v [m,m.dual] [])
    (dg_rawCapDotRight (k := k) RD (wt RD ν v) m d)
  rw [plcL_dg, plcL_dg, List.append_nil] at h
  exact h

/-- With a black through-strand, the dotted cap pitchfork has only
zero-crossing errors in any reflected black rectangle. -/
theorem signedCapPitch_black
    (hP : ∀ r : (pres RD k).Rel, P.lin (blackMirrorLinear RD Λ ((pres RD k).rel r)) = 0)
    (m : Letter I) :
    let s := L ++ [A,bl(m),Bleg] ++ R
    let t := L ++ [bl(m)] ++ R
    signedDg RD Λ P μ s t (signedCapPitchLeft L bl(m) l R d) -
      signedDg RD Λ P μ s t (signedCapPitchRight L bl(m) l R d) ∈
        signedCrossingSpan RD Λ P μ s t 0 := by
  classical
  let s := [l,m,l.dual]
  let t := [m]
  let ar := (xLay l m).map (whL [] [l.dual])
  let al := (xLay m l.dual).map (whL [l] [])
  let cap := rawCapDotRight l.dual d
  let standard := capBlk [] l.dual d
  let rightPath := ar ++ cap.map (whL [m] [])
  let leftPath := al ++ cap.map (whL [] [m])
  have hr : SChain s ar [m,l,l.dual] := by simpa [s,ar] using (sChain_xLay l m).whisk [] [l.dual]
  have hl : SChain s al [l,l.dual,m] := by simpa [s,al] using (sChain_xLay m l.dual).whisk [l] []
  have hc : SChain [l,l.dual] cap [] := by
    simpa only [cap,Letter.dual_dual] using rawCapDotRight_chain l.dual d
  have hstd : SChain [l,l.dual] standard [] := by
    simpa only [standard,List.nil_append,List.cons_append,Letter.dual_dual] using sChain_capBlk [] l.dual d
  have cr : SChain [m,l,l.dual] (cap.map (whL [m] [])) t := by simpa [t] using hc.whisk [m] []
  have cl : SChain [l,l.dual,m] (cap.map (whL [] [m])) t := by simpa [t] using hc.whisk [] [m]
  have sr : SChain [m,l,l.dual] (standard.map (whL [m] [])) t := by simpa [t] using hstd.whisk [m] []
  have sl : SChain [l,l.dual,m] (standard.map (whL [] [m])) t := by simpa [t] using hstd.whisk [] [m]
  have er : dg RD k η s t rightPath = dg RD k η s t (ar ++ standard.map (whL [m] [])) := by
    dsimp only [rightPath]
    rw [← dg_comp hr cr, ← dg_comp hr sr]
    exact congrArg (dg RD k η s [m,l,l.dual] ar ≫ ·)
      (dg_cap_right_whisk RD (k := k) η [m] [] l d)
  have el : dg RD k η s t leftPath = dg RD k η s t (al ++ standard.map (whL [] [m])) := by
    dsimp only [leftPath]
    rw [← dg_comp hl cl, ← dg_comp hl sl]
    exact congrArg (dg RD k η s [l,l.dual,m] al ≫ ·)
      (dg_cap_right_whisk RD (k := k) η [] [m] l d)
  have hraw : dg RD k η s t rightPath - dg RD k η s t leftPath ∈ LeL RD k η s t 0 := by
    rw [er,el]
    have e : al ++ standard.map (whL [] [m]) = capBlk [m] l.dual d := by
      simp [al,standard,capBlk,lmLc,whL,List.map_replicate,Letter.dual_dual]
    rw [e]
    have hk := capBlk_enterL (RD := RD) (k := k) η [] m l.dual d
    rw [show [l.dual.dual,m] ++ [] ++ [l.dual] = s by simp [s, Letter.dual_dual]] at hk
    simpa only [ar,standard,t,Letter.dual_dual,List.nil_append,List.length_nil] using hk
  have hw : endWeight RD Λ μ (L ++ blackWord s) = endWeight RD Λ μ (L ++ blackWord t) := by
    obtain ⟨_,i⟩ := l
    rename_i ε
    cases ε <;> simp [s,t,blackWord,endWeight,DoubleStrand.weight,Letter.dual,add_comm,add_left_comm]
  let F := blackRectangleHom RD Λ μ L R s P hP t hw rfl
  have h := blackRectangleHom_mem_signedCrossingSpan RD Λ P hP μ L R hw rfl hraw
  change F (_ - _) ∈ _ at h
  rw [map_sub] at h
  dsimp only [F] at h
  rw [blackRectangleHom_dg RD Λ P hP μ L R hw rfl (hr.append cr),
    blackRectangleHom_dg RD Λ P hP μ L R hw rfl (hl.append cl)] at h
  have e₁ := signedDg_eq_diag_of_layers RD Λ P μ (signedCapPitchRight_chain L bl(m) l R d)
    (blackDiagram RD Λ μ L R (mkD RD η _ (hr.append cr))) (by
      rw [layers_blackDiagram_mkD]
      obtain ⟨_ | _,i⟩ := l <;> obtain ⟨_ | _,j⟩ := m <;>
        simp [ar,cap,xLay,crosslL,crossrL,whL,signedCapPitchRight,signedCapBlock,sweepBlackLeft,
          crossBlackLeft,upwardMateLayers,rawCapDotRight,capLegDots,signedLayers,blackWord,Sig.shape,
          List.map_replicate,List.append_assoc,Letter.dual])
  have e₂ := signedDg_eq_diag_of_layers RD Λ P μ (signedCapPitchLeft_chain L bl(m) l R d)
    (blackDiagram RD Λ μ L R (mkD RD η _ (hl.append cl))) (by
      rw [layers_blackDiagram_mkD]
      obtain ⟨_ | _,i⟩ := l <;> obtain ⟨_ | _,j⟩ := m <;>
        simp [al,cap,xLay,crosslL,crossrL,whL,signedCapPitchLeft,signedCapBlock,sweepBlackLeft,
          signedCrossLayers,crossBlackLeft,upwardMateLayers,rawCapDotRight,capLegDots,signedLayers,
          blackWord,Sig.shape,List.map_replicate,Letter.dual])
  rw [← e₁, ← e₂] at h
  change _ ∈ signedCrossingSpan RD Λ P μ (L ++ [A,bl(m),Bleg] ++ R) (L ++ [bl(m)] ++ R) 0 at h
  simpa only [neg_sub] using Submodule.neg_mem _ h

end Categorification.Stendhal.DoubleDiagram
