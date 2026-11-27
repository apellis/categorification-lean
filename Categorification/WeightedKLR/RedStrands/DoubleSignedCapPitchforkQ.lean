/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapPitchfork
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBareQ
import Categorification.Diagrams.KL3.SpanningSetBlock
import Categorification.Diagrams.CLQ.SpanningSetBlock

/-!
# The dotted cap pitchfork with a signed through-strand

Webster, arXiv:1309.3796v2, §4.5, Definition 4.24 and Lemma 4.28.
The local cap pitchfork compares the two crossings at a straddled cap.
The black case reflects the one-strand instance of the cap-block
calculation in KL III, arXiv:0807.3250v1, proof of Proposition 3.11.

This is the version of `DoubleSignedCapPitchfork` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe w u v
variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (Λ : Fin ℓ → X)
  {k : Type w} [CommRing k] (sc : KL3.Diagram.CL.CLScalars C k) (P : Presentation.{w,max u v} (signature RD Λ) k)
  (μ : X) (L : List (DoubleStrand I ℓ)) (x : DoubleStrand I ℓ) (l : Letter I)
  (R : List (DoubleStrand I ℓ)) (d : ℕ)

local notation "B" => DoubleStrand I ℓ
local notation "bl(" m ")" => (Sum.inl m : B)
local notation "A" => bl(l.dual)
local notation "Bleg" => bl(l)
local notation "η" => endWeight RD Λ μ L

private theorem dg_cap_right_whiskQ (ν : X) (u v : List (Letter I)) (m : Letter I) (d : ℕ) :
    NF.dg (CLQ.pres RD k sc) ν (u ++ [m,m.dual] ++ v) (u ++ v) ((rawCapDotRight m.dual d).map (whL u v)) =
      NF.dg (CLQ.pres RD k sc) ν (u ++ [m,m.dual] ++ v) (u ++ v) ((capBlk [] m.dual d).map (whL u v)) := by
  have h := congrArg (NF.plcL (CLQ.pres RD k sc) ν u v [m,m.dual] [])
    (dg_rawCapDotRightQ (k := k) RD sc (wt RD ν v) m d)
  rw [NF.plcL_dg, NF.plcL_dg, List.append_nil] at h
  exact h

/-- With a black through-strand, the dotted cap pitchfork has, up to a unit (the scalars
`t_{ij}` of Cautis–Lauda's `U_Q(g)`), only zero-crossing errors in any reflected black
rectangle. -/
theorem signedCapPitch_blackQ
    (hP : ∀ r : (CLQ.pres RD k sc).Rel, P.lin (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel r)) = 0)
    (m : Letter I) :
    let s := L ++ [A,bl(m),Bleg] ++ R
    let t := L ++ [bl(m)] ++ R
    ∃ c : kˣ, signedDg RD Λ P μ s t (signedCapPitchLeft L bl(m) l R d) -
      (c : k) • signedDg RD Λ P μ s t (signedCapPitchRight L bl(m) l R d) ∈
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
  have er : NF.dg (CLQ.pres RD k sc) η s t rightPath = NF.dg (CLQ.pres RD k sc) η s t (ar ++ standard.map (whL [m] [])) := by
    dsimp only [rightPath]
    rw [← NF.dg_comp hr cr, ← NF.dg_comp hr sr]
    exact congrArg (NF.dg (CLQ.pres RD k sc) η s [m,l,l.dual] ar ≫ ·)
      (dg_cap_right_whiskQ RD sc (k := k) η [m] [] l d)
  have el : NF.dg (CLQ.pres RD k sc) η s t leftPath = NF.dg (CLQ.pres RD k sc) η s t (al ++ standard.map (whL [] [m])) := by
    dsimp only [leftPath]
    rw [← NF.dg_comp hl cl, ← NF.dg_comp hl sl]
    exact congrArg (NF.dg (CLQ.pres RD k sc) η s [l,l.dual,m] al ≫ ·)
      (dg_cap_right_whiskQ RD sc (k := k) η [] [m] l d)
  obtain ⟨c, hraw⟩ : ∃ c : kˣ, NF.dg (CLQ.pres RD k sc) η s t rightPath -
      (c : k) • NF.dg (CLQ.pres RD k sc) η s t leftPath ∈ CLQ.LeL RD k sc η s t 0 := by
    rw [er,el]
    have e : al ++ standard.map (whL [] [m]) = capBlk [m] l.dual d := by
      simp [al,standard,capBlk,lmLc,whL,List.map_replicate,Letter.dual_dual]
    rw [e]
    have hk := CLQ.capBlk_enterL (RD := RD) (k := k) (sc := sc) η [] m l.dual d
    rw [show [l.dual.dual,m] ++ [] ++ [l.dual] = s by simp [s, Letter.dual_dual]] at hk
    simpa only [ar,standard,t,Letter.dual_dual,List.nil_append,List.length_nil] using hk
  have hw : endWeight RD Λ μ (L ++ blackWord s) = endWeight RD Λ μ (L ++ blackWord t) := by
    obtain ⟨_,i⟩ := l
    rename_i ε
    cases ε <;> simp [s,t,blackWord,endWeight,DoubleStrand.weight,Letter.dual,add_comm,add_left_comm]
  let F := blackRectangleHomQ RD Λ sc μ L R s P hP t hw rfl
  have h := blackRectangleHom_mem_signedCrossingSpanQ RD Λ sc P hP μ L R hw rfl hraw
  change F (_ - _) ∈ _ at h
  rw [map_sub, map_smul] at h
  dsimp only [F] at h
  rw [blackRectangleHom_dgQ RD Λ sc P hP μ L R hw rfl (hr.append cr),
    blackRectangleHom_dgQ RD Λ sc P hP μ L R hw rfl (hl.append cl)] at h
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
  refine ⟨c⁻¹, ?_⟩
  have h' := Submodule.smul_mem _ (-((c⁻¹ : kˣ) : k)) h
  convert h' using 1
  rw [smul_sub, smul_smul, neg_mul, Units.inv_mul, neg_smul, neg_smul, one_smul]
  abel

end Categorification.Stendhal.DoubleDiagram
