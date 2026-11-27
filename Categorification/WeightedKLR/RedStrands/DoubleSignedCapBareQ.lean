/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBare
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBraidBlackQ
import Categorification.Diagrams.KL3.SpanningSetCaps
import Categorification.Diagrams.CLQ.SpanningSetCaps

/-!
# Dot cyclicity at a bare signed cap

Khovanov–Lauda III, arXiv:0807.3250v1, §3.1.2, (3.3). Reflect the
black cap with any number of dots into a signed rectangle in the cap
sweep of Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28.

This is the version of `DoubleSignedCapBare` in which the black strands carry the relations of
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
  (hP : ∀ r : (CLQ.pres RD k sc).Rel, P.lin (blackMirrorLinear RD Λ ((CLQ.pres RD k sc).rel r)) = 0)
  (μ : X) (L : List (DoubleStrand I ℓ)) (l : Letter I) (R : List (DoubleStrand I ℓ))

local notation "B" => DoubleStrand I ℓ
local notation "bl(" x ")" => (Sum.inl x : B)
local notation "η" => endWeight RD Λ μ L
local notation "rightWeight" => fun s : List (Letter I) => endWeight RD Λ μ (L ++ blackWord s)

/-- Evaluate a reflected KL diagram between two signed exterior words. -/
theorem blackRectangleHom_dgQ {s t : List (Letter I)} {τ : X}
    (hs : (rightWeight) s = τ) (ht : (rightWeight) t = τ)
    {ls : List (LayerData I)} (hc : SChain s ls t) :
    blackRectangleHomQ RD Λ sc μ L R s P hP t hs ht (NF.dg (CLQ.pres RD k sc) η s t ls) =
      P.diag (blackDiagram RD Λ μ L R (mkD RD η ls hc)) := by
  rw [NF.dg_of hc, ← Presentation.lin_of, blackRectangleHom_linQ, blackLinear_of, Presentation.lin_of]

/-- In raw KL order the right and left dot decorations of the bare cap agree. -/
theorem dg_rawCapDotRightQ (ν : X) (l : Letter I) (d : ℕ) :
    NF.dg (CLQ.pres RD k sc) ν [l,l.dual] [] (rawCapDotRight l.dual d) =
      NF.dg (CLQ.pres RD k sc) ν [l,l.dual] [] (capBlk [] l.dual d) := by
  obtain ⟨ε,i⟩ := l
  cases ε
  · exact (CLQ.dg_dots_cap_up RD k sc ν i d).symm
  · exact CLQ.dg_dots_cap_dn RD k sc ν i d

include hP in
/-- Dot decorations can move to the stationary leg of a bare signed cap in
any exterior context, once the reflected black KL equations hold. -/
theorem signedCapDotRight_eqQ (d : ℕ) :
    let s := L ++ [bl(l.dual),bl(l)] ++ R
    signedDg RD Λ P μ s (L ++ R) (signedCapDotRight L l R d) =
      signedDg RD Λ P μ s (L ++ R) (signedCapBlock L [] l R d) := by
  let s := [l, l.dual]
  have hs : (rightWeight) s = (rightWeight) [] := by
    obtain ⟨ε,i⟩ := l
    cases ε <;> simp [s, blackWord, endWeight, DoubleStrand.weight, Letter.dual, add_comm]
  have ha : SChain s (capBlk [] l.dual d) [] := by
    simpa [s, Letter.dual_dual] using sChain_capBlk ([] : List (Letter I)) l.dual d
  have hb : SChain s (rawCapDotRight l.dual d) [] := by
    simpa [s, Letter.dual_dual] using rawCapDotRight_chain l.dual d
  let F := blackRectangleHomQ RD Λ sc μ L R s P hP [] hs rfl
  have h := congrArg F (dg_rawCapDotRightQ (k := k) RD sc η l d)
  dsimp only [F] at h
  rw [blackRectangleHom_dgQ RD Λ sc P hP μ L R hs rfl hb,
    blackRectangleHom_dgQ RD Λ sc P hP μ L R hs rfl ha] at h
  let codEq : obj RD Λ μ (L ++ blackWord [] ++ R) = obj RD Λ μ (L ++ R) := by simp [blackWord]
  have hcast := congrArg (P.castHom rfl codEq) h
  simp only [Presentation.castHom_diag] at hcast
  have e₁ := signedDg_eq_diag_of_layers RD Λ P μ (signedCapDotRight_chain L l R d)
    (Diagram.cast (blackDiagram RD Λ μ L R (mkD RD η _ ha)) rfl codEq) (by
      rw [Diagram.layers_cast, layers_blackDiagram_mkD]
      simp [capBlk, lmLc, signedCapDotRight, signedLayers, List.map_replicate,
        Sig.shape, blackWord, Letter.dual_dual])
  have h₂ : signedChain (L ++ [bl(l.dual),bl(l)] ++ R) (signedCapBlock L [] l R d) (L ++ R) := by
    simpa [List.append_assoc] using signedCapBlock_chain L [] l R d
  have e₂ := signedDg_eq_diag_of_layers RD Λ P μ h₂
    (Diagram.cast (blackDiagram RD Λ μ L R (mkD RD η _ hb)) rfl codEq) (by
    rw [Diagram.layers_cast, layers_blackDiagram_mkD]
    simp [rawCapDotRight, signedCapBlock, sweepBlackLeft, signedLayers, capLegDots, List.map_replicate,
      Sig.shape, blackWord, Letter.dual_dual])
  exact e₁.trans (hcast.symm.trans e₂.symm)

end Categorification.Stendhal.DoubleDiagram
