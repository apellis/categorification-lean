/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleSignedCupPitchfork
import Categorification.WeightedKLR.RedStrands.DoubleSignedCapBraidBlackQ
import Categorification.WeightedKLR.RedStrands.DoubleRedCup

/-!
# Passing a signed strand through a black cup

Webster, arXiv:1309.3796v2, §4.5, Lemma 4.28. When pushing a cap toward
a preceding cup, a through-strand can cross either leg. The black pitchfork
modulo zero crossings uses the black rectangle for KL III, arXiv:0807.3250v1,
proof of Proposition 3.11. For red the cup mate is exact.

This is the version of `DoubleSignedCupPitchfork` in which the black strands carry the relations of
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
  (μ : X) (L : List (DoubleStrand I ℓ)) (x : DoubleStrand I ℓ) (l : Letter I)
  (R : List (DoubleStrand I ℓ))
local notation "bl(" b ")" => (Sum.inl b : DoubleStrand I ℓ)
local notation "η" => endWeight RD Λ μ L
local notation "rightWeight" => fun s : List (Letter I) => endWeight RD Λ μ (L ++ blackWord s)

include hP

/-- The black pitchfork has a zero-crossing error, up to a unit, in a signed exterior word
when the reflected `U_Q(g)` relations hold (the unit comes from the scalars `t_{ij}` of
Cautis–Lauda's cup pitchfork), by the cup pitchfork in the proof of KL III,
arXiv:0807.3250v1, Proposition 3.11. -/
theorem signedCup_blackQ (m : Letter I) :
    let s := L ++ [bl(m)] ++ R
    let t := L ++ [bl(l),bl(m),bl(l.dual)] ++ R
    ∃ c : kˣ, signedDg RD Λ P μ s t (signedCupFromRight L (bl(m)) l R) -
        (c : k) • signedDg RD Λ P μ s t (signedCupFromLeft L (bl(m)) l R) ∈
      signedCrossingSpan RD Λ P μ s t 0 := by
  classical
  let s := [m]
  let t := [l.dual,m,l]
  have ht : (rightWeight) t = (rightWeight) s := by
    obtain ⟨_ | _,i⟩ := l <;>
      simp [s,t,blackWord,endWeight,DoubleStrand.weight,Letter.dual,
        add_comm,add_left_comm]
  let F := blackRectangleHomQ RD Λ sc μ L R s P hP t rfl ht
  let a := [([], Shape.cup l.dual, [m])] ++ (xLay l m).map (whL [l.dual] [])
  let b := [([m], Shape.cup l.dual, [])] ++ (xLay m l.dual).map (whL [] [l])
  have ha : SChain s a t := by
    exact (show SChain s [([], .cup l.dual,[m])] [l.dual,l,m] by simp [s,SChain,Letter.dual_dual]).append
      (by simpa [t] using (sChain_xLay l m).whisk [l.dual] [])
  have hb : SChain s b t := by
    exact (show SChain s [([m], .cup l.dual,[])] [m,l.dual,l] by simp [s,SChain,Letter.dual_dual]).append
      (by simpa [t] using (sChain_xLay m l.dual).whisk [] [l])
  let D := signedDg RD Λ P μ (L ++ [bl(m)] ++ R) (L ++ [bl(l),bl(m),bl(l.dual)] ++ R)
  have e₁ : F (NF.dg (CLQ.pres RD k sc) η s t a) = D (signedCupFromRight L (bl(m)) l R) := by
    dsimp only [F]
    rw [NF.dg_of ha, ← Presentation.lin_of, blackRectangleHom_linQ, blackLinear_of, Presentation.lin_of]
    symm
    apply signedDg_eq_diag_of_layers RD Λ P μ (signedCupFromRight_chain L (bl(m)) l R)
    rw [layers_blackDiagram_mkD]
    obtain ⟨_ | _,i⟩ := l <;> obtain ⟨_ | _,j⟩ := m <;>
      simp [a, signedCupFromRight, xLay, whL, crosslL, crossrL, signedLayers, crossBlackLeft,
        upwardMateLayers, blackWord, Sig.shape, Letter.dual]
  have e₂ : F (NF.dg (CLQ.pres RD k sc) η s t b) = D (signedCupFromLeft L (bl(m)) l R) := by
    dsimp only [F]
    rw [NF.dg_of hb, ← Presentation.lin_of, blackRectangleHom_linQ, blackLinear_of, Presentation.lin_of]
    symm
    apply signedDg_eq_diag_of_layers RD Λ P μ (signedCupFromLeft_chain L (bl(m)) l R)
    rw [layers_blackDiagram_mkD]
    obtain ⟨_ | _,i⟩ := l <;> obtain ⟨_ | _,j⟩ := m <;>
      simp [b, signedCupFromLeft, xLay, whL, crosslL, crossrL, signedLayers, signedCrossLayers,
        crossBlackLeft, upwardMateLayers, blackWord, Sig.shape, Letter.dual, List.append_assoc]
  obtain ⟨c, h⟩ : ∃ c : kˣ, NF.dg (CLQ.pres RD k sc) η s t a -
      (c : k) • NF.dg (CLQ.pres RD k sc) η s t b ∈ CLQ.LeL RD k sc η s t 0 := by
    obtain ⟨_ | _,i⟩ := l <;> exact CLQ.cupPF (RD := RD) (k := k) η _ m
  have hh := blackRectangleHom_mem_signedCrossingSpanQ RD Λ sc P hP μ L R rfl ht h
  change F (_ - _) ∈ _ at hh
  rw [map_sub, map_smul, e₁, e₂] at hh
  exact ⟨c, hh⟩

end Categorification.Stendhal.DoubleDiagram
