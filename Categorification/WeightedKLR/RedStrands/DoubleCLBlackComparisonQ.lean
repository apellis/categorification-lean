/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackComparison
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackRelationsQ

/-!
# The black relations with general parameters, compared with a restricted Rouquier family

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, for black strands carrying the relations
of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`) for scalars `Sb`. The
cover functor sends the reflected black relations to the inversion of orientations of the
relations, restricted to the black colours (`coverLin_blackMirror`); these hold in
`U_{Sb^θ}(g)`, so they are killed by every admissible evaluation of a Rouquier family whose
scalars restrict to `Sb^θ` on the black colours (`coverLin_blackRelQ`). This is the analogue of
`coverLin_blackRel`, which needs `t = 1` on the black colours.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams TwoRep

universe w u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {C' : CartanDatum (I ⊕ Fin ℓ)}
  {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (W : WeightDatum C' X Y)
  (hC : ∀ i j, C'.dot (.inl i) (.inl j) = C.dot i j) (o : X)
  (ho : ∀ i, W.pair (W.iY (.inl i)) o = 0)

local notation "RD" => blackDatum W hC
local notation "Λ" => redWeight W

section Rouquier
open Diagrams.BicatInterp

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] (S : RouqFamily (B := B) W)
  [AdditiveWhiskering B] {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (Bicategory.precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (Bicategory.postcomp a g).Linear k]

include ho in
/-- **The black relations with general parameters hold after reflection.** The image of a
reflected relation of `U_Q(g)` for the black scalars `Sb` under the KL diagrams of the moves is
killed by every admissible evaluation of a Rouquier family for `W` with Cautis–Lauda scalars
`Sc`, Brundan's upward relations and invertible mixed crossings, provided `Sb^θ` is the
restriction of `Sc` to the black colours and `s` vanishes there outside the extremal degrees. -/
theorem coverLin_blackRelQ [DecidableEq I] (Sc : CL.CLScalars C' k) (Sb : CL.CLScalars C k)
    (hθ : CLQ.thetaScalars RD Sb = (coverRestrict W hC o ho).scalars hC Sc)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s (.inl i) (.inl j) p q = 0)
    (H : BrundanUpKLR S Sc) (Mi : BrundanMixedInversion S) (r : (CLQ.pres RD k Sb).Rel) :
    coverLin W hC o (admissibleKernel (S.genImg Sc)) coverSign
      (blackMirrorLinear RD Λ ((CLQ.pres RD k Sb).rel r)) = 0 := by
  by_cases h0 : (CLQ.pres RD k Sb).rel r = 0
  · rw [h0, map_zero]
    simp [coverLin, LayerMap.lin]
  obtain ⟨d, -⟩ := Finsupp.ne_iff.mp h0
  have hdom : ((CLQ.pres RD k Sb).dom r).WF := CLQ.pres_dom_wfQ r
  have hcod : ((CLQ.pres RD k Sb).cod r).WF := (Diagram.chain d).wf hdom
  rw [coverLin_blackMirror W hC o ho _ _ hdom hcod,
    admissibleKernel_lin_eq_zero _ _ ?_, Limits.zero_comp, Limits.comp_zero]
  intro s t ha hb
  have hwd : (Omega.obj RD ((CLQ.pres RD k Sb).dom r)).WF := (Omega.ok_word _ _ hdom).1
  have hwc : (Omega.obj RD ((CLQ.pres RD k Sb).cod r)).WF := (Omega.ok_word _ _ hcod).1
  obtain ⟨rfl, rfl, ha'⟩ := cond_of_map (coverRestrict W hC o ho).sigMap hwd ha
  obtain ⟨hs', ht', hb'⟩ := cond_of_map (coverRestrict W hC o ho).sigMap hwc hb
  have hinj : Function.Injective (coverRestrict W hC o ho).sigMap.region :=
    fun x y h => @add_left_cancel X _ _ o x y h
  have hb'' : Cond (S := psig RD) (Omega.obj RD ((CLQ.pres RD k Sb).dom r)).start
      ((psig RD).endR (Omega.obj RD ((CLQ.pres RD k Sb).dom r)).start
        (Omega.obj RD ((CLQ.pres RD k Sb).dom r)).word)
      ((omegaLayerMap RD).obj ((CLQ.pres RD k Sb).cod r)) := by
    have e1 := hinj hs'
    have e2 := hinj ht'
    refine ⟨e1 ▸ hb'.1, ?_, e1.symm⟩
    rw [e2, e1]
    rfl
  exact omega_rel_restrictQ (coverRestrict W hC o ho) hC S Sc Sb hθ hq H Mi r ha' hb''

end Rouquier

end Categorification.Stendhal.DoubleDiagram
