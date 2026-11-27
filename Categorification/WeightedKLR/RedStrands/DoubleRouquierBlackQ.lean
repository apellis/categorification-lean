/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierBlack
import Categorification.Diagrams.CLQ.ThetaReflection

/-!
# Black double diagrams in a Rouquier family, for all scalars

Webster, arXiv:1309.3796v3, §4.5, proof of Theorem 4.25, for a Rouquier family through which
the Cautis–Lauda presentation acts with arbitrary scalars `Sc` (`r = 1`).

`admissibleMap_blackMirror_rel` (`Categorification.WeightedKLR.RedStrands.DoubleRouquierBlack`)
needs `presCL RD k Sc = pres RD k`, i.e. the KL parameters. Here the reflected relations are
those of `U_{Sc^θ}(g)`, `Sc^θ = CLQ.thetaScalars RD Sc` (`t^θ_{ij} = t_{ji}^{-1}`,
`s^θ = (t_{ij} t_{ji})^{-1} s`), and they act by zero for every `Sc`
(`admissibleMap_blackMirror_relQ`): the reflection with inverted orientations maps the relations
of `U_{Sc^θ}(g)` to relations of `U_{(Sc^θ)^θ}(g) = U_{Sc}(g)`
(`CLQ.lin_thetaLin_eq_zero`, `CLQ.thetaScalars_thetaScalars`). At the KL parameters
`Sc^θ = Sc` and both presentations are KL III's.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram
  StringDiagrams TwoRep Diagrams.BicatInterp

universe w₁ v₁ u₁ w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {ℓ : ℕ} {Λ : Fin ℓ → X}

/-- The sources of the relations of `U_Q(g)` are well formed. -/
theorem presCL_dom_wf {k : Type*} [CommRing k] {S : CL.CLScalars C k}
    (r : (CL.presCL RD k S).Rel) : ((CL.presCL RD k S).dom r).WF := by
  rcases r with ((e | c | c) | r)
  · exact e.elim
  · exact Pivotal.colourObj_wf _ c
  · exact Pivotal.dualObj_wf _ c
  · cases r <;> exact ob_wf RD _ _

/-- The targets of the relations of `U_Q(g)` are well formed. -/
theorem presCL_cod_wf {k : Type*} [CommRing k] {S : CL.CLScalars C k}
    (r : (CL.presCL RD k S).Rel) : ((CL.presCL RD k S).cod r).WF := by
  rcases r with ((e | c | c) | r)
  · exact e.elim
  · exact Pivotal.colourObj_wf _ c
  · exact Pivotal.dualObj_wf _ c
  · cases r <;> exact ob_wf RD _ _

section Relations

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]
  (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)
  (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
  (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
    C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))

include H M hr hq in
/-- **The reflected relations of `U_{Sc^θ}(g)` act by zero** on double diagrams, for generator
images that are those of a Rouquier family on the black generators, for all scalars `Sc` with
`r = 1`. -/
theorem admissibleMap_blackMirror_relQ [DecidableEq I] {G : GenImg (doubleModel S red)}
    (hG : BlackOn Sc G) (r : (CLQ.pres RD k (CLQ.thetaScalars RD Sc)).Rel) {s t : X}
    (ha : Cond s t ((blackMirror RD Λ).obj ((CLQ.pres RD k (CLQ.thetaScalars RD Sc)).dom r)))
    (hb : Cond s t ((blackMirror RD Λ).obj ((CLQ.pres RD k (CLQ.thetaScalars RD Sc)).cod r))) :
    admissibleMap G ha hb
      (blackMirrorLinear RD Λ ((CLQ.pres RD k (CLQ.thetaScalars RD Sc)).rel r)) = 0 := by
  have hwa : ((CLQ.pres RD k (CLQ.thetaScalars RD Sc)).dom r).WF := presCL_dom_wf r
  have hwb : ((CLQ.pres RD k (CLQ.thetaScalars RD Sc)).cod r).WF := presCL_cod_wf r
  rw [blackMirrorLinear_eq RD Λ hwa hwb]
  refine admissibleMap_cast_eq_zero G _ _ _ ha hb ?_
  have ha' := cond_thetaObj hwa ((blackMirror_obj_eq RD Λ hwa) ▸ ha)
  have hb' := cond_thetaObj hwb ((blackMirror_obj_eq RD Λ hwb) ▸ hb)
  refine admissibleMap_pull_eq_zero (blackRelabel RD Λ) G ha' hb' _ ?_
  refine admissibleMap_eq_zero_of_strand_heq (doubleModel_pull_strand S red)
    (G₂ := S.genImg Sc) ?_ ha' hb' _ ?_
  · intro g a b ha hb hd hde hc hce
    refine (eqToHom_comp_heq _ _).trans ((comp_eqToHom_heq _ _).trans ?_)
    refine (heq_of_eq (hG _ _ _ _ _ _ _ _ _ _)).trans ?_
    rcases g with (⟨⟨⟨_ | _, i⟩, r⟩⟩ | ⟨_ | _, i, j, ν⟩) | ⟨⟨_ | _, i⟩, r⟩ | ⟨⟨_ | _, i⟩, r⟩
    · exact HEq.rfl
    · exact HEq.rfl
    · obtain rfl : ν = b := hde
      exact crossDn_heq S Sc i j rfl rfl _ _ _ _ _ _ _ _
    · obtain rfl : ν = b := hde
      exact cross_heq S i j rfl rfl _ _ _ _ _ _ _ _
    · exact (blackImg_cup_up S red Sc _ i _ _ _ _ _ _ (RouqFamily.dn_reg i rfl ha)).trans
        (genImg_cup_dn S Sc i r _ _ _ _ _ _ _).symm
    · exact (blackImg_cup_dn S red Sc _ i _ _ _ _ _ _ (RouqFamily.up_reg i rfl ha)).trans
        (genImg_cup_up S Sc i r _ _ _ _ _ _ _).symm
    · exact (blackImg_cap_up S red Sc _ i _ _ _ _ _ _ (RouqFamily.dn_reg i hde rfl)).trans
        (genImg_cap_dn S Sc i r _ _ _ _ _ _ _).symm
    · exact (blackImg_cap_dn S red Sc _ i _ _ _ _ _ _ (RouqFamily.up_reg i hde rfl)).trans
        (genImg_cap_up S Sc i r _ _ _ _ _ _ _).symm
  · refine admissibleMap_genImg_eq_zero S Sc H M hr hq ha' hb' _ ?_
    have h := CLQ.lin_thetaLin_eq_zero (CLQ.thetaScalars RD Sc) _ hwa
      (Presentation.lin_rel_self _ r)
    rwa [CLQ.thetaScalars_thetaScalars _ hr] at h

end Relations

end Categorification.Stendhal.DoubleDiagram
