/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackRelations
import Categorification.Diagrams.CLQ.SymmetryOmega
import Categorification.TwoRep.RouqRestrictScalars

/-!
# Black relations with general parameters in the cyclotomic evaluation of double diagrams

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, for black strands with general
Cautis–Lauda parameters. `Categorification.WeightedKLR.RedStrands.DoubleCLBlackRelations`
treats the black KL III relations (Khovanov–Lauda parameters). Here the black relations are those
of `U_Q(g)` (S. Cautis, A. D. Lauda, arXiv:1111.1431v3, Definition 1.1, `r = 1`) for scalars
`Sb`. Their inversion of orientations `Ω` (with the sign of KL III's `ω̃`) holds in
`U_{Sb^θ}(g)` (`CLQ.lin_omegaSLin_eq_zero`), and when `Sb^θ` is the restriction of the
scalars `Sc` of a Rouquier family along the colour map of a restriction datum, the reflected
relations are killed by the admissible evaluation of the family (`omega_rel_restrictQ`).

## Main results

* `omegaLayerMap_lin_wlin`: `Ω` as a weighted layer map is `CLQ.omegaSLin`;
* `omega_rel_restrictQ`: **the reflected black relations with general parameters hold for a
  Rouquier family**.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot KL3.Diagram

universe u₁ u₂

section Omega

variable {I : Type u₁} {C : CartanDatum I} {X Y : Type u₂} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) [DecidableEq I] {k : Type*} [CommRing k]

/-- The inversion of orientations as a weighted layer map is `CLQ.omegaSLin`. -/
theorem omegaLayerMap_lin_wlin {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (omegaLayerMap RD).lin (wlin (omegaSign RD) f) = CLQ.omegaSLin k f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [wlin_zero, LayerMap.lin, Finsupp.mapDomain_zero, map_zero]
  | add f g hf hg => rw [wlin_add, LayerMap.lin_add, hf, hg, map_add]
  | single d r =>
    rw [wlin_single, LayerMap.lin_smul, LayerMap.lin_of, CLQ.omegaSLin_single,
      weight_omegaSign]
    rfl

end Omega

section Relations
open TwoRep Diagrams.BicatInterp

variable {I I' : Type*} {C : CartanDatum I} {C' : CartanDatum I'} {X Y : Type u₂}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y} {W : WeightDatum C' X Y}
  [DecidableEq I] (D : RestrictData RD W)
  (hdot : ∀ i j, C'.dot (D.e i) (D.e j) = C.dot i j)
  {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] (S : RouqFamily (B := B) W)
  [AdditiveWhiskering B] {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (Bicategory.precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (Bicategory.postcomp a g).Linear k]

/-- **The reflected black relations with general parameters hold for a Rouquier family.** The
relations of `U_Q(g)` for the scalars `Sb` (`r = 1`), with orientations inverted by `Ω` (and the
sign of `Ω` on generators), then relabelled into `W` along a restriction datum, are killed by
the admissible interpretation of a Rouquier family for `W` with Cautis–Lauda scalars `Sc`,
Brundan's upward relations and invertible mixed crossings, provided `Sb^θ` is the restriction
of `Sc` and `s` vanishes on the image of the colour map in the degrees below the extremal ones
(outside the extremal degree pairs). -/
theorem omega_rel_restrictQ (Sc : CL.CLScalars C' k) (Sb : CL.CLScalars C k)
    (hθ : KL3.Diagram.CLQ.thetaScalars RD Sb = D.scalars hdot Sc)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s (D.e i) (D.e j) p q = 0)
    (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S)
    (r : (KL3.Diagram.CLQ.pres RD k Sb).Rel) {s t : X}
    (ha : Cond (S := psig RD) s t ((omegaLayerMap RD).obj ((KL3.Diagram.CLQ.pres RD k Sb).dom r)))
    (hb : Cond (S := psig RD) s t ((omegaLayerMap RD).obj ((KL3.Diagram.CLQ.pres RD k Sb).cod r))) :
    admissibleMap (S.genImg Sc) (Cond.map D.sigMap ha) (Cond.map D.sigMap hb)
      (D.sigMap.toLayerMap.lin ((omegaLayerMap RD).lin
        (wlin (omegaSign RD) ((KL3.Diagram.CLQ.pres RD k Sb).rel r)))) = 0 := by
  refine admissibleMap_pull_eq_zero D.sigMap (S.genImg Sc) ha hb _
    (D.pull_eq_zeroQ hdot S Sc ha hb _ ?_)
  have hr : ∀ i, (D.scalars hdot Sc).r i = 1 := fun i => by
    rw [← hθ]; exact KL3.Diagram.CLQ.thetaScalars_r Sb i
  have hrel := fun (i : (CL.presCL RD k (D.scalars hdot Sc)).Rel) {s t : X}
      (ha : Cond (S := psig RD) s t _) (hb : Cond (S := psig RD) s t _) =>
    (S.restrict D).presCL_rel (D.scalars hdot Sc)
      (RouqUpKLR.restrict S D H fun i j _ => D.brundanQ_restrictQ hdot Sc i j)
      (BrundanMixedInversion.restrict S D M) hr hq i ha hb
  have hz : (CL.presCL RD k (D.scalars hdot Sc)).lin ((omegaLayerMap RD).lin
      (wlin (omegaSign RD) ((KL3.Diagram.CLQ.pres RD k Sb).rel r))) = 0 := by
    rw [omegaLayerMap_lin_wlin, ← hθ, ← KL3.Diagram.CLQ.pres_thetaScalars]
    exact KL3.Diagram.CLQ.lin_omegaSLin_eq_zero Sb _ (KL3.Diagram.CLQ.pres_dom_wfQ r)
      ((KL3.Diagram.CLQ.pres RD k Sb).lin_rel_self r)
  rw [← admissibleQuotientMap_lin _ (CL.presCL RD k (D.scalars hdot Sc)) hrel
    Signature.IsEven.odd_eq_false, hz, ← Presentation.lin_zero, admissibleQuotientMap_lin,
    map_zero]

end Relations

end Categorification.Stendhal.DoubleDiagram
