/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLCoordinate
import Categorification.Diagrams.KL3.SymmetryOmega
import Categorification.TwoRep.RouqRestrictSig


/-!
# Black KL relations in the cyclotomic evaluation of double diagrams

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29 (arXiv:1309.3796v2, Lemma 4.28).
The black strands of a double diagram are reflected (by the symmetry `Ω` of KL III) and
relabelled into the extended Cartan datum. This file compares that reflection with the
restriction of a Rouquier family to the black vertices, so that the KL III relations among
black strands are killed by the Cautis–Lauda evaluation.

Generic inputs: functors out of a free 2-category agreeing on layers agree on diagrams
(`functor_map_eq_of_layer`, `freeLift_map_eq_of_layer`), the weighted linear extension of a
layer map (`wlin`, `freeLift_toPresented_eq`) and `Ω` as a weighted layer map
(`lin_omegaLayerMap`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams

universe u₀ u₁ u₂ w₁ w₂ w

variable {S : Signature.{u₀, u₁, u₂}} {E : Type w₁} [Category.{w₂} E]

/-- Two functors out of the free 2-category agreeing (up to the identifications of the
images of well-formed objects) on every layer agree on every diagram with a well-formed
source. -/
theorem functor_map_eq_of_layer (F G : Obj S ⥤ E)
    (hobj : ∀ a : Obj S, a.WF → F.obj a = G.obj a)
    (hlay : ∀ (L : Layer S) (hv : L.Valid), F.map (Diagram.ofLayer L hv) =
      eqToHom (hobj _ hv.wf_dom) ≫ G.map (Diagram.ofLayer L hv) ≫
        eqToHom (hobj _ hv.wf_cod).symm) :
    ∀ {a b : Obj S} (d : a ⟶ b) (ha : a.WF),
      F.map d = eqToHom (hobj a ha) ≫ G.map d ≫
        eqToHom (hobj b ((Diagram.chain d).wf ha)).symm := by
  intro a b d ha
  obtain ⟨ls, h⟩ := d
  induction ls generalizing a with
  | nil =>
    obtain rfl : a = b := by assumption
    have e : (⟨[], rfl⟩ : a ⟶ a) = 𝟙 a := rfl
    rw [e]; simp
  | cons L ls ih =>
    rename_i h
    obtain ⟨hv, rfl, hc⟩ := h
    have : (⟨L :: ls, hv, rfl, hc⟩ : L.dom ⟶ b) =
        Diagram.ofLayer L hv ≫ (⟨ls, hc⟩ : L.cod ⟶ b) := rfl
    rw [this, F.map_comp, G.map_comp, hlay L hv, ih hv.wf_cod hc]
    simp


section Weights

variable {R : Type w} [CommRing R]

/-- Rescale every diagram of a linear combination by its weight. -/
def wlin (χ : S.Gen → R) {a b : Obj S} (f : LinDiagram R a b) : LinDiagram R a b :=
  Finsupp.linearCombination R (fun d : a ⟶ b => Diagram.weight χ d • LinDiagram.of d) f

theorem wlin_add (χ : S.Gen → R) {a b : Obj S} (f g : LinDiagram R a b) :
    wlin χ (f + g) = wlin χ f + wlin χ g :=
  map_add (Finsupp.linearCombination R fun d : a ⟶ b => Diagram.weight χ d • LinDiagram.of d) f g

theorem wlin_zero (χ : S.Gen → R) {a b : Obj S} : wlin χ (0 : LinDiagram R a b) = 0 :=
  map_zero (Finsupp.linearCombination R fun d : a ⟶ b => Diagram.weight χ d • LinDiagram.of d)

theorem wlin_single (χ : S.Gen → R) {a b : Obj S} (d : a ⟶ b) (r : R) :
    wlin χ (Finsupp.single d r : LinDiagram R a b) =
      (r * Diagram.weight χ d) • LinDiagram.of d := by
  rw [wlin, Finsupp.linearCombination_single, smul_smul]

theorem freeLift_toPresented_eq {S' : Signature.{u₀, u₁, u₂}} (ψ : LayerMap S S')
    (Q : Presentation.{w, w₂} S' R) (χ : S.Gen → R) {a b : Obj S} (f : LinDiagram R a b) :
    (freeLift R (ψ.toPresented Q χ)).map f = Q.lin (ψ.lin (wlin χ f)) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [Functor.map_zero, wlin_zero, LayerMap.lin, Finsupp.mapDomain_zero, Q.lin_zero]
  | add f g hf hg =>
    rw [Functor.map_add, hf, hg, wlin_add, ψ.lin_add, Q.lin_add]
  | single d r =>
    rw [freeLift_map_single, wlin_single, ψ.lin_smul, Q.lin_smul, ψ.lin_of, Q.lin_of,
      LayerMap.toPresented_map, smul_smul]

end Weights


section Conj
variable {R : Type w} [CommRing R] [Preadditive E] [Linear R E]

theorem freeLift_map_eq_of_layer (F G : Obj S ⥤ E)
    (hobj : ∀ a : Obj S, a.WF → F.obj a = G.obj a)
    (hlay : ∀ (L : Layer S) (hv : L.Valid), F.map (Diagram.ofLayer L hv) =
      eqToHom (hobj _ hv.wf_dom) ≫ G.map (Diagram.ofLayer L hv) ≫
        eqToHom (hobj _ hv.wf_cod).symm)
    {a b : Obj S} (f : LinDiagram R a b) (ha : a.WF) (hb : b.WF) :
    (freeLift R F).map f = eqToHom (hobj a ha) ≫ (freeLift R G).map f ≫
      eqToHom (hobj b hb).symm := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Functor.map_add, Functor.map_add, hf, hg, Preadditive.add_comp,
      Preadditive.comp_add]
  | single d r =>
    rw [freeLift_map_single, freeLift_map_single,
      functor_map_eq_of_layer F G hobj hlay d ha]
    simp
end Conj


section Omega
open QuantumGroup QuantumGroup.UDot KL3.Diagram

variable {I : Type u₁} {C : CartanDatum I} {X Y : Type u₂} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y)

/-- The inversion of orientations as a layer map of the KL III signature. -/
def omegaLayerMap : LayerMap (psig RD) (psig RD) where
  obj := Omega.obj RD
  layer := Omega.rlay
  valid := Omega.rlay_valid
  dom_eq _ := Omega.rlay_dom _
  cod_eq _ := Omega.rlay_cod _

variable [DecidableEq I] {k : Type w} [CommRing k]

/-- The sign of a KL III generator under the inversion of orientations. -/
def omegaSign (g : (psig RD).Gen) : k := ((Sig.sgnG g : ℤ) : k)

theorem weight_omegaSign {a b : Obj (psig RD)} (d : a ⟶ b) :
    Diagram.weight (omegaSign RD (k := k)) d = ((Sig.sgn (Diagram.layers d) : ℤ) : k) := by
  rw [Diagram.weight, Diagram.weightList, Sig.sgn, Int.cast_list_prod, List.map_map]
  rfl

theorem lin_omegaLayerMap {a b : Obj (psig RD)} (f : LinDiagram k a b) :
    (pres RD k).lin ((omegaLayerMap RD).lin (wlin (omegaSign RD) f)) = omegaL RD k f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [wlin_zero, LayerMap.lin, Finsupp.mapDomain_zero, Presentation.lin_zero,
      omegaL_zero]
  | add f g hf hg => rw [wlin_add, LayerMap.lin_add, Presentation.lin_add, hf, hg, omegaL_add]
  | single d r =>
    rw [wlin_single, LayerMap.lin_smul, Presentation.lin_smul, LayerMap.lin_of,
      Presentation.lin_of, omegaL_single, weight_omegaSign, smul_smul]
    rfl

end Omega


section Restrict
open QuantumGroup QuantumGroup.UDot KL3.Diagram TwoRep Diagrams.BicatInterp

theorem LayerMap.lin_comp' {S₁ S₂ S₃ : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R]
    (φ : LayerMap S₁ S₂) (ψ : LayerMap S₂ S₃) {a b : Obj S₁} (f : LinDiagram R a b) :
    (φ.comp ψ).lin f = ψ.lin (φ.lin f) := by
  change Finsupp.mapDomain _ f = Finsupp.mapDomain _ (Finsupp.mapDomain _ f)
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext d
  exact Diagram.ext (by simp [List.map_map])

/-- An admissible object in the image of a map of signatures whose source is well formed comes
from an admissible object for the regions of its start and end. -/
theorem cond_of_map {S₁ S₂ : Signature.{u₀, u₁, u₂}} (φ : SigMap S₁ S₂) {a : Obj S₁}
    (hwf : a.WF) {s t : S₂.Region} (h : Cond s t (φ.toColourMap.obj a)) :
    s = φ.region a.start ∧ t = φ.region (S₁.endR a.start a.word) ∧
      Cond a.start (S₁.endR a.start a.word) a :=
  by
  obtain ⟨_, ht, hs⟩ := h
  subst hs ht
  exact ⟨rfl, φ.endR_map _ _, hwf, rfl, rfl⟩

end Restrict

section Relations
open QuantumGroup QuantumGroup.UDot KL3.Diagram TwoRep Diagrams.BicatInterp

variable {I I' : Type*} {C : CartanDatum I} {C' : CartanDatum I'} {X Y : Type u₂}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y} {W : WeightDatum C' X Y}
  [DecidableEq I] (D : RestrictData RD W)
  {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] (S : RouqFamily (B := B) W)
  [AdditiveWhiskering B] {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (Bicategory.precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (Bicategory.postcomp a g).Linear k]

/-- **The reflected KL III relations hold for `S`.** The relations of KL III for `RD`, with
orientations inverted by `Ω` (and the sign of `Ω` on generators), then relabelled into `W`
along a restriction datum, are killed by the admissible interpretation of a Rouquier family
for `W` with Brundan's upward relations and invertible mixed crossings, provided its scalars
are those of Khovanov–Lauda on the image of the colour map. -/
theorem omega_rel_restrict (Sc : CL.CLScalars C' k)
    (hdot : ∀ i j, C'.dot (D.e i) (D.e j) = C.dot i j) (ht : ∀ i j, Sc.t (D.e i) (D.e j) = 1)
    (hs : ∀ i j p q, p < C.dij i j → q < C.dij j i → Sc.s (D.e i) (D.e j) p q = 0)
    (H : BrundanUpKLR S Sc)
    (M : BrundanMixedInversion S) (r : (pres RD k).Rel) {s t : X}
    (ha : Cond (S := psig RD) s t ((omegaLayerMap RD).obj ((pres RD k).dom r)))
    (hb : Cond (S := psig RD) s t ((omegaLayerMap RD).obj ((pres RD k).cod r))) :
    admissibleMap (S.genImg Sc) (Cond.map D.sigMap ha) (Cond.map D.sigMap hb)
      (D.sigMap.toLayerMap.lin ((omegaLayerMap RD).lin
        (wlin (omegaSign RD) ((pres RD k).rel r)))) = 0 := by
  refine admissibleMap_pull_eq_zero D.sigMap (S.genImg Sc) ha hb _
    (D.pull_eq_zero S Sc ht ha hb _ ?_)
  have hrel := fun (i : (pres RD k).Rel) {s t : X} (ha : Cond (S := psig RD) s t _)
      (hb : Cond (S := psig RD) s t _) =>
    (S.restrict D).pres_rel_kl k (RouqUpKLR.restrict S D H fun i j _ =>
      D.brundanQ_restrict Sc hdot ht hs i j) (BrundanMixedInversion.restrict S D M) i ha hb
  rw [← admissibleQuotientMap_lin _ (pres RD k) hrel Signature.IsEven.odd_eq_false,
    lin_omegaLayerMap, omegaL_eq_zero_of_wf _ (pres_dom_wf r) ((pres RD k).lin_rel_self r),
    ← Presentation.lin_zero, admissibleQuotientMap_lin, map_zero]

end Relations


end Categorification.Stendhal.DoubleDiagram
