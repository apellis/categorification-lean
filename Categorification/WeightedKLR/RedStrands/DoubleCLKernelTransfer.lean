/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLRedNegligibleIdeal
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackComparison

/-!
# From the admissible kernel to red-negligibility

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The black, mixed and upward red
relations of double diagrams are known to vanish after the cover functor into
`admissibleKernel`, the presentation of all relations of the cyclotomic action. This file
transports such vanishing statements to cover red-negligibility in the Cautis–Lauda
presentation (`coverRedNegligible_of_coverLin_admissibleKernel`).

The comparison goes through the functor between two presentations on one signature whose
relations hold in the second (`quotientFunctor`): it commutes with diagrams, whiskering and
the insertion of images of generators, hence with the reflected images of double linear
combinations (`quotientFunctor_coverLin`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams

section Generic

universe u₀ u₁ u₂ w v₁ v₂

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R]

theorem sigMapId_map {a b : Obj S} (d : a ⟶ b) : (SigMap.id S).toLayerMap.map d = d := by
  obtain ⟨ls, h⟩ := d
  show Diagram.mk _ _ = Diagram.mk ls h
  congr 1
  exact List.map_id'' (fun _ => rfl) ls

theorem sigMapId_lin {a b : Obj S} (f : LinDiagram R a b) :
    (SigMap.id S).toLayerMap.lin f = f := by
  unfold LayerMap.lin
  rw [show ((SigMap.id S).toLayerMap.map : (a ⟶ b) → (a ⟶ b)) = id from funext sigMapId_map]
  exact Finsupp.mapDomain_id

/-- A linear functor applied to the linear extension of a functor is the linear extension of
the composite. -/
theorem map_freeLift_map {E E' : Type*} [Category E] [Preadditive E] [Linear R E] [Category E']
    [Preadditive E'] [Linear R E'] (H : Obj S ⥤ E) (Φ : E ⥤ E') [Φ.Additive] [Φ.Linear R]
    {a b : Obj S} (f : LinDiagram R a b) :
    Φ.map ((freeLift R H).map f) = (freeLift R (H ⋙ Φ)).map f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Functor.map_add, Functor.map_add, Functor.map_add, hf, hg]
  | single d r =>
    rw [freeLift_map_single, freeLift_map_single, Functor.map_smul]
    rfl

variable (P : Presentation.{w, v₁} S R) (Q : Presentation.{w, v₂} S R)

/-- The functor between two presentations on one signature whose relations hold in the
second. -/
def quotientFunctor (h : ∀ r, Q.lin (P.rel r) = 0) : P.Presented ⥤ Q.Presented :=
  (SigMap.id S).lift P (Q := Q) (χ := fun _ => 1) (fun _ => rfl) (fun r => by
    rw [LayerMap.freeLift_toPresented_one, sigMapId_lin]; exact h r)

variable {P Q} (h : ∀ r, Q.lin (P.rel r) = 0)

instance : (quotientFunctor P Q h).Additive := by unfold quotientFunctor; infer_instance

instance : (quotientFunctor P Q h).Linear R := by unfold quotientFunctor; infer_instance

example (a : Obj S) : (quotientFunctor P Q h).obj (P.obj a) = Q.obj a := rfl

theorem quotientFunctor_lin {a b : Obj S} (f : LinDiagram R a b) :
    (quotientFunctor P Q h).map (P.lin f) = Q.lin f := by
  unfold quotientFunctor
  rw [SigMap.lift_lin, LayerMap.freeLift_toPresented_one, sigMapId_lin]

theorem quotientFunctor_diag {a b : Obj S} (d : a ⟶ b) :
    (quotientFunctor P Q h).map (P.diag d) = Q.diag d := by
  unfold quotientFunctor
  rw [SigMap.lift_diag, Diagram.weight_one, one_smul, sigMapId_map]

theorem quotientFunctor_whisk {a b : Obj S} (f : P.obj a ⟶ P.obj b) {u : Obj S}
    {v : List S.Colour} (hw : a.WhiskerOK u v) :
    (quotientFunctor P Q h).map (P.whisk f u v) = Q.whisk ((quotientFunctor P Q h).map f) u v := by
  unfold quotientFunctor
  rw [SigMap.lift_whisk _ _ _ _ hw]
  simp
  rfl

omit [CommRing R] in
/-- Two functors out of the free 2-category agreeing on objects and on every layer are
equal. -/
theorem functor_eq_of_layer {S₀ : Signature.{u₀, u₁, u₂}} {E : Type*} [Category E]
    (F G : Obj S₀ ⥤ E) (hobj : ∀ a, F.obj a = G.obj a)
    (hlay : ∀ (L : Layer S₀) (hv : L.Valid), F.map (Diagram.ofLayer L hv) =
      eqToHom (hobj _) ≫ G.map (Diagram.ofLayer L hv) ≫ eqToHom (hobj _).symm) : F = G := by
  refine CategoryTheory.Functor.ext hobj ?_
  intro a b d
  obtain ⟨ls, hc⟩ := d
  induction ls generalizing a with
  | nil =>
    obtain rfl : a = b := hc
    have e : (⟨[], rfl⟩ : a ⟶ a) = 𝟙 a := rfl
    rw [e]; simp
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := hc
    have : (⟨L :: ls, hv, rfl, hc⟩ : L.dom ⟶ b) =
        Diagram.ofLayer L hv ≫ (⟨ls, hc⟩ : L.cod ⟶ b) := rfl
    rw [this, F.map_comp, G.map_comp, hlay, ih _ hc]
    simp

variable {S₀ : Signature.{u₀, u₁, u₂}} (κ : ColourMap S₀ S)

/-- Inserting images of generators commutes with the quotient functor. -/
theorem ofGen_functor_comp_quotientFunctor
    (img : ∀ g, P.obj (LocalMap.genDom κ g) ⟶ P.obj (LocalMap.genCod κ g)) :
    (LocalMap.ofGen κ img).functor ⋙ quotientFunctor P Q h =
      (LocalMap.ofGen κ (fun g => (quotientFunctor P Q h).map (img g))).functor := by
  refine functor_eq_of_layer _ _ (fun _ => rfl) fun L hv => ?_
  rw [Functor.comp_map, LocalMap.functor_map_ofLayer, LocalMap.functor_map_ofLayer,
    LocalMap.ofGen_layer, LocalMap.ofGen_layer, Functor.map_comp, Functor.map_comp,
    eqToHom_map, eqToHom_map, quotientFunctor_whisk h _ (LocalMap.genDom_whiskerOK κ hv)]
  simp

end Generic

section CoverLin

open QuantumGroup QuantumGroup.UDot KL3.Diagram

variable {I : Type u₀} {ℓ : ℕ} {C : CartanDatum I} {C' : CartanDatum (I ⊕ Fin ℓ)}
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (W : WeightDatum C' X Y)
  (hC : ∀ i j, C'.dot (.inl i) (.inl j) = C.dot i j) (o : X)
  {k : Type w} [CommRing k]

theorem quotientFunctor_coverImage {Q₁ : Presentation.{w, v₁} (psig W) k} {Q₂ : Presentation.{w, v₂} (psig W) k}
    (h : ∀ r, Q₂.lin (Q₁.rel r) = 0) (σ : Move I ℓ → k) (g) :
    (quotientFunctor Q₁ Q₂ h).map (coverImage W hC o Q₁ σ g) = coverImage W hC o Q₂ σ g := by
  rw [coverImage, coverImage, Functor.map_smul, Functor.map_comp, Functor.map_comp, eqToHom_map,
    eqToHom_map, quotientFunctor_diag]

/-- The reflected image of a double linear combination in a quotient presentation is the image
of its reflected image under the quotient functor. -/
theorem quotientFunctor_coverLin {Q₁ : Presentation.{w, v₁} (psig W) k} {Q₂ : Presentation.{w, v₂} (psig W) k}
    (h : ∀ r, Q₂.lin (Q₁.rel r) = 0) (σ : Move I ℓ → k)
    {a b : Obj (signature (blackDatum W hC) (redWeight W))} (f : LinDiagram k a b) :
    (quotientFunctor Q₁ Q₂ h).map (coverLin W hC o Q₁ σ f) = coverLin W hC o Q₂ σ f := by
  have E : (LocalMap.ofGen (coverColourMap W hC o) (coverImage W hC o Q₁ σ)).functor ⋙
      quotientFunctor Q₁ Q₂ h =
      (LocalMap.ofGen (coverColourMap W hC o) (coverImage W hC o Q₂ σ)).functor := by
    rw [ofGen_functor_comp_quotientFunctor]
    congr
    funext g
    exact quotientFunctor_coverImage W hC o h σ g
  rw [coverLin, coverLin, map_freeLift_map,
    CategoryTheory.Functor.congr_hom (congrArg (freeLift k) E)]
  simp

end CoverLin

end Categorification.Stendhal.DoubleDiagram

namespace Categorification.Stendhal

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram

universe u v w

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  (hc : CoverDotCentral Λ C Q)

local notation "D" => I ⊕ Fin ℓ
local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "Sc" => cyclotomicScalars sym lead Wgt deg
local notation "hC" => extendedCartanDatum_dot_inl Λ C
local notation "L" => cyclotomicCoverHighest (I := I) (ℓ := ℓ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "Fam" => cyclotomicFamily.{u, v, w} sym lead
  (cyclotomicCoverPolynomial_monic (k := k)) Wgt L (cyclotomicCoverPolynomial_natDegree (k := k) Λ C) deg
local notation "PCL" => KL3.Diagram.CL.presCL Wgt k Sc
set_option quotPrecheck false in
set_option hygiene false in
local notation "AK" => admissibleKernel (k := k) (RouqFamily.genImg Fam Sc)

/-- **Relations of the admissible kernel are cover red-negligible.** If the reflected image of
a double linear combination vanishes in the presentation of the relations of the cyclotomic
action, its reflected image in the Cautis–Lauda presentation is cover red-negligible: all its
admissible components vanish. -/
theorem coverRedNegligible_of_coverLin_admissibleKernel (o : D → ℤ)
    {a b : Obj (signature (coordinateDatum Λ C) (redWeight Wgt))} (f : LinDiagram k a b)
    (hf : coverLin Wgt hC o AK coverSign f = 0) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc (coverCL Λ C hQ o f) := by
  have hrel : ∀ r, (AK).lin ((PCL).rel r) = 0 := fun r =>
    admissibleKernel_lin_eq_zero _ _ fun _ _ ha hb => presCL_cover_rel Λ C hQ r ha hb
  intro s t ha hb
  obtain ⟨g, hg⟩ := (PCL).lin_surjective (coverCL Λ C hQ o f)
  have hg0 : (AK).lin g = 0 := by
    rw [← quotientFunctor_lin hrel, hg, coverCL, quotientFunctor_coverLin, hf]
  have e := admissibleQuotientMap_lin (RouqFamily.genImg Fam Sc) AK
    (admissibleKernel_rel _) Signature.IsEven.odd_eq_false ha hb g
  rw [hg0, admissibleQuotientMap_zero] at e
  rw [← hg]
  change CoverRed.{u, v, w} Λ C hQ hc (admissibleMap _ ha hb g)
  rw [← e]
  exact CoverRed.zero

end Categorification.Stendhal
