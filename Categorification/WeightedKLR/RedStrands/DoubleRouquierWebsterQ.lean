/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierWebster
import Categorification.WeightedKLR.RedStrands.DoubleRouquierPitchforkQ

/-!
# The 2-category `𝒯` for general black parameters and its representation

Webster, arXiv:1309.3796v3, Definitions 4.22 and 4.24 and Theorem 4.25, for general black
parameters. For Cautis–Lauda scalars `W`, the presentation `tensorTwoCatPresentationQ` of `𝒯`
imposes on black strands the reflected relations of `U_W(g)`, the black biadjunction, the
mixed black relations (2.3c), (2.4a) with the scalars `t` of `W` and the cup pitchforks with the
scalars `tⱼᵢ`; the red relations and the downward KLR relations with at most one red strand
are those of `tensorTwoCatPresentation`.

A Rouquier family carrying an action of `U_Sc(g)` with `r = 1` acts on `𝒯` at the reflected
scalars `W = Sc^θ = CLQ.thetaScalars RD Sc` (`admRelsZero_tensorTwoCatPresentationQ`,
`tensorTwoCatPseudofunctorQ`): the vertical reflection with inverted orientations carries
`U_Sc(g)` to `U_{Sc^θ}(g)` (`CLQ.lin_thetaLin_eq_zero`). With `r = 1` the map `Sc ↦ Sc^θ` is an
involution (`CLQ.thetaScalars_thetaScalars`), so every `W` with `r = 1` arises, from the family
scalars `W^θ`. Unlike `tensorTwoCatPseudofunctor`, no hypothesis identifies `U_Sc(g)` with the
KL III presentation.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram
  StringDiagrams TwoRep Diagrams.BicatInterp

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
  {ℓ : ℕ} (Λ : Fin ℓ → X) {k : Type w} [CommRing k]

/-- **The presentation of `𝒯` for the black scalars `W`** (Webster, arXiv:1309.3796v3,
Definitions 4.22 and 4.24) over a base presentation `P`: the red cup and cap relations, the
red/upward slides and their mirrors (4.4c,d), the cup pitchforks with the scalars `tⱼᵢ` of `W`,
the black biadjunction, the reflected relations of `U_W(g)`, the downward KLR relations with at
most one red strand for Webster's polynomials `stendhalQ Q exponents`, the mixed black
relations (2.3c), (2.4a) with the scalars of `W`, and the red/upward bigons (4.4e). -/
abbrev tensorTwoCatPresentationQ (Q : I → I → MvPolynomial (Fin 2) k)
    (exponents : Fin ℓ → I →₀ ℕ) (W : CL.CLScalars C k)
    (P : Presentation.{w, max u v} (signature RD Λ) k) :
    Presentation.{w, max u v} (signature RD Λ) k :=
  addRedUpRelations RD Λ k (addMixedBlackRelations RD Λ k W.t
    (addDownRelationsOneRed RD Λ (stendhalQ Q exponents)
      (addBlackRelationsOf RD Λ (CLQ.pres RD k W) (addBlackAdjunctionRelations RD Λ
        (addMixedCupPitchforkRelations RD Λ (addRedUpSlideRelations RD Λ
          (addRedCapRelations RD Λ (addRedCupRelations RD Λ P))) fun i j => (W.t i j : k))))))

variable {RD Λ}

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]
  {S : RouqFamily (B := B) RD}
  {red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x)}
  {upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁)}
  {Sc : CL.CLScalars C k}
  {P : Presentation.{w, max u v} (signature RD Λ) k}

section Black

variable [DecidableEq I] (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S)
  (hr : ∀ i, Sc.r i = 1)
  (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
    C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
include H M hr hq

/-- Adjoining the mixed black relations (2.3c), (2.4a) with the reflected scalars preserves
`AdmRelsZero` for the double model. -/
theorem AdmRelsZero.addMixedBlackRelationsQ (hP : AdmRelsZero (genImg S red upIso Sc) P) :
    AdmRelsZero (genImg S red upIso Sc)
      (DoubleDiagram.addMixedBlackRelations RD Λ k (CLQ.thetaScalars RD Sc).t P) :=
  hP.addRels fun a _ _ ha hb =>
    admissibleMap_mixedBlackRelationQ S red Sc H M hr hq (genImg_blackOn S red upIso Sc) P a
      ha hb

/-- Adjoining the black biadjunction relations preserves `AdmRelsZero` for the double model,
for all scalars with `r = 1`. -/
theorem AdmRelsZero.addBlackAdjunctionRelationsQ (hP : AdmRelsZero (genImg S red upIso Sc) P) :
    AdmRelsZero (genImg S red upIso Sc) (DoubleDiagram.addBlackAdjunctionRelations RD Λ P) :=
  hP.addRels fun a _ _ ha hb =>
    admissibleMap_blackAdjunctionQ S red Sc H M hr hq (genImg_blackOn S red upIso Sc) P a ha hb

/-- Adjoining the reflected relations of `U_{Sc^θ}(g)` preserves `AdmRelsZero` for the double
model. -/
theorem AdmRelsZero.addBlackRelationsOfQ (hP : AdmRelsZero (genImg S red upIso Sc) P) :
    AdmRelsZero (genImg S red upIso Sc)
      (DoubleDiagram.addBlackRelationsOf RD Λ (CLQ.pres RD k (CLQ.thetaScalars RD Sc)) P) :=
  hP.addRels fun r _ _ ha hb =>
    admissibleMap_blackMirror_relQ S Sc H M hr hq red (genImg_blackOn S red upIso Sc) r ha hb

/-- Adjoining the cup pitchfork relations with the reflected scalars preserves `AdmRelsZero`
for the double model. -/
theorem AdmRelsZero.addMixedCupPitchforkRelationsQ
    (hP : AdmRelsZero (genImg S red upIso Sc) P) :
    AdmRelsZero (genImg S red upIso Sc) (DoubleDiagram.addMixedCupPitchforkRelations RD Λ P
      fun i j => ((CLQ.thetaScalars RD Sc).t i j : k)) :=
  hP.addRels fun a _ _ ha hb =>
    admissibleMap_mixedCupPitchforkQ S red Sc H M hr hq (genImg_blackOn S red upIso Sc) P a ha hb

end Black

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) [DecidableEq I]

/-- **The generator images of a Rouquier family with red lines kill the relations of `𝒯` at
the reflected scalars** (Webster, arXiv:1309.3796v3, proof of Theorem 4.25, for general black
parameters), when they kill those of the base presentation. -/
theorem admRelsZero_tensorTwoCatPresentationQ (hP : AdmRelsZero (genImg S red upIso Sc) P)
    (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
    (HQ : RouqUpKLR S Q)
    (hB : DownBigon S red upIso fun r i => exponents r i) (hdot : UpIsoDotNatural S red upIso)
    (hcross : UpIsoCrossNatural S red upIso Sc)
    (hmid : DownMidSame S red upIso fun r i => exponents r i) :
    AdmRelsZero (genImg S red upIso Sc)
      (tensorTwoCatPresentationQ RD Λ Q exponents (CLQ.thetaScalars RD Sc) P) :=
  have hrbb := (upIsoCrossNatural_iff_downDotCrossNatural S Sc red upIso).1 hcross
  have hbbr := (upIsoCrossNatural_iff_downQuotCrossNatural S Sc red upIso H M).1 hcross
  have hbrb := downMidCrossNatural_of_upIsoCrossNatural S Sc red upIso H M hcross
  ((((((((hP.addRedCupRelations).addRedCapRelations).addRedUpSlideRelations hdot
    hcross).addMixedCupPitchforkRelationsQ H M hr hq).addBlackAdjunctionRelationsQ
    H M hr hq).addBlackRelationsOfQ H M hr hq).addDownRelationsOneRed HQ _ hB hdot
    hrbb hbbr hbrb hmid _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)).addMixedBlackRelationsQ
    H M hr hq).addRedUpRelations

/-- **The representation of `𝒯` defined by a Rouquier family with red lines, for general black
parameters** (Webster, arXiv:1309.3796v3, Theorem 4.25, for the generic model): for a family
carrying an action of `U_Sc(g)` with `r = 1`, the pseudofunctor out of the presented 2-category
`tensorTwoCatPresentationQ` at the reflected scalars `Sc^θ`, read with 1-morphisms from the
right region to the left region, sending a region `μ` to `S.obj μ`, a red line `r` to `red r`,
a downward black strand `i` to `E_i` and an upward one to `F_i`. -/
def tensorTwoCatPseudofunctorQ [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Additive]
    [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Additive]
    (hP : AdmRelsZero (genImg S red upIso Sc) P)
    (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
    (HQ : RouqUpKLR S Q)
    (hB : DownBigon S red upIso fun r i => exponents r i) (hdot : UpIsoDotNatural S red upIso)
    (hcross : UpIsoCrossNatural S red upIso Sc)
    (hmid : DownMidSame S red upIso fun r i => exponents r i) :
    Pseudofunctor (RevBicat
      (tensorTwoCatPresentationQ RD Λ Q exponents (CLQ.thetaScalars RD Sc) P).Bicat) B :=
  admissiblePseudofunctor (genImg S red upIso Sc)
    (admRelsZero_tensorTwoCatPresentationQ Q exponents hP H M hr hq HQ hB hdot hcross hmid)

end Categorification.Stendhal.DoubleDiagram
