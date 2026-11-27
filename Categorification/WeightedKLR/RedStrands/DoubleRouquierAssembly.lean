/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRelations
import Categorification.WeightedKLR.RedStrands.DoubleRouquierDownAll
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedDownMid
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedContext
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedUp
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedUpSlideContext
import Categorification.WeightedKLR.RedStrands.DoubleCapPresentation
import Categorification.Diagrams.BicatInterpAdmissiblePseudo

/-!
# The relations of the downward block in the double model of a Rouquier family

Webster, arXiv:1309.3796v3, proof of Theorem 4.25. The presentation of the double tensor
product 2-category used for Lemma 4.29 and Theorem 4.30 adjoins to a base presentation the red
cup and cap relations, the red/upward slides (4.4c,d) and bigons (4.4e), the cup pitchforks,
the black biadjunction, the reflected black KL III relations, the mixed black relations
(2.3c), (2.4a), and the KL relations on downward strands (Definition 4.24)
(`downwardBlockPresentation`). This file shows that the generator images of a Rouquier family
with red lines kill every one of these relations (`admRelsZero_downwardBlockPresentation`),
so that they define a pseudofunctor out of the presented 2-category
(`downwardBlockPseudofunctor`, by `admissiblePseudofunctor`).

The hypotheses are properties of the Rouquier family and of the images of the red strands and
red/upward crossings: the black part is a 2-representation of the Khovanov–Lauda 2-category
(`BrundanUpKLR`, `BrundanMixedInversion`, the scalar conditions, `BlackOn`), the downward
strands satisfy the KLR relations for the downward polynomials (`RouqUpKLR`), and the red/upward
crossings satisfy the naturality and bigon conditions of `DoubleRouquierDownAll` and
`DoubleRouquierRedUpSlide`. The naturality of the red/down crossings for downward crossings
follows from that of the red/up crossings for upward crossings by mates
(`DoubleRouquierRedDownMates`, `DoubleRouquierRedDownMid`). The remaining conditions are to be
discharged for the cyclotomic region model.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram
  StringDiagrams TwoRep Diagrams.BicatInterp

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {ℓ : ℕ} {Λ : Fin ℓ → X}

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]
  {S : RouqFamily (B := B) RD}
  {red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x)}
  {upIso : (r : Fin ℓ) → (i : I) → {μ μ₁ μ₂ μ₃ : X} → (h₁ : μ + RD.iX i = μ₁) →
    (h₂ : μ + Λ r = μ₂) → (h₃ : μ₁ + Λ r = μ₃) → (h₄ : μ₂ + RD.iX i = μ₃) →
    (S.F i h₄ ≫ red r h₂ ≅ red r h₃ ≫ S.F i h₁)}
  {Sc : CL.CLScalars C k}
  {P : Presentation.{w, max u v} (signature RD Λ) k}


section Red

/-- Adjoining the red cup relations preserves `AdmRelsZero` for the double model. -/
theorem AdmRelsZero.addRedCupRelations (hP : AdmRelsZero (genImg S red upIso Sc) P) :
    AdmRelsZero (genImg S red upIso Sc) (addRedCupRelations RD Λ P) :=
  hP.addRels fun a _ _ ha hb =>
    genImg_redCup (S := S) (red := red) (upIso := upIso) (Sc := Sc) a ha hb

/-- Adjoining the red cap relations preserves `AdmRelsZero` for the double model. -/
theorem AdmRelsZero.addRedCapRelations (hP : AdmRelsZero (genImg S red upIso Sc) P) :
    AdmRelsZero (genImg S red upIso Sc) (addRedCapRelations RD Λ P) :=
  hP.addRels fun a _ _ ha hb =>
    genImg_redCap (S := S) (red := red) (upIso := upIso) (Sc := Sc) a ha hb

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k] in
/-- Adjoining the red/upward bigons (4.4e) preserves `AdmRelsZero` for the double model. -/
theorem AdmRelsZero.addRedUpRelations (hP : AdmRelsZero (genImg S red upIso Sc) P) :
    AdmRelsZero (genImg S red upIso Sc) (addRedUpRelations RD Λ k P) :=
  hP.addRels fun a _ _ ha hb =>
    genImg_redUp (S := S) (red := red) (upIso := upIso) (Sc := Sc) a ha hb

/-- Adjoining the red/upward slides (4.4c,d) and their mirrors preserves `AdmRelsZero` for the
double model. -/
theorem AdmRelsZero.addRedUpSlideRelations (hP : AdmRelsZero (genImg S red upIso Sc) P)
    (hdot : UpIsoDotNatural S red upIso)
    (hcross : UpIsoCrossNatural S red upIso Sc) :
    AdmRelsZero (genImg S red upIso Sc) (addRedUpSlideRelations RD Λ P) :=
  hP.addRels fun ⟨μ, u, r, g, v, mirror⟩ _ _ ha hb => by
    cases mirror
    · exact genImg_redUpSlide S red upIso Sc hdot hcross μ u r g v ha hb
    · exact genImg_redUpSlideMirror S red upIso Sc hdot hcross μ u r g v ha hb

/-- Adjoining the downward KLR relations preserves `AdmRelsZero` for the double model. -/
theorem AdmRelsZero.addDownRelations [DecidableEq I] (hP : AdmRelsZero (genImg S red upIso Sc) P)
    {Qb : I → I → MvPolynomial (Fin 2) k}
    (H : RouqUpKLR S Qb) (n : Fin ℓ → I → ℕ) (hB : DownBigon S red upIso n)
    (hdot : UpIsoDotNatural S red upIso) (hrbb : DownDotCrossNatural S red upIso)
    (hbbr : DownQuotCrossNatural S red upIso) (hbrb : DownMidCrossNatural S red upIso)
    (hmid : DownMidSame S red upIso n) (hrep : RepeatedRedZero S red)
    (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
    (hQb : ∀ i j : I, Q (.inl i) (.inl j) = Qb i j)
    (hQir : ∀ (i : I) (r : Fin ℓ), Q (.inl i) (.inr r) = MvPolynomial.X 0 ^ n r i)
    (hQri : ∀ (i : I) (r : Fin ℓ), Q (.inr r) (.inl i) = MvPolynomial.X 1 ^ n r i)
    (hQrr : ∀ s t : Fin ℓ, MvPolynomial.constantCoeff (Q (.inr s) (.inr t)) = 0) :
    AdmRelsZero (genImg S red upIso Sc) (addDownRelations RD Λ Q P) :=
  hP.addRels fun a _ _ ha hb =>
    admissibleMap_downRelation Sc H n hB hdot hrbb hbbr hbrb hmid hrep Q hQb hQir hQri hQrr P a
      ha hb

end Red

section Black

variable [DecidableEq I] (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S)
  (hr : ∀ i, Sc.r i = 1)
  (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
    C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
  (hSc : CL.presCL RD k Sc = pres RD k)
include H M hr hq hSc

/-- Adjoining the mixed black relations (2.3c), (2.4a) preserves `AdmRelsZero` for the double
model. -/
theorem AdmRelsZero.addMixedBlackRelations (hP : AdmRelsZero (genImg S red upIso Sc) P) :
    AdmRelsZero (genImg S red upIso Sc) (addMixedBlackRelations RD Λ k Sc.t P) :=
  hP.addRels fun a _ _ ha hb =>
    admissibleMap_mixedBlackRelation S red Sc H M hr hq hSc (genImg_blackOn S red upIso Sc) P a
      ha hb

/-- Adjoining the black biadjunction relations preserves `AdmRelsZero` for the double model. -/
theorem AdmRelsZero.addBlackAdjunctionRelations (hP : AdmRelsZero (genImg S red upIso Sc) P) :
    AdmRelsZero (genImg S red upIso Sc) (addBlackAdjunctionRelations RD Λ P) :=
  hP.addRels fun a _ _ ha hb =>
    admissibleMap_blackAdjunction S red Sc H M hr hq hSc (genImg_blackOn S red upIso Sc) P a
      ha hb

/-- Adjoining the reflected black KL III relations preserves `AdmRelsZero` for the double
model. -/
theorem AdmRelsZero.addBlackKLRelations (hP : AdmRelsZero (genImg S red upIso Sc) P) :
    AdmRelsZero (genImg S red upIso Sc) (addBlackKLRelations RD Λ P) :=
  hP.addRels fun r _ _ ha hb =>
    admissibleMap_blackMirror_rel S Sc H M hr hq red hSc (genImg_blackOn S red upIso Sc) r ha hb

/-- Adjoining the cup pitchfork relations at the scalars `tⱼᵢ = 1` preserves `AdmRelsZero` for
the double model. -/
theorem AdmRelsZero.addMixedCupPitchforkRelations (hP : AdmRelsZero (genImg S red upIso Sc) P) :
    AdmRelsZero (genImg S red upIso Sc) (addMixedCupPitchforkRelations RD Λ P fun _ _ => 1) :=
  hP.addRels fun a _ _ ha hb =>
    admissibleMap_mixedCupPitchfork S red Sc H M hr hq hSc (genImg_blackOn S red upIso Sc) P _
      (fun _ _ => rfl) a ha hb

end Black

section Block

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)

/-- **The presentation of the downward block**: the presentation `signedCapKLPresentation` of
the cap and braid moves (Webster, arXiv:1309.3796v2, Definition 4.27) at the scalars `t = 1`,
with the downward KLR relations, the mixed black relations and the red/upward bigons adjoined
again on top. At the coordinate datum, the Khovanov–Lauda scalars and the Cautis–Lauda dual
polynomials this is `clDownwardBlock`. -/
abbrev downwardBlockPresentation (P : Presentation.{w, max u v} (signature RD Λ) k)
    (Sc : CL.CLScalars C k) : Presentation.{w, max u v} (signature RD Λ) k :=
  addRedUpRelations RD Λ k (addMixedBlackRelations RD Λ k Sc.t
    (addDownRelations RD Λ (affineCoverQ Q exponents)
      (signedCapKLPresentation RD Λ P Q exponents fun _ _ => 1)))

variable [DecidableEq I]

/-- **The generator images of a Rouquier family with red lines kill the relations of the
downward block** (Webster, arXiv:1309.3796v3, proof of Theorem 4.25), when they kill those of
the base presentation. -/
theorem admRelsZero_downwardBlockPresentation (hP : AdmRelsZero (genImg S red upIso Sc) P)
    (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
    (hSc : CL.presCL RD k Sc = pres RD k) (HQ : RouqUpKLR S Q)
    (hB : DownBigon S red upIso fun r i => exponents r i) (hdot : UpIsoDotNatural S red upIso)
    (hcross : UpIsoCrossNatural S red upIso Sc)
    (hmid : DownMidSame S red upIso fun r i => exponents r i) (hrep : RepeatedRedZero S red) :
    AdmRelsZero (genImg S red upIso Sc) (downwardBlockPresentation Q exponents P Sc) := by
  have hrbb := (upIsoCrossNatural_iff_downDotCrossNatural S Sc red upIso).1 hcross
  have hbbr := (upIsoCrossNatural_iff_downQuotCrossNatural S Sc red upIso H M).1 hcross
  have hbrb := downMidCrossNatural_of_upIsoCrossNatural S Sc red upIso H M hcross
  have hQb : ∀ i j : I, affineCoverQ Q exponents (.inl i) (.inl j) = Q i j := fun _ _ => rfl
  have hQir : ∀ (i : I) (r : Fin ℓ), affineCoverQ Q exponents (.inl i) (.inr r) =
      MvPolynomial.X 0 ^ exponents r i := fun _ _ => rfl
  have hQri : ∀ (i : I) (r : Fin ℓ), affineCoverQ Q exponents (.inr r) (.inl i) =
      MvPolynomial.X 1 ^ exponents r i := fun _ _ => rfl
  have hQrr : ∀ s t : Fin ℓ,
      MvPolynomial.constantCoeff (affineCoverQ Q exponents (.inr s) (.inr t)) = 0 := by
    intro s t
    simp [affineCoverQ]
  have down : ∀ {P' : Presentation.{w, max u v} (signature RD Λ) k},
      AdmRelsZero (genImg S red upIso Sc) P' →
      AdmRelsZero (genImg S red upIso Sc) (addDownRelations RD Λ (affineCoverQ Q exponents) P') :=
    fun h => h.addDownRelations HQ _ hB hdot hrbb hbbr hbrb hmid hrep _ hQb hQir hQri hQrr
  have h₁ := (((hP.addRedCupRelations).addRedCapRelations).addRedUpSlideRelations hdot
    hcross).addRedUpRelations
  have h₂ := down ((h₁.addMixedCupPitchforkRelations H M hr hq hSc).addBlackAdjunctionRelations
    H M hr hq hSc)
  have h₃ := (down hP.addRedUpRelations).addRedCapRelations
  have h₄ := ((hP.addBlackKLRelations H M hr hq hSc).addRedCupRelations).addRedCapRelations
  have h₅ := down h₄.addRedUpRelations
  have h₆ := (h₂.union h₃).union h₅
  exact ((down h₆).addMixedBlackRelations H M hr hq hSc).addRedUpRelations

/-- **The representation of the downward block defined by a Rouquier family with red lines**
(Webster, arXiv:1309.3796v3, Theorem 4.25, for the generic model): the pseudofunctor out of the
presented 2-category of `downwardBlockPresentation`, read with 1-morphisms from the right region
to the left region, sending a region `μ` to `S.obj μ`, a red line `r` to `red r`, a downward
black strand `i` to `E_i` and an upward one to `F_i`. -/
def downwardBlockPseudofunctor [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Additive]
    [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Additive]
    (hP : AdmRelsZero (genImg S red upIso Sc) P)
    (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
    (hSc : CL.presCL RD k Sc = pres RD k) (HQ : RouqUpKLR S Q)
    (hB : DownBigon S red upIso fun r i => exponents r i) (hdot : UpIsoDotNatural S red upIso)
    (hcross : UpIsoCrossNatural S red upIso Sc)
    (hmid : DownMidSame S red upIso fun r i => exponents r i) (hrep : RepeatedRedZero S red) :
    Pseudofunctor (RevBicat (downwardBlockPresentation Q exponents P Sc).Bicat) B :=
  admissiblePseudofunctor (genImg S red upIso Sc)
    (admRelsZero_downwardBlockPresentation Q exponents hP H M hr hq hSc HQ hB hdot hcross hmid
      hrep)

end Block

end Categorification.Stendhal.DoubleDiagram
