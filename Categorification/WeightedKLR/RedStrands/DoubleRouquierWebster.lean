/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierAssembly

/-!
# The 2-category `𝒯` and its representation from a Rouquier family

Webster, arXiv:1309.3796v3, Definitions 4.22 and 4.24 and Theorem 4.25. The 2-category `𝒯` is
presented on the double signature by the relations of `𝒰` on black strands, the red cup and
cap relations, the red/upward slides (4.4c,d) and bigons (4.4e), and the KLR relations of
Definition 4.5 on downward strands. Red strands never cross in `𝒯`, so only the downward KLR
relations with at most one red strand are imposed (`addDownRelationsOneRed`), with Webster's
polynomials `stendhalQ` (`tensorTwoCatPresentation`).

The presentation `downwardBlockPresentation` used for Lemma 4.29 and Theorem 4.30 also
imposes the KLR relations between two red strands for the affine cover polynomials; these make
every word with a red label twice vanish. The presentation here does not.

The generator images of a Rouquier family with red lines kill every relation of `𝒯`
(`admRelsZero_tensorTwoCatPresentation`) and define a pseudofunctor out of the presented
2-category (`tensorTwoCatPseudofunctor`), under the conditions of `DoubleRouquierAssembly`
except the vanishing of repeated red labels.
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

/-- The downward KLR relations with at most one red strand, in a signed context. -/
abbrev DownRelationOneRed (X : Type v) (I : Type u) (ℓ : ℕ) :=
  {a : DownRelation X I ℓ // a.rel.dom.word.countP (fun c => c.isRight) ≤ 1}

/-- Adjoin the signed images of the ordinary KLR relations with at most one red strand in every
context (Webster, arXiv:1309.3796v3, Definition 4.24). -/
def addDownRelationsOneRed (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
    (P : Presentation.{w, max u v} (signature RD Λ) k) :
    Presentation.{w, max u v} (signature RD Λ) k :=
  P.addRels (DownRelationOneRed X I ℓ)
    (fun a => downContextObj RD Λ a.1.leftWeight a.1.leftSigned a.1.rightSigned
      (a.1.rel.dom.whisker a.1.left a.1.right))
    (fun a => downContextObj RD Λ a.1.leftWeight a.1.leftSigned a.1.rightSigned
      (a.1.rel.cod.whisker a.1.left a.1.right))
    fun a => downLinear RD Λ k a.1.leftWeight a.1.leftSigned a.1.rightSigned
      (LinDiagram.whisker (KLR.Diagram.relation k Q a.1.rel) a.1.left a.1.right
        (Obj.whiskerOK_of_subsingleton ..))

/-- **The presentation of `𝒯`** (Webster, arXiv:1309.3796v3, Definitions 4.22 and 4.24) over a
base presentation `P`: the red cup and cap relations, the red/upward slides and their mirrors
(4.4c,d), the cup pitchforks at `t = 1`, the black biadjunction, the reflected KL III
relations, the downward KLR relations with at most one red strand for Webster's polynomials
`stendhalQ Q exponents`, the mixed black relations (2.3c), (2.4a), and the red/upward bigons
(4.4e). -/
abbrev tensorTwoCatPresentation (Q : I → I → MvPolynomial (Fin 2) k)
    (exponents : Fin ℓ → I →₀ ℕ) (Sc : CL.CLScalars C k)
    (P : Presentation.{w, max u v} (signature RD Λ) k) :
    Presentation.{w, max u v} (signature RD Λ) k :=
  addRedUpRelations RD Λ k (addMixedBlackRelations RD Λ k Sc.t
    (addDownRelationsOneRed RD Λ (stendhalQ Q exponents)
      (addBlackKLRelations RD Λ (addBlackAdjunctionRelations RD Λ
        (addMixedCupPitchforkRelations RD Λ (addRedUpSlideRelations RD Λ
          (addRedCapRelations RD Λ (addRedCupRelations RD Λ P))) fun _ _ => 1)))))

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

/-- Adjoining the downward KLR relations with at most one red strand preserves `AdmRelsZero`
for the double model; no condition on repeated red labels is needed. -/
theorem AdmRelsZero.addDownRelationsOneRed [DecidableEq I]
    (hP : AdmRelsZero (genImg S red upIso Sc) P) {Qb : I → I → MvPolynomial (Fin 2) k}
    (H : RouqUpKLR S Qb) (n : Fin ℓ → I → ℕ) (hB : DownBigon S red upIso n)
    (hdot : UpIsoDotNatural S red upIso) (hrbb : DownDotCrossNatural S red upIso)
    (hbbr : DownQuotCrossNatural S red upIso) (hbrb : DownMidCrossNatural S red upIso)
    (hmid : DownMidSame S red upIso n)
    (Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
    (hQb : ∀ i j : I, Q (.inl i) (.inl j) = Qb i j)
    (hQir : ∀ (i : I) (r : Fin ℓ), Q (.inl i) (.inr r) = MvPolynomial.X 0 ^ n r i)
    (hQri : ∀ (i : I) (r : Fin ℓ), Q (.inr r) (.inl i) = MvPolynomial.X 1 ^ n r i) :
    AdmRelsZero (genImg S red upIso Sc) (addDownRelationsOneRed RD Λ Q P) :=
  hP.addRels fun a _ _ ha hb =>
    admissibleMap_downRelation_of_bare (genImg S red upIso Sc) Q P a.1
      (fun m _ _ ha' hb' => admissibleMap_downRelation_empty_of_le_one Sc H n hB hdot hrbb hbbr
        hbrb hmid Q hQb hQir hQri m a.1.rel a.2 ha' hb') ha hb

variable (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ) [DecidableEq I]

/-- **The generator images of a Rouquier family with red lines kill the relations of `𝒯`**
(Webster, arXiv:1309.3796v3, proof of Theorem 4.25), when they kill those of the base
presentation. -/
theorem admRelsZero_tensorTwoCatPresentation (hP : AdmRelsZero (genImg S red upIso Sc) P)
    (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
    (hSc : CL.presCL RD k Sc = pres RD k) (HQ : RouqUpKLR S Q)
    (hB : DownBigon S red upIso fun r i => exponents r i) (hdot : UpIsoDotNatural S red upIso)
    (hcross : UpIsoCrossNatural S red upIso Sc)
    (hmid : DownMidSame S red upIso fun r i => exponents r i) :
    AdmRelsZero (genImg S red upIso Sc) (tensorTwoCatPresentation RD Λ Q exponents Sc P) :=
  have hrbb := (upIsoCrossNatural_iff_downDotCrossNatural S Sc red upIso).1 hcross
  have hbbr := (upIsoCrossNatural_iff_downQuotCrossNatural S Sc red upIso H M).1 hcross
  have hbrb := downMidCrossNatural_of_upIsoCrossNatural S Sc red upIso H M hcross
  ((((((((hP.addRedCupRelations).addRedCapRelations).addRedUpSlideRelations hdot
    hcross).addMixedCupPitchforkRelations H M hr hq hSc).addBlackAdjunctionRelations
    H M hr hq hSc).addBlackKLRelations H M hr hq hSc).addDownRelationsOneRed HQ _ hB hdot
    hrbb hbbr hbrb hmid _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)).addMixedBlackRelations
    H M hr hq hSc).addRedUpRelations

/-- **The representation of `𝒯` defined by a Rouquier family with red lines** (Webster,
arXiv:1309.3796v3, Theorem 4.25, for the generic model): the pseudofunctor out of the
presented 2-category `tensorTwoCatPresentation`, read with 1-morphisms from the right region
to the left region, sending a region `μ` to `S.obj μ`, a red line `r` to `red r`, a downward
black strand `i` to `E_i` and an upward one to `F_i`. -/
def tensorTwoCatPseudofunctor [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Additive]
    [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Additive]
    (hP : AdmRelsZero (genImg S red upIso Sc) P)
    (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
    (hSc : CL.presCL RD k Sc = pres RD k) (HQ : RouqUpKLR S Q)
    (hB : DownBigon S red upIso fun r i => exponents r i) (hdot : UpIsoDotNatural S red upIso)
    (hcross : UpIsoCrossNatural S red upIso Sc)
    (hmid : DownMidSame S red upIso fun r i => exponents r i) :
    Pseudofunctor (RevBicat (tensorTwoCatPresentation RD Λ Q exponents Sc P).Bicat) B :=
  admissiblePseudofunctor (genImg S red upIso Sc)
    (admRelsZero_tensorTwoCatPresentation Q exponents hP H M hr hq hSc HQ hB hdot hcross hmid)

end Categorification.Stendhal.DoubleDiagram
