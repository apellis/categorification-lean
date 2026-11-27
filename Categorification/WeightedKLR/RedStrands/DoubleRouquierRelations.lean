/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedBlack
import Categorification.WeightedKLR.RedStrands.DoubleCLMixedPitchfork
import Categorification.WeightedKLR.RedStrands.DoublePresentationUnion

/-!
# Relation families killed by generator images of the double signature

Webster, arXiv:1309.3796v3, proof of Theorem 4.25. The presentation of `𝒯` used here is built
from a base presentation by adjoining families of relations (`Presentation.addRels`,
`Presentation.union`). This file records the predicate that generator images kill every
relation of a presentation in every admissible context (`AdmRelsZero`), which is the input of
`admissiblePseudofunctor`, and shows that it is preserved by adjoining a family whose members
are killed and by unions.

For the generator images of a Rouquier family that are black on the black generators, the
cup pitchfork relations (Webster, arXiv:1309.3796v2, (2.1a) and its mirror) at the scalars
`tⱼᵢ = 1` are killed (`admissibleMap_mixedCupPitchfork`): they are reflections of pitchfork
moves of KL III (`dg_pf_cupUp_down`, `dg_pf_cupDn_down`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory CategoryTheory.Bicategory QuantumGroup QuantumGroup.UDot KL3.Diagram
  StringDiagrams TwoRep Diagrams.BicatInterp

universe w u v w₁

section Families

variable {S : Signature} {B : Type*} [Bicategory B] {M : Model S B} {k : Type*} [CommRing k]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]

/-- **The generator images kill every relation of `P`** in every pair of outer regions. -/
def AdmRelsZero (G : GenImg M) (P : Presentation.{_, w₁} S k) : Prop :=
  ∀ (i : P.Rel) {s t : S.Region} (ha : Cond s t (P.dom i)) (hb : Cond s t (P.cod i)),
    admissibleMap G ha hb (P.rel i) = 0

variable {G : GenImg M}

/-- Adjoining a family of killed relations preserves `AdmRelsZero`. -/
theorem AdmRelsZero.addRels {P : Presentation.{_, w₁} S k} (hP : AdmRelsZero G P) {ι : Type w₁}
    {dom cod : ι → Obj S} {rel : ∀ i, LinDiagram k (dom i) (cod i)}
    (h : ∀ (i : ι) {s t : S.Region} (ha : Cond s t (dom i)) (hb : Cond s t (cod i)),
      admissibleMap G ha hb (rel i) = 0) :
    AdmRelsZero G (P.addRels ι dom cod rel)
  | .inl i => hP i
  | .inr i => h i

/-- The union of two presentations with killed relations has killed relations. -/
theorem AdmRelsZero.union {P P' : Presentation.{_, w₁} S k} (hP : AdmRelsZero G P)
    (hP' : AdmRelsZero G P') : AdmRelsZero G (P.union P') :=
  hP.addRels fun i => hP' i

end Families

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {ℓ : ℕ} {Λ : Fin ℓ → X}

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]
  (S : RouqFamily (B := B) RD)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (Sc : CL.CLScalars C k)
  (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
  (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
    C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
  (hSc : CL.presCL RD k Sc = pres RD k)
  {G : GenImg (doubleModel S red)} (hG : BlackOn Sc G)

include H M hr hq hSc hG

/-- **The cup pitchfork relations act by zero** (Webster, arXiv:1309.3796v2, (2.1a) and its
mirror, at the scalars `tⱼᵢ = 1`, in any signed context). -/
theorem admissibleMap_mixedCupPitchfork [DecidableEq I]
    (P : Presentation.{w, max u v} (signature RD Λ) k) (t : I → I → k) (h1 : ∀ i j, t i j = 1)
    (a : MixedCupPitchfork X I ℓ) {x y : X}
    (ha : Cond x y ((addMixedCupPitchforkRelations RD Λ P t).dom (.inr a)))
    (hb : Cond x y ((addMixedCupPitchforkRelations RD Λ P t).cod (.inr a))) :
    admissibleMap G ha hb ((addMixedCupPitchforkRelations RD Λ P t).rel (.inr a)) = 0 := by
  obtain ⟨d₁, d₂, hrel, e₁, e₂⟩ := addMixedCupPitchforkRelations_rel RD Λ P t a
  rw [hrel, h1, one_smul]
  obtain ⟨μ, L, i, j, R, ord⟩ := a
  cases ord
  · have h₁ : SChain [dn j] ([([dn j], .cup (up i), [])] ++ (crossrL i j).map (whL [] [dn i]))
        [up i, dn j, dn i] := by
      simp [crossrL, whL, Shape.dom, Shape.cod]
    have h₂ : SChain [dn j] [([], .cup (up i), [dn j]), ([up i], .cross false i j, [])]
        [up i, dn j, dn i] := by
      simp [Shape.dom, Shape.cod]
    exact admissibleMap_sub_eq_zero_of_dg S red Sc H M hr hq hSc hG μ L R h₁ h₂
      (dg_pf_cupUp_down RD k j i _).symm rfl rfl d₁ d₂
      (by rw [e₁]; simp [signedLayers, mixedCupPitchforkLayers, upwardMateLayers,
        layers_blackDiagram_mkD, crossrL, whL, blackWord])
      (by rw [e₂]; simp [signedLayers, downCupPitchforkLayers, layers_blackDiagram_mkD,
        blackWord]) ha hb
  · have h₁ : SChain [dn j] ([([], .cup (dn i), [dn j])] ++ (crosslL i j).map (whL [dn i] []))
        [dn i, dn j, up i] := by
      simp [crosslL, whL, Shape.dom, Shape.cod]
    have h₂ : SChain [dn j] [([dn j], .cup (dn i), []), ([], .cross false j i, [up i])]
        [dn i, dn j, up i] := by
      simp [Shape.dom, Shape.cod]
    exact admissibleMap_sub_eq_zero_of_dg S red Sc H M hr hq hSc hG μ L R h₁ h₂
      (dg_pf_cupDn_down RD k i j _).symm rfl rfl d₁ d₂
      (by rw [e₁]; simp [signedLayers, mixedCupPitchforkLayers, upwardMateLayers,
        layers_blackDiagram_mkD, crosslL, whL, blackWord])
      (by rw [e₂]; simp [signedLayers, downCupPitchforkLayers, layers_blackDiagram_mkD,
        blackWord]) ha hb

end Categorification.Stendhal.DoubleDiagram
