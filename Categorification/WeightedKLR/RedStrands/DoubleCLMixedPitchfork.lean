/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackNegligible
import Categorification.WeightedKLR.RedStrands.DoubleMixedRedPitchfork

/-!
# The cup pitchfork relations vanish after the cover functor

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, and arXiv:1309.3796v2, (2.1a). The cup
pitchfork relations of `addMixedCupPitchforkRelations`, at the Khovanov–Lauda scalars
`tⱼᵢ = 1`, are reflections of pitchfork moves of a downward strand through a cup of KL III
(`dg_pf_cupUp_down`, `dg_pf_cupDn_down`). So their cover images vanish
(`coverLin_mixedCupPitchfork_eq_zero`) and they are cover red-negligible
(`coverRedNegligible_mixedCupPitchfork`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

/-- **Pitchfork move for a downward strand through the cup `1 ⟶ F_i E_i`**: the cup to the left
of `F_j` followed by the sideways crossing `crossl_{ij}` of its leg `E_i` with `F_j` equals the
cup to the right of `F_j` followed by the downward crossing of `F_j` with the leg `F_i`. -/
theorem dg_pf_cupDn_down (i j : I) (μ : X) :
    dg RD k μ [dn j] [dn i, dn j, up i]
        [([dn j], .cup (dn i), []), ([], .cross false j i, [up i])] =
      dg RD k μ [dn j] [dn i, dn j, up i]
        ([([], .cup (dn i), [dn j])] ++ (crosslL i j).map (whL [dn i] [])) := by
  dat 1 [] [up i] (dg_cycCrossL RD k j i _)
  dswap 0; dswap 1; dswap 2; dswap 3
  dat 4 [dn i, dn j] [] (dg_zigR' RD k _ (dn i))

end Categorification.KL3.Diagram

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams TwoRep

universe w u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {C' : CartanDatum (I ⊕ Fin ℓ)}
  {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (W : WeightDatum C' X Y)
  (hC : ∀ i j, C'.dot (.inl i) (.inl j) = C.dot i j) (o : X)

local notation "RD" => blackDatum W hC
local notation "Λ" => redWeight W

variable (ho : ∀ i, W.pair (W.iY (.inl i)) o = 0)
  {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] (S : RouqFamily (B := B) W)
  [AdditiveWhiskering B] {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (Bicategory.precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (Bicategory.postcomp a g).Linear k]
  [DecidableEq I] (Sc : CL.CLScalars C' k)
  (ht : ∀ i j, Sc.t (.inl i) (.inl j) = 1) (hs : ∀ i j p q, Sc.s (.inl i) (.inl j) p q = 0)
  (H : BrundanUpKLR S Sc) (Mi : BrundanMixedInversion S)

include ho ht hs H Mi

/-- The cup pitchfork relations of `addMixedCupPitchforkRelations` at the scalars `tⱼᵢ = 1`
are sent to zero in `admissibleKernel`. -/
theorem coverLin_mixedCupPitchfork_eq_zero (P : Presentation.{w, max u v} (signature RD Λ) k)
    (t : I → I → k) (h1 : ∀ i j, t i j = 1) (a : MixedCupPitchfork X I ℓ) :
    coverLin W hC o (admissibleKernel (S.genImg Sc)) coverSign
      ((addMixedCupPitchforkRelations RD Λ P t).rel (.inr a)) = 0 := by
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
    exact coverLin_sub_eq_zero_of_dg W hC o ho S Sc ht hs H Mi μ L R h₁ h₂
      (dg_pf_cupUp_down RD k j i _).symm rfl rfl d₁ d₂
      (by rw [e₁]; simp [signedLayers, mixedCupPitchforkLayers, upwardMateLayers,
        layers_blackDiagram_mkD, crossrL, whL, blackWord])
      (by rw [e₂]; simp [signedLayers, downCupPitchforkLayers, layers_blackDiagram_mkD,
        blackWord])
  · have h₁ : SChain [dn j] ([([], .cup (dn i), [dn j])] ++ (crosslL i j).map (whL [dn i] []))
        [dn i, dn j, up i] := by
      simp [crosslL, whL, Shape.dom, Shape.cod]
    have h₂ : SChain [dn j] [([dn j], .cup (dn i), []), ([], .cross false j i, [up i])]
        [dn i, dn j, up i] := by
      simp [Shape.dom, Shape.cod]
    exact coverLin_sub_eq_zero_of_dg W hC o ho S Sc ht hs H Mi μ L R h₁ h₂
      (dg_pf_cupDn_down RD k i j _).symm rfl rfl d₁ d₂
      (by rw [e₁]; simp [signedLayers, mixedCupPitchforkLayers, upwardMateLayers,
        layers_blackDiagram_mkD, crosslL, whL, blackWord])
      (by rw [e₂]; simp [signedLayers, downCupPitchforkLayers, layers_blackDiagram_mkD,
        blackWord])

end Categorification.Stendhal.DoubleDiagram

namespace Categorification.Stendhal

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram

universe u v w

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  (hc : CoverDotCentral Λ C Q)

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
  (cyclotomicCoverPolynomial_monic (k := k)) Wgt L
  (cyclotomicCoverPolynomial_natDegree (k := k) Λ C) deg
local notation "RDc" => coordinateDatum Λ C

variable (o : I ⊕ Fin ℓ → ℤ)
  (ho : ∀ i : I, (cyclotomicCoverWeightDatum Λ C).pair
    ((cyclotomicCoverWeightDatum Λ C).iY (Sum.inl i)) o = 0)
  (ht : ∀ i j : I, (cyclotomicScalars (IsRouquierQ.klrSymm (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
    (IsRouquierQ.polyInY_leading (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
    (cyclotomicCoverWeightDatum Λ C) (IsRouquierQ.polyInY_degree_pair
      (isRouquierQ_cyclotomicCoverQ C Λ Q hQ) (cyclotomicCoverWeightDatum Λ C))).t
      (Sum.inl i) (Sum.inl j) = 1)
  (hs : ∀ (i j : I) (p q : ℕ), (cyclotomicScalars
    (IsRouquierQ.klrSymm (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
    (IsRouquierQ.polyInY_leading (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
    (cyclotomicCoverWeightDatum Λ C) (IsRouquierQ.polyInY_degree_pair
      (isRouquierQ_cyclotomicCoverQ C Λ Q hQ) (cyclotomicCoverWeightDatum Λ C))).s
      (Sum.inl i) (Sum.inl j) p q = 0)

include ho ht hs

/-- **The cup pitchfork relations at the Khovanov–Lauda scalars are cover red-negligible.** -/
theorem coverRedNegligible_mixedCupPitchfork
    (P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k)
    (a : MixedCupPitchfork (I ⊕ Fin ℓ → ℤ) I ℓ) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc
      (coverCL Λ C hQ o ((addMixedCupPitchforkRelations (RDc) (redWeight Wgt) P
        fun _ _ => 1).rel (.inr a))) :=
  coverRedNegligible_of_coverLin_admissibleKernel Λ C hQ hc o _
    (coverLin_mixedCupPitchfork_eq_zero Wgt hC o ho (Fam) (Sc) ht hs
      (cover_brundanUpKLR Λ C hQ) (cover_mixedInversion Λ C hQ) P _ (fun _ _ => rfl) a)

end Categorification.Stendhal
