/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackNegligibleQ
import Categorification.WeightedKLR.RedStrands.DoubleRouquierPitchforkQ

/-!
# The cup pitchfork relations with general parameters are cover red-negligible

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, and arXiv:1309.3796v2, (2.1a), for
black strands carrying the relations of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3,
Definition 1.1, `r = 1`) for scalars `Sb`. The cup pitchfork relations of
`addMixedCupPitchforkRelations` at the scalars `Sb.t` (the bent branch is `Sb.t_{ji}` times the
straight branch, `j` the through colour and `i` the cup colour) are reflections of the
pitchfork moves `CLQ.dg_pf_cupUp_down`, `CLQ.dg_pf_cupDn_down` of `U_{Sb}(g)`. So their cover
images vanish (`coverLin_mixedCupPitchfork_eq_zeroQ`) and, for the cyclotomic family of a
Kang–Kashiwara family `Q`, they are cover red-negligible at the black scalars `blackScalarsQ`
(`coverRedNegligible_mixedCupPitchforkQ`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

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

include ho in
/-- A difference `d₁ - c • d₂` of two double diagrams whose layers are the reflections of two
diagrams with `[xs₁] = c [xs₂]` in `U_Q(g)` for the scalars `Sb` is sent to zero in
`admissibleKernel`. -/
theorem coverLin_sub_smul_eq_zero_of_dgQ [DecidableEq I] (Sc : CL.CLScalars C' k)
    (Sb : CL.CLScalars C k)
    (hθ : CLQ.thetaScalars RD Sb = (coverRestrict W hC o ho).scalars hC Sc)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s (.inl i) (.inl j) p q = 0)
    (H : BrundanUpKLR S Sc) (Mi : BrundanMixedInversion S)
    (μ : X) (L R : List (DoubleStrand I ℓ))
    {s t : List (Letter I)} {xs₁ xs₂ : List (LayerData I)} (h₁ : SChain s xs₁ t)
    (h₂ : SChain s xs₂ t) (c : k)
    (hdg : NF.dg (CLQ.pres RD k Sb) (endWeight RD Λ μ L) s t xs₁ =
      c • NF.dg (CLQ.pres RD k Sb) (endWeight RD Λ μ L) s t xs₂)
    {a b : Obj (signature RD Λ)} (ha : obj RD Λ μ (L ++ blackWord s ++ R) = a)
    (hb : obj RD Λ μ (L ++ blackWord t ++ R) = b) (d₁ d₂ : a ⟶ b)
    (e₁ : Diagram.layers d₁ =
      Diagram.layers (blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₁ h₁)))
    (e₂ : Diagram.layers d₂ =
      Diagram.layers (blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₂ h₂))) :
    coverLin W hC o (admissibleKernel (S.genImg Sc)) coverSign
      (LinDiagram.of (R := k) d₁ - c • LinDiagram.of d₂) = 0 := by
  subst ha hb
  have f₁ : d₁ = blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₁ h₁) := Diagram.ext e₁
  have f₂ : d₂ = blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₂ h₂) := Diagram.ext e₂
  subst f₁ f₂
  rw [← blackLinear_of, ← blackLinear_of, ← map_smul, ← map_sub]
  have htt : endWeight RD Λ μ (L ++ blackWord t) = endWeight RD Λ μ (L ++ blackWord s) := by
    rw [endWeight_append, endWeight_append, endWeight_blackWord, endWeight_blackWord,
      h₁.wt_eq]
  refine coverLin_blackLinear_eq_zeroQ W hC o ho S Sc Sb hθ hq H Mi μ L R s t rfl htt _ ?_
  rw [Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of, Presentation.lin_of,
    ← NF.dg_of h₁, ← NF.dg_of h₂, hdg, sub_self]

include ho in
/-- **The cup pitchfork relations at the scalars `Sb.t` are sent to zero in
`admissibleKernel`.** -/
theorem coverLin_mixedCupPitchfork_eq_zeroQ [DecidableEq I] (Sc : CL.CLScalars C' k)
    (Sb : CL.CLScalars C k)
    (hθ : CLQ.thetaScalars RD Sb = (coverRestrict W hC o ho).scalars hC Sc)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s (.inl i) (.inl j) p q = 0)
    (H : BrundanUpKLR S Sc) (Mi : BrundanMixedInversion S)
    (P : Presentation.{w, max u v} (signature RD Λ) k) (a : MixedCupPitchfork X I ℓ) :
    coverLin W hC o (admissibleKernel (S.genImg Sc)) coverSign
      ((addMixedCupPitchforkRelations RD Λ P fun i j => (Sb.t i j : k)).rel (.inr a)) = 0 := by
  obtain ⟨d₁, d₂, hrel, e₁, e₂⟩ := addMixedCupPitchforkRelations_rel RD Λ P
    (fun i j => (Sb.t i j : k)) a
  rw [hrel]
  obtain ⟨μ, L, i, j, R, ord⟩ := a
  cases ord
  · have h₁ : SChain [dn j] ([([dn j], .cup (up i), [])] ++ (crossrL i j).map (whL [] [dn i]))
        [up i, dn j, dn i] := by
      simp [crossrL, whL, Shape.dom, Shape.cod]
    have h₂ : SChain [dn j] [([], .cup (up i), [dn j]), ([up i], .cross false i j, [])]
        [up i, dn j, dn i] := by
      simp [Shape.dom, Shape.cod]
    refine coverLin_sub_smul_eq_zero_of_dgQ W hC o ho S Sc Sb hθ hq H Mi μ L R h₁ h₂ _ ?_
      rfl rfl d₁ d₂
      (by rw [e₁]; simp [signedLayers, mixedCupPitchforkLayers, upwardMateLayers,
        layers_blackDiagram_mkD, crossrL, whL, blackWord])
      (by rw [e₂]; simp [signedLayers, downCupPitchforkLayers, layers_blackDiagram_mkD,
        blackWord])
    rw [CLQ.dg_pf_cupUp_down RD k _ j i, smul_smul, Units.mul_inv, one_smul]
  · have h₁ : SChain [dn j] ([([], .cup (dn i), [dn j])] ++ (crosslL i j).map (whL [dn i] []))
        [dn i, dn j, up i] := by
      simp [crosslL, whL, Shape.dom, Shape.cod]
    have h₂ : SChain [dn j] [([dn j], .cup (dn i), []), ([], .cross false j i, [up i])]
        [dn i, dn j, up i] := by
      simp [Shape.dom, Shape.cod]
    refine coverLin_sub_smul_eq_zero_of_dgQ W hC o ho S Sc Sb hθ hq H Mi μ L R h₁ h₂ _ ?_
      rfl rfl d₁ d₂
      (by rw [e₁]; simp [signedLayers, mixedCupPitchforkLayers, upwardMateLayers,
        layers_blackDiagram_mkD, crosslL, whL, blackWord])
      (by rw [e₂]; simp [signedLayers, downCupPitchforkLayers, layers_blackDiagram_mkD,
        blackWord])
    rw [CLQ.dg_pf_cupDn_down RD k _ i j, smul_smul, Units.mul_inv, one_smul]

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
  (cyclotomicCoverPolynomial_monic (k := k)) Wgt L (cyclotomicCoverPolynomial_natDegree (k := k) Λ C) deg
local notation "RDc" => coordinateDatum Λ C

variable (o : I ⊕ Fin ℓ → ℤ)
  (ho : ∀ i : I, (cyclotomicCoverWeightDatum Λ C).pair
    ((cyclotomicCoverWeightDatum Λ C).iY (Sum.inl i)) o = 0)

include ho in
/-- **The cup pitchfork relations at the black scalars are cover red-negligible.** -/
theorem coverRedNegligible_mixedCupPitchforkQ
    (P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k)
    (a : MixedCupPitchfork (I ⊕ Fin ℓ → ℤ) I ℓ) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc
      (coverCL Λ C hQ o ((addMixedCupPitchforkRelations (RDc) (redWeight Wgt) P
        fun i j => ((blackScalarsQ Λ C hQ).t i j : k)).rel (.inr a))) :=
  coverRedNegligible_of_coverLin_admissibleKernel Λ C hQ hc o _
    (coverLin_mixedCupPitchfork_eq_zeroQ Wgt hC o ho (Fam) (Sc) _
      (thetaScalars_blackScalarsQ Λ C hQ o ho) (cover_s_eq_zero Λ C hQ)
      (cover_brundanUpKLR Λ C hQ) (cover_mixedInversion Λ C hQ) P a)

end Categorification.Stendhal
