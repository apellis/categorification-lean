/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedBlackQ
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRelations

/-!
# The cup pitchfork relations for general black parameters

Webster, arXiv:1309.3796v3, proof of Theorem 4.25, and arXiv:1309.3796v2, (2.1a) and its
mirror, for general black parameters. In `U_Q(g)` the downward pitchfork moves through a cup
carry the scalar `tⱼᵢ` of the crossing of the through strand `j` with the cup colour `i`
(`CLQ.dg_pf_cupUp_down`, `CLQ.dg_pf_cupDn_down`). So for generator images of a Rouquier family
with the scalars `Sc` on the black generators, the cup pitchfork relations with the scalars
`t^θ` of `Sc^θ = CLQ.thetaScalars RD Sc` act by zero (`admissibleMap_mixedCupPitchforkQ`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)

/-- **Pitchfork move for a downward strand through the cup `1 ⟶ F_i E_i`** in `U_Q(g)`: the
cup to the right of `F_j` followed by the downward crossing of `F_j` with the leg `F_i` is
`tⱼᵢ⁻¹` times the cup to the left of `F_j` followed by the sideways crossing `crossl_{ij}` of
its leg `E_i` with `F_j`. -/
theorem dg_pf_cupDn_down (i j : I) (μ : X) :
    NF.dg (pres RD k sc) μ [dn j] [dn i, dn j, up i]
        [([dn j], .cup (dn i), []), ([], .cross false j i, [up i])] =
      (((sc.t j i)⁻¹ : kˣ) : k) •
          NF.dg (pres RD k sc) μ [dn j] [dn i, dn j, up i]
            ([([], .cup (dn i), [dn j])] ++ (crosslL i j).map (whL [dn i] [])) := by
  refine Eq.trans (NF.dg_step_at_smul _ 1 [] [up i] _ (dg_cycCrossL RD k sc j i _)
    (by (try dnorm); schain) (by (try dnorm); schain) (by dnorm)) ?_
  try dnorm
  congr 1
  dswapQ 0; dswapQ 1; dswapQ 2; dswapQ 3
  datQ 4 [dn i, dn j] [] (NF.dg_zigR' (pres RD k sc) _ (dn i))

end Categorification.KL3.Diagram.CLQ

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
  (S : RouqFamily (B := B) RD)
  (red : (r : Fin ℓ) → {x y : X} → x + Λ r = y → (S.obj y ⟶ S.obj x))
  (Sc : CL.CLScalars C k)
  (H : BrundanUpKLR S Sc) (M : BrundanMixedInversion S) (hr : ∀ i, Sc.r i = 1)
  (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
    C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s i j p q = 0)
  {G : GenImg (doubleModel S red)} (hG : BlackOn Sc G)

include H M hr hq hG

/-- A difference `d₁ - c • d₂` of two double diagrams whose layers are the reflections of two
normal-form diagrams with `[xs₁] = c [xs₂]` in `U_{Sc^θ}(g)` acts by zero. -/
theorem admissibleMap_sub_smul_eq_zero_of_dgQ [DecidableEq I] (μ : X)
    (L R : List (DoubleStrand I ℓ)) {s t : List (Letter I)} {xs₁ xs₂ : List (LayerData I)}
    (h₁ : SChain s xs₁ t) (h₂ : SChain s xs₂ t) (c : k)
    (hdg : NF.dg (CLQ.pres RD k (CLQ.thetaScalars RD Sc)) (endWeight RD Λ μ L) s t xs₁ =
      c • NF.dg (CLQ.pres RD k (CLQ.thetaScalars RD Sc)) (endWeight RD Λ μ L) s t xs₂)
    {a b : Obj (signature RD Λ)} (ha : obj RD Λ μ (L ++ blackWord s ++ R) = a)
    (hb : obj RD Λ μ (L ++ blackWord t ++ R) = b) (d₁ d₂ : a ⟶ b)
    (e₁ : Diagram.layers d₁ =
      Diagram.layers (blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₁ h₁)))
    (e₂ : Diagram.layers d₂ =
      Diagram.layers (blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₂ h₂)))
    {x y : X} (ha' : Cond x y a) (hb' : Cond x y b) :
    admissibleMap G ha' hb' (LinDiagram.of (R := k) d₁ - c • LinDiagram.of d₂) = 0 := by
  subst ha hb
  have f₁ : d₁ = blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₁ h₁) := Diagram.ext e₁
  have f₂ : d₂ = blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₂ h₂) := Diagram.ext e₂
  subst f₁ f₂
  rw [← blackLinear_of, ← blackLinear_of, ← map_smul, ← map_sub]
  have htt : endWeight RD Λ μ (L ++ blackWord t) = endWeight RD Λ μ (L ++ blackWord s) := by
    rw [endWeight_append, endWeight_append, endWeight_blackWord, endWeight_blackWord,
      h₁.wt_eq]
  refine admissibleMap_blackLinear_eq_zeroQ S red Sc H M hr hq hG μ L R s t rfl htt _ ?_ _ _
  rw [Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of, Presentation.lin_of,
    ← NF.dg_of h₁, ← NF.dg_of h₂, hdg, sub_self]

/-- **The cup pitchfork relations with the scalars `t^θ` act by zero** (Webster,
arXiv:1309.3796v2, (2.1a) and its mirror, in any signed context, for general black
parameters): the bent branch equals `t^θ_{ji}` times the straight branch, where `j` is the
through colour and `i` the cup colour. -/
theorem admissibleMap_mixedCupPitchforkQ [DecidableEq I]
    (P : Presentation.{w, max u v} (signature RD Λ) k) (a : MixedCupPitchfork X I ℓ) {x y : X}
    (ha : Cond x y ((addMixedCupPitchforkRelations RD Λ P
      fun i j => ((CLQ.thetaScalars RD Sc).t i j : k)).dom (.inr a)))
    (hb : Cond x y ((addMixedCupPitchforkRelations RD Λ P
      fun i j => ((CLQ.thetaScalars RD Sc).t i j : k)).cod (.inr a))) :
    admissibleMap G ha hb ((addMixedCupPitchforkRelations RD Λ P
      fun i j => ((CLQ.thetaScalars RD Sc).t i j : k)).rel (.inr a)) = 0 := by
  obtain ⟨d₁, d₂, hrel, e₁, e₂⟩ := addMixedCupPitchforkRelations_rel RD Λ P
    (fun i j => ((CLQ.thetaScalars RD Sc).t i j : k)) a
  rw [hrel]
  obtain ⟨μ, L, i, j, R, ord⟩ := a
  cases ord
  · have h₁ : SChain [dn j] ([([dn j], .cup (up i), [])] ++ (crossrL i j).map (whL [] [dn i]))
        [up i, dn j, dn i] := by
      simp [crossrL, whL, Shape.dom, Shape.cod]
    have h₂ : SChain [dn j] [([], .cup (up i), [dn j]), ([up i], .cross false i j, [])]
        [up i, dn j, dn i] := by
      simp [Shape.dom, Shape.cod]
    refine admissibleMap_sub_smul_eq_zero_of_dgQ S red Sc H M hr hq hG μ L R h₁ h₂ _ ?_ rfl rfl
      d₁ d₂
      (by rw [e₁]; simp [signedLayers, mixedCupPitchforkLayers, upwardMateLayers,
        layers_blackDiagram_mkD, crossrL, whL, blackWord])
      (by rw [e₂]; simp [signedLayers, downCupPitchforkLayers, layers_blackDiagram_mkD,
        blackWord]) ha hb
    rw [CLQ.dg_pf_cupUp_down RD k _ j i, smul_smul, Units.mul_inv, one_smul]
  · have h₁ : SChain [dn j] ([([], .cup (dn i), [dn j])] ++ (crosslL i j).map (whL [dn i] []))
        [dn i, dn j, up i] := by
      simp [crosslL, whL, Shape.dom, Shape.cod]
    have h₂ : SChain [dn j] [([dn j], .cup (dn i), []), ([], .cross false j i, [up i])]
        [dn i, dn j, up i] := by
      simp [Shape.dom, Shape.cod]
    refine admissibleMap_sub_smul_eq_zero_of_dgQ S red Sc H M hr hq hG μ L R h₁ h₂ _ ?_ rfl rfl
      d₁ d₂
      (by rw [e₁]; simp [signedLayers, mixedCupPitchforkLayers, upwardMateLayers,
        layers_blackDiagram_mkD, crosslL, whL, blackWord])
      (by rw [e₂]; simp [signedLayers, downCupPitchforkLayers, layers_blackDiagram_mkD,
        blackWord]) ha hb
    rw [CLQ.dg_pf_cupDn_down RD k _ i j, smul_smul, Units.mul_inv, one_smul]

end Categorification.Stendhal.DoubleDiagram
