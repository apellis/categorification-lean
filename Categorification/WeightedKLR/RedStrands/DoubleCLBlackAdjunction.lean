/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackContext
import Categorification.WeightedKLR.RedStrands.DoubleBlackAdjunction
import Categorification.Diagrams.KL3.Pitchfork
import Categorification.Diagrams.KL3.BubbleSlidesEq

/-!
# The black biadjunction relations vanish after the cover functor

Webster, arXiv:1309.3796v3, §4.5, Definition 4.24, and §4.6, proof of Lemma 4.29. The black
biadjunction triangles and the dot cyclicity of black cups and caps
(`addBlackAdjunctionRelations`) are reflections of the zigzag relations of KL III (3.1), (3.2)
and of the dot cyclicity (3.3), placed between signed words. So, under the hypotheses of
`coverLin_blackLinear_eq_zero`, they are sent to zero in `admissibleKernel` of a Rouquier family
(`coverLin_blackAdjunction_eq_zero`).
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
  [DecidableEq I] (Sc : CL.CLScalars C' k)
  (ht : ∀ i j, Sc.t (.inl i) (.inl j) = 1) (hs : ∀ i j p q, Sc.s (.inl i) (.inl j) p q = 0)
  (H : BrundanUpKLR S Sc) (Mi : BrundanMixedInversion S)

include ho ht hs H Mi

/-- A difference of two double diagrams whose layers are the reflections of two KL III diagrams
with equal classes in `U` is sent to zero in `admissibleKernel`. -/
theorem coverLin_sub_eq_zero_of_dg (μ : X) (L R : List (DoubleStrand I ℓ))
    {s t : List (Letter I)} {xs₁ xs₂ : List (LayerData I)} (h₁ : SChain s xs₁ t)
    (h₂ : SChain s xs₂ t)
    (hdg : dg RD k (endWeight RD Λ μ L) s t xs₁ = dg RD k (endWeight RD Λ μ L) s t xs₂)
    {a b : Obj (signature RD Λ)} (ha : obj RD Λ μ (L ++ blackWord s ++ R) = a)
    (hb : obj RD Λ μ (L ++ blackWord t ++ R) = b) (d₁ d₂ : a ⟶ b)
    (e₁ : Diagram.layers d₁ =
      Diagram.layers (blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₁ h₁)))
    (e₂ : Diagram.layers d₂ =
      Diagram.layers (blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₂ h₂))) :
    coverLin W hC o (admissibleKernel (S.genImg Sc)) coverSign
      (LinDiagram.of (R := k) d₁ - LinDiagram.of d₂) = 0 := by
  subst ha hb
  have f₁ : d₁ = blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₁ h₁) := Diagram.ext e₁
  have f₂ : d₂ = blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₂ h₂) := Diagram.ext e₂
  subst f₁ f₂
  rw [← blackLinear_of, ← blackLinear_of, ← map_sub]
  have htt : endWeight RD Λ μ (L ++ blackWord t) = endWeight RD Λ μ (L ++ blackWord s) := by
    rw [endWeight_append, endWeight_append, endWeight_blackWord, endWeight_blackWord,
      h₁.wt_eq]
  refine coverLin_blackLinear_eq_zero W hC o ho S Sc ht hs H Mi μ L R s t rfl htt _ ?_
  rw [Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of, ← dg_of h₁, ← dg_of h₂,
    hdg, sub_self]

/-- The black biadjunction triangles and dot cyclicity relations of
`addBlackAdjunctionRelations` are sent to zero in `admissibleKernel`. -/
theorem coverLin_blackAdjunction_eq_zero (P : Presentation.{w, max u v} (signature RD Λ) k)
    (r : BlackAdjunctionRelation X I ℓ) :
    coverLin W hC o (admissibleKernel (S.genImg Sc)) coverSign
      ((addBlackAdjunctionRelations RD Λ P).rel (.inr r)) = 0 := by
  obtain ⟨kind, μ, L, l, R⟩ := r
  cases kind with
  | snakeLeft =>
    have h₁ : SChain [l] [([l], .cup l.dual, []), ([], .cap l.dual, [l])] [l] := by
      simp [Shape.dom, Shape.cod]
    have h₂ : SChain [l] [] [l] := rfl
    exact coverLin_sub_eq_zero_of_dg W hC o ho S Sc ht hs H Mi μ L R h₁ h₂
      (by
        rcases l with ⟨_ | _, i⟩
        exacts [dg_zigR' RD k _ (true, i), dg_zigR' RD k _ (false, i)])
      (by simp [blackWord]) (by simp [blackWord])
        (blackSnakeLeft RD Λ μ L l R) (𝟙 _)
      (by simp [blackSnakeLeft, moveDiagram, layers_blackDiagram_mkD, blackWord, Sig.shape])
      (by simp [layers_blackDiagram_mkD])
  | snakeRight =>
    have h₁ : SChain [l] [([], .cup l, [l]), ([l], .cap l, [])] [l] := by
      simp [Shape.dom, Shape.cod]
    have h₂ : SChain [l] [] [l] := rfl
    exact coverLin_sub_eq_zero_of_dg W hC o ho S Sc ht hs H Mi μ L R h₁ h₂
      (dg_zigL' RD k _ l) (by simp [blackWord]) (by simp [blackWord])
      (blackSnakeRight RD Λ μ L l R) (𝟙 _)
      (by simp [blackSnakeRight, moveDiagram, layers_blackDiagram_mkD, blackWord, Sig.shape])
      (by simp [layers_blackDiagram_mkD])
  | cupDot =>
    rcases l with ⟨_ | _, i⟩
    · have h₁ : SChain [] [([], .cup (up i), []), ([up i], .dot (dn i), [])] [up i, dn i] := by
        simp [Shape.dom, Shape.cod]
      have h₂ : SChain [] [([], .cup (up i), []), ([], .dot (up i), [dn i])] [up i, dn i] := by
        simp [Shape.dom, Shape.cod]
      exact coverLin_sub_eq_zero_of_dg W hC o ho S Sc ht hs H Mi μ L R h₁ h₂
        (dg_dot_cupUp RD k i _)
        (by simp [blackWord]) (by simp [blackWord])
        (blackCupDotLeft RD Λ μ L _ R) (blackCupDotRight RD Λ μ L _ R)
        (by simp [blackCupDotLeft, blackCup, blackPairDotLeft, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape])
        (by simp [blackCupDotRight, blackCup, blackPairDotRight, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape])
    · have h₁ : SChain [] [([], .cup (dn i), []), ([dn i], .dot (up i), [])] [dn i, up i] := by
        simp [Shape.dom, Shape.cod]
      have h₂ : SChain [] [([], .cup (dn i), []), ([], .dot (dn i), [up i])] [dn i, up i] := by
        simp [Shape.dom, Shape.cod]
      exact coverLin_sub_eq_zero_of_dg W hC o ho S Sc ht hs H Mi μ L R h₁ h₂
        (dg_dot_cupDn RD k i _)
        (by simp [blackWord]) (by simp [blackWord])
        (blackCupDotLeft RD Λ μ L _ R) (blackCupDotRight RD Λ μ L _ R)
        (by simp [blackCupDotLeft, blackCup, blackPairDotLeft, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape])
        (by simp [blackCupDotRight, blackCup, blackPairDotRight, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape])
  | capDot =>
    rcases l with ⟨_ | _, i⟩
    · have h₁ : SChain [up i, dn i] [([up i], .dot (dn i), []), ([], .cap (dn i), [])] [] := by
        simp [Shape.dom, Shape.cod]
      have h₂ : SChain [up i, dn i] [([], .dot (up i), [dn i]), ([], .cap (dn i), [])] [] := by
        simp [Shape.dom, Shape.cod]
      exact coverLin_sub_eq_zero_of_dg W hC o ho S Sc ht hs H Mi μ L R h₁ h₂
        (dg_dot_cap_dn RD k _ i)
        (by simp [blackWord]) (by simp [blackWord])
        (blackCapDotLeft RD Λ μ L _ R) (blackCapDotRight RD Λ μ L _ R)
        (by simp [blackCapDotLeft, blackCap, blackPairDotLeft, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape])
        (by simp [blackCapDotRight, blackCap, blackPairDotRight, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape])
    · have h₁ : SChain [dn i, up i] [([dn i], .dot (up i), []), ([], .cap (up i), [])] [] := by
        simp [Shape.dom, Shape.cod]
      have h₂ : SChain [dn i, up i] [([], .dot (dn i), [up i]), ([], .cap (up i), [])] [] := by
        simp [Shape.dom, Shape.cod]
      exact coverLin_sub_eq_zero_of_dg W hC o ho S Sc ht hs H Mi μ L R h₁ h₂
        ((dg_dot_cap_up RD k _ i).symm)
        (by simp [blackWord]) (by simp [blackWord])
        (blackCapDotLeft RD Λ μ L _ R) (blackCapDotRight RD Λ μ L _ R)
        (by simp [blackCapDotLeft, blackCap, blackPairDotLeft, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape])
        (by simp [blackCapDotRight, blackCap, blackPairDotRight, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape])

end Categorification.Stendhal.DoubleDiagram
