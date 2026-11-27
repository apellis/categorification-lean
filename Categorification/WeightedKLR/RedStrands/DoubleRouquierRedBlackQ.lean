/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRouquierBlackQ
import Categorification.WeightedKLR.RedStrands.DoubleRouquierRedBlack
import Categorification.WeightedKLR.RedStrands.DoubleBlackPresentationOf
import Categorification.Diagrams.CLQ.Pitchfork
import Categorification.Diagrams.CLQ.BubbleSlidesEq

/-!
# Black relations of `U_{Sc^θ}(g)` between signed words, for all scalars

Webster, arXiv:1309.3796v3, §4.5, Definition 4.24, in the proof of Theorem 4.25, for general
black parameters. Let `G` be generator images for the double signature that are those of a
Rouquier family on the black generators (`BlackOn Sc`) for any Cautis–Lauda scalars `Sc` with
`r = 1`, and let `Sc^θ = CLQ.thetaScalars RD Sc` be the scalars of the reflection with inverted
orientations. Then a black linear combination that is zero in `U_{Sc^θ}(g)` acts by zero when
it is placed between two arbitrary signed words (`admissibleMap_blackLinear_eq_zeroQ`). In
particular:

* the mixed black relations (2.3c), (2.4a) with the scalars `t^θ` act by zero
  (`admissibleMap_mixedBlackRelationQ`);
* the black biadjunction and dot cyclicity relations of Definition 2.4 act by zero
  (`admissibleMap_blackAdjunctionQ`).

At the KL III scalars these are the statements of `DoubleRouquierRedBlack`.
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

/-- The relation sources of `U_Q(g)` are well formed. -/
theorem clqPres_wfDom {k : Type*} [CommRing k] (W : CL.CLScalars C k) : (CLQ.pres RD k W).WFDom := fun r => presCL_dom_wf r

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

/-- **Relations of `U_{Sc^θ}(g)` between signed words act by zero.** If a black linear
combination `f` between the words `s` and `t` is zero in `U_{Sc^θ}(g)`, its placement between
the signed words `u` and `v` is killed by every generator images that are those of the
Rouquier family on the black generators (Webster, arXiv:1309.3796v3, Definition 4.24 and proof
of Theorem 4.25, for general black parameters). -/
theorem admissibleMap_blackLinear_eq_zeroQ [DecidableEq I] (μ : X) (u v : List (DoubleStrand I ℓ))
    {τ : X} (s t : List (Letter I))
    (hst : endWeight RD Λ μ (u ++ blackWord s) = τ) (htt : endWeight RD Λ μ (u ++ blackWord t) = τ)
    (f : LinDiagram k (ob RD (endWeight RD Λ μ u) s) (ob RD (endWeight RD Λ μ u) t))
    (hf : (CLQ.pres RD k (CLQ.thetaScalars RD Sc)).lin f = 0) {x y : X}
    (ha : Cond x y (obj RD Λ μ (u ++ blackWord s ++ v)))
    (hb : Cond x y (obj RD Λ μ (u ++ blackWord t ++ v))) :
    admissibleMap G ha hb (blackLinear RD Λ k μ u v f) = 0 := by
  let P := admissibleKernel (k := k) G
  have hP : ∀ r : (CLQ.pres RD k (CLQ.thetaScalars RD Sc)).Rel,
      P.lin (blackMirrorLinear RD Λ ((CLQ.pres RD k (CLQ.thetaScalars RD Sc)).rel r)) = 0 :=
    fun r => admissibleKernel_lin_eq_zero G _ fun _ _ ha hb =>
      admissibleMap_blackMirror_relQ S Sc H M hr hq red hG r ha hb
  refine admissibleMap_eq_zero_of_kernel_lin G ha hb _ ?_
  have e := congrArg (blackRectangleHomOf RD Λ (CLQ.pres RD k (CLQ.thetaScalars RD Sc))
    (clqPres_wfDom _) μ u P hP v s t hst htt) hf
  rwa [blackRectangleHomOf_lin, map_zero] at e

/-- **The mixed black relations with the scalars `t^θ` act by zero** (Webster,
arXiv:1309.3796v3, (2.3c) and (2.4a), in any surrounding signed word, for general black
parameters): they are reflections of the relations of `U_{Sc^θ}(g)` on `E_i F_j` and
`E_i F_i`. -/
theorem admissibleMap_mixedBlackRelationQ [DecidableEq I]
    (P : Presentation.{w, max u v} (signature RD Λ) k) (a : MixedBlackRelation X I ℓ)
    {x y : X}
    (ha : Cond x y ((addMixedBlackRelations RD Λ k (CLQ.thetaScalars RD Sc).t P).dom (.inr a)))
    (hb : Cond x y ((addMixedBlackRelations RD Λ k (CLQ.thetaScalars RD Sc).t P).cod (.inr a))) :
    admissibleMap G ha hb
      ((addMixedBlackRelations RD Λ k (CLQ.thetaScalars RD Sc).t P).rel (.inr a)) = 0 := by
  change admissibleMap G ha hb (mixedBlackRelation RD Λ k (CLQ.thetaScalars RD Sc).withRone.t a) = 0
  cases a with
  | distinct μ L R i j h =>
    rw [mixedBlackRelation_distinct_CL]
    refine admissibleMap_blackLinear_eq_zeroQ S red Sc H M hr hq hG μ L R _ _ rfl rfl _ ?_ _ _
    exact (CLQ.pres RD k (CLQ.thetaScalars RD Sc)).lin_rel_self (.inr (.downupEF i j h _))
  | equal μ L R i =>
    rw [mixedBlackRelation_equal_CL RD Λ k _ μ L R i rfl]
    refine admissibleMap_blackLinear_eq_zeroQ S red Sc H M hr hq hG μ L R _ _ rfl rfl _ ?_ _ _
    exact (CLQ.pres RD k (CLQ.thetaScalars RD Sc)).lin_rel_self (.inr (.decompEF i _))

/-- A difference of two double diagrams whose layers are the reflections of two KL III diagrams
with equal classes acts by zero. -/
theorem admissibleMap_sub_eq_zero_of_dgQ [DecidableEq I] (μ : X) (L R : List (DoubleStrand I ℓ))
    {s t : List (Letter I)} {xs₁ xs₂ : List (LayerData I)} (h₁ : SChain s xs₁ t)
    (h₂ : SChain s xs₂ t)
    (hdg : NF.dg (CLQ.pres RD k (CLQ.thetaScalars RD Sc)) (endWeight RD Λ μ L) s t xs₁ =
      NF.dg (CLQ.pres RD k (CLQ.thetaScalars RD Sc)) (endWeight RD Λ μ L) s t xs₂)
    {a b : Obj (signature RD Λ)} (ha : obj RD Λ μ (L ++ blackWord s ++ R) = a)
    (hb : obj RD Λ μ (L ++ blackWord t ++ R) = b) (d₁ d₂ : a ⟶ b)
    (e₁ : Diagram.layers d₁ =
      Diagram.layers (blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₁ h₁)))
    (e₂ : Diagram.layers d₂ =
      Diagram.layers (blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₂ h₂)))
    {x y : X} (ha' : Cond x y a) (hb' : Cond x y b) :
    admissibleMap G ha' hb' (LinDiagram.of (R := k) d₁ - LinDiagram.of d₂) = 0 := by
  subst ha hb
  have f₁ : d₁ = blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₁ h₁) := Diagram.ext e₁
  have f₂ : d₂ = blackDiagram RD Λ μ L R (mkD RD (endWeight RD Λ μ L) xs₂ h₂) := Diagram.ext e₂
  subst f₁ f₂
  rw [← blackLinear_of, ← blackLinear_of, ← map_sub]
  have htt : endWeight RD Λ μ (L ++ blackWord t) = endWeight RD Λ μ (L ++ blackWord s) := by
    rw [endWeight_append, endWeight_append, endWeight_blackWord, endWeight_blackWord,
      h₁.wt_eq]
  refine admissibleMap_blackLinear_eq_zeroQ S red Sc H M hr hq hG μ L R s t rfl htt _ ?_ _ _
  rw [Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of, ← NF.dg_of h₁, ← NF.dg_of h₂,
    hdg, sub_self]

/-- **The black biadjunction and dot cyclicity relations act by zero** (Webster,
arXiv:1309.3796v3, Definition 2.4, in any signed context, for all scalars): they are reflections of the zigzag
relations of KL III (3.1), (3.2) and of the dot cyclicity (3.3). -/
theorem admissibleMap_blackAdjunctionQ [DecidableEq I]
    (P : Presentation.{w, max u v} (signature RD Λ) k) (r : BlackAdjunctionRelation X I ℓ)
    {x y : X} (ha : Cond x y ((addBlackAdjunctionRelations RD Λ P).dom (.inr r)))
    (hb : Cond x y ((addBlackAdjunctionRelations RD Λ P).cod (.inr r))) :
    admissibleMap G ha hb ((addBlackAdjunctionRelations RD Λ P).rel (.inr r)) = 0 := by
  obtain ⟨kind, μ, L, l, R⟩ := r
  cases kind with
  | snakeLeft =>
    have h₁ : SChain [l] [([l], .cup l.dual, []), ([], .cap l.dual, [l])] [l] := by
      simp [Shape.dom, Shape.cod]
    have h₂ : SChain [l] [] [l] := rfl
    exact admissibleMap_sub_eq_zero_of_dgQ S red Sc H M hr hq hG μ L R h₁ h₂
      (by
        rcases l with ⟨_ | _, i⟩
        exacts [NF.dg_zigR' (CLQ.pres RD k (CLQ.thetaScalars RD Sc)) _ (true, i),
          NF.dg_zigR' (CLQ.pres RD k (CLQ.thetaScalars RD Sc)) _ (false, i)])
      (by simp [blackWord]) (by simp [blackWord])
        (blackSnakeLeft RD Λ μ L l R) (𝟙 _)
      (by simp [blackSnakeLeft, moveDiagram, layers_blackDiagram_mkD, blackWord, Sig.shape])
      (by simp [layers_blackDiagram_mkD]) _ _
  | snakeRight =>
    have h₁ : SChain [l] [([], .cup l, [l]), ([l], .cap l, [])] [l] := by
      simp [Shape.dom, Shape.cod]
    have h₂ : SChain [l] [] [l] := rfl
    exact admissibleMap_sub_eq_zero_of_dgQ S red Sc H M hr hq hG μ L R h₁ h₂
      (NF.dg_zigL' (CLQ.pres RD k (CLQ.thetaScalars RD Sc)) _ l) (by simp [blackWord]) (by simp [blackWord])
      (blackSnakeRight RD Λ μ L l R) (𝟙 _)
      (by simp [blackSnakeRight, moveDiagram, layers_blackDiagram_mkD, blackWord, Sig.shape])
      (by simp [layers_blackDiagram_mkD]) _ _
  | cupDot =>
    rcases l with ⟨_ | _, i⟩
    · have h₁ : SChain [] [([], .cup (up i), []), ([up i], .dot (dn i), [])] [up i, dn i] := by
        simp [Shape.dom, Shape.cod]
      have h₂ : SChain [] [([], .cup (up i), []), ([], .dot (up i), [dn i])] [up i, dn i] := by
        simp [Shape.dom, Shape.cod]
      exact admissibleMap_sub_eq_zero_of_dgQ S red Sc H M hr hq hG μ L R h₁ h₂
        (CLQ.dg_dot_cupUp RD k (CLQ.thetaScalars RD Sc) i _)
        (by simp [blackWord]) (by simp [blackWord])
        (blackCupDotLeft RD Λ μ L _ R) (blackCupDotRight RD Λ μ L _ R)
        (by simp [blackCupDotLeft, blackCup, blackPairDotLeft, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape])
        (by simp [blackCupDotRight, blackCup, blackPairDotRight, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape]) _ _
    · have h₁ : SChain [] [([], .cup (dn i), []), ([dn i], .dot (up i), [])] [dn i, up i] := by
        simp [Shape.dom, Shape.cod]
      have h₂ : SChain [] [([], .cup (dn i), []), ([], .dot (dn i), [up i])] [dn i, up i] := by
        simp [Shape.dom, Shape.cod]
      exact admissibleMap_sub_eq_zero_of_dgQ S red Sc H M hr hq hG μ L R h₁ h₂
        (CLQ.dg_dot_cupDn RD k (CLQ.thetaScalars RD Sc) i _)
        (by simp [blackWord]) (by simp [blackWord])
        (blackCupDotLeft RD Λ μ L _ R) (blackCupDotRight RD Λ μ L _ R)
        (by simp [blackCupDotLeft, blackCup, blackPairDotLeft, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape])
        (by simp [blackCupDotRight, blackCup, blackPairDotRight, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape]) _ _
  | capDot =>
    rcases l with ⟨_ | _, i⟩
    · have h₁ : SChain [up i, dn i] [([up i], .dot (dn i), []), ([], .cap (dn i), [])] [] := by
        simp [Shape.dom, Shape.cod]
      have h₂ : SChain [up i, dn i] [([], .dot (up i), [dn i]), ([], .cap (dn i), [])] [] := by
        simp [Shape.dom, Shape.cod]
      exact admissibleMap_sub_eq_zero_of_dgQ S red Sc H M hr hq hG μ L R h₁ h₂
        (CLQ.dg_dot_cap_dn RD k (CLQ.thetaScalars RD Sc) _ i)
        (by simp [blackWord]) (by simp [blackWord])
        (blackCapDotLeft RD Λ μ L _ R) (blackCapDotRight RD Λ μ L _ R)
        (by simp [blackCapDotLeft, blackCap, blackPairDotLeft, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape])
        (by simp [blackCapDotRight, blackCap, blackPairDotRight, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape]) _ _
    · have h₁ : SChain [dn i, up i] [([dn i], .dot (up i), []), ([], .cap (up i), [])] [] := by
        simp [Shape.dom, Shape.cod]
      have h₂ : SChain [dn i, up i] [([], .dot (dn i), [up i]), ([], .cap (up i), [])] [] := by
        simp [Shape.dom, Shape.cod]
      exact admissibleMap_sub_eq_zero_of_dgQ S red Sc H M hr hq hG μ L R h₁ h₂
        ((CLQ.dg_dot_cap_up RD k (CLQ.thetaScalars RD Sc) _ i).symm)
        (by simp [blackWord]) (by simp [blackWord])
        (blackCapDotLeft RD Λ μ L _ R) (blackCapDotRight RD Λ μ L _ R)
        (by simp [blackCapDotLeft, blackCap, blackPairDotLeft, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape])
        (by simp [blackCapDotRight, blackCap, blackPairDotRight, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape]) _ _

end Categorification.Stendhal.DoubleDiagram
