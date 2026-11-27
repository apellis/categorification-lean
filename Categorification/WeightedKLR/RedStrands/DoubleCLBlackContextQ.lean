/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackAdjunction
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackComparisonQ
import Categorification.WeightedKLR.RedStrands.DoubleBlackPresentationOf

/-!
# Black relations with general parameters between signed words, after the cover functor

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, for black strands carrying the relations
of Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`) for scalars `Sb`. The
analogues of `coverLin_blackLinear_eq_zero`, `coverLin_mixedBlackRelation_eq_zero`,
`coverLin_sub_eq_zero_of_dg` and `coverLin_blackAdjunction_eq_zero`: a black linear combination
vanishing in `U_Q(g)`, placed between signed words, the mixed black relations (2.4a), (2.3c) at
the scalars `Sb.t`, and the black biadjunction and dot cyclicity relations are sent to zero in
`admissibleKernel` of a Rouquier family whose scalars restrict to `Sb^θ` on the black colours
(`coverLin_blackRelQ`).
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
/-- **Black relations with general parameters between signed words vanish after the cover
functor.** If a black linear combination `f` between the words `s` and `t` is zero in
`U_Q(g)` for the scalars `Sb`, its placement between the signed words `u` and `v` is sent to
zero in `admissibleKernel` of a Rouquier family as in `coverLin_blackRelQ`. -/
theorem coverLin_blackLinear_eq_zeroQ [DecidableEq I] (Sc : CL.CLScalars C' k)
    (Sb : CL.CLScalars C k)
    (hθ : CLQ.thetaScalars RD Sb = (coverRestrict W hC o ho).scalars hC Sc)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s (.inl i) (.inl j) p q = 0)
    (H : BrundanUpKLR S Sc) (Mi : BrundanMixedInversion S)
    (μ : X) (u v : List (DoubleStrand I ℓ)) {τ : X} (s t : List (Letter I))
    (hst : endWeight RD Λ μ (u ++ blackWord s) = τ)
    (htt : endWeight RD Λ μ (u ++ blackWord t) = τ)
    (f : LinDiagram k (ob RD (endWeight RD Λ μ u) s) (ob RD (endWeight RD Λ μ u) t))
    (hf : (CLQ.pres RD k Sb).lin f = 0) :
    coverLin W hC o (admissibleKernel (S.genImg Sc)) coverSign
      (blackLinear RD Λ k μ u v f) = 0 := by
  let Q := admissibleKernel (k := k) (S.genImg Sc)
  let P := coverZero W hC o Q coverSign
  have hP : ∀ r : (CLQ.pres RD k Sb).Rel,
      P.lin (blackMirrorLinear RD Λ ((CLQ.pres RD k Sb).rel r)) = 0 :=
    fun r => P.lin_rel_self ⟨_, _, ⟨blackMirrorLinear RD Λ ((CLQ.pres RD k Sb).rel r),
      ((blackMirror RD Λ).toMirrorColourMap.ok_word (CLQ.pres_dom_wfQ r)).1,
      coverLin_blackRelQ W hC o ho S Sc Sb hθ hq H Mi r⟩⟩
  apply coverLin_eq_zero_of_coverZero W hC o Q coverSign
  have e := congrArg (blackRectangleHomOf RD Λ (CLQ.pres RD k Sb)
    (fun r => CLQ.pres_dom_wfQ r) μ u P hP v s t hst htt) hf
  rwa [blackRectangleHomOf_lin, map_zero] at e

include ho in
/-- **The mixed black relations at the scalars `Sb.t` vanish after the cover functor.** The
distinct-colour relation (2.4a) and the equal-colour relation (2.3c) of Webster,
arXiv:1309.3796v3, in any surrounding signed word, are reflections of the relations of
`U_Q(g)` on `E_i F_j` and `E_i F_i` (`r = 1`). -/
theorem coverLin_mixedBlackRelation_eq_zeroQ [DecidableEq I] (Sc : CL.CLScalars C' k)
    (Sb : CL.CLScalars C k)
    (hθ : CLQ.thetaScalars RD Sb = (coverRestrict W hC o ho).scalars hC Sc)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s (.inl i) (.inl j) p q = 0)
    (H : BrundanUpKLR S Sc) (Mi : BrundanMixedInversion S)
    (hr : ∀ i, Sb.r i = 1)
    (a : MixedBlackRelation X I ℓ) :
    coverLin W hC o (admissibleKernel (S.genImg Sc)) coverSign
      (mixedBlackRelation RD Λ k Sb.t a) = 0 := by
  have hSb : Sb.withRone = Sb := CL.CLScalars.withRone_eq_of_r Sb hr
  cases a with
  | distinct μ L R i j h =>
    rw [mixedBlackRelation_distinct_CL]
    refine coverLin_blackLinear_eq_zeroQ W hC o ho S Sc Sb hθ hq H Mi μ L R _ _ rfl rfl _ ?_
    have := CLQ.lin_relationCL RD k Sb (.downupEF i j h (endWeight RD Λ μ L))
    rwa [hSb] at this
  | equal μ L R i =>
    rw [mixedBlackRelation_equal_CL RD Λ k Sb μ L R i (hr i)]
    refine coverLin_blackLinear_eq_zeroQ W hC o ho S Sc Sb hθ hq H Mi μ L R _ _ rfl rfl _ ?_
    have := CLQ.lin_relationCL RD k Sb (.decompEF i (endWeight RD Λ μ L))
    rwa [hSb] at this

include ho in
/-- A difference of two double diagrams whose layers are the reflections of two diagrams with
equal classes in `U_Q(g)` is sent to zero in `admissibleKernel`. -/
theorem coverLin_sub_eq_zero_of_dgQ [DecidableEq I] (Sc : CL.CLScalars C' k)
    (Sb : CL.CLScalars C k)
    (hθ : CLQ.thetaScalars RD Sb = (coverRestrict W hC o ho).scalars hC Sc)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s (.inl i) (.inl j) p q = 0)
    (H : BrundanUpKLR S Sc) (Mi : BrundanMixedInversion S)
    (μ : X) (L R : List (DoubleStrand I ℓ))
    {s t : List (Letter I)} {xs₁ xs₂ : List (LayerData I)} (h₁ : SChain s xs₁ t)
    (h₂ : SChain s xs₂ t)
    (hdg : NF.dg (CLQ.pres RD k Sb) (endWeight RD Λ μ L) s t xs₁ =
      NF.dg (CLQ.pres RD k Sb) (endWeight RD Λ μ L) s t xs₂)
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
  refine coverLin_blackLinear_eq_zeroQ W hC o ho S Sc Sb hθ hq H Mi μ L R s t rfl htt _ ?_
  rw [Presentation.lin_sub, Presentation.lin_of, Presentation.lin_of, ← NF.dg_of h₁,
    ← NF.dg_of h₂, hdg, sub_self]

include ho in
/-- The black biadjunction triangles and dot cyclicity relations of
`addBlackAdjunctionRelations` are sent to zero in `admissibleKernel` (general parameters). -/
theorem coverLin_blackAdjunction_eq_zeroQ [DecidableEq I] (Sc : CL.CLScalars C' k)
    (Sb : CL.CLScalars C k)
    (hθ : CLQ.thetaScalars RD Sb = (coverRestrict W hC o ho).scalars hC Sc)
    (hq : ∀ i j p q, p < C.dij i j → q < C.dij j i →
      C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j → Sc.s (.inl i) (.inl j) p q = 0)
    (H : BrundanUpKLR S Sc) (Mi : BrundanMixedInversion S)
    (P : Presentation.{w, max u v} (signature RD Λ) k)
    (r : BlackAdjunctionRelation X I ℓ) :
    coverLin W hC o (admissibleKernel (S.genImg Sc)) coverSign
      ((addBlackAdjunctionRelations RD Λ P).rel (.inr r)) = 0 := by
  obtain ⟨kind, μ, L, l, R⟩ := r
  cases kind with
  | snakeLeft =>
    have h₁ : SChain [l] [([l], .cup l.dual, []), ([], .cap l.dual, [l])] [l] := by
      simp [Shape.dom, Shape.cod]
    have h₂ : SChain [l] [] [l] := rfl
    exact coverLin_sub_eq_zero_of_dgQ W hC o ho S Sc Sb hθ hq H Mi μ L R h₁ h₂
      (by
        rcases l with ⟨_ | _, i⟩
        exacts [NF.dg_zigR' (CLQ.pres RD k Sb) _ (true, i),
          NF.dg_zigR' (CLQ.pres RD k Sb) _ (false, i)])
      (by simp [blackWord]) (by simp [blackWord])
        (blackSnakeLeft RD Λ μ L l R) (𝟙 _)
      (by simp [blackSnakeLeft, moveDiagram, layers_blackDiagram_mkD, blackWord, Sig.shape])
      (by simp [layers_blackDiagram_mkD])
  | snakeRight =>
    have h₁ : SChain [l] [([], .cup l, [l]), ([l], .cap l, [])] [l] := by
      simp [Shape.dom, Shape.cod]
    have h₂ : SChain [l] [] [l] := rfl
    exact coverLin_sub_eq_zero_of_dgQ W hC o ho S Sc Sb hθ hq H Mi μ L R h₁ h₂
      (NF.dg_zigL' (CLQ.pres RD k Sb) _ l) (by simp [blackWord]) (by simp [blackWord])
      (blackSnakeRight RD Λ μ L l R) (𝟙 _)
      (by simp [blackSnakeRight, moveDiagram, layers_blackDiagram_mkD, blackWord, Sig.shape])
      (by simp [layers_blackDiagram_mkD])
  | cupDot =>
    rcases l with ⟨_ | _, i⟩
    · have h₁ : SChain [] [([], .cup (up i), []), ([up i], .dot (dn i), [])] [up i, dn i] := by
        simp [Shape.dom, Shape.cod]
      have h₂ : SChain [] [([], .cup (up i), []), ([], .dot (up i), [dn i])] [up i, dn i] := by
        simp [Shape.dom, Shape.cod]
      exact coverLin_sub_eq_zero_of_dgQ W hC o ho S Sc Sb hθ hq H Mi μ L R h₁ h₂
        (CLQ.dg_dot_cupUp RD k Sb i _)
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
      exact coverLin_sub_eq_zero_of_dgQ W hC o ho S Sc Sb hθ hq H Mi μ L R h₁ h₂
        (CLQ.dg_dot_cupDn RD k Sb i _)
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
      exact coverLin_sub_eq_zero_of_dgQ W hC o ho S Sc Sb hθ hq H Mi μ L R h₁ h₂
        (CLQ.dg_dot_cap_dn RD k Sb _ i)
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
      exact coverLin_sub_eq_zero_of_dgQ W hC o ho S Sc Sb hθ hq H Mi μ L R h₁ h₂
        ((CLQ.dg_dot_cap_up RD k Sb _ i).symm)
        (by simp [blackWord]) (by simp [blackWord])
        (blackCapDotLeft RD Λ μ L _ R) (blackCapDotRight RD Λ μ L _ R)
        (by simp [blackCapDotLeft, blackCap, blackPairDotLeft, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape])
        (by simp [blackCapDotRight, blackCap, blackPairDotRight, moveDiagram,
          layers_blackDiagram_mkD, blackWord, Sig.shape])

end Categorification.Stendhal.DoubleDiagram
