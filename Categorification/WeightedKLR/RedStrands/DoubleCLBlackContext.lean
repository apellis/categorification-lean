/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackComparison
import Categorification.WeightedKLR.RedStrands.DoubleBlackSuffix
import Categorification.WeightedKLR.RedStrands.DoubleMixedRelations

/-!
# Black KL relations in a signed context, after the cover functor

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. A black KL III relation placed between
two arbitrary signed words (`blackLinear`) is sent to zero by the cover functor into
`admissibleKernel` of a Rouquier family as in `coverLin_blackRel`
(`coverLin_blackLinear_eq_zero`).

The proof uses the presentation `coverZero Q σ` of double diagrams whose relations are the
linear combinations with well-formed domain that the cover functor sends to zero. Its
quotient maps to `Q` (`coverLin_eq_zero_of_coverZero`), and it contains the reflected black
KL relations, so the whiskering of `blackRectangleHom` applies.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams TwoRep

universe w u v v'

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {C' : CartanDatum (I ⊕ Fin ℓ)}
  {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (W : WeightDatum C' X Y)
  (hC : ∀ i j, C'.dot (.inl i) (.inl j) = C.dot i j) (o : X)

local notation "RD" => blackDatum W hC
local notation "Λ" => redWeight W

section CoverZero

variable {k : Type w} [CommRing k] (Q : Presentation.{w, v'} (psig W) k) (σ : Move I ℓ → k)

/-- The double linear combinations with well-formed domain sent to zero by the cover
functor into `Q`, as a presentation of double diagrams. -/
def coverZero : Presentation.{w, max u v w} (signature RD Λ) k where
  Rel := Σ (a b : Obj (signature RD Λ)), {f : LinDiagram k a b //
    a.WF ∧ coverLin W hC o Q σ f = 0}
  dom r := r.1
  cod r := r.2.1
  rel r := r.2.2.1

theorem coverZero_wfDom : (coverZero W hC o Q σ).WFDom := fun r => r.2.2.2.1

/-- A double linear combination trivial in `coverZero Q σ` is sent to zero in `Q`. -/
theorem coverLin_eq_zero_of_coverZero {a b : Obj (signature RD Λ)} (f : LinDiagram k a b)
    (h : (coverZero W hC o Q σ).lin f = 0) : coverLin W hC o Q σ f = 0 := by
  have e := coverFunctor_lin W hC o (coverZero W hC o Q σ) Q σ (coverZero_wfDom W hC o Q σ)
    (fun r => r.2.2.2.2) f
  have e0 := coverFunctor_lin W hC o (coverZero W hC o Q σ) Q σ (coverZero_wfDom W hC o Q σ)
    (fun r => r.2.2.2.2) (0 : LinDiagram k a b)
  rw [Presentation.lin_zero, ← h, e] at e0
  rw [e0]
  simp [coverLin, LayerMap.lin]

end CoverZero

section Rouquier

variable (ho : ∀ i, W.pair (W.iY (.inl i)) o = 0)
  {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] (S : RouqFamily (B := B) W)
  [AdditiveWhiskering B] {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (Bicategory.precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (Bicategory.postcomp a g).Linear k]

include ho in
/-- **Black KL relations between signed words vanish after the cover functor.** If a black
linear combination `f` between the words `s` and `t` is zero in the KL III presentation, its
placement between the signed words `u` and `v` is sent to zero in `admissibleKernel` of a
Rouquier family satisfying the hypotheses of `coverLin_blackRel`. -/
theorem coverLin_blackLinear_eq_zero [DecidableEq I] (Sc : CL.CLScalars C' k)
    (ht : ∀ i j, Sc.t (.inl i) (.inl j) = 1)
    (hs : ∀ i j p q, p < C.dij i j → q < C.dij j i → Sc.s (.inl i) (.inl j) p q = 0)
    (H : BrundanUpKLR S Sc) (Mi : BrundanMixedInversion S)
    (μ : X) (u v : List (DoubleStrand I ℓ)) {τ : X} (s t : List (Letter I))
    (hst : endWeight RD Λ μ (u ++ blackWord s) = τ) (htt : endWeight RD Λ μ (u ++ blackWord t) = τ)
    (f : LinDiagram k (ob RD (endWeight RD Λ μ u) s) (ob RD (endWeight RD Λ μ u) t))
    (hf : (pres RD k).lin f = 0) :
    coverLin W hC o (admissibleKernel (S.genImg Sc)) coverSign
      (blackLinear RD Λ k μ u v f) = 0 := by
  let Q := admissibleKernel (k := k) (S.genImg Sc)
  let P := coverZero W hC o Q coverSign
  have hP : ∀ r : (pres RD k).Rel, P.lin (blackMirrorLinear RD Λ ((pres RD k).rel r)) = 0 :=
    fun r => P.lin_rel_self ⟨_, _, ⟨blackMirrorLinear RD Λ ((pres RD k).rel r),
      ((blackMirror RD Λ).toMirrorColourMap.ok_word (pres_dom_wf r)).1,
      coverLin_blackRel W hC o ho S Sc ht hs H Mi r⟩⟩
  apply coverLin_eq_zero_of_coverZero W hC o Q coverSign
  have e := congrArg (blackRectangleHom RD Λ μ u v s P hP t hst htt) hf
  rwa [blackRectangleHom_lin, map_zero] at e

include ho in
/-- **The mixed black relations vanish after the cover functor.** With the KL scalars
(`t = 1`, `r = 1`) the distinct-colour relation (2.4a) and the equal-colour relation (2.3c)
of Webster, arXiv:1309.3796v3, in any surrounding signed word, are reflections of the KL III
relations on `E_i F_j` and `E_i F_i`; so they are sent to zero in `admissibleKernel` of a
Rouquier family as in `coverLin_blackRel`. -/
theorem coverLin_mixedBlackRelation_eq_zero [DecidableEq I] (Sc : CL.CLScalars C' k)
    (ht : ∀ i j, Sc.t (.inl i) (.inl j) = 1)
    (hs : ∀ i j p q, p < C.dij i j → q < C.dij j i → Sc.s (.inl i) (.inl j) p q = 0)
    (H : BrundanUpKLR S Sc) (Mi : BrundanMixedInversion S) (a : MixedBlackRelation X I ℓ) :
    coverLin W hC o (admissibleKernel (S.genImg Sc)) coverSign
      (mixedBlackRelation RD Λ k (CL.CLScalars.kl : CL.CLScalars C k).t a) = 0 := by
  cases a with
  | distinct μ L R i j h =>
    rw [mixedBlackRelation_distinct_CL]
    refine coverLin_blackLinear_eq_zero W hC o ho S Sc ht hs H Mi μ L R _ _ rfl rfl _ ?_
    rw [CL.relationCL_kl]
    exact (pres RD k).lin_rel_self (.inr (.downupEF i j h _))
  | equal μ L R i =>
    rw [mixedBlackRelation_equal_CL RD Λ k CL.CLScalars.kl μ L R i (CL.CLScalars.kl_r i)]
    refine coverLin_blackLinear_eq_zero W hC o ho S Sc ht hs H Mi μ L R _ _ rfl rfl _ ?_
    rw [CL.relationCL_kl]
    exact (pres RD k).lin_rel_self (.inr (.decompEF i _))

end Rouquier

end Categorification.Stendhal.DoubleDiagram
