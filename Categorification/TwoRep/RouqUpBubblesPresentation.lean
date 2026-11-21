/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqUpBubbles
import Categorification.TwoRep.RouqUpWordsPresentation
import Categorification.Diagrams.CL.SpanningDefs

/-!
# Bubbles to the right of upward words, through an arbitrary presentation

`RouqUpBubbles.upEval_bubAt` evaluates an endomorphism of the empty word placed to the right of
upward strands, for the KL presentation. The same holds for any presentation `P` on the signature
of `U` whose relations hold under the admissible interpretation (`upEvalP_bubAtC`): the
evaluation of `CL.bubAtC P μ (ups t) β` is the right whiskering of the evaluation of `β`,
conjugated by the left unitor. This is used for the cyclotomic Cautis–Lauda presentations in the
proof of Webster, arXiv:1309.3796v2, Proposition 3.25, where the bubbles of the spanning set of
KL III Proposition 3.10 sit to the right of the upward strands.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp

universe w v u

variable {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)]
  {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}

namespace RouqFamily

variable (S : RouqFamily (B := B) RD) {ν : Multiset I}
  {k : Type w} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]
  (Sc : CL.CLScalars C k) (P : Presentation.{w, max u v} (psig RD) k)
  (hrel : ∀ (r : P.Rel) {s t : X} (ha : Cond (S := psig RD) s t (P.dom r))
    (hb : Cond (S := psig RD) s t (P.cod r)),
    admissibleMap (S.genImg Sc) ha hb (P.rel r) = 0)

omit [∀ a b : B, Preadditive (a ⟶ b)] in
private theorem dgC_nil_eqToHom (μ : X) (s t : List (Letter I)) (h : s = t) :
    CL.dgC P μ s t [] = eqToHom (congrArg (fun s => P.obj (ob RD μ s)) h) := by
  subst t
  exact CL.dgC_nil (P := P) μ s

private theorem eqToHom_sandwich' {D : Type*} [Category D]
    {a b c d e f : D} (p : a = b) (q : b = c) (r : d = e) (s : e = f)
    (t : a = c) (u : d = f) (g : c ⟶ d) :
    eqToHom p ≫ (eqToHom q ≫ g ≫ eqToHom r) ≫ eqToHom s =
      eqToHom t ≫ g ≫ eqToHom u := by
  simp

omit [∀ a b : B, Preadditive (a ⟶ b)] in
/-- Placing an endomorphism of the empty word to the right of the strands `s` is whiskering,
up to equality transport. -/
theorem bubAtC_eq_whisk (μ : X) (s : List (Letter I)) (β : End (P.obj (ob RD μ []))) :
    CL.bubAtC P μ s β =
      eqToHom (congrArg P.obj (by
        apply Obj.ext
        · rfl
        · change (ob RD μ s).word = (ob RD μ s).word ++ [] ++ []
          simp only [List.append_nil])) ≫
      P.whisk β (ob RD μ s) [] ≫
      eqToHom (congrArg P.obj (by
        apply Obj.ext
        · rfl
        · change (ob RD μ s).word ++ [] ++ [] = (ob RD μ s).word
          simp only [List.append_nil])) := by
  change CL.dgC P μ s (s ++ [] ++ []) [] ≫ CL.plcLC P μ s [] [] [] β ≫
    CL.dgC P μ (s ++ [] ++ []) s [] = _
  erw [CL.plcLC, dite_eq_left rfl]
  simp only [CL.plcC, LinearMap.coe_mk, AddHom.coe_mk]
  erw [dgC_nil_eqToHom P μ s (s ++ [] ++ []) (by simp),
    dgC_nil_eqToHom P μ (s ++ [] ++ []) s (by simp)]
  change eqToHom _ ≫ (eqToHom _ ≫ P.whisk β (ob RD μ s) [] ≫ eqToHom _) ≫ eqToHom _ = _
  exact eqToHom_sandwich' _ _ _ _ _ _ _

/-- **Bubbles to the right of upward words** (through an arbitrary presentation `P`): the
evaluation of an endomorphism `β` of the empty word placed to the right of the upward word of
`t` is the right whiskering of the evaluation of `β`, conjugated by the left unitor. -/
theorem upEvalP_bubAtC (μ : X) (t : KLR.Seq ν) (β : End (P.obj (ob RD μ []))) :
    S.upEvalP Sc P hrel μ (CL.bubAtC P μ (ups (KLR.Diagram.word t)) β) =
      (λ_ (S.wordCell μ t)).inv ≫
        admissibleQuotientMap (S.genImg Sc) P hrel Signature.IsEven.odd_eq_false
          (bubbleNil μ).property (bubbleNil μ).property β ▷ S.wordCell μ t ≫
        (λ_ (S.wordCell μ t)).hom := by
  let hu := cond_word (RD := RD) μ t
  let q := S.model.word (wtop RD μ ν : X) (ob RD μ (ups (KLR.Diagram.word t))).word μ hu.1 hu.2.1
  have h : admissibleQuotientMap (S.genImg Sc) P hrel Signature.IsEven.odd_eq_false hu hu
      (CL.bubAtC P μ (ups (KLR.Diagram.word t)) β) =
      (λ_ q).inv ≫ admissibleQuotientMap (S.genImg Sc) P hrel Signature.IsEven.odd_eq_false
          (bubbleNil μ).property (bubbleNil μ).property β ▷ q ≫ (λ_ q).hom := by
    rw [bubAtC_eq_whisk]
    have h := quotientMap_bubble_whisk (S.genImg Sc) P hrel Signature.IsEven.odd_eq_false
      (ob RD μ (ups (KLR.Diagram.word t))) hu (bubbleNil μ).obj (bubbleNil μ).property
      rfl (by
        apply Obj.ext
        · rfl
        · change (ob RD μ (ups (KLR.Diagram.word t))).word ++ [] ++ [] = _
          simp only [List.append_nil]) β
    change _ = (λ_ q).inv ≫ (𝟙 _ ≫ admissibleQuotientMap (S.genImg Sc) P hrel
      Signature.IsEven.odd_eq_false (bubbleNil μ).property (bubbleNil μ).property β ≫ 𝟙 _) ▷ q ≫
        (λ_ q).hom at h
    exact h.trans (congrArg (fun b => (λ_ q).inv ≫ b ▷ q ≫ (λ_ q).hom)
      (by rw [Category.id_comp]; exact Category.comp_id _))
  change (S.upIso μ t hu).inv ≫ _ ≫ (S.upIso μ t hu).hom = _
  exact (congrArg (fun f => (S.upIso μ t hu).inv ≫ f ≫ (S.upIso μ t hu).hom) h).trans
    (iso_conj_rightBubble (S.upIso μ t hu) _)

end RouqFamily

end Categorification.TwoRep
