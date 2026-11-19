/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLDownKLR
import Categorification.WeightedKLR.RedStrands.DoubleCLLayerIdealOn
import Categorification.WeightedKLR.RedStrands.DoubleCLRedUp
import Categorification.WeightedKLR.RedStrands.DoubleCLRedDot
import Categorification.Diagrams.CL.NoMix
import Categorification.Diagrams.KL3.SymmetrySigmaSymm
import Categorification.WeightedKLR.RedStrands.DoubleDownCLComparison

/-!
# Downward KLR relations with at most one red strand

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. Under the cover functor, the downward
translation of a KLR diagram with at most one red strand agrees, layer by layer and up to red
dots, with the reflected upward KLR diagram in the Cautis–Lauda presentation of the extended
datum.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram

universe u v w

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  (hc : CoverDotCentral Λ C Q)

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "RDc" => coordinateDatum Λ C
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "Sc" => cyclotomicScalars sym lead Wgt deg
local notation "PCL" => KL3.Diagram.CL.presCL Wgt k Sc

/-- The upward KLR relations with the Cautis–Lauda parameters hold in the Cautis–Lauda
presentation of the extended datum. -/
theorem presCL_cover_klr : CL.KLRHolds PCL (CL.qCL Sc) := by
  intro μ r
  have h := (PCL).lin_rel_self (.inr (.klr μ r))
  have hr' : (fun i => ((CL.CLScalars.r (Sc) i : k))) = fun _ => 1 := funext fun _ => rfl
  change (PCL).lin (upLin Wgt k μ (CL.relationR k (CL.qCL Sc)
    (fun i => ((CL.CLScalars.r (Sc) i : k))) r)) = 0 at h
  rwa [hr', CL.relationR_one] at h

/-- The linear extension of a composite with a linear functor. -/
theorem freeLift_comp_map {S : Signature} {D E : Type*} [Category D] [Preadditive D]
    [Linear k D] [Category E] [Preadditive E] [Linear k E] (F₁ : Obj S ⥤ D) (H : D ⥤ E)
    [H.Additive] [H.Linear k] {a b : Obj S} (f : LinDiagram k a b) :
    (freeLift k (F₁ ⋙ H)).map f = H.map ((freeLift k F₁).map f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Functor.map_add, Functor.map_add, Functor.map_add, hf, hg]
  | single d r => rw [freeLift_map_single, freeLift_map_single, Functor.map_smul]; rfl

local notation "hC" => extendedCartanDatum_dot_inl Λ C

variable (o : I ⊕ Fin ℓ → ℤ)

/-- The downward translation into the empty context, followed by the cover functor. -/
def downCover (μ : I ⊕ Fin ℓ → ℤ) : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ)) ⥤ (PCL).Presented :=
  (downInterpretation (RDc) (redWeight Wgt) k μ [] []).functor ⋙
    freeLift k ((coverMirror Wgt hC o).toLayerMap.functor ⋙
      (LocalMap.ofGen (coverColourMap Wgt hC o) (coverImage Wgt hC o PCL coverSign)).functor)

theorem coverCL_downLinear (μ : I ⊕ Fin ℓ → ℤ) {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))}
    (f : LinDiagram k a b) :
    coverCL Λ C hQ o (downLinear (RDc) (redWeight Wgt) k μ [] [] f) =
      (freeLift k (downCover Λ C hQ o μ)).map f := by
  rw [coverCL, coverLin, freeLift_map_layerLin]
  exact (freeLift_comp_map (downInterpretation (RDc) (redWeight Wgt) k μ [] []).functor _ f).symm

/-- The signed reflection of KLR diagrams, placed on upward strands of the Cautis–Lauda
presentation of the extended datum with rightmost region `o - μ`. -/
def upCover (μ : I ⊕ Fin ℓ → ℤ) : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ)) ⥤ (PCL).Presented :=
  KSig.ksFree (CL.qCL Sc) ⋙ CL.upFunctorC PCL (CL.qCL Sc) (presCL_cover_klr Λ C hQ) (o - μ)

/-- The reflected upward KLR relations with the Cautis–Lauda parameters vanish. -/
theorem upCover_relation (μ : I ⊕ Fin ℓ → ℤ) (r : KLR.Diagram.Rel (I ⊕ Fin ℓ)) :
    (freeLift k (upCover Λ C hQ o μ)).map (KLR.Diagram.relation k (CL.qCL Sc) r) = 0 := by
  rw [show upCover Λ C hQ o μ = _ ⋙ _ from rfl, freeLift_comp_map]
  have h := KSig.ksL_relation_of_symm k (fun a b _ => (CL.rename_swap_qCL (Sc) b a).symm) r
  change (CL.upFunctorC _ _ _ _).map (KSig.ksL _ _) = 0
  rw [h, Functor.map_zero]

omit [DecidableEq I] in
/-- The reflection of a downward word is the reversed upward word. -/
theorem coverWord_map_down (w : List (I ⊕ Fin ℓ)) :
    coverWord (w.map DoubleStrand.down) = ups w.reverse := by
  rw [coverWord, ups, List.map_reverse, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  rcases c with c | c <;> rfl

theorem downCover_obj (μ : I ⊕ Fin ℓ → ℤ) (a : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))) :
    (downCover Λ C hQ o μ).obj a = (PCL).obj (ob Wgt (o - μ) (ups a.word.reverse)) := by
  rw [← coverWord_map_down]
  exact congrArg (PCL).obj (coverObj_move Wgt hC o μ (a.word.map DoubleStrand.down))

theorem upCover_obj (μ : I ⊕ Fin ℓ → ℤ) (a : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))) :
    (upCover Λ C hQ o μ).obj a = (PCL).obj (ob Wgt (o - μ) (ups a.word.reverse)) := rfl

theorem downCover_obj_eq (μ : I ⊕ Fin ℓ → ℤ) (a : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))) :
    (downCover Λ C hQ o μ).obj a = (upCover Λ C hQ o μ).obj a :=
  (downCover_obj Λ C hQ o μ a).trans (upCover_obj Λ C hQ o μ a).symm

theorem upCover_map_ofLayer (μ : I ⊕ Fin ℓ → ℤ) (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ)))
    (hv : L.Valid) :
    (upCover Λ C hQ o μ).map (Diagram.ofLayer L hv) =
      ((KSig.ksg L.gen : ℤ) : k) • (PCL).diag (upDiag Wgt (o - μ) (KSig.ksD (Diagram.ofLayer L hv))) := by
  change (CL.upFunctorC PCL (CL.qCL Sc) (presCL_cover_klr Λ C hQ) (o - μ)).map
    (((KSig.ksgn [L] : ℤ) : k) • (KLR.Diagram.pres k (CL.qCL Sc)).diag
      (KSig.ksD (Diagram.ofLayer L hv))) = _
  rw [Functor.map_smul, CL.upFunctorC_diag]
  simp [KSig.ksgn]

omit [DecidableEq I] in
theorem coverMove_down_layers (ν : I ⊕ Fin ℓ → ℤ) {G : KLR.Diagram.Gen (I ⊕ Fin ℓ)}
    {g : Move I ℓ} (hg : downMove G = some g) :
    ∃ L₀ : Layer (psig Wgt), Diagram.layers (coverMove Wgt ν g) = [L₀] ∧ L₀.left = [] ∧
      L₀.gen = (upShape (KSig.kgen G)).gen Wgt ν := by
  rcases G with ⟨i | r⟩ | ⟨i | r, j | s⟩ <;>
    simp only [downMove, reduceCtorEq, Option.some.injEq] at hg <;> subst hg <;>
    exact ⟨_, rfl, rfl, rfl⟩

theorem downCover_map_ofLayer (μ : I ⊕ Fin ℓ → ℤ) (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ)))
    (hv : L.Valid) {g : Move I ℓ} (hg : downMove L.gen = some g) :
    (downCover Λ C hQ o μ).map (Diagram.ofLayer L hv) =
      eqToHom (downCover_obj_eq Λ C hQ o μ L.dom) ≫ (upCover Λ C hQ o μ).map (Diagram.ofLayer L hv) ≫
        eqToHom (downCover_obj_eq Λ C hQ o μ L.cod).symm := by
  have hF : (downCover Λ C hQ o μ).map (Diagram.ofLayer L hv) =
      (freeLift k ((coverMirror Wgt hC o).toLayerMap.functor ⋙
        (LocalMap.ofGen (coverColourMap Wgt hC o) (coverImage Wgt hC o PCL coverSign)).functor)).map
          (downLinearLayer (RDc) (redWeight Wgt) k μ [] [] L) :=
    congrArg (freeLift k ((coverMirror Wgt hC o).toLayerMap.functor ⋙
        (LocalMap.ofGen (coverColourMap Wgt hC o) (coverImage Wgt hC o PCL coverSign)).functor)).map
      (Interpretation.functor_map_ofLayer
        (downInterpretation (RDc) (redWeight Wgt) k μ [] []) L hv)
  refine hF.trans ?_
  rw [upCover_map_ofLayer, downLinearLayer_of_move _ _ _ _ _ _ L hg, LinDiagram.of,
    freeLift_map_single, one_smul, downLayerDiagram, Diagram.cast_eq]
  simp only [Functor.map_comp, eqToHom_map]
  rw [eqToHom_comp_iff, comp_eqToHom_iff]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  have hobj : ∀ (w₁ w₂ w₃ : List (DoubleStrand I ℓ)) (x : List (I ⊕ Fin ℓ)),
      w₁ ++ w₂ ++ w₃ = x.map DoubleStrand.down →
      ob Wgt (o - μ) (ups x.reverse) = (coverColourMap Wgt hC o).obj ((coverMirror Wgt hC o).obj
        (obj (RDc) (redWeight Wgt) μ (w₁ ++ w₂ ++ w₃))) := by
    intro w₁ w₂ w₃ x hx
    have h := coverObj_move Wgt hC o μ (w₁ ++ w₂ ++ w₃)
    simp only [List.nil_append, List.append_nil] at h
    rw [h, hx, coverWord_map_down]
  have hdom : [] ++ L.left.map DoubleStrand.down ++ g.bottom ++
      (L.right.map DoubleStrand.down ++ []) = L.dom.word.map DoubleStrand.down := by
    rw [(downMove_words hg).1]; simp [Layer.dom]
  have hcod : [] ++ L.left.map DoubleStrand.down ++ g.top ++
      (L.right.map DoubleStrand.down ++ []) = L.cod.word.map DoubleStrand.down := by
    rw [(downMove_words hg).2]; simp [Layer.cod]
  let L₁ := layer (RDc) (redWeight Wgt) μ ([] ++ L.left.map DoubleStrand.down) g
    (L.right.map DoubleStrand.down ++ [])
  let L'' := (coverMirror Wgt hC o).toLayerMap.layer L₁
  have hv'' : L''.Valid := (coverMirror Wgt hC o).toLayerMap.valid (layer_valid ..)
  obtain ⟨L₀, h₀, hl₀, hgen⟩ := coverMove_down_layers Λ C (o - L''.gen.1) hg
  refine (whisk_single_layer PCL _ _ _ _ ((coverColourMap Wgt hC o).obj ⟨L''.start, L''.left⟩)
    ((coverColourMap Wgt hC o).word L''.right)
    (LocalMap.genDom_whiskerOK (coverColourMap Wgt hC o) hv'') h₀
    (Diagram.cast (upDiag Wgt (o - μ) (KSig.ksD (Diagram.ofLayer L hv)))
      (hobj _ _ _ _ hdom) (hobj _ _ _ _ hcod)) rfl ?_ ?_ _ _ _ _).trans ?_
  · rw [hgen]
    change _ = (upShape (KSig.kgen L.gen)).gen Wgt (wt Wgt (o - μ) (ups L.left.reverse))
    rw [← coverWord_map_down, wt_coverWord Wgt hC o μ]
    rfl
  · have hc : ∀ (ν : I ⊕ Fin ℓ → ℤ) (z : List (DoubleStrand I ℓ)),
        (colours (RDc) (redWeight Wgt) ν z).length = z.length := fun ν z => by
      simpa only [List.length_map] using congrArg List.length (forget_colours _ _ ν z)
    have hw : ∀ (ν : I ⊕ Fin ℓ → ℤ) (t : List (Letter (I ⊕ Fin ℓ))),
        (wd Wgt ν t).length = t.length := by
      intro ν t
      induction t generalizing ν with
      | nil => rfl
      | cons a t ih => rw [wd_cons]; simp [ih]
    rw [hl₀]
    simp [L'', L₁, ColourMap.word_eq, SigMirror.layer, MirrorColourMap.word, layer, upLay, lay,
      KSig.klay, ups, hc, hw]
  · have hs : coverSign (k := k) g = ((KSig.ksg L.gen : ℤ) : k) := by
      rcases hG : L.gen with ⟨i | r⟩ | ⟨i | r, j | s⟩ <;> rw [hG] at hg <;>
        simp only [downMove, reduceCtorEq, Option.some.injEq] at hg <;> subst hg <;>
        simp [coverSign, KSig.ksg]
    erw [hs, Presentation.diag_cast]
    simp

theorem downCover_map_ofLayer_of_none (μ : I ⊕ Fin ℓ → ℤ) (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ)))
    (hv : L.Valid) (hg : downMove L.gen = none) :
    (downCover Λ C hQ o μ).map (Diagram.ofLayer L hv) = 0 := by
  have hF := congrArg (freeLift k ((coverMirror Wgt hC o).toLayerMap.functor ⋙
      (LocalMap.ofGen (coverColourMap Wgt hC o) (coverImage Wgt hC o PCL coverSign)).functor)).map
    (Interpretation.functor_map_ofLayer (downInterpretation (RDc) (redWeight Wgt) k μ [] []) L hv)
  refine hF.trans ?_
  have h0 := downLinearLayer_of_none (RDc) (redWeight Wgt) k μ [] [] L hg
  exact (congrArg _ h0).trans (Functor.map_zero _ _ _)

omit [DecidableEq I] in
/-- The colours of a word of upward strands are upward. -/
theorem upward_of_mem_wd_ups (ν : I ⊕ Fin ℓ → ℤ) (t : List (I ⊕ Fin ℓ))
    {c : (psig Wgt).Colour} (h : c ∈ wd Wgt ν (ups t)) : c.l.1 = true := by
  induction t generalizing ν with
  | nil => simp [ups] at h
  | cons a t ih =>
    rw [ups, List.map_cons, wd_cons, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact ih _ h

/-- A dot on an upward red strand, placed on the reflected upward strands, is cover
red-negligible. -/
theorem coverRedNegligible_upCover_redDot (μ : I ⊕ Fin ℓ → ℤ)
    (L : Layer (KLR.Diagram.sig (I ⊕ Fin ℓ))) (hv : L.Valid) (r : Fin ℓ)
    (hg : L.gen = .dot (.inr r)) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc ((upCover Λ C hQ o μ).map (Diagram.ofLayer L hv)) := by
  rw [upCover_map_ofLayer]
  refine CoverRedNegligible.smul.{u, v, w} _ ?_
  have hv' : (upLay Wgt (o - μ) (KSig.klay L)).Valid := lay_valid _ _ _ _ _
  have h1 : (upLay Wgt (o - μ) (KSig.klay L)).dom =
      ob Wgt (o - μ) (ups (KSig.kobj L.dom).word) := by rw [upLay_dom, KSig.klay_dom]
  have h2 : (upLay Wgt (o - μ) (KSig.klay L)).cod =
      ob Wgt (o - μ) (ups (KSig.kobj L.cod).word) := by rw [upLay_cod, KSig.klay_cod]
  have e : upDiag Wgt (o - μ) (KSig.ksD (Diagram.ofLayer L hv)) =
      Diagram.cast (Diagram.ofLayer _ hv') h1 h2 := Diagram.ext rfl
  rw [e, Presentation.diag_cast]
  have hd : CoverRedNegligible.{u, v, w} Λ C hQ hc ((PCL).diag (Diagram.ofLayer _ hv')) := by
    refine coverRedNegligible_redDot.{u, v, w} Λ C hQ hc (upLay Wgt (o - μ) (KSig.klay L)) hv' r
      (wt Wgt (o - μ) (ups (KSig.klay L).right)) ?_ ?_
    · simp [upLay, lay, KSig.klay, KSig.kgen, hg, upShape, Shape.gen, up]
    · intro c hc'
      left
      simp only [upLay, lay, KSig.klay] at hc'
      exact upward_of_mem_wd_ups Λ C _ _ hc'
  apply CoverRedNegligible.comp_left
  apply CoverRedNegligible.comp_right
  exact hd

omit [Field k] [DecidableEq I] in
/-- A boundary word of KLR diagrams for the extended datum with at most one red letter. -/
abbrev AtMostOneRed (x : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))) : Prop :=
  x.word.countP (fun c => c.isRight) ≤ 1

/-- **The downward translation agrees with the reflected upward image up to red dots.** On
diagrams between words with at most one red letter, the downward translation in the empty
context followed by the cover functor differs from the signed reflection on upward strands by a
cover red-negligible morphism. -/
theorem coverRedNegligible_downCover_sub_upCover (μ : I ⊕ Fin ℓ → ℤ)
    {a b : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (f : LinDiagram k a b) (ha : a.WF) (hb : b.WF)
    (hpa : a.word.countP (fun c => c.isRight) ≤ 1) (hpb : b.word.countP (fun c => c.isRight) ≤ 1) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc
      ((freeLift k (downCover Λ C hQ o μ)).map f -
        eqToHom (freeLift_obj_eq_on (R := k) _ _ AtMostOneRed
          (fun x _ _ => downCover_obj_eq Λ C hQ o μ x) a ha hpa) ≫
          (freeLift k (upCover Λ C hQ o μ)).map f ≫
          eqToHom (freeLift_obj_eq_on (R := k) _ _ AtMostOneRed
            (fun x _ _ => downCover_obj_eq Λ C hQ o μ x) b hb hpb).symm) := by
  -- The class is wrapped in a conjunction so that its unfolding to a family of statements
  -- indexed by admissible boundaries does not interfere with elaboration.
  let N : ∀ {x y : (PCL).Presented}, (x ⟶ y) → Prop := fun {x y} φ =>
    CoverRedNegligible.{u, v, w} Λ C hQ hc (c := (PCL).toObj x) (d := (PCL).toObj y) φ ∧ True
  have key : N ((freeLift k (downCover Λ C hQ o μ)).map f -
      eqToHom (freeLift_obj_eq_on (R := k) _ _ AtMostOneRed
        (fun x _ _ => downCover_obj_eq Λ C hQ o μ x) a ha hpa) ≫
        (freeLift k (upCover Λ C hQ o μ)).map f ≫
        eqToHom (freeLift_obj_eq_on (R := k) _ _ AtMostOneRed
          (fun x _ _ => downCover_obj_eq Λ C hQ o μ x) b hb hpb).symm) := by
    refine freeLift_map_sub_mem_of_layer_on (R := k) (downCover Λ C hQ o μ)
      (upCover Λ C hQ o μ) AtMostOneRed ?_ (fun x _ _ => downCover_obj_eq Λ C hQ o μ x) N
      ⟨CoverRedNegligible.zero, trivial⟩
      (fun hf hg => ⟨CoverRedNegligible.add hf.1 hg.1, trivial⟩)
      (fun {_ _} r {_} hf => ⟨CoverRedNegligible.smul r hf.1, trivial⟩)
      (fun {_ _ _} h {_} hf => ⟨CoverRedNegligible.comp_left h hf.1, trivial⟩)
      (fun {_ _ _} {_} h hf => ⟨CoverRedNegligible.comp_right h hf.1, trivial⟩) ?_ f ha hb hpa hpb
    · intro L _ hL
      change L.cod.word.countP _ ≤ 1
      rw [(perm_cod_word L).countP_eq]
      exact hL
    · intro L hv hd
      refine ⟨?_, trivial⟩
      cases hg : downMove L.gen with
      | some g =>
        rw [downCover_map_ofLayer Λ C hQ o μ L hv hg, sub_self]
        exact CoverRedNegligible.zero
      | none =>
        rw [downCover_map_ofLayer_of_none Λ C hQ o μ L hv hg, zero_sub, ← neg_one_smul k]
        refine CoverRedNegligible.smul _ ?_
        obtain ⟨st, lf, gen, rt⟩ := L
        rcases gen with ⟨i | r⟩ | ⟨i | r, j | s⟩
        · simp [downMove] at hg
        · apply CoverRedNegligible.comp_left
          apply CoverRedNegligible.comp_right
          exact coverRedNegligible_upCover_redDot.{u, v, w} Λ C hQ hc o μ _ hv r rfl
        · simp [downMove] at hg
        · simp [downMove] at hg
        · simp [downMove] at hg
        · exfalso
          have : 2 ≤ (lf ++ [Sum.inr r, Sum.inr s] ++ rt).countP Sum.isRight := by
            simp [List.countP_append]; omega
          exact absurd hd (by
            change ¬ (lf ++ [Sum.inr r, Sum.inr s] ++ rt).countP Sum.isRight ≤ 1
            omega)
  intro s t hs ht
  exact key.1 hs ht

theorem coverRedNegligible_of_sub {c d : Obj (psig Wgt)} {f g : (PCL).obj c ⟶ (PCL).obj d}
    (h₁ : CoverRedNegligible.{u, v, w} Λ C hQ hc (f - g))
    (h₂ : CoverRedNegligible.{u, v, w} Λ C hQ hc g) : CoverRedNegligible.{u, v, w} Λ C hQ hc f := by
  have h : CoverRedNegligible.{u, v, w} Λ C hQ hc (f - g + g) := CoverRedNegligible.add h₁ h₂
  rwa [sub_add_cancel] at h

/-- **Downward KLR relations with at most one red strand**, given the comparison of scalars.
If, on the reflected upward strands, the KLR relations with parameters `Qd` differ from those
with the Cautis–Lauda parameters by a cover red-negligible morphism, then the downward KLR
relations with parameters `Qd` and at most one red strand are cover red-negligible. -/
theorem coverRedNegligible_downRelation_le_one
    (Qd : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
    (hscal : ∀ (μ : I ⊕ Fin ℓ → ℤ) (r : KLR.Diagram.Rel (I ⊕ Fin ℓ)),
      r.dom.word.countP (fun c => c.isRight) ≤ 1 →
      CoverRedNegligible.{u, v, w} Λ C hQ hc ((freeLift k (upCover Λ C hQ o μ)).map
        (KLR.Diagram.relation k Qd r - KLR.Diagram.relation k (CL.qCL Sc) r)))
    (μ : I ⊕ Fin ℓ → ℤ) (r : KLR.Diagram.Rel (I ⊕ Fin ℓ))
    (hr : r.dom.word.countP (fun c => c.isRight) ≤ 1) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc
      (coverCL Λ C hQ o (downLinear (RDc) (redWeight Wgt) k μ [] []
        (KLR.Diagram.relation k Qd r))) := by
  rw [coverCL_downLinear]
  have hcod : r.cod.word.countP (fun c => c.isRight) ≤ 1 := by
    rw [(relCod_perm_dom r).countP_eq]; exact hr
  have hG : (freeLift k (upCover Λ C hQ o μ)).map (KLR.Diagram.relation k Qd r) =
      (freeLift k (upCover Λ C hQ o μ)).map
        (KLR.Diagram.relation k Qd r - KLR.Diagram.relation k (CL.qCL Sc) r) := by
    rw [Functor.map_sub, upCover_relation, sub_zero]
  apply coverRedNegligible_of_sub
  · exact coverRedNegligible_downCover_sub_upCover Λ C hQ hc o μ _
      (Signature.ok_of_subsingleton _ _) (Signature.ok_of_subsingleton _ _) hr hcod
  · apply CoverRedNegligible.comp_left
    apply CoverRedNegligible.comp_right
    rw [hG]
    exact hscal μ r hr

omit [DecidableEq I] in
theorem ncEval_C_mul_X_pow {A : Type*} [Ring A] [Algebra k A] (a : Fin 2 → A) (j : Fin 2)
    (c : k) (n : ℕ) :
    ncEval a (MvPolynomial.C c * MvPolynomial.X j ^ n : MvPolynomial (Fin 2) k) = c • a j ^ n := by
  rw [MvPolynomial.C_mul_X_pow_eq_monomial, ncEval_monomial, Algebra.smul_def]
  congr 1
  fin_cases j <;> simp [List.ofFn_succ, Finsupp.single_apply]

omit [DecidableEq I] in
theorem lpoly_add {w : Obj (KLR.Diagram.sig (I ⊕ Fin ℓ))} (y : Fin 2 → (w ⟶ w))
    (p q : MvPolynomial (Fin 2) k) :
    KLR.Diagram.lpoly k y (p + q) = KLR.Diagram.lpoly k y p + KLR.Diagram.lpoly k y q :=
  ncEval_add (A := End (Free.of k w)) _ _ _

/-- **The Cautis–Lauda parameters of the cyclotomic scalars.** For distinct colours, the
Cautis–Lauda polynomial of the scalars of the cover parameters is the cover parameter. -/
theorem qCL_cyclotomicScalars {a b : I ⊕ Fin ℓ} (hab : a ≠ b) :
    CL.qCL Sc a b = cyclotomicCoverQ C Λ Q a b := by
  rw [← TwoRep.brundanQ_eq_qCL _ (kkScalars_s_eq_zero _ sym _ (hS).homogeneous)]
  exact (eq_brundanQ _ sym _ (fun i j h p q hpq =>
    coeff_eq_zero_of_lt_of_hom _ ((hS).homogeneous i j h) p q hpq) hab).symm

/-- A scalar multiple of a positive power of a cover red-negligible dot, evaluated through the
reflected upward strands, is cover red-negligible. -/
theorem coverRedNegligible_lpoly_dot_pow (μ : I ⊕ Fin ℓ → ℤ) (a b : I ⊕ Fin ℓ) (j : Fin 2)
    (c : k) (n : ℕ)
    (hj : CoverRedNegligible.{u, v, w} Λ C hQ hc
      ((upCover Λ C hQ o μ).map (![KLR.Diagram.D0 a b, KLR.Diagram.D1 a b] j))) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc ((freeLift k (upCover Λ C hQ o μ)).map
      (KLR.Diagram.lpoly k ![KLR.Diagram.D0 a b, KLR.Diagram.D1 a b] (MvPolynomial.C c * MvPolynomial.X j ^ (n + 1)))) := by
  rw [KLR.Diagram.lpoly, ncEval_C_mul_X_pow, Functor.map_smul]
  refine CoverRedNegligible.smul.{u, v, w} _ ?_
  rw [pow_succ, End.mul_def, Functor.map_comp]
  apply CoverRedNegligible.comp_right
  rw [freeLift_map_of]
  exact hj

/-- **Comparison of scalars for the affine cover parameters.** If the black parameters `Qb`
agree with `Q` on distinct colours, then on the reflected upward strands the KLR relations with
the affine cover parameters of `Qb` differ from those with the Cautis–Lauda parameters by a
cover red-negligible morphism, on relations with at most one red strand. -/
theorem coverRedNegligible_affineCover_scalars (Qb : I → I → MvPolynomial (Fin 2) k)
    (hb : ∀ i j, i ≠ j → Qb i j = Q i j) (μ : I ⊕ Fin ℓ → ℤ) (r : KLR.Diagram.Rel (I ⊕ Fin ℓ))
    (hr : r.dom.word.countP (fun c => c.isRight) ≤ 1) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc ((freeLift k (upCover Λ C hQ o μ)).map
      (KLR.Diagram.relation k (affineCoverQ Qb Λ) r - KLR.Diagram.relation k (CL.qCL Sc) r)) := by
  cases r
  case sqNe c d h =>
    simp only [KLR.Diagram.relation, sub_sub_sub_cancel_left]
    rw [qCL_cyclotomicScalars Λ C hQ h]
    rcases c with i | s <;> rcases d with j | t
    · have hij : i ≠ j := fun e => h (congrArg Sum.inl e)
      have e : cyclotomicCoverQ C Λ Q (.inl i) (.inl j) = affineCoverQ Qb Λ (.inl i) (.inl j) := by
        simp [cyclotomicCoverQ, affineCoverQ, stendhalQ, hb i j hij]
      rw [e, sub_self, Functor.map_zero]
      apply CoverRedNegligible.zero
    · obtain ⟨c, n, e⟩ := cyclotomicCoverQ_inl_inr_eq C Λ Q i t
      have e' : affineCoverQ Qb Λ (.inl i) (.inr t) = stendhalQ Q Λ (.inl i) (.inr t) := by
        simp [affineCoverQ, stendhalQ]
      rw [e, e', lpoly_add, add_sub_cancel_left]
      apply coverRedNegligible_lpoly_dot_pow Λ C hQ hc o μ (.inl i) (.inr t) 1 c n
      exact coverRedNegligible_upCover_redDot Λ C hQ hc o μ (KLR.Diagram.lay [.inl i] (.dot (.inr t)) [])
        (KLR.Diagram.lay_valid _ _ _) t rfl
    · obtain ⟨c, n, e⟩ := cyclotomicCoverQ_inr_inl_eq C Λ Q s j
      have e' : affineCoverQ Qb Λ (.inr s) (.inl j) = stendhalQ Q Λ (.inr s) (.inl j) := by
        simp [affineCoverQ, stendhalQ]
      rw [e, e', lpoly_add, add_sub_cancel_left]
      apply coverRedNegligible_lpoly_dot_pow Λ C hQ hc o μ (.inr s) (.inl j) 0 c n
      exact coverRedNegligible_upCover_redDot Λ C hQ hc o μ (KLR.Diagram.lay [] (.dot (.inr s)) [.inl j])
        (KLR.Diagram.lay_valid _ _ _) s rfl
    · exact absurd hr (by simp [KLR.Diagram.Rel.dom])
  case braidQ c d h =>
    rcases c with i | s
    · have e : qbar (affineCoverQ Qb Λ (.inl i) d) = qbar (CL.qCL Sc (.inl i) d) := by
        rw [qCL_cyclotomicScalars Λ C hQ h, qbar_cyclotomicCoverQ_black]
        rcases d with j | t
        · have hij : i ≠ j := fun e => h (congrArg Sum.inl e)
          simp [affineCoverQ, stendhalQ, hb i j hij]
        · rfl
      simp only [KLR.Diagram.relation, e, sub_self, Functor.map_zero]
      apply CoverRedNegligible.zero
    · exact absurd hr (by simp [KLR.Diagram.Rel.dom])
  all_goals
    simp only [KLR.Diagram.relation, sub_self, Functor.map_zero]
    apply CoverRedNegligible.zero

/-- **Downward KLR relations in the empty context, affine cover parameters.** If the black
parameters `Qb` agree with `Q` on distinct colours, then every downward KLR relation with the
affine cover parameters of `Qb`, in the empty signed context, is cover red-negligible. -/
theorem coverRedNegligible_downRelation_affineCover (Qb : I → I → MvPolynomial (Fin 2) k)
    (hb : ∀ i j, i ≠ j → Qb i j = Q i j) (μ : I ⊕ Fin ℓ → ℤ)
    (r : KLR.Diagram.Rel (I ⊕ Fin ℓ)) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc
      (coverCL Λ C hQ o (downLinear (RDc) (redWeight Wgt) k μ [] []
        (KLR.Diagram.relation k (affineCoverQ Qb Λ) r))) :=
  coverRedNegligible_downRelation_empty_of_le_one Λ C hQ hc o (affineCoverQ Qb Λ)
    (fun s t => by simp [affineCoverQ])
    (fun μ r hr => coverRedNegligible_downRelation_le_one Λ C hQ hc o _
      (fun μ r hr => coverRedNegligible_affineCover_scalars Λ C hQ hc o Qb hb μ r hr) μ r hr)
    μ r

omit [DecidableEq I] in
/-- For the standard Khovanov–Lauda scalars, the Cautis–Lauda downward parameters are the
upward ones. -/
theorem clDownwardQ_kl (i j : I) :
    DoubleDiagram.clDownwardQ (CL.CLScalars.kl : CL.CLScalars C k) i j =
      CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j := by
  rw [DoubleDiagram.clDownwardQ, DoubleDiagram.reflectedDownward_qCL]
  simp [CL.CLScalars.kl]

/-- **Downward KLR relations at the standard Khovanov–Lauda scalars.** If the black
parameters `Q` are those of the standard Khovanov–Lauda scalars on distinct colours, then
every downward KLR relation with the affine cover of the Cautis–Lauda downward parameters,
in the empty signed context, is cover red-negligible (Webster, arXiv:1309.3796v3, §4.6, proof
of Lemma 4.29, for the KLR part). -/
theorem coverRedNegligible_downRelation_kl
    (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
    (μ : I ⊕ Fin ℓ → ℤ) (r : KLR.Diagram.Rel (I ⊕ Fin ℓ)) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc
      (coverCL Λ C hQ o (downLinear (RDc) (redWeight Wgt) k μ [] []
        (KLR.Diagram.relation k
          (affineCoverQ (DoubleDiagram.clDownwardQ (CL.CLScalars.kl : CL.CLScalars C k)) Λ) r))) :=
  coverRedNegligible_downRelation_affineCover Λ C hQ hc o _
    (fun i j h => (clDownwardQ_kl (C := C) (k := k) i j).trans (hstd i j h).symm) μ r

end Categorification.Stendhal
