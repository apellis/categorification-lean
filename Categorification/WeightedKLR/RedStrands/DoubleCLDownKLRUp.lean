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

end Categorification.Stendhal
