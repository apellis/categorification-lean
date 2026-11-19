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

end Categorification.Stendhal
