/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLVacuumEvaluation
import Categorification.WeightedKLR.RedStrands.DoubleCLDownwardBlock
import Categorification.WeightedKLR.RedStrands.DoubleAllDownBoundary
import Categorification.WeightedKLR.RedStrands.DoubleViolatingQuotient
import Categorification.KLR.CyclotomicAction.VacuumSupport

/-!
# The vacuum evaluation functor of the downward block

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The all-down boundary words of black
content `ν` act from the cyclotomic vacuum of the extended datum to its Stendhal block. This
file fixes the regions: with the cover right region at the vacuum weight, the cover left
region of every all-down word is the Stendhal block (`blockWeight_stendhalWeight`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction
  DoubleDiagram KL3.Diagram Diagrams.BicatInterp InductionAlong

universe u v w v₁

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Regions

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {C' : CartanDatum (I ⊕ Fin ℓ)}
  {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (W : WeightDatum C' X Y)
  (hC : ∀ i j, C'.dot (.inl i) (.inl j) = C.dot i j) (o : X)

/-- **Regions of a reflected boundary.** The reflection of a double boundary with left weight
zero and right weight `right` is a KL word from the region `o - right` to the region `o`. -/
theorem cond_cover {right : X} {w : List (DoubleStrand I ℓ)}
    (hw : endWeight (blackDatum W hC) (redWeight W) 0 w = right) :
    Diagrams.BicatInterp.Cond (o - right) o ((coverColourMap W hC o).obj
      ((coverMirror W hC o).obj (obj (blackDatum W hC) (redWeight W) 0 w))) := by
  have hword : ((coverColourMap W hC o).obj ((coverMirror W hC o).obj
      (obj (blackDatum W hC) (redWeight W) 0 w))).word = wd W (o - 0) (coverWord w) := by
    change ((colours (blackDatum W hC) (redWeight W) 0 w).map (coverColour o)).reverse = _
    exact coverColours W hC o 0 w
  have hwt : wt W (o - 0) (coverWord w) = o - right := by
    rw [wt_coverWord W hC o, hw]
  refine ⟨?_, ?_, ?_⟩
  · rw [hword, ← hwt]; exact ok_wd W _ _
  · rw [hword, ← hwt, endR_wd, sub_zero]
  · exact congrArg (fun x : X => o - x) ((colours_endR _ _ _ _).trans hw)

end Regions

variable {I : Type u} {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "L" => cyclotomicCoverHighest (I := I) (ℓ := ℓ)

/-- **The Stendhal block is the left region of the all-down words.** In coordinates, the
block weight of the Stendhal weight of `ν` is the vacuum block weight minus the common right
weight of the all-down words of black content `ν`. -/
theorem blockWeight_stendhalWeight (ν : Multiset I) :
    blockWeight Wgt L (stendhalWeight ℓ ν) =
      blockWeight Wgt L 0 - downRightWeight (coordinateDatum Λ C) (coordinateRedWeights Λ C) ν := by
  simp only [blockWeight, downRightWeight, stendhalWeight, Multiset.map_add, Multiset.map_map,
    Multiset.sum_add, Multiset.map_zero, Multiset.sum_zero, List.sum_ofFn, Function.comp_def,
    coordinateRedWeights, redWeight, Finset.sum_neg_distrib]
  change _ = _ - (_ - (ν.map fun j => WeightDatum.iX Wgt (Sum.inl j)).sum)
  rw [show (Multiset.map (fun x => WeightDatum.iX Wgt (Sum.inr x)) Finset.univ.val).sum =
      ∑ r, WeightDatum.iX Wgt (Sum.inr r) from rfl]
  abel

section Evaluation

variable [DecidableEq I] {k : Type v} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  (hQ : IsRouquierQ C Q) (hc : CoverDotCentral Λ C Q) (ν : Multiset I)

local notation "S" => cyclotomicCoverQ C Λ Q
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "Sc" => cyclotomicScalars sym lead Wgt deg
local notation "p" => cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)
local notation "monic" => cyclotomicCoverPolynomial_monic (k := k)
local notation "topDeg" => cyclotomicCoverPolynomial_natDegree (k := k) Λ C
local notation "wt₀" => (blockWeight Wgt L 0 : I ⊕ Fin ℓ → ℤ)
local notation "π" => cyclotomicCoverToTensor (Q := Q) Λ ν C
set_option quotPrecheck false in
set_option hygiene false in
local notation "Fam" => cyclotomicFamily.{u, v, w} sym lead monic Wgt L topDeg deg
local notation "PCL" => KL3.Diagram.CL.presCL Wgt k Sc
set_option quotPrecheck false in
set_option hygiene false in
local notation "V" => emptyBlockObj.{u,v,w} S p Wgt L

/-- The cyclotomic vacuum of the extended datum, as an object of its weight space: `R^Λ(∅)` on
the empty block and zero on the other blocks of the vacuum weight. -/
abbrev coverVacuum := familyObj sym lead monic topDeg deg V

/-- **Projected vacuum evaluation.** A morphism of the Cautis–Lauda presentation of the
extended datum acts on the cyclotomic vacuum; its component at the Stendhal block of `ν` is
projected to the tensor-product algebra by extension of scalars. -/
def vacuumEval {s : I ⊕ Fin ℓ → ℤ} (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s)
    {c d : Obj (psig Wgt)} (ha : Cond s wt₀ c) (hb : Cond s wt₀ d)
    (φ : (PCL).obj c ⟶ (PCL).obj d) :=
  (functor (RingHom.toNonUnitalRingHom (AlgHom.toRingHom π))).map
    (((admissibleQuotientMap (RouqFamily.genImg Fam Sc) PCL (presCL_cover_rel Λ C hQ)
      Signature.IsEven.odd_eq_false ha hb φ).hom.app
        (coverVacuum.{u, v, w} Λ C hQ)) ⟨stendhalWeight ℓ ν, hν⟩)

variable {Λ C hQ ν}

/-- **Red-negligible morphisms evaluate to zero.** -/
theorem vacuumEval_eq_zero {s : I ⊕ Fin ℓ → ℤ}
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s) {c d : Obj (psig Wgt)}
    (ha : Cond s wt₀ c) (hb : Cond s wt₀ d) {φ : (PCL).obj c ⟶ (PCL).obj d}
    (h : CoverRedNegligible.{u, v, w} Λ C hQ hc φ) :
    vacuumEval.{u, v, w} Λ C hQ ν hν ha hb φ = 0 :=
  CoverRed.project_eq_zero (h ha hb) ν hν _

theorem vacuumEval_comp {s : I ⊕ Fin ℓ → ℤ}
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s) {c d e : Obj (psig Wgt)}
    (ha : Cond s wt₀ c) (hb : Cond s wt₀ d) (he : Cond s wt₀ e)
    (φ : (PCL).obj c ⟶ (PCL).obj d) (ψ : (PCL).obj d ⟶ (PCL).obj e) :
    vacuumEval.{u, v, w} Λ C hQ ν hν ha he (φ ≫ ψ) =
      vacuumEval.{u, v, w} Λ C hQ ν hν ha hb φ ≫ vacuumEval.{u, v, w} Λ C hQ ν hν hb he ψ := by
  unfold vacuumEval
  rw [admissibleQuotientMap_comp _ _ _ _ ha hb he]
  exact Functor.map_comp _ _ _

theorem vacuumEval_id {s : I ⊕ Fin ℓ → ℤ}
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s) {c : Obj (psig Wgt)}
    (ha : Cond s wt₀ c) :
    vacuumEval.{u, v, w} Λ C hQ ν hν ha ha (𝟙 _) = 𝟙 _ := by
  unfold vacuumEval
  rw [admissibleQuotientMap_id]
  exact CategoryTheory.Functor.map_id _ _

theorem vacuumEval_add {s : I ⊕ Fin ℓ → ℤ}
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s) {c d : Obj (psig Wgt)}
    (ha : Cond s wt₀ c) (hb : Cond s wt₀ d) (φ ψ : (PCL).obj c ⟶ (PCL).obj d) :
    vacuumEval.{u, v, w} Λ C hQ ν hν ha hb (φ + ψ) =
      vacuumEval.{u, v, w} Λ C hQ ν hν ha hb φ + vacuumEval.{u, v, w} Λ C hQ ν hν ha hb ψ := by
  unfold vacuumEval
  rw [admissibleQuotientMap_add]
  exact Functor.map_add _

theorem vacuumEval_smul {s : I ⊕ Fin ℓ → ℤ}
    (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s) {c d : Obj (psig Wgt)}
    (ha : Cond s wt₀ c) (hb : Cond s wt₀ d) (r : k) (φ : (PCL).obj c ⟶ (PCL).obj d) :
    vacuumEval.{u, v, w} Λ C hQ ν hν ha hb (r • φ) =
      r • vacuumEval.{u, v, w} Λ C hQ ν hν ha hb φ := by
  unfold vacuumEval
  rw [admissibleQuotientMap_smul]
  have hπ : ScalarCompatible (k := k)
      (RingHom.toNonUnitalRingHom (AlgHom.toRingHom π)) := fun c => by
    change π (algebraMap k _ c) = _ * π 1
    rw [AlgHom.commutes, map_one, mul_one]
  have := functor_linear hπ
  rw [← Functor.map_smul]
  rfl

/-- The reflection of a double boundary of the coordinate datum, at the vacuum region. -/
abbrev coverObj (a : Obj (signature (coordinateDatum Λ C) (redWeight Wgt))) :
    Obj (psig Wgt) :=
  (coverColourMap Wgt (extendedCartanDatum_dot_inl Λ C) wt₀).obj
    ((coverMirror Wgt (extendedCartanDatum_dot_inl Λ C) wt₀).obj a)

section Presented
/-- **Vacuum evaluation of presented double diagrams.** A morphism of the presented double
diagram category, reflected into the Cautis–Lauda presentation of the extended datum, acts on
the projected cyclotomic vacuum; the relations of `P` act by zero. -/
def presentedVacuumEval {s : I ⊕ Fin ℓ → ℤ} (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s)
    {P : Presentation.{v, v₁} (signature (coordinateDatum Λ C) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc wt₀ P) (hwf : P.WFDom)
    {a b : Obj (signature (coordinateDatum Λ C) (redWeight Wgt))}
    (ha : Cond s wt₀ (coverObj a)) (hb : Cond s wt₀ (coverObj b)) (f : P.obj a ⟶ P.obj b) :=
  Quot.liftOn f (fun g => vacuumEval.{u, v, w} Λ C hQ ν hν ha hb (coverCL Λ C hQ wt₀ g))
    fun g g' h => by
      have hm := (HomRel.compClosure_iff_self P.homRel g g').mp h
      have hn : CoverRedNegligible.{u, v, w} Λ C hQ hc (coverCL Λ C hQ wt₀ (g - g')) :=
        CoverRelsNegligible.mem_ideal hP hwf hm
      have hz := vacuumEval_eq_zero hc hν ha hb hn
      have hsplit : g = (g - g') + g' := (sub_add_cancel g g').symm
      change vacuumEval.{u, v, w} Λ C hQ ν hν ha hb (coverCL Λ C hQ wt₀ g) = _
      conv_lhs => rw [hsplit]
      have hadd : coverCL Λ C hQ wt₀ (g - g' + g') =
          coverCL Λ C hQ wt₀ (g - g') + coverCL Λ C hQ wt₀ g' :=
        coverLin_add _ _ _ _ _ _ _
      rw [hadd, vacuumEval_add, hz, zero_add]

end Presented

section Laws

variable {s : I ⊕ Fin ℓ → ℤ}
  (hν : blockWeight (cyclotomicCoverWeightDatum Λ C) cyclotomicCoverHighest
    (stendhalWeight ℓ ν) = s)
  {P : Presentation.{v, v₁}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc
    (blockWeight (cyclotomicCoverWeightDatum Λ C) cyclotomicCoverHighest 0) P)
  (hwf : P.WFDom)
  {a b e : Obj (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C)))}
  (ha : Cond s
    (blockWeight (cyclotomicCoverWeightDatum Λ C) cyclotomicCoverHighest 0 : I ⊕ Fin ℓ → ℤ)
    (coverObj a))
  (hb : Cond s
    (blockWeight (cyclotomicCoverWeightDatum Λ C) cyclotomicCoverHighest 0 : I ⊕ Fin ℓ → ℤ)
    (coverObj b))
  (he : Cond s
    (blockWeight (cyclotomicCoverWeightDatum Λ C) cyclotomicCoverHighest 0 : I ⊕ Fin ℓ → ℤ)
    (coverObj e))

theorem presentedVacuumEval_lin (g : LinDiagram k a b) :
    presentedVacuumEval.{u, v, w} hc hν hP hwf ha hb (P.lin g) =
      vacuumEval.{u, v, w} Λ C hQ ν hν ha hb (coverCL Λ C hQ wt₀ g) :=
  rfl

theorem presentedVacuumEval_comp (f : P.obj a ⟶ P.obj b) (g : P.obj b ⟶ P.obj e) :
    presentedVacuumEval.{u, v, w} hc hν hP hwf ha he (f ≫ g) =
      presentedVacuumEval.{u, v, w} hc hν hP hwf ha hb f ≫
        presentedVacuumEval.{u, v, w} hc hν hP hwf hb he g := by
  obtain ⟨f, rfl⟩ := P.lin_surjective f
  obtain ⟨g, rfl⟩ := P.lin_surjective g
  rw [← P.lin_comp, presentedVacuumEval_lin, presentedVacuumEval_lin, presentedVacuumEval_lin,
    show coverCL Λ C hQ wt₀ (f ≫ g) = coverCL Λ C hQ wt₀ f ≫ coverCL Λ C hQ wt₀ g from
      coverLin_comp _ _ _ _ _ _ _, vacuumEval_comp hν ha hb he]

theorem presentedVacuumEval_id :
    presentedVacuumEval.{u, v, w} hc hν hP hwf ha ha (𝟙 (P.obj a)) = 𝟙 _ := by
  rw [← P.lin_id, presentedVacuumEval_lin,
    show coverCL Λ C hQ wt₀ (𝟙 (Free.of k a)) = 𝟙 _ from coverLin_id _ _ _ _ _ _,
    vacuumEval_id]

theorem presentedVacuumEval_add (f g : P.obj a ⟶ P.obj b) :
    presentedVacuumEval.{u, v, w} hc hν hP hwf ha hb (f + g) =
      presentedVacuumEval.{u, v, w} hc hν hP hwf ha hb f +
        presentedVacuumEval.{u, v, w} hc hν hP hwf ha hb g := by
  obtain ⟨f, rfl⟩ := P.lin_surjective f
  obtain ⟨g, rfl⟩ := P.lin_surjective g
  rw [← P.lin_add, presentedVacuumEval_lin, presentedVacuumEval_lin, presentedVacuumEval_lin,
    show coverCL Λ C hQ wt₀ (f + g) = coverCL Λ C hQ wt₀ f + coverCL Λ C hQ wt₀ g from
      coverLin_add _ _ _ _ _ _ _, vacuumEval_add]

theorem presentedVacuumEval_smul (r : k) (f : P.obj a ⟶ P.obj b) :
    presentedVacuumEval.{u, v, w} hc hν hP hwf ha hb (r • f) =
      r • presentedVacuumEval.{u, v, w} hc hν hP hwf ha hb f := by
  obtain ⟨f, rfl⟩ := P.lin_surjective f
  rw [← P.lin_smul, presentedVacuumEval_lin, presentedVacuumEval_lin,
    show coverCL Λ C hQ wt₀ (r • f) = r • coverCL Λ C hQ wt₀ f from
      coverLin_smul _ _ _ _ _ _ _, vacuumEval_smul]

end Laws

section Functor

local notation "rt" => downRightWeight (coordinateDatum Λ C) (coordinateRedWeights Λ C) ν

omit [DecidableEq I] in
/-- **Regions of an all-down boundary.** The reflection of a boundary of the downward block of
black content `ν` runs from the Stendhal block to the vacuum region. -/
theorem cond_downBoundary
    {P : Presentation.{v, v₁} (signature (coordinateDatum Λ C) (redWeight Wgt)) k}
    (b : DoubleDiagram.BoundaryCategory (Λ := coordinateRedWeights Λ C) P rt) :
    Cond (wt₀ - rt) wt₀ (coverObj (obj (coordinateDatum Λ C) (redWeight Wgt) 0 b.val.word)) :=
  cond_cover Wgt (extendedCartanDatum_dot_inl Λ C) wt₀ b.property

/-- **The vacuum evaluation functor of the downward block.** Each boundary of black content
`ν` is sent to the projected Stendhal component of its reflected word applied to the cyclotomic
vacuum of the extended datum, and each presented diagram acts by its Cautis–Lauda
reflection. -/
def downVacuumFunctor
    {P : Presentation.{v, v₁} (signature (coordinateDatum Λ C) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc wt₀ P) (hwf : P.WFDom) :
    DoubleDiagram.BoundaryCategory (Λ := coordinateRedWeights Λ C) P rt ⥤
      ModuleCat.{max u v w} (TensorProductAlgebra k Q Λ ν) where
  obj b := (functor (RingHom.toNonUnitalRingHom (AlgHom.toRingHom π))).obj
    ((((Fam).model.word (wt₀ - rt)
      (coverObj (obj (coordinateDatum Λ C) (redWeight Wgt) 0 b.val.word)).word wt₀
        (cond_downBoundary b).1 (cond_downBoundary b).2.1).obj.obj
          (coverVacuum.{u, v, w} Λ C hQ)) ⟨stendhalWeight ℓ ν, blockWeight_stendhalWeight Λ C ν⟩)
  map f := presentedVacuumEval.{u, v, w} hc (blockWeight_stendhalWeight Λ C ν) hP hwf
    (cond_downBoundary _) (cond_downBoundary _) f.hom
  map_id _ := presentedVacuumEval_id hc (blockWeight_stendhalWeight Λ C ν) hP hwf _
  map_comp f g := presentedVacuumEval_comp hc (blockWeight_stendhalWeight Λ C ν) hP hwf _ _ _
    f.hom g.hom

variable {P : Presentation.{v, v₁} (signature (coordinateDatum Λ C) (redWeight Wgt)) k}
  (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc wt₀ P) (hwf : P.WFDom)

instance : (downVacuumFunctor hc hP hwf).Additive where
  map_add {_ _} {f g} :=
    presentedVacuumEval_add hc (blockWeight_stendhalWeight Λ C ν) hP hwf _ _ f.hom g.hom

instance : (downVacuumFunctor hc hP hwf).Linear k where
  map_smul {_ _} f r :=
    presentedVacuumEval_smul hc (blockWeight_stendhalWeight Λ C ν) hP hwf _ _ r f.hom

end Functor


end Evaluation

end Categorification.Stendhal
