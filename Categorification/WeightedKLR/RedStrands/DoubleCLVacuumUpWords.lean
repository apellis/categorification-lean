/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLVacuumFunctor
import Categorification.WeightedKLR.RedStrands.DoubleCLDownKLRUp
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverVacuumEvaluation
import Categorification.TwoRep.RouqUpWordsSigma

/-!
# Vacuum evaluation of upward words and the projected KLR action

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. On upward words of the Cautis–Lauda
presentation of the extended datum, the vacuum evaluation `vacuumEval` and the evaluation
through the cyclotomic Rouquier family differ by conjugation with the isomorphisms identifying
upward words with words of the family. Hence one vanishes exactly when the other does
(`vacuumEval_eq_zero_iff_upEvalP`). For the signed reflection of a KLR diagram, the latter is a
projected matrix entry of the KLR action of the vertical flip
(`vacuumEval_ksMat_eq_zero_iff`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction
  DoubleDiagram KL3.Diagram Diagrams.BicatInterp InductionAlong

universe u v w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- In a category with zero morphisms, a functor kills a morphism conjugated by isomorphisms
exactly when it kills the morphism. -/
theorem Functor.map_conj_eq_zero_iff {A B : Type*} [Category A] [Category B]
    [Limits.HasZeroMorphisms B] (G : A ⥤ B) {x x' y y' : A} (e : x ≅ y) (e' : x' ≅ y')
    (f : y ⟶ y') : G.map (e.hom ≫ f ≫ e'.inv) = 0 ↔ G.map f = 0 := by
  constructor
  · intro h
    have h' : G.map f = G.map e.inv ≫ G.map (e.hom ≫ f ≫ e'.inv) ≫ G.map e'.hom := by
      simp only [← G.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Iso.inv_hom_id_assoc]
    rw [h', h, Limits.zero_comp, Limits.comp_zero]
  · intro h
    simp only [G.map_comp, h, Limits.zero_comp, Limits.comp_zero]

variable {I : Type u} {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  [DecidableEq I] {k : Type v} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  (hQ : IsRouquierQ C Q) (ν : Multiset I)

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "L" => cyclotomicCoverHighest (I := I) (ℓ := ℓ)
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
local notation "μ" => stendhalWeight ℓ ν
set_option quotPrecheck false in
set_option hygiene false in
local notation "Fam" => cyclotomicFamily.{u, v, w} sym lead monic Wgt L topDeg deg
local notation "PCL" => KL3.Diagram.CL.presCL Wgt k Sc
set_option quotPrecheck false in
set_option hygiene false in
local notation "V" => emptyBlockObj.{u,v,w} S p Wgt L
set_option quotPrecheck false in
set_option hygiene false in
local notation "qAct" => cyclotomicFamily_upKLR.{u,v,w} sym lead monic Wgt L topDeg deg

/-- The component at the Stendhal block of the action of a 2-morphism of the cyclotomic family
on the cover vacuum, projected to the tensor-product algebra. -/
def familyVacuumEval {F G : (Fam).obj wt₀ ⟶ (Fam).obj (wtop Wgt wt₀ μ)} (η : F ⟶ G) :=
  (functor (RingHom.toNonUnitalRingHom (AlgHom.toRingHom π))).map
    ((η.hom.app (coverVacuum.{u, v, w} Λ C hQ)) (topBlk (RD := Wgt) (Λ := L) (ν := μ) rfl))

/-- `familyVacuumEval` as a functor on the 2-morphisms of the cyclotomic family. -/
def familyVacuumFunctor :
    ((Fam).obj wt₀ ⟶ (Fam).obj (wtop Wgt wt₀ μ)) ⥤
      ModuleCat (TensorProductAlgebra k Q Λ ν) where
  obj F := (functor (RingHom.toNonUnitalRingHom (AlgHom.toRingHom π))).obj
    ((F.obj.obj (coverVacuum.{u, v, w} Λ C hQ)) (topBlk (RD := Wgt) (Λ := L) (ν := μ) rfl))
  map η := familyVacuumEval Λ C hQ ν η
  map_id _ := (functor _).map_id _
  map_comp _ _ := (functor _).map_comp _ _

/-- **Vacuum evaluation of upward words is conjugate to the family evaluation.** For a
2-morphism between upward words of the Cautis–Lauda presentation, the vacuum evaluation at the
Stendhal block vanishes exactly when the projected component of its evaluation through the
cyclotomic family does. -/
theorem vacuumEval_eq_zero_iff_upEvalP {t t' : Seq μ}
    (φ : (PCL).obj (ob Wgt wt₀ (ups (KLR.Diagram.word t))) ⟶
      (PCL).obj (ob Wgt wt₀ (ups (KLR.Diagram.word t')))) :
    vacuumEval.{u, v, w} Λ C hQ ν (blockWeight_wtop rfl) (RouqFamily.cond_word wt₀ t)
        (RouqFamily.cond_word wt₀ t') φ = 0 ↔
      familyVacuumEval Λ C hQ ν
        ((Fam).upEvalP Sc PCL (presCL_cover_rel Λ C hQ) wt₀ φ) = 0 := by
  have h := Functor.map_conj_eq_zero_iff (familyVacuumFunctor Λ C hQ ν)
    ((Fam).upIso wt₀ t (RouqFamily.cond_word wt₀ t)).symm
    ((Fam).upIso wt₀ t' (RouqFamily.cond_word wt₀ t')).symm
    (admissibleQuotientMap (RouqFamily.genImg Fam Sc) PCL (presCL_cover_rel Λ C hQ)
      Signature.IsEven.odd_eq_false (RouqFamily.cond_word wt₀ t)
      (RouqFamily.cond_word wt₀ t') φ)
  exact h.symm

/-- **Vacuum evaluation of a reflected diagram is a projected entry of the KLR action.** The
vacuum evaluation of the `(t, s)` entry of the signed reflection of the diagram of `a`, placed on
upward strands of the Cautis–Lauda presentation, vanishes exactly when the projected `(t, s)`
entry of the cover action of the vertical flip of `a` does. -/
theorem vacuumEval_ksMat_eq_zero_iff (a : FreeAlgebra k (KLR.Gen μ)) (t s : Seq μ) :
    vacuumEval.{u, v, w} Λ C hQ ν (blockWeight_wtop rfl) (RouqFamily.cond_word wt₀ t)
        (RouqFamily.cond_word wt₀ s)
        ((matEndMap k (CL.upFunctorC PCL (CL.qCL Sc) (presCL_cover_klr Λ C hQ) wt₀) _
          (KSig.ksMat k (CL.qCL Sc) μ (fun a b _ => (CL.rename_swap_qCL Sc b a).symm)
            (KLR.Diagram.toDiagFree k (CL.qCL Sc) μ a))) t s) = 0 ↔
      projectedCoverVacuumEntry.{u, v, w} Λ ν C hQ (KLRAlgebra.sigma sym (KLRAlgebra.mk k S μ a))
        t s = 0 := by
  rw [vacuumEval_eq_zero_iff_upEvalP]
  have h := (Fam).upActP_ksMat_toDiagFree Sc PCL (presCL_cover_rel Λ C hQ) qAct sym
    (fun a b _ => (CL.rename_swap_qCL Sc b a).symm) (presCL_cover_klr Λ C hQ) wt₀ a
  have hts := congrFun (congrFun h t) s
  exact Iff.of_eq (congrArg (fun η => familyVacuumEval Λ C hQ ν η = 0) hts)

end Categorification.Stendhal
