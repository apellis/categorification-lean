/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumBubbleEval
import Categorification.KLR.CyclotomicAction.VacuumEval
import Categorification.TwoRep.RouqUpBubblesPresentation

/-!
# Bubbles to the right of upward words scale vacuum entries

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 3.25. The comparison map `End_𝒰(⊕_𝐢 F_𝐢 λ) → Ř^λ` is `Ř^λ_λ`-linear for the action
of the bubbles at the region `λ` of `P_∅`: an endomorphism `β` of the empty word that acts on
`P_∅` by a scalar `c ∈ Ř^λ_λ`, placed to the right of the upward strands, multiplies every vacuum
entry by `c`.

* `upEvalP_bubAtC_vacuum`: `β` to the right of the word of `t` acts at `P_∅` by `c`;
* `vacBubMat`: the diagonal matrix of `β` placed to the right of the upward words of weight `ν`;
* `vacCoeff_vacBubMat_mul`: `vacCoeff (vacBubMat β * φ) t s = c · vacCoeff φ t s`;
* `vacCoeff_vacBubMat_ccw_mul`: for the counterclockwise bubbles the scalar is `vacTrace`.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory TwoRep QuantumGroup KLRAlgebra StringDiagrams Diagrams.BicatInterp
open KL3.Diagram

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)

attribute [local instance] ScalarRestriction.linearCatHom ScalarRestriction.precompLinear
  ScalarRestriction.postcompLinear

/-- An endomorphism `β` of the empty word at the region of `P_∅` that acts on a module `W` by a
scalar `c` acts by `c` on `W` also when placed to the right of the upward word of `t`. -/
theorem upEvalP_bubAtC_vacuum {ν : Multiset I} (t : KLR.Seq ν)
    (β : End ((CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) [])))
    (c : UnivCycRing k lam) {W}
    (hβ : (admissibleQuotientMap (RouqFamily.genImg (univFamily (lam := lam) hQ RD Λ hΛ)
      (univScalars hQ RD)) (CL.presCL RD k (univScalars hQ RD)) (univPres_rel hQ RD Λ hΛ)
      Signature.IsEven.odd_eq_false (RouqFamily.bubbleNil (RD := RD) (vacWt RD Λ)).property
      (RouqFamily.bubbleNil (RD := RD) (vacWt RD Λ)).property β).hom.app
        W = c • 𝟙 _) :
    (((univFamily.{u, v, w} hQ RD Λ hΛ).upEvalP (univScalars hQ RD)
        (CL.presCL RD k (univScalars hQ RD)) (univPres_rel hQ RD Λ hΛ) (vacWt RD Λ)
        (CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ)
          (ups (KLR.Diagram.word t)) β)).hom.app W) = c • 𝟙 _ := by
  rw [RouqFamily.upEvalP_bubAtC]
  change 𝟙 _ ≫ ((univFamily.{u, v, w} hQ RD Λ hΛ).wordCell (vacWt RD Λ) t).obj.map
    ((admissibleQuotientMap (RouqFamily.genImg (univFamily (lam := lam) hQ RD Λ hΛ)
      (univScalars hQ RD)) (CL.presCL RD k (univScalars hQ RD)) (univPres_rel hQ RD Λ hΛ)
      Signature.IsEven.odd_eq_false (RouqFamily.bubbleNil (RD := RD) (vacWt RD Λ)).property
      (RouqFamily.bubbleNil (RD := RD) (vacWt RD Λ)).property β).hom.app W) ≫ 𝟙 _ = _
  rw [hβ, Category.id_comp, Category.comp_id]
  exact (Functor.map_smul
    (F := ((univFamily.{u, v, w} hQ RD Λ hΛ).wordCell (vacWt RD Λ) t).obj) _ _).trans
    (by erw [CategoryTheory.Functor.map_id]; rfl)

/-- The diagonal matrix of a bubble `β` placed to the right of the upward words of weight `ν` at
the region of `P_∅`. -/
def vacBubMat (ν : Multiset I)
    (β : End ((CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) []))) :
    KLR.Diagram.MatEnd (fun t : KLR.Seq ν =>
      (CL.presCL RD k (univScalars hQ RD)).obj
        (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word t)))) := fun t s =>
  (1 : KLR.Diagram.MatEnd (fun t : KLR.Seq ν =>
      (CL.presCL RD k (univScalars hQ RD)).obj
        (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word t))))) t s ≫
    CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) (ups (KLR.Diagram.word s)) β

/-- Entries of a product with `vacBubMat β`: `β` is placed to the right of the target word. -/
theorem vacBubMat_mul_apply {ν : Multiset I}
    (β : End ((CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) [])))
    (φ : KLR.Diagram.MatEnd (fun t : KLR.Seq ν =>
      (CL.presCL RD k (univScalars hQ RD)).obj
        (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word t))))) (t s : KLR.Seq ν) :
    (vacBubMat hQ RD Λ ν β * φ) t s = φ t s ≫
      CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ) (ups (KLR.Diagram.word s)) β := by
  rw [KLR.Diagram.MatEnd.mul_apply]
  simp only [vacBubMat, ← Category.assoc, ← Preadditive.sum_comp]
  congr 1
  exact congrFun (congrFun (one_mul φ) t) s

/-- **Bubbles scale vacuum entries** (Webster, arXiv:1309.3796v2, proof of Prop. 3.25): if `β`
acts on `P_∅` by `c ∈ Ř^λ_λ`, then `β` placed to the right of the upward strands multiplies every
vacuum entry by `c`. -/
theorem vacCoeff_vacBubMat_mul {ν : Multiset I}
    (β : End ((CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) [])))
    (c : UnivCycRing k lam)
    (hβ : (admissibleQuotientMap (RouqFamily.genImg (univFamily (lam := lam) hQ RD Λ hΛ)
      (univScalars hQ RD)) (CL.presCL RD k (univScalars hQ RD)) (univPres_rel hQ RD Λ hΛ)
      Signature.IsEven.odd_eq_false (RouqFamily.bubbleNil (RD := RD) (vacWt RD Λ)).property
      (RouqFamily.bubbleNil (RD := RD) (vacWt RD Λ)).property β).hom.app
        (univVacuum.{u, v, w} hQ RD Λ hΛ).obj = c • 𝟙 _)
    (φ : KLR.Diagram.MatEnd (fun t : KLR.Seq ν =>
      (CL.presCL RD k (univScalars hQ RD)).obj
        (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word t))))) (t s : KLR.Seq ν) :
    vacCoeff.{u, v, w} hQ RD Λ hΛ ν (vacBubMat hQ RD Λ ν β * φ) t s =
      algebraMap _ (CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν) c *
        vacCoeff.{u, v, w} hQ RD Λ hΛ ν φ t s := by
  unfold vacCoeff
  have h1 : ((univFamily.{u, v, w} hQ RD Λ hΛ).upActP (univScalars hQ RD)
      (CL.presCL RD k (univScalars hQ RD)) (univPres_rel hQ RD Λ hΛ) (vacWt RD Λ) ν
      (vacBubMat hQ RD Λ ν β * φ)) t s =
      (univFamily.{u, v, w} hQ RD Λ hΛ).upEvalP (univScalars hQ RD)
        (CL.presCL RD k (univScalars hQ RD)) (univPres_rel hQ RD Λ hΛ) (vacWt RD Λ) (φ t s) ≫
      (univFamily.{u, v, w} hQ RD Λ hΛ).upEvalP (univScalars hQ RD)
        (CL.presCL RD k (univScalars hQ RD)) (univPres_rel hQ RD Λ hΛ) (vacWt RD Λ)
        (CL.bubAtC (CL.presCL RD k (univScalars hQ RD)) (vacWt RD Λ)
          (ups (KLR.Diagram.word s)) β) := by
    exact (congrArg (fun f => (univFamily.{u, v, w} hQ RD Λ hΛ).upEvalP (univScalars hQ RD)
      (CL.presCL RD k (univScalars hQ RD)) (univPres_rel hQ RD Λ hΛ) (vacWt RD Λ) f)
      (vacBubMat_mul_apply hQ RD Λ β φ t s)).trans (RouqFamily.upEvalP_comp _ _ _ _ _ _ _)
  rw [h1]
  erw [comp_app_apply]
  refine (congrArg (wcoord _ _ _ _ _ _ _ _ s) (?_ : _ =
    algebraMap (UnivCycRing k lam) (CycKLR (UnivCycRing k lam) (cycQ k lam Q)
      (univCycPoly k lam) ν) c •
      ((((univFamily.{u, v, w} hQ RD Λ hΛ).upActP (univScalars hQ RD)
        (CL.presCL RD k (univScalars hQ RD)) (univPres_rel hQ RD Λ hΛ) (vacWt RD Λ) ν
        φ t s).hom.app (familyObj _ _ _ _ _ _) (topBlk rfl)).hom
      (wgen _ _ _ _ _ _ rfl (univVacGen RD Λ) t)))).trans ?_
  · have hA := upEvalP_bubAtC_vacuum hQ RD Λ hΛ s β c hβ
    have h2 := congrArg ModuleCat.Hom.hom (congrFun hA (topBlk rfl))
    exact (congrFun (congrArg DFunLike.coe h2) _).trans rfl
  · erw [map_smul, smul_eq_mul]

/-- The counterclockwise bubbles at the region of `P_∅`, placed to the right of the upward
strands, multiply vacuum entries by the traces `vacTrace`, which generate `Ř^λ_λ`
(`adjoin_vacTrace_eq_top`). -/
theorem vacCoeff_vacBubMat_ccw_mul {ν : Multiset I} (i : I) (m : ℕ)
    (φ : KLR.Diagram.MatEnd (fun t : KLR.Seq ν =>
      (CL.presCL RD k (univScalars hQ RD)).obj
        (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word t))))) (t s : KLR.Seq ν) :
    vacCoeff.{u, v, w} hQ RD Λ hΛ ν (vacBubMat hQ RD Λ ν
        ((CL.presCL RD k (univScalars hQ RD)).diag (ccwReal RD (vacWt RD Λ) i m)) * φ) t s =
      algebraMap _ (CycKLR (UnivCycRing k lam) (cycQ k lam Q) (univCycPoly k lam) ν)
        (vacTrace k lam i m) * vacCoeff.{u, v, w} hQ RD Λ hΛ ν φ t s :=
  vacCoeff_vacBubMat_mul hQ RD Λ hΛ _ _ (univPres_ccwReal_vacuum hQ RD Λ hΛ i m) φ t s

end

end Categorification.KLR.CyclotomicAction
