/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumIdealBubbles
import Categorification.KLR.CyclotomicAction.Vacuum
import Categorification.KLR.BaseChange
import Categorification.TwoRep.RouqUpWordsPresentation

/-!
# Upward diagrams at the vacuum act through the KLR algebra

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 3.25. The comparison map `End_𝒰(⊕_𝐢 F_𝐢 λ) → Ř^λ` sends the upward KLR diagrams
(dots and crossings on upward strands ending at the region `λ` of `P_∅`) to the KLR generators.
This file sets up the first half of this statement:

* `univScalars_klr`: the KLR relations, with the parameters `qCL` of the Cautis–Lauda scalars of
  `Q`, hold on upward strands of the Cautis–Lauda presentation over `k`;
* `vacUpHom`: the resulting algebra homomorphism from the KLR algebra to the endomorphisms of
  the upward words `⊕_t E_t 1_λ` at the region of `P_∅` (Webster's `F_𝐢 λ`);
* `upActP_vacUpHom`: evaluated through the cyclotomic Rouquier family over `Ř^λ_λ`, `vacUpHom r`
  is the action `klrAct` of the image of `r` in the KLR algebra over `Ř^λ_λ`. With `klrAct_wgen`
  (`Vacuum`), this computes the action of upward diagrams on `P_∅`.

The parameters `qCL` agree with `Q` on distinct colours (`qCL_univScalars`), which is all the KLR
relations see (`KLRAlgebra.mapRingHom`).
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory TwoRep QuantumGroup StringDiagrams Diagrams.BicatInterp
open KL3.Diagram

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k] [Nontrivial k] {lam : I → ℕ}
  {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ∀ i, (lam i : ℤ) = RD.pair (RD.iY i) Λ)

attribute [local instance] ScalarRestriction.linearCatHom ScalarRestriction.precompLinear
  ScalarRestriction.postcompLinear

/-- **The KLR relations on upward strands** of the Cautis–Lauda presentation over `k`, with
the parameters `qCL` of the Cautis–Lauda scalars of `Q`. -/
theorem univScalars_klr :
    CL.KLRHolds (CL.presCL RD k (univScalars hQ RD)) (CL.qCL (univScalars hQ RD)) := by
  intro μ r
  have h := (CL.presCL RD k (univScalars hQ RD)).lin_rel_self (.inr (.klr μ r))
  have hr' : (fun i => ((CL.CLScalars.r (univScalars hQ RD) i : k))) = fun _ => 1 :=
    funext fun _ => rfl
  change (CL.presCL RD k (univScalars hQ RD)).lin (upLin RD k μ (CL.relationR k
    (CL.qCL (univScalars hQ RD)) (fun i => ((CL.CLScalars.r (univScalars hQ RD) i : k))) r)) = 0
    at h
  rwa [hr', CL.relationR_one] at h

/-- The Cautis–Lauda parameters of the scalars of `Q` are `Q` on distinct colours. -/
theorem qCL_univScalars {i j : I} (hij : i ≠ j) : CL.qCL (univScalars hQ RD) i j = Q i j := by
  rw [← TwoRep.brundanQ_eq_qCL _ (kkScalars_s_eq_zero C hQ.klrSymm _ hQ.homogeneous)]
  exact (eq_brundanQ C hQ.klrSymm _ (fun i j h p q hpq =>
    coeff_eq_zero_of_lt_of_hom C (hQ.homogeneous i j h) p q hpq) hij).symm

/-- The relations of the Cautis–Lauda presentation over `k` hold in the cyclotomic family over
`Ř^λ_λ`. -/
theorem univPres_rel (r : (CL.presCL RD k (univScalars hQ RD)).Rel) {s t : X}
    (ha : Cond s t ((CL.presCL RD k (univScalars hQ RD)).dom r))
    (hb : Cond s t ((CL.presCL RD k (univScalars hQ RD)).cod r)) :
    admissibleMap (RouqFamily.genImg (univFamily (lam := lam) hQ RD Λ hΛ) (univScalars hQ RD))
      ha hb ((CL.presCL RD k (univScalars hQ RD)).rel r) = 0 :=
  RouqFamily.presCL_rel (univFamily hQ RD Λ hΛ) (univScalars hQ RD)
    (univFamily_brundanUpKLR hQ RD Λ hΛ)
    (cyclotomicFamily_mixedInversion RD Λ hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading
      (univCycPoly_monic k lam) (univCycPoly_natDegree_pair RD Λ hΛ)
      (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji))
    (fun _ => rfl) (kkScalars_s_eq_zero C hQ.klrSymm _ hQ.homogeneous) r ha hb

/-- **Upward KLR diagrams at the region of `P_∅`**: the algebra homomorphism from the KLR algebra
(with the parameters `qCL`) to the endomorphisms of the upward words `⊕_t E_t 1_λ` of the
Cautis–Lauda presentation, `λ` the region of `P_∅`. -/
def vacUpHom (ν : Multiset I) :
    KLRAlgebra k (CL.qCL (univScalars hQ RD)) ν →ₐ[k]
      KLR.Diagram.MatEnd (fun t : KLR.Seq ν => (CL.presCL RD k (univScalars hQ RD)).obj
        (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word t)))) :=
  (KL3.Diagram.matEndMap k (CL.upFunctorC (CL.presCL RD k (univScalars hQ RD))
    (CL.qCL (univScalars hQ RD)) (univScalars_klr hQ RD) (vacWt RD Λ)) _).comp
    (KLR.Diagram.diagREquiv k (CL.qCL (univScalars hQ RD)) ν).toAlgHom

/-- `vacUpHom` on the class of an element of the free algebra. -/
theorem vacUpHom_mk (ν : Multiset I) (a : FreeAlgebra k (KLR.Gen ν)) :
    vacUpHom hQ RD Λ ν (KLRAlgebra.mk k _ ν a) =
      KL3.Diagram.matEndMap k (CL.upFunctorC (CL.presCL RD k (univScalars hQ RD))
        (CL.qCL (univScalars hQ RD)) (univScalars_klr hQ RD) (vacWt RD Λ)) _
        (KLR.Diagram.toDiagFree k _ ν a) := by
  exact congrArg (KL3.Diagram.matEndMap k (CL.upFunctorC (CL.presCL RD k (univScalars hQ RD))
    (CL.qCL (univScalars hQ RD)) (univScalars_klr hQ RD) (vacWt RD Λ)) _)
    (KLR.Diagram.toDiagR_mk (k := k) (Q := CL.qCL (univScalars hQ RD)) a)

/-- The coefficient change from `k` to `Ř^λ_λ` respects the KLR parameters on distinct colours. -/
theorem map_qCL_univScalars (i j : I) (hij : i ≠ j) :
    MvPolynomial.map (algebraMap k (UnivCycRing k lam)) (CL.qCL (univScalars hQ RD) i j) =
      cycQ k lam Q i j := by
  rw [qCL_univScalars hQ RD hij]; rfl

/-- The KLR algebra with the parameters `qCL` over `k` maps to the KLR algebra over `Ř^λ_λ`. -/
abbrev vacKLRMap (ν : Multiset I) :
    KLRAlgebra k (CL.qCL (univScalars hQ RD)) ν →+* KLRAlgebra (UnivCycRing k lam) (cycQ k lam Q) ν :=
  KLRAlgebra.mapRingHom (algebraMap k (UnivCycRing k lam)) (map_qCL_univScalars hQ RD)

/-- **Upward diagrams at the vacuum act through the KLR algebra over `Ř^λ_λ`**: evaluated
through the cyclotomic Rouquier family, `vacUpHom r` is the action `klrAct` of the image of `r`
in the KLR algebra over `Ř^λ_λ`. -/
theorem upActP_vacUpHom (ν : Multiset I) (r : KLRAlgebra k (CL.qCL (univScalars hQ RD)) ν) :
    (univFamily hQ RD Λ hΛ).upActP (univScalars hQ RD) (CL.presCL RD k (univScalars hQ RD))
        (univPres_rel hQ RD Λ hΛ) (vacWt RD Λ) ν (vacUpHom hQ RD Λ ν r) =
      RouqFamily.klrAct (cyclotomicFamily_upKLR hQ.cycQ.klrSymm hQ.cycQ.polyInY_leading
        (univCycPoly_monic k lam) RD Λ (univCycPoly_natDegree_pair RD Λ hΛ)
        (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji)) (vacWt RD Λ)
        (vacKLRMap hQ RD ν r) := by
  obtain ⟨a, rfl⟩ := KLRAlgebra.mk_surjective (k := k) (Q := CL.qCL (univScalars hQ RD)) r
  rw [vacUpHom_mk]
  refine Eq.trans (DFunLike.congr_fun ((univFamily hQ RD Λ hΛ).upActP_comp_upFunctorC
    (univScalars hQ RD) (CL.presCL RD k (univScalars hQ RD)) (univPres_rel hQ RD Λ hΛ)
    (CL.qCL (univScalars hQ RD)) (univScalars_klr hQ RD) (vacWt RD Λ) ν) a) ?_
  rw [KLRAlgebra.mapRingHom_mk]
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    rw [AlgHom.commutes, KLRAlgebra.freeToKLR_algebraMap, AlgHom.commutes]
    rfl
  | grade1 g =>
    rw [KLRAlgebra.freeToKLR_ι]
    cases g with
    | idem t => exact (RouqData.klrActFree_fe t).trans (RouqFamily.klrAct_e _ t).symm
    | dot b => exact (RouqData.klrActFree_fx b).trans (RouqFamily.klrAct_dot _ b).symm
    | cross j => exact (RouqData.klrActFree_fψ j).trans (RouqFamily.klrAct_cross _ j).symm
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

end

end Categorification.KLR.CyclotomicAction
