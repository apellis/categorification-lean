/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumEval
import Categorification.KLR.CyclotomicAction.VacuumIdealBubbles

/-!
# The vacuum entries vanish on the ideal `I`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 3.25: the comparison map `End_𝒰(⊕_𝐢 F_𝐢 λ) → Ř^λ` is defined on the quotient by the
ideal `I` of 2-morphisms factoring through `F_𝐣 E_j 1_λ`. In terms of the vacuum entries
`vacCoeff`:

* `vacCoeff_eq_zero_of_mem_vacIdeal`: if the `(t, s)` entry of a matrix of upward 2-morphisms
  lies in `vacIdeal`, its vacuum entry vanishes.
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

/-- The upward word of `t` as a 1-morphism out of the region of `P_∅`. -/
abbrev vacUpHom₁ {ν : Multiset I} (t : KLR.Seq ν) :
    vacRegion hQ RD Λ ⟶ (⟨⟨(TwoRep.wtop RD (vacWt RD Λ) ν : X)⟩⟩ :
      RevBicat (CL.presCL RD k (univScalars hQ RD)).Bicat) :=
  vacHom hQ RD Λ (ups (KLR.Diagram.word t)) (RouqFamily.cond_word (vacWt RD Λ) t).2.2

/-- **The vacuum entries vanish on `I`** (Webster, arXiv:1309.3796v2, proof of Prop. 3.25). -/
theorem vacCoeff_eq_zero_of_mem_vacIdeal {ν : Multiset I}
    (φ : KLR.Diagram.MatEnd (fun t : KLR.Seq ν =>
      (CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) (ups (KLR.Diagram.word t)))))
    (t s : KLR.Seq ν)
    (hφ : (show vacUpHom₁ hQ RD Λ t ⟶ vacUpHom₁ hQ RD Λ s from φ t s) ∈
      vacIdeal hQ RD Λ _ _) :
    vacCoeff.{u, v, w} (lam := lam) hQ RD Λ hΛ ν φ t s = 0 := by
  have h0 := univVacuum_map₂_eq_zero_of_mem_vacIdeal.{u, v, w} hQ RD Λ hΛ hφ
  have h1 : ((univCyclotomicPresCLL.{u, v, w} hQ RD Λ hΛ).map₂
      (show vacUpHom₁ hQ RD Λ t ⟶ vacUpHom₁ hQ RD Λ s from φ t s)).hom.app
        (univVacuum.{u, v, w} hQ RD Λ hΛ).obj = 0 := congrArg (fun f => f.hom) h0
  unfold vacCoeff
  erw [comp_app_apply, comp_app_apply]
  have h2 : (admissibleQuotientMap (RouqFamily.genImg (univFamily (lam := lam) hQ RD Λ hΛ)
      (univScalars hQ RD)) (CL.presCL RD k (univScalars hQ RD)) (univPres_rel hQ RD Λ hΛ)
      Signature.IsEven.odd_eq_false (RouqFamily.cond_word (vacWt RD Λ) t)
      (RouqFamily.cond_word (vacWt RD Λ) s) (φ t s)).hom.app
        (univVacuum.{u, v, w} hQ RD Λ hΛ).obj = 0 := h1
  erw [h2, zero_app_apply, map_zero, map_zero]
