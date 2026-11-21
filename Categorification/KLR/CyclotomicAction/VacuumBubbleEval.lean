/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumEvalIdeal
import Categorification.KLR.CyclotomicAction.VacuumBubble
import Categorification.TwoRep.RouqFakeBubbles

/-!
# Bubbles at the vacuum act on `P_∅` by the traces `vacTrace`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 3.25.

* `univPres_ccwReal_vacuum`: the counterclockwise bubble of colour `i` with `m` dots, drawn in
  the region `λ` of `P_∅`, acts on `P_∅` by the scalar `vacTrace i m ∈ Ř^λ_λ`.
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

/-- **Bubbles at the vacuum**: the counterclockwise bubble of colour `i` with `m` dots in the
region of `P_∅` acts on `P_∅` by the scalar `vacTrace i m`. -/
theorem univPres_ccwReal_vacuum (i : I) (m : ℕ) :
    ((univCyclotomicPresCLL.{u, v, w} hQ RD Λ hΛ).map₂
      (show vacHom (k := k) hQ RD Λ [] rfl ⟶ vacHom hQ RD Λ [] rfl from
        (CL.presCL RD k (univScalars hQ RD)).diag (ccwReal RD (vacWt RD Λ) i m))).hom.app
        (univVacuum.{u, v, w} hQ RD Λ hΛ).obj =
      vacTrace k lam i m • 𝟙 _ := by
  have hb := (univFamily (lam := lam) hQ RD Λ hΛ).bubble_ccwL (univScalars hQ RD) i
    (sub_add_cancel (vacWt RD Λ) (RD.iX i)) rfl (m : ℤ)
  have hc : ccwL RD k (vacWt RD Λ) i (m : ℤ) =
      LinDiagram.of (ccwReal RD (vacWt RD Λ) i m) := by
    rw [ccwL, ite_eq_left (Int.natCast_nonneg m), Int.toNat_natCast]
  rw [hc] at hb
  have h2 : (univCyclotomicPresCLL.{u, v, w} hQ RD Λ hΛ).map₂
      (show vacHom (k := k) hQ RD Λ [] rfl ⟶ vacHom hQ RD Λ [] rfl from
        (CL.presCL RD k (univScalars hQ RD)).diag (ccwReal RD (vacWt RD Λ) i m)) =
      ((univFamily (lam := lam) hQ RD Λ hΛ).loc i
        (sub_add_cancel (vacWt RD Λ) (RD.iX i)) rfl).cw (m : ℤ) := hb
  rw [h2]
  refine (globalLoc_cw_app_of_vacuum.{u, max u v, w} RD Λ hQ.cycQ.klrSymm
    hQ.cycQ.polyInY_leading (univCycPoly_monic k lam) (univCycPoly_natDegree_pair RD Λ hΛ)
    (fun i j hji => hQ.cycQ.polyInY_degree_pair RD i j hji) i _ rfl
    (univVacuum.{u, v, w} hQ RD Λ hΛ).obj (fun _ hβ => isZero_emptyBlockObj hβ) m).trans ?_
  rw [coeff_modByMonic_univCycPoly]
  rfl

end

end Categorification.KLR.CyclotomicAction
