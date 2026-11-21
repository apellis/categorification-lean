/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumBubbleEval
import Categorification.KLR.CyclotomicAction.VacuumFakeValues
import Categorification.KLR.CyclotomicAction.VacuumBubbleReduction

/-!
# Fake bubbles act on `P_∅` by the signed elementary symmetric functions

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 3.25. At the region `λ` of `P_∅` the clockwise bubbles of colour `j` with negative
labels are the fake bubbles of degree index `n ≤ λ^j`. They are Grassmannian inverses of the
counterclockwise bubbles, which act by `vacTrace` (`univPres_ccwReal_vacuum`), so they act by
`vacFakeVal j n = (-1)^n e_n(p_j)` (`grassInv_vacTrace`).

* `vacEval`, `vacEvalLin`: evaluation at `P_∅`, as ring homomorphisms;
* `vacScalarHom`: the scalars of `Ř^λ_λ` acting on `P_∅`;
* `vacEvalLin_cwL`: the clockwise bubble of colour `j` with label `n - λ^j - 1`, `n ≤ λ^j`,
  acts on `P_∅` by `vacFakeVal j n`.
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

/-- `P_∅` as an object of the linear category of the region of `P_∅`. -/
abbrev vacObj : (univCyclotomicPresCLL.{u, v, w} hQ RD Λ hΛ).obj (vacRegion hQ RD Λ) :=
  (univVacuum.{u, v, w} hQ RD Λ hΛ).obj

/-- Evaluation at `P_∅` of endomorphisms of the empty word at its region, as a ring hom. -/
def vacEval :
    End ((CL.presCL RD k (univScalars hQ RD)).obj (ob RD (vacWt RD Λ) [])) →+*
      End (vacObj.{u, v, w} hQ RD Λ hΛ) :=
  RingHom.mk' {
    toFun := fun β => ((univCyclotomicPresCLL.{u, v, w} hQ RD Λ hΛ).map₂
      (show vacHom (k := k) hQ RD Λ [] rfl ⟶ vacHom hQ RD Λ [] rfl from β)).hom.app
        (vacObj.{u, v, w} hQ RD Λ hΛ)
    map_one' := by
      change ((univCyclotomicPresCLL.{u, v, w} hQ RD Λ hΛ).map₂ (𝟙 _)).hom.app _ = 𝟙 _
      rw [PrelaxFunctor.map₂_id]
      rfl
    map_mul' := fun β β' => by
      change ((univCyclotomicPresCLL.{u, v, w} hQ RD Λ hΛ).map₂
        ((show vacHom (k := k) hQ RD Λ [] rfl ⟶ vacHom hQ RD Λ [] rfl from β') ≫
          (show vacHom (k := k) hQ RD Λ [] rfl ⟶ vacHom hQ RD Λ [] rfl from β))).hom.app _ =
        _ ≫ _
      rw [PrelaxFunctor.map₂_comp]
      rfl }
  fun β β' => by
    change ((univCyclotomicPresCLL.{u, v, w} hQ RD Λ hΛ).map₂
      ((show vacHom (k := k) hQ RD Λ [] rfl ⟶ vacHom hQ RD Λ [] rfl from β) +
        (show vacHom (k := k) hQ RD Λ [] rfl ⟶ vacHom hQ RD Λ [] rfl from β'))).hom.app _ = _
    erw [Diagrams.BicatInterp.admissiblePseudofunctor_map₂_add]
    rfl

/-- Scalars of `Ř^λ_λ` acting on `P_∅`. -/
def vacScalarHom : UnivCycRing k lam →+* End (vacObj.{u, v, w} hQ RD Λ hΛ) where
  toFun c := c • 𝟙 _
  map_one' := one_smul _ _
  map_mul' c d := by
    change (c * d) • 𝟙 _ = (d • 𝟙 _) ≫ (c • 𝟙 _)
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, mul_comm]
  map_zero' := zero_smul _ _
  map_add' c d := add_smul _ _ _

/-- Linear diagrams on the empty word at the region of `P_∅`, evaluated at `P_∅`. -/
def vacEvalLin : LEnd RD k (ob RD (vacWt RD Λ) []) →+* End (vacObj.{u, v, w} hQ RD Λ hΛ) :=
  (vacEval hQ RD Λ hΛ).comp
    { toFun := fun f => (CL.presCL RD k (univScalars hQ RD)).lin f
      map_one' := Presentation.lin_id _ _
      map_mul' := fun f g => Presentation.lin_comp _ g f
      map_zero' := by
        change (CL.presCL RD k (univScalars hQ RD)).linFunctor.map 0 = 0
        exact Functor.map_zero _ _ _
      map_add' := fun f g => Presentation.lin_add _ f g }

/-- Counterclockwise bubbles act on `P_∅` by `vacTrace` (`univPres_ccwReal_vacuum`). -/
theorem vacEvalLin_ccwR (i : I) (m : ℕ) :
    vacEvalLin hQ RD Λ hΛ (ccwR RD k (vacWt RD Λ) i m) =
      vacScalarHom hQ RD Λ hΛ (vacTrace k lam i m) := by
  rw [ccwR, ite_eq_left (Int.natCast_nonneg m), Int.toNat_natCast]
  exact univPres_ccwReal_vacuum hQ RD Λ hΛ i m

include hΛ in
/-- **Fake bubbles at the vacuum**: the clockwise bubble of colour `i` with label
`n - λ^i - 1`, `n ≤ λ^i`, acts on `P_∅` by `vacFakeVal i n = (-1)^n e_n(p_i)`. -/
theorem vacEvalLin_cwL (i : I) (n : ℕ) (hn : n ≤ lam i) :
    vacEvalLin hQ RD Λ hΛ (cwL RD k (vacWt RD Λ) i ((n : ℤ) - lam i - 1)) =
      vacScalarHom hQ RD Λ hΛ (vacFakeVal k lam i n) := by
  have hi := ip_vacWt RD Λ hΛ i
  rw [cwL, ite_eq_right (by omega : ¬ (0 : ℤ) ≤ (n : ℤ) - lam i - 1),
    ite_eq_left (by omega : (0 : ℤ) ≤ (n : ℤ) - lam i - 1 + 1 - ip RD i (vacWt RD Λ)),
    show ((n : ℤ) - lam i - 1 + 1 - ip RD i (vacWt RD Λ)).toNat = n by omega,
    StrongSl2.map_grassInv, ← grassInv_vacTrace k lam i n, StrongSl2.map_grassInv]
  apply congrFun (TwoRep.grassInv_congr ?_)
  intro a ha
  rcases Nat.eq_zero_or_pos (lam i) with h0 | h0
  · rw [show -ip RD i (vacWt RD Λ) - 1 + (a : ℤ) = ((a - 1 : ℕ) : ℤ) by omega,
      vacEvalLin_ccwR, vacTrace_eq_zero_of_lam_eq_zero k lam i h0,
      vacTrace_eq_zero_of_lam_eq_zero k lam i h0]
  · rw [show -ip RD i (vacWt RD Λ) - 1 + (a : ℤ) = ((lam i - 1 + a : ℕ) : ℤ) by omega,
      vacEvalLin_ccwR]

end

end Categorification.KLR.CyclotomicAction
