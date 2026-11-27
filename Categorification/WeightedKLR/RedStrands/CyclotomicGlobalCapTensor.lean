/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.GlobalLocCap
import Categorification.TwoRep.CyclotomicAbsentAdjunction
import Categorification.TwoRep.CyclotomicRouqCapTrace
import Categorification.WeightedKLR.RedStrands.CyclotomicRedAbsentCap

/-!
# The leftward cap of the cyclotomic weight spaces on corner tensors

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.25 (input for the red/down dot crossing). The
leftward cap `E_i F_i ⟶ 1` of Brundan, arXiv:1501.00350v1, (1.15) and (1.17), on the
cyclotomic weight spaces acts on a corner tensor `z ⊗ n` at every block by the opposite cap
`cyclotomicOppositeCap` of `z`: the corner trace when the colour `i` is present in the block,
and the last dot-unit coordinate when it is absent.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra.AbsentColour.BoundaryAdjunction

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (a : I → Polynomial k) (β : Multiset I)
  (hsym : KLRSymm Q)
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) =
    -RD.pair (RD.iY i) (RD.iX j)) (hi : i ∉ β)

/-- **The dot-unit coefficients on corner tensors** (Kang–Kashiwara, arXiv:1102.4677v4,
Theorem 5.2, absent colour): the `d`-th inverse coefficient of `z ⊗ n` is the `d`-th dot-unit
coordinate of `z` acting on `n`. -/
theorem coefficient_app_tmul (d : ℕ) (hd : d < (RD.pair (RD.iY i) (Λ - (β.map RD.iX).sum)).toNat)
    (N : ModuleCat.{max u v w} (CycKLR k Q a β)) (z : Corner Q i a β) (n : N) :
    (coefficient.{u, v, w} Q i a β hsym hQ ha RD Λ hΛ hdeg hi d).app N
        ((resIndEquiv Q i a β N).symm (BalancedTensor.tmul z n)) =
      (finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi).symm z ⟨d, hd⟩ • n := by
  erw [coefficient_app Q i a β hsym hQ ha RD Λ hΛ hdeg hi d hd]
  change (tensorCoefficients Q i a β N hsym hQ ha RD Λ hΛ hdeg hi)
    ((resIndEquiv Q i a β N) ((resIndEquiv Q i a β N).symm (BalancedTensor.tmul z n))) _ = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end Categorification.KLR.KLRAlgebra.AbsentColour.BoundaryAdjunction

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory TwoRep QuantumGroup
  KLRAlgebra.AbsentColour
open scoped ModuleCat.Algebra

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}

/-- The comparison of `res ∘ ind` along the last embedding with the restriction of induction
used for corner tensors (`AbsentColour.EF`). -/
def resIndIso (i : I) (β : Multiset I) (N : ModuleCat.{max (max u v) w} (CycKLR k Q a β)) :
    (res.{u, v, w} Q a i (rfl : {i} + β = {i} + β)).obj ((ind Q a i rfl).obj N) ≅
      (restrictionFunctor Q i a β).obj ((inductionFunctor Q i a β).obj N) :=
  (res.{u, v, w} Q a i rfl).mapIso ((indIso Q a i β).app N) ≪≫
    (resIso Q a i β).app ((inductionFunctor Q i a β).obj N)

variable {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

theorem inv_comp_hom_apply {R : Type*} [Ring R] {A B D : ModuleCat.{w} R} (e : A ≅ B)
    (f : A ⟶ D) (t : A) : (e.inv ≫ f).hom (e.hom.hom t) = f.hom t := by
  change (e.hom ≫ e.inv ≫ f).hom t = _
  rw [Iso.hom_inv_id_assoc]

theorem hom_comp_inv_apply {R : Type*} [Ring R] {A B D : ModuleCat.{w} R} (e : A ≅ B)
    (f : B ⟶ D) (t : B) : (e.hom ≫ f).hom (e.inv.hom t) = f.hom t := by
  change (e.inv ≫ e.hom ≫ f).hom t = _
  rw [Iso.inv_hom_id_assoc]

/-- The corner tensor `z ⊗ n` as an element of `E_i F_i` at the block `β`. -/
def capTensor (i : I) {y z : X} (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (β : WeightBlocks RD Λ y) (c : Corner Q i a β.1) (n : M β) :
    ((globalE.{u, v, w} Q a RD Λ i h₂ ≫ globalF Q a RD Λ i h₂).obj.obj M) β :=
  (cupIso Q a RD Λ i h₂ M β).hom.hom ((resIndIso i β.1 (M β)).inv.hom
    ((resIndEquiv Q i a β.1 (M β)).symm (BalancedTensor.tmul c n)))

/-- **The leftward cap of the weight spaces on corner tensors** (Brundan, arXiv:1501.00350v1,
(1.15), (1.17); Kang–Kashiwara, arXiv:1102.4677v4, Theorem 5.2): at every block `β`, the cap
of `globalLoc` sends `z ⊗ n` to the opposite cap of `z` acting on `n`. -/
theorem globalLoc_capL_capTensor (i : I) {x y z : X} (h₁ : x + RD.iX i = y)
    (h₂ : y + RD.iX i = z)
    (M : ∀ β : WeightBlocks RD Λ y, ModuleCat.{max (max u v) w} (CycKLR k Q a β.1))
    (β : WeightBlocks RD Λ y) (c : Corner Q i a β.1) (n : M β) :
    ((globalLoc.{u, v, w} RD Λ hQ hlead ha hΛ hdeg i h₁ h₂).capL.hom.app M β).hom
        (capTensor RD Λ i h₂ M β c n) =
      Stendhal.cyclotomicOppositeCap Q i β.1 hQ hlead RD (hdeg i) a ha Λ (hΛ i) c • n := by
  by_cases hβ : i ∈ β.1
  · obtain ⟨γ, rfl⟩ := exists_blockSucc_of_mem RD Λ i h₁ β hβ
    have key := globalLoc_capL_app RD Λ hQ hlead ha hΛ hdeg i h₁ h₂ M γ
    have hb := blockLoc_capL.{u, v, w} hQ hlead ha RD Λ hΛ hdeg i γ.1
    erw [hb] at key
    rw [show (globalLoc.{u, v, w} RD Λ hQ hlead ha hΛ hdeg i h₁ h₂).capL.hom.app M
      (blockSucc RD Λ i h₁ γ) = (blockEval RD Λ M (blockSucc RD Λ i h₁ γ)).map
        (globalLoc.{u, v, w} RD Λ hQ hlead ha hΛ hdeg i h₁ h₂).capL from rfl, key]
    refine (inv_comp_hom_apply (cupIso Q a RD Λ i h₂ M (blockSucc RD Λ i h₁ γ)) _ _).trans ?_
    refine (hom_comp_inv_apply (resIndIso i _ (M (blockSucc RD Λ i h₁ γ)))
      ((ConcreteAdjunction.loc.{u, v, w} Q i a γ.1 hQ hlead ha RD Λ (hΛ i) (hdeg i)).capL.hom.app
        (M (blockSucc RD Λ i h₁ γ))) _).trans ?_
    refine (ConcreteAdjunction.capL_app_tmul Q i a γ.1 hQ hlead ha RD Λ (hΛ i) (hdeg i)
      (M (blockSucc RD Λ i h₁ γ)) c n).trans ?_
    erw [Stendhal.cyclotomicOppositeCap_present]
    rfl
  · have hnp := pair_nonpos_of_not_mem Q a RD Λ hΛ hdeg i β hβ
    have hw := blockLoc_weight RD Λ i β
    simp only [Stendhal.cyclotomicOppositeCap, dite_eq_right hβ]
    rcases hnp.lt_or_eq with hneg | hzero
    · have hm : (-RD.pair (RD.iY i) y - 1).toNat < (-RD.pair (RD.iY i) y).toNat := by omega
      have hg := SumInvFrom.g'_eq
        (((globalLoc.{u, v, w} RD Λ hQ hlead ha hΛ hdeg i h₁ h₂).iN hnp).map (blockEval RD Λ M β))
        (locNegBoundary RD Λ hQ hlead ha hΛ hdeg i h₁ h₂ M β hβ) hm
      rw [show (globalLoc.{u, v, w} RD Λ hQ hlead ha hΛ hdeg i h₁ h₂).capL.hom.app M β =
        (blockEval RD Λ M β).map (globalLoc.{u, v, w} RD Λ hQ hlead ha hΛ hdeg i h₁ h₂).capL
          from rfl, RouqLoc.capL_of_neg hneg, RouqLoc.capN, dite_eq_left hnp]
      change ((((globalLoc.{u, v, w} RD Λ hQ hlead ha hΛ hdeg i h₁ h₂).iN hnp).map
        (blockEval RD Λ M β)).g' _).hom _ = _
      rw [hg]
      refine (inv_comp_hom_apply (cupIso Q a RD Λ i h₂ M β) _ _).trans ?_
      have hd : (-RD.pair (RD.iY i) y - 1).toNat <
          (RD.pair (RD.iY i) (Λ - (β.1.map RD.iX).sum)).toNat := by omega
      refine (hom_comp_inv_apply (resIndIso i _ (M β))
        ((BoundaryAdjunction.coefficient.{u, v, w} Q i a β.1 hQ hlead ha RD Λ (hΛ i) (hdeg i) hβ
          _).app (M β)) _).trans ?_
      refine (BoundaryAdjunction.coefficient_app_tmul Q i a β.1 hQ hlead ha RD Λ (hΛ i) (hdeg i)
        hβ _ hd (M β) c n).trans ?_
      unfold oppositeCap
      rw [dite_eq_left (by omega)]
      have hidx : (⟨(-RD.pair (RD.iY i) y - 1).toNat, hd⟩ :
          Fin (RD.pair (RD.iY i) (Λ - (β.1.map RD.iX).sum)).toNat) =
          ⟨(RD.pair (RD.iY i) (Λ - (β.1.map RD.iX).sum)).toNat - 1, by omega⟩ :=
        Fin.ext (by simp only; omega)
      rw [hidx]
      rfl
    · have hY := isZero_of_coefficients Q a i _ (blockBoundary.{u, v, w} hQ hlead ha RD Λ hΛ hdeg i
        hβ (blockSucc_step RD Λ i h₂ β)) (by omega) (M β)
      have h0 : capTensor RD Λ i h₂ M β c n = 0 :=
        (ModuleCat.isZero_iff_subsingleton.mp (hY.of_iso (cupIso Q a RD Λ i h₂ M β).symm)).elim _ _
      rw [h0, map_zero]
      unfold oppositeCap
      rw [dite_eq_right (by omega), LinearMap.zero_apply, zero_smul]
      rfl

end Categorification.KLR.CyclotomicAction
