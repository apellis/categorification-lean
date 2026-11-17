/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensorTransport
import Categorification.WeightedKLR.RedStrands.BlackInduction
import Categorification.WeightedKLR.RedStrands.SingleRedGrading
/-!
# Right black-strand induction under one-red insertion

Webster, arXiv:1309.3796v2, §4.4, Theorem 4.20 and §4.6 after Theorem 4.31.
Inserting the red strand on the left commutes with appending a black strand on the right.
-/
noncomputable section
namespace Categorification.Stendhal.SingleRed
open KLR KLRAlgebra KLRAlgebra.AbsentColour
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I : Type*} (i : I) (ν : Multiset I)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)

private theorem blackLoading_old (s : Seq (stendhalWeight 1 ν)) (a : Fin (stendhalWeight 1 νᵢ).card)
    (ha : a.val < (stendhalWeight 1 ν).card) :
    (appendBlackLoading i ν s).lbl a = s.lbl ⟨a, ha⟩ := by
  change (s.append default).1 (Fin.cast _ a) = _
  rw [Seq.append_apply_lt _ _ _ ha]
  rfl

private theorem blackLoading_last (s : Seq (stendhalWeight 1 ν)) (a : Fin (stendhalWeight 1 νᵢ).card)
    (ha : (stendhalWeight 1 ν).card ≤ a.val) :
    (appendBlackLoading i ν s).lbl a = Sum.inl i := by
  change (s.append default).1 (Fin.cast _ a) = _
  rw [Seq.append_apply_ge _ _ _ ha]
  exact Multiset.mem_singleton.mp (Seq.mem _ _)

/-- Appending a black colour and inserting the one red strand give the same boundary loading
in either order (Webster, Theorem 4.20 and the functor following Theorem 4.31). -/
theorem appendBlackLoading_insertWord (s : Seq ν) :
    appendBlackLoading i ν (insertWord ν s) =
      insertWord νᵢ (Seq.cast (add_comm ν {i}) (s.append default)) := by
  apply Subtype.ext
  funext a
  change (appendBlackLoading i ν (insertWord ν s)).lbl a = (insertWord νᵢ _).lbl a
  obtain ⟨n, hn⟩ := a
  cases n with
  | zero =>
    rw [blackLoading_old i ν _ _ (by simp [stendhalWeight]), insertWord_head, insertWord_head]
  | succ n =>
    have hn' : n < (νᵢ).card := by simp [stendhalWeight] at hn ⊢; omega
    change _ = (insertWord νᵢ _).lbl (blackPos νᵢ ⟨n, hn'⟩)
    rw [insertWord_black]
    by_cases hc : n < ν.card
    · rw [blackLoading_old i ν _ _ (by simpa [stendhalWeight, add_comm] using hc)]
      change (insertWord ν s).lbl (blackPos ν ⟨n, hc⟩) = Sum.inl ((s.append default).1 _)
      rw [insertWord_black, Seq.append_apply_lt _ _ _ hc]
      rfl
    · rw [blackLoading_last i ν _ _ (by simpa [stendhalWeight, add_comm] using le_of_not_gt hc)]
      change _ = Sum.inl ((s.append default).1 _)
      rw [Seq.append_apply_ge _ _ _ (Nat.le_of_not_lt hc)]
      exact congrArg Sum.inl (Multiset.mem_singleton.mp (Seq.mem _ _)).symm

variable [DecidableEq I] {k : Type*} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
  (Λ : Fin 1 → I →₀ ℕ)
local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ Λ 0 j

/-- The right-black map and cyclotomic induction agree on every word idempotent under
the one-red algebra isomorphism of Theorem 4.20. -/
theorem appendBlack_cyclotomicEquiv_e (s : Seq ν) :
    appendBlack Q Λ i ν ((cyclotomicEquiv Q Λ ν) (CycKLR.mk k Q aΛ ν (KLRAlgebra.e s))) =
      (cyclotomicEquiv Q Λ νᵢ) (cyclotomicLast Q i aΛ ν (CycKLR.mk k Q aΛ ν (KLRAlgebra.e s))) := by
  change appendBlack Q Λ i ν (cyclotomicProjection Q Λ ν _) = cyclotomicProjection Q Λ νᵢ _
  rw [cyclotomicLast_mk, cL_e, cyclotomicProjection, CycKLR.lift_mk,
    cyclotomicProjection, CycKLR.lift_mk, insertRed_e, insertRed_e]
  exact (appendBlack_mk_e Q Λ i ν _ (ordered ν _)).trans
    (congrArg (fun s => mk Q Λ νᵢ (StendhalAlgebraAllOrders.e s)) (appendBlackLoading_insertWord i ν s))

/-- The idempotent defining intrinsic right-black induction agrees with the image of the
cyclotomic last-colour idempotent under Theorem 4.20. -/
theorem appendBlack_one_eq_cyclotomicEquiv :
    appendBlack Q Λ i ν 1 = (cyclotomicEquiv Q Λ νᵢ) (lastIdem Q i aΛ ν) := by
  let π := CycKLR.mk k Q aΛ ν
  have h : (1 : CycKLR k Q aΛ ν) = ∑ s : Seq ν, π (KLRAlgebra.e s) := by
    rw [← map_sum, KLRAlgebra.sum_e, map_one]
  change _ = (cyclotomicEquiv Q Λ νᵢ) (cyclotomicLast Q i aΛ ν 1)
  rw [← map_one (cyclotomicEquiv Q Λ ν), h, map_sum, map_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun s _ => appendBlack_cyclotomicEquiv_e i ν Q Λ s

private theorem appendBlack_mk (x : StendhalAlgebraAllOrders k Q Λ ν) :
    appendBlack Q Λ i ν (mk Q Λ ν x) = mk Q Λ νᵢ (appendBlackAllOrders Q Λ i ν x).val := rfl

private theorem insertRed_cL_one :
    appendBlack Q Λ i ν 1 = insertRed Q Λ νᵢ (cL Q i ν 1) := by
  have h := appendBlack_one_eq_cyclotomicEquiv i ν Q Λ
  change _ = cyclotomicProjection Q Λ νᵢ (cyclotomicLast Q i aΛ ν 1) at h
  rwa [cyclotomicLast_one, cyclotomicProjection, CycKLR.lift_mk] at h

/-- The one-red algebra equivalence intertwines the two last-strand maps on every
diagram, as required for the induction in Webster §4.6. -/
theorem appendBlack_cyclotomicEquiv (x : CycKLR k Q aΛ ν) :
    appendBlack Q Λ i ν ((cyclotomicEquiv Q Λ ν) x) =
      (cyclotomicEquiv Q Λ νᵢ) (cyclotomicLast Q i aΛ ν x) := by
  obtain ⟨z, rfl⟩ := CycKLR.mk_surjective x
  change appendBlack Q Λ i ν (cyclotomicProjection Q Λ ν _) = cyclotomicProjection Q Λ νᵢ _
  rw [cyclotomicLast_mk, cyclotomicProjection, CycKLR.lift_mk, cyclotomicProjection, CycKLR.lift_mk]
  have h1 := insertRed_cL_one i ν Q Λ
  have hmk : mk Q Λ νᵢ (appendBlackAllOrders Q Λ i ν 1).val = insertRed Q Λ νᵢ (cL Q i ν 1) := by
    rw [← appendBlack_mk, map_one, h1]
  induction z using klr_induction with
  | hr c => simp only [Algebra.algebraMap_eq_smul_one, map_one, map_smul,
      cL_smul, h1]
  | hadd x y hx hy => rw [map_add, map_add, cL_add, map_add, hx, hy]
  | hmul x y hx hy => rw [map_mul, map_mul, cL_mul, map_mul, hx, hy]
  | he s =>
    rw [cL_e, insertRed_e, insertRed_e, appendBlack_mk, appendBlackAllOrders_e,
      appendBlackLoading_insertWord]
  | hx a =>
    rw [insertRed_x, appendBlack_mk, appendBlackAllOrders_x, map_mul, hmk, cL_x, map_mul, insertRed_x]
    rfl
  | hψ j =>
    by_cases hj : j + 1 < ν.card
    · have hju : j + 1 < (νᵢ).card := by simp; omega
      have hjr : j + 1 + 1 < (stendhalWeight 1 ν).card := by simp [stendhalWeight]; omega
      rw [insertRed_ψ Q Λ ν j hj, appendBlack_mk, appendBlackAllOrders_ψ Q Λ i ν (j+1) hjr,
        map_mul, hmk, cL_ψ i ν hj, map_mul, insertRed_ψ Q Λ νᵢ j hju]
    · rw [ψ_eq_zero j (by omega), cL_zero, map_zero, map_zero, map_zero]

section Intertwining
open Categorification.Graded MulOpposite
variable {F : Type*} [Field F] {S : I → I → MvPolynomial (Fin 2) F}
  (G : GradingDatum S) (d : I → ℤ) (hd : ∀ j, G.degX j = 2 * d j)
local notation "H" => stendhalGradingDatum Λ G d hd
local notation "a₀" => fun j => (Polynomial.X : Polynomial F) ^ Λ 0 j
local notation "R" => CycKLR F S a₀ ν
local notation "R'" => CycKLR F S a₀ νᵢ
local notation "T" => TensorProductAlgebra F S Λ ν
local notation "T'" => TensorProductAlgebra F S Λ νᵢ
local notation "φ" => appendBlack S Λ i ν
local notation "ψ" => cyclotomicLast S i a₀ ν
local notation "σ" => cyclotomicEquiv S Λ ν
local notation "τ" => cyclotomicEquiv S Λ νᵢ
local notation "M" => IndCorner S i a₀ ν
local notation "M'" => InductionAlong.Corner (φ : T →ₙ+* T')

private local instance : IsScalarTower F T' M' where
  smul_assoc c a z := Subtype.ext (smul_mul_assoc c a z.val)

private def cornerInsert : M ≃ₗ[F] M' where
  toFun x := ⟨τ x.val, by
    change τ x.val * φ 1 = τ x.val
    rw [appendBlack_one_eq_cyclotomicEquiv, ← map_mul, mem_lIdeal.mp x.2]⟩
  invFun y := ⟨(τ).symm y.val, by
    apply (τ).injective
    rw [map_mul, AlgEquiv.apply_symm_apply, ← appendBlack_one_eq_cyclotomicEquiv]
    exact y.2⟩
  left_inv x := Subtype.ext ((τ).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((τ).apply_symm_apply y.val)
  map_add' x y := Subtype.ext ((τ).map_add x.val y.val)
  map_smul' c x := Subtype.ext (map_smul (τ).toLinearMap c x.val)

private theorem cornerInsert_right (a : R) (m : M) :
    cornerInsert i ν Λ (S := S) (op a • m) = op (σ a) • cornerInsert i ν Λ m := by
  apply Subtype.ext
  change τ (m.val * ψ a) = τ m.val * φ (σ a)
  rw [map_mul, appendBlack_cyclotomicEquiv]

local notation "lowerGr" => CycKLR.grade G (Λ 0) ν
local notation "upperGr" => CycKLR.grade G (Λ 0) νᵢ
local notation "cycCor" => Graded.submodule upperGr (lIdeal (lastIdem S i a₀ ν))
local notation "redCor" => Graded.submodule (tensorProductGrade H νᵢ) (lIdeal (φ 1))
local notation "restr" => GProj.restrict (𝒜 := lowerGr) (𝒜' := tensorProductGrade H ν) σ
  (fun _ _ hx => cyclotomicEquiv_symm_mem_grade Λ G d hd ν hx)

private theorem blackIndK0_of_insert (P : GProj lowerGr) :
    cyclotomicK0Equiv Λ G d hd νᵢ (CycKLR.indK0 G (Λ 0) i ν (K0.of P)) =
      blackIndK0 H i ν (cyclotomicK0Equiv Λ G d hd ν (K0.of P)) := by
  rw [CycKLR.indK0_of, cyclotomicK0Equiv_of Λ G d hd ν P, blackIndK0_of]
  let f := cornerInsert i ν Λ (S := S)
  let g : P.carrier ≃ₗ[F] (restr P).carrier := LinearEquiv.refl _ _
  have hg (a : R) (m : P.carrier) : g (a • m) = σ a • g m := by
    change a • m = (σ).symm (σ a) • m
    rw [AlgEquiv.symm_apply_apply]
  let e := BalancedTensor.changeRingEquiv (B := R') (B' := T') (σ).toRingEquiv f g
    (cornerInsert_right i ν Λ) hg
  apply K0.map_of_semilinear (τ) (fun _ _ hx => cyclotomicEquiv_symm_mem_grade Λ G d hd νᵢ hx)
    (CycKLR.gradedIndProj G (Λ 0) i ν P) (blackIndProj H i ν (restr P)) e.toAddEquiv
  · exact BalancedTensor.changeRingEquiv_smul (σ).toRingEquiv f g (cornerInsert_right i ν Λ) hg (τ).toRingEquiv
      (fun a m => Subtype.ext (map_mul (τ) a m.val))
  · exact fun _ _ hx => BalancedTensor.changeRingEquiv_mem (B := R') (B' := T')
      (ℳ := cycCor) (ℳ' := redCor) (𝒩 := P.grading) (𝒩' := (restr P).grading)
      (σ).toRingEquiv f g (cornerInsert_right i ν Λ) hg
      (fun _ _ h => cyclotomicEquiv_mem_grade Λ G d hd νᵢ h) (fun _ _ h => h) hx
  · exact fun _ _ hx => BalancedTensor.changeRingEquiv_symm_mem (B := R') (B' := T')
      (ℳ := cycCor) (ℳ' := redCor) (𝒩 := P.grading) (𝒩' := (restr P).grading)
      (σ).toRingEquiv f g (cornerInsert_right i ν Λ) hg
      (fun _ _ h => cyclotomicEquiv_symm_mem_grade Λ G d hd νᵢ h) (fun _ _ h => h) hx

/-- In each weight the one-red equivalence intertwines intrinsic black-strand induction
and cyclotomic induction on every graded projective class (Webster, Theorems 4.20 and 4.38). -/
theorem blackIndK0_cyclotomicK0Equiv (x : K0 lowerGr) :
    blackIndK0 H i ν (cyclotomicK0Equiv Λ G d hd ν x) =
      cyclotomicK0Equiv Λ G d hd νᵢ (CycKLR.indK0 G (Λ 0) i ν x) := by
  induction x using K0.induction_on with
  | of P => exact (blackIndK0_of_insert i ν Λ G d hd P).symm
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | neg x hx => simp only [map_neg, hx]

/-- Right black-strand induction is the lowering operator transported along the one-red
equivalence of Theorem 4.20 (Webster, Theorem 4.38, one factor). -/
theorem blackIndK0_eq_indK0 : blackIndK0 H i ν = indK0 Λ G d hd ν i := by
  ext x
  obtain ⟨y, rfl⟩ := (cyclotomicK0Equiv Λ G d hd ν).surjective x
  rw [blackIndK0_cyclotomicK0Equiv, indK0_cyclotomicK0Equiv]

/-- On the regular projective in every weight, the two inductions give the
same upper-block idempotent class. -/
theorem blackIndK0_regular_eq_indK0 :
    blackIndK0 H i ν (K0.of (GProj.regular (tensorProductGrade H ν))) =
      indK0 Λ G d hd ν i (K0.of (GProj.regular (tensorProductGrade H ν))) := by
  rw [blackIndK0_eq_indK0]

/-- The direct sum of Webster's one-red equivalences intertwines the intrinsic
lowering operator with cyclotomic lowering on all weights (Theorem 4.38, one factor). -/
theorem blackLower_totalCyclotomicK0Equiv (x : CycKLR.projectiveK0 G (Λ 0)) :
    blackLower H i (totalCyclotomicK0Equiv Λ G d hd x) =
      totalCyclotomicK0Equiv Λ G d hd (CycKLR.lower G (Λ 0) i x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of β x =>
    change blackLower H i (totalCyclotomicK0Equiv Λ G d hd
      (DirectSum.lof (LaurentPolynomial ℤ) _ _ β x)) =
      totalCyclotomicK0Equiv Λ G d hd (CycKLR.lower G (Λ 0) i (DirectSum.lof (LaurentPolynomial ℤ) _ _ β x))
    rw [CycKLR.lower_lof, totalCyclotomicK0Equiv_lof, totalCyclotomicK0Equiv_lof,
      blackLower_lof, blackIndK0_cyclotomicK0Equiv]

end Intertwining
end Categorification.Stendhal.SingleRed
