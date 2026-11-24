/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoEndpointFlagAction

/-!
# Independence of the outgoing diagram columns at label two

Webster, arXiv:1309.3796v2, §8.2, printed page 80. The three surviving
loadings carry the two opposite square-zero dot coordinates. A test
vector at the exterior cut reads the undotted and first-dot outgoing
columns as the scalar and nilpotent coordinates at the middle and
terminal loadings.
-/

namespace Categorification.Stendhal.LabelTwoEndpointFlag
open KLR KLRAlgebra KLR.PolyRep MvPolynomial TypeA Equiv LabelTwo

noncomputable section
variable {k : Type*} [CommRing k]
local notation "m" => Multiset.card weight
local instance : NeZero m := ⟨by decide⟩
local notation "R" => MvPolynomial (Fin m) k
local notation "A" => labelTwoExteriorRightLoading
local notation "B" => labelTwoMiddleLoading
local notation "C" => labelTwoExteriorLeftLoading

private def supported (s : Seq weight) : Prop := s = A ∨ s = B ∨ s = C

/-- The polynomial module has three ordered, nonviolated flags. -/
def loadingIdeal (s : Seq weight) : Ideal R :=
  by
    classical
    exact if s = A then endpointFlagIdeal 2 3
      else if s = B then endpointFlagIdeal 1 3
      else if s = C then endpointFlagIdeal 1 2
      else ⊤

private theorem loadingIdeal_a : loadingIdeal (k := k) A = endpointFlagIdeal 2 3 := by
  unfold loadingIdeal
  rw [ite_eq_left rfl]

private theorem loadingIdeal_b : loadingIdeal (k := k) B = endpointFlagIdeal 1 3 := by
  unfold loadingIdeal
  rw [ite_eq_right (by decide), ite_eq_left rfl]

private theorem loadingIdeal_c : loadingIdeal (k := k) C = endpointFlagIdeal 1 2 := by
  unfold loadingIdeal
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

private theorem loadingIdeal_eq_top {s : Seq weight} (hs : ¬ supported s) :
    loadingIdeal (k := k) s = ⊤ := by
  grind [supported, loadingIdeal]

theorem loadingIdeal_of_violated {s : Seq weight} (hs : IsViolated s) :
    loadingIdeal (k := k) s = ⊤ :=
  loadingIdeal_eq_top <| by
    rintro (rfl | rfl | rfl)
    · exact (by unfold IsViolated; decide +kernel : ¬ IsViolated A) hs
    · exact (by unfold IsViolated; decide +kernel : ¬ IsViolated B) hs
    · exact (by unfold IsViolated; decide +kernel : ¬ IsViolated C) hs

theorem loadingIdeal_of_unordered {s : Seq weight} (hs : ¬ IsRedOrdered s) :
    loadingIdeal (k := k) s = ⊤ :=
  loadingIdeal_eq_top <| by
    rintro (rfl | rfl | rfl)
    · exact hs (by unfold IsRedOrdered; decide +kernel)
    · exact hs (by unfold IsRedOrdered; decide +kernel)
    · exact hs (by unfold IsRedOrdered; decide +kernel)

private theorem crossComp_known_labels (j : ℕ) (hj : j + 1 < m)
    (s : Seq weight) (p : R) (a b : Unit ⊕ Fin 2)
    (ha : s.lbl ⟨j, by omega⟩ = a) (hb : s.lbl ⟨j + 1, hj⟩ = b) :
    crossComp flagP j hj s p =
      if a = b then ddiff ⟨j, by omega⟩ ⟨j+1,hj⟩ p
      else rename ![(⟨j, by omega⟩ : Fin m), ⟨j+1,hj⟩] (flagP a b) * rename (sadj m j) p := by
  unfold crossComp
  rw [ha,hb]
  split_ifs <;> rfl

private theorem preserves_a (j : Fin 3) (p : R)
    (hp : p ∈ loadingIdeal (sadj m j • A)) :
    crossComp flagP j (by change j.val + 1 < 4; omega : j.val + 1 < m) (sadj m j • A) p ∈
      loadingIdeal A := by
  rw [loadingIdeal_a]
  fin_cases j
  · change crossComp flagP 0 (by decide) (sadj m 0 • A) p ∈ _
    have hd : (sadj m 0 • A).lbl ⟨0, by decide⟩ = .inr 1 := rfl
    have he : (sadj m 0 • A).lbl ⟨1, by decide⟩ = .inr 0 := rfl
    rw [crossComp_known_labels 0 (by decide) (sadj m 0 • A) p _ _ hd he]
    simp [flagP]
    exact zero_mem _
  · change crossComp flagP 1 (by decide) (sadj m 1 • A) p ∈ _
    have hs : sadj m 1 • A = B := by decide
    change p ∈ loadingIdeal (sadj m 1 • A) at hp
    rw [hs, loadingIdeal_b] at hp
    rw [hs]
    have hd : (B).lbl ⟨1, by decide⟩ = .inl () := rfl
    have he : (B).lbl ⟨2, by decide⟩ = .inr 1 := rfl
    rw [crossComp_known_labels 1 (by decide) (B) p _ _ hd he]
    rw [ite_eq_right (by decide), flagP, ite_eq_right (by decide), map_one, one_mul]
    exact rename_mem_endpointFlagIdeal (sadj m 1) 1 3 hp
  · change crossComp flagP 2 (by decide) (sadj m 2 • A) p ∈ _
    have hs : sadj m 2 • A = A := by decide
    change p ∈ loadingIdeal (sadj m 2 • A) at hp
    rw [hs, loadingIdeal_a] at hp
    rw [hs]
    have hd : (A).lbl ⟨2, by decide⟩ = .inl () := rfl
    have he : (A).lbl ⟨3, by decide⟩ = .inl () := rfl
    rw [crossComp_known_labels 2 (by decide) (A) p _ _ hd he]
    rw [ite_eq_left rfl]
    exact ddiff_mem_endpointFlagIdeal (by decide : (2 : Fin m) ≠ 3) hp

private theorem preserves_b (j : Fin 3) (p : R)
    (hp : p ∈ loadingIdeal (sadj m j • B)) :
    crossComp flagP j (by change j.val + 1 < 4; omega : j.val + 1 < m) (sadj m j • B) p ∈
      loadingIdeal B := by
  rw [loadingIdeal_b]
  fin_cases j
  · change crossComp flagP 0 (by decide) (sadj m 0 • B) p ∈ _
    have hd : (sadj m 0 • B).lbl ⟨0, by decide⟩ = .inl () := rfl
    have he : (sadj m 0 • B).lbl ⟨1, by decide⟩ = .inr 0 := rfl
    rw [crossComp_known_labels 0 (by decide) (sadj m 0 • B) p _ _ hd he]
    simp [flagP, map_pow, rename_X, Matrix.cons_val_one]
    change X (1 : Fin m) ^ 2 * rename (sadj m 0) p ∈ endpointFlagIdeal (1 : Fin m) 3
    exact (endpointFlagIdeal (k := k) (1 : Fin m) 3).mul_mem_right (rename (sadj m 0) p)
      (left_sq_mem_endpointFlagIdeal (k := k) (1 : Fin m) 3)
  · change crossComp flagP 1 (by decide) (sadj m 1 • B) p ∈ _
    have hs : sadj m 1 • B = A := by decide
    rw [hs]
    have hd : (A).lbl ⟨1, by decide⟩ = .inr 1 := rfl
    have he : (A).lbl ⟨2, by decide⟩ = .inl () := rfl
    rw [crossComp_known_labels 1 (by decide) (A) p _ _ hd he]
    simp [flagP, map_pow, rename_X, Matrix.cons_val_zero]
    change X (1 : Fin m) ^ 2 * rename (sadj m 1) p ∈ endpointFlagIdeal (1 : Fin m) 3
    exact (endpointFlagIdeal (k := k) (1 : Fin m) 3).mul_mem_right (rename (sadj m 1) p)
      (left_sq_mem_endpointFlagIdeal (k := k) (1 : Fin m) 3)
  · change crossComp flagP 2 (by decide) (sadj m 2 • B) p ∈ _
    have hs : sadj m 2 • B = C := by decide
    change p ∈ loadingIdeal (sadj m 2 • B) at hp
    rw [hs, loadingIdeal_c] at hp
    rw [hs]
    have hd : (C).lbl ⟨2, by decide⟩ = .inl () := rfl
    have he : (C).lbl ⟨3, by decide⟩ = .inr 1 := rfl
    rw [crossComp_known_labels 2 (by decide) (C) p _ _ hd he]
    rw [ite_eq_right (by decide), flagP, ite_eq_right (by decide), map_one, one_mul]
    exact rename_mem_endpointFlagIdeal (sadj m 2) 1 2 hp

private theorem preserves_c (j : Fin 3) (p : R)
    (hp : p ∈ loadingIdeal (sadj m j • C)) :
    crossComp flagP j (by change j.val + 1 < 4; omega : j.val + 1 < m) (sadj m j • C) p ∈
      loadingIdeal C := by
  rw [loadingIdeal_c]
  fin_cases j
  · change crossComp flagP 0 (by decide) (sadj m 0 • C) p ∈ _
    have hd : (sadj m 0 • C).lbl ⟨0, by decide⟩ = .inl () := rfl
    have he : (sadj m 0 • C).lbl ⟨1, by decide⟩ = .inr 0 := rfl
    rw [crossComp_known_labels 0 (by decide) (sadj m 0 • C) p _ _ hd he]
    simp [flagP, map_pow, rename_X, Matrix.cons_val_one]
    change X (1 : Fin m) ^ 2 * rename (sadj m 0) p ∈ endpointFlagIdeal (1 : Fin m) 2
    exact (endpointFlagIdeal (k := k) (1 : Fin m) 2).mul_mem_right (rename (sadj m 0) p)
      (left_sq_mem_endpointFlagIdeal (k := k) (1 : Fin m) 2)
  · change crossComp flagP 1 (by decide) (sadj m 1 • C) p ∈ _
    have hs : sadj m 1 • C = C := by decide
    change p ∈ loadingIdeal (sadj m 1 • C) at hp
    rw [hs, loadingIdeal_c] at hp
    rw [hs]
    have hd : (C).lbl ⟨1, by decide⟩ = .inl () := rfl
    have he : (C).lbl ⟨2, by decide⟩ = .inl () := rfl
    rw [crossComp_known_labels 1 (by decide) (C) p _ _ hd he]
    rw [ite_eq_left rfl]
    exact ddiff_mem_endpointFlagIdeal (by decide : (1 : Fin m) ≠ 2) hp
  · change crossComp flagP 2 (by decide) (sadj m 2 • C) p ∈ _
    have hs : sadj m 2 • C = B := by decide
    rw [hs]
    have hd : (B).lbl ⟨2, by decide⟩ = .inr 1 := rfl
    have he : (B).lbl ⟨3, by decide⟩ = .inl () := rfl
    rw [crossComp_known_labels 2 (by decide) (B) p _ _ hd he]
    simp [flagP, map_pow, rename_X, Matrix.cons_val_zero]
    change X (2 : Fin m) ^ 2 * rename (sadj m 2) p ∈ endpointFlagIdeal (1 : Fin m) 2
    exact (endpointFlagIdeal (k := k) (1 : Fin m) 2).mul_mem_right (rename (sadj m 2) p)
      (right_sq_mem_endpointFlagIdeal (k := k) (1 : Fin m) 2)

theorem loadingIdeal_preserved : PreservesFlags (loadingIdeal (k := k)) := by
  intro s j hj p hp
  let t := sadj m j • s
  let r : Fin 3 := ⟨j, by change j + 1 < 4 at hj; omega⟩
  have hs : sadj m j • t = s := sadj_smul_sadj_smul s j
  change crossComp flagP j hj s p ∈ loadingIdeal t
  by_cases ht : supported t
  · rcases ht with h | h | h
    · rw [← hs, h]
      exact preserves_a r p (by rwa [← h, hs])
    · rw [← hs, h]
      exact preserves_b r p (by rwa [← h, hs])
    · rw [← hs, h]
      exact preserves_c r p (by rwa [← h, hs])
  · rw [loadingIdeal_eq_top ht]
    exact Submodule.mem_top


end
end Categorification.Stendhal.LabelTwoEndpointFlag

namespace Categorification.Stendhal.LabelTwoEndpointFlag
open KLR KLRAlgebra KLR.PolyRep MvPolynomial TypeA Equiv

noncomputable section
variable {k : Type*} [Field k]
variable (Q : Unit → Unit → MvPolynomial (Fin 2) k)
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "ν" => Multiset.replicate 2 ()
local notation "R" => MvPolynomial (Fin (Multiset.card weight)) k
local notation "M" => Pol k weight ⧸ flagRelations (loadingIdeal (k := k))
local notation "ρ" => allOrdersFlagRep Q (loadingIdeal (k := k)) loadingIdeal_preserved
local notation "A" => StendhalAlgebraAllOrders k Q weights ν
local notation "C" => StendhalAlgebra k Q weights ν
local notation "E" => StendhalAlgebraAllOrders.redOrderedIdem k Q weights ν

private theorem allOrdersFlagRep_loading_eq_zero (s : Seq weight)
    (hs : loadingIdeal (k := k) s = ⊤) : ρ (StendhalAlgebraAllOrders.e s) = 0 := by
  rw [StendhalAlgebraAllOrders.e, allOrdersFlagRep_ofKLR]
  exact flagQuotRep_e_eq_zero_of_flag_eq_top Q _ _ s hs

private theorem allOrdersFlagRep_redOrderedIdem : ρ E = 1 := by
  classical
  rw [StendhalAlgebraAllOrders.redOrderedIdem, map_sum, Finset.sum_filter]
  have hsum : (∑ s : Seq weight, ρ (StendhalAlgebraAllOrders.e s)) = 1 := by
    simp only [← map_sum, StendhalAlgebraAllOrders.e, ← map_sum, KLRAlgebra.sum_e, map_one]
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : IsRedOrdered s
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs, allOrdersFlagRep_loading_eq_zero Q s (loadingIdeal_of_unordered hs)]

/-- The positional flag action restricts to the ordered corner. -/
def orderedFlagRep : C →ₐ[k] Module.End k M where
  toFun a := ρ a.val
  map_one' := allOrdersFlagRep_redOrderedIdem Q
  map_zero' := map_zero ρ
  map_mul' a b := map_mul ρ a.val b.val
  map_add' a b := map_add ρ a.val b.val
  commutes' c := by
    change ρ (algebraMap k A c * E) = algebraMap k _ c
    rw [map_mul, allOrdersFlagRep_redOrderedIdem Q, mul_one, AlgHom.commutes]

/-- The ordered positional flag representation descends to the actual
two-red algebra with violated diagrams killed. -/
def tensorFlagRep : TensorProductAlgebra k Q weights ν →ₐ[k] Module.End k M :=
  (StendhalAlgebra.violatedIdeal k Q weights ν).ringCon.liftₐ (orderedFlagRep Q) (by
    apply (TwoSidedIdeal.ringCon_le_iff
      (J := TwoSidedIdeal.ker (orderedFlagRep Q).toRingHom)).mp
    apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨s, hs, hv, rfl⟩
    apply (TwoSidedIdeal.mem_ker _).2
    exact allOrdersFlagRep_loading_eq_zero Q s (loadingIdeal_of_violated hv))

theorem tensorFlagRep_tensorOfKLR
    (a : KLRAlgebra k (stendhalQ Q weights) weight) :
    tensorFlagRep Q (tensorOfKLR Q weights ν a) =
      flagQuotRep Q _ loadingIdeal_preserved a := by
  change ρ ((orderProjection Q weights ν (StendhalAlgebraAllOrders.ofKLR k Q weights ν a)).val)
    = _
  change ρ (StendhalAlgebraAllOrders.ofKLR k Q weights ν a * E) = _
  rw [map_mul, allOrdersFlagRep_redOrderedIdem Q, mul_one, allOrdersFlagRep_ofKLR]

theorem flag_eval_of_tensorOfKLR_eq_zero {a : KLRAlgebra k (stendhalQ Q weights) weight}
    (ha : tensorOfKLR Q weights ν a = 0) (f : Pol k weight) (s : Seq weight) :
    blackEval s (polyRep (flagP_factor Q) a f s) ∈ loadingIdeal (k := k) s := by
  have hh := congrArg (tensorFlagRep Q) ha
  rw [tensorFlagRep_tensorOfKLR, map_zero] at hh
  exact flagQuotRep_eq_zero_eval Q _ _ hh f s

end
end Categorification.Stendhal.LabelTwoEndpointFlag

namespace Categorification.Stendhal.LabelTwoEndpointFlag
open KLR KLRAlgebra KLR.PolyRep MvPolynomial TypeA Equiv LabelTwo

noncomputable section
variable {k : Type} [Field k]
variable (Q : Unit → Unit → MvPolynomial (Fin 2) k)

local notation "m" => Multiset.card weight
local instance : NeZero m := ⟨by decide⟩
local notation "R" => MvPolynomial (Fin m) k
local notation "ν" => Multiset.replicate 2 ()
local notation "P" => polyRep (flagP_factor Q)
local notation "H" => KLRAlgebra k (stendhalQ Q weights) weight
local notation "A" => labelTwoExteriorRightLoading
local notation "B" => labelTwoMiddleLoading
local notation "C₀" => labelTwoExteriorLeftLoading
local notation "X₁" => (x (⟨1, by decide⟩ : Fin m) : H)
local notation "p" => (e C₀ - X₁ * ψ 1 * e C₀ : H)
local notation "input" => Pi.single C₀ (1 : R)
local notation "W" => (ψ 1 * (ψ 2 * e C₀) : H)

private theorem blackCross_at_left_on_one :
    P (ψ 1 * e C₀ : H) input C₀ = 0 := by
  have hs : sadj m 1 • C₀ = C₀ := by decide
  rw [map_mul, Module.End.mul_apply, polyRep_ψ, opΨ_apply flagP 1 (by decide), hs,
    polyRep_e, opE_apply, ite_eq_left rfl, Pi.single_eq_same]
  rw [crossComp_known_labels 1 (by decide) C₀ 1 (.inl ()) (.inl ()) rfl rfl, ite_eq_left rfl]
  exact ddiff_eq_zero_of_rename_eq (by decide) (map_one _)

private theorem complementaryProjection_at_left_on_one :
    P p input C₀ = 1 := by
  have he : P (e C₀ : H) input C₀ = 1 := by
    rw [polyRep_e, opE_apply, ite_eq_left rfl, Pi.single_eq_same]
  rw [map_sub, LinearMap.sub_apply, Pi.sub_apply, he]
  have hh : P (X₁ * ψ 1 * e C₀ : H) input C₀ = 0 := by
    rw [mul_assoc, map_mul, Module.End.mul_apply, polyRep_x, opX_apply,
      blackCross_at_left_on_one Q, mul_zero]
  rw [hh, sub_zero]

private theorem leftDotProjection_at_left_on_one :
    P (X₁ * p : H) input C₀ = X ⟨1, by decide⟩ := by
  rw [map_mul, Module.End.mul_apply, polyRep_x, opX_apply,
    complementaryProjection_at_left_on_one Q, mul_one]

private theorem mixed_cross_at_middle (a : H) :
    P (ψ 2 * a) input B = rename (sadj m 2) (P a input C₀) := by
  have hs : sadj m 2 • B = C₀ := by decide
  rw [map_mul, Module.End.mul_apply, polyRep_ψ, opΨ_apply flagP 2 (by decide), hs]
  rw [crossComp_known_labels 2 (by decide) C₀ _ (.inl ()) (.inr 1) rfl rfl,
    ite_eq_right (by decide), flagP, ite_eq_right (by decide), map_one, one_mul]

private theorem mixed_cross_at_right (a : H) :
    P (ψ 1 * a) input A = rename (sadj m 1) (P a input B) := by
  have hs : sadj m 1 • A = B := by decide
  rw [map_mul, Module.End.mul_apply, polyRep_ψ, opΨ_apply flagP 1 (by decide), hs]
  rw [crossComp_known_labels 1 (by decide) B _ (.inl ()) (.inr 1) rfl rfl,
    ite_eq_right (by decide), flagP, ite_eq_right (by decide), map_one, one_mul]

private theorem middle_columns_eval_one :
    P (ψ 2 * (e C₀ * p) : H) input B = 1 := by
  rw [mixed_cross_at_middle Q, map_mul, Module.End.mul_apply, polyRep_e, opE_apply, ite_eq_left rfl,
    complementaryProjection_at_left_on_one Q, map_one]

private theorem middle_columns_eval_dot :
    P (ψ 2 * (e C₀ * (X₁ * p)) : H) input B = X ⟨1,by decide⟩ := by
  rw [mixed_cross_at_middle Q, map_mul, Module.End.mul_apply, polyRep_e, opE_apply, ite_eq_left rfl,
    leftDotProjection_at_left_on_one Q, rename_X]
  rfl

private theorem terminal_columns_eval_one :
    P (W * p : H) input A = 1 := by
  rw [mul_assoc, mul_assoc, mixed_cross_at_right Q, middle_columns_eval_one Q, map_one]

private theorem terminal_columns_eval_dot :
    P (W * (X₁ * p) : H) input A = X ⟨2, by decide⟩ := by
  rw [mul_assoc, mul_assoc, mixed_cross_at_right Q, middle_columns_eval_dot Q, rename_X]
  rfl

private def readInput (s : Seq weight) : H →ₗ[k] R where
  toFun a := P a input s
  map_add' a b := by simp only [map_add, LinearMap.add_apply, Pi.add_apply]
  map_smul' c a := by simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply]

private theorem detect_input_coefficients
    (s : Seq weight) (i j : Fin m) (hij : i ≠ j)
    (hI : loadingIdeal (k := k) s = endpointFlagIdeal i j)
    (hi : (s.1 i).isLeft)
    (U V : H) (ha : readInput Q s U = 1) (hb : readInput Q s V = X i) {a b : k}
    (hzero : tensorOfKLR Q weights ν (a • U + b • V) = 0) : a = 0 ∧ b = 0 := by
  have hh := flag_eval_of_tensorOfKLR_eq_zero Q hzero input s
  change (blackEval s) (readInput Q s (a • U + b • V)) ∈ loadingIdeal (k := k) s at hh
  rw [hI, (readInput Q s).map_add, (readInput Q s).map_smul,
    (readInput Q s).map_smul, ha,hb] at hh
  have hrows : (a • (1 : R) + b • X i : R) = C a + C b * X i := by
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, mul_one]
  rw [hrows, map_add, map_mul, blackEval_C, blackEval_C, blackEval_X, ite_eq_left hi] at hh
  exact endpointFlag_coefficients_eq_zero hij hh

/-- The two terminal columns of the outgoing crossing are linearly independent
in the actual violated quotient. -/
theorem outgoing_terminal_coefficients_eq_zero {a b : k}
    (h : tensorOfKLR Q weights ν (a • (W * p) + b • (W * (X₁ * p)) : H) = 0) :
    a = 0 ∧ b = 0 :=
  detect_input_coefficients Q A 2 3 (by decide) loadingIdeal_a (by decide)
    _ _ (terminal_columns_eval_one Q) (terminal_columns_eval_dot Q) h

/-- The two middle columns of the outgoing crossing are linearly independent
in the actual violated quotient. -/
theorem outgoing_middle_coefficients_eq_zero {a b : k}
    (h : tensorOfKLR Q weights ν
      (a • ((ψ 2 * e C₀) * p) + b • ((ψ 2 * e C₀) * (X₁ * p)) : H) = 0) :
    a = 0 ∧ b = 0 :=
  detect_input_coefficients Q B 1 3 (by decide) loadingIdeal_b (by decide)
    _ _ (by rw [mul_assoc]; exact middle_columns_eval_one Q)
      (by rw [mul_assoc]; exact middle_columns_eval_dot Q) h

end
end Categorification.Stendhal.LabelTwoEndpointFlag
