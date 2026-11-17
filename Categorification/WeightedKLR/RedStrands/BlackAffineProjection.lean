/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackInduction
import Categorification.WeightedKLR.RedStrands.TensorProjection
import Categorification.WeightedKLR.RedStrands.AffineCoverGrading

/-!
# Appending black strands to the affine cover

Webster, arXiv:1309.3796v2, §4.6 after Theorem 4.31 and §4.7, Lemma 4.37.
The projection from the affine KLR cover to the ordered violating quotient
commutes with adjoining a black strand on the right.
-/
noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I k : Type*} {ℓ : ℕ} [DecidableEq I] [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)
local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "μ'" => stendhalWeight ℓ νᵢ
local notation "σ" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin ℓ))
local notation "S" => affineCoverQ Q Λ
local notation "A" => StendhalAlgebraAllOrders k Q Λ ν
local notation "B" => appendBlackAllOrders Q Λ i ν
local notation "E" => StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
local notation "E'" => StendhalAlgebraAllOrders.redOrderedIdem k Q Λ νᵢ
local notation "ε" => StendhalAlgebraAllOrders.e
local notation "π" => affineTensorProjection (Q := Q) Λ ν
local notation "π'" => affineTensorProjection (Q := Q) Λ νᵢ

omit [DecidableEq I] in
theorem stendhalWeight_black_cons : σ + μ = μ' := by simp [stendhalWeight]

omit [DecidableEq I] in
theorem appendBlackLoading_ordered_iff (s : Seq μ) :
    IsRedOrdered (appendBlackLoading i ν s) ↔ IsRedOrdered s := by
  refine ⟨fun h a b r r' hab ha hb => ?_, appendBlackLoading_ordered i ν s⟩
  let pos (a : Fin (μ).card) : Fin (μ').card :=
    ⟨a.val, by have H := a.isLt; simp [stendhalWeight] at H ⊢; omega⟩
  have lab (a : Fin (μ).card) : (appendBlackLoading i ν s).lbl (pos a) = s.lbl a := by
    change (s.append default).1 (Fin.cast _ (pos a)) = _
    rw [Seq.append_apply_lt _ _ _ a.isLt]; rfl
  exact h (pos a) (pos b) r r' hab ((lab a).trans ha) ((lab b).trans hb)

private theorem append_orderedIdem :
    (B 1).val * E' = (B E).val := by
  classical
  have hOne : (1 : A) = ∑ s : Seq μ, ε s := by simp [StendhalAlgebraAllOrders.e, ← map_sum, sum_e]
  rw [hOne, show E = ∑ s : Seq μ with IsRedOrdered s, ε s from rfl, map_sum, KLR.Corner.val_sum,
    Finset.sum_mul, map_sum, KLR.Corner.val_sum]
  simp only [appendBlackAllOrders_e, StendhalAlgebraAllOrders.e_mul_redOrderedIdem,
    appendBlackLoading_ordered_iff, Finset.sum_filter]

private theorem append_orderProjection (x : A) :
    appendBlack Q Λ i ν (TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν x)) =
      TensorProductAlgebra.mk Q Λ νᵢ (orderProjection Q Λ νᵢ (B x).val) := by
  apply congrArg (TensorProductAlgebra.mk Q Λ νᵢ)
  apply Subtype.ext
  change (B (x * E)).val = (B x).val * E'
  have h : (B x).val * (B 1).val = (B x).val := by rw [map_one, KLR.Corner.val_one, KLR.Corner.val_mul_E]
  rw [map_mul, KLR.Corner.val_mul, ← append_orderedIdem Λ i ν, ← mul_assoc, h]

local notation "hwt" => stendhalWeight_black_cons (ℓ := ℓ) i ν
local notation "old" => affineCover Q Λ ν
local notation "new" => affineCover Q Λ νᵢ

omit [DecidableEq I] in
private theorem append_loading_cast (s : Seq μ) :
    Seq.cast hwt (Seq.cast (add_comm μ σ) (s.append default)) = appendBlackLoading i ν s := by
  apply Subtype.ext
  funext a
  rfl

private theorem append_cover_e (s : Seq μ) :
    (B (old (KLRAlgebra.e s))).val = new (castKLR S hwt (cL S (Sum.inl i) μ (KLRAlgebra.e s))) := by
  rw [affineCover_e, appendBlackAllOrders_e, cL_e, castKLR_e, affineCover_e, append_loading_cast]

private theorem append_cover_one :
    (B 1).val = new (castKLR S hwt (cL S (Sum.inl i) μ 1)) := by
  rw [cL_one, map_sum, map_sum, ← map_one old, ← sum_e (k := k) (Q := S) (ν := μ), map_sum, map_sum, KLR.Corner.val_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← cL_e]
  exact append_cover_e Λ i ν s

private theorem append_cover (x : KLRAlgebra k S μ) :
    (B (old x)).val = new (castKLR S hwt (cL S (Sum.inl i) μ x)) := by
  have one := append_cover_one (Q := Q) Λ i ν
  induction x using klr_induction with
  | hr c =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one, appendBlackAllOrders_smul,
      cL_smul, map_smul, map_smul, one]
  | hadd x y hx hy => rw [map_add, map_add, KLR.Corner.val_add, cL_add, map_add, map_add, hx, hy]
  | hmul x y hx hy => rw [map_mul, map_mul, KLR.Corner.val_mul, cL_mul, map_mul, map_mul, hx, hy]
  | he s => exact append_cover_e Λ i ν s
  | hx a =>
    rw [affineCover_x, appendBlackAllOrders_x, cL_x, map_mul, map_mul, castKLR_x, affineCover_x, one]
    rfl
  | hψ n =>
    by_cases hn : n + 1 < (μ).card
    · rw [affineCover_ψ, appendBlackAllOrders_ψ Q Λ i ν _ hn, cL_ψ _ _ hn, map_mul, map_mul,
        castKLR_ψ, affineCover_ψ, one]
    · rw [ψ_eq_zero n (by omega), cL_zero, map_zero, map_zero, KLR.Corner.val_zero, map_zero, map_zero]

/-- The ordered violating quotient intertwines the affine last-black-strand map
with intrinsic Stendhal black induction (Webster, §4.6 after Theorem 4.31). -/
theorem appendBlack_affineTensorProjection (x : KLRAlgebra k S μ) :
    appendBlack Q Λ i ν (π x) = π' (castKLR S hwt (cL S (Sum.inl i) μ x)) := by
  change appendBlack Q Λ i ν (TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν (old x))) = _
  rw [append_orderProjection, append_cover]
  rfl

end Categorification.Stendhal
