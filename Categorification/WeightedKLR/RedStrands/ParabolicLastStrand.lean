/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicAffineQuotients
import Categorification.WeightedKLR.RedStrands.BlackInduction

/-!
# Red subfamily projections and the last black strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. The quotient `R(μ.map c) → T^{λ ∘ f}_ν` onto the tensor product algebra of a
red subfamily (`redSubfamilyProjection`) commutes with adjoining a straight black strand on the
right: in the KLR algebra this is concatenation with `R(i)`, in the tensor product algebra it is
Webster's map `appendBlack`.

## Main results

* `map_appendBlackLoading` : relabelling the red strands commutes with appending a black label;
* `relabel_appendBlack` : the corresponding statement for KLR diagrams;
* `appendBlackStendhal_orderProjection` : appending a black strand commutes with the
  projection onto red-ordered idempotents;
* `redSubfamilyProjection_appendBlack` : the compatibility of the two quotients.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Concat

variable {J k : Type*} [DecidableEq J] [CommRing k] {R : J → J → MvPolynomial (Fin 2) k}
  {γ : Multiset J} (j : J)

local notation "Sj" => (Singleton.singleton j : Multiset J)

theorem concat_e_tmul_one_singleton (t : Seq γ) :
    concat R γ Sj (e t ⊗ₜ 1) = e (t.append default) := by
  rw [concat_e_tmul_one, Fintype.sum_subsingleton _ default]

theorem concat_mul_tmul_one (u v : KLRAlgebra k R γ) :
    concat R γ Sj ((u * v) ⊗ₜ 1) = concat R γ Sj (u ⊗ₜ 1) * concat R γ Sj (v ⊗ₜ 1) := by
  rw [← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem concat_ψ_tmul_one (a : ℕ) (ha : a + 1 < Multiset.card γ) :
    concat R γ Sj (ψ a ⊗ₜ 1) = ψ a * oneConcat R γ Sj := by
  have h := concat_ψw_tmul_ψw (Q := R) (ν := γ) (ν' := Sj) (α := [a]) (α' := [])
    (fun b hb => by simp only [List.mem_singleton] at hb; omega) (TypeA.validWord_nil _)
  simpa [ψw_cons, ψw_nil, TypeA.shiftWord] using h

end Concat

variable {I k : Type*} [DecidableEq I] [CommRing k] {m n : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin n → I →₀ ℕ)
    (f : Fin m → Fin n) (hf : Function.Injective f) (i : I) (ν : Multiset I)

local notation "c" => Sum.map (id : I → I) f
local notation "μ" => stendhalWeight m ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "S" => stendhalQ Q Λ
local notation "S₀" => stendhalQ Q (Λ ∘ f)
local notation "σ₀" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin m))
local notation "σ" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin n))

omit [DecidableEq I] in
/-- Relabelling the red strands commutes with adjoining the black weight `i`. -/
theorem map_stendhalWeight_addBlack : (μ).map c + σ = (stendhalWeight m νᵢ).map c := by
  rw [← stendhalWeight_addBlack i ν, Multiset.map_add, Multiset.map_singleton]
  rfl

omit [DecidableEq I] in
theorem card_stendhalWeight_addBlack :
    Multiset.card (stendhalWeight m νᵢ) = Multiset.card μ + 1 := by
  rw [← stendhalWeight_addBlack i ν, Multiset.card_add, Multiset.card_singleton]

omit [DecidableEq I] in
/-- Relabelling the red strands commutes with appending the black label `i` on the right. -/
theorem map_appendBlackLoading (s : Seq μ) :
    Seq.map c (appendBlackLoading i ν s) =
      Seq.cast (map_stendhalWeight_addBlack f i ν) ((Seq.map c s).append default) := by
  apply Subtype.ext
  funext a
  have hlt := a.2
  simp only [Multiset.card_map, card_stendhalWeight_addBlack i ν] at hlt
  by_cases ha : a.val < Multiset.card μ
  · rw [Seq.cast_apply, Seq.append_apply_lt _ _ _ (lt_of_lt_of_eq ha (Multiset.card_map _ _).symm)]
    change c ((appendBlackLoading i ν s).lbl _) = c (s.lbl _)
    rw [appendBlackLoading_lbl_of_lt i ν s _ ha]
    rfl
  · rw [Seq.cast_apply, Seq.append_apply_ge _ _ _
      (le_of_eq_of_le (Multiset.card_map _ _) (Nat.le_of_not_lt ha))]
    change c ((appendBlackLoading i ν s).lbl _) = _
    rw [appendBlackLoading_lbl_of_eq i ν s _ (by change a.val = _; omega)]
    rfl

omit [DecidableEq I] in
/-- The converse of `appendBlackLoading_ordered`. -/
theorem isRedOrdered_of_appendBlackLoading (s : Seq μ)
    (hs : IsRedOrdered (appendBlackLoading i ν s)) : IsRedOrdered s := by
  intro a b r r' hab ha hb
  have hc : ∀ y : Fin (Multiset.card μ), y.val < Multiset.card (stendhalWeight m νᵢ) :=
    fun y => by rw [card_stendhalWeight_addBlack i ν]; omega
  refine hs ⟨a.val, hc a⟩ ⟨b.val, hc b⟩ r r' hab ?_ ?_
  · rw [appendBlackLoading_lbl_of_lt i ν s _ a.2]; exact ha
  · rw [appendBlackLoading_lbl_of_lt i ν s _ b.2]; exact hb

omit [DecidableEq I] in
theorem isRedOrdered_appendBlackLoading_iff (s : Seq μ) :
    IsRedOrdered (appendBlackLoading i ν s) ↔ IsRedOrdered s :=
  ⟨isRedOrdered_of_appendBlackLoading i ν s, appendBlackLoading_ordered i ν s⟩

local notation "ρ" => redSubfamilyRelabel Q Λ f hf ν
local notation "ρᵢ" => redSubfamilyRelabel Q Λ f hf νᵢ
local notation "hB" => stendhalWeight_addBlack (ℓ := m) i ν
local notation "hA" => map_stendhalWeight_addBlack f i ν

private theorem relabel_appendBlack_e (s : Seq μ) :
    relabelEquiv ρᵢ (castKLR S₀ hB (concat S₀ μ σ₀ (e s ⊗ₜ 1))) =
      castKLR S hA (concat S ((μ).map c) σ (relabelEquiv ρ (e s) ⊗ₜ 1)) := by
  rw [concat_e_tmul_one_singleton, castKLR_e, relabelEquiv_apply, relabelHom_e,
    relabelEquiv_apply, relabelHom_e, concat_e_tmul_one_singleton, castKLR_e]
  exact congrArg e (map_appendBlackLoading f i ν s)

private theorem relabel_appendBlack_one :
    relabelEquiv ρᵢ (castKLR S₀ hB (oneConcat S₀ μ σ₀)) =
      castKLR S hA (oneConcat S ((μ).map c) σ) := by
  rw [← concat_one, ← concat_one, Algebra.TensorProduct.one_def, Algebra.TensorProduct.one_def,
    ← sum_e (ν := μ), TensorProduct.sum_tmul, map_sum, map_sum, map_sum,
    ← map_one (relabelEquiv ρ),
    ← sum_e (ν := μ), map_sum, TensorProduct.sum_tmul, map_sum, map_sum]
  exact Finset.sum_congr rfl fun s _ => relabel_appendBlack_e Q Λ f hf i ν s

/-- Relabelling the red strands commutes with adjoining a black strand on the right. -/
theorem relabel_appendBlack (z : KLRAlgebra k S₀ μ) :
    relabelEquiv ρᵢ (castKLR S₀ hB (concat S₀ μ σ₀ (z ⊗ₜ 1))) =
      castKLR S hA (concat S ((μ).map c) σ (relabelEquiv ρ z ⊗ₜ 1)) := by
  induction z using KLRAlgebra.klr_induction with
  | hadd u v hu hv => simp only [TensorProduct.add_tmul, map_add, hu, hv]
  | hmul u v hu hv => simp only [concat_mul_tmul_one, map_mul, hu, hv]
  | hr r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, ← TensorProduct.smul_tmul',
      ← TensorProduct.smul_tmul',
      map_smul, map_smul, map_smul, map_smul, map_smul, map_one]
    congr 1
    have h := relabel_appendBlack_one Q Λ f hf i ν
    rwa [← concat_one, ← concat_one] at h
  | he s => exact relabel_appendBlack_e Q Λ f hf i ν s
  | hx a =>
    rw [concat_x_tmul_one, map_mul, map_mul, relabel_appendBlack_one]
    simp only [relabelEquiv_apply, relabelHom_x, castKLR_x, concat_x_tmul_one, map_mul]
    rfl
  | hψ a =>
    by_cases ha : a + 1 < Multiset.card μ
    · rw [concat_ψ_tmul_one _ _ ha, map_mul, map_mul, relabel_appendBlack_one]
      simp only [relabelEquiv_apply, relabelHom_ψ, castKLR_ψ, map_mul,
        concat_ψ_tmul_one _ _ (show a + 1 < Multiset.card ((μ).map c) by simpa using ha)]
    · rw [ψ_eq_zero a (by omega), map_zero, TensorProduct.zero_tmul, map_zero, map_zero, map_zero,
        TensorProduct.zero_tmul, map_zero, map_zero]

local notation "τ₀" => orderProjection Q (Λ ∘ f) ν
local notation "τᵢ" => orderProjection Q (Λ ∘ f) νᵢ

/-- Appending a black strand commutes with cutting by the red-ordered idempotents. -/
theorem appendBlackStendhal_orderProjection (y : StendhalAlgebraAllOrders k Q (Λ ∘ f) ν) :
    appendBlackStendhal Q (Λ ∘ f) i ν (τ₀ y) =
      τᵢ (appendBlackAllOrders Q (Λ ∘ f) i ν y).val := by
  classical
  apply Subtype.ext
  rw [appendBlackStendhal_val]
  change (appendBlackAllOrders Q (Λ ∘ f) i ν
      (y * StendhalAlgebraAllOrders.redOrderedIdem k Q (Λ ∘ f) ν)).val =
    (appendBlackAllOrders Q (Λ ∘ f) i ν y).val *
      StendhalAlgebraAllOrders.redOrderedIdem k Q (Λ ∘ f) νᵢ
  have hE : (appendBlackAllOrders Q (Λ ∘ f) i ν
      (StendhalAlgebraAllOrders.redOrderedIdem k Q (Λ ∘ f) ν)).val =
      (appendBlackAllOrders Q (Λ ∘ f) i ν 1).val *
        StendhalAlgebraAllOrders.redOrderedIdem k Q (Λ ∘ f) νᵢ := by
    have h1 : (1 : StendhalAlgebraAllOrders k Q (Λ ∘ f) ν) = ∑ s : Seq μ,
        StendhalAlgebraAllOrders.e s := by
      rw [← map_one (StendhalAlgebraAllOrders.ofKLR k Q (Λ ∘ f) ν), ← sum_e, map_sum]
      rfl
    rw [h1, StendhalAlgebraAllOrders.redOrderedIdem, map_sum, map_sum, KLR.Corner.val_sum,
      KLR.Corner.val_sum, Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [appendBlackAllOrders_e, StendhalAlgebraAllOrders.e_mul_redOrderedIdem]
    exact if_congr (isRedOrdered_appendBlackLoading_iff i ν s).symm rfl rfl
  rw [map_mul, KLR.Corner.val_mul, hE, ← mul_assoc, map_one, KLR.Corner.val_one,
    KLR.Corner.val_mul_E]

local notation "P" => redSubfamilyProjection Q Λ f hf ν
local notation "Pᵢ" => redSubfamilyProjection Q Λ f hf νᵢ

/-- **The red subfamily projection commutes with adjoining a black strand**: concatenating
with a straight strand coloured `i` and projecting is the same as projecting and applying
Webster's map `ν_i` (arXiv:1309.3796v3, proof of Proposition 5.5). -/
theorem redSubfamilyProjection_appendBlack (w : KLRAlgebra k S ((μ).map c)) :
    Pᵢ (castKLR S hA (concat S ((μ).map c) σ (w ⊗ₜ 1))) =
      appendBlack Q (Λ ∘ f) i ν (P w) := by
  obtain ⟨z, rfl⟩ := (relabelEquiv ρ).surjective w
  rw [← relabel_appendBlack]
  simp only [redSubfamilyProjection, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]
  rw [appendBlack_mk, appendBlackStendhal_orderProjection, appendBlackAllOrders_ofKLR_val]

end Categorification.Stendhal
