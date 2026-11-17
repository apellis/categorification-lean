/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedLayerSupport

/-!
# Support on a last-red layer

For the filtration in Webster, arXiv:1309.3796v2, proof of Lemma 4.37,
a nonzero representation has a surviving loading with maximal last-red
position. The quotient by the smaller suffixes still acts on the entire
representation.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ+1) → I →₀ ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight (ℓ+1) ν
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "E" => fun (s : Seq μ) (hs : IsRedOrdered s) =>
  TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs)

omit [DecidableEq I] in
private theorem exists_lastRedPosition (s : Seq μ) :
    ∃ p, s.lbl p = .inr (Fin.last ℓ) := by
  have hm : Sum.inr (Fin.last ℓ) ∈ μ := Multiset.mem_add.2 (Or.inr
    (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _)))
  rw [← s.2, Multiset.mem_map] at hm
  obtain ⟨p, _, hp⟩ := hm
  exact ⟨p, hp⟩

/-- For any nonzero representation there is an ordered loading surviving at
the maximal last-red position. The whole smaller-suffix ideal dies there. -/
theorem exists_supported_lastRedLayer {B : Type*} [Ring B] [Nontrivial B] (ρ : T →+* B) :
    ∃ (p : Fin (Multiset.card μ)) (s : Seq μ) (hs : IsRedOrdered s),
      s.lbl p = .inr (Fin.last ℓ) ∧ ρ (E s hs) ≠ 0 ∧
        smallerSuffixIdeal Q Λ p ≤ TwoSidedIdeal.ker ρ := by
  classical
  let S := {s : Seq μ // IsRedOrdered s}
  have hsum : (∑ s : S, StendhalAlgebra.e s.1 s.2 : StendhalAlgebra k Q Λ ν) = 1 := by
    apply Subtype.ext
    rw [KLR.Corner.val_sum, KLR.Corner.val_one]
    change (∑ s : S, StendhalAlgebraAllOrders.e s.1) = StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν
    exact (Finset.sum_subtype _ (fun s => by simp) _).symm
  have hne : ∃ s : S, ρ (E s.1 s.2) ≠ 0 := by
    by_contra! hall
    apply one_ne_zero (α := B)
    rw [← map_one ρ, ← map_one (TensorProductAlgebra.mk Q Λ ν), ← hsum, map_sum, map_sum]
    exact Finset.sum_eq_zero fun s _ => hall s
  let positions := Finset.univ.filter fun p : Fin (Multiset.card μ) => ∃ s : S,
    s.1.lbl p = .inr (Fin.last ℓ) ∧ ρ (E s.1 s.2) ≠ 0
  obtain ⟨s, hs⟩ := hne
  obtain ⟨a, ha⟩ := exists_lastRedPosition s.1
  have hn : positions.Nonempty := ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, s, ha, hs⟩⟩
  let p := positions.max' hn
  obtain ⟨t, ht, hv⟩ := (Finset.mem_filter.1 (positions.max'_mem hn)).2
  refine ⟨p, t.1, t.2, ht, hv, TwoSidedIdeal.span_le.mpr ?_⟩
  rintro x ⟨u, hu, b, hb, hpos, rfl⟩
  apply (TwoSidedIdeal.mem_ker ρ).mpr
  by_contra hu'
  have hb' : b ∈ positions := Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨u, hu⟩, hpos, hu'⟩
  exact (not_lt_of_ge (positions.le_max' b hb')) hb

/-- A nonzero representation factors through a last-red quotient in which at
least one boundary with that last-red position still acts nontrivially. -/
theorem exists_supported_lastRedRepresentation {B : Type*} [Ring B] [Nontrivial B]
    [Algebra k B] (ρ : T →ₐ[k] B) :
    ∃ (p : Fin (Multiset.card μ)) (s : Seq μ) (hs : IsRedOrdered s)
      (σ : (smallerSuffixIdeal Q Λ p).ringCon.Quotient →ₐ[k] B),
      s.lbl p = .inr (Fin.last ℓ) ∧ ρ (E s hs) ≠ 0 ∧
        σ.comp ((smallerSuffixIdeal Q Λ p).ringCon.mkₐ k) = ρ := by
  obtain ⟨p, s, hs, hp, hne, hker⟩ := exists_supported_lastRedLayer ρ.toRingHom
  let J := smallerSuffixIdeal Q Λ p
  have hJ : J.ringCon ≤ RingCon.ker ρ.toRingHom := by
    intro a b hab
    change ρ a = ρ b
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (TwoSidedIdeal.mem_ker _).mp (hker ((TwoSidedIdeal.rel_iff _ _ _).mp hab))
  exact ⟨p, s, hs, J.ringCon.liftₐ ρ hJ, hp, hne, rfl⟩

/-- Each nonzero representation is detected by a corner indexed by a split of
the black content into an earlier red block and a last cyclotomic block. -/
theorem exists_detecting_lastRedCorner {B : Type*} [Ring B] [Nontrivial B] [Algebra k B]
    (ρ : T →ₐ[k] B) :
    ∃ (p : Fin (Multiset.card μ)) (θ β : Multiset I)
      (h : stendhalWeight (ℓ+1) θ + β.map Sum.inl = μ)
      (σ : (smallerSuffixIdeal Q Λ p).ringCon.Quotient →ₐ[k] B),
      θ + β = ν ∧ (stendhalWeight (ℓ+1) θ).card = p.val + 1 ∧
      σ.comp ((smallerSuffixIdeal Q Λ p).ringCon.mkₐ k) = ρ ∧ σ (lastRedLayerIdem Q Λ p h) ≠ 0 := by
  obtain ⟨p, s, hs, σ, hp, hn, hσ⟩ := exists_supported_lastRedRepresentation ρ
  obtain ⟨θ, β, h, hν, ha, he⟩ := exists_lastRedLayerIdem_mul_boundary Q Λ s hs p hp
  refine ⟨p, θ, β, h, σ, hν, ha, hσ, ?_⟩
  intro hz
  apply hn
  rw [← hσ]
  change σ ((smallerSuffixIdeal Q Λ p).ringCon.mk' (E s hs)) = 0
  rw [← he, map_mul, hz, zero_mul]

end Categorification.Stendhal
