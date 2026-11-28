/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoIncomingCoordinates

/-!
# Loading cuts in the label-two middle quotient

Webster, arXiv:1309.3796v2, §8.2, printed page 80. The two surviving
loading idempotents sum to the identity on the middle quotient.
The middle cut is spanned by the unit and its first dot. The terminal
cut is spanned by the two shuffles and their first dots.
-/

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra
noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "μ" => stendhalWeight 2 ν
local notation "A" => TensorProductAlgebra k (parameter k) weights ν
local notation "S" => Standard k
local notation "V" => StandardDotSumQuotient k
local notation "π" => tensorOfKLR (parameter k) weights ν
local notation "Eb" => seqIdem (parameter k) weights loading loading_ordered
local notation "Ea" => seqIdem (parameter k) weights terminalLoading terminalLoading_ordered

private theorem project_loading_if (s : Seq μ) (hs : IsRedOrdered s) :
    π (e s) = seqIdem (parameter k) weights s hs := by
  apply congrArg (TensorProductAlgebra.mk (parameter k) weights ν)
  apply Subtype.ext
  exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs)

private theorem project_unordered (s : Seq μ) (hs : ¬ IsRedOrdered s) :
    π (e s) = 0 := by
  have h : orderProjection (parameter k) weights ν
      (StendhalAlgebraAllOrders.ofKLR k (parameter k) weights ν (e s)) = 0 := by
    apply Subtype.ext
    exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_right hs)
  rw [tensorOfKLR, h]
  exact (TensorProductAlgebra.mk (parameter k) weights ν).map_zero

private theorem middle_standard_support_term (s : Seq μ) (hb : s ≠ loading)
    (ha : s ≠ terminalLoading) (z : S) : π (e s) • z = 0 := by
  by_cases ho : IsRedOrdered s
  · rw [project_loading_if k s ho]
    exact middleStandard_smul_eq_zero_of_other_loading k s ho hb ha z
  · rw [project_unordered k s ho, zero_smul]

/-- The middle standard is the sum of its two surviving loading cuts. -/
theorem labelTwo_middleStandard_split (z : S) : Eb • z + Ea • z = z := by
  classical
  have hne : loading ≠ terminalLoading := by decide +kernel
  have hsum : (∑ s : Seq μ, π (e s)) = (1 : A) := by
    simp only [tensorOfKLR, ← map_sum, sum_e, map_one]
  let survivors : Finset (Seq μ) := {loading, terminalLoading}
  have h : (∑ s ∈ survivors, π (e s) • z) = ∑ s : Seq μ, π (e s) • z := by
    apply Finset.sum_subset (Finset.subset_univ survivors)
    intro s _ hs
    have hb : s ≠ loading := fun h => hs (Finset.mem_insert.mpr (Or.inl h))
    have ha : s ≠ terminalLoading :=
      fun h => hs (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
    exact middle_standard_support_term k s hb ha z
  have hsum_action : (∑ s : Seq μ, π (e s) • z) = z := by
    rw [← Finset.sum_smul, hsum, one_smul]
  exact (by
    simpa only [survivors, Finset.sum_pair hne, project_loading_if k loading loading_ordered,
      project_loading_if k terminalLoading terminalLoading_ordered] using h.trans hsum_action)

/-- The same loading decomposition descends to the actual dot-sum quotient. -/
theorem labelTwo_middleQuotient_split (z : V) : Eb • z + Ea • z = z := by
  obtain ⟨v, rfl⟩ := (LinearMap.range (diagramPlus k)).mkQ_surjective z
  let q := (LinearMap.range (diagramPlus k)).mkQ
  calc
    _ = q (Eb • v) + q (Ea • v) :=
      congrArg₂ (· + ·) (q.map_smul Eb v).symm (q.map_smul Ea v).symm
    _ = q (Eb • v + Ea • v) := (q.map_add _ _).symm
    _ = _ := congrArg q (labelTwo_middleStandard_split k v)

end
end Categorification.Stendhal.LabelTwo

namespace Categorification.Stendhal.LabelTwo
open KLR KLRAlgebra Categorification.Webster.LabelTwo

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "A" => TensorProductAlgebra k (parameter k) weights ν
local notation "g" => leftStandardUnit (parameter k) weights loading loading_ordered
local notation "π" => tensorOfKLR (parameter k) weights ν
local notation "J" => LinearEquiv.symm (terminalToTwoMiddle k)
local notation "W" => fixSub k (Standard k) (seqIdem (parameter k) weights loading loading_ordered)
local notation "V" => fixSub k (StandardDotSumQuotient k)
  (seqIdem (parameter k) weights terminalLoading terminalLoading_ordered)
local notation "M" => Middle k

private abbrev algToEnd := (middlePolynomialEquiv k).symm.trans (middleEndomorphismEquiv k)

/-- The separated first dot is the diagrammatic first black dot. -/
theorem middleToFixed_y₁_val :
    (middleToFixed k (y₁ : M)).val = leftMiddleDot k • g := by
  change (algToEnd k (y₁ : M)) g = _
  have h : (middlePolynomialEquiv k).symm (y₁ : M) = squareQuotientVariable k 0 :=
    (middlePolynomialEquiv k).symm_apply_eq.mpr (middlePolynomialEquiv_variable_zero k).symm
  have hh := (congrArg (fun a : SquareQuotient k => middleEndomorphismEquiv k a) h).trans
    (middleDotQuotientAction_X k 0)
  change algToEnd k (y₁ : M) = dotEnd k 0 at hh
  rw [hh, dotEnd_zero_gen]

/-- A pair of separated elements presented as terminal shuffle diagrams. -/
def terminalVector (a b : M) : V :=
  terminalQuotientMap k (J (middleToFixed k a, middleToFixed k b))

theorem terminalVector_coordinates (a b : M) :
    terminalCutDotSumEquiv k (terminalVector k a b) = (specialize a, specialize b) := by
  have h (c : M) : fixedAugmentation k (middleToFixed k c) = specialize c :=
    congrArg specialize ((middleToFixed k).symm_apply_apply c)
  exact (terminalCutDotSumEquiv_apply k (middleToFixed k a, middleToFixed k b)).trans
    (Prod.ext (h a) (h b))

/-- The two shuffle diagrams use the middle elements as their dot coefficients. -/
theorem terminalVector_val (a b : M) :
    (terminalVector k a b).val = (LinearMap.range (diagramPlus k)).mkQ
      (π (ψw [1]) • (middleToFixed k a).val + π (ψw [2,1]) • (middleToFixed k b).val) := by
  change (LinearMap.range (diagramPlus k)).mkQ (J (middleToFixed k a, middleToFixed k b)).val = _
  rw [terminalToTwoMiddle_symm_apply]

/-- The actual terminal cut is generated by the two shuffles and their first dots. -/
theorem terminal_cut_basis_span (z : V) :
    ∃ a b c d : k,
      z = a • terminalVector k 1 0 + b • terminalVector k y₁ 0 +
          c • terminalVector k 0 1 + d • terminalVector k 0 y₁ := by
  let u := (terminalCutDotSumEquiv k z).1
  let v := (terminalCutDotSumEquiv k z).2
  refine ⟨u.fst,u.snd,v.fst,v.snd,?_⟩
  apply (terminalCutDotSumEquiv k).injective
  simp only [(terminalCutDotSumEquiv k).map_add, (terminalCutDotSumEquiv k).map_smul,
    terminalVector_coordinates, map_one, map_zero, specialize_y₁]
  apply Prod.ext
  · apply TrivSqZeroExt.ext <;> simp [u]
  · apply TrivSqZeroExt.ext <;> simp [v]

end
end Categorification.Stendhal.LabelTwo

namespace Categorification.Stendhal.LabelTwo
open KLR KLRAlgebra Categorification.Webster.LabelTwo

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "A" => TensorProductAlgebra k (parameter k) weights ν
local notation "E" => seqIdem (parameter k) weights loading loading_ordered
local notation "S" => Standard k
local notation "U" => LinearMap.range (diagramPlus k)
local notation "W" => fixSub k S E
local notation "V" => fixSub k (StandardDotSumQuotient k) E
local notation "g" => leftStandardUnit (parameter k) weights loading loading_ordered
local notation "M" => Middle k

private def middleVector : M →ₗ[k] StandardDotSumQuotient k :=
  ((U).mkQ.restrictScalars k).comp ((W).subtype.comp (middleToFixed k).toLinearMap)

private theorem middleVector_apply (a : M) :
    middleVector k a = (U).mkQ (middleToFixed k a).val := rfl

private theorem middleVector_eq_zero {a : M} (ha : specialize a = 0) :
    middleVector k a = 0 := by
  have h : fixedAugmentation k (middleToFixed k a) = 0 :=
    (congrArg specialize ((middleToFixed k).symm_apply_apply a)).trans ha
  have hm : middleToFixed k a ∈ LinearMap.range (fixedPlus k) := by
    rw [← fixedAugmentation_ker]
    exact LinearMap.mem_ker.mpr h
  obtain ⟨v,hv⟩ := hm
  change (Submodule.Quotient.mk (middleToFixed k a).val : StandardDotSumQuotient k) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨v.val, congrArg Subtype.val hv⟩

private theorem middleVector_surjective_of_fixed (u : V) :
    ∃ a : M, middleVector k a = u.val := by
  obtain ⟨v,hv⟩ := (U).mkQ_surjective u.val
  let z : W := ⟨E • v, smul_mem_fixSub (seqIdem_mul_self (parameter k) weights loading loading_ordered) v⟩
  obtain ⟨a, ha⟩ := (middleToFixed k).surjective z
  let q := (U).mkQ
  refine ⟨a, ?_⟩
  exact (congrArg (fun w : W => q w.val) ha).trans <|
    (q.map_smul E v).trans ((congrArg (E • ·) hv).trans u.property)

/-- The middle loading in the actual quotient is spanned by the unit and
the first-dot generator. -/
theorem middle_cut_basis_span (u : V) :
    ∃ a b : k, u.val = a • (U).mkQ g + b • (U).mkQ (leftMiddleDot k • g) := by
  obtain ⟨a,ha⟩ := middleVector_surjective_of_fixed k u
  let d := specialize a
  let a' : M := d.fst • 1 + d.snd • (y₁ : M)
  have hspec : specialize a' = specialize a := by
    let sp : M →ₗ[k] DualNumber k := ((specialize (k := k)).restrictScalars k).toLinearMap
    change sp (d.fst • (1 : M) + d.snd • (y₁ : M)) = d
    have h₀ : sp (1 : M) = 1 := map_one (specialize (k := k))
    have h₁ : sp (y₁ : M) = DualNumber.eps := specialize_y₁
    calc
      _ = sp (d.fst • (1 : M)) + sp (d.snd • (y₁ : M)) := sp.map_add _ _
      _ = d.fst • (1 : DualNumber k) + d.snd • DualNumber.eps :=
        congrArg₂ (· + ·)
          ((sp.map_smul d.fst 1).trans (congrArg (d.fst • ·) h₀))
          ((sp.map_smul d.snd y₁).trans (congrArg (d.snd • ·) h₁))
      _ = _ := by
        apply TrivSqZeroExt.ext <;> simp
  have hv : middleVector k a = middleVector k a' := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply middleVector_eq_zero k
    rw [map_sub, hspec, sub_self]
  refine ⟨d.fst,d.snd,ha.symm.trans (hv.trans ?_)⟩
  change middleVector k (d.fst • (1 : M) + d.snd • (y₁ : M)) = _
  let f := middleVector k
  have hu : f 1 = (U).mkQ g := congrArg (U).mkQ (middleToFixed_one_val k)
  have hd : f y₁ = (U).mkQ (leftMiddleDot k • g) :=
    congrArg (U).mkQ (middleToFixed_y₁_val k)
  exact (f.map_add _ _).trans <|
    congrArg₂ (· + ·)
      ((f.map_smul d.fst 1).trans (congrArg (d.fst • ·) hu))
      ((f.map_smul d.snd y₁).trans (congrArg (d.snd • ·) hd))

end
end Categorification.Stendhal.LabelTwo
