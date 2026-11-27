/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleDetection

/-!
# Independent terminal shuffle columns

The two terminal shuffles from the separated label-two middle loading
retain independent copies of the parabolic factor module when restricted
to red-ordered loadings.
-/


noncomputable section
namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra TypeA
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "singleBlack" => ({()} : Multiset Unit)
local notation "α" => Multiset.map (addRedColor 1) (stendhalWeight 1 singleBlack)
local notation "lc" => Sum.map (id : Unit → Unit) (fun _ : Fin 1 => Fin.last 1)
local notation "δ" => Multiset.map lc (stendhalWeight 1 singleBlack)
local notation "N" => Multiset.card (α + δ)
local notation "Sh" => TypeA.Shuffle (Seq.card_add' α δ)

private def termU : Sh := ⟨(wordProd N [1])⁻¹, by unfold IsShuffle StrictMono; decide +kernel⟩
private def termV : Sh := ⟨(wordProd N [2, 1])⁻¹, by unfold IsShuffle StrictMono; decide +kernel⟩

private theorem terms_ne : termU ≠ termV := by decide +kernel


private def termWord (w : Sh) : List ℕ :=
  if w = termU then [1] else if w = termV then [1, 2] else shufWord w

private theorem termWord_spec (w : Sh) :
    IsReduced N (termWord w) ∧ wordProd N (termWord w) = w.val := by
  unfold termWord
  split_ifs with hu hv
  · subst w
    refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
    · intro j hj
      simp only [List.mem_singleton] at hj
      subst j
      decide
    · rw [length_eq_invCount]
      decide +kernel
  · subst w
    refine ⟨⟨?_, ?_⟩, by decide +kernel⟩
    · intro j hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl <;> decide
    · rw [length_eq_invCount]
      decide +kernel
  · exact shufWord_spec w


variable (k : Type) [Field k]

local notation "P" => stendhalQ (parameter k) weights
local notation "D" => parabolicFactorAlgebra (parameter k) weights singleBlack singleBlack
local notation "D₀" => ParabolicInput (parameter k) weights singleBlack singleBlack D
local notation "V" => ParabolicShuffle (parameter k) weights singleBlack singleBlack D
local notation "ρ" => parabolicShuffleAction (parameter k) weights singleBlack singleBlack D
local notation "F" => parabolicOrderedLoadings (ℓ := 1) singleBlack singleBlack
local notation "s₀" => Seq.cast (Eq.symm (parabolicInputWeights_add (ℓ := 1) singleBlack singleBlack)) terminalLoading
local notation "projV" => Submodule.mkQ (excludedSpace ρ F)

private theorem parameterSymm' : KLRSymm (parameter k) :=
  fun a b h => (h (Subsingleton.elim a b)).elim

private abbrev termColumn (w : Sh) (x : D₀) : V :=
  BalancedTensor.tmul (hatWRevSubOf (Q := P) termWord w) x

private theorem termColumn_fixed (w : Sh) (hw : w = termU ∨ w = termV) (x : D₀) :
    ρ (e s₀) (termColumn k w x) = termColumn k w x := by
  change (e s₀ : KLRAlgebra k P (α + δ)) • termColumn k w x = termColumn k w x
  rw [e_smul_tmul_hatWRevSubOf termWord termWord_spec]
  have h : w.1 • s₀ =
      (Seq.map (addRedColor 1) (SingleRed.insertWord singleBlack (default : Seq singleBlack))).append
        (Seq.map lc (SingleRed.insertWord singleBlack (default : Seq singleBlack))) := by
    rcases hw with rfl | rfl <;> decide +kernel
  rw [h, concatIdem_append]
  congr 1
  change parabolicInputMap (parameter k) weights singleBlack singleBlack _ • (x : D) = x
  have hT : parabolicInputMap (parameter k) weights singleBlack singleBlack
      (e (Seq.map (addRedColor 1) (SingleRed.insertWord singleBlack (default : Seq singleBlack))) ⊗ₜ[k]
        e (Seq.map lc (SingleRed.insertWord singleBlack (default : Seq singleBlack)))) = (1 : D) := by
    rw [parabolicInputMap, Algebra.TensorProduct.map_tmul,
      redSubfamilyProjection_e (parameter k) weights Fin.castSucc (Fin.castSucc_injective 1) singleBlack _
        (SingleRed.ordered singleBlack _),
      parabolicLastCyclotomic_e (parameter k) weights singleBlack (default : Seq singleBlack),
      e_single, map_one]
    have h₁ := oneBlack_extremal_loadingIdem_eq_one (parameter k)
      (weights ∘ (Fin.castSucc : Fin 1 → Fin 2)) ()
    have h₂ : TensorProductAlgebra.mk (parameter k) (weights ∘ (Fin.castSucc : Fin 1 → Fin 2))
        singleBlack (StendhalAlgebra.e (SingleRed.insertWord singleBlack (default : Seq singleBlack))
          (SingleRed.ordered singleBlack _)) = 1 := by
      rw [← h₁]
      apply congrArg (TensorProductAlgebra.mk (parameter k) (weights ∘ (Fin.castSucc : Fin 1 → Fin 2))
        singleBlack)
      apply Subtype.ext
      rfl
    rw [h₂, ← Algebra.TensorProduct.one_def]
  rw [hT, one_smul]

private theorem termPair_ordered (x y : D₀) :
    ρ (eSum P F) (termColumn k termU x + termColumn k termV y) =
      termColumn k termU x + termColumn k termV y := by
  classical
  have hs : s₀ ∈ F := by
    unfold parabolicOrderedLoadings
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold IsRedOrdered
    decide +kernel
  have h : ρ (e s₀) (termColumn k termU x + termColumn k termV y) =
      termColumn k termU x + termColumn k termV y := by
    rw [map_add, termColumn_fixed k _ (Or.inl rfl), termColumn_fixed k _ (Or.inr rfl)]
  calc
    _ = ρ (eSum P F) (ρ (e s₀) _) := congrArg _ h.symm
    _ = _ := by rw [← Module.End.mul_apply, ← map_mul, eSum_mul_e, ite_eq_left hs, h]

private theorem termPair_injective' : Function.Injective
    (fun x : D₀ × D₀ => projV (termColumn k termU x.1 + termColumn k termV x.2)) := by
  intro x y h
  have ha := orderedShuffle_mkQ_injOn ρ F (termPair_ordered k x.1 x.2)
    (termPair_ordered k y.1 y.2) h
  have hb := congrArg (indDecompOf termWord
    (stendhalQ_swap_symm (parameter k) weights (parameterSymm' k)) termWord_spec D₀) ha
  simp only [map_add, termColumn, indDecompOf_tmul_hatWRevSubOf] at hb
  apply Prod.ext
  · have hU := congrFun hb termU
    simpa [Pi.single_eq_same, Pi.single_eq_of_ne terms_ne] using hU
  · have hV := congrFun hb termV
    simpa [Pi.single_eq_same, Pi.single_eq_of_ne terms_ne.symm] using hV

private theorem termColumn_smul_unit (w : Sh) (x : D₀) :
    (ψw (termWord w).reverse : KLRAlgebra k P (α + δ)) • indShuffleUnit D₀ x = termColumn k w x := by
  unfold indShuffleUnit
  rw [BalancedTensor.smul_tmul']
  congr 1

private theorem termColumn_action (w : Sh) (x : D) :
    parabolicStandardAction (parameter k) weights singleBlack singleBlack D (parameterSymm' k)
      (tensorOfKLR (parameter k) weights (singleBlack + singleBlack)
        (ψw (termWord w).reverse))
      (parabolicStandardUnit (parameter k) weights singleBlack singleBlack D x) =
    projV (termColumn k w x) := by
  have he := castKLR_ψw (k := k) (Q := P)
    (parabolicInputWeights_add (ℓ := 1) singleBlack singleBlack) (termWord w).reverse
  unfold tensorOfKLR
  rw [← he, parabolicStandardAction_affine]
  let a : KLRAlgebra k P (α + δ) := ψw (termWord w).reverse
  have hm := orderedShuffleAction_mkQ ρ F
    (parabolicShuffle_returns (parameter k) weights singleBlack singleBlack D (parameterSymm' k))
      a (indShuffleUnit D₀ x)
  exact hm.trans (congrArg projV (termColumn_smul_unit k w x))

set_option maxHeartbeats 2400000 in
/-- The two terminal shuffle columns of the parabolic test representation
remain independent after imposing the red order. -/
theorem terminalParabolicColumns_injective :
    Function.Injective (fun x : D × D =>
      parabolicStandardAction (parameter k) weights singleBlack singleBlack D (parameterSymm' k)
        (tensorOfKLR (parameter k) weights (singleBlack + singleBlack) (ψw [1]))
        (parabolicStandardUnit (parameter k) weights singleBlack singleBlack D x.1) +
      parabolicStandardAction (parameter k) weights singleBlack singleBlack D (parameterSymm' k)
        (tensorOfKLR (parameter k) weights (singleBlack + singleBlack) (ψw [2, 1]))
        (parabolicStandardUnit (parameter k) weights singleBlack singleBlack D x.2)) := by
  have hu : (termWord termU).reverse = [1] := by simp [termWord]
  have hv : (termWord termV).reverse = [2, 1] := by simp [termWord, terms_ne.symm]
  intro x y h
  refine termPair_injective' k (a₁ := (x : D₀ × D₀)) (a₂ := (y : D₀ × D₀)) ?_
  change projV (termColumn k termU x.1 + termColumn k termV x.2) =
    projV (termColumn k termU y.1 + termColumn k termV y.2)
  rw [map_add, map_add, ← termColumn_action, ← termColumn_action,
    ← termColumn_action, ← termColumn_action, hu, hv]
  exact h
end Categorification.Stendhal.LabelTwo
