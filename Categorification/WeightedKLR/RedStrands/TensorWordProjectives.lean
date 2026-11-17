/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorWordWeights
import Categorification.WeightedKLR.RedStrands.DividedProjectives
import Categorification.WeightedKLR.RedStrands.AddRed

/-!
# The projective and vector indexed by an ordered divided word

Webster, arXiv:1309.3796v2, §4.7, Lemmas 4.36–4.37 and Theorem 4.38.
The index for a divided tensor vector also describes a red-ordered
loading. Its divided projective has the usual black nilHecke shift.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KL2 QuantumGroup Categorification.Graded
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} {ℓ : ℕ}

/-- Adjoining a red strand renumbers the existing red labels and appends
the new largest one. A divided black block retains its multiplicity. -/
def TensorWord.blocks : {n : ℕ} → TensorWord I n → List ((I ⊕ Fin n) × ℕ)
  | _, .empty => []
  | n + 1, .red w => w.blocks.map (Prod.map (addRedColor n) id) ++ [(.inr (Fin.last n), 1)]
  | _, .black w i a => w.blocks ++ [(.inl i, a)]

/-- The ordered list of black blocks, with their divided multiplicities. -/
def TensorWord.blackBlocks : {n : ℕ} → TensorWord I n → List (I × ℕ)
  | _, .empty => []
  | _, .red w => w.blackBlocks
  | _, .black w i a => w.blackBlocks ++ [(i, a)]

private theorem expand_map {J : Type*} (f : I → J) (d : List (I × ℕ)) :
    expandDiv (d.map (Prod.map f id)) = (expandDiv d).map f := by
  induction d with
  | nil => rfl
  | cons q d ih =>
    simp only [expandDiv, List.map_cons, List.flatMap_cons, Prod.map_fst, Prod.map_snd, id_eq,
      List.map_append, List.map_replicate] at ih ⊢
    rw [ih]

private theorem expand_red (w : TensorWord I ℓ) : expandDiv w.red.blocks =
    (expandDiv w.blocks).map (addRedColor ℓ) ++ [.inr (Fin.last ℓ)] := by
  rw [TensorWord.blocks, expandDiv_append, expand_map]
  rfl

private theorem expand_black (w : TensorWord I ℓ) (i : I) (n : ℕ) :
    expandDiv (w.black i n).blocks = expandDiv w.blocks ++ List.replicate n (.inl i) := by
  rw [TensorWord.blocks, expandDiv_append]
  simp [expandDiv]

theorem TensorWord.blocks_weight : ∀ {n : ℕ} (w : TensorWord I n),
    (expandDiv w.blocks : Multiset _) = stendhalWeight n w.content.toMultiset
  | _, .empty => by simp [TensorWord.blocks, TensorWord.content, stendhalWeight, expandDiv]
  | _, .red w => by
    rw [expand_red, ← Multiset.coe_add, ← Multiset.map_coe, w.blocks_weight]
    exact stendhalWeight_addRed
  | _, .black w i a => by
    rw [expand_black, ← Multiset.coe_add, w.blocks_weight]
    simp [TensorWord.content, stendhalWeight, Finsupp.toMultiset_single, Multiset.nsmul_singleton,
      Multiset.coe_replicate, add_right_comm]

private def redOrder : I ⊕ Fin ℓ → I ⊕ Fin ℓ → Prop
  | .inr a, .inr b => a < b
  | _, _ => True

private theorem pairwise_redOrder : ∀ {n : ℕ} (w : TensorWord I n), (expandDiv w.blocks).Pairwise redOrder
  | _, .empty => .nil
  | n+1, .red w => by
    rw [expand_red, List.pairwise_append]
    refine ⟨(pairwise_redOrder w).map (addRedColor n) (fun a b h => ?_), by simp, ?_⟩
    · cases a <;> cases b <;> exact h
    · intro a ha b hb
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp ha
      obtain rfl := List.mem_singleton.mp hb
      cases z with
      | inl => trivial
      | inr j => exact Fin.castSucc_lt_last j
  | _, .black w i a => by
    rw [expand_black, List.pairwise_append]
    refine ⟨pairwise_redOrder w, List.pairwise_replicate.mpr (Or.inr trivial), ?_⟩
    intro x _ y hy
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hy
    cases x <;> trivial

/-- The red labels of the expanded word occur in their prescribed order. -/
theorem TensorWord.blocks_redOrdered (w : TensorWord I ℓ) : IsRedOrdered (Seq.ofList _ w.blocks_weight) := by
  intro a b r s hab ha hb
  rw [Seq.ofList_lbl] at ha hb
  have hn := congrArg Multiset.card w.blocks_weight
  simp only [Multiset.coe_card] at hn
  have h := (pairwise_redOrder w).rel_getElem_of_lt (hn.symm ▸ a.isLt) (hn.symm ▸ b.isLt) hab
  rw [ha, hb] at h
  exact h

/-- The boundary loading of a divided tensor word. -/
def TensorWord.loading (w : TensorWord I ℓ) : Seq (stendhalWeight ℓ w.content.toMultiset) :=
  Seq.ofList _ w.blocks_weight

theorem TensorWord.loading_red (w : TensorWord I ℓ) : w.red.loading = appendRedLoading w.loading := by
  change (Seq.ofList _ (show (↑(expandDiv w.red.blocks) : Multiset _) = stendhalWeight (ℓ+1) w.content.toMultiset from w.red.blocks_weight)) = _
  apply Subtype.ext
  funext a
  change (Seq.ofList _ (show _ = stendhalWeight (ℓ+1) w.content.toMultiset from w.red.blocks_weight)).lbl a = (appendRedLoading w.loading).lbl a
  have hn : (expandDiv w.blocks).length = w.content.toMultiset.card + ℓ := by
    simpa [stendhalWeight] using congrArg Multiset.card w.blocks_weight
  rcases eq_lastRedPosition_or a with rfl | ⟨b, rfl⟩
  · rw [show (appendRedLoading w.loading).lbl _ = .inr (Fin.last ℓ) from hasLastRed_appendRedLoading _,
      Seq.ofList_lbl]
    simp only [getElem_congr_coll (expand_red w)]
    rw [List.getElem_append_right]
    · simp [lastRedPosition, hn]
    · simp [lastRedPosition, hn]
  · rw [appendRedLoading_lbl, Seq.ofList_lbl]
    simp only [getElem_congr_coll (expand_red w)]
    rw [List.getElem_append_left]
    · simp [TensorWord.loading, Seq.ofList_lbl]
    · have hb := b.isLt
      simp [stendhalWeight] at hb
      simpa [hn] using hb

private theorem diag_addRed (C : CartanDatum I) (a : I ⊕ Fin ℓ) :
    (affineCoverCartan C (ℓ + 1)).dot (addRedColor ℓ a) (addRedColor ℓ a) =
      (affineCoverCartan C ℓ).dot a a := by
  cases a with
  | inl i => rfl
  | inr j =>
    change (CartanDatum.ofGraph _).dot _ _ = (CartanDatum.ofGraph _).dot _ _
    rw [CartanDatum.ofGraph_dot_self, CartanDatum.ofGraph_dot_self]

/-- There is no grading shift for a red insertion. Each black divided
block contributes its Cartan half-degree times its triangular number. -/
theorem TensorWord.blocks_angle (C : CartanDatum I) : ∀ {n : ℕ} (w : TensorWord I n),
    divAngle2 (affineCoverCartan C n) w.blocks = divAngle2 C w.blackBlocks
  | _, .empty => rfl
  | _, .red w => by
    rw [TensorWord.blocks, divAngle2_append, show divAngle2 _ [(_, 1)] = 0 by simp [divAngle2],
      add_zero, TensorWord.blackBlocks, ← w.blocks_angle C]
    simp [divAngle2, List.map_map, Function.comp_def, diag_addRed]
  | _, .black w i a => by
    rw [TensorWord.blocks, TensorWord.blackBlocks, divAngle2_append, divAngle2_append, w.blocks_angle]
    rfl

/-- The divided-word factorial uses only the black multiplicities. -/
theorem TensorWord.blocks_factorial (C : CartanDatum I) : ∀ {n : ℕ} (w : TensorWord I n),
    divQFact2 (affineCoverCartan C n) w.blocks = divQFact2 C w.blackBlocks
  | _, .empty => rfl
  | _, .red w => by
    rw [TensorWord.blocks, divQFact2_append, show divQFact2 _ [(_, 1)] = 1 by simp [divQFact2],
      mul_one, TensorWord.blackBlocks, ← w.blocks_factorial C]
    simp [divQFact2, List.map_map, Function.comp_def, diag_addRed]
  | _, .black w i a => by
    rw [TensorWord.blocks, TensorWord.blackBlocks, divQFact2_append, divQFact2_append, w.blocks_factorial]
    rfl

variable [DecidableEq I]

section Vectors

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF QuantumGroup.UDot KLGamma
open scoped TensorProduct

local notation "v" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

variable {Y : Type*} [AddCommGroup Y] {C : CartanDatum I} {R : C.toLusztig.RootDatum Y}

/-- The vector of the expanded loading, applying ordinary lowering at each black strand. -/
def tensorWordUndivided : {n : ℕ} → TensorWord I n → (wt : Fin n → Dom R) → TensorSpace wt
  | _, .empty, wt => tensorWordVector .empty wt
  | n+1, .red w, wt => appendTensor wt (tensorWordUndivided w (fun j => wt (Fin.castSucc j)))
      (IrreducibleModule.hwv R v (wt (Fin.last n)).1)
  | _, .black w i a, wt => tensorRepresentation wt (F R v i ^ a) (tensorWordUndivided w wt)

/-- On the vector side the expanded loading has the same quantum factorial
as its projective. Here the KLR Laurent grading parameter evaluates to `v⁻¹`. -/
theorem tensorWordVector_factorial : ∀ {n : ℕ} (w : TensorWord I n) (wt : Fin n → Dom R),
    tensorWordUndivided w wt = qToV (divQFact2 C w.blackBlocks) • tensorWordVector w wt
  | _, .empty, wt => by simp [tensorWordUndivided, TensorWord.blackBlocks, divQFact2]
  | _, .red w, wt => by
    rw [tensorWordUndivided, tensorWordVector_factorial w, TensorWord.blackBlocks,
      tensorWordVector, appendTensor, ← TensorProduct.smul_tmul', map_smul]
    rfl
  | _, .black w i a, wt => by
    rw [tensorWordUndivided, tensorWordVector_factorial w, map_smul, TensorWord.blackBlocks,
      divQFact2_append, map_mul, mul_smul, tensorWordVector]
    congr 1
    have hfac : qToV (divQFact2 C [(i,a)]) = qFactorial (v ^ C.toLusztig.d i) a := by
      rw [KL2Gamma.qToV_divQFact2]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      rw [← PreF.qFactorial_eq_qfact, PreF.val_vi]
      rfl
    change tensorRepresentation wt (F R v i ^ a) _ = qToV (divQFact2 C [(i,a)]) •
      tensorRepresentation wt (qDivPow (v ^ C.toLusztig.d i) a (F R v i)) _
    rw [hfac, qDivPow, map_smul, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀, one_smul]
    rw [← hfac]
    exact KL2Gamma.qToV_divQFact2_ne_zero C _

end Vectors

variable {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I) (hQ : IsRouquierQ C Q)

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

/-- The shifted divided projective indexed by the same word as `tensorWordVector`. -/
def tensorWordProjective (w : TensorWord I ℓ) :
    GProj (tensorProductGrade G w.content.toMultiset) :=
  dividedSequenceProj Λ C hQ _ w.blocks w.blocks_weight

/-- Expanding a shared word multiplies its shifted projective class by exactly
the product of the black quantum factorials. -/
theorem tensorWordProjective_factorial (w : TensorWord I ℓ) :
    K0.of (sequenceProj G (Seq.ofList _ w.blocks_weight) w.blocks_redOrdered) =
      divQFact2 C w.blackBlocks • K0.of (tensorWordProjective Λ C hQ w) := by
  rw [← w.blocks_factorial C]
  exact sequenceProj_eq_factorial Λ C hQ _ w.blocks w.blocks_weight w.blocks_redOrdered

/-- For a comparison map sending the grading shift to `v⁻¹`, testing its
value on an expanded loading is equivalent to testing the correctly shifted
divided projective against its divided tensor vector (Webster, §4.7). -/
theorem map_tensorWordProjective_iff {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y}
    (wt : Fin ℓ → LieLean.QuantumGroup.GrandLoop.Dom R) (w : TensorWord I ℓ)
    (f : K0 (tensorProductGrade G w.content.toMultiset) →ₛₗ[KLGamma.qToV] TensorSpace wt) :
    f (K0.of (sequenceProj G w.loading w.blocks_redOrdered)) = tensorWordUndivided w wt ↔
      f (K0.of (tensorWordProjective Λ C hQ w)) = tensorWordVector w wt := by
  unfold TensorWord.loading
  rw [tensorWordProjective_factorial Λ C hQ w, map_smulₛₗ, tensorWordVector_factorial]
  exact (isRegular_iff_ne_zero.mpr (KL2Gamma.qToV_divQFact2_ne_zero C _)).smul_right_inj

end Categorification.Stendhal.FirstWeight
