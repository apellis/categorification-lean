/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastRed
import Categorification.WeightedKLR.RedStrands.LastStrandDecomposition
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndMap

/-!
# The last red strand on a standardization with a nonempty last block

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. In the standardization `S N` of a module `N` over `T^{λ'} ⊗ R^{λ_ℓ}_β` with
`β` nonempty, the black strands of the last block cannot pass to the left of the red strand
`λ_ℓ`. Hence no loading of `S N` ends with the red strand `λ_ℓ`: the idempotent `e_ℓ` of the
loadings with the last strand red acts by zero.

## Main results

* `Seq.eq_of_lbl_eq_of_count_le_one`: a label occurring at most once in the weight occurs at
  one position only.
* `lastRedIdem_smul_parabolicStandardT`: `e_ℓ` acts by zero on `S N` when `β ≠ 0`.
-/

noncomputable section

namespace Categorification.KLR.Seq

variable {J : Type*} [DecidableEq J] {μ : Multiset J}

/-- A label occurring at most once in the weight occurs at one position only. -/
theorem eq_of_lbl_eq_of_count_le_one (s : Seq μ) {c : J} (hc : μ.count c ≤ 1)
    {a b : Fin (Multiset.card μ)} (ha : s.lbl a = c) (hb : s.lbl b = c) : a = b := by
  classical
  have hcard : (Finset.univ.filter (fun a => c = s.lbl a)).card ≤ 1 := by
    rw [← s.2, Multiset.count_map] at hc
    exact hc
  exact Finset.card_le_one_iff.mp hcard (by simp [ha]) (by simp [hb])

end Categorification.KLR.Seq

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) (θ β : Multiset I)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
  (stendhalWeight 1 β)
local notation "S" => stendhalQ Q Λ
local notation "νall" => (θ + β)
variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
local notation "N₀" => ParabolicInput Q Λ θ β N
local notation "ρ" => parabolicShuffleAction Q Λ θ β N
local notation "F" => parabolicOrderedLoadings (ℓ := ℓ) θ β
local notation "π" => Submodule.mkQ (excludedSpace ρ F)

omit [DecidableEq I] in
private theorem card_lastBlock : (δ).card = β.card + 1 := by simp [stendhalWeight]

omit [DecidableEq I] in
private theorem card_prefixBlock : (α).card = θ.card + ℓ := by simp [stendhalWeight]

/-- The last position of the last block. -/
private def zLast : Fin (δ).card := ⟨(δ).card - 1, by rw [card_lastBlock]; omega⟩

private theorem count_lastBlock_red :
    (δ).count (Sum.inr (Fin.last ℓ) : I ⊕ Fin (ℓ + 1)) ≤ 1 := by
  have hb : (δ) = β.map Sum.inl + ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ+1))) := by
    simp [stendhalWeight, Function.comp_def]
  rw [hb, Multiset.count_add, Multiset.count_eq_zero_of_notMem (by simp)]
  simp

private theorem count_all_red :
    (α + δ).count (Sum.inr (Fin.last ℓ) : I ⊕ Fin (ℓ + 1)) ≤ 1 := by
  rw [parabolicInputWeights_add]
  have hred : Multiset.count (Sum.inr (Fin.last ℓ) : I ⊕ Fin (ℓ + 1))
      ((θ + β).map Sum.inl) = 0 := Multiset.count_eq_zero_of_notMem (by simp)
  rw [stendhalWeight, Multiset.count_add, hred, zero_add]
  exact Multiset.nodup_iff_count_le_one.mp (Finset.univ.nodup.map Sum.inr_injective) _

omit [DecidableEq I] in
private theorem lastBlock_first' (b : Seq δ) (hb : ¬ IsViolated b) :
    b.lbl ⟨0, by rw [card_lastBlock]; omega⟩ = .inr (Fin.last ℓ) := by
  cases hx : b.lbl ⟨0, by rw [card_lastBlock]; omega⟩ with
  | inr r => exact congrArg Sum.inr (parabolicLast_red_eq_last β b _ hx)
  | inl i => exact (hb ⟨_, by rw [hx]; rfl⟩).elim

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- If the final strand of `s` is the red strand `λ_ℓ` and `β ≠ 0`, the concatenation
idempotent of `s` kills the input module. -/
private theorem concatIdem_lastRed (hβ : β ≠ 0) (s : Seq (α+δ))
    (hs : s.lbl (Seq.posR α (zLast β)) = .inr (Fin.last ℓ)) (n : N₀) :
    concatIdem (Q := S) s • n = 0 := by
  by_contra hn
  have hn' : ¬ ∀ n : N₀, concatIdem (Q := S) ((shufOne :
      Shuffle (Seq.card_add' α δ)).1 • s) • n = 0 := by
    intro h; exact hn (by simpa [shufOne] using h n)
  obtain ⟨a, b, he, -, -, -, hb⟩ := parabolicShuffle_supported_input Q Λ θ β N s _ hn'
  have he' : s = a.append b := by simpa [shufOne] using he
  have h0 := lastBlock_first' β b hb
  have h1 : b.lbl (zLast β) = .inr (Fin.last ℓ) := by
    rw [← hs, he']; exact (Seq.append_posR a b _).symm
  have := congrArg Fin.val (Seq.eq_of_lbl_eq_of_count_le_one b (count_lastBlock_red β) h0 h1)
  have hc := card_lastBlock (ℓ := ℓ) β
  simp only [zLast] at this
  exact hβ (Multiset.card_eq_zero.mp (by omega))

/-- On the shuffle module, an idempotent ending with the red strand `λ_ℓ` acts by zero when
`β ≠ 0`. -/
private theorem parabolicShuffle_e_lastRed (hQ : KLRSymm Q) (hβ : β ≠ 0) (s : Seq (α+δ))
    (hs : s.lbl (Seq.posR α (zLast β)) = .inr (Fin.last ℓ))
    (m : ParabolicShuffle Q Λ θ β N) : ρ (e s) m = 0 := by
  have hle : ∀ p : Fin (α+δ).card, s.lbl p = .inr (Fin.last ℓ) → (α).card ≤ p.val := by
    intro p hp
    rw [Seq.eq_of_lbl_eq_of_count_le_one s (count_all_red θ β) hp hs]
    simp [Seq.posR_val]
  obtain ⟨n, hn⟩ := parabolicShuffle_e_smul_mem_unit Q Λ θ β N hQ s hle m
  have hidem : ρ (e s) m = ρ (e s) (ρ (e s) m) := by
    rw [← Module.End.mul_apply, ← map_mul, e_mul_self]
  rw [hidem, hn, parabolicShuffleAction, Algebra.lsmul_coe]
  dsimp only
  rw [idem_smul_indShuffleUnit, concatIdem_lastRed Q Λ θ β N hβ s hs n, indShuffleUnit,
    BalancedTensor.tmul_zero]

/-- **The red strand `λ_ℓ` is never last on `S N`** (arXiv:1309.3796v3, proof of
Proposition 5.5): if the last block is nonempty, the idempotent `e_ℓ` of the loadings ending
with the red strand `λ_ℓ` acts by zero on the standardization. -/
theorem lastRedIdem_smul_parabolicStandardT (hQ : KLRSymm Q) (hβ : β ≠ 0)
    (z : ParabolicStandardT Q Λ θ β N hQ) :
    TensorProductAlgebra.lastRedIdem Q Λ (θ + β) • z = 0 := by
  let H := parabolicInputWeights_add (ℓ := ℓ) θ β
  let T : Finset (Seq (α+δ)) :=
    Finset.univ.filter fun s => (s.lbl (Seq.posR α (zLast β))).isRight
  have hpos (s : Seq (stendhalWeight (ℓ + 1) (θ + β))) :
      (Seq.cast H.symm s).1 (Seq.posR α (zLast β)) = s.1 (lastRedPosition ℓ (θ + β)) := by
    rw [Seq.cast_apply]
    refine congrArg s.1 (Fin.ext ?_)
    simp only [Fin.val_cast, Seq.posR_val, zLast, lastRedPosition]
    simp [stendhalWeight]
    omega
  have hcast : eSum S (Finset.univ.filter fun s => lastBlackColour (θ + β) s = none) =
      castKLR S H (eSum S T) := by
    refine (castKLR_eSum_of_mem_iff H fun s => ?_).symm
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Seq.lbl, hpos, lastBlackColour]
    rcases s.1 (lastRedPosition ℓ (θ + β)) with c | r <;> simp [Sum.getLeft?]
  rw [← lastStrandIdem_none, lastStrandIdem, tensorOfKLR, hcast]
  change parabolicStandardAction Q Λ θ β N hQ _ z = 0
  rw [parabolicStandardAction_affine, eSum, map_sum]
  refine (LinearMap.sum_apply _ _ _).trans (Finset.sum_eq_zero fun s hs => ?_)
  obtain ⟨m, rfl⟩ := (excludedSpace ρ F).mkQ_surjective z
  by_cases ho : s ∈ F
  · have hr : s.lbl (Seq.posR α (zLast β)) = .inr (Fin.last ℓ) := by
      have hT := (Finset.mem_filter.mp hs).2
      rcases hx : s.lbl (Seq.posR α (zLast β)) with c | r
      · rw [hx] at hT; cases hT
      · have hord : IsRedOrdered s := by
          simpa [parabolicOrderedLoadings] using ho
        obtain ⟨a, ha⟩ : ∃ a, s.lbl a = .inr (Fin.last ℓ) := by
          have hm : (Sum.inr (Fin.last ℓ) : I ⊕ Fin (ℓ + 1)) ∈ α + δ := by
            rw [H]; simp [stendhalWeight]; exact em _
          rw [← s.2] at hm
          obtain ⟨a, -, ha⟩ := Multiset.mem_map.mp hm
          exact ⟨a, ha⟩
        have hle : a ≤ Seq.posR α (zLast β) := by
          rw [Fin.le_def]
          have := a.2
          simp only [Seq.posR_val, zLast]
          simp [stendhalWeight] at this ⊢
          omega
        rcases hle.lt_or_eq with hlt | heq
        · exact absurd (hord _ _ _ _ hlt ha hx) (not_lt.2 (Fin.le_last r))
        · rw [← hx, ← heq, ha]
    exact (congrArg π (parabolicShuffle_e_lastRed Q Λ θ β N hQ hβ s hr m)).trans (map_zero _)
  · exact LinearMap.congr_fun (orderedShuffleAction_e_eq_zero _ _ _ s ho) _

end Categorification.Stendhal
