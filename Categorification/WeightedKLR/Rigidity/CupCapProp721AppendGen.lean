/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendLeft

/-!
# Appending a black strand to the generators of `λ` at the maximum

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for a cap not at the right end (`j < ℓ`). In the model of the cap bimodule the
generators `e(t)`, `x_a` and `ψ_p` of the KLR algebra of `λ` act through the diagrams
`CupCap.midIdem`, `CupCap.midDot` and `CupCap.midCross` of `λ⁺`, placed above the maximum.
Appending a black strand `i` at the right of these diagrams gives the corresponding diagrams at
the black weight `{i} + ν`, cut by the idempotent `e' = ∑_s e(s i)` of the appended loadings
(`CupCap.appendPlus_midDot`, `CupCap.appendPlus_midCross`): these are the diagrams of the
appended generators `appendBlack(x_a) = x_a e'` and `appendBlack(ψ_p) = ψ_p e'`.

## Main results

* `CupCap.appendPlus_midDot`, `CupCap.appendPlus_midCross`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I} (ν : Multiset I) (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "ρ" => stendhalWeight (ℓ + 2) (ν + ν₀)
local notation "ρᵢ" => stendhalWeight (ℓ + 2) (νᵢ + ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Ap" => appendPlus Q Λ Λc j hj ν ν₀ i

/-- The idempotent `e'` of the appended loadings, as a KLR diagram of `λ⁺`. -/
abbrev appendIdemKLR : KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) ρᵢ :=
  ∑ s : Seq (stendhalWeight ℓ ν), midIdem j hj Q Λ Λc νᵢ ν₀ (appendBlackLoading i ν s)

theorem appendPlus_ψ_mul {p : ℕ} (hp : p + 1 < Multiset.card ρ) (z : Rp) :
    Ap (KLRAlgebra.ψ p * z) = KLRAlgebra.ψ p * Ap z := by
  rw [map_mul, appendPlus_ψ hp, mul_assoc, appendPlus_one_mul]

theorem appendPlus_ψw_mul (l : List ℕ) (hl : ∀ q ∈ l, q + 1 < Multiset.card ρ) (z : Rp) :
    Ap (KLRAlgebra.ψw l * z) = KLRAlgebra.ψw l * Ap z := by
  induction l with
  | nil => exact (congrArg Ap (one_mul z)).trans (one_mul _).symm
  | cons q l ih =>
    have hq := hl q (List.mem_cons_self ..)
    have hl' : ∀ q ∈ l, q + 1 < Multiset.card ρ := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    simp only [KLRAlgebra.ψw, List.map_cons, List.prod_cons] at ih ⊢
    rw [mul_assoc, appendPlus_ψ_mul ν i hq, ih hl', mul_assoc]

theorem appendPlus_x_mul (c : Fin (Multiset.card ρ)) (z : Rp) :
    Ap (KLRAlgebra.x c * z) =
      KLRAlgebra.x (Fin.cast (congrArg Multiset.card (plusAddBlack ν ν₀ i))
        (Seq.posL (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin (ℓ + 2))) c)) * Ap z := by
  rw [map_mul, appendPlus_x, mul_assoc, appendPlus_one_mul]

/-- The strand `a` of `λ` at the black weight `ν`, as a strand at `{i} + ν`. -/
def appendStrand (a : Fin m) : Fin (Multiset.card (stendhalWeight ℓ νᵢ)) :=
  ⟨a.val, by
    have h2 := congrArg Multiset.card (stendhalWeight_addBlack (ℓ := ℓ) i ν)
    rw [Multiset.card_add, Multiset.card_singleton] at h2
    exact Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt a.2) h2⟩

/-- **Appending the strand to a dot of `λ` at the maximum**, for `j < ℓ`. -/
theorem appendPlus_midDot (h : j < ℓ) (a : Fin m) :
    Ap (midDot j hj Q Λ Λc ν ν₀ a) =
      midDot j hj Q Λ Λc νᵢ ν₀ (appendStrand ν i a) * appendIdemKLR ν i := by
  rw [midDot, map_sum, appendIdemKLR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [appendPlus_x_mul, ← midIdem, appendPlus_midIdem ν i h, midIdem, midDot_mul_eSum]
  congr 2
  apply Fin.ext
  rw [Fin.val_cast, Seq.posL_val, dotPos_val', dotPos_val']
  simp only [appendStrand, midPos_appendBlackLoading j ν i h s]

theorem appendPlus_eSum_mid (h : j < ℓ) (s : Seq (stendhalWeight ℓ ν)) :
    Ap (KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s)
      (midPos_le j s))) =
      KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) (appendBlackLoading i ν s)
        (midPos j (appendBlackLoading i ν s)) (midPos_le j _)) :=
  appendPlus_midIdem ν i h s

/-- **Appending the strand to a crossing of `λ` at the maximum, on one loading**, for `j < ℓ`. -/
theorem appendPlus_midCrossAt (h : j < ℓ) (s : Seq (stendhalWeight ℓ ν)) {p : ℕ}
    (hp : p + 1 < m) :
    Ap (midCrossAt j hj Q Λ Λc ν ν₀ s p) =
      midCrossAt j hj Q Λ Λc νᵢ ν₀ (appendBlackLoading i ν s) p := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hmid := midPos_appendBlackLoading j ν i h s
  have hs := midPos_le j s
  have hl : ∀ (q : ℕ) (hq : q < m) (hq' : q < Multiset.card (stendhalWeight ℓ νᵢ)),
      (appendBlackLoading i ν s).lbl ⟨q, hq'⟩ = s.lbl ⟨q, hq⟩ := fun q hq hq' =>
    appendBlackLoading_lbl_of_lt i ν s ⟨q, hq'⟩ hq
  unfold midCrossAt
  have hp' : p + 1 < Multiset.card (stendhalWeight ℓ νᵢ) := by omega
  simp only [hp, hp', ↓reduceDIte, hmid]
  split_ifs with h1 h2
  · rw [hl p (by omega) (by omega)]
    cases s.lbl ⟨p, by omega⟩ with
    | inl c =>
      simp only []
      rw [mul_assoc, appendPlus_ψ_mul ν i (by omega), underLeft,
        appendPlus_ψw_mul ν i _ (fun q hq => by
          simp only [List.mem_reverse, List.mem_range'] at hq; omega),
        appendPlus_eSum_mid ν i h, mul_assoc]
      simp only [hmid]
      rfl
    | inr r => simp only [map_zero]
  · rw [hl (p + 1) hp (by omega)]
    cases s.lbl ⟨p + 1, hp⟩ with
    | inl c =>
      simp only []
      rw [map_smul, mul_assoc, underRight,
        appendPlus_ψw_mul ν i _ (fun q hq => by simp only [List.mem_range'] at hq; omega),
        appendPlus_ψ_mul ν i (by omega), appendPlus_eSum_mid ν i h, mul_assoc]
      simp only [hmid]
      rfl
    | inr r => simp only [map_zero]
  · rw [appendPlus_ψ_mul ν i (by unfold crossPos; split_ifs <;> omega),
      appendPlus_eSum_mid ν i h]
    simp only [hmid]

/-- **Appending the strand to a crossing of `λ` at the maximum**, for `j < ℓ`. -/
theorem appendPlus_midCross (h : j < ℓ) {p : ℕ} (hp : p + 1 < m) :
    Ap (midCross j hj Q Λ Λc ν ν₀ p) = midCross j hj Q Λ Λc νᵢ ν₀ p * appendIdemKLR ν i := by
  rw [midCross, map_sum, appendIdemKLR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [appendPlus_midCrossAt ν i h s hp, midIdem, midCross_mul_eSum]

end Categorification.Stendhal.CupCap
