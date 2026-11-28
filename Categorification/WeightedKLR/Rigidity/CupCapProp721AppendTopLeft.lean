/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendTopCap

/-!
# The passage of the appended strand and the action of `λ`, for a cap at the right end

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for a cap at the right end (`j = ℓ`). There the window of a loading `s` of `λ`
sits at its right end `m`. After appending a black strand `i` at the right of the diagrams of
`λ⁺`, the identification `𝔉_i(model_ν) ≅ e' · model_{{i} + ν}` passes the new strand under the
window. In the KLR algebra of `λ⁺` this is left multiplication by
`D = underRight N m · ∑_s e_{s i, m}` (`CupCap.topPass`).

The diagrams of `λ` at `ν` act above the maximum, to the left of the window, and so they commute
with `D` up to the idempotents: `D · appendPlus(Y) = Y' · D` for the generators `Y` of `λ` at `ν`
and their counterparts `Y'` at `{i} + ν` (`CupCap.topPass_mul_appendPlus_midIdem`,
`CupCap.topPass_mul_appendPlus_midDot`, `CupCap.topPass_mul_appendPlus_midCross`).

On generators the identification is `z ⊗ v ↦ z D ⊗ v` (`CupCap.appendTopModelEquiv_tmul_tmul`),
so it carries the action of `T̃^λ_ν` to the action of `T̃^λ_{{i} + ν}` along appending the strand
(`CupCap.appendTopModelEquiv_midLeftAlg`), as `CupCap.appendModelEquiv_midLeftAlg` does for
`j < ℓ`.

## Main definitions

* `CupCap.topPassIdem`: `∑_s e_{s i, m}`, the window idempotents of the appended loadings at `m`.
* `CupCap.topPass`: `D = underRight N m · ∑_s e_{s i, m}`.

## Main results

* `CupCap.appendTopModelEquiv_tmul_tmul`, `CupCap.appendTopModelEquiv_map_midEnd_of`.
* `CupCap.appendTopModelEquiv_midKLRAct`, `CupCap.appendTopModelEquiv_midLeftAlg`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

section Windows

variable {μ : Multiset I}

/-- The windows at the same position of distinct loadings are orthogonal. -/
theorem eSum_insertSet_mul_of_ne {u u' : Seq (stendhalWeight ℓ μ)} (h : u ≠ u') {n : ℕ}
    (hn : n ≤ Multiset.card (stendhalWeight ℓ μ)) :
    (KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
        (insertSet (j := j) (hj := hj) (ν₀ := ν₀) u n hn) *
      KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
        (insertSet (j := j) (hj := hj) (ν₀ := ν₀) u' n hn) :
      KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (μ + ν₀))) = 0 := by
  rw [KLRAlgebra.eSum_mul_eSum, Finset.disjoint_iff_inter_eq_empty.1 ?_, KLRAlgebra.eSum_empty]
  refine Finset.disjoint_left.2 fun w hw hw' => h ?_
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hw
  obtain ⟨t', -, ht'⟩ := Finset.mem_image.1 hw'
  exact eq_of_insertSeq_eq' hn hn rfl ht'.symm

omit [DecidableEq I] in
theorem dotPos_val_of_lt (n : Fin (Multiset.card (stendhalWeight ℓ μ) + 1))
    (a : Fin (Multiset.card (stendhalWeight ℓ μ))) (ha : a.val < n.val) :
    (dotPos (j := j) (hj := hj) (ν₀ := ν₀) n a).val = a.val := by
  rw [dotPos_val']
  simp [ha]

/-- For a cap at the right end, the dot on the strand `a` of `λ` is `x_a` times the sum of
the window idempotents. -/
theorem midDot_eq_of_not_lt (h : ¬ j < ℓ) (a : Fin (Multiset.card (stendhalWeight ℓ μ))) :
    midDot j hj Q Λ Λc μ ν₀ a =
      KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀)
        ⟨Multiset.card (stendhalWeight ℓ μ), Nat.lt_succ_self _⟩ a) *
        ∑ s, midIdem j hj Q Λ Λc μ ν₀ s := by
  rw [midDot, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 2
  apply Fin.ext
  simp only [dotPos_val', midPos_of_not_lt j s h]

/-- For a cap at the right end, the crossing `ψ_p` of `λ` with `p + 1 < m` is `ψ_p` times the
sum of the window idempotents. -/
theorem midCross_eq_of_not_lt (h : ¬ j < ℓ) {p : ℕ}
    (hp : p + 1 < Multiset.card (stendhalWeight ℓ μ)) :
    midCross j hj Q Λ Λc μ ν₀ p = KLRAlgebra.ψ p * ∑ s, midIdem j hj Q Λ Λc μ ν₀ s := by
  rw [midCross, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hs := midPos_of_not_lt j s h
  have h1 : ¬ p + 1 = midPos j s := by omega
  have h2 : ¬ p = midPos j s := by omega
  have h3 : p < midPos j s := by omega
  unfold midCrossAt
  simp only [hp, h1, h2, ↓reduceDIte, ↓reduceIte, crossPos, h3]
  rfl

end Windows

variable (ν) (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "mᵢ" => Multiset.card (stendhalWeight ℓ ((Singleton.singleton i : Multiset I) + ν))
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rpᵢ" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj))
    (stendhalWeight (ℓ + 2) ((Singleton.singleton i : Multiset I) + ν + ν₀))
local notation "Ap" => appendPlus Q Λ Λc j hj ν ν₀ i
local notation "E" s:max n:max hn:max =>
  (KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn) : Rp)
local notation "Eᵢ" u:max n:max hn:max =>
  (KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) u n hn) : Rpᵢ)

omit [DecidableEq I] in
theorem le_card_appendBlackWeight : m ≤ mᵢ := by
  have := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i); omega

omit [DecidableEq I] in
theorem succ_le_card_appendBlackWeight : m + 1 ≤ mᵢ := by
  have := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i); omega

omit [DecidableEq I] in
/-- Appending a black strand on the right commutes with adjacent swaps of the old positions. -/
theorem appendBlackLoading_sadj' (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m) :
    appendBlackLoading i ν (sadj m p • s) = sadj mᵢ p • appendBlackLoading i ν s := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have hp' : p + 1 < mᵢ := by omega
  apply Subtype.ext
  funext a
  change (appendBlackLoading i ν (sadj _ p • s)).lbl a =
    (appendBlackLoading i ν s).lbl ((sadj _ p)⁻¹ a)
  rw [sadj_inv]
  by_cases ha : a.val < m
  · have hsa : (sadj _ p a).val < m := by
      rw [sadj_val_of_lt hp']; unfold swapNat; split_ifs <;> omega
    rw [appendBlackLoading_lbl_of_lt i ν _ a ha, appendBlackLoading_lbl_of_lt i ν _ _ hsa]
    change s.lbl ((sadj _ p)⁻¹ _) = _
    rw [sadj_inv]
    congr 1
    ext
    rw [sadj_val_of_lt hp, sadj_val_of_lt hp']
  · have ha' : a.val = m := by have := a.isLt; omega
    rw [sadj_apply_of_ne a (by omega) (by omega), appendBlackLoading_lbl_of_eq i ν _ a ha',
      appendBlackLoading_lbl_of_eq i ν _ a ha']

/-- **The window idempotents of the appended loadings at `m`**: `∑_s e_{s i, m}`. -/
def topPassIdem : Rpᵢ := ∑ s : Seq (stendhalWeight ℓ ν),
  Eᵢ (appendBlackLoading i ν s) m (le_card_appendBlackWeight ν i)

/-- **The passage of the appended strand under the window**: `underRight N m · ∑_s e_{s i, m}`. -/
def topPass : Rpᵢ :=
  underRight N m * topPassIdem (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) ν i

local notation "eA" => topPassIdem (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) ν i
local notation "D" => topPass (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) ν i
local notation "sᵢ" => appendBlackLoading i ν

theorem topPassIdem_mul_eSum (t : Seq (stendhalWeight ℓ ν)) :
    eA * Eᵢ (sᵢ t) m (le_card_appendBlackWeight ν i) =
      Eᵢ (sᵢ t) m (le_card_appendBlackWeight ν i) := by
  rw [topPassIdem, Finset.sum_mul, Finset.sum_eq_single t
    (fun s _ h => eSum_insertSet_mul_of_ne ((appendBlackLoading_injective' i).ne h) _)
    (by simp), (KLRAlgebra.eSum_idem _).eq]

theorem eSum_mul_topPassIdem (t : Seq (stendhalWeight ℓ ν)) :
    Eᵢ (sᵢ t) m (le_card_appendBlackWeight ν i) * eA =
      Eᵢ (sᵢ t) m (le_card_appendBlackWeight ν i) := by
  rw [topPassIdem, Finset.mul_sum, Finset.sum_eq_single t
    (fun s _ h => eSum_insertSet_mul_of_ne ((appendBlackLoading_injective' i).ne h).symm _)
    (by simp), (KLRAlgebra.eSum_idem _).eq]

theorem topPassIdem_mul_self : eA * eA = eA := by
  conv_lhs => rw [topPassIdem, Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => eSum_mul_topPassIdem ν i t

theorem appendPlus_eSum_insertSet (t : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (hn' : n ≤ mᵢ) : Ap (E t n hn) = Eᵢ (sᵢ t) n hn' := by
  rw [← insertMap_one Q Λ Λc t hn, appendPlus_insertMap t n hn hn', insertMap_one]

theorem midIdem_eq_of_not_lt (h : ¬ j < ℓ) (t : Seq (stendhalWeight ℓ ν)) :
    midIdem j hj Q Λ Λc ν ν₀ t = E t m le_rfl := by
  rw [midIdem, insertSet_congr' t (midPos_le j t) le_rfl (midPos_of_not_lt j t h)]

theorem midIdem_append_eq_of_not_lt (h : ¬ j < ℓ) (u : Seq (stendhalWeight ℓ νᵢ)) :
    midIdem j hj Q Λ Λc νᵢ ν₀ u = Eᵢ u (m + 1) (succ_le_card_appendBlackWeight ν i) := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  rw [midIdem, insertSet_congr' u (midPos_le j u) (succ_le_card_appendBlackWeight ν i)
    (by rw [midPos_of_not_lt j u h, hm])]

theorem appendPlus_sum_midIdem (h : ¬ j < ℓ) :
    Ap (∑ t, midIdem j hj Q Λ Λc ν ν₀ t) = eA := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun t _ => by
    rw [midIdem_eq_of_not_lt ν h, appendPlus_eSum_insertSet ν i t le_rfl]

theorem topPass_eq :
    D = ∑ s : Seq (stendhalWeight ℓ ν),
      Eᵢ (sᵢ s) (m + 1) (succ_le_card_appendBlackWeight ν i) * underRight N m := by
  rw [topPass, topPassIdem, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ =>
    underRight_mul_eSum Q Λ Λc (sᵢ s) (succ_le_card_appendBlackWeight ν i)

theorem topPass_mul_topPassIdem : D * eA = D := by
  rw [topPass, mul_assoc, topPassIdem_mul_self]

/-- `∑_u e_{u, m + 1}` fixes `D` from the left. -/
theorem sum_midIdem_mul_topPass (h : ¬ j < ℓ) :
    (∑ u, midIdem j hj Q Λ Λc νᵢ ν₀ u) * D = D := by
  conv_lhs => rw [topPass_eq, Finset.mul_sum]
  conv_rhs => rw [topPass_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← mul_assoc, Finset.sum_mul, Finset.sum_eq_single (sᵢ s)
    (fun u _ hu => by
      rw [midIdem_append_eq_of_not_lt ν i h]
      exact eSum_insertSet_mul_of_ne hu _)
    (fun h' => absurd (Finset.mem_univ _) h'), midIdem_append_eq_of_not_lt ν i h,
    (KLRAlgebra.eSum_idem _).eq]

/-- `e' = ∑_s e(s i)` fixes `D` from the left. -/
theorem appendIdemKLR_mul_topPass (h : ¬ j < ℓ) :
    appendIdemKLR (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ) (Λc := Λc) ν i * D = D := by
  conv_lhs => rw [topPass_eq, Finset.mul_sum]
  conv_rhs => rw [topPass_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← mul_assoc, appendIdemKLR, Finset.sum_mul, Finset.sum_eq_single s
    (fun s' _ hs => by
      rw [midIdem_append_eq_of_not_lt ν i h]
      exact eSum_insertSet_mul_of_ne ((appendBlackLoading_injective' i).ne hs) _)
    (fun h' => absurd (Finset.mem_univ _) h'), midIdem_append_eq_of_not_lt ν i h,
    (KLRAlgebra.eSum_idem _).eq]

theorem topPass_mul_appendPlus_one (h : ¬ j < ℓ) : D * Ap 1 = D := by
  rw [topPass, ← appendPlus_sum_midIdem ν i h, mul_assoc, ← map_mul, mul_one]

/-- **`D` and the idempotents of `λ`**: `D · appendPlus(e_t) = e_{t i} · D`. -/
theorem topPass_mul_appendPlus_midIdem (h : ¬ j < ℓ) (t : Seq (stendhalWeight ℓ ν)) :
    D * Ap (midIdem j hj Q Λ Λc ν ν₀ t) = midIdem j hj Q Λ Λc νᵢ ν₀ (sᵢ t) * D := by
  rw [midIdem_eq_of_not_lt ν h, appendPlus_eSum_insertSet ν i t le_rfl
      (le_card_appendBlackWeight ν i), midIdem_append_eq_of_not_lt ν i h, topPass,
    mul_assoc, topPassIdem_mul_eSum, ← mul_assoc,
    ← underRight_mul_eSum Q Λ Λc (sᵢ t) (succ_le_card_appendBlackWeight ν i), mul_assoc,
    eSum_mul_topPassIdem]

theorem commute_x_topPassIdem (c : Fin (Multiset.card
    (stendhalWeight (ℓ + 2) ((Singleton.singleton i : Multiset I) + ν + ν₀)))) :
    Commute (KLRAlgebra.x c : Rpᵢ) eA :=
  Commute.sum_right _ _ _ fun _ _ => commute_x_eSum c _

/-- **`D` and the dots of `λ`**: `D · appendPlus(x_a) = x_a e' · D`. -/
theorem topPass_mul_appendPlus_midDot (h : ¬ j < ℓ) (a : Fin m) :
    D * Ap (midDot j hj Q Λ Λc ν ν₀ a) =
      midDot j hj Q Λ Λc νᵢ ν₀ (appendStrand ν i a) *
        appendIdemKLR (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ) (Λc := Λc) ν i * D := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  rw [mul_assoc, appendIdemKLR_mul_topPass ν i h, midDot_eq_of_not_lt h,
    midDot_eq_of_not_lt h, appendPlus_x_mul, appendPlus_sum_midIdem ν i h, mul_assoc,
    sum_midIdem_mul_topPass ν i h, topPass, mul_assoc, ← mul_assoc eA,
    ← (commute_x_topPassIdem ν i _).eq, mul_assoc, topPassIdem_mul_self, ← mul_assoc,
    ← (commute_x_underRight _ (Or.inl ?_)).eq, mul_assoc]
  · congr 2
    apply Fin.ext
    rw [Fin.val_cast, Seq.posL_val, dotPos_val_of_lt _ _ (Fin.isLt _),
      dotPos_val_of_lt _ _ (Fin.isLt _)]
    rfl
  · rw [Fin.val_cast, Seq.posL_val, dotPos_val_of_lt _ _ (Fin.isLt _)]
    exact a.2

/-- The crossings of `λ` commute with `∑_s e_{s i, m}`. -/
theorem commute_ψ_topPassIdem {p : ℕ} (hp : p + 1 < m) : Commute (KLRAlgebra.ψ p : Rpᵢ) eA := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have hc : crossPos m N p = p := by
    unfold crossPos
    split_ifs
    · rfl
    · omega
  change KLRAlgebra.ψ p * eA = eA * KLRAlgebra.ψ p
  rw [topPassIdem, Finset.mul_sum, Finset.sum_mul]
  have h1 : ∀ t : Seq (stendhalWeight ℓ ν),
      (KLRAlgebra.ψ p : Rpᵢ) * Eᵢ (sᵢ t) m (le_card_appendBlackWeight ν i) =
        Eᵢ (sᵢ (sadj m p • t)) m (le_card_appendBlackWeight ν i) * KLRAlgebra.ψ p := fun t => by
    have := ψ_crossPos_mul_eSum (k := k) (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
      (ν₀ := ν₀) (sᵢ t) (le_card_appendBlackWeight ν i) (p := p) (Or.inl hp)
    rw [hc] at this
    rw [appendBlackLoading_sadj' ν i t hp]
    exact this
  simp only [h1]
  exact Equiv.sum_comp (MulAction.toPerm (sadj m p)) fun t =>
    Eᵢ (sᵢ t) m (le_card_appendBlackWeight ν i) * KLRAlgebra.ψ p

/-- **`D` and the crossings of `λ`**: `D · appendPlus(ψ_p) = ψ_p e' · D` for `p + 1 < m`. -/
theorem topPass_mul_appendPlus_midCross (h : ¬ j < ℓ) {p : ℕ} (hp : p + 1 < m) :
    D * Ap (midCross j hj Q Λ Λc ν ν₀ p) =
      midCross j hj Q Λ Λc νᵢ ν₀ p *
        appendIdemKLR (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ) (Λc := Λc) ν i * D := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  rw [mul_assoc, appendIdemKLR_mul_topPass ν i h, midCross_eq_of_not_lt h hp,
    midCross_eq_of_not_lt h (by omega), appendPlus_ψ_mul ν i (by omega),
    appendPlus_sum_midIdem ν i h, mul_assoc, sum_midIdem_mul_topPass ν i h, topPass, mul_assoc,
    ← mul_assoc eA, ← (commute_ψ_topPassIdem ν i hp).eq, mul_assoc, topPassIdem_mul_self,
    ← mul_assoc, ← (commute_ψ_underRight p (Or.inl hp)).eq, mul_assoc]

section Model

local notation "bot'" => botMap k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀
local notation "ψA" => appendMidOp Q Λ Λc j hj ν ν₀ i
local notation "φB" => midOp j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀
local notation "Tᵢ" => (StendhalAlgebra k Q (plusLabels Λ Λc j hj)
  ((Singleton.singleton i : Multiset I) + ν + ν₀))ᵐᵒᵖ

theorem topPassOp_mul_midOp_one (h : ¬ j < ℓ) : op (bot' D) * φB 1 = op (bot' D) := by
  rw [midOp_apply, ← op_mul, unop_one, midStendhal_one_eq_botMap, ← map_mul,
    sum_midIdem_mul_topPass ν i h]

omit [DecidableEq I] in
theorem midPos_succ_le_of_not_lt (h : ¬ j < ℓ) (s : Seq (stendhalWeight ℓ ν)) :
    midPos j s + 1 ≤ mᵢ := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  rw [midPos_of_not_lt j s h]; omega

/-- **The passage of the appended strand, loading by loading**: the window of `s i` at `m`,
the passage of the strand under it and the window of `s i` at `m + 1` multiply to `D`. -/
theorem sum_posOp_posPassRightElt (h : ¬ j < ℓ) :
    ∑ s : Seq (stendhalWeight ℓ ν),
        posOp j hj Q Λ Λc ν₀ (sᵢ s) (midPos j s) (midPos_le_appendBlackLoading j ν i s) 1 *
          posPassRightElt j hj Q Λ Λc ν₀ (sᵢ s) (midPos j s) (midPos_succ_le_of_not_lt ν i h s) *
          posOp j hj Q Λ Λc ν₀ (sᵢ s) (midPos j (sᵢ s)) (midPos_le j _) 1 =
      op (bot' D) := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  rw [topPass, topPassIdem, Finset.mul_sum, map_sum]
  refine (Finset.sum_congr rfl fun s _ => ?_).trans (map_sum (MulOpposite.opAddEquiv) _ _).symm
  apply MulOpposite.unop_injective
  change _ = botMap k Q Λ Λc j hj νᵢ ν₀ _
  rw [unop_mul, unop_mul, posOp_apply, posOp_apply, posPassRightElt, unop_op, unop_op, unop_op,
    unop_one, posStendhal_one, posStendhal_one, ← map_mul, ← map_mul]
  congr 1
  have h1 : midPos j (sᵢ s) = m + 1 := by rw [midPos_of_not_lt j _ h, hm]
  have h2 : midPos j s + 1 = m + 1 := by rw [midPos_of_not_lt j s h]
  rw [eSum_insertSet_congr (sᵢ s) h1 _ (succ_le_card_appendBlackWeight ν i),
    eSum_insertSet_congr (sᵢ s) h2 _ (succ_le_card_appendBlackWeight ν i),
    eSum_insertSet_congr (sᵢ s) (midPos_of_not_lt j s h) _ (le_card_appendBlackWeight ν i)]
  simp only [midPos_of_not_lt j s h]
  rw [← underRight_mul_eSum Q Λ Λc (sᵢ s) (succ_le_card_appendBlackWeight ν i),
    mul_assoc (underRight N m), (KLRAlgebra.eSum_idem _).eq, ← mul_assoc,
    ← underRight_mul_eSum Q Λ Λc (sᵢ s) (succ_le_card_appendBlackWeight ν i), mul_assoc,
    (KLRAlgebra.eSum_idem _).eq]

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

theorem posModelCongr_tmul {μ : Multiset I} (s : Seq (stendhalWeight ℓ μ)) {n n' : ℕ}
    (hn : n ≤ Multiset.card (stendhalWeight ℓ μ)) (hn' : n' ≤ Multiset.card (stendhalWeight ℓ μ))
    (h : n = n') (z : Corner (posOp j hj Q Λ Λc ν₀ s n hn)) (v : L) :
    posModelCongr j hj Q Λ Λc ν₀ L s hn hn' h (Ind.tmul z v) =
      Ind.tmul ⟨z.1, by subst h; exact z.2⟩ v := by
  subst h; rfl

variable (L) in
theorem appendFixedIncl_eq_sum
    (f : (s : Seq (stendhalWeight ℓ ν)) →
      PosModel j hj Q Λ Λc ν₀ (sᵢ s) (midPos j (sᵢ s)) (midPos_le j _) L) :
    appendFixedIncl (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν := ν) (ν₀ := ν₀) i L f =
      ∑ s, natMap (intertwines_of_orthogonal_incl midOp_eq_sum_posOp
        (fun _ _ a a' h => posOp_mul_posOp_of_ne h a a') (sᵢ s)) (f s) := by
  rw [← (midModelPiEquiv j hj Q Λ Λc νᵢ ν₀ L).symm_apply_apply (appendFixedIncl i L f),
    midModelPiEquiv_appendFixedIncl, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  change ∑ u, natMap (intertwines_of_orthogonal_incl midOp_eq_sum_posOp
    (fun _ _ a a' h => posOp_mul_posOp_of_ne h a a') u)
    (Pi.single (M := fun t : Seq (stendhalWeight ℓ νᵢ) =>
      PosModel j hj Q Λ Λc ν₀ t (midPos j t) (midPos_le j t) L) (sᵢ s) (f s) u) = _
  rw [Finset.sum_eq_single (sᵢ s) (fun u _ hu => by rw [Pi.single_eq_of_ne hu, map_zero])
    (fun h' => absurd (Finset.mem_univ _) h'), Pi.single_eq_same]

variable (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

/-- **The identification of `𝔉_i(model_ν)` with `e' · model_{{i} + ν}` on generators**, for
`j = ℓ`: `z ⊗ v ↦ z D ⊗ v`, where `D` passes the appended strand under the window. -/
theorem appendFixedEquiv_appendTopPiEquiv_tmul (h : ¬ j < ℓ) (z : Corner ψA) (v : L) :
    (appendFixedEquiv i L (appendTopPiEquiv L i hP hPL hL h hκ (Ind.tmul z v)) :
        MidModel j hj Q Λ Λc νᵢ ν₀ L) =
      Ind.tmul (cornerMulOf (topPassOp_mul_midOp_one ν i h) z) v := by
  rw [appendFixedEquiv_apply, appendFixedIncl_eq_sum]
  simp only [appendTopPiEquiv, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply,
    appendPosPiEquiv_tmul, appendTopPassEquiv, posPassRightEquiv, LinearEquiv.ofBijective_apply,
    posPassRight, natMapOn_tmul, posModelCongr_tmul, natMap_tmul]
  rw [← Ind.sum_tmul]
  congr 1
  apply Subtype.ext
  rw [Submodule.coe_sum]
  change ∑ s, z.1 *
      posOp j hj Q Λ Λc ν₀ (sᵢ s) (midPos j s) (midPos_le_appendBlackLoading j ν i s) 1 *
      posPassRightElt j hj Q Λ Λc ν₀ (sᵢ s) (midPos j s) (midPos_succ_le_of_not_lt ν i h s) *
      posOp j hj Q Λ Λc ν₀ (sᵢ s) (midPos j (sᵢ s)) (midPos_le j _) 1 = z.1 * op (bot' D)
  rw [← sum_posOp_posPassRightElt ν i h, Finset.mul_sum]
  simp only [mul_assoc]

end Model

section Idempotents

local notation "σK" => ∑ u, midIdem j hj Q Λ Λc ν ν₀ u

theorem sum_midIdem_mul_midIdem (t : Seq (stendhalWeight ℓ ν)) :
    σK * midIdem j hj Q Λ Λc ν ν₀ t = midIdem j hj Q Λ Λc ν ν₀ t := by
  rw [Finset.sum_mul]
  simp only [midIdem_mul_midIdem, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem sum_midIdem_mul_self : σK * σK = σK := by
  conv_lhs => rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => sum_midIdem_mul_midIdem ν t

theorem commute_x_sum_midIdem (c : Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) :
    Commute (KLRAlgebra.x c : Rp) σK :=
  Commute.sum_right _ _ _ fun _ _ => commute_x_eSum c _

/-- For a cap at the right end, the crossings `ψ_p` of `λ` commute with `∑_u e_{u, m}`. -/
theorem commute_ψ_sum_midIdem (h : ¬ j < ℓ) {p : ℕ} (hp : p + 1 < m) :
    Commute (KLRAlgebra.ψ p : Rp) σK := by
  have hc : crossPos m N p = p := by
    unfold crossPos
    split_ifs
    · rfl
    · omega
  change KLRAlgebra.ψ p * σK = σK * KLRAlgebra.ψ p
  rw [Finset.mul_sum, Finset.sum_mul]
  have h1 : ∀ u : Seq (stendhalWeight ℓ ν),
      (KLRAlgebra.ψ p : Rp) * midIdem j hj Q Λ Λc ν ν₀ u =
        midIdem j hj Q Λ Λc ν ν₀ (sadj m p • u) * KLRAlgebra.ψ p := fun u => by
    have := ψ_crossPos_mul_eSum (k := k) (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
      (ν₀ := ν₀) u le_rfl (p := p) (Or.inl hp)
    rw [hc] at this
    rw [midIdem_eq_of_not_lt ν h, midIdem_eq_of_not_lt ν h]
    exact this
  simp only [h1]
  exact Equiv.sum_comp (MulAction.toPerm (sadj m p)) fun u =>
    midIdem j hj Q Λ Λc ν ν₀ u * KLRAlgebra.ψ p

theorem sum_midIdem_mul_midDot (h : ¬ j < ℓ) (a : Fin m) :
    σK * midDot j hj Q Λ Λc ν ν₀ a = midDot j hj Q Λ Λc ν ν₀ a := by
  rw [midDot_eq_of_not_lt h, ← mul_assoc, ← (commute_x_sum_midIdem ν _).eq, mul_assoc,
    sum_midIdem_mul_self]

theorem sum_midIdem_mul_midCross (h : ¬ j < ℓ) {p : ℕ} (hp : p + 1 < m) :
    σK * midCross j hj Q Λ Λc ν ν₀ p = midCross j hj Q Λ Λc ν ν₀ p := by
  rw [midCross_eq_of_not_lt h hp, ← mul_assoc, ← (commute_ψ_sum_midIdem ν h hp).eq, mul_assoc,
    sum_midIdem_mul_self]

end Idempotents

local notation "σK'" => ∑ u, midIdem j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ u

theorem sum_midIdem_mul_appendIdemKLR :
    σK' * appendIdemKLR (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ) (Λc := Λc) ν i =
      appendIdemKLR (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ) (Λc := Λc) ν i := by
  rw [appendIdemKLR, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => sum_midIdem_mul_midIdem νᵢ _

/-- **The sandwich**: if `D · appendPlus(Y) = Z · D` and `Z` is cut on the left by the window
idempotents, then `D` carries the action of `Y` above the maximum at `ν` to that of `Z` at
`{i} + ν`. -/
theorem topPass_sandwich (h : ¬ j < ℓ) {Y : Rp} {Z : Rpᵢ} (hYZ : D * Ap Y = Z * D)
    (hσZ : σK' * Z = Z) :
    D * (Ap (∑ u, midIdem j hj Q Λ Λc ν ν₀ u) * Ap Y * Ap (∑ u, midIdem j hj Q Λ Λc ν ν₀ u)) =
      σK' * Z * σK' * D := by
  rw [appendPlus_sum_midIdem ν i h]
  calc D * (eA * Ap Y * eA) = D * eA * Ap Y * eA := by simp only [mul_assoc]
    _ = Z * D := by rw [topPass_mul_topPassIdem, hYZ, mul_assoc, topPass_mul_topPassIdem]
    _ = σK' * Z * σK' * D := by rw [mul_assoc (σK' * Z), sum_midIdem_mul_topPass ν i h, hσZ]

section Left

local notation "bot'" => botMap k Q Λ Λc j hj ((Singleton.singleton i : Multiset I) + ν) ν₀
local notation "Fν" => FreeAlgebra k (Gen (stendhalWeight ℓ ν))
local notation "Fνᵢ" => FreeAlgebra k (Gen (stendhalWeight ℓ ((Singleton.singleton i : Multiset I)
  + ν)))
local notation "AL" => appendLam Q Λ ν i
local notation "mkν" => KLRAlgebra.mk k (stendhalQ Q Λ) (stendhalWeight ℓ ν)
local notation "mkνᵢ" => KLRAlgebra.mk k (stendhalQ Q Λ)
  (stendhalWeight ℓ ((Singleton.singleton i : Multiset I) + ν))

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) (h : ¬ j < ℓ)

local notation "MMᵢ" => MidModel j hj Q Λ Λc ((Singleton.singleton i : Multiset I) + ν) ν₀ L

local notation "Θ" => appendTopModelEquiv (i := i) (ν := ν) hL hP hPL hκ h

/-- **`𝔉_i(model_ν) ≅ e' · model_{{i} + ν}` on generators**, for `j = ℓ`:
`c ⊗ (w ⊗ v) ↦ c · appendPlus(w) · D ⊗ v`. -/
theorem appendTopModelEquiv_tmul_tmul (c : Corner (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i))
    (w : Corner (midOp j hj Q Λ Λc ν ν₀)) (v : L) :
    (Θ (Ind.tmul c (Ind.tmul w v)) : MMᵢ) =
      Ind.tmul (cornerMulOf (topPassOp_mul_midOp_one ν i h)
        (compMul (midOp j hj Q Λ Λc ν ν₀) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i) c w)) v :=
  appendFixedEquiv_appendTopPiEquiv_tmul ν i hP hPL hL hκ h _ v

include hP hPL hκ in
/-- **The identification and the sliding diagrams** (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for `j = ℓ`: if `D · appendPlus(Y) = Z · D` and `Z` is cut on the left by the
window idempotents, the identification carries `𝔉_i` of the action of `Y` to the action of `Z`. -/
theorem appendTopModelEquiv_map_midEnd_of {Y : Rp} (hY : MidSlides j hj Q Λ Λc ν ν₀ Y)
    {Z : Rpᵢ} (hZ : MidSlides j hj Q Λ Λc νᵢ ν₀ Z) (hYZ : D * Ap Y = Z * D)
    (hσZ : σK' * Z = Z)
    (x : Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)) :
    (Θ (Ind.map (midEnd L hL hY) x) : MMᵢ) = midEnd L hL hZ (Θ x) := by
  have key : appendBlackPlusOp Q Λ Λc j hj ν ν₀ i (midElt j hj Q Λ Λc ν ν₀ Y) * op (bot' D) =
      op (bot' D) * midElt j hj Q Λ Λc νᵢ ν₀ Z := by
    apply MulOpposite.unop_injective
    rw [midElt, midElt, appendBlackPlusOp_op, unop_mul, unop_mul, unop_op, unop_op, unop_op,
      midStendhal_one_eq_botMap ν, midStendhal_one_eq_botMap νᵢ, ← map_mul, ← map_mul,
      appendBlackPlus_botMap, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    rw [map_mul (appendPlus Q Λ Λc j hj ν ν₀ i), map_mul (appendPlus Q Λ Λc j hj ν ν₀ i),
      topPass_sandwich ν i h hYZ hσZ]
  induction x using Ind.induction_on with
  | zero => simp only [map_zero, ZeroMemClass.coe_zero]
  | add a b ha hb => simp only [map_add, Submodule.coe_add, ha, hb]
  | tmul c t =>
  induction t using Ind.induction_on with
  | zero => simp only [Ind.tmul_zero, map_zero, ZeroMemClass.coe_zero]
  | add a b ha hb =>
    simp only [Ind.tmul_add, map_add, Submodule.coe_add] at ha hb ⊢
    rw [ha, hb]
  | tmul w v =>
    rw [Ind.map_tmul, midEnd, natMapOn_tmul, appendTopModelEquiv_tmul_tmul ν i hP hPL hκ h,
      appendTopModelEquiv_tmul_tmul ν i hP hPL hκ h, midEnd, natMapOn_tmul]
    congr 1
    apply Subtype.ext
    change c.1 * appendBlackPlusOp Q Λ Λc j hj ν ν₀ i (w.1 * midElt j hj Q Λ Λc ν ν₀ Y) *
        op (bot' D) =
      c.1 * appendBlackPlusOp Q Λ Λc j hj ν ν₀ i w.1 * op (bot' D) *
        midElt j hj Q Λ Λc νᵢ ν₀ Z
    rw [map_mul, mul_assoc, mul_assoc, key, ← mul_assoc, ← mul_assoc]

include hP hPL hκ in
/-- One step of the comparison of the actions of `λ`, for `j = ℓ`. -/
theorem appendTopModelEquiv_step (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL) (a : Fν) (a' : Fνᵢ)
    (happ : AL (mkν a) = mkνᵢ a')
    (hYZ : D * Ap (midFree j hj Q Λ Λc ν ν₀ a).val = (midFree j hj Q Λ Λc νᵢ ν₀ a').val * D)
    (hσZ : σK' * (midFree j hj Q Λ Λc νᵢ ν₀ a').val = (midFree j hj Q Λ Λc νᵢ ν₀ a').val)
    (x : Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)) :
    (Θ (Ind.map (midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ a).2)) x) : MMᵢ) =
      midKLRAct hR' (AL (mkν a)) (Θ x) := by
  rw [happ, midKLRAct_mk, midEndAlg_apply]
  exact appendTopModelEquiv_map_midEnd_of ν i hP hPL hκ h _ _ hYZ hσZ x

include hP hPL hκ in
/-- **The identification intertwines the actions of `λ`** (arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21), for `j = ℓ`, on the free algebra: `𝔉_i` of the action of a word `a` at `ν` is
carried to the action of its appended image `appendLam a` at `{i} + ν`. -/
theorem appendTopModelEquiv_midFree (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL) (a : Fν)
    (x : Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)) :
    (Θ (Ind.map (midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ a).2)) x) : MMᵢ) =
      midKLRAct hR' (AL (mkν a)) (Θ x) := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  induction a using FreeAlgebra.induction generalizing x with
  | grade0 c =>
    have hl : (midFree j hj Q Λ Λc νᵢ ν₀ (algebraMap k Fνᵢ c * appendIdemFree ν i)).val =
        c • appendIdemKLR (hj := hj) (ν₀ := ν₀) (Q := Q) (Λ := Λ) (Λc := Λc) ν i := by
      rw [map_mul, AlgHom.commutes, Subalgebra.coe_mul, Subalgebra.coe_algebraMap,
        midFree_appendIdemFree, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    have hr : (midFree j hj Q Λ Λc ν ν₀ (algebraMap k Fν c)).val = c • (1 : Rp) := by
      rw [AlgHom.commutes, Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one]
    refine appendTopModelEquiv_step ν i hP hPL hκ h hR' _
      (algebraMap k Fνᵢ c * appendIdemFree ν i) ?_ ?_ ?_ x
    · rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul, appendLam_one_eq_mk,
        map_mul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    · rw [hl, hr, map_smul, mul_smul_comm, topPass_mul_appendPlus_one ν i h, smul_mul_assoc,
        appendIdemKLR_mul_topPass ν i h]
    · rw [hl, mul_smul_comm, sum_midIdem_mul_appendIdemKLR]
  | grade1 g =>
    cases g with
    | idem t =>
      refine appendTopModelEquiv_step ν i hP hPL hκ h hR' _ (fe k _ (appendBlackLoading i ν t))
        (appendLam_e t) ?_ ?_ x
      · rw [midFree_fe, midFree_fe]
        exact topPass_mul_appendPlus_midIdem ν i h t
      · rw [midFree_fe]
        exact sum_midIdem_mul_midIdem νᵢ _
    | dot a =>
      refine appendTopModelEquiv_step ν i hP hPL hκ h hR' _
        (fx k _ (appendStrand ν i a) * appendIdemFree ν i) ?_ ?_ ?_ x
      · change AL (KLRAlgebra.x a) = _
        rw [appendLam_x, appendLam_one_eq_mk, map_mul]
        congr 2
      · rw [map_mul, Subalgebra.coe_mul, midFree_fx, midFree_fx, midFree_appendIdemFree]
        exact topPass_mul_appendPlus_midDot ν i h a
      · rw [map_mul, Subalgebra.coe_mul, midFree_fx, midFree_appendIdemFree, ← mul_assoc,
          sum_midIdem_mul_midDot νᵢ h]
    | cross p =>
      by_cases hp : p + 1 < Multiset.card (stendhalWeight ℓ ν)
      · refine appendTopModelEquiv_step ν i hP hPL hκ h hR' _ (fψ k _ p * appendIdemFree ν i)
          ?_ ?_ ?_ x
        · change AL (KLRAlgebra.ψ p) = _
          rw [appendLam_ψ hp, appendLam_one_eq_mk, map_mul]
          rfl
        · rw [map_mul, Subalgebra.coe_mul, midFree_fψ, midFree_fψ, midFree_appendIdemFree]
          exact topPass_mul_appendPlus_midCross ν i h hp
        · rw [map_mul, Subalgebra.coe_mul, midFree_fψ, midFree_appendIdemFree, ← mul_assoc,
            sum_midIdem_mul_midCross νᵢ h (by omega)]
      · refine appendTopModelEquiv_step ν i hP hPL hκ h hR' _ 0 ?_ ?_ ?_ x
        · change AL (KLRAlgebra.ψ p) = _
          rw [KLRAlgebra.ψ_eq_zero p (by omega), map_zero, map_zero]
        · have h0 : midCross j hj Q Λ Λc ν ν₀ p = 0 :=
            Finset.sum_eq_zero fun s _ => by simp [midCrossAt, hp]
          rw [midFree_fψ, h0, map_zero, map_zero, ZeroMemClass.coe_zero, mul_zero, zero_mul]
        · rw [map_zero, ZeroMemClass.coe_zero, mul_zero]
  | mul a b ha hb =>
    have hab : midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ (a * b)).2) =
        (midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ a).2)).comp
          (midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ b).2)) := by
      rw [← midEnd_mul]
      exact midEnd_eq_of_eq hL _ _ (by rw [map_mul, Subalgebra.coe_mul])
    rw [hab, Ind.map_comp, LinearMap.comp_apply, ha, hb, map_mul, map_mul, map_mul,
      Module.End.mul_apply]
  | add a b ha hb =>
    have hab : midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ (a + b)).2) =
        midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ a).2) +
          midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ b).2) := by
      rw [← midEnd_add]
      exact midEnd_eq_of_eq hL _ _ (by rw [map_add, Subalgebra.coe_add])
    rw [hab, ind_map_add, map_add, Submodule.coe_add, ha, hb, map_add, map_add, map_add,
      LinearMap.add_apply]

include hP hPL hκ in
/-- **The identification intertwines the actions of the KLR algebra of `λ`**
(arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for `j = ℓ`. -/
theorem appendTopModelEquiv_midKLRAct (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL)
    (w : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν))
    (x : Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)) :
    (Θ (Ind.map (midKLRActLin ν hL hR w) x) : MMᵢ) = midKLRAct hR' (AL w) (Θ x) := by
  obtain ⟨a, rfl⟩ := KLRAlgebra.mk_surjective w
  have hw : midKLRActLin ν hL hR (mkν a) =
      midEnd L hL (mem_midSlidesSub.1 (midFree j hj Q Λ Λc ν ν₀ a).2) :=
    LinearMap.ext fun y => by
      change midKLRAct hR (mkν a) y = _
      rw [midKLRAct_mk, midEndAlg_apply]
  rw [hw]
  exact appendTopModelEquiv_midFree ν i hP hPL hκ h hR' a x

include hP hPL hκ in
/-- **`𝔉_i(model_ν) ≅ e' · model_{{i} + ν}` intertwines the actions of `T̃^λ`**
(arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for a cap at the right end (`j = ℓ`):
`𝔉_i` of the action of `z ∈ T̃^λ_ν` is carried to the action of `z` with a black strand `i`
appended at the right. -/
theorem appendTopModelEquiv_midLeftAlg (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL) (z : StendhalAlgebra k Q Λ ν)
    (x : Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i)) :
    (Θ (Ind.map (midLeftLin ν hL hR z) x) : MMᵢ) =
      midLeftAlg L hL hR' (appendBlackStendhal Q Λ i ν z) (Θ x) := by
  obtain ⟨w, hw⟩ := StendhalAlgebraAllOrders.ofKLR_surjective (k := k) (Q := Q) (Λ := Λ)
    (ν := ν) z.val
  have hz : midLeftLin ν hL hR z = midKLRActLin ν hL hR w :=
    LinearMap.ext fun y => by
      change allOrdersLift (redRelations_midKLRAct hR) z.val y = _
      rw [← hw, allOrdersLift_ofKLR]
      rfl
  have hz' : midLeftAlg L hL hR' (appendBlackStendhal Q Λ i ν z) = midKLRAct hR' (AL w) := by
    change allOrdersLift (redRelations_midKLRAct hR') (appendBlackStendhal Q Λ i ν z).val = _
    rw [appendBlackStendhal_val, ← hw, appendBlackAllOrders_ofKLR_appendLam, allOrdersLift_ofKLR]
    rfl
  rw [hz, hz']
  exact appendTopModelEquiv_midKLRAct ν i hP hPL hκ h hR hR' w x

end Left

end Categorification.Stendhal.CupCap
