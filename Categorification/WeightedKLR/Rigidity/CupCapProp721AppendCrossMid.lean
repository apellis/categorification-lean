/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendDotMidCap

/-!
# The crossing of the two appended strands, for a cap left of the right end

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔈_i² ≅ 𝔈_i² ∘ K` with the crossing, for `j < ℓ`.

The model map `ι₂ ∘ ι₁` sends `w ⊗ v` to `appendBlack(appendBlack(σ(1) w)) ⊗ v`
(`CupCap.appendBlackPlus_two`), and the crossing `Y` of the last two strands of `λ⁺` commutes
with every doubly appended diagram (`CupCap.commute_lastCrossPlus_appendBlackPlus_two`). On the
doubly appended loadings the window lies to the left of the last two strands, so the crossing
of the last two strands of `λ` acts as `Y` (`CupCap.midCross_mul_midIdem_append_two`).

## Main results

* `CupCap.negCrossStendhal_eq_mul`, `CupCap.commute_newCross_appendBlackStendhal_two`.
* `CupCap.lastCrossPlus_eq`, `CupCap.commute_lastCrossPlus_appendBlackPlus_two`.
* `CupCap.midCross_mul_midIdem_append_two`, `CupCap.appendIota_two_appendedCross`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Generic

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {n : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin n → I →₀ ℕ) (i : I) (μ : Multiset I)

local notation "μᵢ" => ((Singleton.singleton i : Multiset I) + μ)
local notation "μᵢᵢ" => ((Singleton.singleton i : Multiset I) + μᵢ)

/-- Minus the crossing of the two appended strands times their unit, as an element of `T̃^λ`:
the projection of minus the crossing times the image of the unit. -/
theorem negCrossStendhal_eq_mul :
    (⟨-StendhalAlgebraAllOrders.newCross Q Λ' i μ *
        appendBlackValue Q Λ' i μᵢ (appendBlackValue Q Λ' i μ
          (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ' μ)),
      negCross_mul_E2_mem Q Λ' i μ⟩ : StendhalAlgebra k Q Λ' μᵢᵢ) =
      orderProjection Q Λ' μᵢᵢ (-StendhalAlgebraAllOrders.newCross Q Λ' i μ) *
        appendBlackStendhal Q Λ' i μᵢ (appendBlackStendhal Q Λ' i μ 1) := by
  apply Subtype.ext
  have hE := (Subsemigroup.mem_corner_iff
    StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).mp (E2_mem Q Λ' i μ)
  change _ = -StendhalAlgebraAllOrders.newCross Q Λ' i μ * _ *
    appendBlackValue Q Λ' i μᵢ (appendBlackValue Q Λ' i μ _)
  rw [mul_assoc]
  erw [hE.1]

/-- In `T̃^λ`, the crossing of the two appended strands commutes with every diagram with two
black strands appended. -/
theorem commute_newCross_appendBlackStendhal_two (W : StendhalAlgebra k Q Λ' μ) :
    Commute (orderProjection Q Λ' μᵢᵢ (StendhalAlgebraAllOrders.newCross Q Λ' i μ))
      (appendBlackStendhal Q Λ' i μᵢ (appendBlackStendhal Q Λ' i μ W)) := by
  apply Subtype.ext
  have hc := (StendhalAlgebraAllOrders.newCross_commute Q Λ' i μ W.val).eq
  have hP := (redOrderedIdem_commute Q Λ' μᵢᵢ (StendhalAlgebraAllOrders.newCross Q Λ' i μ)).eq
  have hl := KLR.Corner.E_mul_val (appendBlackStendhal Q Λ' i μᵢ (appendBlackStendhal Q Λ' i μ W))
  have hr := KLR.Corner.val_mul_E (appendBlackStendhal Q Λ' i μᵢ (appendBlackStendhal Q Λ' i μ W))
  change StendhalAlgebraAllOrders.newCross Q Λ' i μ * _ *
      (appendBlackStendhal Q Λ' i μᵢ (appendBlackStendhal Q Λ' i μ W)).val =
    (appendBlackStendhal Q Λ' i μᵢ (appendBlackStendhal Q Λ' i μ W)).val *
      (StendhalAlgebraAllOrders.newCross Q Λ' i μ * _)
  rw [mul_assoc, hl, ← hP, ← mul_assoc, hr]
  exact hc

end Generic

section Sadj

variable {J : Type} {μ : Multiset J}

/-- An adjacent swap of two positions with the same label fixes the sequence. -/
theorem sadj_smul_eq_self_of_lbl {p : ℕ} (hp : p + 1 < Multiset.card μ) {s : Seq μ}
    (hs : s.1 ⟨p, by omega⟩ = s.1 ⟨p + 1, hp⟩) : TypeA.sadj (Multiset.card μ) p • s = s := by
  apply Subtype.ext
  funext a
  rw [Seq.smul_apply]
  change s.1 ((TypeA.sadj _ p)⁻¹ a) = s.1 a
  rw [TypeA.sadj_inv]
  by_cases ha : a.val = p
  · have : a = ⟨p, by omega⟩ := Fin.ext ha
    rw [this, TypeA.sadj_apply_left hp]
    exact hs.symm
  · by_cases hb : a.val = p + 1
    · have : a = ⟨p + 1, hp⟩ := Fin.ext hb
      rw [this, TypeA.sadj_apply_right hp]
      exact hs
    · rw [TypeA.sadj_apply_of_ne a ha hb]

end Sadj

section Plus

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "ρ" => stendhalWeight (ℓ + 2) (ν + ν₀)
local notation "Λ⁺" => plusLabels Λ Λc j hj

theorem castPlusStendhal_trans {n : ℕ} {Λ' : Fin n → I →₀ ℕ} {μ μ' μ'' : Multiset I}
    (h : μ = μ') (h' : μ' = μ'') (z : StendhalAlgebra k Q Λ' μ) :
    castPlusStendhal Q Λ' h' (castPlusStendhal Q Λ' h z) = castPlusStendhal Q Λ' (h.trans h') z :=
  by subst h h'; rfl

theorem appendBlackStendhal_castPlusStendhal {n : ℕ} {Λ' : Fin n → I →₀ ℕ} {μ μ' : Multiset I}
    (h : μ = μ') (z : StendhalAlgebra k Q Λ' μ) :
    appendBlackStendhal Q Λ' i μ' (castPlusStendhal Q Λ' h z) =
      castPlusStendhal Q Λ' (congrArg (Singleton.singleton i + ·) h)
        (appendBlackStendhal Q Λ' i μ z) := by
  subst h; rfl

omit [DecidableEq I] in
theorem plusWeight_assoc_two :
    (Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + (ν + ν₀)) =
      νᵢᵢ + ν₀ :=
  (congrArg (Singleton.singleton i + ·) (plusWeight_assoc ν ν₀ i)).trans
    (plusWeight_assoc νᵢ ν₀ i)

/-- Appending two strands in `T̃^{λ⁺}` is appending them in `T̃^{λ⁺}_{ν + ν₀}`, then casting. -/
theorem appendBlackPlus_two (W : StendhalAlgebra k Q Λ⁺ (ν + ν₀)) :
    appendBlackPlus Q Λ Λc j hj νᵢ ν₀ i (appendBlackPlus Q Λ Λc j hj ν ν₀ i W) =
      castPlusStendhal Q Λ⁺ (plusWeight_assoc_two ν i)
        (appendBlackStendhal Q Λ⁺ i _ (appendBlackStendhal Q Λ⁺ i (ν + ν₀) W)) := by
  change castPlusStendhal Q Λ⁺ (plusWeight_assoc νᵢ ν₀ i) (appendBlackStendhal Q Λ⁺ i (νᵢ + ν₀)
    (castPlusStendhal Q Λ⁺ (plusWeight_assoc ν ν₀ i) (appendBlackStendhal Q Λ⁺ i (ν + ν₀) W))) = _
  rw [appendBlackStendhal_castPlusStendhal, castPlusStendhal_trans]

variable (k Q Λ Λc j hj ν₀) in
/-- The crossing `Y` of the last two strands of `λ⁺` in `T̃^{λ⁺}` at `({i} + ({i} + ν)) + ν₀`. -/
def lastCrossPlus : StendhalAlgebra k Q Λ⁺ (νᵢᵢ + ν₀) :=
  botMap k Q Λ Λc j hj νᵢᵢ ν₀ (KLRAlgebra.ψ (Multiset.card ρ))

/-- `Y` is the crossing of the two appended strands of `T̃^{λ⁺}`, cast. -/
theorem lastCrossPlus_eq :
    lastCrossPlus k Q Λ Λc j hj ν ν₀ i =
      castPlusStendhal Q Λ⁺ (plusWeight_assoc_two ν i)
        (orderProjection Q Λ⁺ _ (StendhalAlgebraAllOrders.newCross Q Λ⁺ i (ν + ν₀))) := by
  change _ = castPlusStendhal Q Λ⁺ (plusWeight_assoc_two ν i)
    (orderProjection Q Λ⁺ _ (StendhalAlgebraAllOrders.ofKLR k Q _ _ (KLRAlgebra.ψ _)))
  rw [castPlusStendhal_orderProjection, KLRAlgebra.castKLR_ψ]
  rfl

/-- **`Y` commutes with every diagram with two black strands appended.** -/
theorem commute_lastCrossPlus_appendBlackPlus_two (W : StendhalAlgebra k Q Λ⁺ (ν + ν₀)) :
    Commute (lastCrossPlus k Q Λ Λc j hj ν ν₀ i)
      (appendBlackPlus Q Λ Λc j hj νᵢ ν₀ i (appendBlackPlus Q Λ Λc j hj ν ν₀ i W)) := by
  rw [lastCrossPlus_eq, appendBlackPlus_two]
  exact (commute_newCross_appendBlackStendhal_two Q Λ⁺ i _ W).map _

/-- **The crossing of the last two strands of `λ` on a doubly appended loading**, for
`j < ℓ`: the window lies to the left, so it is the crossing `ψ` of the last two strands of `λ⁺`,
and it fixes the loading. -/
theorem midCross_mul_midIdem_append_two (h : j < ℓ) (s : Seq (stendhalWeight ℓ ν)) :
    midCross j hj Q Λ Λc νᵢᵢ ν₀ m *
        midIdem j hj Q Λ Λc νᵢᵢ ν₀ (appendBlackLoading i νᵢ (appendBlackLoading i ν s)) =
      midIdem j hj Q Λ Λc νᵢᵢ ν₀ (appendBlackLoading i νᵢ (appendBlackLoading i ν s)) *
        KLRAlgebra.ψ (Multiset.card ρ) := by
  set t := appendBlackLoading i νᵢ (appendBlackLoading i ν s) with ht
  have h1 := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have h2 := card_appendBlackWeight (ℓ := ℓ) (ν := νᵢ) (i := i)
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hpos : midPos j t = midPos j s := by
    rw [ht, midPos_appendBlackLoading j νᵢ i h, midPos_appendBlackLoading j ν i h]
  have hlt := midPos_lt (j := j) (s := s) h
  have hfix : TypeA.sadj (Multiset.card (stendhalWeight ℓ νᵢᵢ)) m • t = t := by
    have ha : t.lbl ⟨m, by omega⟩ = .inl i := by
      rw [ht, appendBlackLoading_lbl_of_lt i νᵢ _ _ (by dsimp only; omega)]
      exact appendBlackLoading_lbl_of_eq i ν _ _ rfl
    have hb : t.lbl ⟨m + 1, by omega⟩ = .inl i := by
      rw [ht]
      exact appendBlackLoading_lbl_of_eq i νᵢ _ _ (by dsimp only; omega)
    exact sadj_smul_eq_self_of_lbl (by omega) (ha.trans hb.symm)
  have key := ψ_crossPos_mul_eSum (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀)
    t (midPos_le j t) (p := m) (Or.inr (by omega))
  rw [hfix] at key
  have hc : crossPos (midPos j t) N m = Multiset.card ρ := by
    unfold crossPos; split_ifs <;> omega
  rw [hc] at key
  rw [midIdem, midCross_mul_eSum]
  unfold midCrossAt
  have e1 : ¬ m + 1 = midPos j t := by omega
  have e2 : ¬ m = midPos j t := by omega
  have e3 : m + 1 < Multiset.card (stendhalWeight ℓ νᵢᵢ) := by omega
  simp only [e1, e2, e3, dite_true, ite_false, hc]
  exact key

local notation "aB₁" => appendBlackPlus Q Λ Λc j hj ν ν₀ i
local notation "aB₂" => appendBlackPlus Q Λ Λc j hj νᵢ ν₀ i
local notation "σ₀" => midStendhal j hj Q Λ Λc ν ν₀
local notation "σ₁" => midStendhal j hj Q Λ Λc νᵢ ν₀
local notation "σ₂" => midStendhal j hj Q Λ Λc νᵢᵢ ν₀
local notation "Y" => lastCrossPlus k Q Λ Λc j hj ν ν₀ i

/-- Appending two strands to the unit of the diagrams at the maximum, for `j < ℓ`. -/
theorem appendBlackPlus_two_midStendhal_one (h : j < ℓ) :
    aB₂ (aB₁ (σ₀ 1)) = botMap k Q Λ Λc j hj νᵢᵢ ν₀ (∑ s : Seq (stendhalWeight ℓ ν),
      midIdem j hj Q Λ Λc νᵢᵢ ν₀ (appendBlackLoading i νᵢ (appendBlackLoading i ν s))) := by
  rw [appendBlackPlus_midStendhal_one ν i h, appendIdemPlus, appendBlackPlus_botMap, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun s _ => appendPlus_midIdem νᵢ i h _)

/-- The crossing of the last two strands of `λ`, on the doubly appended loadings, for `j < ℓ`. -/
theorem botMap_midCross_mul_appendBlackPlus_two (h : j < ℓ) :
    botMap k Q Λ Λc j hj νᵢᵢ ν₀ (midCross j hj Q Λ Λc νᵢᵢ ν₀ m) * aB₂ (aB₁ (σ₀ 1)) =
      aB₂ (aB₁ (σ₀ 1)) * Y := by
  rw [appendBlackPlus_two_midStendhal_one ν i h, ← map_mul, Finset.mul_sum,
    Finset.sum_congr rfl fun s _ => midCross_mul_midIdem_append_two ν i h s, ← Finset.sum_mul,
    map_mul]
  rfl

/-- The unit of the diagrams at the maximum fixes the appended diagrams, for `j < ℓ`. -/
theorem midStendhal_one_mul_appendBlackPlus (h : j < ℓ) (W : StendhalAlgebra k Q Λ⁺ (ν + ν₀)) :
    σ₁ 1 * aB₁ (σ₀ 1 * W) = aB₁ (σ₀ 1 * W) := by
  rw [map_mul, appendBlackPlus_midStendhal_one ν i h, ← mul_assoc,
    midStendhal_one_mul_appendIdemPlus ν i h]

/-- The unit of the diagrams at the maximum fixes the doubly appended diagrams, for `j < ℓ`. -/
theorem midStendhal_one_mul_appendBlackPlus_two (h : j < ℓ) (W : StendhalAlgebra k Q Λ⁺ (ν + ν₀)) :
    σ₂ 1 * aB₂ (aB₁ (σ₀ 1 * W)) = aB₂ (aB₁ (σ₀ 1 * W)) := by
  have e1 : aB₁ (σ₀ 1 * W) = σ₁ 1 * aB₁ (σ₀ 1 * W) := by
    rw [map_mul, appendBlackPlus_midStendhal_one ν i h, ← mul_assoc,
      midStendhal_one_mul_appendIdemPlus ν i h]
  rw [e1, map_mul, appendBlackPlus_midStendhal_one νᵢ i h, ← mul_assoc,
    midStendhal_one_mul_appendIdemPlus νᵢ i h]

end Plus
section Model

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "νᵢᵢ" =>
  ((Singleton.singleton i : Multiset I) + ((Singleton.singleton i : Multiset I) + ν))
local notation "aB₁" => appendBlackPlus Q Λ Λc j hj ν ν₀ i
local notation "aB₂" => appendBlackPlus Q Λ Λc j hj νᵢ ν₀ i
local notation "Y" => lastCrossPlus k Q Λ Λc j hj ν ν₀ i

/-- **Appending two strands carries the crossing of the new strands to the crossing**, for
`j < ℓ` (arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): on the image of `ι₂ ∘ ι₁`, the
left action of minus the crossing of the two appended strands of `T̃^λ` times their unit is the
right action of minus the crossing `Y` of the two appended strands of `T̃^{λ⁺}` times their
unit. -/
theorem appendIota_two_appendedCross (h : j < ℓ) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL) (hR'' : MidKLRRel j hj Q Λ Λc νᵢᵢ ν₀ L hL)
    (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midLeftAlg L hL hR'' (orderProjection Q Λ νᵢᵢ (-StendhalAlgebraAllOrders.newCross Q Λ i ν) *
        appendBlackStendhal Q Λ i νᵢ (appendBlackStendhal Q Λ i ν 1))
        (appendIota νᵢ i L h (appendIota ν i L h y)) =
      op (-(Y * aB₂ (aB₁ 1))) • appendIota νᵢ i L h (appendIota ν i L h y) := by
  rw [map_mul, Module.End.mul_apply, ← appendIota_midLeftAlg νᵢ i h hR' hR'',
    ← appendIota_midLeftAlg ν i h hR hR' 1, map_one, Module.End.one_apply]
  have hY : orderProjection Q Λ νᵢᵢ (-StendhalAlgebraAllOrders.newCross Q Λ i ν) =
      topMap k Q Λ νᵢᵢ (-(KLRAlgebra.ψ (Multiset.card (stendhalWeight ℓ ν)))) := by
    rw [map_neg, map_neg]; rfl
  rw [hY, map_neg, map_neg, midLeftAlg_topMap, LinearMap.neg_apply, midKLRAct_ψ, op_neg, neg_smul,
    neg_inj]
  induction y using Ind.induction_on with
  | zero =>
    have h0 : ∀ μ : Multiset I, appendIota (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc)
        (ν₀ := ν₀) μ i L h 0 = 0 := fun μ => by
      rw [appendIota, Ind.tmul_zero, map_zero]
    rw [h0, h0, map_zero, smul_zero]
  | add a b ha hb => rw [appendIota_add, appendIota_add, map_add, ha, hb, smul_add]
  | tmul w v =>
    rw [appendIota_tmul, appendIota_tmul, midEnd]
    change natMapOn _ (Ind.tmul _ v) = op (Y * aB₂ (aB₁ 1)) • Ind.tmul _ v
    rw [natMapOn_tmul, Ind.smul_tmul]
    congr 1
    apply Subtype.ext
    apply MulOpposite.unop_injective
    change (_ * midElt j hj Q Λ Λc νᵢᵢ ν₀ _).unop = (op (Y * aB₂ (aB₁ 1)) * _).unop
    have hA : ∀ (μ : Multiset I) x, (appendBlackPlusOp Q Λ Λc j hj μ ν₀ i x).unop =
        appendBlackPlus Q Λ Λc j hj μ ν₀ i x.unop := fun _ _ => rfl
    simp only [midElt, unop_mul, unop_op, appendMidOp_apply _ i h, midOp_apply, unop_one,
      cornerMul, compMul, unitGen, hA]
    set w' := w.1.unop
    have hW : appendIdemPlus Q Λ Λc j hj νᵢ ν₀ i * midStendhal j hj Q Λ Λc νᵢᵢ ν₀ 1 *
        (aB₂ (appendIdemPlus Q Λ Λc j hj ν ν₀ i * midStendhal j hj Q Λ Λc νᵢ ν₀ 1 *
          (aB₁ w' * aB₁ 1)) * aB₂ 1) =
        aB₂ (aB₁ (midStendhal j hj Q Λ Λc ν ν₀ 1 * w')) := by
      rw [appendIdemPlus_mul_midStendhal_one νᵢ i h, appendIdemPlus_mul_midStendhal_one ν i h,
        ← appendBlackPlus_midStendhal_one νᵢ i h, ← appendBlackPlus_midStendhal_one ν i h,
        ← map_mul aB₁ w' 1, mul_one, ← map_mul aB₁, ← map_mul aB₂ _ 1, mul_one, ← map_mul aB₂,
        midStendhal_one_mul_appendBlackPlus ν i h]
    rw [hW]
    set W := aB₂ (aB₁ (midStendhal j hj Q Λ Λc ν ν₀ 1 * w')) with hWdef
    have f1 : midStendhal j hj Q Λ Λc νᵢᵢ ν₀ 1 * W = W :=
      midStendhal_one_mul_appendBlackPlus_two ν i h w'
    have f2 : botMap k Q Λ Λc j hj νᵢᵢ ν₀ (midCross j hj Q Λ Λc νᵢᵢ ν₀
        (Multiset.card (stendhalWeight ℓ ν))) * W = W * Y := by
      have e : W = aB₂ (aB₁ (midStendhal j hj Q Λ Λc ν ν₀ 1)) * W := by
        rw [hWdef, ← map_mul, ← map_mul, ← mul_assoc, ← map_mul, one_mul]
      have hc : Y * W = W * Y := by
        rw [hWdef]; exact (commute_lastCrossPlus_appendBlackPlus_two ν i _).eq
      rw [e, ← mul_assoc, botMap_midCross_mul_appendBlackPlus_two ν i h, mul_assoc, hc,
        ← mul_assoc]
    have f3 : W * aB₂ (aB₁ 1) = W := by
      rw [hWdef, ← map_mul, ← map_mul, mul_one]
    rw [mul_assoc _ _ W, f1, mul_assoc, f2, ← mul_assoc, f1,
      (commute_lastCrossPlus_appendBlackPlus_two ν i 1).eq, ← mul_assoc, f3]

end Model

end Categorification.Stendhal.CupCap
