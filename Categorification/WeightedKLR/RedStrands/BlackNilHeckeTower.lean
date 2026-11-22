/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.BlackNilHecke
import Categorification.WeightedKLR.RedStrands.BlackModuleTower
import Categorification.Algebra.ResTowerNilHecke

/-!
# The nil-Hecke action on `Eᵢ` along an `i`-string

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5.1: the
dot on the last black strand and the crossing of the last two black strands, both labelled `i`,
act on the functors `Eᵢ` and `Eᵢ²` on right `T^λ`-modules. This is the action used in
Chuang–Rouquier's definition of an `𝔰𝔩₂`-categorification (arXiv:math/0407205v2, §5.2.1).

In `T^λ` at weight `ν + i`, the dot is `y = x_n · ν_i(1)` (`appendedDot`), and in `T^λ` at
weight `ν + 2i`, the crossing is `τ = -ψ_n · ν_i(ν_i(1))` (`appendedCross`), where `n` is the
number of strands at weight `ν` and `ν_i` is the black-appending map. They commute with the
images of the old diagrams and satisfy the nil-Hecke relations (`appendedDot_commute`,
`appendedCross_sq`, `appendedCross_braid`, `appendedCross_appendedDot`,
`appendedDot_appendedCross`). Restriction along a tower of rings then makes these into a
`NilHeckeData` on the string endofunctor `stringE` (`stringNilHecke`); the sign makes
`τ y' - y τ = 1` the relation of `resTowerNilHecke`.

## Main definitions

* `Stendhal.appendedDot`, `Stendhal.appendedCross`: the dot and the crossing on new strands.
* `Stendhal.stringNilHecke`: the nil-Hecke action on `stringE`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace Categorification.Stendhal

open StendhalAlgebraAllOrders MulOpposite Categorification.Sl2 Categorification.InductionAlong

/-- If `E` is an idempotent in the corner of `e` and `a` commutes with `E`, then `a E` lies in
the corner of `e`. -/
theorem mul_mem_corner_of_commute {R : Type*} [Ring R] {e E a : R} (he : IsIdempotentElem e)
    (hE : E ∈ Subsemigroup.corner e) (hEE : IsIdempotentElem E) (hc : Commute a E) :
    a * E ∈ Subsemigroup.corner e := by
  rw [Subsemigroup.mem_corner_iff he] at hE ⊢
  have h : a * E = E * (a * E) := by rw [← mul_assoc, ← hc.eq, mul_assoc, hEE.eq]
  constructor
  · rw [h, ← mul_assoc, hE.1]
  · rw [mul_assoc, hE.2]

/-- The braid relation for `τ = -a F` and `τ' = -b K` when `K` absorbs `F`. -/
theorem braid_of_absorb {R : Type*} [Ring R] {a b F K : R} (haK : Commute a K)
    (hbK : Commute b K) (hFK : F * K = K) (hKF : K * F = K) (hK : K * K = K)
    (hbr : (b * a * b - a * b * a) * K = 0) :
    -a * F * (-b * K) * (-a * F) = -b * K * (-a * F) * (-b * K) := by
  have hl : a * F * (b * K) = a * b * K := by
    rw [mul_assoc, hbK.eq, ← mul_assoc F, hFK, ← hbK.eq, ← mul_assoc]
  have hr : K * (a * F) = a * K := by
    rw [← mul_assoc, ← haK.eq, mul_assoc, hKF]
  have e1 : a * F * (b * K) * (a * F) = a * b * a * K := by
    calc a * F * (b * K) * (a * F) = a * F * (b * (K * K)) * (a * F) := by rw [hK]
      _ = a * F * (b * K) * (K * (a * F)) := by noncomm_ring
      _ = a * b * (K * a) * K := by rw [hl, hr]; noncomm_ring
      _ = a * b * a * K := by rw [← haK.eq, ← mul_assoc, mul_assoc _ K K, hK]
  have e2 : b * K * (a * F) * (b * K) = b * a * b * K := by
    calc b * K * (a * F) * (b * K) = b * (a * K) * (b * K) := by rw [mul_assoc b K, hr]
      _ = b * a * (K * b) * K := by noncomm_ring
      _ = b * a * b * K := by rw [← hbK.eq, ← mul_assoc, mul_assoc _ K K, hK]
  have h : b * a * b * K = a * b * a * K := by rw [← sub_eq_zero, ← sub_mul, hbr]
  calc -a * F * (-b * K) * (-a * F) = -(a * F * (b * K) * (a * F)) := by noncomm_ring
    _ = -(b * K * (a * F) * (b * K)) := by rw [e1, e2, h]
    _ = -b * K * (-a * F) * (-b * K) := by noncomm_ring

/-- The first mixed nil-Hecke relation, with `τ = -c E` and the new dot `d F`. -/
theorem mixed_left {R : Type*} [Ring R] {c d x E F D : R} (hcE : Commute c E)
    (hdE : Commute d E) (hEF : E * F = E) (hEE : E * E = E) (hD : D = x * E)
    (hrel : (x * c - c * d) * E = E) :
    -c * E * (d * F) - D * (-c * E) = E := by
  subst hD
  calc -c * E * (d * F) - x * E * (-c * E) = -(c * (E * d) * F) + x * (E * c) * E := by
        noncomm_ring
    _ = -(c * d * (E * F)) + x * c * (E * E) := by rw [← hdE.eq, ← hcE.eq]; noncomm_ring
    _ = (x * c - c * d) * E := by rw [hEF, hEE]; noncomm_ring
    _ = E := hrel

/-- The second mixed nil-Hecke relation, with `τ = -c E` and the new dot `d F`. -/
theorem mixed_right {R : Type*} [Ring R] {c d x E F D : R} (hcE : Commute c E)
    (hFE : F * E = E) (hED : E * D = D) (hD : D = x * E)
    (hrel : (c * x - d * c) * E = E) :
    d * F * (-c * E) - -c * E * D = E := by
  calc d * F * (-c * E) - -c * E * D = -(d * (F * (c * E))) + c * (E * D) := by
        noncomm_ring
    _ = -(d * (c * E)) + c * D := by
        rw [hcE.eq, ← mul_assoc F E c, hFE, ← hcE.eq, hED]
    _ = (c * x - d * c) * E := by rw [hD]; noncomm_ring
    _ = E := hrel

variable {I : Type u} {ℓ : ℕ} [DecidableEq I] {k : Type u} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "n" => Multiset.card (stendhalWeight ℓ ν)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "νᵢᵢ" => ((Singleton.singleton i : Multiset I) + νᵢ)
local notation "νᵢᵢᵢ" => ((Singleton.singleton i : Multiset I) + νᵢᵢ)
local notation "G" => appendBlackValue Q Λ i ν
local notation "G'" => appendBlackValue Q Λ i νᵢ
local notation "G''" => appendBlackValue Q Λ i νᵢᵢ
local notation "P" => redOrderedIdem k Q Λ ν
local notation "P'" => redOrderedIdem k Q Λ νᵢ
local notation "π" => TensorProductAlgebra.mk Q Λ ν
local notation "π'" => TensorProductAlgebra.mk Q Λ νᵢ
local notation "π''" => TensorProductAlgebra.mk Q Λ νᵢᵢ
local notation "π'''" => TensorProductAlgebra.mk Q Λ νᵢᵢᵢ

theorem isIdempotentElem_appendBlackValue {μ : Multiset I}
    {z : StendhalAlgebraAllOrders k Q Λ μ} (h : IsIdempotentElem z) :
    IsIdempotentElem (appendBlackValue Q Λ i μ z) := by
  unfold IsIdempotentElem
  rw [← map_mul, h.eq]

theorem appendBlackValue_mem_corner {μ : Multiset I} (z : StendhalAlgebraAllOrders k Q Λ μ)
    (hz : z ∈ Subsemigroup.corner (redOrderedIdem k Q Λ μ)) :
    appendBlackValue Q Λ i μ z ∈
      Subsemigroup.corner (redOrderedIdem k Q Λ ((Singleton.singleton i : Multiset I) + μ)) :=
  (appendBlackStendhal Q Λ i μ ⟨z, hz⟩).2

theorem appendBlack_mk_val {μ : Multiset I} (z : StendhalAlgebraAllOrders k Q Λ μ)
    (hz : z ∈ Subsemigroup.corner (redOrderedIdem k Q Λ μ)) :
    appendBlack Q Λ i μ (TensorProductAlgebra.mk Q Λ μ ⟨z, hz⟩) =
      TensorProductAlgebra.mk Q Λ _ ⟨appendBlackValue Q Λ i μ z,
        appendBlackValue_mem_corner Q Λ i z hz⟩ :=
  rfl

theorem tensorProductAlgebra_mk_mul {μ : Multiset I} {a b : StendhalAlgebraAllOrders k Q Λ μ}
    (ha : a ∈ Subsemigroup.corner (redOrderedIdem k Q Λ μ))
    (hb : b ∈ Subsemigroup.corner (redOrderedIdem k Q Λ μ)) :
    TensorProductAlgebra.mk Q Λ μ ⟨a, ha⟩ * TensorProductAlgebra.mk Q Λ μ ⟨b, hb⟩ =
      TensorProductAlgebra.mk Q Λ μ ⟨a * b, Subsemigroup.mul_mem _ ha hb⟩ := by
  rw [← map_mul]; rfl

theorem tensorProductAlgebra_mk_eq {μ : Multiset I} {a b : StendhalAlgebraAllOrders k Q Λ μ}
    (ha : a ∈ Subsemigroup.corner (redOrderedIdem k Q Λ μ))
    (hb : b ∈ Subsemigroup.corner (redOrderedIdem k Q Λ μ)) (h : a = b) :
    TensorProductAlgebra.mk Q Λ μ ⟨a, ha⟩ = TensorProductAlgebra.mk Q Λ μ ⟨b, hb⟩ := by
  subst h; rfl

theorem tensorProductAlgebra_one (μ : Multiset I) :
    (1 : TensorProductAlgebra k Q Λ μ) =
      TensorProductAlgebra.mk Q Λ μ ⟨redOrderedIdem k Q Λ μ,
        (1 : StendhalAlgebra k Q Λ μ).2⟩ :=
  (map_one _).symm

section Elements

theorem isIdempotentElem_E1 : IsIdempotentElem (G P) :=
  isIdempotentElem_appendBlackValue Q Λ i isIdempotentElem_redOrderedIdem

theorem E1_mem : G P ∈ Subsemigroup.corner P' := appendBlackValue_ordered Q Λ i ν

theorem isIdempotentElem_E2 : IsIdempotentElem (G' (G P)) :=
  isIdempotentElem_appendBlackValue Q Λ i (isIdempotentElem_E1 Q Λ i ν)

theorem E2_mem : G' (G P) ∈ Subsemigroup.corner (redOrderedIdem k Q Λ νᵢᵢ) :=
  appendBlackValue_mem_corner Q Λ i _ (E1_mem Q Λ i ν)

theorem newDot_mul_E1_mem : newDot Q Λ i ν * G P ∈ Subsemigroup.corner P' :=
  mul_mem_corner_of_commute isIdempotentElem_redOrderedIdem (E1_mem Q Λ i ν)
    (isIdempotentElem_E1 Q Λ i ν) (newDot_commute Q Λ i ν P)

theorem negCross_mul_E2_mem :
    -newCross Q Λ i ν * G' (G P) ∈ Subsemigroup.corner (redOrderedIdem k Q Λ νᵢᵢ) :=
  mul_mem_corner_of_commute isIdempotentElem_redOrderedIdem (E2_mem Q Λ i ν)
    (isIdempotentElem_E2 Q Λ i ν) (newCross_commute Q Λ i ν P).neg_left

/-- The dot on the newly appended black strand, `x_n · ν_i(1)` in `T^λ` at weight `ν + i`
(arXiv:1309.3796v2, §5.1). -/
def appendedDot : TensorProductAlgebra k Q Λ νᵢ :=
  π' ⟨newDot Q Λ i ν * G P, newDot_mul_E1_mem Q Λ i ν⟩

/-- Minus the crossing of the two newly appended black strands, `-ψ_n · ν_i(ν_i(1))` in `T^λ`
at weight `ν + 2i` (arXiv:1309.3796v2, §5.1). -/
def appendedCross : TensorProductAlgebra k Q Λ νᵢᵢ :=
  π'' ⟨-newCross Q Λ i ν * G' (G P), negCross_mul_E2_mem Q Λ i ν⟩

end Elements

section Relations

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

theorem corner_left {μ : Multiset I} {z : StendhalAlgebraAllOrders k Q Λ μ}
    (hz : z ∈ Subsemigroup.corner (redOrderedIdem k Q Λ μ)) :
    redOrderedIdem k Q Λ μ * z = z :=
  ((Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem).1 hz).1

theorem corner_right {μ : Multiset I} {z : StendhalAlgebraAllOrders k Q Λ μ}
    (hz : z ∈ Subsemigroup.corner (redOrderedIdem k Q Λ μ)) :
    z * redOrderedIdem k Q Λ μ = z :=
  ((Subsemigroup.mem_corner_iff isIdempotentElem_redOrderedIdem).1 hz).2

/-- The new dot commutes with the image of every element of `T^λ_ν`. -/
theorem appendedDot_commute (a : TensorProductAlgebra k Q Λ ν) :
    appendBlack Q Λ i ν a * appendedDot Q Λ i ν = appendedDot Q Λ i ν * appendBlack Q Λ i ν a := by
  obtain ⟨⟨z, hz⟩, rfl⟩ : ∃ w, π w = a := RingCon.mkₐ_surjective _ a
  rw [appendBlack_mk_val, appendedDot, tensorProductAlgebra_mk_mul,
    tensorProductAlgebra_mk_mul]
  refine tensorProductAlgebra_mk_eq Q Λ _ _ ?_
  rw [← mul_assoc, ← (newDot_commute Q Λ i ν z).eq, mul_assoc, mul_assoc, ← map_mul, ← map_mul,
    corner_left Q Λ hz, corner_right Q Λ hz]

/-- The new crossing fixes the image of the unit on the right. -/
theorem appendedCross_mul_one :
    appendedCross Q Λ i ν * appendBlack Q Λ i νᵢ 1 = appendedCross Q Λ i ν := by
  rw [tensorProductAlgebra_one, appendBlack_mk_val, appendedCross, tensorProductAlgebra_mk_mul]
  refine tensorProductAlgebra_mk_eq Q Λ _ _ ?_
  rw [mul_assoc, ← map_mul]
  congr 2
  exact corner_right Q Λ (E1_mem Q Λ i ν)

/-- The new crossing commutes with the image of every element of `T^λ_ν`. -/
theorem appendedCross_commute (a : TensorProductAlgebra k Q Λ ν) :
    appendedCross Q Λ i ν * appendBlack Q Λ i νᵢ (appendBlack Q Λ i ν a) =
      appendBlack Q Λ i νᵢ (appendBlack Q Λ i ν a) * appendedCross Q Λ i ν := by
  obtain ⟨⟨z, hz⟩, rfl⟩ : ∃ w, π w = a := RingCon.mkₐ_surjective _ a
  rw [appendBlack_mk_val, appendBlack_mk_val, appendedCross, tensorProductAlgebra_mk_mul,
    tensorProductAlgebra_mk_mul]
  refine tensorProductAlgebra_mk_eq Q Λ _ _ ?_
  rw [mul_assoc, ← map_mul, ← map_mul, corner_left Q Λ hz, ← mul_assoc,
    ← (newCross_commute Q Λ i ν z).neg_left.eq, mul_assoc, ← map_mul, ← map_mul,
    corner_right Q Λ hz]

/-- The new crossing squares to zero. -/
theorem appendedCross_sq : appendedCross Q Λ i ν * appendedCross Q Λ i ν = 0 := by
  rw [appendedCross, tensorProductAlgebra_mk_mul, ← map_zero π'']
  refine tensorProductAlgebra_mk_eq Q Λ _ (0 : StendhalAlgebra k Q Λ νᵢᵢ).2 ?_
  simp only [neg_mul, mul_neg, neg_neg]
  rw [mul_assoc, ← mul_assoc (G' (G P)),
    ← (newCross_commute Q Λ i ν P).eq, mul_assoc, (isIdempotentElem_E2 Q Λ i ν).eq,
    ← mul_assoc]
  exact newCross_sq Q Λ i ν P

theorem tensorProductAlgebra_mk_sub {μ : Multiset I} {a b : StendhalAlgebraAllOrders k Q Λ μ}
    (ha : a ∈ Subsemigroup.corner (redOrderedIdem k Q Λ μ))
    (hb : b ∈ Subsemigroup.corner (redOrderedIdem k Q Λ μ)) :
    TensorProductAlgebra.mk Q Λ μ ⟨a, ha⟩ - TensorProductAlgebra.mk Q Λ μ ⟨b, hb⟩ =
      TensorProductAlgebra.mk Q Λ μ ((⟨a, ha⟩ - ⟨b, hb⟩ : StendhalAlgebra k Q Λ μ)) :=
  (map_sub _ _ _).symm

theorem newCross_addBlack :
    newCross Q Λ i νᵢ = (ψ (n + 1) : StendhalAlgebraAllOrders k Q Λ νᵢᵢᵢ) := by
  unfold newCross; rw [card_stendhalWeight_addBlack]

theorem newDot_addBlack :
    newDot Q Λ i νᵢ = (x ⟨n + 1, by
      rw [card_stendhalWeight_addBlack, card_stendhalWeight_addBlack]; omega⟩ :
        StendhalAlgebraAllOrders k Q Λ νᵢᵢ) := by
  unfold newDot; congr 1; ext; exact card_stendhalWeight_addBlack i ν

theorem appendBlackValue_newDot_mul :
    G' (newDot Q Λ i ν * G P) = x ⟨n, by
      rw [card_stendhalWeight_addBlack, card_stendhalWeight_addBlack]; omega⟩ * G' (G P) := by
  rw [map_mul, newDot, appendBlackValue_x, mul_assoc, appendBlackValue_one_mul]

/-- The braid relation for the crossings of the new strands. -/
theorem appendedCross_braid :
    appendedCross Q Λ i νᵢ * appendBlack Q Λ i νᵢᵢ (appendedCross Q Λ i ν) *
        appendedCross Q Λ i νᵢ =
      appendBlack Q Λ i νᵢᵢ (appendedCross Q Λ i ν) * appendedCross Q Λ i νᵢ *
        appendBlack Q Λ i νᵢᵢ (appendedCross Q Λ i ν) := by
  have h1 := card_stendhalWeight_addBlack (ℓ := ℓ) i ν
  have h2 := card_stendhalWeight_addBlack (ℓ := ℓ) i νᵢ
  have h3 := card_stendhalWeight_addBlack (ℓ := ℓ) i νᵢᵢ
  simp only [appendedCross, appendBlack_mk_val, tensorProductAlgebra_mk_mul]
  refine tensorProductAlgebra_mk_eq Q Λ _ _ ?_
  have hB : G'' (-newCross Q Λ i ν * G' (G P)) = -ψ n * G'' (G' (G P)) := by
    rw [map_mul, map_neg, newCross, appendBlackValue_ψ Q Λ i νᵢᵢ n (by omega), neg_mul,
      neg_mul, mul_assoc, appendBlackValue_one_mul]
  rw [hB, newCross_addBlack]
  have hE := isIdempotentElem_E2 Q Λ i ν
  refine braid_of_absorb (newCross_commute_three Q Λ i ν P (n + 1) (by omega) le_rfl)
    (newCross_commute_three Q Λ i ν P n le_rfl (by omega)) ?_ ?_
    (isIdempotentElem_appendBlackValue Q Λ i hE).eq ?_
  · rw [← map_mul, ← map_mul, corner_left Q Λ (E1_mem Q Λ i ν)]
  · rw [← map_mul, ← map_mul, corner_right Q Λ (E1_mem Q Λ i ν)]
  · have := newCross_braid Q Λ i ν P
    rw [← this]

/-- The relation `τ y' - y τ = 1` on `ν_i(ν_i(1))`. -/
theorem appendedCross_appendedDot :
    appendedCross Q Λ i ν * appendedDot Q Λ i νᵢ -
        appendBlack Q Λ i νᵢ (appendedDot Q Λ i ν) * appendedCross Q Λ i ν =
      appendBlack Q Λ i νᵢ (appendBlack Q Λ i ν 1) := by
  rw [tensorProductAlgebra_one]
  simp only [appendedCross, appendedDot, appendBlack_mk_val, tensorProductAlgebra_mk_mul,
    tensorProductAlgebra_mk_sub]
  refine tensorProductAlgebra_mk_eq Q Λ _ _ ?_
  refine mixed_left (newCross_commute Q Λ i ν P) (newDot_commute Q Λ i νᵢ (G P)) ?_
    (isIdempotentElem_E2 Q Λ i ν).eq (appendBlackValue_newDot_mul Q Λ i ν) ?_
  · rw [← map_mul, corner_right Q Λ (E1_mem Q Λ i ν)]
  · rw [newDot_addBlack]; exact newDot_newCross_left Q Λ i ν P

/-- The relation `y' τ - τ y = 1` on `ν_i(ν_i(1))`. -/
theorem appendedDot_appendedCross :
    appendedDot Q Λ i νᵢ * appendedCross Q Λ i ν -
        appendedCross Q Λ i ν * appendBlack Q Λ i νᵢ (appendedDot Q Λ i ν) =
      appendBlack Q Λ i νᵢ (appendBlack Q Λ i ν 1) := by
  rw [tensorProductAlgebra_one]
  simp only [appendedCross, appendedDot, appendBlack_mk_val, tensorProductAlgebra_mk_mul,
    tensorProductAlgebra_mk_sub]
  refine tensorProductAlgebra_mk_eq Q Λ _ _ ?_
  refine mixed_right (newCross_commute Q Λ i ν P) ?_ ?_ (appendBlackValue_newDot_mul Q Λ i ν) ?_
  · rw [← map_mul, corner_left Q Λ (E1_mem Q Λ i ν)]
  · rw [← map_mul, ← mul_assoc, ← (newDot_commute Q Λ i ν P).eq, mul_assoc,
      (isIdempotentElem_E1 Q Λ i ν).eq]
  · rw [newDot_addBlack]; exact newDot_newCross_right Q Λ i ν P

/-! ### The relations in the opposite rings, as used by `resTowerNilHecke` -/

theorem op_appendedDot_commute (a : (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ) :
    op (appendedDot Q Λ i ν) * appendBlackOp Q Λ i ν a =
      appendBlackOp Q Λ i ν a * op (appendedDot Q Λ i ν) := by
  induction a using MulOpposite.rec' with | _ a => ?_
  rw [appendBlackOp_op, ← op_mul, ← op_mul, appendedDot_commute]

theorem op_appendedCross_fix :
    appendBlackOp Q Λ i νᵢ 1 * op (appendedCross Q Λ i ν) = op (appendedCross Q Λ i ν) := by
  rw [← op_one, appendBlackOp_op, ← op_mul, appendedCross_mul_one]

theorem op_appendedCross_commute (a : (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ) :
    op (appendedCross Q Λ i ν) * appendBlackOp Q Λ i νᵢ (appendBlackOp Q Λ i ν a) =
      appendBlackOp Q Λ i νᵢ (appendBlackOp Q Λ i ν a) * op (appendedCross Q Λ i ν) := by
  induction a using MulOpposite.rec' with | _ a => ?_
  rw [appendBlackOp_op, appendBlackOp_op, ← op_mul, ← op_mul, appendedCross_commute]

theorem op_appendedCross_sq :
    op (appendedCross Q Λ i ν) * op (appendedCross Q Λ i ν) = 0 := by
  rw [← op_mul, appendedCross_sq, op_zero]

theorem op_appendedCross_braid :
    op (appendedCross Q Λ i νᵢ) * appendBlackOp Q Λ i νᵢᵢ (op (appendedCross Q Λ i ν)) *
        op (appendedCross Q Λ i νᵢ) =
      appendBlackOp Q Λ i νᵢᵢ (op (appendedCross Q Λ i ν)) * op (appendedCross Q Λ i νᵢ) *
        appendBlackOp Q Λ i νᵢᵢ (op (appendedCross Q Λ i ν)) := by
  rw [appendBlackOp_op, ← op_mul, ← op_mul, ← op_mul, ← op_mul, ← mul_assoc, ← mul_assoc,
    appendedCross_braid]

theorem op_appendedCross_appendedDot :
    op (appendedDot Q Λ i νᵢ) * op (appendedCross Q Λ i ν) -
        op (appendedCross Q Λ i ν) * appendBlackOp Q Λ i νᵢ (op (appendedDot Q Λ i ν)) =
      appendBlackOp Q Λ i νᵢ (appendBlackOp Q Λ i ν 1) := by
  rw [← op_one, appendBlackOp_op, appendBlackOp_op, appendBlackOp_op, ← op_mul, ← op_mul,
    ← op_sub, appendedCross_appendedDot]

theorem op_appendedDot_appendedCross :
    op (appendedCross Q Λ i ν) * op (appendedDot Q Λ i νᵢ) -
        appendBlackOp Q Λ i νᵢ (op (appendedDot Q Λ i ν)) * op (appendedCross Q Λ i ν) =
      appendBlackOp Q Λ i νᵢ (appendBlackOp Q Λ i ν 1) := by
  rw [← op_one, appendBlackOp_op, appendBlackOp_op, appendBlackOp_op, ← op_mul, ← op_mul,
    ← op_sub, appendedDot_appendedCross]

end Relations

section Tower

variable (ν₀ : Multiset I)

/-- **The nil-Hecke action on `Eᵢ` along an `i`-string** (arXiv:1309.3796v2, §5.1; the data of
Chuang–Rouquier's `𝔰𝔩₂`-categorification, arXiv:math/0407205v2, §5.2.1): the dot on the last
black strand acts on `Eᵢ`, and minus the crossing of the last two black strands on `Eᵢ²`. -/
def stringNilHecke : NilHeckeData (stringE Q Λ i ν₀) :=
  resTowerNilHecke (fun m => appendBlackOp Q Λ i (stringWeight i ν₀ m))
    (fun m => op (appendedDot Q Λ i (stringWeight i ν₀ m)))
    (fun _ a => op_appendedDot_commute Q Λ i _ a)
    (fun m => op (appendedCross Q Λ i (stringWeight i ν₀ m)))
    (fun _ => op_appendedCross_fix Q Λ i _)
    (fun _ a => op_appendedCross_commute Q Λ i _ a)
    (fun _ => op_appendedCross_sq Q Λ i _)
    (fun _ => op_appendedCross_braid Q Λ i _)
    (fun _ => op_appendedCross_appendedDot Q Λ i _)
    (fun _ => op_appendedDot_appendedCross Q Λ i _)

end Tower

end Categorification.Stendhal
