/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedBlackSlide

/-!
# Dots and crossings on the appended black strands

Webster's functor `Eᵢ` (arXiv:1309.3796v2, §4.6) restricts along the map `ν_i` which appends a
black strand coloured `i` on the right. A dot on the new strand and a crossing of the two newest
strands give the nil-Hecke action on `Eᵢ` used to apply Chuang–Rouquier's results
(arXiv:math/0407205v2, §5.2.1) in Webster's §5. This file proves the relations between these
elements in the all-orders Stendhal algebras: they commute with the image of the smaller
algebra, and satisfy the nil-Hecke relations up to the image of the identity.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR

variable {I : Type*} {ℓ : ℕ} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

namespace StendhalAlgebraAllOrders

variable {ν : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "A" => StendhalAlgebraAllOrders k Q Λ ν

theorem x_mul_e (a : Fin m) (s : Seq (stendhalWeight ℓ ν)) : (x a * e s : A) = e s * x a := by
  rw [x, e, ← map_mul, KLRAlgebra.x_mul_e, map_mul]

theorem x_mul_x (a b : Fin m) : (x a * x b : A) = x b * x a := by
  rw [x, x, ← map_mul, KLRAlgebra.x_mul_x, map_mul]

theorem ψ_mul_e_of_lbl_eq {j : ℕ} (h : j + 1 < m) {s : Seq (stendhalWeight ℓ ν)}
    (hs : s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, h⟩) : (ψ j * e s : A) = e s * ψ j := by
  rw [ψ, e, ← map_mul, KLRAlgebra.ψ_mul_e_comm j h hs, map_mul]

theorem dot_cross_left_of_lbl_eq {j : ℕ} (h : j + 1 < m) {s : Seq (stendhalWeight ℓ ν)}
    (hs : s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, h⟩) :
    ((x ⟨j, by omega⟩ * ψ j - ψ j * x ⟨j + 1, h⟩) * e s : A) = e s := by
  have := congrArg (ofKLR k Q Λ ν) (KLRAlgebra.dot_cross_left (Q := stendhalQ Q Λ) j h s)
  simp only [map_mul, map_sub, hs, ↓reduceIte] at this
  exact this

theorem dot_cross_right_of_lbl_eq {j : ℕ} (h : j + 1 < m) {s : Seq (stendhalWeight ℓ ν)}
    (hs : s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, h⟩) :
    ((ψ j * x ⟨j, by omega⟩ - x ⟨j + 1, h⟩ * ψ j) * e s : A) = e s := by
  have := congrArg (ofKLR k Q Λ ν) (KLRAlgebra.dot_cross_right (Q := stendhalQ Q Λ) j h s)
  simp only [map_mul, map_sub, hs, ↓reduceIte] at this
  exact this

theorem ψ_sq_of_lbl_eq {j : ℕ} (h : j + 1 < m) {s : Seq (stendhalWeight ℓ ν)}
    (hs : s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, h⟩) : (ψ j * ψ j * e s : A) = 0 := by
  have := congrArg (ofKLR k Q Λ ν) (KLRAlgebra.ψ_sq (Q := stendhalQ Q Λ) j h s)
  simp only [map_mul, hs, ↓reduceIte, map_zero] at this
  exact this

theorem braid_of_lbl_eq {j : ℕ} (h : j + 2 < m) {s : Seq (stendhalWeight ℓ ν)}
    (hs : s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, by omega⟩) :
    ((ψ j * ψ (j + 1) * ψ j - ψ (j + 1) * ψ j * ψ (j + 1)) * e s : A) = 0 := by
  have := congrArg (ofKLR k Q Λ ν) (KLRAlgebra.braid (Q := stendhalQ Q Λ) j h s)
  simp only [map_mul, map_sub, hs, ne_eq, not_true_eq_false, and_false, ↓reduceIte,
    map_zero] at this
  exact this

/-- An element commuting with the images of all idempotents commutes with the image of `1`. -/
theorem commute_map_one {R : Type*} [Ring R] (f : A →ₙ+* R) (c : R)
    (he : ∀ s, Commute c (f (e s))) : Commute c (f 1) := by
  rw [← sum_e (k := k) (Q := Q) (Λ := Λ) (ν := ν), map_sum]
  exact Commute.sum_right _ _ _ fun s _ => he s

/-- An element commuting with the images of all generators under a coefficient-linear
non-unital ring map commutes with the whole image. -/
theorem commute_of_generators {R : Type*} [Ring R] [Algebra k R] (f : A →ₙ+* R)
    (hf : ∀ (c : k) (z : A), f (c • z) = c • f z) (c : R)
    (he : ∀ s, Commute c (f (e s))) (hx : ∀ a, Commute c (f (x a)))
    (hψ : ∀ j, Commute c (f (ψ j))) (z : A) : Commute c (f z) := by
  have h1 := commute_map_one f c he
  obtain ⟨w, rfl⟩ := ofKLR_surjective z
  obtain ⟨u, rfl⟩ := KLRAlgebra.mk_surjective w
  induction u using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, hf]
    exact h1.smul_right r
  | grade1 g =>
    cases g with
    | idem s => exact he s
    | dot a => exact hx a
    | cross j => exact hψ j
  | add a b ha hb => rw [map_add, map_add, map_add]; exact ha.add_right hb
  | mul a b ha hb => rw [map_mul, map_mul, map_mul]; exact ha.mul_right hb

section BlackStrands

variable (Q Λ) (i : I) (ν : Multiset I)

local notation "n" => Multiset.card (stendhalWeight ℓ ν)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "νᵢᵢ" => ((Singleton.singleton i : Multiset I) + νᵢ)
local notation "νᵢᵢᵢ" => ((Singleton.singleton i : Multiset I) + νᵢᵢ)
local notation "G" => appendBlackValue Q Λ i ν
local notation "G'" => appendBlackValue Q Λ i νᵢ
local notation "G''" => appendBlackValue Q Λ i νᵢᵢ
local notation "L" => appendBlackLoading i ν
local notation "L'" => appendBlackLoading i νᵢ
local notation "L''" => appendBlackLoading i νᵢᵢ

omit [DecidableEq I] in
theorem card_stendhalWeight_addBlack :
    Multiset.card (stendhalWeight ℓ νᵢ) = n + 1 := by
  rw [← stendhalWeight_addBlack i ν, Multiset.card_add, Multiset.card_singleton]

omit [DecidableEq I] in
/-- After appending two black strands, both new positions carry the label `i`. -/
theorem appendBlackLoading_two_lbl (s : Seq (stendhalWeight ℓ ν))
    (a : Fin (Multiset.card (stendhalWeight ℓ νᵢᵢ))) (ha : n ≤ a.val) :
    (L' (L s)).lbl a = .inl i := by
  have h1 := card_stendhalWeight_addBlack (ℓ := ℓ) i ν
  have h2 := card_stendhalWeight_addBlack (ℓ := ℓ) i νᵢ
  have := a.isLt
  by_cases h : a.val < Multiset.card (stendhalWeight ℓ νᵢ)
  · rw [appendBlackLoading_lbl_of_lt _ _ _ _ h]
    exact appendBlackLoading_lbl_of_eq _ _ _ _ (by simp only; omega)
  · exact appendBlackLoading_lbl_of_eq _ _ _ _ (by omega)

omit [DecidableEq I] in
/-- After appending three black strands, the three new positions carry the label `i`. -/
theorem appendBlackLoading_three_lbl (s : Seq (stendhalWeight ℓ ν))
    (a : Fin (Multiset.card (stendhalWeight ℓ νᵢᵢᵢ))) (ha : n ≤ a.val) :
    (L'' (L' (L s))).lbl a = .inl i := by
  have h1 := card_stendhalWeight_addBlack (ℓ := ℓ) i ν
  have h2 := card_stendhalWeight_addBlack (ℓ := ℓ) i νᵢ
  have h3 := card_stendhalWeight_addBlack (ℓ := ℓ) i νᵢᵢ
  have := a.isLt
  by_cases h : a.val < Multiset.card (stendhalWeight ℓ νᵢᵢ)
  · rw [appendBlackLoading_lbl_of_lt _ _ _ _ h]
    exact appendBlackLoading_two_lbl i ν s _ (by simp only; omega)
  · exact appendBlackLoading_lbl_of_eq _ _ _ _ (by omega)

theorem appendBlackValue_one_mul (z : StendhalAlgebraAllOrders k Q Λ ν) :
    G 1 * G z = G z := by
  rw [← map_mul, one_mul]

theorem appendBlackValue_mul_one (z : StendhalAlgebraAllOrders k Q Λ ν) :
    G z * G 1 = G z := by
  rw [← map_mul, mul_one]

theorem appendBlackValue_one_eq_sum :
    G (1 : StendhalAlgebraAllOrders k Q Λ ν) = ∑ s, e (L s) := by
  rw [← sum_e (k := k) (Q := Q) (Λ := Λ) (ν := ν), map_sum]
  exact Finset.sum_congr rfl fun s _ => appendBlackValue_e Q Λ i ν s

theorem appendBlackValue_two_one_eq_sum :
    G' (G (1 : StendhalAlgebraAllOrders k Q Λ ν)) = ∑ s, e (L' (L s)) := by
  rw [appendBlackValue_one_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun s _ => appendBlackValue_e Q Λ i νᵢ _

theorem appendBlackValue_three_one_eq_sum :
    G'' (G' (G (1 : StendhalAlgebraAllOrders k Q Λ ν))) = ∑ s, e (L'' (L' (L s))) := by
  rw [appendBlackValue_two_one_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun s _ => appendBlackValue_e Q Λ i νᵢᵢ _

theorem appendBlackValue_x (a : Fin n) :
    G (x a) = x ⟨a.val, by rw [card_stendhalWeight_addBlack]; omega⟩ * G 1 :=
  appendBlackAllOrders_x Q Λ i ν a

theorem appendBlackValue_ψ (j : ℕ) (hj : j + 1 < n) : G (ψ j) = ψ j * G 1 :=
  appendBlackAllOrders_ψ Q Λ i ν j hj

/-- The dot on the newly appended black strand. -/
def newDot : StendhalAlgebraAllOrders k Q Λ νᵢ :=
  x ⟨n, by rw [card_stendhalWeight_addBlack]; omega⟩

/-- The crossing of the two most recently appended black strands. -/
def newCross : StendhalAlgebraAllOrders k Q Λ νᵢᵢ := ψ n

theorem newDot_commute_e (s : Seq (stendhalWeight ℓ νᵢ)) :
    Commute (newDot (k := k) Q Λ i ν) (e s) :=
  x_mul_e _ s

/-- A dot on the new strand commutes with every diagram on the old strands. -/
theorem newDot_commute (z : StendhalAlgebraAllOrders k Q Λ ν) :
    Commute (newDot (k := k) Q Λ i ν) (G z) := by
  have h1 : Commute (newDot (k := k) Q Λ i ν) (G 1) :=
    commute_map_one _ _ fun s => by rw [appendBlackValue_e]; exact newDot_commute_e Q Λ i ν _
  refine commute_of_generators G (appendBlackValue_smul Q Λ i ν) _
    (fun s => by rw [appendBlackValue_e]; exact newDot_commute_e Q Λ i ν _) (fun a => ?_)
    (fun j => ?_) z
  · rw [appendBlackValue_x]
    exact Commute.mul_right (x_mul_x _ _) h1
  · by_cases hj : j + 1 < n
    · rw [appendBlackValue_ψ Q Λ i ν j hj]
      refine Commute.mul_right ?_ h1
      exact x_mul_ψ _ j (by simp only; omega) (by simp only; omega)
    · rw [ψ_eq_zero j (by omega), map_zero]
      exact Commute.zero_right _

theorem newCross_commute_e (s : Seq (stendhalWeight ℓ ν)) :
    Commute (newCross (k := k) Q Λ i ν) (e (L' (L s))) := by
  have h1 := card_stendhalWeight_addBlack (ℓ := ℓ) i ν
  have h2 := card_stendhalWeight_addBlack (ℓ := ℓ) i νᵢ
  exact ψ_mul_e_of_lbl_eq (by omega) (by
    rw [appendBlackLoading_two_lbl _ _ _ _ le_rfl,
      appendBlackLoading_two_lbl _ _ _ _ (by simp only; omega)])

/-- The crossing of the two new strands commutes with every diagram on the old strands. -/
theorem newCross_commute (z : StendhalAlgebraAllOrders k Q Λ ν) :
    Commute (newCross (k := k) Q Λ i ν) (G' (G z)) := by
  have h1 := card_stendhalWeight_addBlack (ℓ := ℓ) i ν
  have h2 := card_stendhalWeight_addBlack (ℓ := ℓ) i νᵢ
  let f := (appendBlackValue Q Λ i νᵢ).comp G
  have he : ∀ s, Commute (newCross (k := k) Q Λ i ν) (f (e s)) := fun s => by
    change Commute _ (G' (G (e s)))
    rw [appendBlackValue_e, appendBlackValue_e]
    exact newCross_commute_e Q Λ i ν s
  have hone : Commute (newCross (k := k) Q Λ i ν) (G' (G 1)) := commute_map_one f _ he
  refine commute_of_generators f (fun c w => by
    change G' (G (c • w)) = c • G' (G w)
    rw [appendBlackValue_smul, appendBlackValue_smul]) _ he (fun a => ?_) (fun j => ?_) z
  · change Commute _ (G' (G (x a)))
    rw [appendBlackValue_x, map_mul, appendBlackValue_x, mul_assoc,
      appendBlackValue_one_mul]
    refine Commute.mul_right ?_ hone
    exact (x_mul_ψ _ n (by simp only; omega) (by simp only; omega)).symm
  · change Commute _ (G' (G (ψ j)))
    by_cases hj : j + 1 < n
    · rw [appendBlackValue_ψ Q Λ i ν j hj, map_mul,
        appendBlackValue_ψ Q Λ i νᵢ j (by omega), mul_assoc, appendBlackValue_one_mul]
      exact Commute.mul_right (ψ_mul_ψ j n hj).symm hone
    · rw [ψ_eq_zero j (by omega), map_zero, map_zero]
      exact Commute.zero_right _

/-- Both crossings of three new strands commute with every diagram on the old strands. -/
theorem newCross_commute_three (z : StendhalAlgebraAllOrders k Q Λ ν) (p : ℕ) (hp : n ≤ p)
    (hp' : p ≤ n + 1) :
    Commute (ψ p : StendhalAlgebraAllOrders k Q Λ νᵢᵢᵢ) (G'' (G' (G z))) := by
  have h1 := card_stendhalWeight_addBlack (ℓ := ℓ) i ν
  have h2 := card_stendhalWeight_addBlack (ℓ := ℓ) i νᵢ
  have h3 := card_stendhalWeight_addBlack (ℓ := ℓ) i νᵢᵢ
  let f := (appendBlackValue Q Λ i νᵢᵢ).comp ((appendBlackValue Q Λ i νᵢ).comp G)
  have he : ∀ s, Commute (ψ p : StendhalAlgebraAllOrders k Q Λ νᵢᵢᵢ) (f (e s)) := by
    intro s
    change Commute _ (G'' (G' (G (e s))))
    rw [appendBlackValue_e, appendBlackValue_e, appendBlackValue_e]
    exact ψ_mul_e_of_lbl_eq (by omega) (by
      rw [appendBlackLoading_three_lbl _ _ _ _ hp,
        appendBlackLoading_three_lbl _ _ _ _ (by simp only; omega)])
  have hone : Commute (ψ p : StendhalAlgebraAllOrders k Q Λ νᵢᵢᵢ) (G'' (G' (G 1))) :=
    commute_map_one f _ he
  refine commute_of_generators f (fun c w => by
    change G'' (G' (G (c • w))) = c • G'' (G' (G w))
    rw [appendBlackValue_smul, appendBlackValue_smul, appendBlackValue_smul]) _ he
    (fun a => ?_) (fun j => ?_) z
  · change Commute _ (G'' (G' (G (x a))))
    rw [appendBlackValue_x, map_mul, map_mul, appendBlackValue_x, map_mul, appendBlackValue_x,
      mul_assoc _ (appendBlackValue Q Λ i νᵢᵢ 1), appendBlackValue_one_mul, mul_assoc,
      ← map_mul (appendBlackValue Q Λ i νᵢᵢ) (appendBlackValue Q Λ i νᵢ 1),
      appendBlackValue_one_mul]
    refine Commute.mul_right ?_ hone
    exact (x_mul_ψ _ p (by simp only; omega) (by simp only; omega)).symm
  · change Commute _ (G'' (G' (G (ψ j))))
    by_cases hj : j + 1 < n
    · rw [appendBlackValue_ψ Q Λ i ν j hj, map_mul, map_mul,
        appendBlackValue_ψ Q Λ i νᵢ j (by omega), map_mul,
        appendBlackValue_ψ Q Λ i νᵢᵢ j (by omega),
        mul_assoc _ (appendBlackValue Q Λ i νᵢᵢ 1), appendBlackValue_one_mul, mul_assoc,
        ← map_mul (appendBlackValue Q Λ i νᵢᵢ) (appendBlackValue Q Λ i νᵢ 1),
        appendBlackValue_one_mul]
      exact Commute.mul_right (ψ_mul_ψ j p (by omega)).symm hone
    · rw [ψ_eq_zero j (by omega), map_zero, map_zero, map_zero]
      exact Commute.zero_right _

theorem appendBlackValue_two_one_mul (z : StendhalAlgebraAllOrders k Q Λ ν) :
    G' (G 1) * G' (G z) = G' (G z) := by
  rw [← map_mul, appendBlackValue_one_mul]

/-- The nil-Hecke relation `x₁ψ - ψx₂ = 1` on two new strands. -/
theorem newDot_newCross_left (z : StendhalAlgebraAllOrders k Q Λ ν) :
    (x ⟨n, by rw [card_stendhalWeight_addBlack, card_stendhalWeight_addBlack]; omega⟩ * ψ n -
      ψ n * x ⟨n + 1, by
        rw [card_stendhalWeight_addBlack, card_stendhalWeight_addBlack]; omega⟩) *
        G' (G z) = G' (G z) := by
  have h1 := card_stendhalWeight_addBlack (ℓ := ℓ) i ν
  have h2 := card_stendhalWeight_addBlack (ℓ := ℓ) i νᵢ
  rw [← appendBlackValue_two_one_mul, ← mul_assoc, appendBlackValue_two_one_eq_sum,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => dot_cross_left_of_lbl_eq (by omega) ?_
  rw [appendBlackLoading_two_lbl _ _ _ _ le_rfl,
    appendBlackLoading_two_lbl _ _ _ _ (by simp only; omega)]

/-- The nil-Hecke relation `ψx₁ - x₂ψ = 1` on two new strands. -/
theorem newDot_newCross_right (z : StendhalAlgebraAllOrders k Q Λ ν) :
    (ψ n * x ⟨n, by rw [card_stendhalWeight_addBlack, card_stendhalWeight_addBlack]; omega⟩ -
      x ⟨n + 1, by
        rw [card_stendhalWeight_addBlack, card_stendhalWeight_addBlack]; omega⟩ * ψ n) *
        G' (G z) = G' (G z) := by
  have h1 := card_stendhalWeight_addBlack (ℓ := ℓ) i ν
  have h2 := card_stendhalWeight_addBlack (ℓ := ℓ) i νᵢ
  rw [← appendBlackValue_two_one_mul, ← mul_assoc, appendBlackValue_two_one_eq_sum,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => dot_cross_right_of_lbl_eq (by omega) ?_
  rw [appendBlackLoading_two_lbl _ _ _ _ le_rfl,
    appendBlackLoading_two_lbl _ _ _ _ (by simp only; omega)]

/-- The crossing of two new strands squares to zero. -/
theorem newCross_sq (z : StendhalAlgebraAllOrders k Q Λ ν) :
    ψ n * ψ n * G' (G z) = 0 := by
  have h1 := card_stendhalWeight_addBlack (ℓ := ℓ) i ν
  have h2 := card_stendhalWeight_addBlack (ℓ := ℓ) i νᵢ
  rw [← appendBlackValue_two_one_mul, ← mul_assoc, appendBlackValue_two_one_eq_sum,
    Finset.mul_sum]
  rw [Finset.sum_eq_zero fun s _ => ψ_sq_of_lbl_eq (k := k) (Q := Q) (Λ := Λ) (ν := νᵢᵢ)
    (j := n) (by omega) (s := L' (L s)) ?_, zero_mul]
  rw [appendBlackLoading_two_lbl _ _ _ _ le_rfl,
    appendBlackLoading_two_lbl _ _ _ _ (by simp only; omega)]

theorem appendBlackValue_three_one_mul (z : StendhalAlgebraAllOrders k Q Λ ν) :
    G'' (G' (G 1)) * G'' (G' (G z)) = G'' (G' (G z)) := by
  rw [← map_mul, appendBlackValue_two_one_mul]

/-- The braid relation on three new strands. -/
theorem newCross_braid (z : StendhalAlgebraAllOrders k Q Λ ν) :
    (ψ n * ψ (n + 1) * ψ n - ψ (n + 1) * ψ n * ψ (n + 1)) * G'' (G' (G z)) = 0 := by
  have h1 := card_stendhalWeight_addBlack (ℓ := ℓ) i ν
  have h2 := card_stendhalWeight_addBlack (ℓ := ℓ) i νᵢ
  have h3 := card_stendhalWeight_addBlack (ℓ := ℓ) i νᵢᵢ
  rw [← appendBlackValue_three_one_mul, ← mul_assoc, appendBlackValue_three_one_eq_sum,
    Finset.mul_sum]
  rw [Finset.sum_eq_zero fun s _ => braid_of_lbl_eq (k := k) (Q := Q) (Λ := Λ) (ν := νᵢᵢᵢ)
    (j := n) (by omega) (s := L'' (L' (L s))) ?_, zero_mul]
  rw [appendBlackLoading_three_lbl _ _ _ _ le_rfl,
    appendBlackLoading_three_lbl _ _ _ _ (by simp only; omega)]

end BlackStrands

end StendhalAlgebraAllOrders

end Categorification.Stendhal
