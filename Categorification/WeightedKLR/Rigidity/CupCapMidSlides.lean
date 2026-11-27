/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidNull
import Categorification.WeightedKLR.Rigidity.CupCapModelMap

/-!
# Diagrams of `λ` above the maximum of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. In the model of `K̃^{λ⁺}_λ` with the
maximum just before the red strand `λ_{j+1}` (`CupCap.MidModel`), the diagrams of `λ` act above
the maximum. Away from `λ_{j+1}` a dot or a crossing of `λ` is the same dot or crossing of `λ⁺`,
which commutes with the diagrams at the maximum up to moving the loading
(`CupCap.ψ_crossPos_mul_insertMap`, `CupCap.commute_x_insertMap`). A crossing of `λ_{j+1}` with a
black strand moves the maximum: the black strand passes under the maximum.

This file sets up the positions of the maximum under these crossings and the elements of `λ⁺` that
represent idempotents, dots and crossings of `λ` away from `λ_{j+1}`.

## Main results

* `CupCap.midPos_sadj_of_far`, `CupCap.midPos_sadj_left`, `CupCap.midPos_sadj_right`: the
  position of the maximum after a crossing.
* `CupCap.ψ_crossPos_mul_insertMap`, `CupCap.commute_x_insertMap`: diagrams away from the
  window commute with the diagrams on the window.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

section Position

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} (j : ℕ) {ν : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)

theorem midPos_eq {s : Seq (stendhalWeight ℓ ν)} (h : j < ℓ) {a : Fin m}
    (ha : s.lbl a = .inr ⟨j, h⟩) : midPos j s = a.val := by
  obtain ⟨b, hb, hlb⟩ := midPos_of_lt j s h
  rw [← hb]; exact congrArg Fin.val (lbl_eq_inr_unique hlb ha)

omit [DecidableEq I] in
theorem lbl_sadj_of_swapNat (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m) (a b : Fin m)
    (h : swapNat p a = b) : (sadj m p • s).lbl a = s.lbl b := by
  rw [lbl_sadj]; exact congrArg s.lbl (Fin.ext ((sadj_val_of_lt hp a).trans h))

omit [DecidableEq I] in
theorem midPos_lt {s : Seq (stendhalWeight ℓ ν)} (h : j < ℓ) : midPos j s < m := by
  obtain ⟨b, hb, -⟩ := midPos_of_lt j s h
  rw [← hb]; exact b.2

omit [DecidableEq I] in
theorem lt_of_midPos_lt {s : Seq (stendhalWeight ℓ ν)} {p : ℕ} (hp : p < m)
    (h : midPos j s ≤ p) : j < ℓ := by
  by_contra hj
  rw [midPos_of_not_lt j s hj] at h
  omega

/-- A crossing away from `λ_{j+1}` does not move the maximum. -/
theorem midPos_sadj_of_far (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hf : p + 1 < midPos j s ∨ midPos j s + 1 ≤ p) :
    midPos j (sadj m p • s) = midPos j s := by
  by_cases h : j < ℓ
  · obtain ⟨b, hb, hlb⟩ := midPos_of_lt j s h
    refine (midPos_eq j h (a := b) ?_).trans hb
    rw [lbl_sadj_of_swapNat s hp b b (by unfold swapNat; split_ifs <;> omega), hlb]
  · rw [midPos_of_not_lt j _ h, midPos_of_not_lt j _ h]

/-- The crossing of `λ_{j+1}` with the strand on its left moves the maximum one step left. -/
theorem midPos_sadj_left (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p + 1 = midPos j s) : midPos j (sadj m p • s) = p := by
  have h := lt_of_midPos_lt j (s := s) (p := p + 1) hp hc.ge
  obtain ⟨b, hb, hlb⟩ := midPos_of_lt j s h
  refine midPos_eq j h (a := ⟨p, by omega⟩) ?_
  rw [lbl_sadj_of_swapNat s hp _ b (by unfold swapNat; split_ifs <;> simp_all), hlb]

/-- The crossing of `λ_{j+1}` with the strand on its right moves the maximum one step right. -/
theorem midPos_sadj_right (s : Seq (stendhalWeight ℓ ν)) {p : ℕ} (hp : p + 1 < m)
    (hc : p = midPos j s) : midPos j (sadj m p • s) = p + 1 := by
  have h := lt_of_midPos_lt j (s := s) (p := p) (by omega) hc.ge
  obtain ⟨b, hb, hlb⟩ := midPos_of_lt j s h
  refine midPos_eq j h (a := ⟨p + 1, hp⟩) ?_
  rw [lbl_sadj_of_swapNat s hp _ b (by unfold swapNat; split_ifs <;> simp_all), hlb]

end Position

theorem ψ_mul_ψ_comm {J : Type*} [DecidableEq J] {k : Type*} [CommRing k] {μ : Multiset J}
    {Q' : J → J → MvPolynomial (Fin 2) k} {a b : ℕ} (h : a + 1 < b ∨ b + 1 < a) :
    (KLRAlgebra.ψ a * KLRAlgebra.ψ b : KLRAlgebra k Q' μ) = KLRAlgebra.ψ b * KLRAlgebra.ψ a := by
  rcases h with h | h
  · exact KLRAlgebra.ψ_mul_ψ a b h
  · exact (KLRAlgebra.ψ_mul_ψ b a h).symm

section Window

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)

theorem insertSet_congr' (s : Seq (stendhalWeight ℓ ν)) {p p' : ℕ} (hp : p ≤ m) (hp' : p' ≤ m)
    (h : p = p') : insertSet (j := j) (hj := hj) (ν₀ := ν₀) s p hp =
      insertSet (j := j) (hj := hj) (ν₀ := ν₀) s p' hp' := by
  subst h; rfl

theorem insertMap_congr' (s : Seq (stendhalWeight ℓ ν)) {p p' : ℕ} (hp : p ≤ m) (hp' : p' ≤ m)
    (h : p = p') (x : Rc) : ι s p hp x = ι s p' hp' x := by
  subst h; rfl

theorem exitSpan_congr' (s : Seq (stendhalWeight ℓ ν)) {p p' : ℕ} (hp : p ≤ m) (hp' : p' ≤ m)
    (h : p = p') :
    exitSpan Q Λ Λc j hj (ν₀ := ν₀) s p hp = exitSpan Q Λ Λc j hj s p' hp' := by
  subst h; rfl

/-- **A crossing away from the window commutes with the diagrams on the window**, moving the
loading of `λ`. -/
theorem ψ_crossPos_mul_insertMap (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) {p : ℕ}
    (hp : p + 1 < n ∨ n ≤ p) (x : Rc) :
    (KLRAlgebra.ψ (crossPos n N p) * ι s n hn x : Rp) =
      ι (sadj m p • s) n hn x * KLRAlgebra.ψ (crossPos n N p) := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  induction x using KLRAlgebra.klr_induction generalizing s with
  | hadd u v hu hv => rw [insertMap_add, insertMap_add, mul_add, add_mul, hu, hv]
  | hmul u v hu hv => rw [insertMap_mul, insertMap_mul, ← mul_assoc, hu, mul_assoc, hv,
      mul_assoc]
  | hr c =>
    rw [insertMap_algebraMap, insertMap_algebraMap, mul_smul_comm, smul_mul_assoc,
      ψ_crossPos_mul_eSum s hn hp]
  | he w =>
    rw [insertMap_e, insertMap_e, KLRAlgebra.ψ_mul_e]
    congr 2
    have h := smul_insertSeq_old s hn (Seq.map (cupColour j hj) w) hp
    rw [Multiset.card_map] at h
    exact h
  | hx b =>
    have hb := b.2
    rw [insertMap_x, insertMap_x, ← mul_assoc,
      ← (KLRAlgebra.x_mul_ψ (⟨n + b.val, add_lt_M hn b⟩ : Fin M) (crossPos n N p)
        (by unfold crossPos; split_ifs <;> dsimp only <;> omega)
        (by unfold crossPos; split_ifs <;> dsimp only <;> omega)), mul_assoc,
      ψ_crossPos_mul_eSum s hn hp, mul_assoc]
  | hψ r =>
    by_cases hr : r + 1 < N
    · rw [insertMap_ψ s hn hr, insertMap_ψ _ hn hr, ← mul_assoc,
        ψ_mul_ψ_comm (by unfold crossPos; split_ifs <;> omega), mul_assoc,
        ψ_crossPos_mul_eSum s hn hp, mul_assoc]
    · rw [KLRAlgebra.ψ_eq_zero r (by omega), ← map_zero (algebraMap k Rc), insertMap_algebraMap,
        insertMap_algebraMap, zero_smul, zero_smul, mul_zero, zero_mul]

/-- **A dot away from the window commutes with the diagrams on the window.** -/
theorem commute_x_insertMap (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) (a : Fin M)
    (ha : a.val < n ∨ n + N ≤ a.val) (x : Rc) :
    Commute (KLRAlgebra.x a : Rp) (ι s n hn x) := by
  induction x using KLRAlgebra.klr_induction with
  | hadd u v hu hv => rw [insertMap_add]; exact hu.add_right hv
  | hmul u v hu hv => rw [insertMap_mul]; exact hu.mul_right hv
  | hr c => rw [insertMap_algebraMap]; exact (commute_x_eSum a _).smul_right c
  | he w => rw [insertMap_e]; exact KLRAlgebra.x_mul_e a _
  | hx b =>
    rw [insertMap_x]
    refine (Commute.mul_right ?_ (commute_x_eSum a _))
    exact KLRAlgebra.x_mul_x _ _
  | hψ r =>
    by_cases hr : r + 1 < N
    · rw [insertMap_ψ s hn hr]
      refine (Commute.mul_right ?_ (commute_x_eSum a _))
      exact KLRAlgebra.x_mul_ψ a (n + r) (by have := hr; omega) (by omega)
    · rw [KLRAlgebra.ψ_eq_zero r (by omega), ← map_zero (algebraMap k Rc), insertMap_algebraMap,
        zero_smul]
      exact Commute.zero_right _

end Window

end Categorification.Stendhal.CupCap
