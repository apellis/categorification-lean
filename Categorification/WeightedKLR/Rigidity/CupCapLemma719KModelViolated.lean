/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeCoe

/-!
# Violated diagrams above the cap act through violated diagrams below it, on the model

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof: the inverse `Ψ` of the comparison map is
defined on the model `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}` of `K̃^{λ⁺}_λ` (Lemma 7.17) and has to vanish
on `V_λ K̃`. Every diagram of `T̃^λ` acts on a generator `Z ⊗ v` of the model by multiplying `Z`
on the left by a diagram of `T̃^{λ⁺}` (`midLeftAlg_tmul_midGen_exists`). For a violated diagram
of `T̃^λ` that diagram of `T̃^{λ⁺}` can be chosen violated (`midLeftAlg_tmul_midGen_violated`):
the leftmost black strand stays leftmost below the cap.

## Main results

* `Stendhal.CupCap.midLeftAlg_tmul_midGen_exists`: diagrams of `T̃^λ` act by left
  multiplication on the generators of the model.
* `Stendhal.CupCap.midLeftAlg_tmul_midGen_violated`: violated diagrams act through violated
  diagrams of `T̃^{λ⁺}`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Insert

variable {I : Type*} {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}

/-- The maximum of the model sits right of the first strand of a violated loading. -/
theorem midPos_pos_of_isViolated {s : Seq (stendhalWeight ℓ ν)} (hs : IsViolated s) :
    0 < midPos j s := by
  obtain ⟨h0, hb⟩ := hs
  unfold midPos
  split_ifs with h
  · refine Nat.pos_of_ne_zero fun h' => ?_
    have hr := (exists_lbl_eq_inr s ⟨j, h⟩).choose_spec
    have he : (exists_lbl_eq_inr s ⟨j, h⟩).choose = ⟨0, h0⟩ := Fin.ext h'
    rw [he] at hr
    rw [hr] at hb
    exact absurd hb (by simp)
  · exact h0

/-- **Inserting the strands at the maximum right of the first strand keeps a violation.** -/
theorem insertSeq_isViolated {s : Seq (stendhalWeight ℓ ν)} (hs : IsViolated s) {n : ℕ}
    (hn : n ≤ Multiset.card (stendhalWeight ℓ ν)) (hn0 : 0 < n)
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) :
    IsViolated (insertSeq (j := j) (hj := hj) (ν₀ := ν₀) s n hn t) := by
  obtain ⟨h0, hb⟩ := hs
  have h := insertSeq_lbl_old (j := j) (hj := hj) (ν₀ := ν₀) s n hn t ⟨0, h0⟩
  have hidx :
      (Fin.cast (card_plus j hj ν ν₀).symm (insertPos _ _ n hn (.inl ⟨0, h0⟩))).val = 0 := by
    simp [insertPos, hn0]
  refine ⟨by rw [← hidx]; exact Fin.is_lt _, ?_⟩
  have he : (⟨0, by rw [← hidx]; exact Fin.is_lt _⟩ :
      Fin (Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀)))) =
      Fin.cast (card_plus j hj ν ν₀).symm (insertPos _ _ n hn (.inl ⟨0, h0⟩)) := Fin.ext hidx.symm
  rw [he, h]
  revert hb
  rcases s.lbl ⟨0, h0⟩ with b | r <;> simp [oldColour]

end Insert

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "T" => StendhalAlgebra k Q Λ ν
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Vp" => StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "σ" => midStendhal j hj Q Λ Λc ν ν₀

/-- **The idempotent of a violated loading, placed above the maximum, is violated.** -/
theorem botMap_midIdem_mem_violated {s : Seq (stendhalWeight ℓ ν)} (hs : IsViolated s) :
    bot (midIdem j hj Q Λ Λc ν ν₀ s) ∈ Vp := by
  rw [midIdem, KLRAlgebra.eSum, map_sum]
  refine Finset.sum_induction _ (· ∈ Vp) (fun _ _ => add_mem) (zero_mem _) fun u hu => ?_
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hu
  by_cases ho : IsRedOrdered (insertSeq (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s)
    (midPos_le j s) t)
  · rw [show bot (KLRAlgebra.e _) = StendhalAlgebra.e (k := k) (Q := Q)
        (Λ := plusLabels Λ Λc j hj) _ ho from topMap_e_of_isRedOrdered _ ho]
    exact TwoSidedIdeal.subset_span ⟨_, ho,
      insertSeq_isViolated hs _ (midPos_pos_of_isViolated hs) t, rfl⟩
  · rw [botMap, AlgHom.comp_apply, orderProjection_e_of_not ho]
    exact zero_mem _

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

theorem midGen_zero' : midGen j hj Q Λ Λc ν ν₀ (0 : Tp) = 0 :=
  Subtype.ext (by simp [midGen])

theorem midGen_add' (Z Z' : Tp) :
    midGen j hj Q Λ Λc ν ν₀ (Z + Z') = midGen j hj Q Λ Λc ν ν₀ Z + midGen j hj Q Λ Λc ν ν₀ Z' :=
  Subtype.ext (by simp [midGen, mul_add])

theorem midGen_neg' (Z : Tp) : midGen j hj Q Λ Λc ν ν₀ (-Z) = -midGen j hj Q Λ Λc ν ν₀ Z :=
  eq_neg_of_add_eq_zero_left (by rw [← midGen_add', neg_add_cancel, midGen_zero'])

/-- **A diagram of `T̃^λ` acts on the generators of the model by left multiplication** with a
diagram of `T̃^{λ⁺}`. -/
theorem midLeftAlg_tmul_midGen_exists (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) (a : T) :
    ∃ Y : Rp, ∀ (Z : Tp) (v : L), midLeftAlg L hL hR a (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ Z) v) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot Y * σ 1 * Z)) v := by
  obtain ⟨r, rfl⟩ := topMap_surjective' (k := k) (Q := Q) (Λ := Λ) (ν := ν) a
  obtain ⟨x, rfl⟩ := KLRAlgebra.mk_surjective (k := k) (Q := stendhalQ Q Λ)
    (ν := stendhalWeight ℓ ν) r
  refine ⟨(midFree j hj Q Λ Λc ν ν₀ x).val, fun Z v => ?_⟩
  rw [midLeftAlg_topMap, midKLRAct_mk, midEndAlg_apply, midEnd_tmul]

/-- **A violated diagram of `T̃^λ` acts on the generators of the model through a violated
diagram of `T̃^{λ⁺}`.** -/
theorem midLeftAlg_tmul_midGen_violated (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL) {a : T}
    (ha : a ∈ StendhalAlgebra.violatedIdeal k Q Λ ν) :
    ∃ W ∈ Vp, ∀ (Z : Tp) (v : L),
      midLeftAlg L hL hR a (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ Z) v) =
        Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (W * Z)) v := by
  refine TwoSidedIdeal.span_induction
    (p := fun a _ => ∃ W ∈ Vp, ∀ (Z : Tp) (v : L),
      midLeftAlg L hL hR a (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ Z) v) =
        Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (W * Z)) v) ?_ ?_ ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨s, hs, hv, rfl⟩
    refine ⟨bot (midIdem j hj Q Λ Λc ν ν₀ s) * σ 1,
      TwoSidedIdeal.mul_mem_right _ _ _ (botMap_midIdem_mem_violated hv), fun Z v => ?_⟩
    rw [← topMap_e_of_isRedOrdered s hs, midLeftAlg_topMap, KLRAlgebra.e, midKLRAct_mk,
      midEndAlg_apply, midEnd_tmul, midFree_fe]
  · exact ⟨0, zero_mem _, fun Z v => by
      rw [map_zero, LinearMap.zero_apply, zero_mul, midGen_zero', Ind.zero_tmul]⟩
  · rintro a b - - ⟨W, hW, h⟩ ⟨W', hW', h'⟩
    exact ⟨W + W', add_mem hW hW', fun Z v => by
      rw [map_add, LinearMap.add_apply, h, h', add_mul, midGen_add', Ind.add_tmul]⟩
  · rintro a - ⟨W, hW, h⟩
    exact ⟨-W, neg_mem hW, fun Z v => by
      rw [map_neg, LinearMap.neg_apply, h, show -W * Z = -(W * Z) from neg_mul W Z, midGen_neg',
        Ind.neg_tmul]⟩
  · rintro t a - ⟨W, hW, h⟩
    obtain ⟨Y, hY⟩ := midLeftAlg_tmul_midGen_exists hR t
    exact ⟨bot Y * σ 1 * W, TwoSidedIdeal.mul_mem_left _ _ _ hW, fun Z v => by
      rw [map_mul, Module.End.mul_apply, h, hY, mul_assoc (bot Y * σ 1)]⟩
  · rintro a t - ⟨W, hW, h⟩
    obtain ⟨Y, hY⟩ := midLeftAlg_tmul_midGen_exists hR a
    exact ⟨W * (bot Y * σ 1), TwoSidedIdeal.mul_mem_right _ _ _ hW, fun Z v => by
      rw [map_mul, Module.End.mul_apply, hY, h, mul_assoc W, mul_assoc]⟩

end Categorification.Stendhal.CupCap
