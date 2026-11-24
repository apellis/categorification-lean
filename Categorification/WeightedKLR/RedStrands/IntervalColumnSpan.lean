/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AdjacentBlockRoot
import Categorification.KLR.InductionFree

/-!
# Generators supported in an adjacent red interval

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8, kernel test following (6.21).
A reduced right factor performing the red exchange inside the bottom interval
can be chosen in each top-dot PBW word of the affine loading column.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA Equiv MvPolynomial

variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "A" => KLRAlgebra k (stendhalQ Q Λ) μ

/-- The affine column exchanging two adjacent red strands is spanned by left
multiples of undotted crossings supported in their bottom interval. The two
red strands are consecutive immediately above the interval factor.
Webster v2, §6.1, the kernel test following (6.21). -/
theorem mem_span_interval_crossing_column (hQ : KLRSymm Q)
    (s t : Seq μ) {q p : Fin m} {a b : Fin ℓ} {L M : List (Fin ℓ)}
    (hq : s.lbl q = .inr a) (hp : s.lbl p = .inr b)
    (hs : redWord s = L ++ a :: b :: M) (ht : redWord t = L ++ b :: a :: M)
    (z : A) :
    e t * z * e s ∈ Submodule.span k {y : A | ∃ (x : A) (v : Perm (Fin m)),
      (∀ j, j < q ∨ p < j → v j = j) ∧ redWord (v • s) = redWord t ∧
      (v q : ℕ) = v p + 1 ∧ e t * x * e (v • s) = x ∧
      y = x * (ψw (canWord m v) * e s)} := by
  classical
  have frame (w : Perm (Fin m)) (hw : w • s = t) :
      ∃ v : Perm (Fin m), invSet m v ⊆ invSet m w ∧
        (∀ j, j < q ∨ p < j → v j = j) ∧ redWord (v • s) = redWord t ∧
        (v q : ℕ) = v p + 1 := by
    have hqp := lt_of_redWord_eq_append hs hq hp
    obtain ⟨v, hv, hfix, hadj⟩ := exists_isSwapBelow_interval_adjacent (R := redSet s) hqp
      (mem_invSet_of_sublist_redWord (by rw [hw, ht]; simp) hqp hq hp)
      (fun j hj => not_lt_of_redWord_eq_append hs hq hp (by simpa [redSet] using hj))
    exact ⟨v, hv.le, hfix, ((redWord_smul_eq_swap_iff' hs hq hp v).2 hv.red).trans ht.symm, hadj⟩
  let ρ (w : Perm (Fin m)) := if hw : w • s = t then
    canWord m (w * (frame w hw).choose⁻¹) ++ canWord m (frame w hw).choose
    else canWord m w
  have hρ : IsReducedChoice ρ := by
    intro w
    dsimp only [ρ]
    split_ifs with hw
    · let v := (frame w hw).choose
      have hsub : invSet m v ⊆ invSet m w := (frame w hw).choose_spec.1
      have hprod : wordProd m (canWord m (w * v⁻¹) ++ canWord m v) = w := by
        rw [wordProd_append, wordProd_canWord, wordProd_canWord, inv_mul_cancel_right]
      exact ⟨⟨validWord_append.2 ⟨validWord_canWord _ _, validWord_canWord _ _⟩,
        by rw [List.length_append, length_canWord, length_canWord, hprod]
           exact length_add_of_invSet_subset hsub⟩, hprod⟩
    · exact ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩
  let B := lbasis (k := k) («μ» := μ) (stendhalQ_symm Q Λ hQ) ρ hρ
  induction B.mem_span z using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ hx hy => rw [mul_add, add_mul]; exact add_mem hx hy
  | smul c _ _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
  | mem _ h =>
    obtain ⟨⟨s',w,d⟩, rfl⟩ := h
    rw [show B (s',w,d) = _ from lbasis_apply .., mul_assoc, mul_assoc _ (e s'), e_mul_e]
    split_ifs with h
    swap
    · rw [mul_zero, mul_zero]; exact zero_mem _
    subst s'
    by_cases hw : w • s = t
    · apply Submodule.subset_span
      let v := (frame w hw).choose
      let x : A := e t * pol (monomial d 1) * ψw (canWord m (w * v⁻¹)) * e (v • s)
      refine ⟨x, v, (frame w hw).choose_spec.2.1, (frame w hw).choose_spec.2.2.1,
        (frame w hw).choose_spec.2.2.2, ?_, ?_⟩
      · dsimp only [x]
        simp only [← mul_assoc, e_mul_self]
        rw [mul_assoc _ (e (v • s)) (e (v • s)), e_mul_self]
      · have he : (e (v • s) * (ψw (canWord m v) * e s) : A) = ψw (canWord m v) * e s := by
          have hh := e_mul_pol_ψw_e (Q := stendhalQ Q Λ) 1 (canWord m v) s
          simpa only [wordProd_canWord, map_one, one_mul] using hh
        change e t * (pol (monomial d 1) * ψw (ρ w) * e s) = x * _
        simp only [x, ρ, dite_eq_left hw, ψw_append]
        rw [mul_assoc _ (e (v • s)), he]
        simp only [mul_assoc, v]
    · have cut := e_mul_pol_ψw_e (Q := stendhalQ Q Λ) (monomial d (1 : k)) (ρ w) s
      rw [(hρ w).2] at cut
      rw [← cut, ← mul_assoc, e_mul_e, ite_eq_right (Ne.symm hw), zero_mul]
      exact zero_mem _

end Categorification.Stendhal.BraidedStendhalAlgebra
