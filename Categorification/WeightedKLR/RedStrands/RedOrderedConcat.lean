/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyIndIdempotent
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyLeftInd
import Categorification.WeightedKLR.RedStrands.Stendhal

/-!
# Red-ordered loadings of a concatenation

If every red label of `ν` is smaller than every red label of `ν'`, a concatenation `i j` of
loadings of `ν` and `ν'` has its red strands in order exactly when `i` and `j` do
(`isRedOrdered_append_iff`). So the idempotent of the red-ordered loadings of `ν'' + ν''' = ν + ν'`
acts on the image of `R(ν) ⊗ R(ν')` as `P_ν ⊗ P_{ν'}`, the tensor product of the idempotents of
the red-ordered loadings of the two factors (`concatLoadIdem_redOrdered`).

This splits the ordered-loading idempotent of a partial standardization along the top cut at the
end of the window, for the trace half of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v3, Lemma 7.19: there the top part carries the reds of the head blocks
and of the window, the bottom part those of the tail blocks.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {ℓ : ℕ}

omit [DecidableEq I] in
theorem isRedOrdered_seqCast {μ₁ μ₂ : Multiset (I ⊕ Fin ℓ)} (h : μ₁ = μ₂) (s : Seq μ₁) :
    IsRedOrdered (seqCast h s) ↔ IsRedOrdered s := by
  subst h; rfl

omit [DecidableEq I] in
theorem Seq.lbl_mem {μ : Multiset (I ⊕ Fin ℓ)} (s : Seq μ) (a : Fin (Multiset.card μ)) :
    s.lbl a ∈ μ := by
  have h := Multiset.mem_map_of_mem s.1 (Finset.mem_univ_val a)
  rwa [s.2] at h

omit [DecidableEq I] in
/-- **Red order of a concatenation**: when the reds of `ν` precede those of `ν'`, the loading `i j`
is red-ordered iff `i` and `j` are. -/
theorem isRedOrdered_append_iff {ν ν' : Multiset (I ⊕ Fin ℓ)}
    (hsep : ∀ r r' : Fin ℓ, Sum.inr r ∈ ν → Sum.inr r' ∈ ν' → r < r') (i : Seq ν) (j : Seq ν') :
    IsRedOrdered (i.append j) ↔ IsRedOrdered i ∧ IsRedOrdered j := by
  constructor
  · intro h
    refine ⟨fun a b r r' hab ha hb => ?_, fun a b r r' hab ha hb => ?_⟩
    · refine h (Seq.posL ν' a) (Seq.posL ν' b) r r' hab ?_ ?_
      · change (i.append j).1 (Seq.posL ν' a) = _; rw [Seq.append_posL]; exact ha
      · change (i.append j).1 (Seq.posL ν' b) = _; rw [Seq.append_posL]; exact hb
    · refine h (Seq.posR ν a) (Seq.posR ν b) r r' ((blockEquiv_inr_lt_inr _).2 hab) ?_ ?_
      · change (i.append j).1 (Seq.posR ν a) = _; rw [Seq.append_posR]; exact ha
      · change (i.append j).1 (Seq.posR ν b) = _; rw [Seq.append_posR]; exact hb
  · rintro ⟨hi, hj⟩ x y r r' hxy hx hy
    obtain ⟨x', rfl⟩ := (blockEquiv (Seq.card_add' ν ν')).surjective x
    obtain ⟨y', rfl⟩ := (blockEquiv (Seq.card_add' ν ν')).surjective y
    rcases x' with a | a <;> rcases y' with b | b
    · change (i.append j).1 (Seq.posL ν' a) = _ at hx
      change (i.append j).1 (Seq.posL ν' b) = _ at hy
      rw [Seq.append_posL] at hx hy
      exact hi a b r r' hxy hx hy
    · change (i.append j).1 (Seq.posL ν' a) = _ at hx
      change (i.append j).1 (Seq.posR ν b) = _ at hy
      rw [Seq.append_posL] at hx
      rw [Seq.append_posR] at hy
      exact hsep r r' (hx ▸ Seq.lbl_mem i a) (hy ▸ Seq.lbl_mem j b)
    · exact absurd hxy (not_lt.2 (le_of_lt (blockEquiv_inl_lt_inr _ b a)))
    · change (i.append j).1 (Seq.posR ν a) = _ at hx
      change (i.append j).1 (Seq.posR ν b) = _ at hy
      rw [Seq.append_posR] at hx hy
      exact hj a b r r' ((blockEquiv_inr_lt_inr _).1 hxy) hx hy

variable {k : Type*} [CommRing k] {Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k}

open Classical in
/-- **The red-ordered idempotent on the image of `R(ν) ⊗ R(ν')`** is `P_ν ⊗ P_{ν'}` when the reds
of `ν` precede those of `ν'`. -/
theorem concatLoadIdem_redOrdered {ν ν' ν'' ν''' : Multiset (I ⊕ Fin ℓ)}
    (h : ν'' + ν''' = ν + ν')
    (hsep : ∀ r r' : Fin ℓ, Sum.inr r ∈ ν → Sum.inr r' ∈ ν' → r < r') :
    concatLoadIdem Q h (Finset.univ.filter fun s : Seq (ν'' + ν''') => IsRedOrdered s) =
      eSum Q (Finset.univ.filter fun s : Seq ν => IsRedOrdered s) ⊗ₜ
        eSum Q (Finset.univ.filter fun s : Seq ν' => IsRedOrdered s) := by
  rw [concatLoadIdem, eSum, eSum, TensorProduct.sum_tmul, Fintype.sum_prod_type,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : ∀ j : Seq ν', IsRedOrdered (seqCast h.symm (i.append j)) ↔
      IsRedOrdered i ∧ IsRedOrdered j := fun j => by
    rw [isRedOrdered_seqCast, isRedOrdered_append_iff hsep]
  by_cases hi : IsRedOrdered i
  · rw [ite_eq_left hi, TensorProduct.tmul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : IsRedOrdered j
    · rw [ite_eq_left (Finset.mem_filter.2 ⟨Finset.mem_univ _, (hc j).2 ⟨hi, hj⟩⟩),
        ite_eq_left hj]
    · rw [ite_eq_right (fun hm => hj ((hc j).1 (Finset.mem_filter.1 hm).2).2),
        ite_eq_right hj]
  · rw [ite_eq_right hi]
    exact Finset.sum_eq_zero fun j _ =>
      ite_eq_right (fun hm => hi ((hc j).1 (Finset.mem_filter.1 hm).2).1)

section Cut

variable {a r : ℕ} (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ)
  (θ β : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)

open Classical in
/-- **The ordered loadings of a cut on the image of a top cut `ν | ν'`** whose reds of `ν` precede
those of `ν'`: `P_{ν,ν'} = P_ν ⊗ P_{ν'}`. -/
theorem cutConcatIdem_eq_tmul {ν ν' : Multiset (I ⊕ Fin (a + r))} (h : α + δ = ν + ν')
    (hsep : ∀ r₁ r₂ : Fin (a + r), Sum.inr r₁ ∈ ν → Sum.inr r₂ ∈ ν' → r₁ < r₂) :
    cutConcatIdem Q Λ θ β h =
      eSum (stendhalQ Q Λ) (Finset.univ.filter fun s : Seq ν => IsRedOrdered s) ⊗ₜ
        eSum (stendhalQ Q Λ) (Finset.univ.filter fun s : Seq ν' => IsRedOrdered s) :=
  concatLoadIdem_redOrdered h hsep

end Cut

end Categorification.Stendhal
