/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicInputLastStrand
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleDescent
import Categorification.KLR.IndLastStrandDescent

/-!
# The red-ordered idempotent and the last black strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. Standardization is the quotient of parabolic induction by the kernel of the
idempotent `P` summing `e(s)` over the red-ordered loadings `s`. Adjoining a black strand on
the right does not change the red order, so `P` commutes with the idempotent `1_{-,i}` of the
last-strand sequence and `P 1_{-,i} = ι(P₂ ⊗ 1_i)` with `P₂` the red-ordered idempotent one
strand shorter. These are the hypotheses of `KLRAlgebra.lastDescend_exact`.

## Main definitions

* `redOrderedSet μ`: the red-ordered loadings of weight `μ`.

## Main results

* `castKLR_eSum_redOrderedSet`: transport along equal weights preserves the idempotent;
* `eSum_redOrderedSet_mul_oneConcat`: `P · ι(1 ⊗ 1_i) = ι(P₂ ⊗ 1_i)` for a black label `i`;
* `commute_eSum_redOrderedSet_lastIdem`: `P` commutes with `1_{-,i}`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct

section Generic

variable {J k : Type*} [DecidableEq J] [CommRing k] {R : J → J → MvPolynomial (Fin 2) k}

theorem castKLR_eSum_of_mem_iff {μ μ' : Multiset J} (h : μ = μ') {T : Finset (Seq μ)}
    {T' : Finset (Seq μ')} (hT : ∀ s, s ∈ T' ↔ Seq.cast h.symm s ∈ T) :
    castKLR R h (eSum R T) = eSum R T' := by
  subst h
  change eSum R T = eSum R T'
  exact congrArg (eSum R) (Finset.ext fun s => (hT s).symm)

/-- `e_T · ι(1 ⊗ 1_j) = ι(e_{T₂} ⊗ 1_j)` when `a.j ∈ T ↔ a ∈ T₂`. -/
theorem eSum_mul_oneConcat_singleton {μ : Multiset J} (j : J) {T : Finset (Seq (μ + {j}))}
    {T₂ : Finset (Seq μ)} (hT : ∀ a, a.append default ∈ T ↔ a ∈ T₂) :
    eSum R T * oneConcat R μ {j} = concat R μ {j} (eSum R T₂ ⊗ₜ 1) := by
  conv_rhs => rw [eSum, TensorProduct.sum_tmul, map_sum]
  rw [← concat_one, Algebra.TensorProduct.one_def, ← sum_e (ν := μ), TensorProduct.sum_tmul,
    map_sum, Finset.mul_sum]
  simp only [concat_e_tmul_one_singleton, eSum_mul_e, hT]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem commute_e_e {μ : Multiset J} (s t : Seq μ) : Commute (e s : KLRAlgebra k R μ) (e t) := by
  unfold Commute SemiconjBy
  rw [e_mul_e, e_mul_e]
  by_cases h : s = t
  · subst h; rfl
  · simp [h, Ne.symm h]

theorem commute_eSum_eSum {μ : Multiset J} (T T' : Finset (Seq μ)) :
    Commute (eSum R T : KLRAlgebra k R μ) (eSum R T') :=
  Commute.sum_left _ _ _ fun s _ => Commute.sum_right _ _ _ fun t _ => commute_e_e s t

end Generic

variable {I k : Type*} [DecidableEq I] [CommRing k] {n : ℕ}

open Classical in
/-- The red-ordered loadings of weight `μ`. -/
def redOrderedSet (μ : Multiset (I ⊕ Fin n)) : Finset (Seq μ) :=
  Finset.univ.filter fun s => IsRedOrdered s

omit [DecidableEq I] in
theorem mem_redOrderedSet {μ : Multiset (I ⊕ Fin n)} {s : Seq μ} :
    s ∈ redOrderedSet μ ↔ IsRedOrdered s := by
  classical
  simp [redOrderedSet]

omit [DecidableEq I] in
theorem isRedOrdered_cast {μ μ' : Multiset (I ⊕ Fin n)} (h : μ = μ') (s : Seq μ) :
    IsRedOrdered (Seq.cast h s) ↔ IsRedOrdered s := by
  subst h; rfl

omit [DecidableEq I] in
/-- Appending a black strand does not change the red order. -/
theorem isRedOrdered_append_black {μ : Multiset (I ⊕ Fin n)} (c : I) (s : Seq μ)
    (t : Seq ({Sum.inl c} : Multiset (I ⊕ Fin n))) :
    IsRedOrdered (s.append t) ↔ IsRedOrdered s := by
  have hcard : Multiset.card (μ + {Sum.inl c}) = Multiset.card μ + 1 := by simp
  have hlbl : ∀ a : Fin (Multiset.card (μ + {Sum.inl c})), Multiset.card μ ≤ a.val →
      (s.append t).lbl a = Sum.inl c := fun a ha => by
    rw [Seq.lbl, Seq.append_apply_ge _ _ _ ha]
    exact Multiset.mem_singleton.1 (t.mem _)
  constructor
  · intro h a b r r' hab ha hb
    refine h ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ r r' hab ?_ ?_
    · rw [Seq.lbl, Seq.append_apply_lt _ _ _ a.2]; exact ha
    · rw [Seq.lbl, Seq.append_apply_lt _ _ _ b.2]; exact hb
  · intro h a b r r' hab ha hb
    have hb' : b.val < Multiset.card μ := by
      by_contra hc
      rw [hlbl b (by omega)] at hb
      exact Sum.inl_ne_inr hb
    have ha' : a.val < Multiset.card μ := lt_trans hab hb'
    refine h ⟨a.val, ha'⟩ ⟨b.val, hb'⟩ r r' hab ?_ ?_
    · rw [Seq.lbl, Seq.append_apply_lt _ _ _ ha'] at ha; exact ha
    · rw [Seq.lbl, Seq.append_apply_lt _ _ _ hb'] at hb; exact hb

variable {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin n → I →₀ ℕ}

local notation "S" => stendhalQ Q Λ

theorem castKLR_eSum_redOrderedSet {μ μ' : Multiset (I ⊕ Fin n)} (h : μ = μ') :
    castKLR S h (eSum S (redOrderedSet μ)) = eSum S (redOrderedSet μ') :=
  castKLR_eSum_of_mem_iff h fun s => by
    rw [mem_redOrderedSet, mem_redOrderedSet, isRedOrdered_cast]


variable (ν₀ ν₀' : Multiset (I ⊕ Fin n)) (c : I)

local notation "j" => (Sum.inl c : I ⊕ Fin n)

/-- **`P 1_{-,i} = ι(P₂ ⊗ 1_i)`** for the red-ordered idempotents `P`, `P₂` and a black
label `i`. -/
theorem eSum_redOrderedSet_mul_lastIdem :
    eSum S (redOrderedSet (ν₀ + {j} + (ν₀' + {j}))) * lastIdem S ν₀ ν₀' j =
      castKLR S (add_assoc (ν₀ + {j}) ν₀' {j})
        (appendR S (ν₀ + {j} + ν₀') j (eSum S (redOrderedSet (ν₀ + {j} + ν₀')))) := by
  rw [← castKLR_eSum_redOrderedSet (add_assoc (ν₀ + {j}) ν₀' {j}), lastIdem, ← map_mul,
    appendR_apply, eSum_mul_oneConcat_singleton]
  intro a
  rw [mem_redOrderedSet, mem_redOrderedSet, isRedOrdered_append_black]

/-- **The red-ordered idempotent commutes with `1_{-,i}`.** -/
theorem commute_eSum_redOrderedSet_lastIdem :
    Commute (eSum S (redOrderedSet (ν₀ + {j} + (ν₀' + {j})))) (lastIdem S ν₀ ν₀' j) := by
  rw [← castKLR_eSum_redOrderedSet (add_assoc (ν₀ + {j}) ν₀' {j}), lastIdem, oneConcat]
  exact (commute_eSum_eSum _ _).map _

end Categorification.Stendhal
