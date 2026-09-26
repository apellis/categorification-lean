/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.IdempotentEquiv
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.BigOperators

/-!
# Finite orthogonal families of idempotents

Background for M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum
groups II*, arXiv:0804.2080v1, §3, Proposition 6 and Corollary 7: a direct sum
`⊕_{a ∈ s} e_a A` of right projectives attached to pairwise orthogonal idempotents `e_a` is the
right ideal `e A` of their sum `e = ∑_a e_a` (`rIdealSumEquiv`); likewise for left ideals
(`lIdealSumEquiv`) and for the subspaces `e M` of a module (`fixSubSumEquiv`).
-/

namespace Categorification

open MulOpposite

variable {A : Type*} [Ring A] {ι : Type*} [DecidableEq ι]

/-- A finite family of pairwise orthogonal idempotents: `e_a e_b = δ_{ab} e_a` for `a, b ∈ s`. -/
def IsOrthFamily (s : Finset ι) (e : ι → A) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, e a * e b = if a = b then e a else 0

namespace IsOrthFamily

variable {s : Finset ι} {e : ι → A} (h : IsOrthFamily s e)
include h

theorem idem {a : ι} (ha : a ∈ s) : IsIdempotentElem (e a) := by
  have := h a ha a ha; rwa [if_pos rfl] at this

theorem mul_sum {a : ι} (ha : a ∈ s) : e a * ∑ b ∈ s, e b = e a := by
  rw [Finset.mul_sum, Finset.sum_eq_single a (fun b hb hba => by rw [h a ha b hb, if_neg
    (Ne.symm hba)]) (fun h' => absurd ha h'), (h.idem ha).eq]

theorem sum_mul {a : ι} (ha : a ∈ s) : (∑ b ∈ s, e b) * e a = e a := by
  rw [Finset.sum_mul, Finset.sum_eq_single a (fun b hb hba => by rw [h b hb a ha, if_neg hba])
    (fun h' => absurd ha h'), (h.idem ha).eq]

theorem sum_idem : IsIdempotentElem (∑ b ∈ s, e b) := by
  rw [IsIdempotentElem, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a ha => h.mul_sum ha

end IsOrthFamily

section ideals

variable {s : Finset ι} {e : ι → A} (h : IsOrthFamily s e)

/-- `(∑_{a ∈ s} e_a) A ≅ ⊕_{a ∈ s} e_a A` (right `A`-modules), `y ↦ (e_a y)_a`. -/
def rIdealSumEquiv : rIdeal (∑ a ∈ s, e a) ≃ₗ[Aᵐᵒᵖ] ((a : s) → rIdeal (e a)) where
  toFun y a := ⟨e a * (y : A), by rw [mem_rIdeal, ← mul_assoc, (h.idem a.2).eq]⟩
  invFun z := ⟨∑ a : s, (z a : A), by
    rw [mem_rIdeal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← (z a).2, ← mul_assoc, h.sum_mul a.2]⟩
  map_add' x y := by ext; simp [mul_add]
  map_smul' c x := by ext; simp [smul_eq_mul_unop, mul_assoc]
  left_inv y := Subtype.ext (by
    change ∑ a : s, e a * (y : A) = y
    rw [← Finset.sum_mul, Finset.sum_coe_sort s e]; exact y.2)
  right_inv z := by
    funext a
    apply Subtype.ext
    change e a * ∑ b : s, (z b : A) = z a
    rw [Finset.mul_sum, Finset.sum_eq_single a (fun b _ hba => by
      rw [← (z b).2, ← mul_assoc, h a a.2 b b.2, if_neg (fun h' => hba (Subtype.ext h').symm),
        zero_mul]) (fun h' => absurd (Finset.mem_univ a) h'), (z a).2]

/-- `A (∑_{a ∈ s} e_a) ≅ ⊕_{a ∈ s} A e_a` (left `A`-modules), `y ↦ (y e_a)_a`. -/
def lIdealSumEquiv : lIdeal (∑ a ∈ s, e a) ≃ₗ[A] ((a : s) → lIdeal (e a)) where
  toFun y a := ⟨(y : A) * e a, by rw [mem_lIdeal, mul_assoc, (h.idem a.2).eq]⟩
  invFun z := ⟨∑ a : s, (z a : A), by
    rw [mem_lIdeal, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← (z a).2, mul_assoc, h.mul_sum a.2]⟩
  map_add' x y := by ext; simp [add_mul]
  map_smul' c x := by ext; simp [mul_assoc]
  left_inv y := Subtype.ext (by
    change ∑ a : s, (y : A) * e a = y
    rw [← Finset.mul_sum, Finset.sum_coe_sort s e]; exact y.2)
  right_inv z := by
    funext a
    apply Subtype.ext
    change (∑ b : s, (z b : A)) * e a = z a
    rw [Finset.sum_mul, Finset.sum_eq_single a (fun b _ hba => by
      rw [← (z b).2, mul_assoc, h b b.2 a a.2, if_neg (fun h' => hba (Subtype.ext h')),
        mul_zero]) (fun h' => absurd (Finset.mem_univ a) h'), (z a).2]

variable (k : Type*) [CommRing k] [Algebra k A] (M : Type*) [AddCommGroup M] [Module A M]
  [Module k M] [IsScalarTower k A M]

/-- `(∑_{a ∈ s} e_a) M ≅ ⊕_{a ∈ s} e_a M` for a left `A`-module `M`, `m ↦ (e_a m)_a`. -/
def fixSubSumEquiv : fixSub k M (∑ a ∈ s, e a) ≃ₗ[k] ((a : s) → fixSub k M (e a)) where
  toFun m a := ⟨e a • (m : M), smul_mem_fixSub (h.idem a.2) _⟩
  invFun z := ⟨∑ a : s, (z a : M), by
    rw [mem_fixSub, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← (z a).2, smul_smul, h.sum_mul a.2]⟩
  map_add' x y := by ext; simp [smul_add]
  map_smul' c x := by ext; simp [smul_comm _ c]
  left_inv m := Subtype.ext (by
    change ∑ a : s, e a • (m : M) = m
    rw [← Finset.sum_smul, Finset.sum_coe_sort s e]; exact m.2)
  right_inv z := by
    funext a
    apply Subtype.ext
    change e a • ∑ b : s, (z b : M) = z a
    rw [Finset.smul_sum, Finset.sum_eq_single a (fun b _ hba => by
      rw [← (z b).2, smul_smul, h a a.2 b b.2, if_neg (fun h' => hba (Subtype.ext h').symm),
        zero_smul]) (fun h' => absurd (Finset.mem_univ a) h'), (z a).2]

end ideals

/-- The image of an orthogonal family under an additive anti-homomorphism is orthogonal. -/
theorem IsOrthFamily.map_anti {s : Finset ι} {e : ι → A} (h : IsOrthFamily s e) (φ : A → A)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hφ : ∀ x y, φ (x * y) = φ y * φ x) :
    IsOrthFamily s (fun a => φ (e a)) := by
  intro a ha b hb
  rw [← hφ, h b hb a ha]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg (Ne.symm hab), if_neg hab]
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this

end Categorification
