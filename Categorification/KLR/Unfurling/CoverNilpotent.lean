/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.CoverFamily
import Categorification.KLR.CyclotomicAction.GlobalNilpotent
import Categorification.TwoRep.RouqProductNilpotent

/-!
# Nilpotent dots in the cyclotomic families of the unfurled graph

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`. The action of `g` on the representation of `g̃` sends the dot
of the colour `i` on the summand of the label `a = (i, u)` to `ϖ_a(ỹ) = u (1 + ỹ)^{d_i}`, a power
series in the dot `ỹ` of `g̃`. It makes sense because `ỹ` is nilpotent on each weight space
(undeformed cyclotomic quotients; Brundan–Kleshchev, arXiv:0808.2032v3, Lemma 2.1).

* `unfQ_aeval_zero`: `Q_{ab}(0, v) = ±v^{n_{ab} + n_{ba}}`, the hypothesis of
  `CyclotomicAction.dot_pow_eq_zero`.
* `coverWeight_weightBlocks_subsingleton`: for the root-graded weight datum `coverWeight`, each
  weight has at most one block `R^Λ(β)`.
* `coverFamily_dot_nilpotent`, `coverProduct_dot_nilpotent`: some power of the dot of
  `coverFamily n Λ`, and of the product family `coverProduct`, vanishes on each `E_a`.
-/

open MvPolynomial CategoryTheory

noncomputable section

namespace Categorification.KLR.Unfurling

open QuantumGroup QuantumGroup.UDot TwoRep CyclotomicAction

universe u v w

variable {J : Type u} (n : J → J → ℕ)

/-- `Q_{ab}(0, v) = (-1)^{n_{ab}} v^{n_{ab} + n_{ba}}`. -/
theorem unfQ_aeval_zero {k : Type*} [CommRing k] (a b : J) :
    ∃ (c : k) (d : ℕ), IsUnit c ∧
      aeval (![0, X 1] : Fin 2 → MvPolynomial (Fin 2) k) (unfQ (k := k) n a b) =
        C c * X 1 ^ d := by
  refine ⟨(-1) ^ n a b, n a b + n b a, (isUnit_neg_one (α := k)).pow _, ?_⟩
  simp only [unfQ, unfP, map_mul, map_pow, map_sub, aeval_rename, aeval_X, Function.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, map_one]
  rw [zero_sub, sub_zero, neg_pow, pow_add]
  ring

variable [DecidableEq J]

theorem coverWeight_sum_snd_apply (β : Multiset J) (c : J) :
    ((β.map (coverWeight n).iX).sum).2 c = β.count c := by
  induction β using Multiset.induction_on with
  | empty => simp
  | cons b β ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Prod.snd_add, Finsupp.add_apply, ih,
      coverWeight_iX, Multiset.count_cons, Finsupp.single_apply]
    by_cases hbc : b = c
    · subst hbc
      simp [add_comm]
    · simp [hbc, Ne.symm hbc]

/-- For the root-graded weight datum `coverWeight`, each weight has at most one block. -/
theorem coverWeight_weightBlocks_subsingleton (Λ x : (J → ℤ) × (J →₀ ℤ)) :
    Subsingleton (WeightBlocks (coverWeight n) Λ x) := by
  refine ⟨fun β β' => Subtype.ext (Multiset.ext.2 fun c => ?_)⟩
  have h := congrArg (fun y => (y + Λ).2 c) (β.2.trans β'.2.symm)
  simp only [blockWeight, sub_add_cancel, coverWeight_sum_snd_apply] at h
  exact_mod_cast h

variable {L : Type v} [Field L] (Λ : J → ℕ)

/-- **The dots of the cyclotomic family of the unfurled graph are nilpotent** on each `E_a`
(Brundan–Kleshchev, arXiv:0808.2032v3, Lemma 2.1, on the single block of each weight). -/
theorem coverFamily_dot_nilpotent (a : J) {x y : (J → ℤ) × (J →₀ ℤ)}
    (h : x + (coverWeight n).iX a = y) :
    ∃ N : ℕ, powComp ((coverFamily.{u, v, w} n (L := L) Λ).dot a h) N = 0 :=
  globalDot_powComp_eq_zero.{u, v, w} (coverWeight n) _
    (fun a b _ => unfQ_aeval_zero n a b) Λ
    (coverWeight_weightBlocks_subsingleton n _) a h

variable {J₂ : Type u} [DecidableEq J₂] (n₂ : J₂ → J₂ → ℕ) (Λ₂ : J₂ → ℕ)

/-- **The dots of the product family `coverProduct` are nilpotent** on each 1-morphism. -/
theorem coverProduct_dot_nilpotent :
    ∀ (c : J ⊕ J₂) {x y} (h : x + ((coverWeight n).prod (coverWeight n₂)).iX c = y),
      ∃ N : ℕ, powComp ((coverProduct.{u, v, w} n (L := L) Λ n₂ Λ₂).dot c h) N = 0 :=
  RouqFamily.homProduct_dot_nilpotent L _ _ (fun a _ _ h => coverFamily_dot_nilpotent n Λ a h)
    (fun a _ _ h => coverFamily_dot_nilpotent n₂ Λ₂ a h)

end Categorification.KLR.Unfurling

end
