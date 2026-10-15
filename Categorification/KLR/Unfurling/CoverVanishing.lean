/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.CoverNilpotent
import Categorification.TwoRep.RouqVanishing

/-!
# Labels acting by zero in the cyclotomic family of the unfurled graph

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`. The generators `E_i`, `F_i` of `g` act on the representation
of `g̃` as direct sums over the labels `a` over `i`, and the labels are infinite in number. At
the block `R^Λ(β)`, a label `a` with `Λ_a = 0` that does not occur in `β` and has no arrows to
the labels of `β` acts by zero (`coverFamily_isZero_E`):

* `F_a` out of the block lands in an empty product of categories (there is no block `β - a`);
* the weight of the block at `a` is `-Λ_a + Σ_{b ∈ β} a · b = 0`;
* so `E_a` vanishes by Rouquier's invertibility at weight zero
  (`RouqFamily.isZero_E_of_isZero_F`).

Hence only the finitely many labels occurring in `β` or `Λ`, or adjacent to `β`, act at the
block `β`.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Categorification.KLR

namespace CyclotomicAction

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  {C : QuantumGroup.CartanDatum I} {Xw Yw : Type u₁} [AddCommGroup Xw] [AddCommGroup Yw]
  (RD : QuantumGroup.UDot.WeightDatum C Xw Yw) (Λ : Xw)

/-- A 1-morphism into a weight space without blocks is zero. -/
theorem isZero_to_weightSpace {D : TwoRep.LinearCat k} {x : Xw}
    (hx : IsEmpty (WeightBlocks RD Λ x)) (G : D ⟶ weightSpace.{u, v, w} Q a RD Λ x) : IsZero G := by
  rw [IsZero.iff_id_eq_zero]
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun M => funext fun β => ?_))
  exact isEmptyElim β

/-- A 1-morphism out of a weight space without blocks is zero: the source is a single zero
object. -/
theorem isZero_from_weightSpace {D : TwoRep.LinearCat k} {x : Xw}
    (hx : IsEmpty (WeightBlocks RD Λ x)) (G : weightSpace.{u, v, w} Q a RD Λ x ⟶ D) :
    IsZero G := by
  rw [IsZero.iff_id_eq_zero]
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun M => ?_))
  have hM : 𝟙 M = 0 := funext fun β => isEmptyElim β
  change 𝟙 (G.obj.obj M) = 0
  rw [← G.obj.map_id, hM, Functor.map_zero]

end CyclotomicAction

namespace Unfurling

open QuantumGroup QuantumGroup.UDot TwoRep CyclotomicAction

universe u v w

variable {J : Type u} [DecidableEq J] (n : J → J → ℕ) {L : Type v} [Field L] (Λ : J → ℕ)

theorem coverWeight_sum_fst_apply (β : Multiset J) (a : J) :
    ((β.map (coverWeight n).iX).sum).1 a = (β.map fun c => (coverCartan n).dot a c).sum := by
  induction β using Multiset.induction_on with
  | empty => simp
  | cons b β ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Prod.fst_add, Pi.add_apply, ih, coverWeight_iX,
      Multiset.map_cons, Multiset.sum_cons]

/-- The weight of a block at a label `a` that does not occur in it, carries no weight and has no
arrows to its labels is zero. -/
theorem blockWeight_apply_eq_zero (β : Multiset J) {a : J} (ha : a ∉ β) (hΛ : Λ a = 0)
    (hn : ∀ b ∈ β, n a b = 0 ∧ n b a = 0) :
    (blockWeight (coverWeight n) ((fun j => (Λ j : ℤ)), 0) β).1 a = 0 := by
  simp only [blockWeight, Prod.fst_sub, Pi.sub_apply, hΛ, Nat.cast_zero, sub_zero]
  rw [coverWeight_sum_fst_apply]
  refine Multiset.sum_eq_zero fun t ht => ?_
  obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 ht
  have hac : a ≠ c := fun e => ha (e ▸ hc)
  rw [coverCartan_dot_of_ne n hac, (hn c hc).1, (hn c hc).2]
  rfl

/-- **A label with no weight, absent from the block and without arrows to it, acts by zero**
on the block: `E_a` and `F_a` out of the weight space of `β` vanish. -/
theorem coverFamily_isZero_E (b : J) {x y : (J → ℤ) × (J →₀ ℤ)}
    (h : x + (coverWeight n).iX b = y)
    (hx : ∀ β : WeightBlocks (coverWeight n) ((fun j => (Λ j : ℤ)), 0) x,
      b ∉ β.1 ∧ ∀ c ∈ β.1, n b c = 0 ∧ n c b = 0)
    (hΛ : Λ b = 0) :
    IsZero ((coverFamily.{u, v, w} n (L := L) Λ).E b h) ∧
      IsZero ((coverFamily.{u, v, w} n (L := L) Λ).F b h) := by
  have h₁ : (x - (coverWeight n).iX b) + (coverWeight n).iX b = x := sub_add_cancel _ _
  have hz : IsEmpty (WeightBlocks (coverWeight n) ((fun j => (Λ j : ℤ)), 0)
      (x - (coverWeight n).iX b)) := by
    refine ⟨fun γ => ?_⟩
    exact (hx (blockSucc (coverWeight n) _ b h₁ γ)).1 (by
      rw [blockSucc_val]
      exact Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self b)))
  by_cases hne : Nonempty (WeightBlocks (coverWeight n) ((fun j => (Λ j : ℤ)), 0) x)
  · obtain ⟨β⟩ := hne
    refine (coverFamily.{u, v, w} n (L := L) Λ).isZero_E_of_isZero_F b h₁ h ?_
      (isZero_to_weightSpace _ _ _ _ hz _)
    rw [coverWeight_pair_iY, ← β.2]
    exact blockWeight_apply_eq_zero n Λ β.1 (hx β).1 hΛ (hx β).2
  · have he : IsEmpty (WeightBlocks (coverWeight n) ((fun j => (Λ j : ℤ)), 0) x) :=
      not_nonempty_iff.1 hne
    exact ⟨isZero_from_weightSpace _ _ _ _ he _, isZero_to_weightSpace _ _ _ _ he _⟩

end Unfurling

end Categorification.KLR
