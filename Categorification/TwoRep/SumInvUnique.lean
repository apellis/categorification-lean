/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqSl2

/-!
# Uniqueness of explicit inverses

An explicit inverse of `(f, g 0, …, g (n-1))` (`SumInvTo`, `SumInvFrom`) is an inverse of an
isomorphism, so its components are determined by `f` and the `g m`. This lets one compare the
leftward cups and caps of two Rouquier data (Brundan (1.14)–(1.18)) without unfolding the way the
inverses were built.
-/

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits

variable {D : Type*} [Category D] [Preadditive D] {X Y Z : D} {n : ℕ}

/-- The component `f'` of an explicit inverse is determined by `f` and the `g m`. -/
theorem SumInvTo.f'_eq {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)} (S T : SumInvTo f g n) : S.f' = T.f' := by
  calc S.f' = S.f' ≫ (f ≫ T.f' + ∑ m ∈ Finset.range n, g m ≫ T.g' m) := by
        rw [T.total, Category.comp_id]
    _ = T.f' := by
        rw [Preadditive.comp_add, Preadditive.comp_sum, reassoc_of% S.ff,
          Finset.sum_eq_zero fun m hm => by
            rw [reassoc_of% (S.fg m (Finset.mem_range.1 hm)), zero_comp], add_zero]

/-- The components `g' m`, `m < n`, of an explicit inverse are determined by `f` and the `g m`. -/
theorem SumInvTo.g'_eq {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)} (S T : SumInvTo f g n) {m : ℕ}
    (hm : m < n) : S.g' m = T.g' m := by
  calc S.g' m = S.g' m ≫ (f ≫ T.f' + ∑ m' ∈ Finset.range n, g m' ≫ T.g' m') := by
        rw [T.total, Category.comp_id]
    _ = ∑ m' ∈ Finset.range n, (if m = m' then T.g' m' else 0) := by
        rw [Preadditive.comp_add, Preadditive.comp_sum, reassoc_of% (S.gf m hm), zero_comp,
          zero_add]
        refine Finset.sum_congr rfl fun m' hm' => ?_
        rw [reassoc_of% (S.gg m m' hm (Finset.mem_range.1 hm'))]
        split_ifs <;> simp
    _ = T.g' m := by rw [Finset.sum_ite_eq]; simp [hm]

/-- The component `f'` of an explicit inverse is determined by `f` and the `g m`. -/
theorem SumInvFrom.f'_eq {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)} (S T : SumInvFrom f g n) :
    S.f' = T.f' := by
  calc S.f' = (T.f' ≫ f + ∑ m ∈ Finset.range n, T.g' m ≫ g m) ≫ S.f' := by
        rw [T.total, Category.id_comp]
    _ = T.f' := by
        rw [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc, S.ff, Category.comp_id,
          Finset.sum_eq_zero fun m hm => by
            rw [Category.assoc, S.gf m (Finset.mem_range.1 hm), comp_zero], add_zero]

/-- The components `g' m`, `m < n`, of an explicit inverse are determined by `f` and the `g m`. -/
theorem SumInvFrom.g'_eq {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)} (S T : SumInvFrom f g n) {m : ℕ}
    (hm : m < n) : S.g' m = T.g' m := by
  calc S.g' m = (T.f' ≫ f + ∑ m' ∈ Finset.range n, T.g' m' ≫ g m') ≫ S.g' m := by
        rw [T.total, Category.id_comp]
    _ = ∑ m' ∈ Finset.range n, (if m' = m then T.g' m' else 0) := by
        rw [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc, S.fg m hm, comp_zero,
          zero_add]
        refine Finset.sum_congr rfl fun m' hm' => ?_
        rw [Category.assoc, S.gg m' m (Finset.mem_range.1 hm') hm]
        split_ifs <;> simp
    _ = T.g' m := by rw [Finset.sum_ite_eq']; simp [hm]

end Categorification.TwoRep
