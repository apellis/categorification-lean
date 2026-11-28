/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqSl2

/-!
# Changing the summand maps of an explicit inverse

Rouquier's invertibility conditions (`TwoRep.RouqLoc`; Brundan, arXiv:1501.00350v1, (1.8),
(1.9)) are stated as explicit inverses `SumInvTo`, `SumInvFrom` of maps into or out of a sum
`Y ⊕ Z^{⊕ n}` with prescribed summand maps. Presentations such as Cautis–Lauda's give such an
inverse for other summand maps (dotted caps corrected by bubbles, or indexed in the opposite
order). This file provides the changes of summand maps needed to pass between them.

* `SumInvTo.ofEqs`, `SumInvFrom.ofEqs`: an explicit inverse from four of its five equations (the
  remaining one follows).
* `SumInvTo.changeSummands`: replace the summand maps `g` by `g₂` with `g t = ∑ₛ g₂ s ≫ B s t`.
* `SumInvFrom.reindex`: reindex the summand maps along an involution of `{0, …, n - 1}`.
-/

namespace Categorification.TwoRep

open CategoryTheory Limits

variable {D : Type*} [Category D] [Preadditive D]

/-- An explicit inverse of `(f, g)` from `total`, `ff`, `gf` and `gg`: the equation `fg` follows. -/
def SumInvTo.ofEqs {X Y Z : D} {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)} {n : ℕ} (f' : Y ⟶ X)
    (g' : ℕ → (Z ⟶ X)) (total : f ≫ f' + ∑ m ∈ Finset.range n, g m ≫ g' m = 𝟙 X)
    (ff : f' ≫ f = 𝟙 Y) (gf : ∀ m, m < n → g' m ≫ f = 0)
    (gg : ∀ m m', m < n → m' < n → g' m ≫ g m' = if m = m' then 𝟙 Z else 0) :
    SumInvTo f g n where
  f' := f'
  g' := g'
  total := total
  ff := ff
  fg t ht := by
    have h := congrArg (fun φ => f' ≫ φ ≫ g t) total
    simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
      Preadditive.comp_sum, Category.assoc, Category.id_comp] at h
    rw [reassoc_of% ff, Finset.sum_eq_single t] at h
    · rw [gg t t ht ht] at h
      simpa using h
    · intro s hs hst
      rw [gg s t (Finset.mem_range.1 hs) ht]
      simp [hst]
    · intro h'; exact absurd (Finset.mem_range.2 ht) h'
  gf := gf
  gg := gg

/-- An explicit inverse of `(f, g)` from `total`, `ff`, `gf` and `gg`: the equation `fg` follows. -/
def SumInvFrom.ofEqs {X Y Z : D} {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)} {n : ℕ} (f' : X ⟶ Y)
    (g' : ℕ → (X ⟶ Z)) (total : f' ≫ f + ∑ m ∈ Finset.range n, g' m ≫ g m = 𝟙 X)
    (ff : f ≫ f' = 𝟙 Y) (gf : ∀ m, m < n → g m ≫ f' = 0)
    (gg : ∀ m m', m < n → m' < n → g m ≫ g' m' = if m = m' then 𝟙 Z else 0) :
    SumInvFrom f g n where
  f' := f'
  g' := g'
  total := total
  ff := ff
  fg t ht := by
    have h := congrArg (fun φ => f ≫ φ ≫ g' t) total
    simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
      Preadditive.comp_sum, Category.assoc, Category.id_comp] at h
    rw [reassoc_of% ff, Finset.sum_eq_single t] at h
    · rw [gg t t ht ht] at h
      simpa using h
    · intro s hs hst
      rw [gg s t (Finset.mem_range.1 hs) ht]
      simp [hst]
    · intro h'; exact absurd (Finset.mem_range.2 ht) h'
  gf := gf
  gg := gg

/-- **Changing the summand maps of an explicit inverse into a sum**: if `g t = ∑ₛ g₂ s ≫ B s t`
and the maps `∑ₜ B s t ≫ g' t` are left inverse to the `g₂ s'`, then `(f, g₂)` is invertible with
these as the new summand components. -/
def SumInvTo.changeSummands {X Y Z : D} {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)} {n : ℕ}
    (S : SumInvTo f g n) (g₂ : ℕ → (X ⟶ Z)) (B : ℕ → ℕ → (Z ⟶ Z))
    (hg : ∀ t, t < n → g t = ∑ s ∈ Finset.range n, g₂ s ≫ B s t)
    (hgg : ∀ s s', s < n → s' < n →
      (∑ t ∈ Finset.range n, B s t ≫ S.g' t) ≫ g₂ s' = if s = s' then 𝟙 Z else 0) :
    SumInvTo f g₂ n :=
  SumInvTo.ofEqs S.f' (fun s => ∑ t ∈ Finset.range n, B s t ≫ S.g' t)
    (by
      rw [← S.total]
      congr 1
      simp only [Preadditive.comp_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [hg t (Finset.mem_range.1 ht), Preadditive.sum_comp]
      simp only [Category.assoc])
    S.ff
    (fun s _ => by
      simp only [Preadditive.sum_comp, Category.assoc]
      exact Finset.sum_eq_zero fun t ht => by rw [S.gf t (Finset.mem_range.1 ht), comp_zero])
    hgg

/-- **Reindexing the summand maps of an explicit inverse out of a sum** along the involution
`m ↦ n - 1 - m` of `{0, …, n - 1}`. -/
def SumInvFrom.reindex {X Y Z : D} {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)} {n : ℕ}
    (S : SumInvFrom f g n) (g₂ : ℕ → (Z ⟶ X)) (hg : ∀ m, m < n → g₂ m = g (n - 1 - m)) :
    SumInvFrom f g₂ n where
  f' := S.f'
  g' m := S.g' (n - 1 - m)
  total := by
    rw [← S.total, ← Finset.sum_range_reflect]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.1 hm
    rw [hg _ (by omega), show n - 1 - (n - 1 - m) = m by omega]
  ff := S.ff
  fg m hm := S.fg _ (by omega)
  gf m hm := by rw [hg m hm]; exact S.gf _ (by omega)
  gg m m' hm hm' := by
    rw [hg m hm, S.gg _ _ (by omega) (by omega)]
    by_cases h : m = m'
    · simp [h]
    · rw [ite_eq_right (by omega), ite_eq_right h]

end Categorification.TwoRep
