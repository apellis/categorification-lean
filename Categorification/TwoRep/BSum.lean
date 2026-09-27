/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Basic

/-!
# Finite direct sums indexed by `ℕ`: summand inclusions and projections

The direct sums `⊕_{[n]} 1_λ` of CL §2.1.2 are `qsum d n X = lsum ((List.range n).map _)`
(`Basic.lean`), a nested biproduct. To speak about *the* summand `X⟨d(n-1-2j)⟩` (its inclusion and
projection), as CL do throughout §3 ("the inclusion of `1_{n+2}` into the lowest degree summand",
"the projection out of the top degree summand", the matrix of a map between such sums), we use
the equivalent form `bsum f n = f (n-1) ⊞ (f (n-2) ⊞ (⋯ ⊞ 0))` of the sum of `f 0, …, f (n-1)`:

* `bsumι f n j : f j ⟶ bsum f n`, `bsumπ f n j : bsum f n ⟶ f j` (zero for `j ≥ n`);
* `bsumι_π_self`, `bsumι_π_ne`, `bsum_total`: the biproduct identities
  `ι_j π_j = 1`, `ι_j π_{j'} = 0` (`j ≠ j'`), `∑_j π_j ι_j = 1`;
* `bsumIsoQsum : bsum (fun j => X⟦d (n-1-2j)⟧) n ≅ qsum d n X`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

open ZeroObject

/-- The direct sum `f (n-1) ⊞ (⋯ ⊞ (f 0 ⊞ 0))`. -/
def bsum (f : ℕ → C) : ℕ → C
  | 0 => 0
  | n + 1 => f n ⊞ bsum f n

@[simp] theorem bsum_zero (f : ℕ → C) : bsum f 0 = 0 := rfl

@[simp] theorem bsum_succ (f : ℕ → C) (n : ℕ) : bsum f (n + 1) = (f n ⊞ bsum f n) := rfl

/-- The inclusion of the `j`-th summand (zero if `j ≥ n`). -/
def bsumι (f : ℕ → C) : (n j : ℕ) → (f j ⟶ bsum f n)
  | 0, _ => 0
  | n + 1, j =>
    if h : j = n then eqToHom (congrArg f h) ≫ biprod.inl else bsumι f n j ≫ biprod.inr

/-- The projection onto the `j`-th summand (zero if `j ≥ n`). -/
def bsumπ (f : ℕ → C) : (n j : ℕ) → (bsum f n ⟶ f j)
  | 0, _ => 0
  | n + 1, j =>
    if h : j = n then biprod.fst ≫ eqToHom (congrArg f h).symm else biprod.snd ≫ bsumπ f n j

theorem bsumι_π_self (f : ℕ → C) : ∀ (n j : ℕ), j < n → bsumι f n j ≫ bsumπ f n j = 𝟙 (f j)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, j, h => by
    by_cases hj : j = n
    · subst hj
      simp [bsumι, bsumπ]
    · simp only [bsumι, bsumπ, dif_neg hj, Category.assoc, biprod.inr_snd_assoc]
      exact bsumι_π_self f n j (by omega)

theorem bsumι_π_ne (f : ℕ → C) : ∀ (n j j' : ℕ), j ≠ j' → bsumι f n j ≫ bsumπ f n j' = 0
  | 0, _, _, _ => by simp [bsumι]
  | n + 1, j, j', h => by
    by_cases hj : j = n
    · subst hj
      have hj' : ¬ j' = j := fun e => h e.symm
      simp [bsumι, bsumπ, hj']
    · by_cases hj' : j' = n
      · subst hj'
        simp [bsumι, bsumπ, hj]
      · simp only [bsumι, bsumπ, dif_neg hj, dif_neg hj', Category.assoc, biprod.inr_snd_assoc]
        exact bsumι_π_ne f n j j' h

theorem bsumπ_of_le (f : ℕ → C) : ∀ (n j : ℕ), n ≤ j → bsumπ f n j = 0
  | 0, _, _ => by simp [bsumπ]
  | n + 1, j, h => by
    have hj : ¬ j = n := by omega
    simp only [bsumπ, dif_neg hj, bsumπ_of_le f n j (by omega), comp_zero]

theorem bsumι_of_le (f : ℕ → C) : ∀ (n j : ℕ), n ≤ j → bsumι f n j = 0
  | 0, _, _ => by simp [bsumι]
  | n + 1, j, h => by
    have hj : ¬ j = n := by omega
    simp only [bsumι, dif_neg hj, bsumι_of_le f n j (by omega), zero_comp]

theorem bsum_total (f : ℕ → C) :
    ∀ n : ℕ, ∑ j ∈ Finset.range n, bsumπ f n j ≫ bsumι f n j = 𝟙 (bsum f n)
  | 0 => (isZero_zero C).eq_of_src _ _
  | n + 1 => by
    rw [Finset.sum_range_succ]
    have h1 : ∀ j ∈ Finset.range n, bsumπ f (n + 1) j ≫ bsumι f (n + 1) j =
        biprod.snd ≫ (bsumπ f n j ≫ bsumι f n j) ≫ biprod.inr := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hj' : ¬ j = n := by omega
      simp [bsumι, bsumπ, hj']
    rw [Finset.sum_congr rfl h1, ← Preadditive.comp_sum, ← Preadditive.sum_comp, bsum_total f n,
      Category.id_comp]
    have h2 : bsumπ f (n + 1) n ≫ bsumι f (n + 1) n = biprod.fst ≫ biprod.inl := by
      simp [bsumι, bsumπ]
    rw [h2]
    exact (add_comm _ _).trans biprod.total

/-- `lsum [X] ≅ X`. -/
def lsumSingletonIso (X : C) : lsum [X] ≅ X where
  hom := biprod.fst
  inv := biprod.lift (𝟙 X) 0
  hom_inv_id := by
    apply biprod.hom_ext
    · simp
    · simp only [Category.assoc, biprod.lift_snd, comp_zero, Category.id_comp]
      exact (isZero_zero C).eq_of_tgt _ _
  inv_hom_id := by simp

/-- `lsum (L ++ L') ≅ lsum L ⊞ lsum L'`. -/
def lsumAppendIso : ∀ (L L' : List C), lsum (L ++ L') ≅ lsum L ⊞ lsum L'
  | [], L' =>
    { hom := biprod.lift 0 (𝟙 _)
      inv := biprod.snd
      hom_inv_id := by simp
      inv_hom_id := by
        apply biprod.hom_ext
        · simp only [Category.assoc, biprod.lift_fst, comp_zero, Category.id_comp]
          exact (isZero_zero C).eq_of_tgt _ _
        · simp }
  | X :: L, L' =>
    biprod.mapIso (Iso.refl X) (lsumAppendIso L L') ≪≫ (biprod.associator X (lsum L) (lsum L')).symm

/-- `bsum g n ≅ lsum ((List.range n).map g)`. -/
def bsumIsoLsumRange (g : ℕ → C) : ∀ n : ℕ, bsum g n ≅ lsum ((List.range n).map g)
  | 0 => Iso.refl _
  | n + 1 => by
    refine biprod.mapIso (Iso.refl _) (bsumIsoLsumRange g n) ≪≫ biprod.braiding _ _ ≪≫ ?_
    rw [List.range_succ, List.map_append, List.map_singleton]
    exact biprod.mapIso (Iso.refl _) (lsumSingletonIso _).symm ≪≫ (lsumAppendIso _ _).symm

variable [HasShift C ℤ]

/-- `bsum (fun j => X⟦d (n-1-2j)⟧) n ≅ qsum d n X`. -/
def bsumIsoQsum (d : ℤ) (n : ℕ) (X : C) :
    bsum (fun j : ℕ => X⟦d * ((n : ℤ) - 1 - 2 * (j : ℤ))⟧) n ≅ qsum d n X :=
  bsumIsoLsumRange _ n

end Categorification.TwoRep
