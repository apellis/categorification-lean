/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEnd

/-!
# Block-diagonal algebra homomorphisms into matrix algebras of morphisms

Let `Z : Idx → C` be a finite family of objects of a `k`-linear category, whose index set is
identified with a product `κ × ι` (`e : κ × ι ≃ Idx`). Suppose that for every block `t : κ` we
are given an algebra homomorphism `φ t : A →ₐ[k] MatEnd (X t)` for a family `X t : ι → C'`, and
a functorial `k`-linear transport `F t i j` of morphisms `X t i ⟶ X t j` to morphisms
`Z (e (t, i)) ⟶ Z (e (t, j))` (compatible with composition and identities, e.g. the placement of
2-morphisms between fixed strands). Then the block-diagonal assembly

`matBlockMap φ F r = ∑_t ∑_{i, j} single (e (t, i)) (e (t, j)) (F t i j (φ t r i j))`

is an algebra homomorphism `A →ₐ[k] MatEnd Z` (`matBlockMap`). This is used to build the action
`α : R(ν) ⊗ R(ν') → END_U(E_{ν,-ν'} 1_λ)` of KL III (3.36) from the actions of `R(ν)` on upward
strands and of `R(ν')` on downward strands.
-/

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory Preadditive

variable {k : Type*} [CommRing k] {C : Type*} [Category C] [Preadditive C] [Linear k C]
  {C' : Type*} [Category C'] [Preadditive C'] [Linear k C']

variable {Idx κ ι : Type*} [Fintype Idx] [DecidableEq Idx] [Fintype κ]
  [Fintype ι] [DecidableEq ι] {Z : Idx → C} (e : κ × ι ≃ Idx) {X : κ → ι → C'}

/-- Functorial transport of morphisms along a block. -/
structure BlockTransport (e : κ × ι ≃ Idx) (X : κ → ι → C') (Z : Idx → C) where
  /-- The transport maps. -/
  F : ∀ t i j, (X t i ⟶ X t j) →ₗ[k] (Z (e (t, i)) ⟶ Z (e (t, j)))
  map_comp : ∀ t i j l (f : X t i ⟶ X t j) (g : X t j ⟶ X t l), F t i l (f ≫ g) = F t i j f ≫ F t j l g
  map_id : ∀ t i, F t i i (𝟙 _) = 𝟙 _

variable {A : Type*} [Ring A] [Algebra k A]

open MatEnd

/-- The underlying linear map of `matBlockMap`. -/
def matBlockMapₗ (T : BlockTransport (k := k) e X Z) (φ : ∀ t, A →ₐ[k] MatEnd (X t)) :
    A →ₗ[k] MatEnd Z where
  toFun r := ∑ t, ∑ i, ∑ j, single (e (t, i)) (e (t, j)) (T.F t i j (φ t r i j))
  map_add' r r' := by
    simp only [map_add, MatEnd.add_apply, single_add, ← Finset.sum_add_distrib]
  map_smul' c r := by
    simp only [map_smul, MatEnd.smul_apply, single_smul, Finset.smul_sum, RingHom.id_apply]

theorem matBlockMapₗ_apply (T : BlockTransport (k := k) e X Z) (φ : ∀ t, A →ₐ[k] MatEnd (X t))
    (r : A) : matBlockMapₗ e T φ r =
      ∑ t, ∑ i, ∑ j, single (e (t, i)) (e (t, j)) (T.F t i j (φ t r i j)) := rfl

theorem matBlockMapₗ_one (T : BlockTransport (k := k) e X Z) (φ : ∀ t, A →ₐ[k] MatEnd (X t)) :
    matBlockMapₗ e T φ 1 = 1 := by
  rw [matBlockMapₗ_apply, one_eq_sum_single]
  have h1 : ∀ t i j, single (e (t, i)) (e (t, j)) (T.F t i j ((φ t 1) i j)) =
      if i = j then single (e (t, i)) (e (t, i)) (𝟙 _) else 0 := by
    intro t i j
    rw [map_one]
    split_ifs with h
    · subst h; rw [one_apply_self, T.map_id]
    · rw [one_apply_of_ne h, map_zero, single_zero]
  simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Fintype.sum_prod_type', ← e.sum_comp]

theorem matBlockMapₗ_mul (T : BlockTransport (k := k) e X Z) (φ : ∀ t, A →ₐ[k] MatEnd (X t))
    (r r' : A) : matBlockMapₗ e T φ (r * r') = matBlockMapₗ e T φ r * matBlockMapₗ e T φ r' := by
  simp only [matBlockMapₗ_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  -- collapse the sum over the blocks of the first factor
  have hcol : ∀ i m, ∑ t', ∑ i', ∑ j', single (e (t', i')) (e (t', j')) (T.F t' i' j' (φ t' r i' j')) *
      single (e (t, i)) (e (t, m)) (T.F t i m (φ t r' i m)) =
      ∑ j, single (e (t, i)) (e (t, j)) (T.F t i m (φ t r' i m) ≫ T.F t m j (φ t r m j)) := by
    intro i m
    rw [Finset.sum_eq_single t]
    · rw [Finset.sum_eq_single m]
      · exact Finset.sum_congr rfl fun j _ => single_mul_single _ _ _ _ _
      · intro i' _ hi'
        exact Finset.sum_eq_zero fun j' _ => single_mul_single_of_ne _ _
          (fun h => hi' (Prod.ext_iff.1 (e.injective h)).2.symm)
      · simp
    · intro t' _ ht'
      refine Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun j' _ => ?_
      exact single_mul_single_of_ne _ _ (fun h => ht' (Prod.ext_iff.1 (e.injective h)).1.symm)
    · simp
  simp only [hcol]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_apply, map_sum, single_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [T.map_comp]

/-- **Block-diagonal assembly** of algebra homomorphisms along functorial transports. -/
def matBlockMap (T : BlockTransport (k := k) e X Z) (φ : ∀ t, A →ₐ[k] MatEnd (X t)) :
    A →ₐ[k] MatEnd Z :=
  AlgHom.ofLinearMap (matBlockMapₗ e T φ) (matBlockMapₗ_one e T φ) (matBlockMapₗ_mul e T φ)

theorem matBlockMap_apply (T : BlockTransport (k := k) e X Z) (φ : ∀ t, A →ₐ[k] MatEnd (X t))
    (r : A) : matBlockMap e T φ r =
      ∑ t, ∑ i, ∑ j, single (e (t, i)) (e (t, j)) (T.F t i j (φ t r i j)) := rfl

/-- The entries of `matBlockMap`: within a block they are the transported entries. -/
theorem matBlockMap_apply_block (T : BlockTransport (k := k) e X Z) (φ : ∀ t, A →ₐ[k] MatEnd (X t))
    (r : A) (t : κ) (i j : ι) : matBlockMap e T φ r (e (t, i)) (e (t, j)) = T.F t i j (φ t r i j) := by
  rw [matBlockMap_apply, sum_apply, Finset.sum_eq_single t]
  · rw [sum_apply, Finset.sum_eq_single i]
    · rw [sum_apply, Finset.sum_eq_single j]
      · exact single_apply_self _ _ _
      · intro j' _ hj'
        exact single_apply_of_ne _ (fun h => hj' (Prod.ext_iff.1 (e.injective h.2.symm)).2)
      · simp
    · intro i' _ hi'
      rw [sum_apply]
      exact Finset.sum_eq_zero fun j' _ =>
        single_apply_of_ne _ (fun h => hi' (Prod.ext_iff.1 (e.injective h.1.symm)).2)
    · simp
  · intro t' _ ht'
    rw [sum_apply]
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [sum_apply]
    exact Finset.sum_eq_zero fun j' _ =>
      single_apply_of_ne _ (fun h => ht' (Prod.ext_iff.1 (e.injective h.1.symm)).1)
  · simp

/-- The entries of `matBlockMap` between different blocks vanish. -/
theorem matBlockMap_apply_ne (T : BlockTransport (k := k) e X Z) (φ : ∀ t, A →ₐ[k] MatEnd (X t))
    (r : A) {t t' : κ} (i j : ι) (h : t ≠ t') : matBlockMap e T φ r (e (t, i)) (e (t', j)) = 0 := by
  rw [matBlockMap_apply, sum_apply]
  refine Finset.sum_eq_zero fun t'' _ => ?_
  rw [sum_apply]
  refine Finset.sum_eq_zero fun i' _ => ?_
  rw [sum_apply]
  refine Finset.sum_eq_zero fun j' _ => single_apply_of_ne _ fun hh => h ?_
  have h1 := (Prod.ext_iff.1 (e.injective hh.1)).1
  have h2 := (Prod.ext_iff.1 (e.injective hh.2)).1
  exact h1.trans h2.symm

/-- If every `φ t` sends `r` to the diagonal matrix unit at `i`, then `matBlockMap` sends `r` to the
sum of the diagonal matrix units at the `e (t, i)`. -/
theorem matBlockMap_eq_of_single (T : BlockTransport (k := k) e X Z)
    (φ : ∀ t, A →ₐ[k] MatEnd (X t)) (r : A) (i : ι) (h : ∀ t, φ t r = single i i (𝟙 _)) :
    matBlockMap e T φ r = ∑ t, single (e (t, i)) (e (t, i)) (𝟙 _) := by
  rw [matBlockMap_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [h t, Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · rw [single_apply_self, T.map_id]
    · intro j _ hj
      rw [single_apply_of_ne _ (fun h' => hj h'.2), map_zero, single_zero]
    · simp
  · intro i' _ hi'
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [single_apply_of_ne _ (fun h' => hi' h'.1), map_zero, single_zero]
  · simp

end Categorification.KLR.Diagram
