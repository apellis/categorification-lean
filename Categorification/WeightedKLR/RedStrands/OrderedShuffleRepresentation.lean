/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedShuffleModule

/-!
# The ordered quotient of a shuffle representation

For Webster, arXiv:1309.3796v2, §5, Theorem 5.8 the affine induced module
has a quotient supported on the prescribed red order. The descent needs
only the vanishing of crossings returning from an excluded loading.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
variable {I k : Type*} [DecidableEq I] [CommRing k] {μ : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {M : Type*} [AddCommGroup M] [Module k M]
  (ρ : KLRAlgebra k Q μ →ₐ[k] Module.End k M) (S : Finset (Seq μ))

local notation "A" => KLRAlgebra k Q μ
local notation "P" => (eSum Q S : A)

/-- The subspace supported on the excluded loadings. -/
def excludedSpace : Submodule k M := LinearMap.ker (ρ P)

/-- An adjacent crossing returning to an allowed loading from an excluded
one acts by zero. This condition involves the original affine representation. -/
def VanishingReturnCrossings : Prop :=
  ∀ (j : ℕ) (s : Seq μ), s ∉ S → sadj μ.card j • s ∈ S → ρ (ψ j * e s) = 0

private theorem eSum_cross_component (j : ℕ) (s : Seq μ) :
    P * (ψ j * e s) =
      if sadj μ.card j • s ∈ S then ψ j * e s else 0 := by
  have h : (e (sadj μ.card j • s) * (ψ j * e s) : A) = ψ j * e s := by
    rw [← mul_assoc, e_mul_ψ, sadj_smul_smul, mul_assoc, e_mul_self]
  calc P * (ψ j * e s) = (P * e (sadj μ.card j • s)) * (ψ j * e s) := by rw [mul_assoc, h]
       _ = _ := by rw [eSum_mul_e]; split_ifs <;> simp [h]

private theorem return_stable (hret : VanishingReturnCrossings ρ S) (j : ℕ) (m : M)
    (hm : ρ P m = 0) : ρ P (ρ (ψ j) m) = 0 := by
  have hz (s : Seq μ) : ρ (P * (ψ j * e s)) m = 0 := by
    by_cases hs : s ∈ S
    · have he : ρ (e s) m = 0 := by
        have hx : (e s * P : A) = e s := by simp [e_mul_eSum, hs]
        rw [← hx, map_mul, Module.End.mul_apply, hm, map_zero]
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, he, map_zero, map_zero]
    · by_cases ht : sadj μ.card j • s ∈ S
      · rw [eSum_cross_component, ite_eq_left ht, hret j s hs ht, LinearMap.zero_apply]
      · rw [eSum_cross_component, ite_eq_right ht, map_zero, LinearMap.zero_apply]
  have he : ∑ s : Seq μ, (P * (ψ j * e s)) = P * ψ j := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_e, mul_one]
  rw [← Module.End.mul_apply, ← map_mul, ← he, map_sum, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun s _ => hz s

private theorem excludedSpace_stable (hret : VanishingReturnCrossings ρ S) (z : A) :
    excludedSpace ρ S ≤ (excludedSpace ρ S).comap (ρ z) := by
  obtain ⟨f,rfl⟩ := mk_surjective z
  induction f using FreeAlgebra.induction with
  | grade0 c =>
    intro m hm
    change ρ P (ρ ((mk k Q μ) (algebraMap k _ c)) m) = 0
    rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, map_smul, show ρ P m = 0 from hm, smul_zero]
  | grade1 g =>
    intro m hm
    cases g with
    | idem s =>
      change ρ P (ρ (e s) m) = 0
      have h : (P * e s : A) = e s * P := by rw [eSum_mul_e, e_mul_eSum]
      rw [← Module.End.mul_apply, ← map_mul, h, map_mul, Module.End.mul_apply, show ρ P m = 0 from hm, map_zero]
    | dot a =>
      change ρ P (ρ (x a) m) = 0
      rw [← Module.End.mul_apply, ← map_mul, ← x_mul_eSum, map_mul, Module.End.mul_apply, show ρ P m = 0 from hm, map_zero]
    | cross j => exact return_stable ρ S hret j m hm
  | add f g hf hg =>
    intro m hm
    change ρ ((mk k Q μ) (f+g)) m ∈ excludedSpace ρ S
    rw [map_add, map_add, LinearMap.add_apply]
    exact (excludedSpace ρ S).add_mem (hf hm) (hg hm)
  | mul f g hf hg =>
    intro m hm
    change ρ ((mk k Q μ) (f*g)) m ∈ excludedSpace ρ S
    rw [map_mul, map_mul, Module.End.mul_apply]
    exact hf (hg hm)

/-- The quotient action on the permitted-loading sectors. -/
def orderedShuffleAction (hret : VanishingReturnCrossings ρ S) :
    A →ₐ[k] Module.End k (M ⧸ excludedSpace ρ S) := by
  let K := excludedSpace ρ S
  let F (z : A) := K.mapQ K (ρ z) (excludedSpace_stable ρ S hret z)
  have h (z : A) (y : M) : F z (K.mkQ y) = K.mkQ (ρ z y) := rfl
  exact {
    toFun := F
    map_one' := by
      apply LinearMap.ext; intro z; obtain ⟨y,rfl⟩ := K.mkQ_surjective z
      rw [h, map_one, Module.End.one_apply, Module.End.one_apply]
    map_zero' := by
      apply LinearMap.ext; intro z; obtain ⟨y,rfl⟩ := K.mkQ_surjective z
      rw [h, map_zero, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
    map_add' a b := by
      apply LinearMap.ext; intro z; obtain ⟨y,rfl⟩ := K.mkQ_surjective z
      rw [h, map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, h, h]
    map_mul' a b := by
      apply LinearMap.ext; intro z; obtain ⟨y,rfl⟩ := K.mkQ_surjective z
      rw [h, map_mul, Module.End.mul_apply, Module.End.mul_apply, h, h]
    commutes' c := by
      apply LinearMap.ext; intro z; obtain ⟨y,rfl⟩ := K.mkQ_surjective z
      rw [h, AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul] }

theorem orderedShuffleAction_mkQ (hret : VanishingReturnCrossings ρ S) (z : A) (m : M) :
    orderedShuffleAction ρ S hret z ((excludedSpace ρ S).mkQ m) =
      (excludedSpace ρ S).mkQ (ρ z m) := rfl

/-- Projection to the ordered quotient is injective on the included subspace. -/
theorem orderedShuffle_mkQ_injOn :
    Set.InjOn (excludedSpace ρ S).mkQ {m : M | ρ P m = m} := by
  intro x hx y hy he
  have hz : (excludedSpace ρ S).mkQ (x-y) = 0 := by rw [map_sub, he, sub_self]
  have hm := (Submodule.Quotient.mk_eq_zero (excludedSpace ρ S)).mp hz
  change ρ P (x-y) = 0 at hm
  rw [map_sub, hx, hy] at hm
  exact sub_eq_zero.mp hm

/-- The ordered quotient kills every excluded idempotent. -/
theorem orderedShuffleAction_e_eq_zero (hret : VanishingReturnCrossings ρ S)
    (s : Seq μ) (hs : s ∉ S) : orderedShuffleAction ρ S hret (e s) = 0 := by
  apply LinearMap.ext
  intro y
  obtain ⟨m,rfl⟩ := (excludedSpace ρ S).mkQ_surjective y
  rw [orderedShuffleAction_mkQ]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change ρ P (ρ (e s) m) = 0
  rw [← Module.End.mul_apply, ← map_mul, eSum_mul_e, ite_eq_right hs, map_zero, LinearMap.zero_apply]


/-- A generator with either endpoint in an excluded sector acts by zero
on the quotient. -/
theorem orderedShuffleAction_cross_eq_zero (hret : VanishingReturnCrossings ρ S)
    (j : ℕ) (s : Seq μ) (h : s ∉ S ∨ sadj μ.card j • s ∉ S) :
    orderedShuffleAction ρ S hret (ψ j * e s) = 0 := by
  rcases h with hs | ht
  · rw [map_mul, orderedShuffleAction_e_eq_zero ρ S hret s hs, mul_zero]
  · rw [ψ_mul_e, map_mul, orderedShuffleAction_e_eq_zero ρ S hret _ ht, zero_mul]

/-- An affine relation already acting by zero on induction still vanishes
on its ordered quotient. -/
theorem orderedShuffleAction_eq_zero_of_eq_zero (hret : VanishingReturnCrossings ρ S)
    {z : A} (hz : ρ z = 0) : orderedShuffleAction ρ S hret z = 0 := by
  apply LinearMap.ext
  intro y
  obtain ⟨m, rfl⟩ := (excludedSpace ρ S).mkQ_surjective y
  rw [orderedShuffleAction_mkQ, hz, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

end Categorification.Stendhal
