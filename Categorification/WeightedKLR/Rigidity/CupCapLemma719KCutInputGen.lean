/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationLift
import Categorification.KLR.Examples.Small

/-!
# The intertwining condition at a cut on generators

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof of the inverse `Ψ`: the map
`S_cut Y → Hom(K^σ, S_+(Y ⊠ L'))` comes from the universal property of the partial
standardization at a cut (`cutStandardLift`), whose intertwining condition `IsCutInputHom` is
checked on generators. This file proves that reduction: the condition holds as soon as it holds
for the pairs of idempotents `e(i) ⊗ e(l)` and for the dots and crossings of each block, placed
in their tensor factor (`isCutInputHom_of_gens`). It is the two-block form of
`KLR.KLRAlgebra.isInd3InputHom_of_gens`.

## Main definitions

* `Stendhal.IsCutAt`: the intertwining condition at one element.

## Main results

* `Stendhal.isCutInputHom_of_gens`: the intertwining condition from the generators.
* `Stendhal.isCutAt_of_concat_eq`: the condition at a generator `g` juxtaposed as
  `g 1_{α,δ}`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct
open Algebra.TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (a + r) → I →₀ ℕ} {θ β : Multiset I}

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ

variable {N : Type*} [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  {X : Type*} [AddCommGroup X] [Module k X]
  (σ : TensorProductAlgebra k Q Λ (θ + β) →ₐ[k] Module.End k X) (f : N →ₗ[k] X)

variable (Q Λ θ β) in
/-- The intertwining condition at a cut at one element `t`. -/
def IsCutAt (t : TensorKLR S α δ) : Prop :=
  ∀ n : N, f (cutInputMap Q Λ θ β t • n) = σ (cutAffineMap Q Λ θ β (concat S α δ t)) (f n)

theorem IsCutAt.add {s t : TensorKLR S α δ} (hs : IsCutAt Q Λ θ β σ f s)
    (ht : IsCutAt Q Λ θ β σ f t) : IsCutAt Q Λ θ β σ f (s + t) := fun n => by
  rw [IsCutAt] at hs ht
  rw [map_add, add_smul, map_add, hs, ht, map_add, map_add, map_add, LinearMap.add_apply]

theorem IsCutAt.zero : IsCutAt Q Λ θ β σ f (0 : TensorKLR S α δ) := fun n => by
  rw [map_zero, zero_smul (cutFactorAlgebra Q Λ θ β) n, map_zero, map_zero, map_zero, map_zero,
    LinearMap.zero_apply]

theorem IsCutAt.sum {ι : Type*} (F : Finset ι) {t : ι → TensorKLR S α δ}
    (ht : ∀ i ∈ F, IsCutAt Q Λ θ β σ f (t i)) : IsCutAt Q Λ θ β σ f (∑ i ∈ F, t i) := by
  classical
  induction F using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact IsCutAt.zero σ f
  | insert i F hi ih =>
    rw [Finset.sum_insert hi]
    exact (ht i (Finset.mem_insert_self i F)).add σ f
      (ih fun i' hi' => ht i' (Finset.mem_insert_of_mem hi'))

/-- The elements at which the intertwining condition holds, as a subalgebra, when it holds at
the unit. -/
def cutAtSubalgebra [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]
    (h1 : IsCutAt Q Λ θ β σ f 1) : Subalgebra k (TensorKLR S α δ) where
  carrier := {t | IsCutAt Q Λ θ β σ f t}
  mul_mem' {s t} hs ht n := by
    rw [map_mul, mul_smul, hs, ht, concat_mul, map_mul, map_mul, Module.End.mul_apply]
  add_mem' {s t} hs ht := hs.add σ f ht
  algebraMap_mem' c n := by
    change f (cutInputMap Q Λ θ β (algebraMap k _ c) • n) =
      σ (cutAffineMap Q Λ θ β (concat S α δ (algebraMap k _ c))) (f n)
    rw [Algebra.algebraMap_eq_smul_one, AlgHom.map_smul_of_tower (cutInputMap Q Λ θ β),
      smul_assoc, f.map_smul, h1 n,
      LinearMap.map_smul (concat S α δ), map_smul (cutAffineMap Q Λ θ β), map_smul σ,
      LinearMap.smul_apply]

/-- **The condition at a generator juxtaposed as `g 1_{α,δ}`**, from its action through `g`. -/
theorem isCutAt_of_concat_eq (h1 : IsCutAt Q Λ θ β σ f 1) (t : TensorKLR S α δ)
    (g : KLRAlgebra k S (α + δ)) (hg : concat S α δ t = g * oneConcat S α δ)
    (ht : ∀ n : N, f (cutInputMap Q Λ θ β t • n) = σ (cutAffineMap Q Λ θ β g) (f n)) :
    IsCutAt Q Λ θ β σ f t := fun n => by
  have h1' : ∀ n : N, σ (cutAffineMap Q Λ θ β (oneConcat S α δ)) (f n) = f n := fun n => by
    rw [← concat_one, ← h1 n, map_one, one_smul]
  rw [ht, hg, map_mul, map_mul, Module.End.mul_apply, h1']

variable {J₁ J₂ : Type*} [DecidableEq J₁] [DecidableEq J₂]
  {P₁ : J₁ → J₁ → MvPolynomial (Fin 2) k} {P₂ : J₂ → J₂ → MvPolynomial (Fin 2) k}
  {μ₁ : Multiset J₁} {μ₂ : Multiset J₂}
  (φ₁ : KLRAlgebra k P₁ μ₁ →ₐ[k] KLRAlgebra k (stendhalQ Q Λ)
    (Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)))
  (φ₂ : KLRAlgebra k P₂ μ₂ →ₐ[k] KLRAlgebra k (stendhalQ Q Λ)
    (Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)))

/-- **The intertwining condition at the unit**, from the pairs of idempotents. -/
theorem isCutAt_one_of_e
    (hE : ∀ (i : Seq μ₁) (l : Seq μ₂), IsCutAt Q Λ θ β σ f (φ₁ (e i) ⊗ₜ[k] φ₂ (e l))) :
    IsCutAt Q Λ θ β σ f 1 := by
  have h : (1 : TensorKLR S α δ) = ∑ i : Seq μ₁, ∑ l : Seq μ₂, φ₁ (e i) ⊗ₜ[k] φ₂ (e l) := by
    simp only [← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, ← map_sum, sum_e, map_one,
      Algebra.TensorProduct.one_def]
  rw [h]
  exact IsCutAt.sum σ f _ fun i _ => IsCutAt.sum σ f _ fun l _ => hE i l

/-- **The intertwining condition from the generators**: for surjections `φ₁`, `φ₂` onto the
affine KLR algebras of the two blocks, it holds if it holds at the pairs of idempotents
`φ₁(e(i)) ⊗ φ₂(e(l))` and at the images of the dots `x_a` and the crossings `ψ_p` of each block,
placed in its tensor factor. -/
theorem isCutInputHom_of_gens [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂)
    (hE : ∀ (i : Seq μ₁) (l : Seq μ₂), IsCutAt Q Λ θ β σ f (φ₁ (e i) ⊗ₜ[k] φ₂ (e l)))
    (hAx : ∀ a : Fin (Multiset.card μ₁), IsCutAt Q Λ θ β σ f (φ₁ (x a) ⊗ₜ (1 : KLRAlgebra k S δ)))
    (hAψ : ∀ p : ℕ, IsCutAt Q Λ θ β σ f (φ₁ (ψ p) ⊗ₜ (1 : KLRAlgebra k S δ)))
    (hBx : ∀ b : Fin (Multiset.card μ₂), IsCutAt Q Λ θ β σ f ((1 : KLRAlgebra k S α) ⊗ₜ φ₂ (x b)))
    (hBψ : ∀ p : ℕ, IsCutAt Q Λ θ β σ f ((1 : KLRAlgebra k S α) ⊗ₜ φ₂ (ψ p))) :
    IsCutInputHom Q Λ θ β N σ f := by
  let T := cutAtSubalgebra σ f (isCutAt_one_of_e σ f φ₁ φ₂ hE)
  have hAe : ∀ i, IsCutAt Q Λ θ β σ f (φ₁ (e i) ⊗ₜ[k] (1 : KLRAlgebra k S δ)) := fun i => by
    have h : φ₁ (e i) ⊗ₜ[k] (1 : KLRAlgebra k S δ) = ∑ l : Seq μ₂, φ₁ (e i) ⊗ₜ[k] φ₂ (e l) := by
      rw [← TensorProduct.tmul_sum, ← map_sum, sum_e, map_one]
    rw [h]
    exact IsCutAt.sum σ f _ fun l _ => hE i l
  have hBe : ∀ l, IsCutAt Q Λ θ β σ f ((1 : KLRAlgebra k S α) ⊗ₜ[k] φ₂ (e l)) := fun l => by
    have h : (1 : KLRAlgebra k S α) ⊗ₜ[k] φ₂ (e l) = ∑ i : Seq μ₁, φ₁ (e i) ⊗ₜ[k] φ₂ (e l) := by
      rw [← TensorProduct.sum_tmul, ← map_sum, sum_e, map_one]
    rw [h]
    exact IsCutAt.sum σ f _ fun i _ => hE i l
  let iA : KLRAlgebra k S α →ₐ[k] TensorKLR S α δ := includeLeft
  let iB : KLRAlgebra k S δ →ₐ[k] TensorKLR S α δ := includeRight
  have hA : ∀ u : KLRAlgebra k S α, u ⊗ₜ (1 : KLRAlgebra k S δ) ∈ T := fun u => by
    obtain ⟨u, rfl⟩ := hφ₁ u
    exact mem_of_gens (iA.comp φ₁) T hAe hAx hAψ u
  have hB : ∀ u : KLRAlgebra k S δ, (1 : KLRAlgebra k S α) ⊗ₜ u ∈ T := fun u => by
    obtain ⟨u, rfl⟩ := hφ₂ u
    exact mem_of_gens (iB.comp φ₂) T hBe hBx hBψ u
  have hall : ∀ t : TensorKLR S α δ, t ∈ T := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add s t hs ht => exact add_mem hs ht
    | tmul u u' =>
      have h : u ⊗ₜ[k] u' = (u ⊗ₜ[k] (1 : KLRAlgebra k S δ)) *
          ((1 : KLRAlgebra k S α) ⊗ₜ[k] u') := by
        simp only [tmul_mul_tmul, one_mul, mul_one]
      rw [h]
      exact mul_mem (hA u) (hB u')
  exact fun t n => hall t n

end Categorification.Stendhal
