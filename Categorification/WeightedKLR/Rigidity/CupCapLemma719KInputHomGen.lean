/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KOneStepLift
import Categorification.KLR.Examples.Small

/-!
# The intertwining condition of the one-step induction on generators

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof: the map `S_+(Z ⊠ L) → K S(Z)` is built from
the universal property of the one-step partial standardization with three blocks
(`ind3QuotLift`), whose intertwining condition `IsInd3InputHom` is checked "generator by
generator". This file proves that reduction: a map satisfies the intertwining condition as soon
as it does for the triples of idempotents `e(i) ⊗ e(j) ⊗ e(l)` and for the dots `x_a` and the
crossings `ψ_p` of each of the three affine KLR algebras (or of algebras mapping onto them),
placed in their tensor factor (`isInd3InputHom_of_gens`). The unit is the sum of the triples
of idempotents (`isInd3At_one_of_e`).

## Main definitions

* `KLR.KLRAlgebra.IsInd3At`: the intertwining condition at one element.

## Main results

* `KLR.KLRAlgebra.isInd3InputHom_of_gens`: the intertwining condition from the generators.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open scoped TensorProduct
open Algebra.TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' ν'' : Multiset I}
  {N : Type*} [AddCommGroup N] [Module k N] [Module (TensorKLR3 Q ν ν' ν'') N]
  {X : Type*} [AddCommGroup X] [Module k X]
  (σ : KLRAlgebra k Q (ν + (ν' + ν'')) →ₐ[k] Module.End k X) (f : N →ₗ[k] X)

/-- The intertwining condition of the one-step induction at one element `t`. -/
def IsInd3At (t : TensorKLR3 Q ν ν' ν'') : Prop :=
  ∀ n : N, f (t • n) = σ (concat3 Q ν ν' ν'' t) (f n)

theorem IsInd3At.add {s t : TensorKLR3 Q ν ν' ν''} (hs : IsInd3At σ f s)
    (ht : IsInd3At σ f t) : IsInd3At σ f (s + t) := fun n => by
  change f ((s + t) • n) = σ (concat3 Q ν ν' ν'' (s + t)) (f n)
  rw [add_smul, map_add, hs, ht, map_add, map_add, LinearMap.add_apply]

theorem IsInd3At.zero : IsInd3At σ f (0 : TensorKLR3 Q ν ν' ν'') := fun n => by
  change f ((0 : TensorKLR3 Q ν ν' ν'') • n) = σ (concat3 Q ν ν' ν'' 0) (f n)
  rw [zero_smul (TensorKLR3 Q ν ν' ν'') n, map_zero, map_zero, map_zero,
    LinearMap.zero_apply]

theorem IsInd3At.sum {ι : Type*} (F : Finset ι) {t : ι → TensorKLR3 Q ν ν' ν''}
    (ht : ∀ i ∈ F, IsInd3At σ f (t i)) : IsInd3At σ f (∑ i ∈ F, t i) := by
  classical
  induction F using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact IsInd3At.zero σ f
  | insert i F hi ih =>
    rw [Finset.sum_insert hi]
    exact (ht i (Finset.mem_insert_self i F)).add σ f
      (ih fun i' hi' => ht i' (Finset.mem_insert_of_mem hi'))

/-- The elements at which the intertwining condition holds, as a subalgebra, when it holds at
the unit. -/
def ind3AtSubalgebra [IsScalarTower k (TensorKLR3 Q ν ν' ν'') N] (h1 : IsInd3At σ f 1) :
    Subalgebra k (TensorKLR3 Q ν ν' ν'') where
  carrier := {t | IsInd3At σ f t}
  mul_mem' {s t} hs ht n := by
    change f ((s * t) • n) = σ (concat3 Q ν ν' ν'' (s * t)) (f n)
    rw [mul_smul, hs, ht, concat3_mul, map_mul, Module.End.mul_apply]
  add_mem' {s t} hs ht := hs.add σ f ht
  algebraMap_mem' c n := by
    change f (algebraMap k _ c • n) = σ (concat3 Q ν ν' ν'' (algebraMap k _ c)) (f n)
    rw [Algebra.algebraMap_eq_smul_one, smul_assoc, f.map_smul, (concat3 Q ν ν' ν'').map_smul,
      map_smul σ, LinearMap.smul_apply, ← h1 n]

variable {J₁ J₂ J₃ : Type*} [DecidableEq J₁] [DecidableEq J₂] [DecidableEq J₃]
  {P₁ : J₁ → J₁ → MvPolynomial (Fin 2) k} {P₂ : J₂ → J₂ → MvPolynomial (Fin 2) k}
  {P₃ : J₃ → J₃ → MvPolynomial (Fin 2) k} {μ₁ : Multiset J₁} {μ₂ : Multiset J₂}
  {μ₃ : Multiset J₃}
  (φ₁ : KLRAlgebra k P₁ μ₁ →ₐ[k] KLRAlgebra k Q ν)
  (φ₂ : KLRAlgebra k P₂ μ₂ →ₐ[k] KLRAlgebra k Q ν')
  (φ₃ : KLRAlgebra k P₃ μ₃ →ₐ[k] KLRAlgebra k Q ν'')

/-- The unit is the sum of the triples of idempotents. -/
theorem one_eq_sum_e_tmul_e_tmul_e :
    (1 : TensorKLR3 Q ν ν' ν'') =
      ∑ i : Seq μ₁, ∑ j : Seq μ₂, ∑ l : Seq μ₃, φ₁ (e i) ⊗ₜ[k] (φ₂ (e j) ⊗ₜ[k] φ₃ (e l)) := by
  simp only [← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, ← map_sum, sum_e, map_one,
    Algebra.TensorProduct.one_def]

theorem e_tmul_one_eq_sum (i : Seq μ₁) :
    φ₁ (e i) ⊗ₜ[k] (1 : TensorKLR Q ν' ν'') =
      ∑ j : Seq μ₂, ∑ l : Seq μ₃, φ₁ (e i) ⊗ₜ[k] (φ₂ (e j) ⊗ₜ[k] φ₃ (e l)) := by
  simp only [← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, ← map_sum, sum_e, map_one,
    Algebra.TensorProduct.one_def]

theorem one_tmul_e_tmul_one_eq_sum (j : Seq μ₂) :
    (1 : KLRAlgebra k Q ν) ⊗ₜ[k] (φ₂ (e j) ⊗ₜ[k] (1 : KLRAlgebra k Q ν'')) =
      ∑ i : Seq μ₁, ∑ l : Seq μ₃, φ₁ (e i) ⊗ₜ[k] (φ₂ (e j) ⊗ₜ[k] φ₃ (e l)) := by
  simp only [← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, ← map_sum, sum_e, map_one]

theorem one_tmul_one_tmul_e_eq_sum (l : Seq μ₃) :
    (1 : KLRAlgebra k Q ν) ⊗ₜ[k] ((1 : KLRAlgebra k Q ν') ⊗ₜ[k] φ₃ (e l)) =
      ∑ i : Seq μ₁, ∑ j : Seq μ₂, φ₁ (e i) ⊗ₜ[k] (φ₂ (e j) ⊗ₜ[k] φ₃ (e l)) := by
  simp only [← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, ← map_sum, sum_e, map_one]

variable {φ₁ φ₂ φ₃}

/-- **The intertwining condition at the unit**, from the triples of idempotents. -/
theorem isInd3At_one_of_e
    (hE : ∀ i j l, IsInd3At σ f (φ₁ (e i) ⊗ₜ[k] (φ₂ (e j) ⊗ₜ[k] φ₃ (e l)))) : IsInd3At σ f 1 := by
  rw [one_eq_sum_e_tmul_e_tmul_e φ₁ φ₂ φ₃]
  exact IsInd3At.sum σ f _ fun i _ => IsInd3At.sum σ f _ fun j _ =>
    IsInd3At.sum σ f _ fun l _ => hE i j l

/-- **The intertwining condition from the generators**: for surjections `φ₁`, `φ₂`, `φ₃` onto
the affine KLR algebras of the three blocks (in practice relabellings), it holds if it holds at
the triples of idempotents `φ₁(e(i)) ⊗ φ₂(e(j)) ⊗ φ₃(e(l))` and at the images of the dots
`x_a` and the crossings `ψ_p` of each block, placed in its tensor factor. -/
theorem isInd3InputHom_of_gens [IsScalarTower k (TensorKLR3 Q ν ν' ν'') N]
    (hφ₁ : Function.Surjective φ₁) (hφ₂ : Function.Surjective φ₂) (hφ₃ : Function.Surjective φ₃)
    (hE : ∀ i j l, IsInd3At σ f (φ₁ (e i) ⊗ₜ[k] (φ₂ (e j) ⊗ₜ[k] φ₃ (e l))))
    (hAx : ∀ a, IsInd3At σ f (φ₁ (x a) ⊗ₜ (1 : TensorKLR Q ν' ν'')))
    (hAψ : ∀ p, IsInd3At σ f (φ₁ (ψ p) ⊗ₜ (1 : TensorKLR Q ν' ν'')))
    (hBx : ∀ a, IsInd3At σ f ((1 : KLRAlgebra k Q ν) ⊗ₜ (φ₂ (x a) ⊗ₜ (1 : KLRAlgebra k Q ν''))))
    (hBψ : ∀ p, IsInd3At σ f ((1 : KLRAlgebra k Q ν) ⊗ₜ (φ₂ (ψ p) ⊗ₜ (1 : KLRAlgebra k Q ν''))))
    (hCx : ∀ a, IsInd3At σ f ((1 : KLRAlgebra k Q ν) ⊗ₜ ((1 : KLRAlgebra k Q ν') ⊗ₜ φ₃ (x a))))
    (hCψ : ∀ p, IsInd3At σ f ((1 : KLRAlgebra k Q ν) ⊗ₜ ((1 : KLRAlgebra k Q ν') ⊗ₜ φ₃ (ψ p)))) :
    IsInd3InputHom σ f := by
  let S := ind3AtSubalgebra σ f (isInd3At_one_of_e σ f hE)
  have hAe : ∀ i, IsInd3At σ f (φ₁ (e i) ⊗ₜ[k] (1 : TensorKLR Q ν' ν'')) := fun i => by
    rw [e_tmul_one_eq_sum φ₁ φ₂ φ₃]
    exact IsInd3At.sum σ f _ fun j _ => IsInd3At.sum σ f _ fun l _ => hE i j l
  have hBe : ∀ j, IsInd3At σ f
      ((1 : KLRAlgebra k Q ν) ⊗ₜ[k] (φ₂ (e j) ⊗ₜ[k] (1 : KLRAlgebra k Q ν''))) := fun j => by
    rw [one_tmul_e_tmul_one_eq_sum φ₁ φ₂ φ₃]
    exact IsInd3At.sum σ f _ fun i _ => IsInd3At.sum σ f _ fun l _ => hE i j l
  have hCe : ∀ l, IsInd3At σ f
      ((1 : KLRAlgebra k Q ν) ⊗ₜ[k] ((1 : KLRAlgebra k Q ν') ⊗ₜ[k] φ₃ (e l))) := fun l => by
    rw [one_tmul_one_tmul_e_eq_sum φ₁ φ₂ φ₃]
    exact IsInd3At.sum σ f _ fun i _ => IsInd3At.sum σ f _ fun j _ => hE i j l
  let iA : KLRAlgebra k Q ν →ₐ[k] TensorKLR3 Q ν ν' ν'' := includeLeft
  let iB : KLRAlgebra k Q ν' →ₐ[k] TensorKLR3 Q ν ν' ν'' :=
    (includeRight : TensorKLR Q ν' ν'' →ₐ[k] TensorKLR3 Q ν ν' ν'').comp includeLeft
  let iC : KLRAlgebra k Q ν'' →ₐ[k] TensorKLR3 Q ν ν' ν'' :=
    (includeRight : TensorKLR Q ν' ν'' →ₐ[k] TensorKLR3 Q ν ν' ν'').comp includeRight
  have hA : ∀ a : KLRAlgebra k Q ν, a ⊗ₜ (1 : TensorKLR Q ν' ν'') ∈ S := fun a => by
    obtain ⟨a, rfl⟩ := hφ₁ a
    exact mem_of_gens (iA.comp φ₁) S hAe hAx hAψ a
  have hB : ∀ b : KLRAlgebra k Q ν',
      (1 : KLRAlgebra k Q ν) ⊗ₜ (b ⊗ₜ (1 : KLRAlgebra k Q ν'')) ∈ S := fun b => by
    obtain ⟨b, rfl⟩ := hφ₂ b
    exact mem_of_gens (iB.comp φ₂) S hBe hBx hBψ b
  have hC : ∀ c : KLRAlgebra k Q ν'',
      (1 : KLRAlgebra k Q ν) ⊗ₜ ((1 : KLRAlgebra k Q ν') ⊗ₜ c) ∈ S := fun c => by
    obtain ⟨c, rfl⟩ := hφ₃ c
    exact mem_of_gens (iC.comp φ₃) S hCe hCx hCψ c
  have hall : ∀ t : TensorKLR3 Q ν ν' ν'', t ∈ S := by
    intro t
    induction t using TensorProduct.inductionOn with
    | add s t hs ht => exact add_mem hs ht
    | tmul a u =>
      induction u using TensorProduct.inductionOn with
      | add u u' hu hu' => rw [TensorProduct.tmul_add]; exact add_mem hu hu'
      | tmul b c =>
        have h : a ⊗ₜ[k] (b ⊗ₜ[k] c) =
            (a ⊗ₜ[k] (1 : TensorKLR Q ν' ν'')) *
              (((1 : KLRAlgebra k Q ν) ⊗ₜ[k] (b ⊗ₜ[k] (1 : KLRAlgebra k Q ν''))) *
                ((1 : KLRAlgebra k Q ν) ⊗ₜ[k] ((1 : KLRAlgebra k Q ν') ⊗ₜ[k] c))) := by
          simp only [Algebra.TensorProduct.one_def, tmul_mul_tmul, one_mul, mul_one]
        rw [h]
        exact mul_mem (hA a) (mul_mem (hB b) (hC c))
  exact fun t n => hall t n

/-! ### The triple concatenation on generators -/

section Concat3

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν ν' ν'' : Multiset I}

theorem concat3_tmul_of_concat_eq (a : KLRAlgebra k Q ν) (u : TensorKLR Q ν' ν'')
    (g : KLRAlgebra k Q (ν' + ν'')) (hu : concat Q ν' ν'' u = g * oneConcat Q ν' ν'') :
    concat3 Q ν ν' ν'' (a ⊗ₜ u) =
      concat Q ν (ν' + ν'') (a ⊗ₜ g) * oneConcat3 Q ν ν' ν'' := by
  have h : a ⊗ₜ[k] (g * oneConcat Q ν' ν'') =
      (a ⊗ₜ[k] g) * ((1 : KLRAlgebra k Q ν) ⊗ₜ[k] oneConcat Q ν' ν'') := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [concat3_tmul, hu, h, concat_mul, oneConcat3_eq]

theorem concat3_x_tmul_one (a : Fin (Multiset.card ν)) :
    concat3 Q ν ν' ν'' (x a ⊗ₜ 1) = x (Seq.posL (ν' + ν'') a) * oneConcat3 Q ν ν' ν'' := by
  rw [concat3_tmul_of_concat_eq _ _ 1 (by rw [concat_one, one_mul]), concat_x_tmul_one,
    mul_assoc, oneConcat3_eq, oneConcat_mul_concat]

theorem concat3_ψ_tmul_one {p : ℕ} (hp : p + 1 < Multiset.card ν) :
    concat3 Q ν ν' ν'' (ψ p ⊗ₜ 1) = ψ p * oneConcat3 Q ν ν' ν'' := by
  rw [concat3_tmul_of_concat_eq _ _ 1 (by rw [concat_one, one_mul]), concat_ψ_tmul_one hp,
    mul_assoc, oneConcat3_eq, oneConcat_mul_concat]

theorem concat3_one_tmul_x_tmul_one (b : Fin (Multiset.card ν')) :
    concat3 Q ν ν' ν'' (1 ⊗ₜ (x b ⊗ₜ 1)) =
      x (Seq.posR ν (Seq.posL ν'' b)) * oneConcat3 Q ν ν' ν'' := by
  rw [concat3_tmul_of_concat_eq _ _ _ (concat_x_tmul_one b), concat_one_tmul_x, mul_assoc,
    oneConcat3_eq, oneConcat_mul_concat]

theorem concat3_one_tmul_ψ_tmul_one {q : ℕ} (hq : q + 1 < Multiset.card ν') :
    concat3 Q ν ν' ν'' (1 ⊗ₜ (ψ q ⊗ₜ 1)) =
      ψ (Multiset.card ν + q) * oneConcat3 Q ν ν' ν'' := by
  rw [concat3_tmul_of_concat_eq _ _ _ (concat_ψ_tmul_one hq),
    concat_one_tmul_ψ (by rw [Multiset.card_add]; omega), mul_assoc, oneConcat3_eq,
    oneConcat_mul_concat]

theorem concat3_one_tmul_one_tmul_x (c : Fin (Multiset.card ν'')) :
    concat3 Q ν ν' ν'' (1 ⊗ₜ (1 ⊗ₜ x c)) =
      x (Seq.posR ν (Seq.posR ν' c)) * oneConcat3 Q ν ν' ν'' := by
  rw [concat3_tmul_of_concat_eq _ _ _ (concat_one_tmul_x c), concat_one_tmul_x, mul_assoc,
    oneConcat3_eq, oneConcat_mul_concat]

theorem concat3_one_tmul_one_tmul_ψ {r : ℕ} (hr : r + 1 < Multiset.card ν'') :
    concat3 Q ν ν' ν'' (1 ⊗ₜ (1 ⊗ₜ ψ r)) =
      ψ (Multiset.card ν + (Multiset.card ν' + r)) * oneConcat3 Q ν ν' ν'' := by
  rw [concat3_tmul_of_concat_eq _ _ _ (concat_one_tmul_ψ hr),
    concat_one_tmul_ψ (by rw [Multiset.card_add]; omega), mul_assoc, oneConcat3_eq,
    oneConcat_mul_concat]

theorem concat3_e_tmul_e_tmul_e (i : Seq ν) (j : Seq ν') (l : Seq ν'') :
    concat3 Q ν ν' ν'' (e i ⊗ₜ (e j ⊗ₜ e l)) = e (i.append (j.append l)) := by
  rw [concat3_tmul, concat_e_tmul_e, concat_e_tmul_e]

end Concat3

end Categorification.KLR.KLRAlgebra
