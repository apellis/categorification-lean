/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedShuffleModule

/-!
# The excluded part of an input module stays excluded after induction

Webster, arXiv:1309.3796v3, §5.1, comparing iterated partial standardizations. Let `M` be a
module over `R(ν) ⊗ R(ν')` for Stendhal-type colours, and `K ⊆ M` a submodule killed by every
idempotent `e(a) ⊗ e(b)` with the red strands of `b` in order (for instance the part of an
inner induced module supported on unordered loadings). Then, in the induced module
`Ind_{ν,ν'} M`, the image of `Ind_{ν,ν'} K` is killed by the sum of the idempotents of all
red-ordered loadings (`eSum_redOrdered_smul_mapRight_eq_zero`): a shuffle keeps the relative
order of the strands of each block (`isRedOrdered_right_of_shuffle`).

## Main results

* `Stendhal.isRedOrdered_right_of_shuffle`, `Stendhal.isRedOrdered_left_of_shuffle`: the blocks
  of a shuffle of a red-ordered loading are red-ordered.
* `Stendhal.eSum_redOrdered_smul_mapRight_eq_zero`: the induced excluded part is excluded.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {ν ν' : Multiset (I ⊕ Fin ℓ)}

omit [DecidableEq I] in
private theorem shuffle_lbl (s : Seq (ν + ν')) (u : Shuffle (Seq.card_add' ν ν'))
    (x : Fin (ν + ν').card) : (u.1 • s).lbl x = s.lbl (u.1⁻¹ x) := rfl

omit [DecidableEq I] in
/-- **The second block of a shuffle of a red-ordered loading is red-ordered.** -/
theorem isRedOrdered_right_of_shuffle {s : Seq (ν + ν')} (hs : IsRedOrdered s)
    (u : Shuffle (Seq.card_add' ν ν')) {a : Seq ν} {b : Seq ν'} (hu : u.1 • s = a.append b) :
    IsRedOrdered b := by
  intro p q r t hpq hp hq
  have hp' : s.lbl (u.1⁻¹ (Seq.posR ν p)) = .inr r := by
    rw [← shuffle_lbl, hu]
    exact (Seq.append_posR a b p).trans hp
  have hq' : s.lbl (u.1⁻¹ (Seq.posR ν q)) = .inr t := by
    rw [← shuffle_lbl, hu]
    exact (Seq.append_posR a b q).trans hq
  exact hs _ _ r t (u.2.2 hpq) hp' hq'

omit [DecidableEq I] in
/-- **The first block of a shuffle of a red-ordered loading is red-ordered.** -/
theorem isRedOrdered_left_of_shuffle {s : Seq (ν + ν')} (hs : IsRedOrdered s)
    (u : Shuffle (Seq.card_add' ν ν')) {a : Seq ν} {b : Seq ν'} (hu : u.1 • s = a.append b) :
    IsRedOrdered a := by
  intro p q r t hpq hp hq
  have hp' : s.lbl (u.1⁻¹ (Seq.posL ν' p)) = .inr r := by
    rw [← shuffle_lbl, hu]
    exact (Seq.append_posL a b p).trans hp
  have hq' : s.lbl (u.1⁻¹ (Seq.posL ν' q)) = .inr t := by
    rw [← shuffle_lbl, hu]
    exact (Seq.append_posL a b q).trans hq
  exact hs _ _ r t (u.2.1 hpq) hp' hq'

variable {S : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k} (hS : KLRSymm S)
  {M : Type*} [AddCommGroup M] [Module k M] [Module (TensorKLR S ν ν') M]
  [IsScalarTower k (TensorKLR S ν ν') M]

open Classical in
/-- The sum of the idempotents of the red-ordered loadings of all strands. -/
abbrev redOrderedSum : KLRAlgebra k S (ν + ν') :=
  eSum (Q := S) (Finset.univ.filter fun s : Seq (ν + ν') => IsRedOrdered s)

include hS in
/-- **The induced excluded part is excluded**: if `K ⊆ M` is killed by `e(a) ⊗ e(b)` whenever
`b` is red-ordered, then the image of `Ind K` in `Ind M` is killed by the red-ordered
loadings. -/
theorem eSum_redOrdered_smul_mapRight_eq_zero (K : Submodule (TensorKLR S ν ν') M)
    (hK : ∀ n ∈ K, ∀ (a : Seq ν) (b : Seq ν'), IsRedOrdered b →
      (e a ⊗ₜ e b : TensorKLR S ν ν') • n = 0)
    (z : Ind S ν ν' K) :
    (redOrderedSum : KLRAlgebra k S (ν + ν')) •
      BalancedTensor.mapRight (k := k) (B := KLRAlgebra k S (ν + ν')) K.subtype z = 0 := by
  classical
  rw [← LinearMap.map_smul]
  let σ : Shuffle (Seq.card_add' ν ν') → List ℕ := fun u => canWord _ u.1
  have hσ : ∀ u, IsReduced (ν + ν').card (σ u) ∧ wordProd (ν + ν').card (σ u) = u.1 :=
    fun u => ⟨isReduced_canWord _ _, wordProd_canWord _ _⟩
  induction z using indShuffle_induction hS K σ hσ with
  | hz => rw [smul_zero, map_zero]
  | ha x y hx hy => rw [smul_add, map_add, hx, hy, add_zero]
  | ht u n =>
    rw [← mul_smul, redOrderedSum, eSum, Finset.sum_mul, Finset.sum_smul, map_sum]
    refine Finset.sum_eq_zero fun s hs => ?_
    have hso : IsRedOrdered s := (Finset.mem_filter.1 hs).2
    rw [e_mul_ψw, mul_smul, idem_smul_indShuffleUnit, wordProd_reverse, inv_inv, (hσ u).2,
      LinearMap.map_smul]
    have hzero : concatIdem (Q := S) (u.1 • s) • n = 0 := by
      by_cases hc : u.1 • s ∈ concatSet ν ν'
      · obtain ⟨a, b, hab⟩ := mem_concatSet.1 hc
        rw [← hab, concatIdem_append]
        exact Subtype.ext (hK n n.2 a b (isRedOrdered_right_of_shuffle hso u hab.symm))
      · rw [concatIdem_of_not_mem hc, zero_smul]
    rw [hzero]
    change _ • BalancedTensor.tmul _ ((K.subtype) 0) = 0
    rw [map_zero, BalancedTensor.tmul_zero, smul_zero]

end Categorification.Stendhal
