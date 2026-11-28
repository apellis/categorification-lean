/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyLeftInd
import Categorification.KLR.MackeyTailIdempotent

/-!
# The top of the Mackey filtration of a partial standardization on a loading

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half: the leading layer of the
filtration of `S_+(X) e_s` by the head strands passing the window. This file proves the
vanishing half of the identification of the leading layer, for any cut `A | B` of the red
strands, in the coordinates of KL I, Prop. 2.18 (`MackeyIndAssoc`).

* On the input `N` of the induced model of the cut, a loading of the second block whose
  leftmost strand is black acts by zero (`cutInput_one_tmul_e_smul_eq_zero`): it projects to
  zero in `T^B` (Definition 4.3 of arXiv:1309.3796v2).
* Let `ν | ν'` be a top cut of the weight and `s` a loading of `ν` such that, in the first
  `p` positions of `s`, every strand whose label can belong to the second bottom block is black.
  If the Mackey datum `λ` has more than `|ν| - p` strands from the second bottom block to the
  first top block, or exactly `|ν| - p` but with a weight different from the labels of `s`
  after `p`, then `1_s ⊗ 1` kills the piece `MackeyTop_λ ⊗_{R'} (MackeyBot_λ ⊗_{R''} N)` of the
  layer (`cutInput_e_tmul_one_smul_mackeyLeftInd_eq_zero`) and its image in the layer of
  `Ind N` (`indTopAct_e_tmul_one_indMackeyLeftMap_eq_zero`).

Applied at the cut `A | MR` of `λ⁺` with `p = midPos s` and `|ν| = p + |window|`, this says
that on `e_s` only the datum `λ₀` (the window strands, in order) contributes to the top layer.
Webster's proof does not spell this out; it is the step L2 of the trace half.

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`.

## Main results

* `Stendhal.cutInput_one_tmul_e_smul_eq_zero`,
  `Stendhal.cutInput_e_tmul_one_smul_mackeyLeftInd_eq_zero`,
  `Stendhal.indTopAct_e_tmul_one_indMackeyLeftMap_eq_zero`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

section Violated

variable {I : Type*} {ℓ : ℕ}

/-- A cast of a violated loading is violated. -/
theorem seqCast_isViolated {μ μ' : Multiset (I ⊕ Fin ℓ)} (h : μ = μ') {s : Seq μ}
    (hs : IsViolated s) : IsViolated (seqCast h s) := by
  subst h; exact hs

/-- A concatenation whose first factor is violated is violated. -/
theorem append_isViolated_of_left {μ μ' : Multiset (I ⊕ Fin ℓ)} {s : Seq μ} (d : Seq μ')
    (hs : IsViolated s) : IsViolated (s.append d) := by
  obtain ⟨h0, hv⟩ := hs
  refine ⟨by simp only [Multiset.card_add]; omega, ?_⟩
  have := Seq.append_posL s d ⟨0, h0⟩
  rw [show Seq.posL μ' ⟨0, h0⟩ = ⟨0, by simp only [Multiset.card_add]; omega⟩ from
    Fin.ext rfl] at this
  rw [Seq.lbl, this]; exact hv

end Violated

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (a + r) → I →₀ ℕ} {θ β : Multiset I}

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ

variable {N : Type*} [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]

omit [Module k N] [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- **L1: a violated loading of the second block kills the input** of the induced model. -/
theorem cutInput_one_tmul_e_smul_eq_zero (t : Seq δ) (ht : IsViolated t)
    (x : CutInput Q Λ θ β N) :
    ((1 : KLRAlgebra k S α) ⊗ₜ (e t : KLRAlgebra k S δ) : TensorKLR S α δ) • x = 0 := by
  change (cutInputMap Q Λ θ β ((1 : KLRAlgebra k S α) ⊗ₜ (e t : KLRAlgebra k S δ))) •
    (x : N) = 0
  rw [cutInputMap, Algebra.TensorProduct.map_tmul,
    redSubfamilyProjection_e_violated_ambient Q Λ (Fin.natAdd a) (Fin.natAdd_injective r a) β t
      ht, TensorProduct.tmul_zero]
  exact zero_smul (cutFactorAlgebra Q Λ θ β) (x : N)

variable {ν ν' : Multiset (I ⊕ Fin (a + r))}

/-- The violated loadings of a weight. -/
def violatedLoadings (μ : Multiset (I ⊕ Fin (a + r))) : Finset (Seq μ) := by
  classical exact Finset.univ.filter fun j : Seq μ => IsViolated j

omit [DecidableEq I] in
theorem mem_violatedLoadings {μ : Multiset (I ⊕ Fin (a + r))} {j : Seq μ} :
    j ∈ violatedLoadings μ ↔ IsViolated j := by
  classical
  unfold violatedLoadings
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- **L1 on the bottom factor**: `(1 ⊗ 1_T) ⊗ 1`, `T` the violated loadings of `λ`, kills
`MackeyBot_λ ⊗_{R''} N`, since the strands of `λ` are the first ones of the second block. -/
theorem cutInput_tail_smul_eq_zero (q : MackeyQuad ν ν' α δ)
    (y : BalancedTensor k (QuadAlg S q) (TensorKLR S α δ) (MackeyBot S q)
      (CutInput Q Λ θ β N)) :
    ((((1 : KLRAlgebra k S q.α) ⊗ₜ eSum S (violatedLoadings q.β)) ⊗ₜ
      (1 : TensorKLR S q.γ q.δ) : QuadAlg S q) • y) = 0 :=
  quadAlg_tail_smul_eq_zero q (CutInput Q Λ θ β N) _ (fun _ hj v x =>
    cutInput_one_tmul_e_smul_eq_zero _
      (seqCast_isViolated q.h₄ (append_isViolated_of_left v (mem_violatedLoadings.1 hj))) x) y

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- **L2 for the cut, on one Mackey datum**: let `s` be a loading of the first top block `ν`
whose strands left of `p` with labels in `λ` are black. If `λ` has more than `|ν| - p` strands,
or exactly `|ν| - p` with a weight different from the labels of `s` after `p`, then
`1_s ⊗ 1` kills `MackeyTop_λ ⊗_{R'} (MackeyBot_λ ⊗_{R''} N)`. -/
theorem cutInput_e_tmul_one_smul_mackeyLeftInd_eq_zero (hsym : KLRSymm S)
    (q : MackeyQuad ν ν' α δ) (s : Seq ν) {p : ℕ} (hp : p ≤ Multiset.card ν)
    (hs : ∀ a' : Fin (Multiset.card (q.α + q.β)), a'.val < p →
      (seqCast q.h₁.symm s).1 a' ∈ q.β → ((seqCast q.h₁.symm s).1 a').isLeft)
    (hpos : Multiset.card q.α < p ∨ (Multiset.card q.α = p ∧
      (Finset.univ.val.map fun b : Fin (Multiset.card q.β) =>
        (seqCast q.h₁.symm s).1 (Seq.posR q.α b)) ≠ q.β))
    (w : MackeyLeftInd S (CutInput Q Λ θ β N) q) :
    ((e s : KLRAlgebra k S ν) ⊗ₜ (1 : KLRAlgebra k S ν') : TensorKLR S ν ν') • w = 0 := by
  by_cases hc : 0 < Multiset.card q.β
  · refine e_tmul_one_smul_mackeyLeftInd_eq_zero q hsym s (violatedLoadings q.β) ?_
      (cutInput_tail_smul_eq_zero q) w
    intro u i j h
    exact mem_violatedLoadings.2 ⟨hc, tail_first_of_lt _ p (fun z => z.isLeft = true) hs hpos
      hc u i j h⟩
  · exfalso
    have hβ : q.β = 0 := Multiset.card_eq_zero.1 (by omega)
    have hcard : Multiset.card q.α + Multiset.card q.β = Multiset.card ν := by
      rw [← Multiset.card_add, q.h₁]
    rcases hpos with hlt | ⟨-, hne⟩
    · omega
    · apply hne
      have h0 : IsEmpty (Fin (Multiset.card q.β)) := by
        rw [hβ, Multiset.card_zero]; exact Fin.isEmpty'
      have h1 : (Finset.univ.val : Multiset (Fin (Multiset.card q.β))) = 0 :=
        Finset.val_eq_zero.2 Finset.univ_eq_empty
      rw [h1, Multiset.map_zero]
      exact hβ.symm

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- **L2 for the cut, in the layer of `Ind N`**: under the hypotheses of
`cutInput_e_tmul_one_smul_mackeyLeftInd_eq_zero`, `1_s ⊗ 1` kills the image of `Ξ_λ` in the
`|λ|`-th layer of the Mackey filtration of the induced model at the top cut `ν | ν'`. -/
theorem indTopAct_e_tmul_one_indMackeyLeftMap_eq_zero (hsym : KLRSymm S) (h : α + δ = ν + ν')
    (q : MackeyQuad ν ν' α δ) {c : ℕ} (hc : Multiset.card q.β = c) (s : Seq ν) {p : ℕ}
    (hp : p ≤ Multiset.card ν)
    (hs : ∀ a' : Fin (Multiset.card (q.α + q.β)), a'.val < p →
      (seqCast q.h₁.symm s).1 a' ∈ q.β → ((seqCast q.h₁.symm s).1 a').isLeft)
    (hpos : Multiset.card q.α < p ∨ (Multiset.card q.α = p ∧
      (Finset.univ.val.map fun b : Fin (Multiset.card q.β) =>
        (seqCast q.h₁.symm s).1 (Seq.posR q.α b)) ≠ q.β))
    (w : MackeyLeftInd S (CutInput Q Λ θ β N) q) :
    indTopAct (Q := S) h (CutInput Q Λ θ β N) c
        ((e s : KLRAlgebra k S ν) ⊗ₜ (1 : KLRAlgebra k S ν'))
        (indMackeyLeftMap (Q := S) h (CutInput Q Λ θ β N) q hc w) = 0 := by
  rw [← indMackeyLeftMap_smul,
    cutInput_e_tmul_one_smul_mackeyLeftInd_eq_zero hsym q s hp hs hpos w, map_zero]

end Categorification.Stendhal
