/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyFiltration
import Categorification.KLR.MackeyRightFree

/-!
# The Mackey filtration of a partial standardization in shuffle coordinates

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19: the steps of the filtration of a
partial standardization at a cut by the strands of the first block that pass position `n`.

In the shuffle coordinates `𝕊(N) ≅ ⊕_u ε_u N` of the cut (`cutStandardShuffleEquiv`), the step
`F_c` (`cutMackeyFilt n c`) consists of the elements whose coordinates vanish at every shuffle
`u` such that `u⁻¹` has more than `c` strands from the second bottom block to the top positions
`< n` (`mem_cutMackeyFilt_iff`). So `F_c / F_{c-1} ≅ ⊕_{u : crossCount(u⁻¹) = c} ε_u N` as
`k`-modules. The same holds for the induced module before the quotient
(`mem_indMackeyFilt_iff`). Both follow from the description of the Mackey filtration of KL I,
Prop. 2.18, in the coordinates of Prop. 2.16 (`KLRAlgebra.mem_span_tmul_mackeyFilt_iff`).

Any commutative ring `k`, symmetric `Q`.

## Main results

* `Stendhal.mem_indMackeyFilt_iff`, `Stendhal.mem_cutMackeyFilt_iff`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ
local notation "Sh" => Shuffle (Seq.card_add' α δ)

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]

local notation "N₀" => CutInput Q Λ θ β N

variable (hQ : KLRSymm Q)

/-- **The Mackey filtration of the induced module in shuffle coordinates.** -/
theorem mem_indMackeyFilt_iff {n c : ℕ} (hn : n ≤ Multiset.card (α + δ))
    (y : CutShuffle Q Λ θ β N) :
    y ∈ indMackeyFilt Q Λ θ β N n c ↔
      ∀ u : Sh, c < crossCount n (Multiset.card α) u.1⁻¹ →
        indDecomp (cutStendhalQ_symm Q Λ hQ) N₀ y u = 0 :=
  mem_span_tmul_mackeyFilt_iff (cutStendhalQ_symm Q Λ hQ) shufWord_spec N₀ hn y

/-- **The Mackey filtration of a partial standardization in shuffle coordinates**: `v ∈ F_c` iff
the coordinates of `v` in `𝕊(N) ≅ ⊕_u ε_u N` vanish at every shuffle `u` such that `u⁻¹` has
more than `c` strands from the second bottom block to the top positions `< n`. -/
theorem mem_cutMackeyFilt_iff {n c : ℕ} (hn : n ≤ Multiset.card (α + δ))
    (v : CutStandard Q Λ θ β N) :
    v ∈ cutMackeyFilt Q Λ θ β N n c ↔
      ∀ u : Sh, c < crossCount n (Multiset.card α) u.1⁻¹ →
        (cutStandardShuffleEquiv Q Λ θ β N hQ v : Sh → N₀) u = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩ u hu
    rw [cutStandardShuffleEquiv_mkQ, (mem_indMackeyFilt_iff Q Λ θ β N hQ hn y).1 hy u hu,
      smul_zero]
  · intro h
    set g := (cutStandardShuffleEquiv Q Λ θ β N hQ v : Sh → N₀)
    set y := (indDecomp (cutStendhalQ_symm Q Λ hQ) N₀).symm g
    have hy : indDecomp (cutStendhalQ_symm Q Λ hQ) N₀ y = g := LinearEquiv.apply_symm_apply _ _
    have hv : Submodule.mkQ _ y = v := by
      refine (cutStandardShuffleEquiv Q Λ θ β N hQ).injective (Subtype.ext (funext fun u => ?_))
      rw [cutStandardShuffleEquiv_mkQ, hy]
      exact (cutShuffleIdem_mem_range_iff Q Λ θ β N u (g u)).1
        ((cutStandardShuffleEquiv Q Λ θ β N hQ v).2 u (Set.mem_univ u))
    refine ⟨y, (mem_indMackeyFilt_iff Q Λ θ β N hQ hn y).2 fun u hu => ?_, hv⟩
    rw [hy]
    exact h u hu

end Categorification.Stendhal
