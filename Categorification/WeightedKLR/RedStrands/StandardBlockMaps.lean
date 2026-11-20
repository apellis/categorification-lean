/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.StandardBlocks
import Categorification.KLR.CornerHom
import Categorification.KLR.Reindex
import Categorification.KLR.BlockCommute

/-!
# The block maps into the corner `e_α T̃^λ e_α`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, proof
of Proposition 5.3.

For a decomposition `b_0 + ⋯ + b_ℓ = ν` of the black weight and the root function `α` of the
blocks, the black strands of every sequence with root function `α` fall into the blocks: the
`j`-th block holds the black strands between the red strands `λ_j` and `λ_{j+1}`, and has
weight `b_j`. Placing a KLR diagram of weight `b_j` on the `j`-th block and the identity
everywhere else is a unital algebra map `R(b_j) → e_α T̃^λ e_α` (`StendhalAlgebra.blockHom`):
the composite of the relabelling `R(b_j) ≅ R((b_j)^{inl})` of the black labels, the block
embedding `StendhalAlgebra.blockEmb`, and the quotient map of the KLR algebra of the Stendhal
data onto `T̃^λ`.

## Main definitions

* `Stendhal.StendhalAlgebra.blockHom`: the algebra map `R(b_j) → e_α T̃^λ e_α`.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

namespace StendhalAlgebra

local notation "μ" => stendhalWeight ℓ ν

variable (Q Λ) in
/-- The quotient map sends the idempotent `∑_{s ∈ T_α} e(s)` of the KLR algebra of the
Stendhal data to `e_α`. -/
theorem ofKLR_eSum_rootSet (α : Fin ℓ → I → ℕ) :
    StendhalAlgebraAllOrders.ofKLR k Q Λ ν (eSum (stendhalQ Q Λ) (rootSet ν α)) =
      (rootIdem Q Λ α : StendhalAlgebra k Q Λ ν).1 := by
  rw [coe_rootIdem, eSum, map_sum]
  rfl

variable {b : Fin (ℓ + 1) → Multiset I}

variable (Q Λ ν) in
/-- The quotient map `R(μ) → T̃^λ`, restricted to the corner of `T_α` and landing in the corner
`e_α T̃^λ e_α`. -/
noncomputable def rootCornerHom (α : Fin ℓ → I → ℕ) :
    (eSum_idem (k := k) (Q := stendhalQ Q Λ) (rootSet ν α)).Corner →ₐ[k]
      (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν) α).Corner :=
  (cornerNest (isIdempotentElem_rootIdem α)).comp
    (cornerHom (StendhalAlgebraAllOrders.ofKLR k Q Λ ν) (eSum_idem _)
      (isIdempotentElem_val (isIdempotentElem_rootIdem α)) (ofKLR_eSum_rootSet Q Λ α))

theorem val_val_rootCornerHom (α : Fin ℓ → I → ℕ)
    (a : (eSum_idem (k := k) (Q := stendhalQ Q Λ) (rootSet ν α)).Corner) :
    (rootCornerHom Q Λ ν α a).val.val = StendhalAlgebraAllOrders.ofKLR k Q Λ ν a.val :=
  rfl

variable (Q Λ) in
/-- **The block map** of arXiv:1309.3796v3, proof of Proposition 5.3: a KLR diagram of
weight `b_j` placed on the `j`-th block of black strands, as an element of the corner
`e_α T̃^λ e_α` for the root function `α` of the blocks. -/
noncomputable def blockHom (hb : blockPrefix b (ℓ + 1) = ν) (j : ℕ) (hj : j < ℓ + 1) :
    KLRAlgebra k Q (b ⟨j, hj⟩) →ₐ[k]
      (isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν) (blockRoot b)).Corner :=
  (rootCornerHom Q Λ ν (blockRoot b)).comp
    (((blockEmb hb j hj).hom (stendhalQ Q Λ)).comp
      (KLRAlgebra.reindexEquiv Sum.inl_injective (stendhalQ Q Λ) (b ⟨j, hj⟩)).toAlgHom)

theorem val_val_blockHom (hb : blockPrefix b (ℓ + 1) = ν) (j : ℕ) (hj : j < ℓ + 1)
    (a : KLRAlgebra k Q (b ⟨j, hj⟩)) :
    (blockHom Q Λ hb j hj a).val.val = StendhalAlgebraAllOrders.ofKLR k Q Λ ν
      ((blockEmb hb j hj).hom (stendhalQ Q Λ)
        (KLRAlgebra.reindexEquiv Sum.inl_injective (stendhalQ Q Λ) (b ⟨j, hj⟩) a)).val :=
  rfl

omit [DecidableEq I] in
theorem blockStart_add_card_le {j j' : ℕ} (hj : j < ℓ + 1) (h : j < j') :
    blockStart b j + Multiset.card (b ⟨j, hj⟩) + 1 ≤ blockStart b j' := by
  rw [← blockStart_succ b hj]
  rcases (Nat.succ_le_of_lt h).lt_or_eq with h' | h'
  · exact (blockStart_lt_blockStart b h').le
  · rw [← h']

theorem sadj_mem_rootSet_iff (hb : blockPrefix b (ℓ + 1) = ν) {j : ℕ} (hj : j < ℓ + 1) {l : ℕ}
    (hl : l + 1 < Multiset.card ((b ⟨j, hj⟩).map (Sum.inl : I → I ⊕ Fin ℓ))) (t : Seq μ) :
    t ∈ rootSet ν (blockRoot b) ↔
      TypeA.sadj (Multiset.card μ) (blockStart b j + l) • t ∈ rootSet ν (blockRoot b) :=
  ⟨sadj_mem_rootSet hb hj hl, fun h => by
    rw [← KLRAlgebra.sadj_smul_smul (blockStart b j + l) t]
    exact sadj_mem_rootSet hb hj hl h⟩

/-- **The block maps commute** (arXiv:1309.3796v3, proof of Proposition 5.3): diagrams on
different blocks of black strands commute in `e_α T̃^λ e_α`. -/
theorem commute_blockHom (hb : blockPrefix b (ℓ + 1) = ν) {j j' : ℕ} (hj : j < ℓ + 1)
    (hj' : j' < ℓ + 1) (h : j < j') (a : KLRAlgebra k Q (b ⟨j, hj⟩))
    (a' : KLRAlgebra k Q (b ⟨j', hj'⟩)) :
    Commute (blockHom Q Λ hb j hj a) (blockHom Q Λ hb j' hj' a') := by
  have hle := blockStart_add_card_le (b := b) hj h
  have hE := blockEnd_le hb hj'
  have hE0 := blockEnd_le hb hj
  simp only [Multiset.card_map] at hE hE0
  refine (KLRAlgebra.BlockEmb.commute_hom (Q := stendhalQ Q Λ) (blockEmb hb j hj)
    (blockEmb hb j' hj') ?_ ?_ ?_ _ _).map (rootCornerHom Q Λ ν (blockRoot b))
  · change blockStart b j + _ ≤ blockStart b j'
    simp only [Multiset.card_map]
    omega
  · intro i l hl s
    have hl' := hl
    simp only [Multiset.card_map] at hl'
    exact KLRAlgebra.BlockEmb.window_F_sadj _ _ _ _ _ i (p := blockStart b j' + l)
      (by omega) (Or.inr (by simp only [Multiset.card_map]; omega))
      (sadj_mem_rootSet_iff hb hj' hl) s
  · intro i l hl s
    have hl' := hl
    simp only [Multiset.card_map] at hl'
    exact KLRAlgebra.BlockEmb.window_F_sadj _ _ _ _ _ i (p := blockStart b j + l)
      (by omega) (Or.inl (by omega)) (sadj_mem_rootSet_iff hb hj hl) s

end StendhalAlgebra

end Categorification.Stendhal
