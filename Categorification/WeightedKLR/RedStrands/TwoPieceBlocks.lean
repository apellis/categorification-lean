/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceDecomposition
import Categorification.WeightedKLR.RedStrands.StandardBlockMaps

/-!
# Blocks of `ℓ + 1` red strands from blocks of the first `ℓ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1. For
a decomposition `b_0 + ⋯ + b_{ℓ+1}` of the black weight into the blocks of `ℓ + 1` red strands,
the first `ℓ + 1` blocks `b' = (b_0, …, b_ℓ)` are the blocks of the first `ℓ` red strands, with
black weight `θ = b_0 + ⋯ + b_ℓ`, and the last block is `β = b_{ℓ+1}`. The sequences of root
function `α` of `b` are exactly the two-piece loadings `t λ_{ℓ+1} u` with `t` of root function
`α'` of `b'` and `u` any sequence of `β` (`mem_rootSet_blockRoot_iff`), each exactly once
(`twoPieceLoading_injective`).
-/

namespace Categorification.Stendhal

open KLR StendhalAlgebra

variable {I : Type} [DecidableEq I] {ℓ : ℕ}

section Blocks

variable (b : Fin (ℓ + 2) → Multiset I)

/-- The first `ℓ + 1` blocks. -/
abbrev initBlocks : Fin (ℓ + 1) → Multiset I := fun j => b j.castSucc

/-- The black weight of the first `ℓ + 1` blocks. -/
abbrev initWeight : Multiset I := blockPrefix (initBlocks b) (ℓ + 1)

/-- The last block. -/
abbrev lastBlock : Multiset I := b (Fin.last (ℓ + 1))

omit [DecidableEq I] in
theorem blockPrefix_initBlocks {n : ℕ} (hn : n ≤ ℓ + 1) :
    blockPrefix b n = blockPrefix (initBlocks b) n := by
  rw [blockPrefix, blockPrefix, Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc,
    ite_eq_right_of_eq_false _ _ (eq_false (by simp only [Fin.val_last]; omega)), add_zero]
  rfl

omit [DecidableEq I] in
theorem blockPrefix_last : blockPrefix b (ℓ + 2) = initWeight b + lastBlock b := by
  rw [blockPrefix_succ b (Nat.lt_succ_self (ℓ + 1)), blockPrefix_initBlocks b le_rfl]
  rfl

omit [DecidableEq I] in
theorem blockStart_initBlocks {j : ℕ} (hj : j ≤ ℓ + 1) :
    blockStart b j = blockStart (initBlocks b) j := by
  rw [blockStart, blockStart, blockPrefix_initBlocks b hj]

theorem blockRoot_castSucc (r : Fin ℓ) (i : I) :
    blockRoot b r.castSucc i = blockRoot (initBlocks b) r i := by
  rw [blockRoot, blockRoot, Fin.val_castSucc, blockPrefix_initBlocks b (by omega)]

theorem blockRoot_last (i : I) : blockRoot b (Fin.last ℓ) i = (initWeight b).count i := by
  rw [blockRoot, Fin.val_last, blockPrefix_initBlocks b le_rfl]

end Blocks

section Loadings

variable (θ β : Multiset I)

omit [DecidableEq I] in
theorem seq_cast_injective {J : Type*} {μ μ' : Multiset J} (h : μ = μ') :
    Function.Injective (Seq.cast h) := by
  subst h
  exact fun _ _ h => h

omit [DecidableEq I] in
theorem seq_map_injective {J J' : Type*} {f : J → J'} (hf : Function.Injective f)
    {μ : Multiset J} : Function.Injective (Seq.map (ν' := μ) f) := by
  intro s s' h
  apply Subtype.ext
  funext a
  have := congrArg (fun z : Seq (μ.map f) => z.1 (Fin.cast (Multiset.card_map f μ).symm a)) h
  simpa [Seq.map] using hf this

omit [DecidableEq I] in
theorem twoPieceLoading_injective :
    Function.Injective fun p : Seq (stendhalWeight ℓ θ) × Seq β => twoPieceLoading θ β p.1 p.2 := by
  rintro ⟨t, u⟩ ⟨t', u'⟩ h
  simp only [twoPieceLoading, concatLoading] at h
  have h1 := seq_cast_injective _ h
  obtain ⟨h2, h3⟩ := Seq.append_inj.1 h1
  refine Prod.ext (seq_map_injective (addRedColor_injective ℓ) h2) ?_
  exact SingleRed.insertWord_injective (ν := β) (seq_map_injective
    (Sum.map_injective.2 ⟨Function.injective_id, fun _ _ _ => Subsingleton.elim _ _⟩) h3)

theorem twoPieceLoading_mem_rootSet (b : Fin (ℓ + 2) → Multiset I)
    {t : Seq (stendhalWeight ℓ (initWeight b))}
    (ht : t ∈ rootSet (initWeight b) (blockRoot (initBlocks b))) (u : Seq (lastBlock b)) :
    twoPieceLoading (initWeight b) (lastBlock b) t u ∈
      rootSet (initWeight b + lastBlock b) (blockRoot b) := by
  refine mem_rootSet.2 ⟨isRedOrdered_twoPieceLoading (mem_rootSet.1 ht).1 u, ?_⟩
  funext r i
  induction r using Fin.lastCases with
  | last => rw [blackCount_twoPieceLoading_last, blockRoot_last]
  | cast r =>
    rw [blackCount_twoPieceLoading_castSucc, (mem_rootSet.1 ht).2, blockRoot_castSucc]

/-- **The sequences of root function `α` of `b` are the two-piece loadings** `t λ_{ℓ+1} u`
with `t` of root function `α'` of the first `ℓ + 1` blocks. -/
theorem mem_rootSet_blockRoot_iff (b : Fin (ℓ + 2) → Multiset I)
    (s : Seq (stendhalWeight (ℓ + 1) (initWeight b + lastBlock b))) :
    s ∈ rootSet (initWeight b + lastBlock b) (blockRoot b) ↔
      ∃ t ∈ rootSet (initWeight b) (blockRoot (initBlocks b)), ∃ u : Seq (lastBlock b),
        twoPieceLoading (initWeight b) (lastBlock b) t u = s := by
  constructor
  · intro hs
    obtain ⟨θ', β', h, t, w, ht, hst⟩ := exists_twoPieceLoading_eq (mem_rootSet.1 hs).1
    have hθ : θ' = initWeight b := by
      ext i
      have := congrFun (congrFun (mem_rootSet.1 hs).2 (Fin.last ℓ)) i
      rw [← hst, blackCount_cast, blackCount_twoPieceLoading_last, blockRoot_last] at this
      exact this
    subst hθ
    have hβ : β' = lastBlock b := (add_right_inj _).1 h
    subst hβ
    refine ⟨t, mem_rootSet.2 ⟨ht, ?_⟩, w, hst⟩
    funext r i
    have := congrFun (congrFun (mem_rootSet.1 hs).2 r.castSucc) i
    rw [← hst, blackCount_cast, blackCount_twoPieceLoading_castSucc, blockRoot_castSucc] at this
    exact this
  · rintro ⟨t, ht, u, rfl⟩
    exact twoPieceLoading_mem_rootSet b ht u

end Loadings

end Categorification.Stendhal
