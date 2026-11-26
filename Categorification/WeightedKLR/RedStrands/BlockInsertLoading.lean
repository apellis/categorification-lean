/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceDecomposition
import Categorification.WeightedKLR.RedStrands.BlackInduction
import Categorification.WeightedKLR.RedStrands.BlockInsertWord
import Categorification.WeightedKLR.RedStrands.PhiDiagrams

/-!
# Inserting a black strand at the end of a block

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Proposition 5.5 and the proof of Proposition 5.6. The red strands `λ_1, …, λ_n` of a loading cut
its black strands into the blocks `0, 1, …, n`: block `k` is the part right of the `k`-th red
strand and left of the `(k+1)`-st. The loading `t^{(k)}` (`blockInsertLoading i k t`) adds a
black strand coloured `i` at the right end of block `k`. In Proposition 5.5, `Fᵢ S_t` is filtered
by the standard modules `S_{t^{(k)}}`, `k = 0, …, n`; these are the loadings `𝐢_k, κ_k` of the
proof of Proposition 5.6.

The loading is defined on words: the new strand is inserted just before the first red strand
of index at least `k`, or at the end (`insertBefore`). This description needs no hypothesis on
the order of the red strands, so it is compatible with the decomposition `t = t' λ_{n} u` at the
last red strand (`twoPieceLoading`) for every `t'`.

## Main definitions

* `insertBefore`: insert an element before the first one satisfying a predicate.
* `blockInsertLoading i k t`: the loading `t^{(k)}`.

## Main results

* `ofFn_blockInsertLoading`: the word of `t^{(k)}`.
* `isRedOrdered_blockInsertLoading`: `t^{(k)}` is red-ordered when `t` is.
* `blockInsertLoading_twoPiece_of_le`, `blockInsertLoading_twoPiece_last`: insertion into
  `t' λ_{ℓ+1} u` happens in `t'` for `k ≤ ℓ`, and at the end of `u` for `k = ℓ + 1`.
* `blockInsertLoading_zero_red`: with no red strands, `t^{(0)}` appends the new strand.
-/

namespace Categorification.Stendhal

open KLR


variable {I : Type*} {n ℓ : ℕ}

@[simp] theorem redAtLeast_addRedColor (k : ℕ) (y : I ⊕ Fin ℓ) :
    redAtLeast k (addRedColor ℓ y) = redAtLeast k y := by
  rcases y with i | r <;> rfl

theorem redAtLeast_comp_addRedColor (k : ℕ) :
    (redAtLeast (I := I) (n := ℓ + 1) k) ∘ addRedColor ℓ = redAtLeast k :=
  funext fun y => redAtLeast_addRedColor k y

private theorem coe_ofFn_lbl {J : Type*} {μ : Multiset J} (s : Seq μ) :
    ((List.ofFn s.lbl : List J) : Multiset J) = μ := by
  rw [← Fin.univ_val_map]
  exact s.2

theorem coe_blockInsertList (i : I) (k : ℕ) {ν : Multiset I}
    (t : Seq (stendhalWeight n ν)) :
    ((blockInsertList i k (List.ofFn t.lbl) : List (I ⊕ Fin n)) : Multiset (I ⊕ Fin n)) =
      stendhalWeight n ((Singleton.singleton i : Multiset I) + ν) := by
  rw [Multiset.coe_eq_coe.2 (insertBefore_perm _ _ _), ← Multiset.cons_coe, coe_ofFn_lbl,
    ← stendhalWeight_addBlack, Multiset.cons_eq_add_singleton]
  rfl

/-- **The loading `t^{(k)}`**: `t` with a black strand coloured `i` added at the right end of
block `k` (Webster, arXiv:1309.3796v3, Proposition 5.5 and proof of Proposition 5.6). -/
def blockInsertLoading (i : I) (k : ℕ) {ν : Multiset I} (t : Seq (stendhalWeight n ν)) :
    Seq (stendhalWeight n ((Singleton.singleton i : Multiset I) + ν)) :=
  KLRAlgebra.Seq.ofList (blockInsertList i k (List.ofFn t.lbl)) (coe_blockInsertList i k t)

theorem seq_ext_ofFn' {J : Type*} {w : Multiset J} {s t : Seq w}
    (h : List.ofFn s.lbl = List.ofFn t.lbl) : s = t :=
  Subtype.ext (List.ofFn_injective h)

theorem ofFn_seqCast' {J : Type*} {a b : Multiset J} (h : a = b) (s : Seq a) :
    List.ofFn (KLR.Seq.cast h s).lbl = List.ofFn s.lbl := by
  subst b
  rfl

theorem ofFn_seqOfList' {J : Type*} {a : Multiset J} (l : List J)
    (h : (l : Multiset J) = a) : List.ofFn (KLRAlgebra.Seq.ofList l h).lbl = l := by
  apply List.ext_getElem
  · rw [List.length_ofFn, ← Multiset.coe_card, h]
  · intro m h1 h2
    rw [List.getElem_ofFn]
    rfl

theorem ofFn_seqSingleton' {J : Type*} {a : J} (s : Seq ({a} : Multiset J)) :
    List.ofFn s.lbl = [a] := by
  have hl : s.lbl = fun _ => a := funext fun j => Multiset.mem_singleton.mp (s.mem j)
  rw [hl]
  simp

@[simp] theorem ofFn_blockInsertLoading (i : I) (k : ℕ) {ν : Multiset I}
    (t : Seq (stendhalWeight n ν)) :
    List.ofFn (blockInsertLoading i k t).lbl = blockInsertList i k (List.ofFn t.lbl) :=
  ofFn_seqOfList' _ _

theorem isRedOrdered_blockInsertLoading (i : I) (k : ℕ) {ν : Multiset I}
    {t : Seq (stendhalWeight n ν)} (ht : IsRedOrdered t) :
    IsRedOrdered (blockInsertLoading i k t) := by
  rw [isRedOrdered_iff_ofFn] at ht ⊢
  rw [ofFn_blockInsertLoading, blockInsertList, filterMap_insertBefore _ _ _ rfl]
  exact ht

private theorem ofFn_append' {J : Type*} {μ ν' : Multiset J} (j : Seq μ) (c : Seq ν') :
    List.ofFn (j.append c).lbl = List.ofFn j.lbl ++ List.ofFn c.lbl :=
  KLR.ofFn_append j c

/-- The word of `u` with `i` appended, in the form of `cycProjIndEquiv`. -/
theorem ofFn_appendDefault {β : Multiset I} (i : I) (u : Seq β) :
    List.ofFn (KLR.Seq.cast (add_comm β (Singleton.singleton i)) (u.append default)).lbl =
      List.ofFn u.lbl ++ [i] := by
  rw [ofFn_seqCast', ofFn_append', ofFn_seqSingleton']

variable [DecidableEq I]

/-- **Insertion into `t' λ_{ℓ+1} u` at a block `k ≤ ℓ`** happens in `t'`. -/
theorem blockInsertLoading_twoPiece_of_le (i : I) {k : ℕ} (hk : k ≤ ℓ) {θ β : Multiset I}
    (t : Seq (stendhalWeight ℓ θ)) (u : Seq β) :
    blockInsertLoading i k (twoPieceLoading θ β t u) =
      KLR.Seq.cast (congrArg (stendhalWeight (ℓ + 1)) (add_assoc _ θ β))
        (twoPieceLoading ((Singleton.singleton i : Multiset I) + θ) β
          (blockInsertLoading i k t) u) := by
  apply seq_ext_ofFn'
  rw [ofFn_seqCast', ofFn_blockInsertLoading, ofFn_twoPieceLoading, ofFn_twoPieceLoading,
    ofFn_blockInsertLoading, blockInsertList, blockInsertList]
  by_cases hex : ∃ y ∈ (List.ofFn t.lbl), redAtLeast k y = true
  · have hex' : ∃ y ∈ (List.ofFn t.lbl).map (addRedColor ℓ), redAtLeast k y = true := by
      obtain ⟨y, hy, hpy⟩ := hex
      exact ⟨_, List.mem_map_of_mem hy, by rw [redAtLeast_addRedColor]; exact hpy⟩
    rw [insertBefore_append_of_exists _ _ _ _ hex',
      show (Sum.inl i : I ⊕ Fin (ℓ + 1)) = addRedColor ℓ (.inl i) from rfl,
      insertBefore_map, redAtLeast_comp_addRedColor]
  · push_neg at hex
    have hex' : ∀ y ∈ (List.ofFn t.lbl).map (addRedColor ℓ), redAtLeast k y = false := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      rw [redAtLeast_addRedColor]
      simpa using hex z hz
    have hex'' : ∀ y ∈ List.ofFn t.lbl, redAtLeast k y = false := fun y hy => by
      simpa using hex y hy
    rw [insertBefore_append_of_forall _ _ _ _ hex', insertBefore_of_forall _ _ _ hex'',
      insertBefore, if_pos (by simp [redAtLeast, hk])]
    simp

/-- **Insertion into `t' λ_{ℓ+1} u` at the last block** appends the new strand to `u`. -/
theorem blockInsertLoading_twoPiece_last (i : I) {θ β : Multiset I}
    (t : Seq (stendhalWeight ℓ θ)) (u : Seq β) :
    blockInsertLoading i (ℓ + 1) (twoPieceLoading θ β t u) =
      KLR.Seq.cast (congrArg (stendhalWeight (ℓ + 1)) (add_left_comm θ _ β))
        (twoPieceLoading θ ((Singleton.singleton i : Multiset I) + β) t
          (KLR.Seq.cast (add_comm β (Singleton.singleton i)) (u.append default))) := by
  apply seq_ext_ofFn'
  rw [ofFn_seqCast', ofFn_blockInsertLoading, ofFn_twoPieceLoading, ofFn_twoPieceLoading,
    ofFn_appendDefault, blockInsertList, insertBefore_of_forall]
  · simp
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy
      rcases z with j | r
      · rfl
      · simp only [addRedColor, Sum.map_inr, redAtLeast, Fin.coe_castSucc, decide_eq_false_iff_not,
          not_le]
        omega
    · rcases List.mem_cons.1 hy with rfl | hy
      · simp [redAtLeast]
      · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy
        rfl

/-- **With no red strands**, `t^{(0)}` appends the new strand on the right. -/
theorem ofFn_blockInsertLoading_zero_red (i : I) (k : ℕ) {ν : Multiset I}
    (t : Seq (stendhalWeight 0 ν)) :
    List.ofFn (blockInsertLoading i k t).lbl = List.ofFn t.lbl ++ [.inl i] := by
  rw [ofFn_blockInsertLoading, blockInsertList, insertBefore_of_forall]
  intro y _
  rcases y with j | r
  · rfl
  · exact r.elim0

end Categorification.Stendhal
