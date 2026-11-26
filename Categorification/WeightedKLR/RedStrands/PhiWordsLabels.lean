/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.PhiDiagrams

/-!
# The bottom words of Lemma 5.19 under relabelling and induction

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Lemma 5.19. Properties of the words `phiWords L` of the bottoms `φ • s` used to match them with
the labels of the standard filtration of `T^λ e(s)`:

* the block assignments of a labelling have no repetitions (`nodup_assignments`);
* `phiWords` commutes with renaming the red letters along a map preserving their indices
  (`phiWords_map`), as when a red strand is added on the right;
* with no red letters, `phiWords L = [L]` (`phiWords_of_forall_isLeft`);
* the words of a loading with `n` red strands have `n` red letters (`redCount_ofFn_lbl`).
-/

namespace Categorification.Stendhal

open KLR

section Assignments

variable {I : Type*} {n : ℕ}

theorem nodup_assignList : ∀ (m : ℕ) (S : Fin m → List ℕ), (∀ p, (S p).Nodup) →
    (assignList m S).Nodup
  | 0, _, _ => List.nodup_singleton _
  | m + 1, S, hS => by
    rw [assignList]
    refine List.nodup_flatMap.2 ⟨fun g _ => (hS _).map fun a b h => ?_, ?_⟩
    · simpa using congrFun h (Fin.last m)
    · refine (nodup_assignList m _ fun p => hS _).imp fun {g g'} hne => ?_
      refine List.disjoint_left.2 fun {x} hx hx' => hne ?_
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨a', -, h⟩ := List.mem_map.1 hx'
      have := congrArg (fun f : Fin (m + 1) → ℕ => Fin.init f) h
      simpa [Fin.init_snoc] using this.symm

theorem nodup_assignments {m : ℕ} (lbl : Fin m → I ⊕ Fin n) : (assignments lbl).Nodup :=
  nodup_assignList m _ fun p => by
    unfold assignChoices
    split_ifs
    · exact List.nodup_singleton _
    · exact List.nodup_range

end Assignments

section Relabel

variable {I : Type*} {n n' : ℕ} (e : Fin n → Fin n') (he : ∀ r, (e r).val = r.val)

local notation "f" => Sum.map (id : I → I) e

include he in
theorem redAtLeast_map (k : ℕ) (x : I ⊕ Fin n) : redAtLeast k (f x) = redAtLeast k x := by
  rcases x with i | r
  · rfl
  · simp [redAtLeast, he]

include he in
theorem blockInsertList_map (i : I) (k : ℕ) (L : List (I ⊕ Fin n)) :
    blockInsertList i k (L.map f) = (blockInsertList i k L).map f := by
  unfold blockInsertList
  have := insertBefore_map f (redAtLeast k) (.inl i) L
  rw [show (redAtLeast k ∘ f) = redAtLeast k from funext (redAtLeast_map e he k)] at this
  exact this

theorem redCount_map (L : List (I ⊕ Fin n)) : redCount (L.map f) = redCount L := by
  unfold redCount
  rw [List.countP_map]
  congr 1
  funext x
  rcases x with i | r <;> rfl

include he in
theorem phiWordsRev_map : ∀ L : List (I ⊕ Fin n),
    phiWordsRev (L.map f) = (phiWordsRev L).map (List.map f)
  | [] => rfl
  | .inl i :: R => by
    rw [List.map_cons, show (f (.inl i) : I ⊕ Fin n') = .inl i from rfl, phiWordsRev,
      phiWordsRev, phiWordsRev_map R, redCount_map, List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun W _ => ?_
    rw [List.map_map]
    exact List.map_congr_left fun k _ => blockInsertList_map e he i k W
  | .inr r :: R => by
    rw [List.map_cons, show (f (.inr r) : I ⊕ Fin n') = .inr (e r) from rfl, phiWordsRev,
      phiWordsRev, phiWordsRev_map R, List.map_map, List.map_map]
    refine List.map_congr_left fun W _ => ?_
    simp

include he in
/-- `phiWords` commutes with renaming the red letters along an index-preserving map. -/
theorem phiWords_map (L : List (I ⊕ Fin n)) :
    phiWords (L.map f) = (phiWords L).map (List.map f) := by
  rw [phiWords, phiWords, ← List.map_reverse, phiWordsRev_map e he]

end Relabel

section Black

variable {I : Type*} {n : ℕ}

theorem phiWords_of_forall_isLeft (L : List (I ⊕ Fin n)) (hL : ∀ x ∈ L, x.isLeft) :
    phiWords L = [L] := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L x ih =>
    have hL' : ∀ y ∈ L, y.isLeft := fun y hy => hL y (List.mem_append_left _ hy)
    obtain ⟨i, rfl⟩ : ∃ i, x = .inl i := by
      rcases x with i | r
      · exact ⟨i, rfl⟩
      · simpa using hL _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hc : redCount L = 0 := by
      unfold redCount
      rw [List.countP_eq_zero]
      intro y hy
      have := hL' y hy
      rcases y with j | r <;> simp_all
    rw [phiWords_append_inl, ih hL', hc]
    simp only [zero_add, List.range_one, List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    rw [blockInsertList, insertBefore_of_forall]
    intro y hy
    have := hL' y hy
    rcases y with j | r
    · rfl
    · simp at this

end Black

section Loadings

variable {I : Type} {ℓ : ℕ} {ν : Multiset I}

theorem redCount_ofFn_lbl (s : Seq (stendhalWeight ℓ ν)) : redCount (List.ofFn s.lbl) = ℓ := by
  rw [redCount_eq_length_filterMap, (filterMap_ofFn_lbl_perm s).length_eq, List.length_finRange]

end Loadings

end Categorification.Stendhal
