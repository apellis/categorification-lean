/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockJuxtapositionCuts

/-!
# The two red orders of an adjacent-block product

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8. In the juxtaposition, every spectator
contributes its single red label, while the two red labels in the distinguished block
can occur in either order. The exterior black content is arbitrary.
-/

namespace Categorification.Stendhal.RedBlock
open KLR
variable {I : Type*} {ℓ : ℕ}

/-- A singleton spectator with its own black content. -/
abbrev spectator (x : Fin ℓ × Multiset I) : RedBlock I ℓ :=
  ⟨1, ⟨fun _ => x.1, fun _ _ _ => Subsingleton.elim ..⟩, x.2⟩

/-- The horizontal row with a single distinguished two-red block. -/
abbrev adjacentRow (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) :
    List (RedBlock I ℓ) := L.map spectator ++ ⟨2,f,β⟩ :: M.map spectator

private def reds {w : Multiset (I ⊕ Fin ℓ)} (s : Seq w) : List (Fin ℓ) :=
  (List.ofFn s.lbl).filterMap Sum.getRight?

private theorem reds_eq {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν)) : reds s = redWord s := by
  rw [reds,List.ofFn_eq_map,List.filterMap_map]; rfl

private theorem reds_cast {v w : Multiset (I ⊕ Fin ℓ)} (h : v = w) (s : Seq v) :
    reds (Seq.cast h s) = reds s := by subst w; rfl

private theorem reds_append {v w : Multiset (I ⊕ Fin ℓ)} (s : Seq v) (t : Seq w) :
    reds (s.append t) = reds s ++ reds t := by
  have hw : List.ofFn (s.append t).1 = List.ofFn s.1 ++ List.ofFn t.1 := by
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂
      rw [List.getElem_ofFn]
      by_cases hn : n < v.card
      · rw [Seq.append_apply_lt _ _ _ hn, List.getElem_append_left (by simpa using hn),
          List.getElem_ofFn]
      · rw [Seq.append_apply_ge _ _ _ (by exact Nat.le_of_not_lt hn), List.getElem_append_right (by simp; omega),
          List.getElem_ofFn]; simp
  exact (congrArg (List.filterMap Sum.getRight?) hw).trans List.filterMap_append

private theorem reds_map (B : RedBlock I ℓ) (s : Seq B.localWeight) :
    reds (Seq.map B.colour s) = (redWord s).map B.label := by
  have hw : List.ofFn (Seq.map B.colour s).lbl = (List.ofFn s.lbl).map B.colour := by
    rw [List.map_ofFn]
    exact (List.ofFn_congr (Multiset.card_map B.colour B.localWeight).symm (B.colour ∘ s.lbl)).symm
  rw [← reds_eq, reds, reds, hw, List.filterMap_map, List.map_filterMap]
  congr 1
  funext x; cases x <;> rfl

private theorem reds_perm {m : ℕ} {ν : Multiset I} (s : Seq (stendhalWeight m ν)) :
    (redWord s).Perm (List.finRange m) :=
  (List.perm_ext_iff_of_nodup (redWord_nodup _) (List.nodup_finRange _)).2
    (fun r => by simp [mem_redWord])

private theorem reds_spectator (x : Fin ℓ × Multiset I) (s : Seq (spectator x).localWeight) :
    reds (Seq.map (spectator x).colour s) = [x.1] := by
  have hp : (redWord s).Perm [0] := reds_perm s
  rw [reds_map, List.perm_singleton.1 hp]; rfl

private theorem reds_spectators : ∀ (L : List (Fin ℓ × Multiset I)) (s : Loadings (L.map spectator)),
    reds (place _ s) = L.map Prod.fst
  | [], _ => by simp [reds, weightSum, Seq.lbl]
  | x :: xs, s => by
    change reds ((Seq.map _ s.1).append _) = _
    rw [reds_append, reds_spectator x, reds_spectators xs s.2]; rfl

/-- The order of a juxtaposed loading can change only by the adjacent transposition. -/
theorem redWord_place_adjacent (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ)
    (β : Multiset I) {ν : Multiset I} (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν)
    (s : Loadings (adjacentRow L M f β)) :
    redWord (Seq.cast h (place _ s)) = L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst ∨
    redWord (Seq.cast h (place _ s)) = L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst := by
  rw [← reds_eq, reds_cast]
  clear h
  induction L with
  | nil =>
    have hp : (redWord s.1).Perm [0,1] := reds_perm s.1
    rcases List.perm_pair.1 hp with he | he
    · left; change reds ((Seq.map _ s.1).append _) = _
      rw [reds_append, reds_map, reds_spectators, he]; rfl
    · right; change reds ((Seq.map _ s.1).append _) = _
      rw [reds_append, reds_map, reds_spectators, he]; rfl
  | cons x xs ih =>
    have step : reds (place (adjacentRow (x :: xs) M f β) s) =
        x.1 :: reds (place (adjacentRow xs M f β) s.2) := by
      change reds ((Seq.map _ s.1).append _) = _
      rw [reds_append, reds_spectator x]; rfl
    rw [step]
    rcases ih s.2 with he | he <;> rw [he] <;> first | exact .inl rfl | exact .inr rfl

/-- The blocks of the row are precisely the fibers of the retained cuts. -/
theorem aligned_adjacent (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)
    (hn : (L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst).Nodup) :
    Aligned (f 0) (f 1) (adjacentRow L M f β) := by
  have hspec (x : Fin ℓ × Multiset I) (hx : x ∈ L ∨ x ∈ M) :
      ∃ r, ∀ z, Sum.inr z ∈ (spectator x).weight ↔ z ∈ cut (f 0) (f 1) r := by
    have hh : x.1 ≠ f 0 ∧ x.1 ≠ f 1 := by
      rcases hx with hx | hx
      · have h := List.nodup_append.1 hn |>.2.2 _ (List.mem_map_of_mem hx)
        exact ⟨fun he => h _ (by simp) he, fun he => h _ (by simp) he⟩
      · have h := (List.nodup_append.1 hn).2.1
        have hx' : x.1 ∈ M.map Prod.fst := List.mem_map_of_mem hx
        exact ⟨fun he => (List.nodup_cons.1 h).1 (.tail _ (he ▸ hx')),
          fun he => (List.nodup_cons.1 (List.nodup_cons.1 h).2).1 (he ▸ hx')⟩
    refine ⟨x.1, fun z => ?_⟩
    rw [mem_red_iff, cut, ite_eq_right (not_or.mpr hh), Finset.mem_singleton]
    exact ⟨fun ⟨_,he⟩ => he.symm, fun he => ⟨0,he.symm⟩⟩
  intro B hB
  rcases List.mem_append.1 hB with hm | hm
  · obtain ⟨x,hx,rfl⟩ := List.mem_map.1 hm; exact hspec x (.inl hx)
  · rcases List.mem_cons.1 hm with rfl | hm
    · refine ⟨f 0, fun z => ?_⟩
      rw [mem_red_iff]; simp only [cut, true_or, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨j,rfl⟩; fin_cases j <;> simp
      · rintro (rfl | rfl); exacts [⟨0,rfl⟩,⟨1,rfl⟩]
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.1 hm; exact hspec x (.inr hx)

end Categorification.Stendhal.RedBlock
