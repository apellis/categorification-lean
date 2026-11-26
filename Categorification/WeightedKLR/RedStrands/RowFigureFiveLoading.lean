/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.IteratedLeftStandard
import Categorification.WeightedKLR.RedStrands.BlockCrossingRowStandard
import Categorification.WeightedKLR.RedStrands.TwoPieceDecomposition

/-!
# Row loadings as Figure 5 row loadings

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Corollary 6.10. The row loading
`λ_1 u_1 ⋯ λ_ℓ u_ℓ` (`rowLoading`) whose word `u_{a+1}` is empty is a row of red blocks in the
sense of Proposition 6.9: spectators `λ_j u_j` for `j ≠ a, a + 1`, and the two-red block
`λ_a u_a λ_{a+1}` carrying the crossed Figure 5 loading. Swapping that block to the uncrossed
loading `λ_{a+1} λ_a u_a` gives the row loading of the swapped words, relabelled by the
transposition of `a` and `a + 1`.

All identities are proved on the words of the loadings (`ofFn_rowLoading`, `ofFn_place`).
-/

namespace Categorification.Stendhal.FirstWeight

open KLR RedBlock BraidedStendhalAlgebra

section Words

variable {I : Type}

theorem seq_ext_ofFn {J : Type*} {w : Multiset J} {s t : Seq w}
    (h : List.ofFn s.lbl = List.ofFn t.lbl) : s = t :=
  Subtype.ext (List.ofFn_injective h)

theorem ofFn_seqCast {J : Type*} {a b : Multiset J} (h : a = b) (s : Seq a) :
    List.ofFn (KLR.Seq.cast h s).lbl = List.ofFn s.lbl := by
  subst b
  rfl

theorem ofFn_seqMap {J K : Type*} (f : J → K) {a : Multiset J} (s : Seq a) :
    List.ofFn (KLR.Seq.map f s).lbl = (List.ofFn s.lbl).map f := by
  rw [List.map_ofFn]
  exact (List.ofFn_congr (Multiset.card_map f a).symm (f ∘ s.lbl)).symm

theorem ofFn_seqOfList {J : Type*} {a : Multiset J} (l : List J)
    (h : (l : Multiset J) = a) : List.ofFn (KLRAlgebra.Seq.ofList l h).lbl = l := by
  apply List.ext_getElem
  · rw [List.length_ofFn, ← Multiset.coe_card, h]
  · intro n h1 h2
    rw [List.getElem_ofFn]
    rfl

/-- The word `λ_1 u_1 ⋯ λ_n u_n` of the row loading. -/
def rowWord (n : ℕ) (u : Fin n → List I) : List (I ⊕ Fin n) :=
  (List.finRange n).flatMap fun j => .inr j :: (u j).map .inl

theorem ofFn_rowLoading : ∀ (n : ℕ) (u : Fin n → List I),
    List.ofFn (rowLoading n u).lbl = rowWord n u
  | 0, u => by
    rw [rowLoading, ofFn_seqCast]
    simp [rowWord, stendhalWeight]
  | n+1, u => by
    rw [rowLoading_succ, ofFn_seqCast, ofFn_twoPieceLoading, ofFn_rowLoading n, ofFn_seqOfList]
    simp [rowWord, List.finRange_succ_last, List.flatMap_append, List.flatMap_map,
      List.map_flatMap, Function.comp_def]

theorem ofFn_insertWord {ν : Multiset I} (u : Seq ν) :
    List.ofFn (SingleRed.insertWord ν u).lbl = .inr 0 :: (List.ofFn u.lbl).map .inl := by
  let z := SingleRed.insertWord ν u
  have hc : (stendhalWeight 1 ν).card = ν.card + 1 := by simp [stendhalWeight]
  have h₀ : z.lbl (Fin.cast hc.symm (0 : Fin (ν.card + 1))) = .inr 0 :=
    SingleRed.insertWord_head ν u
  have h₁ (i : Fin ν.card) : z.lbl (Fin.cast hc.symm i.succ) = .inl (u.lbl i) :=
    SingleRed.insertWord_black ν u i
  change List.ofFn z.lbl = _
  rw [List.ofFn_congr hc z.lbl, List.ofFn_succ, ← List.ofFn_comp']
  exact congrArg₂ List.cons h₀ (congrArg List.ofFn (funext h₁))

theorem ofFn_place_cons {ℓ : ℕ} (B : RedBlock I ℓ) (Bs : List (RedBlock I ℓ))
    (s : Loadings (B :: Bs)) :
    List.ofFn (place (B :: Bs) s).lbl =
      (List.ofFn s.1.lbl).map B.colour ++ List.ofFn (place Bs s.2).lbl := by
  rw [place, KLR.ofFn_append, ofFn_seqMap]

end Words

section Rows

variable {I : Type} {ℓ : ℕ}

/-- A spectator given by a red label and a black word. -/
abbrev wordSpec (x : Fin ℓ × List I) : Fin ℓ × Multiset I := (x.1, (x.2 : Multiset I))

/-- The loading `λ_r w` of the spectator of a red label `r` and a black word `w`. -/
def spectatorLoading (x : Fin ℓ × List I) : Seq (spectator (wordSpec x)).localWeight :=
  SingleRed.insertWord (x.2 : Multiset I) (KLRAlgebra.Seq.ofList x.2 rfl)

/-- The loadings of a list of spectators. -/
def spectatorLoadings : (M : List (Fin ℓ × List I)) → Loadings ((M.map wordSpec).map spectator)
  | [] => PUnit.unit
  | x :: M => (spectatorLoading x, spectatorLoadings M)

/-- The word of a list of spectators. -/
def spectatorWord (M : List (Fin ℓ × List I)) : List (I ⊕ Fin ℓ) :=
  M.flatMap fun x => .inr x.1 :: x.2.map .inl

variable (Mw : List (Fin ℓ × List I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)

/-- The loadings of a row whose spectators carry `λ_r w`, with `σ` in the distinguished
block. -/
def rowLoadings (σ : Seq (RedBlock.mk 2 f β : RedBlock I ℓ).localWeight) :
    (L : List (Fin ℓ × List I)) →
      Loadings (adjacentRow (L.map wordSpec) (Mw.map wordSpec) f β)
  | [] => (σ, spectatorLoadings Mw)
  | x :: L => (spectatorLoading x, rowLoadings σ L)

theorem setPairLoading_rowLoadings (σ τ : Seq (RedBlock.mk 2 f β : RedBlock I ℓ).localWeight) :
    ∀ L : List (Fin ℓ × List I),
      setPairLoading (Mw.map wordSpec) f β τ (L.map wordSpec) (rowLoadings Mw f β σ L) =
        rowLoadings Mw f β τ L
  | [] => rfl
  | x :: L => by
    change (spectatorLoading x, setPairLoading (Mw.map wordSpec) f β τ (L.map wordSpec)
      (rowLoadings Mw f β σ L)) = _
    rw [setPairLoading_rowLoadings σ τ L]
    rfl

theorem ofFn_place_spectatorLoadings : ∀ M : List (Fin ℓ × List I),
    List.ofFn (place ((M.map wordSpec).map spectator) (spectatorLoadings M)).lbl =
      spectatorWord M
  | [] => rfl
  | x :: M => by
    change List.ofFn (place (_ :: _) (spectatorLoading x, spectatorLoadings M)).lbl = _
    rw [ofFn_place_cons, ofFn_place_spectatorLoadings M, spectatorLoading, ofFn_insertWord,
      ofFn_seqOfList]
    simp [spectatorWord, Function.comp_def]
    rfl

theorem ofFn_place_rowLoadings (σ : Seq (RedBlock.mk 2 f β : RedBlock I ℓ).localWeight) :
    ∀ L : List (Fin ℓ × List I),
      List.ofFn (place _ (rowLoadings Mw f β σ L)).lbl =
        spectatorWord L ++ (List.ofFn σ.lbl).map (RedBlock.mk 2 f β : RedBlock I ℓ).colour ++
          spectatorWord Mw
  | [] => by
    change List.ofFn (place (_ :: _) (σ, spectatorLoadings Mw)).lbl = _
    rw [ofFn_place_cons, ofFn_place_spectatorLoadings]
    simp [spectatorWord]
  | x :: L => by
    change List.ofFn (place (_ :: _) (spectatorLoading x, rowLoadings Mw f β σ L)).lbl = _
    rw [ofFn_place_cons, ofFn_place_rowLoadings σ L, spectatorLoading, ofFn_insertWord,
      ofFn_seqOfList]
    simp [spectatorWord, Function.comp_def]
    rfl

end Rows

section Concrete

variable {I : Type} {n m : ℕ}

theorem coe_ofFn_lbl {J : Type*} {w : Multiset J} (s : Seq w) :
    ((List.ofFn s.lbl : List J) : Multiset J) = w := by
  rw [← Fin.univ_val_map]
  exact s.2

/-- The red strand `λ_{n+1}` of `n + 2 + m` red strands, left of the distinguished pair. -/
abbrev leftPos (n m : ℕ) : Fin (n + 2 + m) := Fin.castAdd m (Fin.natAdd n 0)

/-- The red strand `λ_{n+2}`, right of the distinguished pair. -/
abbrev rightPos (n m : ℕ) : Fin (n + 2 + m) := Fin.castAdd m (Fin.natAdd n 1)

theorem finRange_split : List.finRange (n + 2 + m) =
    (List.finRange n).map (fun j => Fin.castAdd m (Fin.castAdd 2 j)) ++
      leftPos n m :: rightPos n m :: (List.finRange m).map (Fin.natAdd (n + 2)) := by
  rw [← List.ofFn_id, List.ofFn_add, List.ofFn_add]
  simp [List.ofFn_eq_map, List.ofFn_succ]
  rfl

/-- The distinguished pair of red strands: `f 0 = λ_{n+2}` and `f 1 = λ_{n+1}`. -/
def pairEmb (n m : ℕ) : Fin 2 ↪ Fin (n + 2 + m) :=
  ⟨fun i => Fin.castAdd m (Fin.natAdd n (Fin.rev i)), fun _ _ h =>
    Fin.rev_injective (Fin.natAdd_injective _ _ (Fin.castAdd_injective _ _ h))⟩

@[simp] theorem pairEmb_zero : pairEmb n m 0 = rightPos n m := rfl

@[simp] theorem pairEmb_one : pairEmb n m 1 = leftPos n m := rfl

/-- The spectators left of the distinguished pair in the row of `u`. -/
def leftWords (u : Fin (n + 2 + m) → List I) : List (Fin (n + 2 + m) × List I) :=
  (List.finRange n).map fun j =>
    (Fin.castAdd m (Fin.castAdd 2 j), u (Fin.castAdd m (Fin.castAdd 2 j)))

/-- The spectators right of the distinguished pair in the row of `u`. -/
def rightWords (u : Fin (n + 2 + m) → List I) : List (Fin (n + 2 + m) × List I) :=
  (List.finRange m).map fun j => (Fin.natAdd (n + 2) j, u (Fin.natAdd (n + 2) j))

theorem perm_crossedWord (w : List I) :
    ((Sum.inr 1 :: w.map Sum.inl ++ [Sum.inr 0] : List (I ⊕ Fin 2)) : Multiset _) =
      stendhalWeight 2 (w : Multiset I) := by
  rw [stendhalWeight, Fin.univ_val_map, Multiset.map_coe, Multiset.coe_add, Multiset.coe_eq_coe]
  simp [List.ofFn_succ]
  refine ((List.perm_append_singleton (Sum.inr (1 : Fin 2))
    (w.map (Sum.inl (β := Fin 2)) ++ [Sum.inr 0])).symm).trans ?_
  simp

theorem perm_uncrossedWord (w : List I) :
    ((Sum.inr 0 :: Sum.inr 1 :: w.map Sum.inl : List (I ⊕ Fin 2)) : Multiset _) =
      stendhalWeight 2 (w : Multiset I) := by
  rw [stendhalWeight, Fin.univ_val_map, Multiset.map_coe, Multiset.coe_add, Multiset.coe_eq_coe]
  simp [List.ofFn_succ]
  exact (List.perm_append_comm (l₁ := w.map Sum.inl) (l₂ := [Sum.inr 0, Sum.inr 1])).symm

/-- The crossed Figure 5 loading `λ_1 w λ_0` of two red strands. -/
def crossedLoading (w : List I) : Seq (stendhalWeight 2 (w : Multiset I)) :=
  KLRAlgebra.Seq.ofList _ (perm_crossedWord w)

/-- The uncrossed Figure 5 loading `λ_0 λ_1 w` of two red strands. -/
def uncrossedLoading (w : List I) : Seq (stendhalWeight 2 (w : Multiset I)) :=
  KLRAlgebra.Seq.ofList _ (perm_uncrossedWord w)

theorem rowWord_split (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []) :
    rowWord (n + 2 + m) u = spectatorWord (leftWords u) ++
      (List.ofFn (crossedLoading (u (leftPos n m))).lbl).map
        (RedBlock.mk 2 (pairEmb n m) (u (leftPos n m) : Multiset I) : RedBlock I _).colour ++
      spectatorWord (rightWords u) := by
  rw [rowWord, finRange_split, crossedLoading, ofFn_seqOfList]
  simp [List.flatMap_append, spectatorWord, leftWords, rightWords, List.flatMap_map, hu,
    Function.comp_def]

/-- The row of red blocks of `u`: spectators `λ_j u_j` for `j ≠ n + 1, n + 2`, and the pair
`λ_{n+1} λ_{n+2}` with the black content of `u_{n+1}`. -/
abbrev rowBlocks (u : Fin (n + 2 + m) → List I) : List (RedBlock I (n + 2 + m)) :=
  adjacentRow ((leftWords u).map wordSpec) ((rightWords u).map wordSpec) (pairEmb n m)
    (u (leftPos n m) : Multiset I)

/-- The loadings of `rowBlocks u` with the local loading `σ` in the distinguished pair. -/
abbrev rowBlockLoadings (u : Fin (n + 2 + m) → List I)
    (σ : Seq (stendhalWeight 2 (u (leftPos n m) : Multiset I))) : Loadings (rowBlocks u) :=
  rowLoadings (rightWords u) (pairEmb n m) _ σ (leftWords u)

theorem ofFn_place_rowBlockLoadings (u : Fin (n + 2 + m) → List I)
    (σ : Seq (stendhalWeight 2 (u (leftPos n m) : Multiset I))) :
    List.ofFn (place (rowBlocks u) (rowBlockLoadings u σ)).lbl =
      spectatorWord (leftWords u) ++ (List.ofFn σ.lbl).map
        (RedBlock.mk 2 (pairEmb n m) (u (leftPos n m) : Multiset I) : RedBlock I _).colour ++
      spectatorWord (rightWords u) :=
  ofFn_place_rowLoadings _ _ _ σ _

theorem weightSum_rowBlocks (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []) :
    weightSum (rowBlocks u) = stendhalWeight (n + 2 + m) (blockContent u) := by
  rw [← coe_ofFn_lbl (place _ (rowBlockLoadings u (crossedLoading _))), ofFn_place_rowBlockLoadings,
    ← rowWord_split u hu, ← ofFn_rowLoading, coe_ofFn_lbl]

/-- **The row loading of `u` is the crossed Figure 5 row loading**, when `u_{n+2}` is empty. -/
theorem rowLoading_eq_place (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []) :
    rowLoading (n + 2 + m) u = KLR.Seq.cast (weightSum_rowBlocks u hu)
      (place _ (rowBlockLoadings u (crossedLoading _))) :=
  seq_ext_ofFn (by rw [ofFn_seqCast, ofFn_place_rowBlockLoadings, ofFn_rowLoading, rowWord_split u hu])

/-- The transposition of the distinguished pair `λ_{n+1}, λ_{n+2}`. -/
abbrev pairSwap (n m : ℕ) : Equiv.Perm (Fin (n + 2 + m)) := Equiv.swap (leftPos n m) (rightPos n m)

theorem pairSwap_castAdd (j : Fin n) :
    pairSwap n m (Fin.castAdd m (Fin.castAdd 2 j)) = Fin.castAdd m (Fin.castAdd 2 j) :=
  Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)

theorem pairSwap_natAdd (j : Fin m) :
    pairSwap n m (Fin.natAdd (n + 2) j) = Fin.natAdd (n + 2) j :=
  Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)

theorem blockContent_comp_perm (u : Fin (n + 2 + m) → List I) (π : Equiv.Perm (Fin (n + 2 + m))) :
    blockContent (u ∘ π) = blockContent u :=
  Equiv.sum_comp π fun j => (u j : Multiset I)

/-- The row loading of the words of `u` with those of the distinguished pair swapped, as a
loading of the black content of `u`. -/
def swappedRowLoading (u : Fin (n + 2 + m) → List I) :
    Seq (stendhalWeight (n + 2 + m) (blockContent u)) :=
  KLR.Seq.cast (congrArg (stendhalWeight _) (blockContent_comp_perm u (pairSwap n m)))
    (rowLoading (n + 2 + m) (u ∘ pairSwap n m))

theorem ofFn_redPerm {ℓ : ℕ} {ν : Multiset I} (π : Equiv.Perm (Fin ℓ))
    (s : Seq (stendhalWeight ℓ ν)) :
    List.ofFn (Seq.redPerm π s).lbl = (List.ofFn s.lbl).map (Sum.map id π) := by
  rw [List.map_ofFn]
  rfl

/-- **The swapped row loading, relabelled by the transposition, is the uncrossed Figure 5 row
loading**, when `u_{n+2}` is empty. -/
theorem redPerm_swappedRowLoading (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []) :
    Seq.redPerm (pairSwap n m) (swappedRowLoading u) = KLR.Seq.cast (weightSum_rowBlocks u hu)
      (place _ (rowBlockLoadings u (uncrossedLoading _))) := by
  apply seq_ext_ofFn
  rw [ofFn_redPerm, swappedRowLoading, ofFn_seqCast, ofFn_seqCast, ofFn_place_rowBlockLoadings,
    ofFn_rowLoading, rowWord, finRange_split, uncrossedLoading, ofFn_seqOfList]
  simp [List.flatMap_append, spectatorWord, leftWords, rightWords, List.flatMap_map, hu,
    Function.comp_def, pairSwap_castAdd, pairSwap_natAdd, List.map_flatMap]

/-! ### The hypotheses of Proposition 6.9 at these loadings -/

theorem redWord_eq_filterMap {ℓ : ℕ} {ν : Multiset I} (s : Seq (stendhalWeight ℓ ν)) :
    redWord s = (List.ofFn s.lbl).filterMap Sum.getRight? := by
  rw [redWord, List.ofFn_eq_map, List.filterMap_map]
  rfl

theorem redWord_crossedLoading (w : List I) : redWord (crossedLoading w) = [1, 0] := by
  rw [redWord_eq_filterMap, crossedLoading, ofFn_seqOfList]
  simp [List.filterMap_append, List.filterMap_map, Function.comp_def]

theorem redWord_uncrossedLoading (w : List I) : redWord (uncrossedLoading w) = [0, 1] := by
  rw [redWord_eq_filterMap, uncrossedLoading, ofFn_seqOfList]
  simp [List.filterMap_map, Function.comp_def]

theorem one_lt_card_stendhalWeight_two (β : Multiset I) :
    1 < Multiset.card (stendhalWeight 2 β) := by
  simp [stendhalWeight]

theorem uncrossedLoading_lbl_zero (w : List I) :
    (uncrossedLoading w).lbl ⟨0, by simp [stendhalWeight]⟩ = .inr 0 := rfl

theorem uncrossedLoading_lbl_one (w : List I) :
    (uncrossedLoading w).lbl ⟨1, one_lt_card_stendhalWeight_two _⟩ = .inr 1 := rfl

theorem not_isViolated_of_ofFn {ℓ : ℕ} {μ : Multiset (I ⊕ Fin ℓ)} (s : Seq μ) {r : Fin ℓ}
    {l : List (I ⊕ Fin ℓ)} (hs : List.ofFn s.lbl = .inr r :: l) : ¬ IsViolated s := by
  rintro ⟨h, hl⟩
  have h0 := congrArg (fun l => l[0]?) hs
  simp only [List.getElem?_ofFn, List.getElem?_cons_zero] at h0
  simp only [h, ↓reduceDIte] at h0
  rw [Option.some_inj.mp h0] at hl
  simp at hl

theorem not_isViolated_spectatorLoading {ℓ : ℕ} (x : Fin ℓ × List I) :
    ¬ IsViolated (spectatorLoading x) :=
  not_isViolated_of_ofFn _ (by rw [spectatorLoading, ofFn_insertWord])

theorem not_violated_spectatorLoadings {ℓ : ℕ} : ∀ M : List (Fin ℓ × List I),
    ¬ Violated _ (spectatorLoadings M)
  | [] => id
  | x :: M => by
    rintro (h | h)
    · exact not_isViolated_spectatorLoading x h
    · exact not_violated_spectatorLoadings M h

theorem not_violated_rowLoadings {ℓ : ℕ} (Mw : List (Fin ℓ × List I)) (f : Fin 2 ↪ Fin ℓ)
    (β : Multiset I) (σ : Seq (RedBlock.mk 2 f β : RedBlock I ℓ).localWeight)
    (hσ : ¬ IsViolated σ) : ∀ L : List (Fin ℓ × List I),
      ¬ Violated _ (rowLoadings Mw f β σ L)
  | [] => by
    rintro (h | h)
    · exact hσ h
    · exact not_violated_spectatorLoadings Mw h
  | x :: L => by
    rintro (h | h)
    · exact not_isViolated_spectatorLoading x h
    · exact not_violated_rowLoadings Mw f β σ hσ L h

theorem not_violated_rowBlockLoadings (u : Fin (n + 2 + m) → List I) :
    ¬ Violated (rowBlocks u) (rowBlockLoadings u (crossedLoading _)) :=
  not_violated_rowLoadings _ _ _ _
    (not_isViolated_of_ofFn _ (by rw [crossedLoading, ofFn_seqOfList]; rfl)) _

theorem map_fst_leftWords (u : Fin (n + 2 + m) → List I) :
    ((leftWords u).map wordSpec).map Prod.fst =
      (List.finRange n).map fun j => Fin.castAdd m (Fin.castAdd 2 j) := by
  simp [leftWords, Function.comp_def]

theorem map_fst_rightWords (u : Fin (n + 2 + m) → List I) :
    ((rightWords u).map wordSpec).map Prod.fst = (List.finRange m).map (Fin.natAdd (n + 2)) := by
  simp [rightWords, Function.comp_def]

theorem finRange_eq_rowBlocks (u : Fin (n + 2 + m) → List I) :
    List.finRange (n + 2 + m) = ((leftWords u).map wordSpec).map Prod.fst ++
      pairEmb n m 1 :: pairEmb n m 0 :: ((rightWords u).map wordSpec).map Prod.fst := by
  rw [map_fst_leftWords, map_fst_rightWords, pairEmb_zero, pairEmb_one, finRange_split]

theorem map_pairSwap_finRange (u : Fin (n + 2 + m) → List I) :
    (List.finRange (n + 2 + m)).map (pairSwap n m) = ((leftWords u).map wordSpec).map Prod.fst ++
      pairEmb n m 0 :: pairEmb n m 1 :: ((rightWords u).map wordSpec).map Prod.fst := by
  rw [map_fst_leftWords, map_fst_rightWords, pairEmb_zero, pairEmb_one, finRange_split]
  simp [Function.comp_def, pairSwap_castAdd, pairSwap_natAdd]

theorem redWord_rowBlockLoadings (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []) :
    redWord (KLR.Seq.cast (weightSum_rowBlocks u hu)
        (place _ (rowBlockLoadings u (crossedLoading _)))) =
      ((leftWords u).map wordSpec).map Prod.fst ++
        pairEmb n m 1 :: pairEmb n m 0 :: ((rightWords u).map wordSpec).map Prod.fst := by
  rw [← rowLoading_eq_place u hu, (redWord_eq_finRange_iff _).2 (isRedOrdered_rowLoading _ u),
    finRange_eq_rowBlocks]

theorem redWord_swappedRowLoading (u : Fin (n + 2 + m) → List I) :
    redWord (swappedRowLoading u) = List.finRange (n + 2 + m) := by
  rw [swappedRowLoading, (redWord_eq_finRange_iff _).2]
  exact (isRedOrdered_cast_iff _ _).2 (isRedOrdered_rowLoading _ _)

theorem finRotate_val_of_ne {k : ℕ} (x : Fin k) (hx : (x : ℕ) ≠ k - 1) :
    (finRotate k x : ℕ) = x + 1 := by
  cases k with
  | zero => exact x.elim0
  | succ k => exact coe_finRotate_of_ne_last fun h => hx (by simp [h])

theorem finRotate_val_of_eq {k : ℕ} (x : Fin k) (hx : (x : ℕ) = k - 1) :
    (finRotate k x : ℕ) = 0 := by
  cases k with
  | zero => exact x.elim0
  | succ k =>
    have : x = Fin.last k := Fin.ext (by simpa using hx)
    subst this
    simp

/-- Rotating `x :: l` one step to the left gives `l ++ [x]`. -/
theorem finRotate_inv_smul_ofList {J : Type*} {μ : Multiset J} (x : J) (l : List J)
    (h₁ : ((x :: l : List J) : Multiset J) = μ) (h₂ : ((l ++ [x] : List J) : Multiset J) = μ) :
    (finRotate (Multiset.card μ))⁻¹ • KLRAlgebra.Seq.ofList (x :: l) h₁ =
      KLRAlgebra.Seq.ofList (l ++ [x]) h₂ := by
  have hlen : Multiset.card μ = l.length + 1 := by rw [← h₁]; simp
  apply Subtype.ext
  funext a
  change (KLRAlgebra.Seq.ofList (x :: l) h₁).lbl (finRotate _ a) =
    (KLRAlgebra.Seq.ofList (l ++ [x]) h₂).lbl a
  rw [KLRAlgebra.Seq.ofList_lbl, KLRAlgebra.Seq.ofList_lbl]
  by_cases ha : (a : ℕ) = Multiset.card μ - 1
  · simp only [finRotate_val_of_eq a ha, List.getElem_cons_zero]
    simp only [ha, hlen, Nat.add_sub_cancel, List.getElem_concat_length]
  · simp only [finRotate_val_of_ne a ha, List.getElem_cons_succ]
    rw [List.getElem_append_left (by omega)]

/-- **The braiding move of the Figure 5 pair**: rotating the uncrossed loading `λ_0 λ_1 w`
one step to the left gives the crossed loading `λ_1 w λ_0`. -/
theorem edgeBraid_crossedLoading (w : List I) :
    EdgeBraid (show 0 < Multiset.card (stendhalWeight 2 (w : Multiset I)) by
        simp [stendhalWeight]) 0 (finRotate _)⁻¹ (crossedLoading w) (uncrossedLoading w) where
  smul_eq := finRotate_inv_smul_ofList _ _ _ _
  last := by
    rw [crossedLoading, KLRAlgebra.Seq.ofList_lbl]
    simp [stendhalWeight]
  shift x hx := by
    rw [inv_inv]
    exact finRotate_val_of_ne x hx

end Concrete

end Categorification.Stendhal.FirstWeight
