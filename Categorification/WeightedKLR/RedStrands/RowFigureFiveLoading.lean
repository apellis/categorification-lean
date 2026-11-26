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

open KLR RedBlock

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

end Categorification.Stendhal.FirstWeight
