/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockShuffleLoading
import Categorification.WeightedKLR.RedStrands.BlockPairedCrossingLoading
import Categorification.WeightedKLR.RedStrands.StandardPartialKernel

/-!
# Black counts at the second red strand of the distinguished pair

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9 (v3: Proposition 6.10):
partial standardization of the local two-red standard module is the global standard module.
At a placed loading of an adjacent row `L, (λ_a λ_b), M`, the black strands left of `λ_b` are
those of the spectators of `L` and the black strands left of `λ_b` inside the pair
(`blockBlackCount_place_pair`). A shuffle compatible with the blocks of a nonviolated tuple only
moves black strands to the right of red strands (`blockBlackCount_le_of_shuffleLoading`).

These counts compare the global order at a placed loading with the local order in the pair:
at a nonviolated pair loading `σ` of red order `λ_a λ_b`, the black strands left of `λ_a` are
zero, so `σ` lies strictly above a loading `t₀` with no black strand left of a red strand
exactly when `σ` has a black strand left of `λ_b`.
-/

namespace Categorification.Stendhal.RedBlock

open KLR TypeA Equiv BraidedStendhalAlgebra

variable {I : Type} [DecidableEq I] {ℓ : ℕ}

/-- Relabelling the red strands of a block preserves the black counts at a red strand. -/
theorem blockBlackCount_map_colour (B : RedBlock I ℓ) (σ : Seq B.localWeight) (j : Fin B.size)
    (i : I) : blockBlackCount (Seq.map B.colour σ) {B.label j} i = blackCount σ j i := by
  rw [← blockBlackCount_singleton]
  unfold blockBlackCount
  refine Finset.card_bij (fun x _ => Fin.cast (Multiset.card_map _ _) x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      forall_eq, Seq.map_lbl] at hx ⊢
    refine ⟨?_, fun y hy => ?_⟩
    · rcases h : σ.lbl (Fin.cast (Multiset.card_map _ _) x) with a | r
      · rw [h] at hx; simpa using hx.1
      · rw [h] at hx; simp at hx
    · have := hx.2 (Fin.cast (Multiset.card_map _ _).symm y) (by
        simp only [Fin.cast_cast, Fin.cast_eq_self, hy]; rfl)
      exact this
  · intro x _ y _ h
    exact Fin.cast_injective _ h
  · intro y hy
    refine ⟨Fin.cast (Multiset.card_map _ _).symm y, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      forall_eq, Seq.map_lbl] at hy ⊢
    refine ⟨by simp [hy.1], fun z hz => ?_⟩
    rcases h : σ.lbl (Fin.cast (Multiset.card_map _ _) z) with a | r
    · rw [h] at hz; simp at hz
    · rw [h] at hz
      have hr : r = j := B.label.injective (Sum.inr_injective hz)
      subst hr
      have := hy.2 _ h
      exact this


variable (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)

/-- **Black counts at a red strand of the pair.** At a placed loading of the adjacent row, the
black strands of label `i` left of `λ_{f j}` are those of the spectators of `L` and those left
of `λ_{f j}` in the pair. -/
theorem blockBlackCount_place_pair (j : Fin 2) (i : I) :
    ∀ (L : List (Fin ℓ × Multiset I)) (s : Loadings (adjacentRow L M f β)), (∀ x ∈ L, x.1 ≠ f j) →
      blockBlackCount (place _ s) {f j} i =
        boundaryCount {f j} i (adjacentRow L M f β) + blackCount (pairLoading M f β L s) j i
  | [], s, _ => by
    have hh : Hits {f j} (RedBlock.mk 2 f β : RedBlock I ℓ).weight :=
      ⟨f j, Finset.mem_singleton_self _, (mem_red_iff _ _).2 ⟨j, rfl⟩⟩
    change blockBlackCount ((Seq.map _ s.1).append (place _ s.2)) {f j} i =
      boundaryCount {f j} i ((RedBlock.mk 2 f β : RedBlock I ℓ) :: M.map spectator) + _
    rw [count_append, ite_eq_left_of_eq_true _ _ (eq_true hh), boundaryCount,
      ite_eq_left_of_eq_true _ _ (eq_true hh), zero_add]
    exact blockBlackCount_map_colour ⟨2, f, β⟩ s.1 j i
  | x :: L, s, hL => by
    have hh : ¬ Hits {f j} (spectator x).weight := by
      rintro ⟨r, hr, hm⟩
      obtain ⟨_, he⟩ := (mem_red_iff _ _).1 hm
      exact hL x (List.mem_cons_self ..) ((he.trans (Finset.mem_singleton.1 hr)))
    change blockBlackCount ((Seq.map _ s.1).append (place _ s.2)) {f j} i =
      boundaryCount {f j} i (spectator x :: adjacentRow L M f β) + _
    rw [count_append, ite_eq_right_of_eq_false _ _ (eq_false hh), boundaryCount,
      ite_eq_right_of_eq_false _ _ (eq_false hh)]
    erw [blockBlackCount_place_pair j i L s.2 (fun y hy => hL y (List.mem_cons_of_mem _ hy))]
    rw [add_assoc]
    rfl

/-- A loading with no black strand left of any red strand lies strictly below every loading with
a black strand left of some red strand. -/
theorem stendhalLT_of_blackCount_pos {n : ℕ} {γ : Multiset I} {t σ : Seq (stendhalWeight n γ)}
    (ht : ∀ r i, blackCount t r i = 0) {r : Fin n} {i : I} (h : 0 < blackCount σ r i) :
    StendhalLT t σ :=
  ⟨fun r i => by rw [ht]; exact Nat.zero_le _, fun hle => by
    have := hle r i
    rw [ht] at this
    omega⟩

/-- In a nonviolated two-red loading of red order `λ_0 λ_1`, no black strand lies left of
`λ_0`. -/
theorem blackCount_zero_eq_zero {γ : Multiset I} {σ : Seq (stendhalWeight 2 γ)}
    (hσ : redWord σ = [0, 1]) (hv : ¬ IsViolated σ) (i : I) : blackCount σ 0 i = 0 := by
  rw [blackCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x - ⟨hx, hlt⟩
  obtain ⟨y, hy⟩ := exists_lbl_eq_inr σ 0
  have hpos : 0 < Multiset.card (stendhalWeight 2 γ) := Nat.zero_lt_of_lt x.isLt
  apply hv ⟨hpos, ?_⟩
  rcases h0 : σ.lbl ⟨0, hpos⟩ with a | r
  · rfl
  · exfalso
    have hxy := hlt y hy
    fin_cases r
    · rw [lbl_inj_of_inr σ 0 hy h0] at hxy
      exact Nat.not_lt_zero _ hxy
    · have h01 := lt_of_redWord_eq_append (L := []) (M := []) (a := 0) (b := 1) hσ hy h0
      exact Nat.not_lt_zero _ h01

/-- A nonviolated two-red loading of red order `λ_0 λ_1` strictly above a loading with no black
strand left of a red strand has a black strand left of `λ_1`. -/
theorem exists_blackCount_one_pos {γ : Multiset I} {t σ : Seq (stendhalWeight 2 γ)}
    (ht : ∀ r i, blackCount t r i = 0) (hσ : redWord σ = [0, 1]) (hv : ¬ IsViolated σ)
    (hlt : StendhalLT t σ) : ∃ i, 0 < blackCount σ 1 i := by
  by_contra hn
  push Not at hn
  apply hlt.2
  intro r i
  rw [ht]
  fin_cases r
  · exact (blackCount_zero_eq_zero hσ hv i).le
  · exact hn i

section Root

variable {ν : Multiset I} {a b : Fin ℓ} {L' M' : List (Fin ℓ)}
local notation "μ" => stendhalWeight ℓ ν

/-- The block root functions are monotone along Webster's order within one red order with
`a b` adjacent. -/
theorem adjacentBlockRoot_mono {s t : Seq μ} (hs : redWord s = L' ++ a :: b :: M')
    (ht : redWord t = L' ++ a :: b :: M') (hle : StendhalLE s t) :
    adjacentBlockRoot a b s ≤ adjacentBlockRoot a b t := by
  intro r i
  by_cases hr : r = a ∨ r = b
  · have e : ∀ u : Seq μ, adjacentBlockRoot a b u r = adjacentBlockRoot a b u b := fun u => by
      simp only [adjacentBlockRoot, hr, or_true, ↓reduceIte]
    rw [e, e, adjacentBlockRoot_pair hs, adjacentBlockRoot_pair ht]
    exact hle a i
  · have e : ∀ u : Seq μ, adjacentBlockRoot a b u r = blackCount u r := fun u => by
      funext i
      simp only [adjacentBlockRoot, hr, ↓reduceIte, blockBlackCount_singleton]
    rw [e, e]
    exact hle r i

/-- If `t` lies strictly above `s` in the same red order with `a b` adjacent and both have the
same block roots, then `t` has more black strands left of `b` than `s`. -/
theorem exists_blackCount_lt_of_adjacentBlockRoot_eq {s t : Seq μ}
    (hs : redWord s = L' ++ a :: b :: M') (ht : redWord t = L' ++ a :: b :: M')
    (hlt : StendhalLT s t) (hroot : adjacentBlockRoot a b t = adjacentBlockRoot a b s) :
    ∃ i, blackCount s b i < blackCount t b i := by
  by_contra hn
  push Not at hn
  apply hlt.2
  intro r i
  by_cases hrb : r = b
  · subst hrb; exact hn i
  by_cases hra : r = a
  · subst hra
    have := congrFun (congrFun hroot b) i
    rw [adjacentBlockRoot_pair ht, adjacentBlockRoot_pair hs] at this
    exact this.le
  · have := congrFun (congrFun hroot r) i
    simp only [adjacentBlockRoot, hra, hrb, or_self, ↓reduceIte, blockBlackCount_singleton]
      at this
    exact this.le

end Root

end Categorification.Stendhal.RedBlock
