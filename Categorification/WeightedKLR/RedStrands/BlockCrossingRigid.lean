/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingRowStandard
import Categorification.WeightedKLR.RedStrands.StandardPartialKernel
import Categorification.WeightedKLR.RedStrands.CommonUpperLoading

/-!
# The cut after the crossed Figure 5 block is rigid

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9 (v3: Proposition
6.10). In the crossed Figure 5 loading of the distinguished block every black strand lies left of
the red strand `f 0`, which ends the block; the next block starts with its red strand. Hence the
red strand `f 0` has as many black strands to its left as the next red strand (or all of them),
and its cut is rigid (`isRigidCut_place_setPairLoading`).
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR BraidedStendhalAlgebra

variable {I : Type} [DecidableEq I] {ℓ : ℕ}

section Criteria

variable {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν

private theorem card_filter_lbl_eq (s : Seq μ) (x : I ⊕ Fin ℓ) :
    (Finset.univ.filter fun a => s.lbl a = x).card = Multiset.count x μ := by
  have h := congrArg (Multiset.count x) s.2
  rw [← h, count_map_univ, Finset.card_filter]

/-- A red strand with as many black strands to its left as a red strand to its right has a
rigid cut. -/
theorem isRigidCut_of_next (t : Seq μ) {b c : Fin ℓ} (hbc : redPos t b < redPos t c)
    (h : ∀ i, blackCount t c i ≤ blackCount t b i) : IsRigidCut t b := by
  intro u hu hle hoff
  funext i
  refine le_antisymm ?_ (hle b i)
  have hcb : c ≠ b := by
    rintro rfl
    exact lt_irrefl _ hbc
  calc blackCount u b i ≤ blackCount u c i :=
        blackCount_le_of_redPos_lt u (redPos_lt_redPos_of_redWord_eq hu hbc) i
    _ = blackCount t c i := by rw [hoff c hcb]
    _ ≤ blackCount t b i := h i

/-- A red strand with every black strand to its left has a rigid cut. -/
theorem isRigidCut_of_all (t : Seq μ) (b : Fin ℓ)
    (h : ∀ i, Multiset.count (.inl i) μ ≤ blackCount t b i) : IsRigidCut t b := by
  intro u _ hle _
  funext i
  refine le_antisymm ((?_ : blackCount u b i ≤ _).trans (h i)) (hle b i)
  rw [blackCount_eq_card_lt_redPos, ← card_filter_lbl_eq u]
  refine Finset.card_le_card fun x hx => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact hx.1

end Criteria

section Row

variable (M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I)
local notation "B₂" => (RedBlock.mk 2 f β : RedBlock I ℓ)
local notation "m₂" => Multiset.card (stendhalWeight 2 β)

private theorem card_filter_black {w : Multiset (I ⊕ Fin ℓ)} (s : Seq w) (i : I) :
    (Finset.univ.filter fun a => s.lbl a = .inl i).card = w.count (.inl i) := by
  rw [← congrArg (Multiset.count (.inl i)) s.2, count_map_univ, Finset.card_filter]

variable {M f β} in
/-- In the crossed Figure 5 loading, every black strand lies left of `f 0`. -/
private theorem pair_count {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)}
    {h0 : 0 < m₂} (hb : EdgeBraid h0 0 g σ t₂) (i : I) :
    blockBlackCount (Seq.map (B₂).colour σ) {f 0} i = (B₂).weight.count (.inl i) := by
  rw [← card_filter_black (Seq.map (B₂).colour σ) i, blockBlackCount]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    and_iff_left_iff_imp]
  intro hx y r hr hy
  subst hr
  rw [Seq.map_lbl] at hx hy
  have hy' : σ.lbl (Fin.cast (Multiset.card_map _ _) y) = .inr 0 := by
    rcases hσ : σ.lbl (Fin.cast (Multiset.card_map _ _) y) with j | j
    · rw [hσ] at hy; cases hy
    · rw [hσ] at hy
      have := f.injective (Sum.inr.inj hy)
      rw [this]
  have hx' : (σ.lbl (Fin.cast (Multiset.card_map _ _) x)).isLeft := by
    rcases hσ : σ.lbl (Fin.cast (Multiset.card_map _ _) x) with j | j
    · rfl
    · rw [hσ] at hx; cases hx
  have := hb.black_lt _ _ hx' hy'
  exact this

private theorem localCount_zero_spectator (x : Fin ℓ × Multiset I)
    (s : Seq (spectator x).localWeight) (hs : ¬ IsViolated s) (i : I) :
    blockBlackCount (Seq.map (spectator x).colour s) {x.1} i = 0 := by
  rw [blockBlackCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro y _ ⟨_, hy⟩
  have hpos : 0 < (spectator x).localWeight.card := by
    have := y.isLt; simpa using Nat.zero_lt_of_lt this
  rcases hz : s.lbl ⟨0, hpos⟩ with j | r
  · exact hs ⟨hpos, by simp [hz]⟩
  · let z : Fin (spectator x).weight.card := ⟨0, by simpa using hpos⟩
    have he : (Seq.map (spectator x).colour s).lbl z = .inr x.1 := by
      rw [Seq.map_lbl]; exact congrArg (spectator x).colour hz
    exact Nat.not_lt_zero _ (hy z _ (Finset.mem_singleton_self _) he)

omit [DecidableEq I] in
private theorem not_hits_spectator {x : Fin ℓ × Multiset I} {C : Finset (Fin ℓ)}
    (hx : x.1 ∉ C) : ¬ Hits C (spectator x).weight := by
  rintro ⟨r, hr, hm⟩
  obtain ⟨j, hj⟩ := (mem_red_iff (spectator x) r).1 hm
  rw [← hj] at hr
  exact hx hr

omit [DecidableEq I] in
private theorem hits_pair (r : Fin ℓ) : Hits {r} (B₂).weight ↔ r = f 0 ∨ r = f 1 := by
  constructor
  · rintro ⟨r', hr', hm⟩
    obtain ⟨j, hj⟩ := (mem_red_iff (B₂) r').1 hm
    rw [Finset.mem_singleton] at hr'
    subst hr'
    fin_cases j
    · exact Or.inl hj.symm
    · exact Or.inr hj.symm
  · rintro (rfl | rfl)
    · exact ⟨f 0, Finset.mem_singleton_self _, (mem_red_iff (B₂) _).2 ⟨0, rfl⟩⟩
    · exact ⟨f 1, Finset.mem_singleton_self _, (mem_red_iff (B₂) _).2 ⟨1, rfl⟩⟩

variable {M f β} in
/-- With a spectator right of the block, `f 0` and that spectator's red strand see the same
black strands. -/
private theorem count_next_eq {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)}
    {h0 : 0 < m₂} (hb : EdgeBraid h0 0 g σ t₂) (c : Fin ℓ × Multiset I)
    (hc : c.1 ≠ f 0 ∧ c.1 ≠ f 1) (i : I) :
    ∀ (L : List (Fin ℓ × Multiset I)) (s : Loadings (adjacentRow L (c :: M) f β)),
      (∀ x ∈ L, x.1 ≠ f 0 ∧ x.1 ≠ c.1) → pairLoading (c :: M) f β L s = σ →
      ¬ Violated _ s →
      blockBlackCount (place _ s) {c.1} i = blockBlackCount (place _ s) {f 0} i
  | [], s, _, hσ, hv => by
    change blockBlackCount ((Seq.map (B₂).colour s.1).append
        ((Seq.map (spectator c).colour s.2.1).append (place _ s.2.2))) {c.1} i =
      blockBlackCount ((Seq.map (B₂).colour s.1).append
        ((Seq.map (spectator c).colour s.2.1).append (place _ s.2.2))) {f 0} i
    have hs1 : s.1 = σ := hσ
    rw [count_append, count_append, ite_eq_right (fun h' => (hits_pair f β c.1).1 h' |>.elim hc.1 hc.2),
      ite_eq_left (⟨c.1, Finset.mem_singleton_self _, (mem_red_iff (spectator c) _).2 ⟨0, rfl⟩⟩),
      localCount_zero_spectator c s.2.1 (fun h' => hv (.inr (.inl h'))) i, add_zero, count_append,
      ite_eq_left ((hits_pair f β (f 0)).2 (Or.inl rfl)), hs1, pair_count hb]
  | x :: L, s, hL, hσ, hv => by
    change blockBlackCount ((Seq.map (spectator x).colour s.1).append (place _ s.2)) {c.1} i =
      blockBlackCount ((Seq.map (spectator x).colour s.1).append (place _ s.2)) {f 0} i
    have hx := hL x (List.mem_cons_self ..)
    rw [count_append, count_append,
      ite_eq_right (not_hits_spectator (by rw [Finset.mem_singleton]; exact hx.2)),
      ite_eq_right (not_hits_spectator (by rw [Finset.mem_singleton]; exact hx.1))]
    congr 1
    exact count_next_eq hb c hc i L s.2 (fun y hy => hL y (List.mem_cons_of_mem _ hy)) hσ
      (fun h' => hv (.inr h'))

variable {f β} in
/-- With no spectator right of the block, every black strand is left of `f 0`. -/
private theorem count_last_eq {σ t₂ : Seq (stendhalWeight 2 β)} {g : Equiv.Perm (Fin m₂)}
    {h0 : 0 < m₂} (hb : EdgeBraid h0 0 g σ t₂) (i : I) :
    ∀ (L : List (Fin ℓ × Multiset I)) (s : Loadings (adjacentRow L [] f β)),
      (∀ x ∈ L, x.1 ≠ f 0) → pairLoading [] f β L s = σ →
      blockBlackCount (place _ s) {f 0} i = (weightSum (adjacentRow L [] f β)).count (.inl i)
  | [], s, _, hσ => by
    change blockBlackCount ((Seq.map (B₂).colour s.1).append (place [] s.2)) {f 0} i =
      ((B₂).weight + 0).count (.inl i)
    have hs1 : s.1 = σ := hσ
    rw [count_append, ite_eq_left ((hits_pair f β (f 0)).2 (Or.inl rfl)), hs1, pair_count hb,
      add_zero]
  | x :: L, s, hL, hσ => by
    change blockBlackCount ((Seq.map (spectator x).colour s.1).append (place _ s.2)) {f 0} i =
      ((spectator x).weight + weightSum (adjacentRow L [] f β)).count (.inl i)
    rw [count_append, ite_eq_right (not_hits_spectator (by
        rw [Finset.mem_singleton]; exact hL x (List.mem_cons_self ..))),
      Multiset.count_add]
    congr 1
    exact count_last_eq hb i L s.2 (fun y hy => hL y (List.mem_cons_of_mem _ hy)) hσ

private theorem blockBlackCount_cast {u w : Multiset (I ⊕ Fin ℓ)} (e : u = w) (z : Seq u)
    (X : Finset (Fin ℓ)) (i : I) : blockBlackCount (Seq.cast e z) X i = blockBlackCount z X i := by
  subst w; rfl

/-- **The cut at `f 0` in a crossed Figure 5 row loading is rigid** (Webster,
arXiv:1309.3796v2, §6.1, the loading `P_{…;i_j;∅;…}` of Proposition 6.9). -/
theorem isRigidCut_place_setPairLoading {σ t₂ : Seq (stendhalWeight 2 β)}
    {g : Equiv.Perm (Fin m₂)} {h0 : 0 < m₂} (hb : EdgeBraid h0 0 g σ t₂)
    (L : List (Fin ℓ × Multiset I)) {ν : Multiset I}
    (h : weightSum (adjacentRow L M f β) = stendhalWeight ℓ ν) (u : Loadings (adjacentRow L M f β))
    (hs : ¬ Violated _ (setPairLoading M f β σ L u))
    (ht : redWord (Seq.cast h (place _ (setPairLoading M f β σ L u))) =
      L.map Prod.fst ++ f 1 :: f 0 :: M.map Prod.fst) :
    IsRigidCut (Seq.cast h (place _ (setPairLoading M f β σ L u))) (f 0) := by
  set t := Seq.cast h (place _ (setPairLoading M f β σ L u)) with ht_def
  have hcount (r : Fin ℓ) (i : I) : blackCount t r i =
      blockBlackCount (place _ (setPairLoading M f β σ L u)) {r} i := by
    rw [← blockBlackCount_singleton, ht_def, blockBlackCount_cast]
  have hn := ht ▸ redWord_nodup t
  have hpair := pairLoading_setPairLoading M f β σ L u
  have hL0 : ∀ x ∈ L, x.1 ≠ f 0 := fun x hx he => by
    have := List.disjoint_of_nodup_append hn (List.mem_map_of_mem hx)
    exact this (by rw [he]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
  cases M with
  | nil =>
    refine isRigidCut_of_all t (f 0) fun i => ?_
    rw [hcount, count_last_eq hb i L _ hL0 hpair, h]
  | cons c M' =>
    have hsuf : (f 1 :: f 0 :: c.1 :: M'.map Prod.fst).Nodup := (List.nodup_append.1 hn).2.1
    have hc : c.1 ≠ f 0 ∧ c.1 ≠ f 1 := by
      refine ⟨fun he => ?_, fun he => ?_⟩
      · exact (List.nodup_cons.1 (List.nodup_cons.1 hsuf).2).1 (he ▸ List.mem_cons_self ..)
      · exact (List.nodup_cons.1 hsuf).1
          (he ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hLc : ∀ x ∈ L, x.1 ≠ f 0 ∧ x.1 ≠ c.1 := fun x hx => ⟨hL0 x hx, fun he => by
      have := List.disjoint_of_nodup_append hn (List.mem_map_of_mem hx)
      exact this (by rw [he]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))⟩
    have hpw := ht ▸ redWord_pairwise_one t
    have hrel := (List.pairwise_cons.1 (List.pairwise_cons.1
      (List.pairwise_append.1 hpw).2.1).2).1 c.1 (List.mem_cons_self ..)
    have hlt : redPos t (f 0) < redPos t c.1 := hrel _ _ (lbl_redPos t _) (lbl_redPos t _)
    refine isRigidCut_of_next t hlt fun i => ?_
    rw [hcount, hcount, count_next_eq hb c hc i L _ hLc hpair hs]

end Row

end Categorification.Stendhal.RedBlock
