/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AdjacentBlockRoot
import Categorification.WeightedKLR.RedStrands.BlackCountTransport

/-!
# Cuts in a horizontal juxtaposition of red blocks

Webster, arXiv:1309.3796v2, §5.1 after Definition 5.4 and §6.1, proof of Lemma 6.8.
The minimum at a block boundary counts exactly the black strands in earlier blocks.
A locally leftmost black strand raises that count, though it need not be globally leftmost.
The cut is before the entire two-red block, independently of its internal red order.
-/

namespace Categorification.Stendhal
open KLR

variable {I : Type*} {ℓ : ℕ}

/-- A block of red weights in the alphabet of the full diagram, with fixed black content. -/
structure RedBlock (I : Type*) (ℓ : ℕ) where
  size : ℕ
  label : Fin size ↪ Fin ℓ
  black : Multiset I

namespace RedBlock
variable (B : RedBlock I ℓ)

abbrev localWeight := stendhalWeight B.size B.black
abbrev colour := Sum.map (id : I → I) B.label
abbrev weight := B.localWeight.map B.colour

abbrev weightSum : List (RedBlock I ℓ) → Multiset (I ⊕ Fin ℓ)
  | [] => 0
  | B :: Bs => B.weight + weightSum Bs

/-- One local loading per block, in horizontal order. -/
abbrev Loadings : List (RedBlock I ℓ) → Type _
  | [] => PUnit
  | B :: Bs => Seq B.localWeight × Loadings Bs

/-- Read the local loadings side by side in the common alphabet. -/
def place : (Bs : List (RedBlock I ℓ)) → Loadings Bs → Seq (weightSum Bs)
  | [], _ => Seq.nil
  | B :: Bs, s => (Seq.map B.colour s.1).append (place Bs s.2)

/-- Some component has a leftmost black strand. -/
def Violated : (Bs : List (RedBlock I ℓ)) → Loadings Bs → Prop
  | [], _ => False
  | _ :: Bs, s => IsViolated s.1 ∨ Violated Bs s.2

/-- A cut sees a block if that block contains one of its red labels. -/
def Hits (C : Finset (Fin ℓ)) (w : Multiset (I ⊕ Fin ℓ)) := ∃ r ∈ C, Sum.inr r ∈ w

theorem mem_red_iff (r : Fin ℓ) : Sum.inr r ∈ B.weight ↔ ∃ j, B.label j = r := by
  simp [weight, localWeight, colour, stendhalWeight, Multiset.map_add, Multiset.map_map,
    Function.comp_def]

private theorem exists_label_of_mem {w : Multiset (I ⊕ Fin ℓ)} (s : Seq w) {x} (hx : x ∈ w) :
    ∃ j, s.lbl j = x := by
  rw [← s.2] at hx
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hx
  exact ⟨j, hj⟩

variable [DecidableEq I]

open Classical in
/-- Concatenation counts up to the first piece containing a red label of `C`. -/
theorem count_append {u v : Multiset (I ⊕ Fin ℓ)} (s : Seq u) (t : Seq v)
    (C : Finset (Fin ℓ)) (i : I) : blockBlackCount (s.append t) C i =
      if Hits C u then blockBlackCount s C i else u.count (.inl i) + blockBlackCount t C i := by
  classical
  have hl (x : Fin u.card) :
      (∀ y r, r ∈ C → (s.append t).lbl y = .inr r → Seq.posL v x < y) ↔
        ∀ y r, r ∈ C → s.lbl y = .inr r → x < y := by
    rw [Seq.forall_pos]
    simp only [Seq.lbl, Seq.append_posL, Seq.append_posR, Seq.posL_lt_posL, Seq.posL_lt_posR,
      implies_true, and_true]
  have hr (x : Fin v.card) :
      (∀ y r, r ∈ C → (s.append t).lbl y = .inr r → Seq.posR u x < y) ↔
        ¬ Hits C u ∧ ∀ y r, r ∈ C → t.lbl y = .inr r → x < y := by
    rw [Seq.forall_pos]
    simp only [Seq.lbl, Seq.append_posL, Seq.append_posR, Seq.not_posR_lt_posL, Seq.posR_lt_posR]
    refine and_congr_left fun _ => ⟨?_, ?_⟩
    · rintro h ⟨r, hr, hy⟩
      obtain ⟨y, he⟩ := exists_label_of_mem s hy
      exact h y r hr he
    · intro h y r hC he
      exact h ⟨r, hC, he ▸ s.mem y⟩
  have hc : u.count (.inl i) = (Finset.univ.filter fun a => s.lbl a = .inl i).card := by
    rw [← congrArg (Multiset.count (.inl i)) s.2, count_map_univ, Finset.card_filter]
  rw [hc]
  simp only [blockBlackCount, Finset.card_filter, Seq.sum_pos, hl, hr]
  split_ifs with hc
  · simp [hc, Seq.lbl]
  · have h (x : Fin u.card) : ∀ y r, r ∈ C → s.lbl y = .inr r → x < y := by
      intro y r hr hy; exact (hc ⟨r,hr,hy ▸ s.mem y⟩).elim
    simp [hc, Seq.lbl]
    congr 1; ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_iff_left (h x)

/-- The boundary value for the juxtaposition: count whole preceding blocks, not the
black strands between two red strands of the same block. -/
noncomputable def boundaryCount (C : Finset (Fin ℓ)) (i : I) : List (RedBlock I ℓ) → ℕ
  | [] => 0
  | B :: Bs => open Classical in if Hits C B.weight then 0 else
      B.weight.count (.inl i) + boundaryCount C i Bs

theorem boundaryCount_le (C : Finset (Fin ℓ)) (i : I) : ∀ Bs (s : Loadings Bs),
    boundaryCount C i Bs ≤ blockBlackCount (place Bs s) C i
  | [], _ => Nat.zero_le _
  | B :: Bs, s => by
    classical
    rw [place, count_append, boundaryCount]
    split_ifs
    · exact Nat.zero_le _
    · exact Nat.add_le_add_left (boundaryCount_le C i Bs s.2) _

private theorem count_pos {w : Multiset (I ⊕ Fin ℓ)} {s : Seq w} (hv : IsViolated s)
    (C : Finset (Fin ℓ)) : ∃ i, 0 < blockBlackCount s C i := by
  obtain ⟨h, hv⟩ := hv
  rcases hx : s.lbl ⟨0, h⟩ with i | r
  · refine ⟨i, Finset.card_pos.2 ⟨⟨0,h⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx, ?_⟩⟩⟩
    intro y z _ hy
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [show y = ⟨0,h⟩ from Fin.ext h0, hx] at hy
    cases hy
  · simp [hx] at hv

omit [DecidableEq I] in
private theorem violated_map {s : Seq B.localWeight} (hv : IsViolated s) :
    IsViolated (Seq.map B.colour s) := by
  obtain ⟨h, hv⟩ := hv
  refine ⟨by simpa using h, ?_⟩
  rw [Seq.map_lbl]
  change (B.colour (s.lbl ⟨0,h⟩)).isLeft
  cases hx : s.lbl ⟨0,h⟩ with
  | inl j => rfl
  | inr r => simp [hx] at hv

/-- The red labels defining a retained cut. -/
def cut (a b r : Fin ℓ) : Finset (Fin ℓ) := if r = a ∨ r = b then {a,b} else {r}

private theorem self_mem_cut (a b r : Fin ℓ) : r ∈ cut a b r := by
  unfold cut; split_ifs with h
  · rcases h with rfl | rfl <;> simp
  · simp

private theorem cut_eq_of_mem {a b r z : Fin ℓ} (h : z ∈ cut a b r) : cut a b z = cut a b r := by
  unfold cut at *
  split_ifs at * <;> simp_all

/-- The reds of each component constitute one block of the specified partition. -/
def Aligned (a b : Fin ℓ) (Bs : List (RedBlock I ℓ)) : Prop :=
  ∀ B ∈ Bs, ∃ r, ∀ z, Sum.inr z ∈ B.weight ↔ z ∈ cut a b r

omit [DecidableEq I] in
private theorem hits_all {B : RedBlock I ℓ} {a b r : Fin ℓ}
    (hB : ∃ q, ∀ z, Sum.inr z ∈ B.weight ↔ z ∈ cut a b q) (hh : Hits (cut a b r) B.weight) :
    ∀ z, Sum.inr z ∈ B.weight ↔ z ∈ cut a b r := by
  obtain ⟨q,hq⟩ := hB
  obtain ⟨z,hz,hz'⟩ := hh
  rw [← cut_eq_of_mem hz, cut_eq_of_mem ((hq z).1 hz')]
  exact hq

private theorem localCount_zero {s : Seq B.localWeight} (hs : ¬ IsViolated s)
    {C : Finset (Fin ℓ)} (hall : ∀ r, Sum.inr r ∈ B.weight → r ∈ C) (i : I) :
    blockBlackCount (Seq.map B.colour s) C i = 0 := by
  rw [blockBlackCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x _ ⟨_,hx⟩
  have hpos : 0 < B.localWeight.card := by have := x.isLt; simpa using Nat.zero_lt_of_lt this
  rcases hy : s.lbl ⟨0,hpos⟩ with j | r
  · exact hs ⟨hpos, by simp [hy]⟩
  · let y : Fin B.weight.card := ⟨0, by simpa using hpos⟩
    have he : (Seq.map B.colour s).lbl y = .inr (B.label r) := by
      rw [Seq.map_lbl]; exact congrArg B.colour hy
    exact Nat.not_lt_zero _ (hx y _ (hall _ (he ▸ (Seq.map B.colour s).mem y)) he)

/-- On a tuple of nonviolated loadings every retained cut takes its boundary value. -/
theorem count_place_of_not_violated {a b : Fin ℓ} (r : Fin ℓ) (i : I) :
    ∀ {Bs} (s : Loadings Bs), Aligned a b Bs → ¬ Violated Bs s →
      blockBlackCount (place Bs s) (cut a b r) i = boundaryCount (cut a b r) i Bs
  | [], _, _, _ => by
    apply Finset.card_eq_zero.2; ext x; exact Fin.elim0 x
  | B :: Bs, s, ha, hv => by
    classical
    rw [place, count_append, boundaryCount]
    split_ifs with hh
    · exact localCount_zero B (fun h => hv (.inl h))
        (fun z => (hits_all (ha B (by simp)) hh z).1) i
    · rw [count_place_of_not_violated r i s.2 (fun z hz => ha z (.tail _ hz))
        (fun h => hv (.inr h))]

private theorem exists_strict {a b : Fin ℓ} : ∀ {Bs : List (RedBlock I ℓ)} (s : Loadings Bs), Aligned a b Bs →
    (∀ r : Fin ℓ, (weightSum Bs).count (.inr r) ≤ 1) → Violated Bs s →
    ∃ r i, Hits (cut a b r) (weightSum Bs) ∧
      boundaryCount (cut a b r) i Bs < blockBlackCount (place Bs s) (cut a b r) i
  | [], _, _, _, hv => hv.elim
  | B :: Bs, s, ha, hm, hv => by
    classical
    have hB := ha B (.head _)
    simp only [weightSum, Multiset.count_add] at hm
    rcases hv with hv | hv
    · obtain ⟨r,hr⟩ := hB
      have hh : Hits (cut a b r) B.weight :=
        ⟨r, self_mem_cut _ _ _, (hr r).2 (self_mem_cut _ _ _)⟩
      obtain ⟨i,hi⟩ := count_pos (violated_map B hv) (cut a b r)
      refine ⟨r,i,⟨r,self_mem_cut _ _ _,Multiset.mem_add.2 (.inl ((hr r).2 (self_mem_cut _ _ _)))⟩,?_⟩
      simpa only [place, boundaryCount, count_append, ite_eq_left hh] using hi
    · obtain ⟨r,i,⟨z,hz,hz'⟩,hi⟩ := exists_strict s.2 (fun z hz => ha z (.tail _ hz))
        (fun z => (Nat.le_add_left _ _).trans (hm z)) hv
      have hn : ¬ Hits (cut a b r) B.weight := by
        intro hh
        have h₁ := Multiset.count_pos.2 ((hits_all hB hh z).2 hz)
        have h₂ := Multiset.count_pos.2 hz'
        have := hm z
        omega
      refine ⟨r,i,⟨z,hz,Multiset.mem_add.2 (.inr hz')⟩,?_⟩
      simpa only [place, boundaryCount, count_append, ite_eq_right hn, Nat.add_lt_add_iff_left]
        using hi

/-- **Local violation raises a retained cut** (Webster, arXiv:1309.3796v2, §5.1 after
Definition 5.4; Lemma 6.8). This includes a black strand before the first red of the pair
in either order, but does not exclude black strands between the two reds. -/
theorem root_lt_of_violated {a b : Fin ℓ} {Bs : List (RedBlock I ℓ)} {ν : Multiset I}
    (h : weightSum Bs = stendhalWeight ℓ ν) (ha : Aligned a b Bs) (s : Loadings Bs)
    (hv : Violated Bs s) : (fun r i => boundaryCount (cut a b r) i Bs) <
      adjacentBlockRoot a b (Seq.cast h (place Bs s)) := by
  have hc (r : Fin ℓ) : (weightSum Bs).count (.inr r) ≤ 1 := by
    have hz : (ν.map (Sum.inl : I → I ⊕ Fin ℓ)).count (.inr r) = 0 :=
      Multiset.count_eq_zero_of_notMem (by simp)
    rw [h, stendhalWeight, Multiset.count_add, hz, zero_add]
    exact Multiset.nodup_iff_count_le_one.mp (Finset.univ.nodup.map Sum.inr_injective) _
  obtain ⟨r,i,-,hi⟩ := exists_strict s ha hc hv
  have he (C : Finset (Fin ℓ)) (j : I) : blockBlackCount (Seq.cast h (place Bs s)) C j =
      blockBlackCount (place Bs s) C j := by
    generalize (stendhalWeight ℓ ν) = w at h ⊢
    subst w; rfl
  refine ⟨fun q j => ?_, fun hle => hi.not_ge ?_⟩
  · change _ ≤ blockBlackCount _ (cut a b q) j
    rw [he]; exact boundaryCount_le _ _ _ _
  · exact he _ _ ▸ hle r i

end RedBlock
end Categorification.Stendhal
