/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AdjacentBlockRow

/-!
# Loading cuts of adjacent-block shuffles

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
A shuffle preserving the source red order can only move black strands to the
right of retained red boundaries when all of its input blocks are nonviolated.
A globally violated or strictly higher loading therefore has a violated block
in each of its compatible splits.
-/

namespace Categorification.Stendhal.RedBlock

open KLR TypeA Equiv
variable {I : Type*} {ℓ : ℕ}

/-- An interleaving preserves the order of the positions belonging to each input block.
The map sends positions in the juxtaposition to positions in the interleaving. -/
def PreservesBlockOrder {α : Type*} [Preorder α] :
    (Bs : List (RedBlock I ℓ)) → (Fin (weightSum Bs).card → α) → Prop
  | [], _ => True
  | B :: Bs, f => StrictMono (f ∘ Seq.posL (weightSum Bs)) ∧
      PreservesBlockOrder Bs (f ∘ Seq.posR B.weight)

private theorem mapped_black_has_red {B : RedBlock I ℓ} (s : Seq B.localWeight)
    (hs : ¬ IsViolated s) (x : Fin B.weight.card) {i : I}
    (hx : (Seq.map B.colour s).lbl x = .inl i) :
    ∃ y r, (Seq.map B.colour s).lbl y = .inr r ∧ y < x := by
  have hpos : 0 < B.localWeight.card := by simpa using Nat.zero_lt_of_lt x.isLt
  rcases he : s.lbl ⟨0,hpos⟩ with j | r
  · exact (hs ⟨hpos, by simp [he]⟩).elim
  · let y : Fin B.weight.card := ⟨0,by simpa using hpos⟩
    have hy : (Seq.map B.colour s).lbl y = .inr (B.label r) := by
      rw [Seq.map_lbl]; exact congrArg B.colour he
    refine ⟨y,_,hy,?_⟩
    exact Nat.pos_of_ne_zero fun hz => by rw [show x = y from Fin.ext hz,hy] at hx; cases hx

private theorem black_has_red {α : Type*} [Preorder α] : ∀ (Bs : List (RedBlock I ℓ))
    (s : Loadings Bs) (f : Fin (weightSum Bs).card → α),
    PreservesBlockOrder Bs f → ¬ Violated Bs s →
    ∀ x i, (place Bs s).lbl x = .inl i →
      ∃ y r, (place Bs s).lbl y = .inr r ∧ f y < f x
  | [], _, _, _, _ => fun x => Fin.elim0 x
  | B :: Bs, s, f, hf, hv => by
    rw [Seq.forall_pos]
    constructor
    · intro x i hx
      have hx' : (Seq.map B.colour s.1).lbl x = .inl i := by simpa [place, Seq.lbl] using hx
      obtain ⟨y,r,hy,hxy⟩ := mapped_black_has_red s.1 (fun h => hv (.inl h)) x hx'
      exact ⟨Seq.posL _ y,r,by simpa only [place,Seq.lbl,Seq.append_posL] using hy,hf.1 hxy⟩
    · intro x i hx
      have hx' : (place Bs s.2).lbl x = .inl i := by
        simpa only [place, Seq.lbl, Seq.append_posR] using hx
      obtain ⟨y, r, hy, hxy⟩ :=
        black_has_red Bs s.2 (f ∘ Seq.posR B.weight) hf.2 (fun h => hv (.inr h)) x i hx'
      exact ⟨Seq.posR _ y,r,by simpa only [place,Seq.lbl,Seq.append_posR] using hy,hxy⟩

/-- A red strand before a black strand in a nonviolated block row stays before it
when an interleaving preserves the red order. -/
theorem red_before_black {α : Type*} [Preorder α] : ∀ (Bs : List (RedBlock I ℓ))
    (s : Loadings Bs) (f : Fin (weightSum Bs).card → α),
    PreservesBlockOrder Bs f → ¬ Violated Bs s →
    (∀ y z r r', (place Bs s).lbl y = .inr r → (place Bs s).lbl z = .inr r' →
      y < z → f y < f z) →
    ∀ y x r i, (place Bs s).lbl y = .inr r → (place Bs s).lbl x = .inl i → y < x → f y < f x
  | [], _, _, _, _, _ => fun y => Fin.elim0 y
  | B :: Bs, s, f, hf, hv, ho => by
    rw [Seq.forall_pos]
    constructor <;> intro y <;> rw [Seq.forall_pos] <;> constructor
    · intro x _ _ _ _ h; exact hf.1 (Seq.posL_lt_posL.mp h)
    · intro x r i hy hx _
      have hx' : (place Bs s.2).lbl x = .inl i := by
        simpa only [place, Seq.lbl, Seq.append_posR] using hx
      obtain ⟨z, r', hz, hzx⟩ :=
        black_has_red Bs s.2 (f ∘ Seq.posR B.weight) hf.2 (fun h => hv (.inr h)) x i hx'
      have red : (place (B::Bs) s).lbl (Seq.posR _ z) = .inr r' := by
        simpa only [place,Seq.lbl,Seq.append_posR] using hz
      exact (ho _ _ _ _ hy red (Seq.posL_lt_posR _ _)).trans hzx
    · intro x _ _ _ _ h; exact (Seq.not_posR_lt_posL _ _ h).elim
    · intro x r i hy hx h
      apply red_before_black Bs s.2 (f ∘ Seq.posR B.weight) hf.2 (fun h => hv (.inr h)) _ y x r i
      · simpa only [place,Seq.lbl,Seq.append_posR] using hy
      · simpa only [place,Seq.lbl,Seq.append_posR] using hx
      · exact Seq.posR_lt_posR.mp h
      · intro a b m n ha hb hab
        apply ho _ _ m n
        · simpa only [place,Seq.lbl,Seq.append_posR] using ha
        · simpa only [place,Seq.lbl,Seq.append_posR] using hb
        · exact Seq.posR_lt_posR.mpr hab



/-- Matching a loading to the local loadings of the recursively chosen binary shuffles. -/
def ShuffleLoading : (Bs : List (RedBlock I ℓ)) → Seq (weightSum Bs) → Loadings Bs → Prop
  | [], _, _ => True
  | B :: Bs, z, s =>
    ∃ (u : Shuffle (Seq.card_add' B.weight (weightSum Bs))) (t : Seq (weightSum Bs)),
      u.1 • z = (Seq.map B.colour s.1).append t ∧ ShuffleLoading Bs t s.2

theorem PreservesBlockOrder.comp_right {α β : Type*} [Preorder α] [Preorder β] (g : α → β)
    (hg : StrictMono g) : ∀ (Bs : List (RedBlock I ℓ)) (f : Fin (weightSum Bs).card → α),
    PreservesBlockOrder Bs f → PreservesBlockOrder Bs (g ∘ f)
  | [], _, _ => trivial
  | B :: Bs, f, hf => ⟨hg.comp hf.1, PreservesBlockOrder.comp_right g hg Bs (f ∘ Seq.posR B.weight) hf.2⟩

private theorem permutation_of_shuffle :
    ∀ (Bs : List (RedBlock I ℓ)) (z : Seq (weightSum Bs)) (s : Loadings Bs),
    ShuffleLoading Bs z s →
    ∃ p : Perm (Fin (weightSum Bs).card), p • place Bs s = z ∧ PreservesBlockOrder Bs p
  | [], z, _, _ => ⟨1,by apply Subtype.ext; funext x; exact Fin.elim0 x,trivial⟩
  | B :: Bs, z, s, ⟨u,t,hu,hs⟩ => by
    obtain ⟨p,hp,hf⟩ := permutation_of_shuffle Bs t s.2 hs
    let e := blockPerm (Seq.card_add' B.weight (weightSum Bs)) 1 p
    refine ⟨u.1⁻¹ * e,?_,?_,?_⟩
    · rw [mul_smul, place, show e • _ = _ from Seq.blockPerm_smul_append 1 p _ _, one_smul,
        hp, ← hu, inv_smul_smul]
    · change StrictMono (fun x => u.1⁻¹ (e (Seq.posL (weightSum Bs) x)))
      simpa only [e, Seq.posL, blockPerm_inl, Perm.one_apply] using u.2.1
    · have he : (fun x => (u.1⁻¹ * e) (Seq.posR B.weight x)) =
          (fun x => u.1⁻¹ (Seq.posR B.weight x)) ∘ p := by
        funext x; simp only [Perm.mul_apply,Function.comp_apply,e,Seq.posR,blockPerm_inr]
      change PreservesBlockOrder Bs (fun x => (u.1⁻¹ * e) (Seq.posR B.weight x))
      rw [he]; exact PreservesBlockOrder.comp_right _ u.2.2 Bs p hf

/-- Equal red words preserve the order of red positions under the loading permutation. -/
theorem red_order_cast {w : Multiset (I ⊕ Fin ℓ)} {ν : Multiset I}
    (h : w = stendhalWeight ℓ ν) (p : Perm (Fin w.card)) (s : Seq w)
    (ho : redWord (Seq.cast h (p • s)) = redWord (Seq.cast h s)) :
    ∀ y z r r', s.lbl y = .inr r → s.lbl z = .inr r' → y < z → p y < p z := by
  subst w
  have eq : redWord (p • s) = redWord ((1 : Perm (Fin (stendhalWeight ℓ ν).card)) • s) := by
    simpa using ho
  intro y z r r' hy hz hyz
  exact ((redWord_smul_eq_iff s p 1).mp eq y z r r' hy hz).2 (by simpa using hyz)

private theorem count_cast {w w' : Multiset (I ⊕ Fin ℓ)} [DecidableEq I]
    (h : w = w') (s : Seq w) (C : Finset (Fin ℓ)) (i : I) :
    blockBlackCount (Seq.cast h s) C i = blockBlackCount s C i := by subst w'; rfl

private theorem count_shuffle_le [DecidableEq I] (Bs : List (RedBlock I ℓ)) (s : Loadings Bs)
    (p : Perm (Fin (weightSum Bs).card)) (hf : PreservesBlockOrder Bs p) (hv : ¬ Violated Bs s)
    (ho : ∀ y z r r', (place Bs s).lbl y = .inr r → (place Bs s).lbl z = .inr r' →
      y < z → p y < p z)
    (C : Finset (Fin ℓ)) (i : I) :
    blockBlackCount (p • place Bs s) C i ≤ blockBlackCount (place Bs s) C i := by
  classical
  unfold blockBlackCount
  refine Finset.card_le_card_of_injOn p.symm ?_ p.symm.injective.injOn
  intro x hx
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  have hblack : (place Bs s).lbl (p.symm x) = .inl i := hx.1
  refine ⟨hblack,?_⟩
  intro y r hr hy
  by_contra hn
  have hyx : y < p.symm x := lt_of_le_of_ne (not_lt.mp hn) (fun he => by
    rw [he, hblack] at hy
    cases hy)
  have hyx' := red_before_black Bs s p hf hv ho y (p.symm x) r i hy hblack hyx
  rw [Equiv.apply_symm_apply] at hyx'
  have hpy : (p • place Bs s).lbl (p y) = .inr r := by
    change (place Bs s).lbl (p.symm (p y)) = _; rwa [Equiv.symm_apply_apply]
  exact (not_lt_of_gt hyx') (hx.2 (p y) r hr hpy)

/-- In a compatible interleaving, a globally leftmost black came from a locally violated block. -/
theorem violated_of_shuffleLoading_global (Bs : List (RedBlock I ℓ))
    (z : Seq (weightSum Bs)) (s : Loadings Bs) (hs : ShuffleLoading Bs z s)
    (hz : IsViolated z) : Violated Bs s := by
  by_contra hn
  obtain ⟨p,rfl,hf⟩ := permutation_of_shuffle Bs z s hs
  obtain ⟨n,hfirst⟩ := hz
  let x : Fin (weightSum Bs).card := ⟨0,n⟩
  change ((place Bs s).lbl (p.symm x)).isLeft at hfirst
  cases hd : (place Bs s).lbl (p.symm x) with
  | inr r => simp [hd] at hfirst
  | inl i =>
    obtain ⟨y,_,_,hy⟩ := black_has_red Bs s p hf hn _ _ hd
    rw [Equiv.apply_symm_apply] at hy
    exact Nat.not_lt_zero _ hy

/-- No coordinate with nonviolated internal loadings can be supported at a strictly higher
retained boundary in the same red order (Webster v2, Lemma 6.8, after (6.21)). -/
theorem violated_of_shuffleLoading_higher [DecidableEq I] {Bs : List (RedBlock I ℓ)}
    {ν : Multiset I} {a b : Fin ℓ} (h : weightSum Bs = stendhalWeight ℓ ν)
    (hal : Aligned a b Bs) (z : Seq (weightSum Bs)) (s : Loadings Bs) (hs : ShuffleLoading Bs z s)
    (ho : redWord (Seq.cast h z) = redWord (Seq.cast h (place Bs s)))
    (high : (fun r i => boundaryCount (cut a b r) i Bs) < adjacentBlockRoot a b (Seq.cast h z)) :
    Violated Bs s := by
  by_contra hn
  obtain ⟨p,rfl,hf⟩ := permutation_of_shuffle Bs z s hs
  apply high.not_ge
  intro r i
  change blockBlackCount (Seq.cast h _) (cut a b r) i ≤ boundaryCount (cut a b r) i Bs
  rw [count_cast,← count_place_of_not_violated r i s hal hn]
  exact count_shuffle_le Bs s p hf hn (red_order_cast h p _ ho) _ _

private theorem local_label_mem {w : Multiset (I ⊕ Fin ℓ)} (s : Seq w) {x} (h : x ∈ w) :
    ∃ y, s.lbl y = x := by
  rw [← s.2] at h
  obtain ⟨y,_,hy⟩ := Multiset.mem_map.1 h
  exact ⟨y,hy⟩

private theorem pair_positions (M : List (Fin ℓ × Multiset I)) (g : Fin 2 ↪ Fin ℓ)
    (β : Multiset I)
    {α : Type*} [Preorder α] :
    ∀ L (s : Loadings (adjacentRow L M g β))
    (p : Fin (weightSum (adjacentRow L M g β)).card → α),
    PreservesBlockOrder _ p →
    ∃ x y, (place _ s).lbl x = .inr (g 0) ∧ (place _ s).lbl y = .inr (g 1) ∧
      (x < y → p x < p y) ∧ (y < x → p y < p x)
  | [],s,p,hp => by
    let B : RedBlock I ℓ := ⟨2,g,β⟩
    have has (r : Fin 2) : ∃ x, (Seq.map B.colour s.1).lbl x = .inr (g r) :=
      local_label_mem _ ((mem_red_iff B _).2 ⟨r,rfl⟩)
    obtain ⟨x,hx⟩ := has 0
    obtain ⟨y,hy⟩ := has 1
    exact ⟨Seq.posL _ x,Seq.posL _ y,(Seq.append_posL _ _ x).trans hx,
      (Seq.append_posL _ _ y).trans hy,
      fun h => hp.1 (Seq.posL_lt_posL.mp h),fun h => hp.1 (Seq.posL_lt_posL.mp h)⟩
  | A :: L,s,p,hp => by
    obtain ⟨x, y, hx, hy, hxy, hyx⟩ :=
      pair_positions M g β L s.2 (p ∘ Seq.posR (spectator A).weight) hp.2
    exact ⟨Seq.posR _ x,Seq.posR _ y,(Seq.append_posR _ _ x).trans hx,
      (Seq.append_posR _ _ y).trans hy,
      fun h => hxy (Seq.posR_lt_posR.mp h),fun h => hyx (Seq.posR_lt_posR.mp h)⟩

private theorem cast_lt_of_order {w : Multiset (I ⊕ Fin ℓ)} {ν : Multiset I}
    (h : w = stendhalWeight ℓ ν) {s : Seq w} {L M : List (Fin ℓ)} {a b : Fin ℓ}
    (ho : redWord (Seq.cast h s) = L ++ a :: b :: M) {x y : Fin w.card}
    (hx : s.lbl x = .inr a) (hy : s.lbl y = .inr b) : x < y := by
  subst w
  exact BraidedStendhalAlgebra.lt_of_redWord_eq_append (by simpa using ho) hx hy

/-- For an adjacent row, the ambient source order determines the internal order of the
two-red block in every compatible split (Webster v2, §6.1, Lemma 6.8). -/
theorem redWord_place_eq_of_shuffleLoading (L M : List (Fin ℓ × Multiset I)) (g : Fin 2 ↪ Fin ℓ)
    (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M g β) = stendhalWeight ℓ ν)
    (z : Seq (weightSum (adjacentRow L M g β))) (s : Loadings (adjacentRow L M g β))
    (hs : ShuffleLoading _ z s)
    (ho : redWord (Seq.cast h z) = L.map Prod.fst ++ g 0 :: g 1 :: M.map Prod.fst) :
    redWord (Seq.cast h z) = redWord (Seq.cast h (place _ s)) := by
  obtain ⟨p,rfl,hp⟩ := permutation_of_shuffle _ z s hs
  rcases redWord_place_adjacent L M g β h s with eq | rev
  · exact ho.trans eq.symm
  · obtain ⟨x,y,hx,hy,_,hyx⟩ := pair_positions M g β L s p hp
    have fromPerm (v) : (p • place _ s).lbl (p v) = (place _ s).lbl v := by
      change (place _ s).lbl (p.symm (p v)) = _; rw [Equiv.symm_apply_apply]
    exact ((cast_lt_of_order h ho ((fromPerm x).trans hx) ((fromPerm y).trans hy)).not_gt
      (hyx (cast_lt_of_order h rev hy hx))).elim

/-- **Each compatible shuffle of a bad source loading has an internally violated block.**
Webster v2, §6.1, the cut after (6.21) in Lemma 6.8. The ambient source order fixes the
relative order of the two reds in the paired block. -/
theorem violated_of_adjacent_shuffleLoading [DecidableEq I] (L M : List (Fin ℓ × Multiset I))
    (g : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}
    (h : weightSum (adjacentRow L M g β) = stendhalWeight ℓ ν)
    (z : Seq (weightSum (adjacentRow L M g β))) (s : Loadings (adjacentRow L M g β))
    (hs : ShuffleLoading _ z s)
    (ho : redWord (Seq.cast h z) = L.map Prod.fst ++ g 0 :: g 1 :: M.map Prod.fst)
    (bad : IsViolated z ∨
      (fun r i => boundaryCount (cut (g 0) (g 1) r) i (adjacentRow L M g β)) <
        adjacentBlockRoot (g 0) (g 1) (Seq.cast h z)) : Violated _ s := by
  rcases bad with hg | hh
  · exact violated_of_shuffleLoading_global _ z s hs hg
  · exact violated_of_shuffleLoading_higher h
      (aligned_adjacent L M g β (ho ▸ redWord_nodup _)) z s hs
      (redWord_place_eq_of_shuffleLoading L M g β h z s hs ho) hh

end Categorification.Stendhal.RedBlock
