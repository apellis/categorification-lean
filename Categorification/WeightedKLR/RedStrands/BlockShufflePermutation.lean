/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockCrossingCoordinates

/-!
# Right ascents of a block-row shuffle

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8. An adjacent right crossing
on an ascent either extends the row shuffle or crosses adjacent strands inside a
single upper block. Changing reduced expressions introduces braid terms in lower
crossing filtration.
-/

noncomputable section
namespace Categorification.Stendhal.RedBlock
open KLR TypeA Equiv

variable {I : Type} {ℓ : ℕ}

/-- The permutation represented by the chosen reduced word of a row shuffle. -/
def shufflePerm (row : List (RedBlock I ℓ)) (u : ShuffleIndex row) : Perm (Fin (weightSum row).card) :=
  wordProd _ (shuffleWord row u)

theorem shufflePerm_cons (B : RedBlock I ℓ) (row : List (RedBlock I ℓ))
    (u : ShuffleIndex (B :: row)) :
    shufflePerm (B :: row) u = blockPerm (Seq.card_add' B.weight (weightSum row)) 1 (shufflePerm row u.2) * u.1.1 := by
  change wordProd _ (shiftWord _ _ ++ canWord _ _) = _
  rw [wordProd_append, wordProd_canWord, wordProd_shiftWord (Seq.card_add' B.weight (weightSum row))
    (isReduced_shuffleWord row _).1]
  rfl

/-- Different nested parabolic shuffles represent different permutations. -/
theorem shufflePerm_injective : ∀ (row : List (RedBlock I ℓ)), Function.Injective (shufflePerm row)
  | [] => fun x y _ => @Subsingleton.elim Unit _ x y
  | B :: row => by
    intro x y h
    let e := parabolicEquiv (Seq.card_add' B.weight (weightSum row))
    have hp : e (1, shufflePerm row x.2, x.1) = e (1, shufflePerm row y.2, y.1) := by
      exact (shufflePerm_cons B row x).symm.trans (h.trans (shufflePerm_cons B row y))
    have hh := e.injective hp
    apply Prod.ext
    · exact congrArg (fun z => z.2.2) hh
    · exact shufflePerm_injective row (congrArg (fun z => z.2.1) hh)

/-- An adjacent crossing position entirely inside one of the incoming blocks. -/
def InsideBlock : List (RedBlock I ℓ) → ℕ → Prop
  | [], _ => False
  | B :: row, a => a + 1 < B.weight.card ∨ ∃ b, a = B.weight.card + b ∧ InsideBlock row b


/-- The index of the input block containing a position in the juxtaposed top row. -/
def inputBlock : (row : List (RedBlock I ℓ)) → Fin (weightSum row).card → ℕ
  | [], x => Fin.elim0 x
  | B :: row, x => match (blockEquiv (Seq.card_add' B.weight (weightSum row))).symm x with
      | .inl _ => 0
      | .inr y => (inputBlock row y).succ

private theorem inputBlock_left (B : RedBlock I ℓ) (row : List (RedBlock I ℓ)) (x : Fin B.weight.card) :
    inputBlock (B :: row) (blockEquiv (Seq.card_add' B.weight (weightSum row)) (.inl x)) = 0 := by
  simp only [inputBlock, Equiv.symm_apply_apply]

private theorem inputBlock_right (B : RedBlock I ℓ) (row : List (RedBlock I ℓ)) (y : Fin (weightSum row).card) :
    inputBlock (B :: row) (blockEquiv (Seq.card_add' B.weight (weightSum row)) (.inr y)) = (inputBlock row y).succ := by
  simp only [inputBlock, Equiv.symm_apply_apply]

/-- Whether two adjacent bottom slots of a shuffle are drawn from the same input block. -/
def SameInputBlock (row : List (RedBlock I ℓ)) (u : ShuffleIndex row) (j : ℕ)
    (hj : j+1 < (weightSum row).card) : Prop :=
  inputBlock row (shufflePerm row u ⟨j, by omega⟩) = inputBlock row (shufflePerm row u ⟨j+1,hj⟩)

theorem sameInputBlock_swap_iff (row : List (RedBlock I ℓ)) (u v : ShuffleIndex row) (j : ℕ)
    (hj : j+1 < (weightSum row).card) (hv : shufflePerm row v = shufflePerm row u * sadj _ j) :
    SameInputBlock row v j hj ↔ SameInputBlock row u j hj := by
  simp only [SameInputBlock, hv, Perm.mul_apply, sadj_apply_left hj, sadj_apply_right hj]
  exact eq_comm

theorem shufflePerm_right_ascent_target_descends (row : List (RedBlock I ℓ)) (u v : ShuffleIndex row)
    (j : ℕ) (hj : j+1 < (weightSum row).card)
    (ha : shufflePerm row u ⟨j,by omega⟩ < shufflePerm row u ⟨j+1,hj⟩)
    (hv : shufflePerm row v = shufflePerm row u * sadj _ j) :
    shufflePerm row v ⟨j+1,hj⟩ < shufflePerm row v ⟨j,by omega⟩ := by
  simpa only [hv, Perm.mul_apply, sadj_apply_left hj, sadj_apply_right hj] using ha

private theorem perm_mul_sadj_of_consecutive {m j : ℕ} (w : Perm (Fin m)) (hj : j + 1 < m)
    (hp : (w ⟨j+1,hj⟩).val = (w ⟨j,by omega⟩).val + 1) :
    w * sadj m j = sadj m (w ⟨j,by omega⟩).val * w := by
  have hm := (w ⟨j+1,hj⟩).isLt
  have ha : (w ⟨j,by omega⟩).val + 1 < m := hp ▸ hm
  rw [sadj, dite_eq_left hj, mul_swap_eq_swap_mul, sadj, dite_eq_left ha]
  congr 2
  exact Fin.ext hp

private theorem shufflePerm_ascent_cases : ∀ (row : List (RedBlock I ℓ))
    (u : ShuffleIndex row) (j : ℕ) (hj : j + 1 < (weightSum row).card),
    shufflePerm row u ⟨j, by omega⟩ < shufflePerm row u ⟨j + 1, hj⟩ →
      (∃ v : ShuffleIndex row, shufflePerm row v = shufflePerm row u * sadj _ j ∧ ¬ SameInputBlock row u j hj) ∨
      (SameInputBlock row u j hj ∧ InsideBlock row (shufflePerm row u ⟨j, by omega⟩).val ∧
        (shufflePerm row u ⟨j+1, hj⟩).val = (shufflePerm row u ⟨j, by omega⟩).val + 1)
  | [], _, j, hj, _ => by change j + 1 < 0 at hj; omega
  | B :: row, u, j, hj, asc => by
    let h := Seq.card_add' B.weight (weightSum row)
    let A := u.1
    let w := shufflePerm row u.2
    have pos (x : Fin (weightSum (B :: row)).card) :
        shufflePerm (B :: row) u x = blockPerm h 1 w (A.1 x) := by rw [shufflePerm_cons]; rfl
    obtain ⟨x,hx⟩ := (blockEquiv h).surjective (A.1 ⟨j, Nat.lt_of_succ_lt hj⟩)
    obtain ⟨y,hy⟩ := (blockEquiv h).surjective (A.1 ⟨j+1,hj⟩)
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        have adj := (shuffle_mul_sadj_left h A hj hx.symm hy.symm).1
        have h0 : (shufflePerm (B :: row) u ⟨j,by omega⟩).val = x.val := by
          rw [pos, ← hx, blockPerm_inl, Perm.one_apply, blockEquiv_inl_val]
        have h1 : (shufflePerm (B :: row) u ⟨j+1,hj⟩).val = y.val := by
          rw [pos, ← hy, blockPerm_inl, Perm.one_apply, blockEquiv_inl_val]
        right
        refine ⟨?_, ?_⟩
        · simp only [SameInputBlock, pos, ← hx, ← hy, blockPerm_inl, inputBlock_left]
        rw [h0,h1]
        exact ⟨Or.inl (adj ▸ y.isLt), adj.symm⟩
      | inr y =>
        have hu := (shuffle_right_ascent h A hj hx.symm hy.symm).1
        left
        refine ⟨(⟨A.1 * sadj _ j, hu⟩, u.2), (shufflePerm_cons B row _).trans ?_, ?_⟩
        · exact (mul_assoc _ _ _).symm.trans (congrArg (· * sadj _ j) (shufflePerm_cons B row u).symm)
        · simp only [SameInputBlock, pos, ← hx, ← hy, blockPerm_inl, blockPerm_inr,
            inputBlock_left, inputBlock_right, Nat.zero_ne_add_one, not_false_eq_true]
    | inr x =>
      cases y with
      | inl y =>
        rw [pos, pos, ← hx, ← hy, blockPerm_inr, blockPerm_inl] at asc
        exact (not_blockEquiv_inr_lt_inl h _ _ asc).elim
      | inr y =>
        obtain ⟨hxy, hu⟩ := shuffle_mul_sadj_right h A hj hx.symm hy.symm
        have hn : x.val + 1 < (weightSum row).card := hxy ▸ y.isLt
        have eqy : (⟨x.val + 1, hn⟩ : Fin (weightSum row).card) = y := Fin.ext hxy
        have h0 := pos ⟨j,by omega⟩
        have h1 := pos ⟨j+1,hj⟩
        rw [← hx, blockPerm_inr] at h0
        rw [← hy, blockPerm_inr] at h1
        have htail : w x < w ⟨x.val+1, hn⟩ := by
          rw [eqy]; exact (blockEquiv_inr_lt_inr h).1 (h0 ▸ h1 ▸ asc)
        have sameBlocks : SameInputBlock (B :: row) u j hj ↔ SameInputBlock row u.2 x.val hn := by
          simp only [SameInputBlock, h0, h1, inputBlock_right, Nat.succ.injEq, eqy]
          rfl
        rcases shufflePerm_ascent_cases row u.2 x.val hn htail with ⟨v, hv, hdiff⟩ | ⟨hsame, hi, hp⟩
        · left
          refine ⟨(A, v), (shufflePerm_cons B row _).trans (Eq.trans ?_
            (congrArg (· * sadj _ j) (shufflePerm_cons B row u).symm)), fun hs => hdiff (sameBlocks.1 hs)⟩
          change blockPerm h 1 (shufflePerm row v) * A.1 = (blockPerm h 1 w * A.1) * sadj _ j
          rw [mul_assoc, hu, ← mul_assoc, blockPerm_mul, one_mul, hv]
        · right
          refine ⟨sameBlocks.2 hsame, ?_⟩
          rw [h0, h1, blockEquiv_inr_val, blockEquiv_inr_val]
          rw [eqy] at hp
          exact ⟨Or.inr ⟨(w x).val, rfl, hi⟩, by change (w y).val = (w x).val + 1 at hp; omega⟩

/-- At an ascent a right crossing extends the shuffle by one crossing, or becomes
an internal adjacent crossing on the left of the same row shuffle. -/
theorem shuffleWord_right_ascent (row : List (RedBlock I ℓ)) (u : ShuffleIndex row)
    (j : ℕ) (hj : j + 1 < (weightSum row).card)
    (ha : shufflePerm row u ⟨j, by omega⟩ < shufflePerm row u ⟨j+1,hj⟩) :
    (∃! v : ShuffleIndex row, shufflePerm row v = shufflePerm row u * sadj _ j ∧
      (shuffleWord row v).length = (shuffleWord row u).length + 1 ∧ ¬ SameInputBlock row v j hj) ∨
    (SameInputBlock row u j hj ∧ InsideBlock row (shufflePerm row u ⟨j, by omega⟩).val ∧
      (shufflePerm row u ⟨j+1,hj⟩).val = (shufflePerm row u ⟨j,by omega⟩).val + 1 ∧
      shufflePerm row u * sadj _ j = sadj _ (shufflePerm row u ⟨j,by omega⟩).val * shufflePerm row u) := by
  rcases shufflePerm_ascent_cases row u j hj ha with ⟨v,hv,hd⟩ | ⟨hs, hi, hp⟩
  · left
    refine ⟨v, ⟨hv, ?_, fun hs => hd ((sameInputBlock_swap_iff row u v j hj hv).1 hs)⟩, fun y hy => shufflePerm_injective row (hy.1.trans hv.symm)⟩
    have hlen (a : ShuffleIndex row) : (shuffleWord row a).length = length _ (shufflePerm row a) :=
      (isReduced_shuffleWord row a).2
    rw [hlen, hlen, hv, length_mul_sadj_of_lt hj ha]
  · exact Or.inr ⟨hs, hi, hp, perm_mul_sadj_of_consecutive _ hj hp⟩


open KLRAlgebra

private theorem shuffleWord_reduced_append (row : List (RedBlock I ℓ)) (u : ShuffleIndex row)
    (j : ℕ) (hj : j+1 < (weightSum row).card)
    (ha : shufflePerm row u ⟨j, by omega⟩ < shufflePerm row u ⟨j+1,hj⟩) :
    IsReduced (weightSum row).card (shuffleWord row u ++ [j]) := by
  have red := isReduced_shuffleWord row u
  refine ⟨validWord_append.2 ⟨red.1, ?_⟩, ?_⟩
  · intro a h; obtain rfl := List.mem_singleton.1 h; exact hj
  · rw [List.length_append, List.length_singleton, wordProd_append, wordProd_singleton]
    exact congrArg (· + 1) red.2 |>.trans (length_mul_sadj_of_lt hj ha).symm

variable {k : Type*} [CommRing k] [DecidableEq I]
    (Q : (I ⊕ Fin ℓ) → (I ⊕ Fin ℓ) → MvPolynomial (Fin 2) k)

/-- The leading diagram at a right ascent is the extended shuffle or an internal
upper crossing. The braid error drops three crossings from the extended word, and
vanishes for incoming shuffles of length at most one. -/
theorem shuffleWord_right_ascent_crossing (row : List (RedBlock I ℓ)) (u : ShuffleIndex row)
    (j : ℕ) (hj : j+1 < (weightSum row).card)
    (ha : shufflePerm row u ⟨j, by omega⟩ < shufflePerm row u ⟨j+1,hj⟩)
    (s : Seq (weightSum row)) :
    let w := shuffleWord row u
    let a := (shufflePerm row u ⟨j, by omega⟩).val
    let close := fun (leading : KLRAlgebra k Q (weightSum row)) =>
      (ψw w * ψ j * e s - leading * e s ∈ filt k Q (weightSum row) (w.length - 2)) ∧
      (w.length ≤ 1 → ψw w * ψ j = leading)
    (∃ v : ShuffleIndex row, shufflePerm row v = shufflePerm row u * sadj _ j ∧
      (shuffleWord row v).length = w.length + 1 ∧ ¬ SameInputBlock row v j hj ∧ close (ψw (shuffleWord row v))) ∨
    (SameInputBlock row u j hj ∧ InsideBlock row a ∧ (shufflePerm row u ⟨j+1,hj⟩).val = a + 1 ∧
      shufflePerm row u * sadj _ j = sadj _ a * shufflePerm row u ∧ close (ψ a * ψw w)) := by
  intro w a close
  have extend : IsReduced (weightSum row).card (w ++ [j]) := shuffleWord_reduced_append row u j hj ha
  have compare (v : List ℕ) (hv : IsReduced (weightSum row).card v)
      (he : wordProd _ v = shufflePerm row u * sadj _ j) : close (ψw v) := by
    have same : wordProd (weightSum row).card (w ++ [j]) = wordProd _ v := by
      rw [wordProd_append, wordProd_singleton, he]; rfl
    exact ⟨rightCrossing_error_of_reduced extend hv same s,
      rightCrossing_eq_of_short_reduced extend hv same⟩
  rcases shuffleWord_right_ascent row u j hj ha with ⟨v, ⟨hv, hl, hd⟩, _⟩ | ⟨hs, hi, hp, he⟩
  · exact Or.inl ⟨v, hv, hl, hd, compare _ (isReduced_shuffleWord row v) hv⟩
  · refine Or.inr ⟨hs, hi, hp, he, ?_⟩
    have hpos : a+1 < (weightSum row).card := hp ▸ (shufflePerm row u ⟨j+1,hj⟩).isLt
    have same : wordProd (weightSum row).card (a :: w) = shufflePerm row u * sadj _ j := by
      rw [wordProd_cons, he]; rfl
    have red : IsReduced (weightSum row).card (a :: w) := by
      refine ⟨validWord_cons.2 ⟨hpos, (isReduced_shuffleWord row u).1⟩, ?_⟩
      rw [List.length_cons, same, length_mul_sadj_of_lt hj ha]
      exact congrArg (· + 1) (isReduced_shuffleWord row u).2
    exact compare _ red same

end Categorification.Stendhal.RedBlock
