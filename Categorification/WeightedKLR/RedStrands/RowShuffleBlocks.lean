/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockShufflePermutation
import Categorification.WeightedKLR.RedStrands.BlockShuffleLoading

/-!
# Input blocks of a row shuffle

Combinatorics of the nested shuffles of a row of red blocks, for the proof of Webster,
arXiv:1309.3796v3, §6.1, Lemma 6.9 (v2: Lemma 6.8). Input blocks occupy consecutive positions
of the juxtaposed row (`inputBlock_le_of_le`), so adjacent bottom slots drawn from increasing
input blocks form an ascent between different blocks (`ascent_of_inputBlock_lt`). The inverse
of a row shuffle preserves the order inside each block (`preservesBlockOrder_shufflePerm_inv`).
For a row of single red strands, a black strand immediately left of a red strand at the bottom
of a compatible nonviolated shuffle is drawn from an earlier block
(`inputBlock_lt_of_black_red`).
-/

namespace Categorification.Stendhal.RedBlock
open KLR TypeA Equiv

variable {I : Type} {ℓ : ℕ}

theorem inputBlock_posL (B : RedBlock I ℓ) (row : List (RedBlock I ℓ)) (x : Fin B.weight.card) :
    inputBlock (B :: row) (Seq.posL (weightSum row) x) = 0 := by
  change inputBlock (B :: row) (blockEquiv (Seq.card_add' B.weight (weightSum row)) (.inl x)) = 0
  simp only [inputBlock, Equiv.symm_apply_apply]

theorem inputBlock_posR (B : RedBlock I ℓ) (row : List (RedBlock I ℓ))
    (y : Fin (weightSum row).card) :
    inputBlock (B :: row) (Seq.posR B.weight y) = (inputBlock row y).succ := by
  change inputBlock (B :: row) (blockEquiv (Seq.card_add' B.weight (weightSum row)) (.inr y)) = _
  simp only [inputBlock, Equiv.symm_apply_apply]

private theorem fin_add_cases {B : RedBlock I ℓ} {row : List (RedBlock I ℓ)}
    (x : Fin (weightSum (B :: row)).card) :
    (∃ a, x = Seq.posL (weightSum row) a) ∨ (∃ b, x = Seq.posR B.weight b) := by
  obtain ⟨y, rfl⟩ := (blockEquiv (Seq.card_add' B.weight (weightSum row))).surjective x
  rcases y with a | b
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr ⟨b, rfl⟩

/-- Input blocks occupy consecutive positions of the juxtaposed row. -/
theorem inputBlock_le_of_le : ∀ (row : List (RedBlock I ℓ)) {x y : Fin (weightSum row).card},
    x ≤ y → inputBlock row x ≤ inputBlock row y
  | [], x, _, _ => Fin.elim0 x
  | B :: row, x, y, hxy => by
    rcases fin_add_cases x with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [inputBlock_posL]; exact Nat.zero_le _
    · rcases fin_add_cases y with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · exact absurd hxy (not_le.2 (blockEquiv_inl_lt_inr _ b a))
      · rw [inputBlock_posR, inputBlock_posR]
        refine Nat.succ_le_succ (inputBlock_le_of_le row ?_)
        by_contra hlt
        push Not at hlt
        exact (not_lt.2 hxy) ((blockEquiv_inr_lt_inr _).2 hlt)

/-- Adjacent bottom slots drawn from increasing input blocks form an ascent between different
input blocks. -/
theorem ascent_of_inputBlock_lt (row : List (RedBlock I ℓ)) (u : ShuffleIndex row) (j : ℕ)
    (hj : j + 1 < (weightSum row).card)
    (hlt : inputBlock row (shufflePerm row u ⟨j, by omega⟩) <
      inputBlock row (shufflePerm row u ⟨j + 1, hj⟩)) :
    shufflePerm row u ⟨j, by omega⟩ < shufflePerm row u ⟨j + 1, hj⟩ ∧
      ¬ SameInputBlock row u j hj :=
  ⟨lt_of_not_ge fun hge => (inputBlock_le_of_le row hge).not_gt hlt, fun hs => hlt.ne hs⟩

/-- The inverse of a row shuffle preserves the order inside each input block. -/
theorem preservesBlockOrder_shufflePerm_inv : ∀ (row : List (RedBlock I ℓ)) (u : ShuffleIndex row),
    PreservesBlockOrder row ((shufflePerm row u)⁻¹ : Perm (Fin (weightSum row).card))
  | [], _ => trivial
  | B :: row, u => by
    let h := Seq.card_add' B.weight (weightSum row)
    have hinv : ((shufflePerm (B :: row) u)⁻¹ : Perm _) =
        u.1.1⁻¹ * blockPerm h 1 (shufflePerm row u.2)⁻¹ := by
      rw [shufflePerm_cons, mul_inv_rev]
      congr 1
    refine ⟨?_, ?_⟩
    · intro a b hab
      simp only [Function.comp_apply, hinv, Perm.mul_apply]
      change u.1.1⁻¹ (blockPerm h 1 _ (blockEquiv h (.inl a))) <
        u.1.1⁻¹ (blockPerm h 1 _ (blockEquiv h (.inl b)))
      rw [blockPerm_inl, blockPerm_inl]
      exact u.1.2.1 hab
    · have he : ((⇑((shufflePerm (B :: row) u)⁻¹ : Perm _)) ∘ Seq.posR B.weight) =
          (fun y => u.1.1⁻¹ (blockEquiv h (.inr y))) ∘ ((shufflePerm row u.2)⁻¹ : Perm _) := by
        funext y
        simp only [Function.comp_apply, hinv, Perm.mul_apply]
        change u.1.1⁻¹ (blockPerm h 1 _ (blockEquiv h (.inr y))) = _
        rw [blockPerm_inr]
      rw [he]
      exact PreservesBlockOrder.comp_right _ u.1.2.2 row _
        (preservesBlockOrder_shufflePerm_inv row u.2)

/-- In a row of single red strands with nonviolated local loadings, the red strand of a block
is its first position. -/
theorem red_le_of_sameInputBlock : ∀ (row : List (RedBlock I ℓ)), (∀ B ∈ row, B.size = 1) →
    ∀ (v : Loadings row), ¬ Violated row v →
    ∀ (q₁ q₂ : Fin (weightSum row).card) (r : Fin ℓ), (place row v).lbl q₂ = .inr r →
      inputBlock row q₁ = inputBlock row q₂ → q₂ ≤ q₁
  | [], _, _, _, q₁, _, _, _, _ => Fin.elim0 q₁
  | B :: row, hsize, v, hv, q₁, q₂, r, hr, hq => by
    rcases fin_add_cases q₂ with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rcases fin_add_cases q₁ with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · -- the red strand of the first block is its first position
        have hr' : (Seq.map B.colour v.1).lbl b = .inr r := by
          simpa only [place, Seq.lbl, Seq.append_posL] using hr
        rw [Seq.map_lbl] at hr'
        have hsz : B.size = 1 := hsize B List.mem_cons_self
        set b' := Fin.cast (Multiset.card_map B.colour B.localWeight) b with hb'
        obtain ⟨c, hc⟩ : ∃ c, v.1.lbl b' = .inr c := by
          rcases hb : v.1.lbl b' with i | c
          · rw [hb] at hr'; cases hr'
          · exact ⟨c, rfl⟩
        have hpos : 0 < Multiset.card B.localWeight := Nat.lt_of_le_of_lt (Nat.zero_le _) b'.isLt
        have h0 : ∃ c', v.1.lbl ⟨0, hpos⟩ = .inr c' := by
          rcases h0 : v.1.lbl ⟨0, hpos⟩ with i | c'
          · exact (hv (Or.inl ⟨hpos, by simp [h0]⟩)).elim
          · exact ⟨c', rfl⟩
        obtain ⟨c', hc'⟩ := h0
        have hcc : c = c' := by
          have := Fin.subsingleton_iff_le_one.2 (le_of_eq hsz)
          exact Subsingleton.elim _ _
        subst hcc
        have hb0 : b' = ⟨0, hpos⟩ := Stendhal.lbl_inj_of_inr v.1 c hc hc'
        have hv0 : b.val = 0 := by
          have := congrArg Fin.val hb0
          simpa [hb'] using this
        change b.val ≤ a.val
        omega
      · rw [inputBlock_posL, inputBlock_posR] at hq
        exact absurd hq (Nat.succ_ne_zero _)
    · rcases fin_add_cases q₁ with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [inputBlock_posL, inputBlock_posR] at hq
        exact absurd hq.symm (Nat.succ_ne_zero _)
      · rw [inputBlock_posR, inputBlock_posR] at hq
        have hr' : (place row v.2).lbl b = .inr r := by
          simpa only [place, Seq.lbl, Seq.append_posR] using hr
        have := red_le_of_sameInputBlock row (fun B hB => hsize B (List.mem_cons_of_mem _ hB))
          v.2 (fun h => hv (Or.inr h)) a b r hr' (Nat.succ_injective hq)
        exact not_lt.1 fun hlt => not_lt.2 this ((blockEquiv_inr_lt_inr _).1 hlt)

/-- **A black strand left of a red strand comes from an earlier block** (Webster,
arXiv:1309.3796v3, proof of Lemma 6.9). For a row of single red strands, a compatible shuffle
`σ` with `σ • s = place v` of a nonviolated tuple `v` in the same red order, and a black strand
at position `j` of `s` immediately left of a red strand, the black strand is drawn from an
earlier input block than the red one. -/
theorem inputBlock_lt_of_black_red (row : List (RedBlock I ℓ)) (hsize : ∀ B ∈ row, B.size = 1)
    {ν : Multiset I} (h : weightSum row = stendhalWeight ℓ ν) (u : ShuffleIndex row)
    (s : Seq (weightSum row)) (v : Loadings row) (hv : ¬ Violated row v)
    (hp : shufflePerm row u • s = place row v)
    (ho : redWord (Seq.cast h s) = redWord (Seq.cast h (place row v)))
    (j : ℕ) (hj : j + 1 < (weightSum row).card) {i : I} {r : Fin ℓ}
    (hb : s.lbl ⟨j, by omega⟩ = .inl i) (hr : s.lbl ⟨j + 1, hj⟩ = .inr r) :
    inputBlock row (shufflePerm row u ⟨j, by omega⟩) <
      inputBlock row (shufflePerm row u ⟨j + 1, hj⟩) := by
  set σ := shufflePerm row u
  have hl (p : Fin (weightSum row).card) : (place row v).lbl (σ p) = s.lbl p := by
    rw [← hp]
    change s.lbl (σ.symm (σ p)) = _
    rw [Equiv.symm_apply_apply]
  have hs : σ⁻¹ • place row v = s := by rw [← hp, inv_smul_smul]
  have hred := red_order_cast h σ⁻¹ (place row v) (by rw [hs]; exact ho)
  have key := red_before_black row v (⇑σ⁻¹) (preservesBlockOrder_shufflePerm_inv row u) hv hred
  have hX : (place row v).lbl (σ ⟨j, by omega⟩) = .inl i := (hl _).trans hb
  have hR : (place row v).lbl (σ ⟨j + 1, hj⟩) = .inr r := (hl _).trans hr
  have hXR : σ ⟨j, by omega⟩ < σ ⟨j + 1, hj⟩ := by
    rcases lt_trichotomy (σ ⟨j, by omega⟩) (σ ⟨j + 1, hj⟩) with h1 | h1 | h1
    · exact h1
    · rw [h1] at hX; rw [hX] at hR; cases hR
    · have := key _ _ r i hR hX h1
      rw [show ∀ p, (σ⁻¹ : Perm _) (σ p) = p from fun p => σ.symm_apply_apply p,
        show ∀ p, (σ⁻¹ : Perm _) (σ p) = p from fun p => σ.symm_apply_apply p, Fin.lt_def] at this
      exact absurd this (by simp)
  refine lt_of_le_of_ne (inputBlock_le_of_le row hXR.le) fun he => ?_
  exact absurd (red_le_of_sameInputBlock row hsize v hv _ _ r hR he) (not_le.2 hXR)

end Categorification.Stendhal.RedBlock
