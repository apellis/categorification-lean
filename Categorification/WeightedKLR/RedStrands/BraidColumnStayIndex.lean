/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnChoice
import Categorification.WeightedKLR.RedStrands.BraidColumnBottomReconstruction
import Categorification.WeightedKLR.RedStrands.BraidColumnDiagramFiltration

/-!
# The stay index of a braid column

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.15. The column filtration of a cut `e(t) V e_{σλ}` (proof of Lemma 6.11) has one
layer for each eligible index `W`, with label the bottom `W⁻¹ t`. When `σ` reverses the red
strands, these labels are triangular for the number of pairs of a red strand left of a black
strand (`redBlackPairs`): the index `W₀` that keeps every black strand in its own block
(`braidColumnStayIndex`) has the fewest such pairs, and every other index strictly more
(`redBlackPairs_lt_of_ne_stay`). Every nonviolated bottom with red order `σ(1, …, ℓ)` is the
label of the stay index of some loading (`exists_stay_label`).

## Main results

* `redBlackPairs_braidBottom`: the pairs of an eligible bottom, black strand by black strand.
* `exists_stay_label`: every nonviolated bottom of red order `σ(1, …, ℓ)` is a stay label, and
  for `σ` strictly decreasing every other eligible index has strictly more pairs.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra Equiv FirstWeight BraidColumn BraidedStendhalAlgebra
open scoped BigOperators

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

private theorem perm_apply_inv' {d : ℕ} (φ : Perm (Fin d)) (x : Fin d) : φ (φ⁻¹ x) = x :=
  φ.apply_symm_apply x

private theorem perm_inv_apply' {d : ℕ} (φ : Perm (Fin d)) (x : Fin d) : φ⁻¹ (φ x) = x :=
  φ.symm_apply_apply x

/-- The number of pairs of a red strand left of a black strand of a loading. -/
def redBlackPairs (u : Seq μ) : ℕ :=
  ∑ y : Fin m, if (u.lbl y).isLeft then redsBefore u.lbl y.val else 0

theorem redBlackPairs_le (u : Seq μ) : redBlackPairs u ≤ m * ℓ := by
  have h := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin m))
    (fun y => if (u.lbl y).isLeft then redsBefore u.lbl y.val else 0) ℓ fun y _ => by
      split_ifs
      · rw [redsBefore_lbl]
        exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
      · exact Nat.zero_le _
  rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h
  exact h

omit [DecidableEq I] in
/-- The block starts left of a non-initial strand of block `q` are those of blocks `≤ q`. -/
theorem card_blockStart_lt (n : Fin ℓ → ℕ) {d : ℕ} (hn : (∑ r, (n r + 1)) = d)
    (g : Perm (Fin ℓ)) (q : Fin ℓ) (a : Fin (n q + 1)) (ha : a ≠ 0) :
    (Finset.univ.filter fun r =>
      braidBlockPositions n hn ⟨g r, 0⟩ < braidBlockPositions n hn ⟨q, a⟩).card = q.val + 1 := by
  have : (Finset.univ.filter fun r =>
      braidBlockPositions n hn ⟨g r, 0⟩ < braidBlockPositions n hn ⟨q, a⟩) =
      (Finset.Iic q).map g.symm.toEmbedding := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
      Finset.mem_Iic, Equiv.symm_symm]
    constructor
    · intro h
      by_contra hc
      exact absurd h (lt_asymm (braidBlockPositions_lt_of_lt n hn (not_le.1 hc) a 0))
    · intro h
      rcases h.lt_or_eq with h | h
      · exact braidBlockPositions_lt_of_lt n hn h 0 a
      · subst h
        exact (braidBlockPositions_lt_iff n hn (g r) 0 a).2 (Fin.pos_iff_ne_zero.2 ha)
  rw [this, Finset.card_map, Fin.card_Iic]

/-- In a loading whose red strands start the blocks, the reds left of a black strand of block
`q` are those of the blocks `≤ q`. -/
theorem redsBefore_blockStart (t : Seq μ) (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m)
    (g : Perm (Fin ℓ)) (hred : ∀ r, t.lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr (g r))
    (q : Fin ℓ) (a : Fin (n q + 1)) (ha : a ≠ 0) :
    redsBefore t.lbl (braidBlockPositions n hn ⟨q, a⟩).val = q.val + 1 := by
  have hp : ∀ r, redPos t r = braidBlockPositions n hn ⟨g.symm r, 0⟩ := fun r =>
    (eq_redPos (by rw [hred, Equiv.apply_symm_apply])).symm
  rw [redsBefore_lbl, ← card_blockStart_lt n hn g.symm q a ha]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hp, Fin.lt_def]

omit [DecidableEq I] in
/-- The bottom of a block-permuted wiring, block by block. -/
theorem lbl_braidBottom (b : Seq μ) (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m)
    (σ : Perm (Fin ℓ)) (φ : Perm (Fin m)) (r : Fin ℓ) (a : Fin (n (σ r) + 1)) :
    ((braidColumnBottomBlockIndex n hn σ φ)⁻¹ • b).lbl
        (braidBlockPositions (n ∘ σ) ((Equiv.sum_comp σ fun r => n r + 1).trans hn) ⟨r, a⟩) =
      (φ⁻¹ • b).lbl (braidBlockPositions n hn ⟨σ r, a⟩) := by
  rw [lbl_inv_smul, lbl_inv_smul, braidColumnBottomBlockIndex_apply]

/-- **The pairs of an eligible bottom** (Webster, arXiv:1309.3796v3, proof of Theorem 6.15): a
black strand of the top `b` coming from the bottom block `c` sits in block `σ⁻¹ c` of the
bottom, right of `σ⁻¹ c + 1` red strands. -/
theorem redBlackPairs_braidBottom (b : Seq μ) (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m)
    (σ : Perm (Fin ℓ)) (φ : Perm (Fin m))
    (hred : ∀ r : Fin ℓ, (φ⁻¹ • b).lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr r) :
    redBlackPairs ((braidColumnBottomBlockIndex n hn σ φ)⁻¹ • b) =
      ∑ x : Fin m, if (b.lbl x).isLeft then
        (σ.symm ((braidBlockPositions n hn).symm (φ⁻¹ x)).1).val + 1 else 0 := by
  set W := braidColumnBottomBlockIndex n hn σ φ
  have hn' : (∑ r, ((n ∘ σ) r + 1)) = m := (Equiv.sum_comp σ fun r => n r + 1).trans hn
  refine (Equiv.sum_comp (W⁻¹ : Perm (Fin m)) _).symm.trans
    (Finset.sum_congr rfl fun x _ => ?_)
  have hx : (W⁻¹ • b).lbl (W⁻¹ x) = b.lbl x := by
    rw [lbl_inv_smul, perm_apply_inv']
  change (if ((W⁻¹ • b).lbl (W⁻¹ x)).isLeft then
    redsBefore (W⁻¹ • b).lbl (W⁻¹ x).val else 0) = _
  rw [hx]
  split_ifs with hb
  · obtain ⟨⟨r, a⟩, hp⟩ : ∃ p, braidBlockPositions (n ∘ σ) hn' p = W⁻¹ x :=
      ⟨_, Equiv.apply_symm_apply _ _⟩
    have hWx : x = φ (braidBlockPositions n hn ⟨σ r, a⟩) := by
      rw [← braidColumnBottomBlockIndex_apply n hn σ φ r a]
      change x = W (braidBlockPositions (n ∘ σ) hn' ⟨r, a⟩)
      rw [hp, perm_apply_inv']
    have hφx : φ⁻¹ x = braidBlockPositions n hn ⟨σ r, a⟩ := by
      rw [hWx, perm_inv_apply']
    have ha : a ≠ 0 := by
      rintro rfl
      have h1 : b.lbl x = .inr (σ r) := by
        rw [← hred (σ r), ← hφx, lbl_inv_smul, perm_apply_inv']
      rw [h1] at hb
      simp at hb
    have hred' : ∀ q, (W⁻¹ • b).lbl (braidBlockPositions (n ∘ σ) hn' ⟨q, 0⟩) = .inr (σ q) :=
      fun q => (lbl_braidBottom b n hn σ φ q 0).trans (hred (σ q))
    rw [← hp, redsBefore_blockStart (W⁻¹ • b) (n ∘ σ) hn' σ hred' r a ha, hφx,
      Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · rfl

omit [DecidableEq I] in
/-- The identity wiring of a loading with red-led blocks is eligible. -/
theorem projectiveBlockIndex_one {b : Seq μ} (hb : IsRedOrdered b) :
    ProjectiveBlockIndex b 1 where
  bottom_ordered := by rw [inv_one, one_smul]; exact hb
  only_rightwards := by
    intro b' a i r _ h2
    simp only [b', inv_one, one_smul] at h2
    simpa using h2
  bottom_block_order := by
    intro b' a a' i j _ _ h _
    simpa using h

/-- The stay index of a loading with red-led blocks: every black strand stays in its block. -/
def braidColumnStayIndex (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m) (σ : Perm (Fin ℓ)) :
    Perm (Fin m) :=
  braidColumnBottomBlockIndex n hn σ 1

omit [DecidableEq I] in
theorem stay_inv_smul (b : Seq μ) (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m)
    (σ : Perm (Fin ℓ)) :
    (braidColumnStayIndex n hn σ)⁻¹ • b = braidBlockPermutation n hn σ • b := by
  rw [braidColumnStayIndex, braidColumnBottomBlockIndex_bottom, inv_one, one_smul]

theorem stay_mem_braidColumnIndexList {b : Seq μ} (hb : IsRedOrdered b) (n : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = m) (σ : Perm (Fin ℓ))
    (hred : ∀ r : Fin ℓ, b.lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr r) :
    braidColumnStayIndex n hn σ ∈ braidColumnIndexList b σ :=
  mem_braidColumnIndexList.2 ⟨n, hn, 1, projectiveBlockIndex_one hb, fun r => by
    rw [inv_one, one_smul]; exact hred r, rfl⟩

omit [DecidableEq I] in
/-- A black strand of a loading with red-led blocks is not at the start of its block. -/
theorem blockStart_ne_zero_of_isLeft {b : Seq μ} (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m)
    (g : Perm (Fin ℓ)) (hred : ∀ r : Fin ℓ, b.lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr (g r))
    {x : Fin m} (hb : (b.lbl x).isLeft) : ((braidBlockPositions n hn).symm x).2 ≠ 0 := by
  intro h
  obtain ⟨⟨r, a⟩, hp⟩ : ∃ p, (braidBlockPositions n hn).symm x = p := ⟨_, rfl⟩
  rw [hp] at h
  change a = 0 at h
  subst h
  have hx : x = braidBlockPositions n hn ⟨r, 0⟩ := by rw [← hp, Equiv.apply_symm_apply]
  rw [hx, hred] at hb
  simp at hb

/-- **The stay index has the fewest pairs** (Webster, arXiv:1309.3796v3, proof of Theorem 6.15):
for `σ` strictly decreasing, every other eligible index of the column at a loading with red-led
blocks has a bottom with strictly more pairs of a red strand left of a black strand. -/
theorem redBlackPairs_lt_of_ne_stay {σ : Perm (Fin ℓ)} (hσ : StrictAnti σ) {b : Seq μ}
    (hb : IsRedOrdered b) (n₀ : Fin ℓ → ℕ) (hn₀ : (∑ r, (n₀ r + 1)) = m)
    (hred₀ : ∀ r : Fin ℓ, b.lbl (braidBlockPositions n₀ hn₀ ⟨r, 0⟩) = .inr r)
    {W : Perm (Fin m)} (hW : W ∈ braidColumnIndexList b σ)
    (hne : W ≠ braidColumnStayIndex n₀ hn₀ σ) :
    redBlackPairs ((braidColumnStayIndex n₀ hn₀ σ)⁻¹ • b) < redBlackPairs (W⁻¹ • b) := by
  obtain ⟨n, hn, φ, hφ, hred, rfl⟩ := mem_braidColumnIndexList.1 hW
  have hred₁ : ∀ r : Fin ℓ, ((1 : Perm (Fin m))⁻¹ • b).lbl
      (braidBlockPositions n₀ hn₀ ⟨r, 0⟩) = .inr r := fun r => by
    rw [inv_one, one_smul]; exact hred₀ r
  have hφ₁ := projectiveBlockIndex_one hb
  rw [braidColumnStayIndex, redBlackPairs_braidBottom b n₀ hn₀ σ 1 hred₁,
    redBlackPairs_braidBottom b n hn σ φ hred]
  -- the blocks of the stay index
  let c₀ : Fin m → Fin ℓ := fun x => ((braidBlockPositions n₀ hn₀).symm ((1 : Perm (Fin m))⁻¹ x)).1
  let c : Fin m → Fin ℓ := fun x => ((braidBlockPositions n hn).symm (φ⁻¹ x)).1
  have hle : ∀ x, (b.lbl x).isLeft → c x ≤ c₀ x := fun x hx => by
    have h1 := (isAdmissibleChoice_blockChoice hφ hred hb).black x hx
    have h2 : redsBefore b.lbl x.val = (c₀ x).val + 1 := by
      have ha := blockStart_ne_zero_of_isLeft n₀ hn₀ 1 (fun r => hred₀ r) hx
      have := redsBefore_blockStart b n₀ hn₀ 1 (fun r => hred₀ r) _ _ ha
      rw [Sigma.eta, Equiv.apply_symm_apply] at this
      rw [this]
      rfl
    change (c x).val < redsBefore b.lbl x.val at h1
    rw [Fin.le_iff_val_le_val]
    omega
  have hanti : ∀ x, (b.lbl x).isLeft → σ.symm (c₀ x) ≤ σ.symm (c x) := fun x hx =>
    (hσ.le_iff_ge).1 (by simpa using hle x hx)
  have hsum : ∀ x ∈ (Finset.univ : Finset (Fin m)),
      (if (b.lbl x).isLeft then (σ.symm (c₀ x)).val + 1 else 0) ≤
        (if (b.lbl x).isLeft then (σ.symm (c x)).val + 1 else 0) := fun x _ => by
    split_ifs with hx
    · have := hanti x hx
      rw [Fin.le_iff_val_le_val] at this
      omega
    · exact le_rfl
  refine lt_of_le_of_ne (Finset.sum_le_sum hsum) fun heq => hne ?_
  have hterm := (Finset.sum_eq_sum_iff_of_le hsum).1 heq
  have hch : blockChoice n hn φ = blockChoice n₀ hn₀ 1 := funext fun x => by
    by_cases hx : (b.lbl x).isLeft
    · have := hterm x (Finset.mem_univ x)
      simp only [hx, ite_true, add_left_inj, Fin.val_inj] at this
      exact congrArg Fin.val (σ.symm.injective this).symm
    · have hr : (b.lbl x).isRight := by
        cases h : b.lbl x <;> simp_all
      rw [(isAdmissibleChoice_blockChoice hφ hred hb).red x hr,
        (isAdmissibleChoice_blockChoice hφ₁ hred₁ hb).red x hr]
  obtain ⟨rfl, rfl⟩ := blockChoice_injective hφ hred hφ₁ hred₁ hch
  rfl

/-- **Every nonviolated bottom is a stay label** (Webster, arXiv:1309.3796v3, proof of
Theorem 6.15): a nonviolated loading `u` of red order `σ(1, …, ℓ)` is the bottom `W₀⁻¹ b` of the
stay index `W₀` of the column at some red-ordered loading `b`, and for `σ` strictly decreasing
every other eligible index of that column has a bottom with strictly more pairs. -/
theorem exists_stay_label {σ : Perm (Fin ℓ)} (hσ : StrictAnti σ) (u : Seq μ)
    (hu : redWord u = (List.finRange ℓ).map σ) (hv : ¬ IsViolated u) :
    ∃ b : Seq μ, IsRedOrdered b ∧ ∃ W₀ ∈ braidColumnIndexList b σ, W₀⁻¹ • b = u ∧
      ∀ W ∈ braidColumnIndexList b σ, W ≠ W₀ → redBlackPairs u < redBlackPairs (W⁻¹ • b) := by
  obtain ⟨b, n, hn, hb, hred, hbu⟩ := exists_braidBottomBlockReconstruction u σ hu hv
  have hlab : (braidColumnStayIndex n hn σ)⁻¹ • b = u := by rw [stay_inv_smul, hbu]
  refine ⟨b, hb, _, stay_mem_braidColumnIndexList hb n hn σ hred, hlab, fun W hW hne => ?_⟩
  rw [← hlab]
  exact redBlackPairs_lt_of_ne_stay hσ hb n hn hred hW hne

end Categorification.Stendhal
