/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Fin
import Categorification.TypeA.Length

/-!
# Reorder the blocks in the braid filtration index

Webster, arXiv:1309.3796v2, §5.4 just before Proposition 5.20 and §6.1, the
proof of Lemma 6.11. The blocks in a nonviolated loading consist of each red
strand together with the following black strands. A red permutation acts by
reordering the whole blocks, preserving the position of every strand relative
to the leading red of its block. The permutation of a filtration diagram is
then recomputed with this new bottom. This module supplies that positional
change on the set of indices selected in §5.4.
-/

namespace Categorification.Stendhal.BraidFiltrationIndex

open scoped BigOperators

variable {ℓ : ℕ}

/-- The number of strand positions after attaching one leading red to each
block of black strands. -/
abbrev size (n : Fin ℓ → ℕ) := ∑ b, (n b + 1)

/-- The global strand position for a block and its internal position. Offset
zero is the leading red. -/
def blockPosition (n : Fin ℓ → ℕ) (b : Fin ℓ) (i : Fin (n b + 1)) : Fin (size n) :=
  finSigmaFinEquiv ⟨b, i⟩

/-- Reordering the blocks preserves the total number of strands. -/
theorem size_reindex (n : Fin ℓ → ℕ) (σ : Equiv.Perm (Fin ℓ)) :
    size (n ∘ σ.symm) = size n :=
  Equiv.sum_comp σ.symm (fun b => n b + 1)

/-- Reorder all strand positions with their leading reds. Here `σ b` is the
new location of the block that was at `b`. -/
def blockReorder (n : Fin ℓ → ℕ) (σ : Equiv.Perm (Fin ℓ)) :
    Equiv.Perm (Fin (size n)) :=
  finSigmaFinEquiv.symm.trans
    ((Equiv.sigmaCongr (β₁ := fun b => Fin (n b + 1))
      (β₂ := fun b => Fin ((n ∘ σ.symm) b + 1)) σ (fun b => finCongr (by simp))).trans
      (finSigmaFinEquiv.trans (finCongr (size_reindex n σ))))

/-- Under block reordering every internal offset is carried unchanged to the
new block. In particular this holds for the red at offset zero and for every
black strand after it. -/
theorem blockReorder_blockPosition (n : Fin ℓ → ℕ) (σ : Equiv.Perm (Fin ℓ))
    (b : Fin ℓ) (i : Fin (n b + 1)) :
    blockReorder n σ (blockPosition n b i) =
      finCongr (size_reindex n σ)
        (blockPosition (n ∘ σ.symm) (σ b) (Fin.cast (by simp) i)) := by
  simp only [blockReorder, blockPosition, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- Starting with the bottom-to-top diagram permutation, change its bottom
coordinates by the given reordering of the red blocks. -/
def reorderBottom (n : Fin ℓ → ℕ) (σ : Equiv.Perm (Fin ℓ))
    (φ : Equiv.Perm (Fin (size n))) : Equiv.Perm (Fin (size n)) :=
  φ * (blockReorder n σ)⁻¹

/-- The strand at a given offset of the reordered bottom block retains its
original top endpoint. This is the positional composition in the proof of
Webster's Lemma 6.11. -/
theorem reorderBottom_blockPosition (n : Fin ℓ → ℕ) (σ : Equiv.Perm (Fin ℓ))
    (φ : Equiv.Perm (Fin (size n))) (b : Fin ℓ) (i : Fin (n b + 1)) :
    reorderBottom n σ φ
        (finCongr (size_reindex n σ)
          (blockPosition (n ∘ σ.symm) (σ b) (Fin.cast (by simp) i))) =
      φ (blockPosition n b i) := by
  rw [← blockReorder_blockPosition, reorderBottom, Equiv.Perm.mul_apply,
    Equiv.Perm.inv_def, Equiv.symm_apply_apply]

/-- The index of the block containing the strand position. -/
def blockOf (n : Fin ℓ → ℕ) (a : Fin (size n)) : Fin ℓ :=
  (finSigmaFinEquiv.symm a : Σ b : Fin ℓ, Fin (n b + 1)).1

/-- The bottom parabolic subgroup permutes black strands within each block
and fixes every leading red. -/
def bottomBlockPermutations (n : Fin ℓ → ℕ) : Subgroup (Equiv.Perm (Fin (size n))) where
  carrier := {u | (∀ a, blockOf n (u a) = blockOf n a) ∧
    (∀ b, u (blockPosition n b 0) = blockPosition n b 0)}
  one_mem' := ⟨fun _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro u v ⟨hu, hur⟩ ⟨hv, hvr⟩
    exact ⟨fun a => (hu (v a)).trans (hv a), fun b => by
      rw [Equiv.Perm.mul_apply, hvr, hur]⟩
  inv_mem' := by
    rintro u ⟨hu, hur⟩
    constructor
    · intro a
      simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using
        (hu (u.symm a)).symm
    · intro b
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
      exact (hur b).symm

/-- The source indices of Webster's Proposition 5.20 for fixed top and bottom
block sizes. Reds preserve their order. Read from top to bottom, a black strand
can only move to a block weakly to its left. The permutation has minimal
length among representatives obtained by varying the bottom black order
inside its blocks. -/
def sourceIndices (top bottom : Fin ℓ → ℕ) (h : size top = size bottom) :
    Set (Equiv.Perm (Fin (size bottom))) :=
  {φ |
    (∀ b, φ (blockPosition bottom b 0) = finCongr h (blockPosition top b 0)) ∧
    (∀ b (i : Fin (bottom b + 1)), 0 < i.val →
      b ≤ blockOf top (finCongr h.symm (φ (blockPosition bottom b i)))) ∧
    (∀ u ∈ bottomBlockPermutations bottom,
      TypeA.length (size bottom) φ ≤ TypeA.length (size bottom) (φ * u))}

/-- The contribution of this bottom block-size profile to the selected braid
filtration indices. The red permutation acts by moving whole bottom blocks. -/
def braidedIndices (top bottom : Fin ℓ → ℕ) (h : size top = size bottom)
    (σ : Equiv.Perm (Fin ℓ)) : Set (Equiv.Perm (Fin (size bottom))) :=
  reorderBottom bottom σ '' sourceIndices top bottom h

/-- Undoing the bottom block reorder identifies a braid filtration index
with its original index. This is a bijection for the fixed block sizes. -/
theorem mem_braidedIndices_iff (top bottom : Fin ℓ → ℕ) (h : size top = size bottom)
    (σ : Equiv.Perm (Fin ℓ)) (φ : Equiv.Perm (Fin (size bottom))) :
    φ ∈ braidedIndices top bottom h σ ↔
      φ * blockReorder bottom σ ∈ sourceIndices top bottom h := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa only [reorderBottom, mul_assoc, inv_mul_cancel, mul_one] using hu
  · intro hφ
    refine ⟨φ * blockReorder bottom σ, hφ, ?_⟩
    simp [reorderBottom, mul_assoc]

/-- The original identity diagram is selected when the top and bottom
block sizes coincide. -/
theorem one_mem_sourceIndices (n : Fin ℓ → ℕ) :
    (1 : Equiv.Perm (Fin (size n))) ∈ sourceIndices n n rfl := by
  refine ⟨fun _ => rfl, ?_, fun _ _ => ?_⟩
  · intro b i _
    change b ≤ (finSigmaFinEquiv.symm (blockPosition n b i) : Σ a : Fin ℓ, Fin (n a + 1)).1
    unfold blockPosition
    rw [Equiv.symm_apply_apply]
  · rw [TypeA.length_one]
    exact Nat.zero_le _

/-- A selected braid diagram joins each reordered bottom red to the same top
red as the original index. The label is read from the original block number. -/
theorem braidedIndex_red (top bottom : Fin ℓ → ℕ) (h : size top = size bottom)
    (σ : Equiv.Perm (Fin ℓ)) {φ : Equiv.Perm (Fin (size bottom))}
    (hφ : φ ∈ braidedIndices top bottom h σ) (b : Fin ℓ) :
    φ (blockReorder bottom σ (blockPosition bottom b 0)) =
      finCongr h (blockPosition top b 0) := by
  obtain ⟨u, hu, rfl⟩ := hφ
  change (u * (blockReorder bottom σ)⁻¹)
    (blockReorder bottom σ (blockPosition bottom b 0)) = _
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  exact hu.1 b

/-- The leftward condition is measured in the original block order. After
reordering, the strand in the block at `σ b` still joins its original top block. -/
theorem braidedIndex_black_le (top bottom : Fin ℓ → ℕ) (h : size top = size bottom)
    (σ : Equiv.Perm (Fin ℓ)) {φ : Equiv.Perm (Fin (size bottom))}
    (hφ : φ ∈ braidedIndices top bottom h σ) (b : Fin ℓ) (i : Fin (bottom b + 1))
    (hi : 0 < i.val) :
    b ≤ blockOf top
      (finCongr h.symm (φ (blockReorder bottom σ (blockPosition bottom b i)))) := by
  obtain ⟨u, hu, rfl⟩ := hφ
  change b ≤ blockOf top
    (finCongr h.symm ((u * (blockReorder bottom σ)⁻¹) (blockReorder bottom σ (blockPosition bottom b i))))
  rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  exact hu.2.1 b i hi

/-- The full set of selected braid indices for a fixed top shape. Allow the
bottom block sizes to vary subject to the total number of strands. -/
def braidIndices (top : Fin ℓ → ℕ) (σ : Equiv.Perm (Fin ℓ)) :
    Set (Equiv.Perm (Fin (size top))) :=
  {φ | ∃ (bottom : Fin ℓ → ℕ) (h : size top = size bottom),
    (finCongr h).symm.trans (φ.trans (finCongr h)) ∈ braidedIndices top bottom h σ}

/-- The identity source index yields a selected braid index by reordering
its entire bottom blocks. -/
theorem reorderBottom_one_mem_braidIndices (top : Fin ℓ → ℕ) (σ : Equiv.Perm (Fin ℓ)) :
    reorderBottom top σ 1 ∈ braidIndices top σ := by
  refine ⟨top, rfl, ?_⟩
  change reorderBottom top σ 1 ∈ braidedIndices top top rfl σ
  exact ⟨1, one_mem_sourceIndices top, rfl⟩

end Categorification.Stendhal.BraidFiltrationIndex
