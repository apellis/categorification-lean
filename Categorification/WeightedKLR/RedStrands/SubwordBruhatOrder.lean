/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.DoubleCoset

/-!
# The Bruhat order of `S_m` through subwords

The Bruhat order on `S_m` in its subword form: `v ≤ w` when `v` is the product of a subword of
a reduced word of `w`. This is the order used to state straightening in Stendhal algebras in
Bruhat form (B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, the spanning argument of Prop. 4.16, where local relations only delete
crossings).

We define the order with the canonical reduced word `TypeA.canWord`; by Matsumoto's theorem and
the braid invariance of subword products (`TypeA.BraidEquiv.subProds_eq`), any reduced word
gives the same set (`TypeA.mem_subProds_iff_bruhatLE`).

## Main definitions

* `TypeA.BruhatLE m v w`: `v` is the product of a subword of the canonical reduced word of `w`.

## Main results

* `TypeA.mem_subProds_iff_bruhatLE`: for any reduced word `γ`, the subword products of `γ` are
  exactly the elements Bruhat below `wordProd m γ` (subword property).
* `TypeA.exists_isReduced_subProds_subset`: every valid word `γ` has a reduced word `δ` with the
  same product and with `subProds δ ⊆ subProds γ`.
* `TypeA.mem_subProds_of_bruhatLE`: for every valid word `γ` (reduced or not), the subword
  products of `γ` form a lower set for the Bruhat order. So the subword products of a product
  of words are the Bruhat lower set they generate, which is the form in which straightening
  bounds are used.
* `TypeA.BruhatLE.refl`, `TypeA.BruhatLE.trans`, `TypeA.BruhatLE.antisymm`,
  `TypeA.BruhatLE.length_le`, `TypeA.BruhatLE.length_lt_of_ne`: it is a partial order, and
  strictly lower elements are strictly shorter.
-/

namespace Categorification.TypeA

open Equiv

variable {m : ℕ}

/-- The Bruhat order on `S_m`, subword form: `v` is the product of a subword of the canonical
reduced word of `w`. -/
def BruhatLE (m : ℕ) (v w : Perm (Fin m)) : Prop :=
  v ∈ subProds m (canWord m w)

/-- **Subword property.** For a reduced word `γ`, the subword products of `γ` are the elements
Bruhat below `wordProd m γ`. -/
theorem mem_subProds_iff_bruhatLE {γ : List ℕ} (hγ : IsReduced m γ) {v : Perm (Fin m)} :
    v ∈ subProds m γ ↔ BruhatLE m v (wordProd m γ) := by
  have hE : BraidEquiv γ (canWord m (wordProd m γ)) :=
    braidEquiv_of_isReduced hγ (isReduced_canWord m _) (wordProd_canWord m _).symm
  rw [BruhatLE, ← BraidEquiv.subProds_eq hE hγ.1]

theorem BruhatLE.refl (w : Perm (Fin m)) : BruhatLE m w w := by
  have := wordProd_mem_subProds (m := m) (canWord m w)
  rwa [wordProd_canWord] at this

/-- Deleting a repeated letter `a a` from a valid word keeps its product. -/
private theorem wordProd_delete_repeat (α β : List ℕ) (a : ℕ) :
    wordProd m (α ++ [a, a] ++ β) = wordProd m (α ++ β) := by
  simp only [wordProd_append]
  simp [wordProd]

/-- Every valid word has a reduced word with the same product whose subword products are among
its own. -/
theorem exists_isReduced_subProds_subset {γ : List ℕ} (hγ : ValidWord m γ) :
    ∃ δ, IsReduced m δ ∧ wordProd m δ = wordProd m γ ∧ subProds m δ ⊆ subProds m γ := by
  induction hn : γ.length using Nat.strong_induction_on generalizing γ with
  | _ n ih =>
  by_cases hred : IsReduced m γ
  · exact ⟨γ, hred, rfl, subset_rfl⟩
  obtain ⟨τ, hE, α, β, a, rfl⟩ := exists_braidEquiv_hasRepeat_of_not_isReduced hγ hred
  have hvτ : ValidWord m (α ++ [a, a] ++ β) := (BraidEquiv.validWord_iff hE).1 hγ
  have hsl : (α ++ β).Sublist (α ++ [a, a] ++ β) := by
    rw [List.append_assoc]
    exact (List.sublist_append_right _ _).append_left α
  have hlt : (α ++ β).length < n := by
    rw [← hn, BraidEquiv.length_eq hE]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  obtain ⟨δ, hδ, hp, hs⟩ := ih _ hlt (hvτ.sublist hsl) rfl
  refine ⟨δ, hδ, ?_, ?_⟩
  · rw [hp, ← wordProd_delete_repeat, ← BraidEquiv.wordProd_eq hE hγ]
  · rw [BraidEquiv.subProds_eq hE hγ]
    exact hs.trans (subProds_mono hsl)

/-- **Subword products form a Bruhat lower set**, for every valid word `γ`. -/
theorem mem_subProds_of_bruhatLE {γ : List ℕ} (hγ : ValidWord m γ) {u v : Perm (Fin m)}
    (hv : v ∈ subProds m γ) (huv : BruhatLE m u v) : u ∈ subProds m γ := by
  obtain ⟨ε, hε, rfl⟩ := hv
  obtain ⟨δ, hδ, hp, hs⟩ := exists_isReduced_subProds_subset (hγ.sublist hε)
  rw [← hp, ← mem_subProds_iff_bruhatLE hδ] at huv
  exact subProds_mono hε (hs huv)

theorem BruhatLE.trans {u v w : Perm (Fin m)} (huv : BruhatLE m u v) (hvw : BruhatLE m v w) :
    BruhatLE m u w :=
  mem_subProds_of_bruhatLE (isReduced_canWord m w).1 hvw huv

theorem BruhatLE.length_le {v w : Perm (Fin m)} (h : BruhatLE m v w) :
    length m v ≤ length m w := by
  obtain ⟨δ, hδ, rfl⟩ := h
  have h1 := length_wordProd_le ((isReduced_canWord m w).1.sublist hδ)
  have h2 := hδ.length_le
  have h3 := (isReduced_canWord m w).2
  rw [wordProd_canWord] at h3
  omega

/-- An element strictly Bruhat below `w` is strictly shorter than `w`. -/
theorem BruhatLE.length_lt_of_ne {v w : Perm (Fin m)} (h : BruhatLE m v w) (hne : v ≠ w) :
    length m v < length m w := by
  refine lt_of_le_of_ne h.length_le fun hl => hne ?_
  obtain ⟨δ, hδ, rfl⟩ := h
  have h1 := length_wordProd_le ((isReduced_canWord m w).1.sublist hδ)
  have h2 := hδ.length_le
  have h3 := (isReduced_canWord m w).2
  rw [wordProd_canWord] at h3
  have hlen : δ.length = (canWord m w).length := by omega
  rw [hδ.eq_of_length hlen, wordProd_canWord]

theorem BruhatLE.antisymm {v w : Perm (Fin m)} (hvw : BruhatLE m v w) (hwv : BruhatLE m w v) :
    v = w := by
  by_contra hne
  exact absurd (hwv.length_le) (not_le.2 (hvw.length_lt_of_ne hne))

end Categorification.TypeA
