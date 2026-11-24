/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.ExitsInterval
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationSpan
import Categorification.WeightedKLR.RedStrands.StandardModule

/-!
# Root functions for standardization outside an adjacent red pair

Webster, arXiv:1309.3796v2, §5.1 after Definition 5.4 and §6.1, Lemma 6.8. In the
partition `λ(j)` the two red labels `a,b` form one block. Count black strands before each
singleton and before the *first* strand of the pair; there is no cut inside the pair. Index
these counts by red label, repeating the same coordinate on the two labels of the pair so
that the indices do not change when the pair crosses.

Every reduced diagram exchanging these red labels has a reduced factor which performs the
red crossing and does not decrease any block count (`exists_adjacentBlock_frame`). The factor
fixes every strand outside the interval of the pair. In particular black strands already
left of that block stay left of it, even when its two red strands are not adjacent positions.
-/

namespace Categorification.Stendhal

open KLR TypeA Equiv BraidedStendhalAlgebra

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- The black `i`-strands before every red strand of the block `C`. -/
def blockBlackCount (s : Seq μ) (C : Finset (Fin ℓ)) (i : I) : ℕ :=
  (Finset.univ.filter fun x => s.lbl x = .inl i ∧
    ∀ y r, r ∈ C → s.lbl y = .inr r → x < y).card

theorem blockBlackCount_singleton (s : Seq μ) (r : Fin ℓ) (i : I) :
    blockBlackCount s {r} i = blackCount s r i := by simp [blockBlackCount, blackCount]

/-- The root function for singleton blocks except for the adjacent block `a,b` (Webster,
§6.1, Lemma 6.8). Both labels of this block index its one boundary. -/
def adjacentBlockRoot (a b : Fin ℓ) (s : Seq μ) (r : Fin ℓ) : I → ℕ :=
  blockBlackCount s (if r = a ∨ r = b then {a,b} else {r})

theorem adjacentBlockRoot_swap (a b : Fin ℓ) (s : Seq μ) :
    adjacentBlockRoot a b s = adjacentBlockRoot b a s := by
  funext r
  simp only [adjacentBlockRoot, or_comm (a := r = a), Finset.pair_comm a b]

theorem adjacentBlockRoot_pair {a b : Fin ℓ} {s : Seq μ} {L M : List (Fin ℓ)}
    (hs : redWord s = L ++ a :: b :: M) : adjacentBlockRoot a b s b = blackCount s a := by
  obtain ⟨p, hp⟩ := exists_lbl_eq_inr s a
  funext i
  simp only [adjacentBlockRoot, or_true, ↓reduceIte, blockBlackCount, blackCount]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  refine and_congr_right fun _ => ⟨fun h y hy => h y a (.inl rfl) hy, ?_⟩
  rintro h y r (rfl | rfl) hy
  · exact h _ hy
  · exact (h p hp).trans (lt_of_redWord_eq_append hs hp hy)

private theorem blockBlackCount_le_smul (s : Seq μ) (C : Finset (Fin ℓ)) (v : Perm (Fin m))
    (h : ∀ x, (∀ y r, r ∈ C → s.lbl y = .inr r → x < y) →
      ∀ y r, r ∈ C → s.lbl y = .inr r → v x < v y) (i : I) :
    blockBlackCount s C i ≤ blockBlackCount (v • s) C i := by
  unfold blockBlackCount
  refine Finset.card_le_card_of_injOn v ?_ v.injective.injOn
  intro x hx
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  refine ⟨by simpa [lbl_smul] using hx.1, fun y r hr hy => ?_⟩
  simpa using h x hx.2 (v⁻¹ y) r hr (by simpa [lbl_smul] using hy)

private theorem perm_lt_exterior {n : ℕ} {q p : Fin n} {v : Perm (Fin n)}
    (hf : ∀ t, t < q ∨ p < t → v t = t) {x y : Fin n}
    (hxy : x < y) (hy : y < q ∨ p < y) : v x < v y := by
  rw [hf _ hy]
  by_cases hx : x < q ∨ p < x
  · rwa [hf _ hx]
  · have hxc : x ∈ Set.Icc q p :=
      ⟨not_lt.mp (fun h => hx (.inl h)), not_lt.mp (fun h => hx (.inr h))⟩
    have hv := mem_Icc_of_perm_fix_outside hf hxc
    rcases hy with hy | hy
    · exact (not_lt.mpr hxc.1 (hxy.trans hy)).elim
    · exact hv.2.trans_lt hy

/-- The interval-supported crossing preserves or raises the block root function. -/
theorem adjacentBlockRoot_le_of_fix {a b : Fin ℓ} {L M : List (Fin ℓ)} {s : Seq μ}
    (hs : redWord s = L ++ a :: b :: M) {q p : Fin m}
    (hq : s.lbl q = .inr a) (hp : s.lbl p = .inr b) {v : Perm (Fin m)}
    (hf : ∀ t, t < q ∨ p < t → v t = t) :
    adjacentBlockRoot a b s ≤ adjacentBlockRoot a b (v • s) := by
  have hqp := lt_of_redWord_eq_append hs hq hp
  intro r i
  unfold adjacentBlockRoot
  split_ifs with hr
  · refine blockBlackCount_le_smul _ _ _ (fun x hx y z hz hy => ?_) _
    have hxq : x < q := hx _ a (by simp) hq
    rw [hf _ (.inl hxq)]
    have hyc : y ∈ Set.Icc q p := by
      rcases Finset.mem_insert.1 hz with rfl | hz
      · rw [lbl_inj_of_inr s _ hy hq]; exact ⟨le_rfl, hqp.le⟩
      · obtain rfl := Finset.mem_singleton.1 hz
        rw [lbl_inj_of_inr s _ hy hp]; exact ⟨hqp.le, le_rfl⟩
    exact hxq.trans_le (mem_Icc_of_perm_fix_outside hf hyc).1
  · refine blockBlackCount_le_smul _ _ _ (fun x hx y z hz hy => ?_) _
    obtain rfl := Finset.mem_singleton.1 hz
    apply perm_lt_exterior hf (hx _ _ (by simp) hy)
    by_contra! hc
    have hqy : q ≠ y := fun he => hr (.inl (Sum.inr_injective (hy.symm.trans (he ▸ hq))))
    have hyp : y ≠ p := fun he => hr (.inr (Sum.inr_injective (hy.symm.trans (he ▸ hp))))
    exact not_lt_of_redWord_eq_append hs hq hp (by simp [hy])
      (lt_of_le_of_ne hc.1 hqy) (lt_of_le_of_ne hc.2 hyp)

/-- **Block cuts across an adjacent red crossing** (Webster, arXiv:1309.3796v2, proof of
Lemma 6.8). In every diagram exchanging `a,b`, there is a reduced factor through the new
red order with block counts at least those of the bottom loading. -/
theorem exists_adjacentBlock_frame {a b : Fin ℓ} {L M : List (Fin ℓ)} {s : Seq μ}
    {τ : Perm (Fin m)} (hs : redWord s = L ++ a :: b :: M)
    (hτ : redWord (τ • s) = L ++ b :: a :: M) :
    ∃ v : Perm (Fin m), invSet m v ⊆ invSet m τ ∧ redWord (v • s) = L ++ b :: a :: M ∧
      adjacentBlockRoot a b s ≤ adjacentBlockRoot a b (v • s) := by
  obtain ⟨q, hq⟩ := exists_lbl_eq_inr s a
  obtain ⟨p, hp⟩ := exists_lbl_eq_inr s b
  have hqp := lt_of_redWord_eq_append hs hq hp
  obtain ⟨v, hv, hfix⟩ := exists_isSwapBelow_interval (R := redSet s) hqp
    (mem_invSet_of_sublist_redWord (by rw [hτ]; simp) hqp hq hp)
    (fun t ht => not_lt_of_redWord_eq_append hs hq hp (by simpa [redSet] using ht))
  exact ⟨v, hv.le, (redWord_smul_eq_swap_iff' hs hq hp _).2 hv.red,
    adjacentBlockRoot_le_of_fix hs hq hp hfix⟩

end Categorification.Stendhal
