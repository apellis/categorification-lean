/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.Parabolic

/-!
# Shuffles for three blocks as iterated shuffles

Webster, arXiv:1309.3796v3, §5.1, the partial standardizations after Definition 5.4, used in
§7.3, proof of Lemma 7.19: the standard basis of a partial standardization with three blocks
is indexed by pairs of a shuffle `u_out` of the blocks `(A, MR)` and a shuffle `u_in` of the
blocks `(M, R)` (`Stendhal.mem_blocksShuffleCoords_iff`). Here these pairs are identified with
the shuffles of three blocks: `(u_out, u_in) ↦ (1 × u_in) u_out` is a bijection onto the
permutations `w` with `w⁻¹` increasing on each of the three blocks (`shuffleThreeEquiv`), and
lengths add (`length_blockPerm_one_mul`). This is the parabolic factorization of shuffles
(cf. `TypeA.parabolicEquiv`).

## Main definitions

* `TypeA.IsShuffleThree`, `TypeA.shuffleThreeEquiv`.

## Main results

* `TypeA.isShuffleThree_blockPerm_one_mul`, `TypeA.length_blockPerm_one_mul`,
  `TypeA.shuffleThreeEquiv_apply`.
-/

namespace Categorification.TypeA

open Equiv

variable {n₁ n₂ n₃ n' m : ℕ} (h : n₁ + n' = m) (h' : n₂ + n₃ = n')

/-- `w` is a *shuffle of three blocks* `n₁, n₂, n₃`: `w⁻¹` is increasing on each block. -/
def IsShuffleThree (w : Perm (Fin m)) : Prop :=
  StrictMono (fun x : Fin n₁ => w⁻¹ (blockEquiv h (Sum.inl x))) ∧
    StrictMono (fun y : Fin n₂ => w⁻¹ (blockEquiv h (Sum.inr (blockEquiv h' (Sum.inl y))))) ∧
      StrictMono (fun z : Fin n₃ => w⁻¹ (blockEquiv h (Sum.inr (blockEquiv h' (Sum.inr z)))))

variable {h h'}

theorem inv_blockPerm_one_mul_inl (u : Perm (Fin m)) (v : Perm (Fin n')) (x : Fin n₁) :
    (blockPerm h 1 v * u)⁻¹ (blockEquiv h (Sum.inl x)) = u⁻¹ (blockEquiv h (Sum.inl x)) := by
  rw [mul_inv_rev, blockPerm_inv, Perm.mul_apply, blockPerm_inl, inv_one, Perm.one_apply]

theorem inv_blockPerm_one_mul_inr (u : Perm (Fin m)) (v : Perm (Fin n')) (y : Fin n') :
    (blockPerm h (1 : Perm (Fin n₁)) v * u)⁻¹ (blockEquiv h (Sum.inr y)) =
      u⁻¹ (blockEquiv h (Sum.inr (v⁻¹ y))) := by
  rw [mul_inv_rev, blockPerm_inv, Perm.mul_apply, blockPerm_inr]

/-- `(1 × u_in) u_out` is a shuffle of the three blocks. -/
theorem isShuffleThree_blockPerm_one_mul {u : Perm (Fin m)} {v : Perm (Fin n')}
    (hu : IsShuffle h u) (hv : IsShuffle h' v) :
    IsShuffleThree h h' (blockPerm h (1 : Perm (Fin n₁)) v * u) := by
  refine ⟨fun x x' hx => ?_, fun y y' hy => ?_, fun z z' hz => ?_⟩
  · simp only [inv_blockPerm_one_mul_inl]
    exact hu.1 hx
  · simp only [inv_blockPerm_one_mul_inr]
    exact hu.2 (hv.1 hy)
  · simp only [inv_blockPerm_one_mul_inr]
    exact hu.2 (hv.2 hz)

omit h' in
/-- **Lengths add**: `ℓ((1 × u_in) u_out) = ℓ(u_in) + ℓ(u_out)`. -/
theorem length_blockPerm_one_mul {u : Perm (Fin m)} (hu : IsShuffle h u) (v : Perm (Fin n')) :
    length m (blockPerm h (1 : Perm (Fin n₁)) v * u) = length n' v + length m u := by
  rw [length_blockPerm_mul h _ _ hu, length_one, zero_add]

private theorem eq_one_of_strictMono' {k : ℕ} {c : Perm (Fin k)} (hc : StrictMono c) : c = 1 := by
  have := Subsingleton.elim (hc.orderIsoOfSurjective c c.surjective) (OrderIso.refl _)
  ext x
  exact congrArg Fin.val (congrArg (fun φ : Fin k ≃o Fin k => φ x) this)

private theorem strictMono_of_comp {k k' : ℕ} {g : Fin k → Fin k'} (hg : StrictMono g)
    {c : Perm (Fin k)} (hgc : StrictMono (g ∘ c)) : StrictMono c :=
  fun _ _ hxy => hg.lt_iff_lt.1 (hgc hxy)

/-- Every shuffle of three blocks is `(1 × u_in) u_out`. -/
theorem exists_blockPerm_one_mul {w : Perm (Fin m)} (hw : IsShuffleThree h h' w) :
    ∃ (u : Perm (Fin m)) (v : Perm (Fin n')), IsShuffle h u ∧ IsShuffle h' v ∧
      blockPerm h (1 : Perm (Fin n₁)) v * u = w := by
  obtain ⟨a, b, u, hu, rfl⟩ := exists_blockPerm_mul h w
  obtain ⟨c, d, v, hv, rfl⟩ := exists_blockPerm_mul h' b
  have hinv : ∀ p, (blockPerm h a (blockPerm h' c d * v) * u)⁻¹ p =
      u⁻¹ (blockPerm h a⁻¹ (v⁻¹ * blockPerm h' c⁻¹ d⁻¹) p) := fun p => by
    rw [mul_inv_rev, blockPerm_inv, mul_inv_rev, blockPerm_inv, Perm.mul_apply]
  have ha : a = 1 := by
    have h1 : StrictMono (⇑(a⁻¹ : Perm (Fin n₁))) := strictMono_of_comp hu.1 (fun x x' hx => by
      have := hw.1 hx
      simpa only [Function.comp_apply, hinv, blockPerm_inl] using this)
    have := eq_one_of_strictMono' h1
    rwa [inv_eq_one] at this
  have hc : c = 1 := by
    have h1 : StrictMono (⇑(c⁻¹ : Perm (Fin n₂))) :=
        strictMono_of_comp (hu.2.comp hv.1) (fun y y' hy => by
      have := hw.2.1 hy
      simpa only [Function.comp_apply, hinv, blockPerm_inr, Perm.mul_apply, blockPerm_inl]
        using this)
    have := eq_one_of_strictMono' h1
    rwa [inv_eq_one] at this
  have hd : d = 1 := by
    have h1 : StrictMono (⇑(d⁻¹ : Perm (Fin n₃))) :=
        strictMono_of_comp (hu.2.comp hv.2) (fun z z' hz => by
      have := hw.2.2 hz
      simpa only [Function.comp_apply, hinv, blockPerm_inr, Perm.mul_apply] using this)
    have := eq_one_of_strictMono' h1
    rwa [inv_eq_one] at this
  subst ha hc hd
  exact ⟨u, v, hu, hv, by rw [blockPerm_one, one_mul]⟩

variable (h h') in
/-- **Shuffles of three blocks are iterated shuffles**: `(u_out, u_in) ↦ (1 × u_in) u_out`. -/
noncomputable def shuffleThreeEquiv :
    Shuffle h × Shuffle h' ≃ {w : Perm (Fin m) // IsShuffleThree h h' w} :=
  Equiv.ofBijective
    (fun p => ⟨blockPerm h (1 : Perm (Fin n₁)) p.2.1 * p.1.1,
      isShuffleThree_blockPerm_one_mul p.1.2 p.2.2⟩)
    ⟨fun p q he => by
      obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := p
      obtain ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ := q
      obtain ⟨-, rfl, rfl⟩ := blockPerm_mul_injective h hu hu' (congrArg Subtype.val he)
      rfl,
     fun w => by
      obtain ⟨u, v, hu, hv, he⟩ := exists_blockPerm_one_mul w.2
      exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), Subtype.ext he⟩⟩

@[simp] theorem shuffleThreeEquiv_apply (p : Shuffle h × Shuffle h') :
    (shuffleThreeEquiv h h' p : Perm (Fin m)) = blockPerm h (1 : Perm (Fin n₁)) p.2.1 * p.1.1 :=
  rfl

end Categorification.TypeA
