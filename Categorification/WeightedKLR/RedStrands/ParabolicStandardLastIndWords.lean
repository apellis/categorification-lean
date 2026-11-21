/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndLayer
import Categorification.KLR.IndFirstSlideQuad

/-!
# Reduced words through the crossing `ψ_d` of the first slide

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. In the decomposition `R(ν₀ + ν' + i) 1_{ν₀+ν',i} ≅ ⊕_u R ⊗ R`
(Khovanov–Lauda I, arXiv:0803.4121v2, Proposition 2.16), the shuffles `u` that move the new
strand `i` to a position at most `|ν₀|` factor as `u⁻¹ = (a × 1) d⁻¹`, where `d` is the
crossing of the first-factor Mackey datum. Choosing reduced words adapted to the parabolic
factorisation `S_{|ν₀|+1} × S_{|ν'|}`, the basis vector `ŵ_u^*` of such a shuffle is
`ψ_a ψ_d^* 1_{ν₀+ν',i}`, which is the shape needed to slide it through
`G = 1_{ν₀+i,ν'} ψ_d^* 1_{ν₀+ν',i}`.

## Main results

* `TypeA.parabolicWord`: reduced words adapted to a parabolic factorisation.
* `KLRAlgebra.firstSlideWord`: the corresponding reduced words for the shuffles of `(ν₀+ν', i)`.
* `KLRAlgebra.exists_hatWRevOf_firstSlideWord`: `ŵ_u^* = ψ_a ψ_d^* 1_{ν₀+ν',i}` when the new
  strand of `u` ends at most at position `|ν₀|`.
-/

noncomputable section

namespace Categorification.TypeA

open Equiv

variable {n n' m : ℕ} (h : n + n' = m)

/-- A permutation fixing the second block pointwise acts through the first block. -/
theorem exists_blockPerm_one_eq {w : Perm (Fin m)}
    (hw : ∀ y : Fin n', w (blockEquiv h (Sum.inr y)) = blockEquiv h (Sum.inr y)) :
    ∃ a : Perm (Fin n), blockPerm h a 1 = w := by
  have hlt : ∀ x : Fin n, (w (blockEquiv h (Sum.inl x))).val < n := by
    intro x
    by_contra hge
    have hy : (w (blockEquiv h (Sum.inl x))).val - n < n' := by
      have := (w (blockEquiv h (Sum.inl x))).2; omega
    have he : w (blockEquiv h (Sum.inl x)) = w (blockEquiv h (Sum.inr ⟨_, hy⟩)) := by
      rw [hw]; apply Fin.ext; simp only [blockEquiv_inr_val]; omega
    exact Sum.inl_ne_inr ((blockEquiv h).injective (w.injective he))
  let f : Fin n → Fin n := fun x => ⟨(w (blockEquiv h (Sum.inl x))).val, hlt x⟩
  have hf : Function.Injective f := fun x y he => by
    have he' : w (blockEquiv h (Sum.inl x)) = w (blockEquiv h (Sum.inl y)) :=
      Fin.ext (congrArg Fin.val he :)
    exact Sum.inl_injective ((blockEquiv h).injective (w.injective he'))
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), Equiv.ext fun p => ?_⟩
  obtain ⟨q, rfl⟩ := (blockEquiv h).surjective p
  rcases q with x | y
  · rw [blockPerm_inl]; exact Fin.ext rfl
  · rw [blockPerm_inr, hw]; rfl

/-- A strictly monotone map of `Fin` types grows at least by the distance of its arguments. -/
theorem strictMono_val_add_le {p q : ℕ} {f : Fin p → Fin q} (hf : StrictMono f) {x y : Fin p}
    (hxy : y.val ≤ x.val) : (f y).val + (x.val - y.val) ≤ (f x).val := by
  obtain ⟨k, hk⟩ : ∃ k, x.val = y.val + k := ⟨x.val - y.val, by omega⟩
  induction k generalizing x with
  | zero =>
    have : x = y := Fin.ext (by omega)
    subst this; omega
  | succ k ih =>
    have hx' : y.val + k < p := by have := x.2; omega
    have h1 := ih (x := ⟨y.val + k, hx'⟩) (by simp) rfl
    have hlt : f ⟨y.val + k, hx'⟩ < f x := hf (Fin.lt_def.2 (by simp only; omega))
    rw [Fin.lt_def] at hlt
    simp only at h1
    omega

/-- For a shuffle of one strand into a block of `n`, the positions of the first block at or
after the new strand move up by one. -/
theorem shuffle_inl_val_of_le (hn' : n' = 1) (u : Shuffle h) (z : Fin n') (x : Fin n)
    (hx : (u.1⁻¹ (blockEquiv h (Sum.inr z))).val ≤ x.val) :
    (u.1⁻¹ (blockEquiv h (Sum.inl x))).val = x.val + 1 := by
  subst hn'
  have hf : StrictMono fun x : Fin n => u.1⁻¹ (blockEquiv h (Sum.inl x)) := u.2.1
  have hup := shuffle_inl_le h u x
  have hlow := strictMono_val_add_le hf (x := x) (y := ⟨0, by have := x.2; omega⟩)
    (by simp)
  simp only [Nat.sub_zero] at hlow
  by_contra hne
  have hr : (u.1⁻¹ (blockEquiv h (Sum.inr z))).val < n := lt_of_le_of_lt hx x.2
  have h1 := strictMono_val_add_le hf (x := x) (y := ⟨_, hr⟩) hx
  have h2 := strictMono_val_add_le hf (x := ⟨_, hr⟩) (y := ⟨0, by omega⟩) (by simp)
  simp only [Nat.sub_zero] at h1 h2
  have hfr : u.1⁻¹ (blockEquiv h (Sum.inl ⟨_, hr⟩)) = u.1⁻¹ (blockEquiv h (Sum.inr z)) :=
    Fin.ext (by omega)
  exact Sum.inl_ne_inr ((blockEquiv h).injective (u.1⁻¹.injective hfr))

/-- Reduced words adapted to the parabolic factorisation `w = (a × b) u`: a reduced word for
`a`, then one for `b` shifted to the second block, then one for the shuffle `u`. -/
def parabolicWord (w : Perm (Fin m)) : List ℕ :=
  canWord n ((parabolicEquiv h).symm w).1 ++
    shiftWord n (canWord n' ((parabolicEquiv h).symm w).2.1) ++
      (canWord m ((parabolicEquiv h).symm w).2.2.1⁻¹).reverse

theorem parabolicWord_spec (w : Perm (Fin m)) :
    IsReduced m (parabolicWord h w) ∧ wordProd m (parabolicWord h w) = w := by
  set p := (parabolicEquiv h).symm w with hp
  have hσ : IsReduced m (canWord m p.2.2.1⁻¹).reverse :=
    ⟨validWord_reverse.2 (isReduced_canWord _ _).1, by
      rw [List.length_reverse, wordProd_reverse, length_inv]; exact (isReduced_canWord _ _).2⟩
  have hu : IsShuffle h (wordProd m (canWord m p.2.2.1⁻¹).reverse) := by
    rw [wordProd_reverse, wordProd_canWord, inv_inv]; exact p.2.2.2
  obtain ⟨hr, hw⟩ := IsReduced.parabolic h (isReduced_canWord n p.1)
    (isReduced_canWord n' p.2.1) hσ hu
  refine ⟨hr, ?_⟩
  rw [parabolicWord, ← hp, hw, wordProd_canWord, wordProd_canWord, wordProd_reverse,
    wordProd_canWord, inv_inv]
  change parabolicEquiv h p = w
  rw [hp, Equiv.apply_symm_apply]

/-- The adapted word of `(a × 1) u`. -/
theorem parabolicWord_of_eq {w : Perm (Fin m)} {a : Perm (Fin n)} {u : Perm (Fin m)}
    (hu : IsShuffle h u) (hw : blockPerm h a 1 * u = w) :
    parabolicWord h w = canWord n a ++ (canWord m u⁻¹).reverse := by
  have hp : (parabolicEquiv h).symm w = (a, 1, ⟨u, hu⟩) :=
    (Equiv.symm_apply_eq _).2 hw.symm
  have h1 : canWord n' (1 : Perm (Fin n')) = [] :=
    List.eq_nil_of_length_eq_zero ((length_canWord _ _).trans (length_one _))
  rw [parabolicWord, hp]
  simp only [h1, shiftWord, List.map_nil, List.append_nil]

end Categorification.TypeA

namespace Categorification.KLR

open Equiv TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

local notation "Si" i:max => (Singleton.singleton i : Multiset I)

namespace KLRAlgebra

variable (ν₀ ν' : Multiset I) (i : I)

omit [DecidableEq I] in
/-- The blocks `(|ν₀| + 1, |ν'|)` of the bottom of the first-factor Mackey datum. -/
theorem firstBlock_h :
    (Multiset.card ν₀ + 1) + Multiset.card ν' = Multiset.card (ν₀ + ν' + Si i) := by
  simp only [Multiset.card_add, Multiset.card_singleton]; omega

/-- Reduced words for the shuffles of `(ν₀ + ν', i)`, adapted to the factorisation of `u⁻¹`
with respect to the blocks `(|ν₀| + 1, |ν'|)`. -/
def firstSlideWord (u : Shuffle (Seq.card_add' (ν₀ + ν') (Si i))) : List ℕ :=
  (parabolicWord (firstBlock_h ν₀ ν' i) u.1⁻¹).reverse

omit [DecidableEq I] in
theorem firstSlideWord_spec (u : Shuffle (Seq.card_add' (ν₀ + ν') (Si i))) :
    IsReduced (Multiset.card (ν₀ + ν' + Si i)) (firstSlideWord ν₀ ν' i u) ∧
      wordProd (Multiset.card (ν₀ + ν' + Si i)) (firstSlideWord ν₀ ν' i u) = u.1 := by
  obtain ⟨hr, hw⟩ := parabolicWord_spec (firstBlock_h ν₀ ν' i) u.1⁻¹
  refine ⟨⟨validWord_reverse.2 hr.1, ?_⟩, ?_⟩
  · rw [firstSlideWord, List.length_reverse, wordProd_reverse, length_inv]; exact hr.2
  · rw [firstSlideWord, wordProd_reverse, hw, inv_inv]

variable {ν₀ ν' i}

omit [DecidableEq I] in
/-- `d⁻¹` is a shuffle for the blocks `(|ν₀| + 1, |ν'|)`. -/
theorem isShuffle_inv_quadPerm_firstQuad :
    IsShuffle (firstBlock_h ν₀ ν' i)
      (quadPerm (firstQuad_h ν₀ ν' i) (firstQuad ν₀ ν' i))⁻¹ := by
  refine ⟨fun x x' hxx' => ?_, fun y y' hyy' => ?_⟩
  · simp only [inv_inv]
    rw [Fin.lt_def, quadPerm_val, quadPerm_val]
    have := x'.2
    simp only [blockEquiv_inl_val, Multiset.card_add, Multiset.card_singleton]
    split_ifs <;> omega
  · simp only [inv_inv]
    rw [Fin.lt_def, quadPerm_val, quadPerm_val]
    rw [Fin.lt_def] at hyy'
    have := y'.2
    simp only [blockEquiv_inr_val, Multiset.card_add, Multiset.card_singleton]
    split_ifs <;> omega

omit [DecidableEq I] in
/-- A shuffle of `(ν₀ + ν', i)` whose new strand ends at most at position `|ν₀|` factors as
`u⁻¹ = (a × 1) d⁻¹`. -/
theorem exists_inv_eq_blockPerm_mul (u : Shuffle (Seq.card_add' (ν₀ + ν') (Si i)))
    (z : Fin (Multiset.card (Si i)))
    (hr : (u.1⁻¹ (blockEquiv (Seq.card_add' (ν₀ + ν') (Si i)) (Sum.inr z))).val ≤
      Multiset.card ν₀) :
    ∃ a : Perm (Fin (Multiset.card ν₀ + 1)), u.1⁻¹ = blockPerm (firstBlock_h ν₀ ν' i) a 1 *
      (quadPerm (firstQuad_h ν₀ ν' i) (firstQuad ν₀ ν' i))⁻¹ := by
  set d := quadPerm (firstQuad_h ν₀ ν' i) (firstQuad ν₀ ν' i)
  obtain ⟨a, ha⟩ := exists_blockPerm_one_eq (firstBlock_h ν₀ ν' i) (w := u.1⁻¹ * d) (by
    intro y
    have hy := y.2
    have hdy : (d (blockEquiv (firstBlock_h ν₀ ν' i) (Sum.inr y))).val =
        Multiset.card ν₀ + y.val := by
      rw [quadPerm_val]
      simp only [blockEquiv_inr_val, Multiset.card_add, Multiset.card_singleton]
      split_ifs <;> omega
    have hx : Multiset.card ν₀ + y.val < Multiset.card (ν₀ + ν') := by
      simp only [Multiset.card_add]; omega
    have hdx : d (blockEquiv (firstBlock_h ν₀ ν' i) (Sum.inr y)) =
        blockEquiv (Seq.card_add' (ν₀ + ν') (Si i)) (Sum.inl ⟨_, hx⟩) := Fin.ext hdy
    rw [Perm.mul_apply, hdx]
    apply Fin.ext
    rw [shuffle_inl_val_of_le _ (Multiset.card_singleton i) u z _ (by simp only; omega)]
    simp only [blockEquiv_inr_val]
    omega)
  exact ⟨a, by rw [ha, mul_inv_cancel_right]⟩

/-- **`ŵ_u^* = ψ_a ψ_d^* 1_{ν₀+ν',i}`** for a shuffle `u` whose new strand ends at most at
position `|ν₀|`, with the words `firstSlideWord`. -/
theorem exists_hatWRevOf_firstSlideWord (u : Shuffle (Seq.card_add' (ν₀ + ν') (Si i)))
    (z : Fin (Multiset.card (Si i)))
    (hr : (u.1⁻¹ (blockEquiv (Seq.card_add' (ν₀ + ν') (Si i)) (Sum.inr z))).val ≤
      Multiset.card ν₀) :
    ∃ a : Perm (Fin (Multiset.card ν₀ + 1)),
      u.1⁻¹ = blockPerm (firstBlock_h ν₀ ν' i) a 1 *
        (quadPerm (firstQuad_h ν₀ ν' i) (firstQuad ν₀ ν' i))⁻¹ ∧
      (hatWRevOf (firstSlideWord ν₀ ν' i) u : KLRAlgebra k Q (ν₀ + ν' + Si i)) =
        ψw (canWord _ a) * hflip (firstψ Q ν₀ ν' i) * oneConcat Q (ν₀ + ν') (Si i) := by
  obtain ⟨a, ha⟩ := exists_inv_eq_blockPerm_mul u z hr
  refine ⟨a, ha, ?_⟩
  rw [hatWRevOf, firstSlideWord, List.reverse_reverse,
    parabolicWord_of_eq _ isShuffle_inv_quadPerm_firstQuad ha.symm, inv_inv, ψw_append,
    firstψ, hflip_ψw]

end KLRAlgebra

end Categorification.KLR
