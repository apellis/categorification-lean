/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.GapSort
import Categorification.WeightedKLR.RedStrands.SplitRedInjective

/-!
# Splitting a red strand: violated diagrams

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.3,
Proposition 4.21. A loading of `λ'` in which the red strands `c` and `c + 1` are adjacent is the
split loading of a loading of `λ`. A diagram between split loadings that passes through a
violated loading factors through a violated split loading: the strands between the two red
strands are slid out of the gap, which is the effect of the bigon and triangle relations
(Webster, Lemma 4.10) in the proof of Proposition 4.21.

## Main results

* `exists_splitLoading_eq` : a loading with adjacent red strands `c`, `c + 1` is split.
-/

noncomputable section

namespace Categorification.Stendhal.SplitRed

open KLR TypeA Equiv

variable {I : Type} {ℓ : ℕ} (c : Fin ℓ) {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "μ'" => stendhalWeight (ℓ + 1) ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-! ### Merging adjacent red strands -/

/-- A left inverse of `splitColor c`. -/
def mergeColor : I ⊕ Fin (ℓ + 1) → I ⊕ Fin ℓ :=
  haveI : Nonempty (I ⊕ Fin ℓ) := ⟨.inr c⟩
  Function.invFun (splitColor c)

@[simp] theorem mergeColor_splitColor (x : I ⊕ Fin ℓ) : mergeColor c (splitColor c x) = x :=
  haveI : Nonempty (I ⊕ Fin ℓ) := ⟨.inr c⟩
  Function.leftInverse_invFun (splitColor_injective c) x

theorem splitColor_mergeColor {y : I ⊕ Fin (ℓ + 1)} (hy : y ≠ .inr c.succ) :
    splitColor c (mergeColor c y) = y := by
  rcases y with i | r
  · exact congrArg (splitColor c) (mergeColor_splitColor c (.inl i))
  · obtain ⟨r', hr'⟩ := Fin.exists_succAbove_eq (x := r) (y := c.succ)
      (fun e => hy (by rw [e]))
    rw [← hr']
    exact congrArg (splitColor c) (mergeColor_splitColor c (.inr r'))

variable [DecidableEq I]

/-- The label of the new red strand of a loading of `λ'` occurs at one position only. -/
theorem ne_new_of_ne {t : Seq μ'} {a b : Fin (Multiset.card μ')} (hab : a ≠ b)
    (hb : t.lbl b = .inr c.succ) : t.lbl a ≠ .inr c.succ := fun ha =>
  hab (eq_of_lbl_eq_inr (ν := ν) ha hb)

/-- The positions of the old strands, given the position `b` of the red strand `c`. -/
private def oldPos (b : Fin m) (a : Fin m) : Fin (Multiset.card μ') :=
  (posEquiv ℓ ν).symm (b.succ.succAbove a)

omit [DecidableEq I] in
private theorem oldPos_val (b a : Fin m) :
    (oldPos (ν := ν) b a : ℕ) = if (a : ℕ) ≤ b then (a : ℕ) else (a : ℕ) + 1 := by
  simp only [oldPos, finCongr_symm, finCongr_apply, Fin.val_cast, Fin.succAbove]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Fin.castSucc_lt_succ_iff.1 h1) h2
  · exact absurd (Fin.castSucc_lt_succ_iff.2 h2) h1
  · simp

omit [DecidableEq I] in
private theorem map_univ_oldPos {α : Type*} (b : Fin m) (g : Fin (Multiset.card μ') → α) :
    Finset.univ.val.map g = Finset.univ.val.map (fun a => g (oldPos (ν := ν) b a)) +
      {g ⟨b + 1, by have := card_split ℓ ν; omega⟩} := by
  have hu := congrArg Finset.val (Finset.map_univ_equiv (posEquiv ℓ ν).symm)
  rw [show (Finset.univ : Finset (Fin (Multiset.card μ'))).val =
    Finset.univ.val.map (posEquiv ℓ ν).symm from hu.symm, Multiset.map_map,
    Fin.univ_succAbove m b.succ]
  change ((b.succ ::ₘ (Finset.univ.map (Fin.succAboveEmb _)).val).map _) = _
  rw [Multiset.map_cons, ← Multiset.singleton_add, add_comm]
  simp only [Finset.map_val, Multiset.map_map, Function.comp_def, Fin.coe_succAboveEmb]
  rfl

/-- A loading of `λ'` with the red strand `c + 1` just right of the red strand `c` is the
split loading of a loading of `λ`. -/
theorem exists_splitLoading_eq (t : Seq μ') (b : Fin m)
    (hb : t.lbl ⟨b, by have := card_split ℓ ν; omega⟩ = .inr c.castSucc)
    (hb' : t.lbl ⟨b + 1, by have := card_split ℓ ν; omega⟩ = .inr c.succ) :
    ∃ t₀ : Seq μ, splitLoading c t₀ = t ∧ redPos c t₀ = b := by
  have hcard := card_split ℓ ν
  set B' : Fin (Multiset.card μ') := ⟨b + 1, by omega⟩
  have hne : ∀ a : Fin m, t.lbl (oldPos b a) ≠ .inr c.succ := fun a =>
    ne_new_of_ne c (b := B') (fun e => by
      have := congrArg Fin.val e; rw [oldPos_val] at this; simp only [B'] at this
      split_ifs at this <;> omega) hb'
  let f : Fin m → I ⊕ Fin ℓ := fun a => mergeColor c (t.lbl (oldPos b a))
  have hf : Finset.univ.val.map f = μ := by
    apply Multiset.map_injective (splitColor_injective c)
    have h1 : (Finset.univ.val.map f).map (splitColor c) =
        Finset.univ.val.map fun a => t.lbl (oldPos b a) := by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun a _ => splitColor_mergeColor c (hne a)
    rw [h1]
    apply (add_left_inj ({.inr c.succ} : Multiset (I ⊕ Fin (ℓ + 1)))).1
    rw [stendhalWeight_split]
    -- the positions of `μ'` are the old positions and `b + 1`
    refine Eq.trans ?_ t.2
    rw [map_univ_oldPos b t.1]
    exact congrArg₂ (· + ·) rfl (congrArg _ hb'.symm)
  let t₀ : Seq μ := ⟨f, hf⟩
  have hred : redPos c t₀ = b := by
    refine (eq_redPos c ?_).symm
    change mergeColor c (t.lbl (oldPos b b)) = _
    have : oldPos (ν := ν) b b = ⟨b, by omega⟩ := Fin.ext (by rw [oldPos_val]; simp)
    rw [this, hb, ← succAbove_self, ← splitColor_inr, mergeColor_splitColor]
  refine ⟨t₀, ?_, hred⟩
  apply Subtype.ext
  funext x
  change (splitLoading c t₀).lbl x = t.lbl x
  have hr : (redPos c t₀ : ℕ) = b := congrArg Fin.val hred
  rw [splitLoading_lbl]
  split_ifs with h1 h2
  · change splitColor c (mergeColor c (t.lbl (oldPos b ⟨x, _⟩))) = _
    rw [splitColor_mergeColor c (hne _)]
    congr 1; apply Fin.ext; rw [oldPos_val]; simp only; split_ifs <;> omega
  · rw [show x = B' from Fin.ext (by simp only [B']; omega), hb']
  · change splitColor c (mergeColor c (t.lbl (oldPos b ⟨x - 1, _⟩))) = _
    rw [splitColor_mergeColor c (hne _)]
    congr 1; apply Fin.ext; rw [oldPos_val]; simp only; split_ifs <;> omega

end Categorification.Stendhal.SplitRed
