/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Relabel
import Categorification.WeightedKLR.Segment

/-!
# Walls and diagonals as affine functions

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.1 and proof of
Theorem 2.8.

Every hyperplane `h` of the arrangement of walls and diagonals has the form
`x_{h.hi} - x_{h.lo} = h.cst` for two distinct strands `h.lo`, `h.hi`. This file packages the
hyperplanes as affine functions `hypAff h`, so that the general results on segments in
`Segment/*.lean` apply, and proves that under assumption (†) and the absence of loops of
weight `0` two distinct hyperplanes are distinct as subsets of the configuration space
(`hdist`): the input `hdist` of `Segment.exists_simple` and `Segment.reflTransGen_flip_of_simple`.

## Main definitions

* `Hyp.lo`, `Hyp.hi`, `Hyp.cst`: `h.val p = p h.hi - p h.lo - h.cst`.
* `Hyp.Mem s h`: the strand `s` is one of `h.lo`, `h.hi`.
* `Hyp.IsPair h a b`: the strands of `h` are `a` and `b`.
* `hypAff h`: the affine function `h.val`.

## Main results

* `Hyp.eq_of_isPair`: two hyperplanes on the same two strands through a common point coincide.
* `hdist`: every hyperplane has a point off any other hyperplane.
-/

namespace Categorification.WeightedKLR

open Equiv

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace Hyp

/-- The first strand of a hyperplane: the source of a wall, the strand of smaller rank of a
diagonal. -/
def lo : Hyp Γ ν → Strand ν
  | .inl w => w.src
  | .inr d => d.fst

/-- The second strand of a hyperplane. -/
def hi : Hyp Γ ν → Strand ν
  | .inl w => w.tgt
  | .inr d => d.snd

/-- The constant of a hyperplane: the weight of the edge of a wall, `0` for a diagonal. -/
def cst : Hyp Γ ν → 𝕜
  | .inl w => Γ.weight w.edge
  | .inr _ => 0

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem val_eq (h : Hyp Γ ν) (p : Strand ν → 𝕜) : h.val p = p h.hi - p h.lo - h.cst := by
  rcases h with w | d
  · rfl
  · simp [val, Diag.val, hi, lo, cst]

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem lo_ne_hi (h : Hyp Γ ν) : h.lo ≠ h.hi := by
  rcases h with w | d
  · exact w.2.2.2
  · exact d.fst_ne_snd

/-- The strand `s` is one of the two strands of `h`. -/
def Mem (s : Strand ν) (h : Hyp Γ ν) : Prop := s = h.lo ∨ s = h.hi

/-- The two strands of `h` are `a` and `b`. -/
def IsPair (h : Hyp Γ ν) (a b : Strand ν) : Prop :=
  (h.lo = a ∧ h.hi = b) ∨ (h.lo = b ∧ h.hi = a)

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem IsPair.symm {h : Hyp Γ ν} {a b : Strand ν} (hp : h.IsPair a b) : h.IsPair b a :=
  Or.symm hp

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem isPair_self (h : Hyp Γ ν) : h.IsPair h.lo h.hi := Or.inl ⟨rfl, rfl⟩

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem IsPair.mem_iff {h : Hyp Γ ν} {a b : Strand ν} (hp : h.IsPair a b) (s : Strand ν) :
    Mem s h ↔ s = a ∨ s = b := by
  unfold Mem
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2, or_comm]

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem IsPair.ne {h : Hyp Γ ν} {a b : Strand ν} (hp : h.IsPair a b) : a ≠ b := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.lo_ne_hi
  · exact h.lo_ne_hi.symm

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem isPair_of_mem {h : Hyp Γ ν} {a b : Strand ν} (ha : Mem a h) (hb : Mem b h)
    (hab : a ≠ b) : h.IsPair a b := by
  unfold Mem at ha hb
  unfold IsPair
  have := h.lo_ne_hi
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- If the strands of `h` are strands of `g`, then `g` lies on the same two strands. -/
theorem isPair_of_forall_mem {h g : Hyp Γ ν} (hs : ∀ s, Mem s h → Mem s g) :
    g.IsPair h.lo h.hi :=
  isPair_of_mem (hs _ (Or.inl rfl)) (hs _ (Or.inr rfl)) h.lo_ne_hi

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A strand of `h` other than `a` is the other strand of `h`. -/
theorem exists_other {h : Hyp Γ ν} {a : Strand ν} (ha : Mem a h) :
    ∃ b, b ≠ a ∧ h.IsPair a b := by
  rcases ha with rfl | rfl
  · exact ⟨h.hi, h.lo_ne_hi.symm, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨h.lo, h.lo_ne_hi, Or.inr ⟨rfl, rfl⟩⟩

/-! ### Distinct hyperplanes on the same strands -/

omit [DecidableEq I] in
theorem _root_.Categorification.WeightedKLR.Diag.label_fst (d : Diag ν) :
    d.fst.label = d.snd.label := congrArg Subtype.val d.2.1

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem _root_.Categorification.WeightedKLR.Wall.label_src (w : Wall Γ ν) :
    w.src.label = Γ.head w.edge := w.2.1

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem _root_.Categorification.WeightedKLR.Wall.label_tgt (w : Wall Γ ν) :
    w.tgt.label = Γ.tail w.edge := w.2.2.1

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A wall whose two strands have the same colour comes from a loop. -/
theorem _root_.Categorification.WeightedKLR.Wall.head_eq_tail_of_label {w : Wall Γ ν}
    (h : w.src.label = w.tgt.label) : Γ.head w.edge = Γ.tail w.edge :=
  w.label_src.symm.trans (h.trans w.label_tgt)

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Two distinct hyperplanes on the same strands in the same order have different constants. -/
theorem cst_ne_of_same (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {h g : Hyp Γ ν}
    (hlo : h.lo = g.lo) (hhi : h.hi = g.hi) (hne : h ≠ g) : h.cst ≠ g.cst := by
  intro hc
  apply hne
  rcases h with w | d <;> rcases g with w' | d'
  · have he : w.edge = w'.edge := hD.1 _ _
      (by rw [← w.label_tgt, ← w'.label_tgt]; exact congrArg Strand.label hhi)
      (by rw [← w.label_src, ← w'.label_src]; exact congrArg Strand.label hlo) hc
    exact congrArg Sum.inl (Subtype.ext (Prod.ext he (Prod.ext hlo hhi)))
  · change w.src = d'.fst at hlo
    change w.tgt = d'.snd at hhi
    have hl : w.src.label = w.tgt.label := by rw [hlo, hhi]; exact d'.label_fst
    exact absurd hc (hZ _ (Wall.head_eq_tail_of_label hl))
  · change d.fst = w'.src at hlo
    change d.snd = w'.tgt at hhi
    have hl : w'.src.label = w'.tgt.label := by rw [← hlo, ← hhi]; exact d.label_fst
    exact absurd hc.symm (hZ _ (Wall.head_eq_tail_of_label hl))
  · exact congrArg Sum.inr (Subtype.ext (Prod.ext hlo hhi))

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Two hyperplanes on the same strands in opposite orders have constants of nonzero sum. -/
theorem cst_add_ne_of_swap (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {h g : Hyp Γ ν}
    (hlo : h.lo = g.hi) (hhi : h.hi = g.lo) : h.cst + g.cst ≠ 0 := by
  rcases h with w | d <;> rcases g with w' | d'
  · change w.src = w'.tgt at hlo
    change w.tgt = w'.src at hhi
    have := hD.2 w.edge w'.edge
      (by rw [← w.label_tgt, ← w'.label_src]; exact congrArg Strand.label hhi)
      (by rw [← w.label_src, ← w'.label_tgt]; exact congrArg Strand.label hlo)
    change Γ.weight w.edge + Γ.weight w'.edge ≠ 0
    intro h0
    exact this (eq_neg_of_add_eq_zero_right h0)
  · change w.src = d'.snd at hlo
    change w.tgt = d'.fst at hhi
    have hl : w.src.label = w.tgt.label := by rw [hlo, hhi]; exact d'.label_fst.symm
    change Γ.weight w.edge + 0 ≠ 0
    rw [add_zero]
    exact hZ _ (Wall.head_eq_tail_of_label hl)
  · change d.fst = w'.tgt at hlo
    change d.snd = w'.src at hhi
    have hl : w'.src.label = w'.tgt.label := by rw [← hlo, ← hhi]; exact d.label_fst.symm
    change 0 + Γ.weight w'.edge ≠ 0
    rw [zero_add]
    exact hZ _ (Wall.head_eq_tail_of_label hl)
  · exfalso
    change d.fst = d'.snd at hlo
    change d.snd = d'.fst at hhi
    have h1 := d.2.2
    have h2 := d'.2.2
    change d.fst.2.val < d.snd.2.val at h1
    change d'.fst.2.val < d'.snd.2.val at h2
    rw [hlo, hhi] at h1
    omega

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Two hyperplanes on the same two strands through a common point coincide. -/
theorem eq_of_isPair (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {h g : Hyp Γ ν} {a b : Strand ν}
    {x : Strand ν → 𝕜} (hx : h.val x = 0) (gx : g.val x = 0) (hp : h.IsPair a b)
    (gp : g.IsPair a b) : h = g := by
  by_contra hne
  rw [val_eq] at hx gx
  have same : h.lo = g.lo → h.hi = g.hi → False := fun hlo hhi =>
    cst_ne_of_same hD hZ hlo hhi hne (by rw [hlo, hhi] at hx; linear_combination gx - hx)
  have swap : h.lo = g.hi → h.hi = g.lo → False := fun hlo hhi =>
    cst_add_ne_of_swap hD hZ hlo hhi (by rw [hlo, hhi] at hx; linear_combination -hx - gx)
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases gp with ⟨g1, g2⟩ | ⟨g1, g2⟩
  · exact same (h1.trans g1.symm) (h2.trans g2.symm)
  · exact swap (h1.trans g2.symm) (h2.trans g1.symm)
  · exact swap (h1.trans g2.symm) (h2.trans g1.symm)
  · exact same (h1.trans g1.symm) (h2.trans g2.symm)

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem val_add (h : Hyp Γ ν) (p v : Strand ν → 𝕜) :
    h.val (p + v) = h.val p + (v h.hi - v h.lo) := by
  rw [val_eq, val_eq]; simp only [Pi.add_apply]; ring

end Hyp

/-! ### Hyperplanes as affine functions -/

/-- The hyperplane `h` as the affine function `p ↦ p h.hi - p h.lo - h.cst`. -/
def hypAff (h : Hyp Γ ν) : (Strand ν → 𝕜) →ᵃ[𝕜] 𝕜 where
  toFun := h.val
  linear := LinearMap.proj (R := 𝕜) (φ := fun _ : Strand ν => 𝕜) h.hi -
    LinearMap.proj (R := 𝕜) (φ := fun _ : Strand ν => 𝕜) h.lo
  map_vadd' p v := by
    change h.val (v + p) = (v h.hi - v h.lo) + h.val p
    rw [add_comm v p, Hyp.val_add]
    ring

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem hypAff_apply (h : Hyp Γ ν) (p : Strand ν → 𝕜) : hypAff h p = h.val p := rfl

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem hypAff_linear_apply (h : Hyp Γ ν) (v : Strand ν → 𝕜) :
    (hypAff h).linear v = v h.hi - v h.lo := by
  rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem signs_hypAff (p : Strand ν → 𝕜) :
    Segment.signs (hypAff (Γ := Γ)) p = fullSigns p := rfl

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem generic_hypAff_iff (p : Strand ν → 𝕜) :
    Segment.Generic (hypAff (Γ := Γ)) p ↔ IsGeneric Γ p := Iff.rfl

omit [IsStrictOrderedRing 𝕜] in
/-- Under (†) and the absence of loops of weight `0`, every hyperplane has a point off any other
hyperplane. -/
theorem hdist (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (h g : Hyp Γ ν) (hne : h ≠ g) :
    ∃ x, hypAff h x = 0 ∧ hypAff g x ≠ 0 := by
  classical
  set x₀ : Strand ν → 𝕜 := Pi.single h.hi h.cst
  have h₀ : h.val x₀ = 0 := by
    rw [Hyp.val_eq]
    simp [x₀, h.lo_ne_hi]
  simp only [hypAff_apply]
  by_cases hs : ∃ s, Hyp.Mem s g ∧ ¬ Hyp.Mem s h
  · obtain ⟨s, hsg, hsh⟩ := hs
    by_cases hg : g.val x₀ = 0
    · refine ⟨x₀ + Pi.single s 1, ?_, ?_⟩
      · rw [Hyp.val_add, h₀]
        unfold Hyp.Mem at hsh
        push Not at hsh
        simp [Ne.symm hsh.1, Ne.symm hsh.2]
      · rw [Hyp.val_add, hg, zero_add]
        rcases hsg with rfl | rfl
        · simp [g.lo_ne_hi.symm]
        · simp [g.lo_ne_hi]
    · exact ⟨x₀, h₀, hg⟩
  · push Not at hs
    refine ⟨x₀, h₀, fun hg => hne ?_⟩
    exact Hyp.eq_of_isPair hD hZ h₀ hg (Hyp.isPair_of_forall_mem hs) (Hyp.isPair_self g)

end Categorification.WeightedKLR
