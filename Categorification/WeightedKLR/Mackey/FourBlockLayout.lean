/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.BlockConjugate

/-!
# The two layouts of the middle parabolic

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4). For dimension vectors
`a, b, c, d`, the strands of `(a + b) + (c + d)` fall into four blocks `a, b, c, d` (in this order,
colour by colour), and those of `(a + c) + (b + d)` into the blocks `a, c, b, d`. The relabelling
`middleSwap a b c d` of the strands of `(a + b) + (c + d)` exchanges the two middle blocks: it
sends the strands drawn in the order `a b c d` to the same strands drawn in the order `a c b d`,
read in `(a + b) + (c + d)` along the equality `(a + c) + (b + d) = (a + b) + (c + d)`.

## Main definitions

* `Juxtapose.middleRank`: the rank map exchanging the two middle blocks.
* `Juxtapose.middleSwap a b c d`: the corresponding relabelling.

## Main results

* `Juxtapose.middleSwap_inl_inl`, `middleSwap_inl_inr`, `middleSwap_inr_inl`,
  `middleSwap_inr_inr`: `middleSwap` sends each block of the layout `a b c d` to the same block
  of the layout `a c b d`.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

attribute [local instance] ColPerm.fintype

namespace Juxtapose

variable (a b c d : I →₀ ℕ)

omit [DecidableEq I] in
/-- The two layouts have the same strands. -/
theorem layout_eq : a + c + (b + d) = a + b + (c + d) := add_add_add_comm a c b d

/-- The rank map exchanging the two middle blocks, of sizes `p` and `q`, after a block of
size `n`. -/
def middleRank (n p q r : ℕ) : ℕ :=
  if r < n then r else if r < n + p then r + q else if r < n + p + q then r - p else r

omit [DecidableEq I] in
theorem middleRank_middleRank (n p q r : ℕ) : middleRank n q p (middleRank n p q r) = r := by
  unfold middleRank
  split_ifs <;> omega

omit [DecidableEq I] in
theorem middleRank_lt (n p q m r : ℕ) (hr : r < n + p + q + m) :
    middleRank n p q r < n + p + q + m := by
  unfold middleRank
  split_ifs <;> omega

omit [DecidableEq I] in
theorem middleRank_first {n p q r : ℕ} (hr : r < n) : middleRank n p q r = r := by
  unfold middleRank; simp [hr]

omit [DecidableEq I] in
theorem middleRank_second {n p q r : ℕ} (hr : r < p) : middleRank n p q (n + r) = n + q + r := by
  unfold middleRank; split_ifs <;> omega

omit [DecidableEq I] in
theorem middleRank_third {n p q r : ℕ} (hr : r < q) : middleRank n p q (n + p + r) = n + r := by
  unfold middleRank; split_ifs <;> omega

omit [DecidableEq I] in
theorem middleRank_fourth (n p q r : ℕ) :
    middleRank n p q (n + p + (q + r)) = n + q + (p + r) := by
  unfold middleRank; split_ifs <;> omega

omit [DecidableEq I] in
theorem apply_four (t : Strand (a + b + (c + d))) :
    (a + b + (c + d)) (t.1 : I) = a t.1 + b t.1 + c t.1 + d t.1 := by
  simp only [Finsupp.add_apply]
  omega

/-- The map of strands of `(a + b) + (c + d)` exchanging the two middle blocks, of sizes `p i`
and `q i` after a block of size `a i`. -/
def middleStrand (p q : I →₀ ℕ) (hpq : ∀ i, p i + q i = b i + c i)
    (t : Strand (a + b + (c + d))) : Strand (a + b + (c + d)) :=
  ⟨t.1, ⟨middleRank (a t.1) (p t.1) (q t.1) t.2.val, by
    have h₁ := t.2.2
    have h₂ := hpq t.1
    simp only [Finsupp.add_apply] at h₁ ⊢
    have := middleRank_lt (a t.1) (p t.1) (q t.1) (d t.1) t.2.val (by omega)
    omega⟩⟩

/-- **The middle swap.** The relabelling of the strands of `(a + b) + (c + d)` exchanging the
blocks `b` and `c`, colour by colour. -/
def middleSwap : ColPerm (a + b + (c + d)) :=
  ⟨{ toFun := middleStrand a b c d b c fun _ => rfl
     invFun := middleStrand a b c d c b fun _ => add_comm _ _
     left_inv := fun _ => Strand.ext_of rfl (middleRank_middleRank _ _ _ _)
     right_inv := fun _ => Strand.ext_of rfl (middleRank_middleRank _ _ _ _) },
    mem_colPerm.2 fun _ => rfl⟩

omit [DecidableEq I] in
theorem middleSwap_apply (t : Strand (a + b + (c + d))) :
    (middleSwap a b c d).1 t =
      ⟨t.1, ⟨middleRank (a t.1) (b t.1) (c t.1) t.2.val, ((middleSwap a b c d).1 t).2.2⟩⟩ :=
  rfl

omit [DecidableEq I] in
theorem middleSwap_inl_inl (s : Strand a) :
    (middleSwap a b c d).1 (inlStrand (a + b) (c + d) (inlStrand a b s)) =
      castStrand (layout_eq a b c d) (inlStrand (a + c) (b + d) (inlStrand a c s)) := by
  refine Strand.ext_of (Subtype.ext (by rw [castStrand_colour]; rfl)) ?_
  rw [castStrand_rank]
  show middleRank (a (s.1 : I)) (b (s.1 : I)) (c (s.1 : I)) s.2.val = s.2.val
  exact middleRank_first s.2.2

omit [DecidableEq I] in
theorem middleSwap_inl_inr (s : Strand b) :
    (middleSwap a b c d).1 (inlStrand (a + b) (c + d) (inrStrand a b s)) =
      castStrand (layout_eq a b c d) (inrStrand (a + c) (b + d) (inlStrand b d s)) := by
  refine Strand.ext_of (Subtype.ext (by rw [castStrand_colour]; rfl)) ?_
  rw [castStrand_rank]
  show middleRank (a (s.1 : I)) (b (s.1 : I)) (c (s.1 : I)) (a s.1 + s.2.val) =
    (a + c) s.1 + s.2.val
  rw [middleRank_second s.2.2, Finsupp.add_apply]

omit [DecidableEq I] in
theorem middleSwap_inr_inl (s : Strand c) :
    (middleSwap a b c d).1 (inrStrand (a + b) (c + d) (inlStrand c d s)) =
      castStrand (layout_eq a b c d) (inlStrand (a + c) (b + d) (inrStrand a c s)) := by
  refine Strand.ext_of (Subtype.ext (by rw [castStrand_colour]; rfl)) ?_
  rw [castStrand_rank]
  show middleRank (a (s.1 : I)) (b (s.1 : I)) (c (s.1 : I)) ((a + b) s.1 + s.2.val) =
    a s.1 + s.2.val
  rw [Finsupp.add_apply, middleRank_third s.2.2]

omit [DecidableEq I] in
theorem middleSwap_inr_inr (s : Strand d) :
    (middleSwap a b c d).1 (inrStrand (a + b) (c + d) (inrStrand c d s)) =
      castStrand (layout_eq a b c d) (inrStrand (a + c) (b + d) (inrStrand b d s)) := by
  refine Strand.ext_of (Subtype.ext (by rw [castStrand_colour]; rfl)) ?_
  rw [castStrand_rank]
  show middleRank (a (s.1 : I)) (b (s.1 : I)) (c (s.1 : I)) ((a + b) s.1 + (c s.1 + s.2.val)) =
    (a + c) s.1 + (b s.1 + s.2.val)
  rw [Finsupp.add_apply, Finsupp.add_apply, middleRank_fourth]

end Juxtapose

end Categorification.WeightedKLR
