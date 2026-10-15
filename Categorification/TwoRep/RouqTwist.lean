/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqModel

/-!
# The orientation-reversing twist of Rouquier's data

M. Khovanov, A. Lauda, *A categorification of quantum sl(n)* (KL III), arXiv:0807.3250v1,
§3.3.2 (Symmetries): the 2-functor `ω̃` that sends `λ ↦ -λ`, reverses the orientation of every
strand and rescales the same-colour crossings by `-1`.
We realize it on Rouquier's data (J. Brundan, *On the definition of Kac–Moody 2-category*,
arXiv:1501.00350v1, Definition 1.1), in the **same** bicategory: from data at the weight `h` we
obtain data at the weight `-h` with

* `E' = F`, `F' = E`, and the adjunction `F ⊣ E` the left adjunction of Brundan's Theorem 4.3
  (`RouqLoc.leftAdjunction`, `RouqFamily.adjL`);
* the dot `x'` the downward dot, i.e. the right mate of the dot (Brundan (1.12)); by the dot
  cyclicity (Brundan (5.6), `RouqFamily.dotDn_eq_rightMate`) it is also the left mate;
* the crossing `τ'` **minus** the right mate of the upward crossing (the downward crossing). The
  sign is forced by the nilHecke dot slides `x'₂ τ' - τ' x'₁ = 1` (`RouqLoc.twist`, fields
  `slide_left`, `slide_right`), and agrees with the sign of the crossing in Brundan's Theorem 2.3.

The invertibility of Rouquier's map for the twisted data (Brundan (1.8)/(1.9) at `-h`) comes
from that of the original data: the twisted rightward crossing is minus the leftward crossing
`σ'` (Brundan (1.14)–(1.16); `RouqLoc.twist_sig`, via the mate identity of Brundan §5,
`RouqLoc.mate_rightMate_eq_sigL`), the twisted dotted caps and cups are the leftward caps and
cups with dots, and Brundan's decompositions (3.16), (3.17) (Corollary 3.4,
`RouqLoc.decompEF`, `RouqLoc.decompFE`) give the inverse components explicitly: dotted
rightward caps (resp. cups) followed (resp. preceded) by bubbles. The orthogonality relations
are Brundan (3.6), (3.7) (Lemma 3.1) and the bubble pairing (3.15) with its mirror image.

## Main declarations

* `RouqLoc.twist`: twisted Rouquier data at one weight, from data at three consecutive weights;
* `RouqLoc.twist_sig`: the twisted rightward crossing is `-σ'`;
* `RouqSl2Generic.neg_rightMate_square`, `RouqSl2Generic.neg_rightMate_braid`: the nilHecke
  relations (Brundan (1.3), (1.4)) for the twisted crossing;
* `RouqFamily.twist`: the twist of a whole Rouquier family (weights `x ↦ -x`), with
  `RouqFamily.twist_dot` (the dot is `dotDn`) and `RouqFamily.twist_adj` (the adjunction is
  `adjL`). Restricting along `RouqFamily.toRouqSl2` gives the twist of a single-colour string.

For distinct colours the twisted crossing of `RouqFamily.twist` is also minus the right mate of
the upward crossing. KL's `ω̃` rescales only the same-colour crossings, so for `i ≠ j` this differs
from the orientation reversal of KL by the sign `-1`. `RouqFamily` imposes no relation on mixed
crossings; the mixed-colour convention is not used by any statement in this file.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory Opposite

universe w v u u₁

/-! ## Generic lemmas -/

namespace RouqSl2Generic

section Slides

variable {C : Type u} [Bicategory.{w, v} C] {a b : C} {E : a ⟶ b} {R : b ⟶ a}

/-- Iterated dot slide around a cup `𝟙 ⟶ R ≫ E`. -/
theorem cup_powComp_slide {η : 𝟙 b ⟶ R ≫ E} {x : E ⟶ E} {y : R ⟶ R}
    (hη : η ≫ R ◁ x = η ≫ y ▷ E) (n : ℕ) :
    η ≫ R ◁ powComp x n = η ≫ powComp y n ▷ E := by
  induction n with
  | zero => simp [powComp_zero]
  | succ n ih =>
    rw [powComp_succ x, Bicategory.whiskerLeft_comp, ← Category.assoc, ih, Category.assoc,
      ← whisker_exchange, ← Category.assoc, hη, Category.assoc, ← Bicategory.comp_whiskerRight,
      comp_powComp]

/-- Iterated dot slide around a cap `E ≫ R ⟶ 𝟙`. -/
theorem cap_powComp_slide {e : E ≫ R ⟶ 𝟙 a} {x : E ⟶ E} {y : R ⟶ R}
    (he : x ▷ R ≫ e = E ◁ y ≫ e) (n : ℕ) :
    powComp x n ▷ R ≫ e = E ◁ powComp y n ≫ e := by
  induction n with
  | zero => simp [powComp_zero]
  | succ n ih =>
    rw [powComp_succ x, Bicategory.comp_whiskerRight, Category.assoc, he, ← Category.assoc,
      ← whisker_exchange, Category.assoc, ih, ← Category.assoc, ← Bicategory.whiskerLeft_comp,
      comp_powComp]

end Slides

section Sigma

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)]
  [AdditiveWhiskering C] {a b c : C} {E₁ : a ⟶ b} {E₂ : b ⟶ c} {R₁ : b ⟶ a} {R₂ : c ⟶ b}

/-- The rightward crossing of minus a 2-morphism is minus the rightward crossing. -/
theorem sigma_neg (η₂ : 𝟙 b ⟶ E₂ ≫ R₂) (φ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (ε₁ : R₁ ≫ E₁ ⟶ 𝟙 b) :
    RightwardCrossing.sigma η₂ (-φ) ε₁ = -RightwardCrossing.sigma η₂ φ ε₁ := by
  simp only [RightwardCrossing.sigma_eq, AdditiveWhiskering.whiskerLeft_neg,
    AdditiveWhiskering.neg_whiskerRight, Preadditive.comp_neg, Preadditive.neg_comp]

end Sigma

section NilHecke

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)]
  [AdditiveWhiskering C] {a₀ a₁ a₂ a₃ : C}
  {E₀ : a₀ ⟶ a₁} {R₀ : a₁ ⟶ a₀} {E₁ : a₁ ⟶ a₂} {R₁ : a₂ ⟶ a₁} {E₂ : a₂ ⟶ a₃} {R₂ : a₃ ⟶ a₂}
  (adj₀ : E₀ ⊣ R₀) (adj₁ : E₁ ⊣ R₁) (adj₂ : E₂ ⊣ R₂)

/-- Brundan (1.3) for the twisted crossing: minus the right mate of a crossing with square zero
has square zero. -/
theorem neg_rightMate_square (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (hs : τ ≫ τ = 0) :
    (-conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ) ≫
      (-conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ) = 0 := by
  rw [Preadditive.neg_comp_neg, Bicategory.conjugateEquiv_comp, hs]
  exact (rightMateAddEquiv (adj₁.comp adj₂)).map_zero

/-- Brundan (1.4) for the twisted crossing: minus the right mates of crossings satisfying the
braid relation satisfy the braid relation on the reversed composite `R₂ ≫ R₁ ≫ R₀`. -/
theorem neg_rightMate_braid (τ₀ : E₀ ≫ E₁ ⟶ E₀ ≫ E₁) (τ₁ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (hb : E₀ ◁ τ₁ ≫ ((α_ E₀ E₁ E₂).inv ≫ τ₀ ▷ E₂ ≫ (α_ E₀ E₁ E₂).hom) ≫ E₀ ◁ τ₁ =
      ((α_ E₀ E₁ E₂).inv ≫ τ₀ ▷ E₂ ≫ (α_ E₀ E₁ E₂).hom) ≫ E₀ ◁ τ₁ ≫
        ((α_ E₀ E₁ E₂).inv ≫ τ₀ ▷ E₂ ≫ (α_ E₀ E₁ E₂).hom)) :
    R₂ ◁ (-conjugateEquiv (adj₀.comp adj₁) (adj₀.comp adj₁) τ₀) ≫
      ((α_ R₂ R₁ R₀).inv ≫ (-conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ₁) ▷ R₀ ≫
        (α_ R₂ R₁ R₀).hom) ≫
      R₂ ◁ (-conjugateEquiv (adj₀.comp adj₁) (adj₀.comp adj₁) τ₀) =
    ((α_ R₂ R₁ R₀).inv ≫ (-conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ₁) ▷ R₀ ≫
        (α_ R₂ R₁ R₀).hom) ≫
      R₂ ◁ (-conjugateEquiv (adj₀.comp adj₁) (adj₀.comp adj₁) τ₀) ≫
      ((α_ R₂ R₁ R₀).inv ≫ (-conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ₁) ▷ R₀ ≫
        (α_ R₂ R₁ R₀).hom) := by
  let A := adj₀.comp (adj₁.comp adj₂)
  have hh := congrArg (conjugateEquiv A A) hb
  simp only [← Bicategory.conjugateEquiv_comp A A A] at hh
  dsimp only [A] at hh
  rw [rightMate_reassociate, Bicategory.conjugateEquiv_whiskerRight,
    Bicategory.conjugateEquiv_whiskerLeft] at hh
  have e := congrArg (fun z => (α_ R₂ R₁ R₀).inv ≫ z ≫ (α_ R₂ R₁ R₀).hom) hh
  simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id] at e
  simp only [AdditiveWhiskering.whiskerLeft_neg, AdditiveWhiskering.neg_whiskerRight,
    Preadditive.comp_neg, Preadditive.neg_comp, neg_neg, neg_inj, Category.assoc]
  exact e.symm

end NilHecke

end RouqSl2Generic

/-! ## The twist at one weight -/

namespace RouqLoc

open RouqSl2Generic

section Orthogonality

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a b c : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

/-- The mirror image of Brundan (3.14): for `h < 0` a left cap with fewer than `-h` dots kills
the rightward crossing. -/
theorem sig_powComp_capL (hh : h < 0) {m : ℕ} (hm : m < (-h).toNat) :
    L.sig ≫ powComp x₂ m ▷ R₂ ≫ L.capL = 0 := by
  have hs : L.sig ≫ powComp x₂ m ▷ R₂ =
      R₁ ◁ powComp x₁ m ≫ L.sig + ∑ j ∈ Finset.range m, L.capD j ≫ L.cupD (m - 1 - j) := by
    rw [L.powComp_sig]; abel
  rw [← Category.assoc, hs, Preadditive.add_comp, Category.assoc, L.sig_capL hh,
    Limits.comp_zero, zero_add, Preadditive.sum_comp]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [Category.assoc, L.cupD_capL hh (by omega), ite_eq_right (by omega), Limits.comp_zero]

/-- The mirror image of the bubble pairing (3.15), for `h < 0`. -/
theorem capN_bubble_pairing (hh : h < 0) {m n : ℕ} (hm : m < (-h).toNat) (hn : n < (-h).toNat) :
    ∑ r ∈ Finset.range ((-h).toNat - n), L.cw (r + m) ≫ L.ccw (-(n : ℤ) - r - 2) =
      if n = m then 𝟙 _ else 0 := by
  have hd := L.dual.cupN_bubble_pairing (by omega) hm hn
  simp only [dual_cw, dual_ccw] at hd
  have hu := congrArg Quiver.Hom.unop hd
  rw [Coop.unop_sum₂] at hu
  split_ifs at hu with hnm
  · rw [ite_eq_left hnm]; exact hu
  · rw [ite_eq_right hnm]; exact hu

omit [AdditiveWhiskering C] in
theorem cw_natCast (k : ℕ) : L.cw k = L.cupD k ≫ L.capL := by
  rw [cw_of_nonneg (by positivity), Int.toNat_natCast]

omit [AdditiveWhiskering C] in
theorem ccw_natCast (k : ℕ) : L.ccw k = L.cupL ≫ L.capD k := by
  rw [ccw_of_nonneg (by positivity), Int.toNat_natCast]

/-- For `h ≤ 0`: `(-σ', leftward caps with dots) : F E 1_λ → E F 1_λ ⊕ 1_λ^{⊕ -h}` is invertible,
with inverse `σ` and the dotted rightward cups preceded by counter-clockwise bubbles (Brundan
(3.17)). -/
def twistInvPos (hh : h ≤ 0) :
    SumInvTo (-L.sigL) (fun n => powComp x₂ n ▷ R₂ ≫ L.capL) (-h).toNat where
  f' := L.sig
  g' r := ∑ n ∈ Finset.range ((-h).toNat - r), L.ccw (-(n : ℤ) - r - 2) ≫ L.cupD n
  total := by
    have hd := L.decompFE
    have hs : ∑ r ∈ Finset.range (-h).toNat, (powComp x₂ r ▷ R₂ ≫ L.capL) ≫
        ∑ n ∈ Finset.range ((-h).toNat - r), L.ccw (-(n : ℤ) - r - 2) ≫ L.cupD n =
        ∑ n ∈ Finset.range (-h).toNat, ∑ r ∈ Finset.range ((-h).toNat - n),
          powComp x₂ r ▷ R₂ ≫ L.capL ≫ L.ccw (-(n : ℤ) - r - 2) ≫ L.cupD n := by
      simp only [Preadditive.comp_sum, Category.assoc]
      exact Finset.sum_comm' (fun r n => by simp only [Finset.mem_range]; omega)
    rw [hs, Preadditive.neg_comp, hd]
    abel
  ff := by rw [Preadditive.comp_neg, L.sig_sigL_of_nonpos hh, neg_neg]
  fg m hm := by rw [L.sig_powComp_capL (by omega) hm]
  gf m hm := by
    rw [Preadditive.comp_neg, Preadditive.sum_comp]
    rw [Finset.sum_eq_zero, neg_zero]
    intro n hn
    rw [Category.assoc, L.cupD_sigL hh (by have := Finset.mem_range.mp hn; omega),
      Limits.comp_zero]
  gg m m' hm hm' := by
    rw [Preadditive.sum_comp]
    have he : ∀ n ∈ Finset.range ((-h).toNat - m),
        (L.ccw (-(n : ℤ) - m - 2) ≫ L.cupD n) ≫ powComp x₂ m' ▷ R₂ ≫ L.capL =
          L.cw (n + m') ≫ L.ccw (-(m : ℤ) - n - 2) := by
      intro n _
      rw [Category.assoc, ← Category.assoc (L.cupD n), L.cupD_powComp_whiskerRight,
        ← L.cw_natCast, Bicategory.endId_comm]
      congr 2
      ring
    rw [Finset.sum_congr rfl he, L.capN_bubble_pairing (by omega) hm' hm]

/-- For `h ≥ 0`: `(-σ', leftward cups with dots) : F E 1_λ ⊕ 1_λ^{⊕ h} → E F 1_λ` is invertible,
with inverse `σ` and the dotted rightward caps followed by clockwise bubbles (Brundan (3.16)). -/
def twistInvNeg (hh : 0 ≤ h) :
    SumInvFrom (-L.sigL) (fun n => L.cupL ≫ R₁ ◁ powComp x₁ n) h.toNat where
  f' := L.sig
  g' r := ∑ n ∈ Finset.range (h.toNat - r), L.capD n ≫ L.cw (-(n : ℤ) - r - 2)
  total := by
    have hd := L.decompEF
    have hs : ∑ r ∈ Finset.range h.toNat,
        (∑ n ∈ Finset.range (h.toNat - r), L.capD n ≫ L.cw (-(n : ℤ) - r - 2)) ≫
          L.cupL ≫ R₁ ◁ powComp x₁ r =
        ∑ n ∈ Finset.range h.toNat, ∑ r ∈ Finset.range (h.toNat - n),
          L.capD n ≫ L.cw (-(n : ℤ) - r - 2) ≫ L.cupL ≫ R₁ ◁ powComp x₁ r := by
      simp only [Preadditive.sum_comp, Category.assoc]
      exact Finset.sum_comm' (fun r n => by simp only [Finset.mem_range]; omega)
    rw [hs, Preadditive.comp_neg, hd]
    abel
  ff := by rw [Preadditive.neg_comp, L.sigL_sig_of_nonneg hh, neg_neg]
  fg m hm := by
    rw [Preadditive.neg_comp, Preadditive.comp_sum, Finset.sum_eq_zero, neg_zero]
    intro n hn
    rw [← Category.assoc, L.sigL_capD hh (by have := Finset.mem_range.mp hn; omega),
      Limits.zero_comp]
  gf m hm := by rw [Category.assoc]; exact L.cupL_powComp_sig (by omega) hm
  gg m m' hm hm' := by
    rw [Preadditive.comp_sum]
    have he : ∀ n ∈ Finset.range (h.toNat - m'),
        (L.cupL ≫ R₁ ◁ powComp x₁ m) ≫ L.capD n ≫ L.cw (-(n : ℤ) - m' - 2) =
          L.cw (-(m' : ℤ) - n - 2) ≫ L.ccw (n + m) := by
      intro n _
      rw [Category.assoc, ← Category.assoc (R₁ ◁ powComp x₁ m), L.whiskerLeft_powComp_capD,
        ← Category.assoc, ← L.ccw_natCast, Bicategory.endId_comm]
      congr 2 <;> push_cast <;> ring
    rw [Finset.sum_congr rfl he, L.cupN_bubble_pairing (by omega) hm hm']
    by_cases hmm : m = m'
    · subst hmm; simp
    · simp [hmm, Ne.symm hmm]

end Orthogonality

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a₀ a₁ a₂ a₃ a₄ : C}
  {E₀ : a₀ ⟶ a₁} {R₀ : a₁ ⟶ a₀} {E₁ : a₁ ⟶ a₂} {R₁ : a₂ ⟶ a₁}
  {E₂ : a₂ ⟶ a₃} {R₂ : a₃ ⟶ a₂} {E₃ : a₃ ⟶ a₄} {R₃ : a₄ ⟶ a₃}
  {adj₀ : E₀ ⊣ R₀} {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {adj₃ : E₃ ⊣ R₃}
  {x₀ : E₀ ⟶ E₀} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {x₃ : E₃ ⟶ E₃}
  {τ₀ : E₀ ≫ E₁ ⟶ E₀ ≫ E₁} {τ₁ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}
  {τ₂ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃} {h₀ h₁ h₂ : ℤ}
  (K : RouqLoc adj₀ adj₁ x₀ x₁ τ₀ h₀) (L : RouqLoc adj₁ adj₂ x₁ x₂ τ₁ h₁)
  (U : RouqLoc adj₂ adj₃ x₂ x₃ τ₂ h₂)
  (hw₀ : h₁ = h₀ + 2) (hw₁ : h₂ = h₁ + 2)
  (hsq₀ : τ₀ ≫ τ₀ = 0) (hsq₁ : τ₁ ≫ τ₁ = 0) (hsq₂ : τ₂ ≫ τ₂ = 0)
  (hb₀ : E₀ ◁ τ₁ ≫ ((α_ E₀ E₁ E₂).inv ≫ τ₀ ▷ E₂ ≫ (α_ E₀ E₁ E₂).hom) ≫ E₀ ◁ τ₁ =
    ((α_ E₀ E₁ E₂).inv ≫ τ₀ ▷ E₂ ≫ (α_ E₀ E₁ E₂).hom) ≫ E₀ ◁ τ₁ ≫
      ((α_ E₀ E₁ E₂).inv ≫ τ₀ ▷ E₂ ≫ (α_ E₀ E₁ E₂).hom))
  (hb₁ : E₁ ◁ τ₂ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ₁ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂ =
    ((α_ E₁ E₂ E₃).inv ≫ τ₁ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂ ≫
      ((α_ E₁ E₂ E₃).inv ≫ τ₁ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom))

include K U hw₀ hw₁ hsq₀ hsq₁ hsq₂ hb₀ hb₁ in
/-- Brundan §5 (the mate identity behind the cyclicity of the crossing): the partial mate, along
the left adjunctions, of the right mate of the upward crossing is the leftward crossing `σ'`. -/
theorem mate_rightMate_eq_sigL :
    mateEquiv (L.leftAdjunction U hw₁ hsq₁ hsq₂ hb₁) (K.leftAdjunction L hw₀ hsq₀ hsq₁ hb₀)
      (conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ₁) = L.sigL := by
  let A₁ := K.leftAdjunction L hw₀ hsq₀ hsq₁ hb₀
  let A₂ := L.leftAdjunction U hw₁ hsq₁ hsq₂ hb₁
  have hm : mateEquiv (HOp.adjunction A₁) (HOp.adjunction A₂) L.mirror.sigL = L.mirrorTau :=
    K.mirror.mate_sigL_of_units_counits L.mirror U.mirror hw₀ hw₁
      (K.mirror_square hsq₀) (L.mirror_square hsq₁) (U.mirror_square hsq₂)
      (K.mirror_braid L hb₀) (L.mirror_braid U hb₁)
      (HOp.adjunction A₁) (HOp.adjunction A₂)
      (by exact L.mirror_cupL.symm) (by exact U.mirror_cupL.symm)
      (by exact K.mirror_capL.symm) (by exact L.mirror_capL.symm)
  rw [HOp.mateEquiv_reflect, L.mirror_sigL] at hm
  change (mateEquiv A₂ A₁).symm L.sigL =
    conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ₁ at hm
  rw [← hm, Equiv.apply_symm_apply]

include K U hw₀ hw₁ hsq₀ hsq₁ hsq₂ hb₀ hb₁ in
/-- The twisted rightward crossing is minus the leftward crossing `σ'` of the original data. -/
theorem twist_sig :
    RightwardCrossing.sigma (K.leftAdjunction L hw₀ hsq₀ hsq₁ hb₀).unit
      (-conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ₁)
      (L.leftAdjunction U hw₁ hsq₁ hsq₂ hb₁).counit = -L.sigL := by
  rw [sigma_neg, sigma_eq_mate (L.leftAdjunction U hw₁ hsq₁ hsq₂ hb₁)
    (K.leftAdjunction L hw₀ hsq₀ hsq₁ hb₀),
    K.mate_rightMate_eq_sigL L U hw₀ hw₁ hsq₀ hsq₁ hsq₂ hb₀ hb₁]

/-- **The twist of Rouquier's data** (KL III v1 §3.3.2, `ω̃`; Brundan, Definition 1.1 at `-h`):
from data at the weights `h - 2`, `h`, `h + 2`, data at the weight `-h` in the same bicategory,
with upward 1-morphisms `R₂`, `R₁` (Brundan's `F`), the left adjunctions `R₂ ⊣ E₂`, `R₁ ⊣ E₁`
of Brundan's Theorem 4.3, the downward dots and minus the right mate of the crossing. -/
def twist (h' : ℤ) (hw : h' = -h₁) :
    RouqLoc (L.leftAdjunction U hw₁ hsq₁ hsq₂ hb₁) (K.leftAdjunction L hw₀ hsq₀ hsq₁ hb₀)
      L.dotD₂ L.dotD₁ (-conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ₁) h' where
  slide_left := by
    have hs := L.mirror.slide_right
    change conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ₁ ≫ L.dotD₂ ▷ R₁ -
      R₂ ◁ L.dotD₁ ≫ conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ₁ = 𝟙 _ at hs
    rw [Preadditive.comp_neg, Preadditive.neg_comp, ← hs]
    abel
  slide_right := by
    have hs := L.mirror.slide_left
    change L.dotD₂ ▷ R₁ ≫ conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ₁ -
      conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ₁ ≫ R₂ ◁ L.dotD₁ = 𝟙 _ at hs
    rw [Preadditive.comp_neg, Preadditive.neg_comp, ← hs]
    abel
  invPos hh :=
    (L.twistInvPos (by omega)).congr
      (K.twist_sig L U hw₀ hw₁ hsq₀ hsq₁ hsq₂ hb₀ hb₁).symm
      (funext fun n => cap_powComp_slide (L.capL_dot U hw₁ hsq₁ hsq₂ hb₁) n)
      (by rw [hw])
  invNeg hh :=
    (L.twistInvNeg (by omega)).congr
      (K.twist_sig L U hw₀ hw₁ hsq₀ hsq₁ hsq₂ hb₀ hb₁).symm
      (funext fun n => cup_powComp_slide (K.cupL_dot L hw₀ hsq₀ hsq₁ hb₀) n)
      (by rw [hw, neg_neg])

end RouqLoc

/-! ## The twist of a Rouquier family -/

namespace RouqFamily

open QuantumGroup UDot

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [AdditiveWhiskering B]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} (S : RouqFamily (B := B) RD)

/-- An edge `x → y` of colour `i` gives the edge `-y → -x`. -/
theorem neg_reg (i : I) {x y : X} (h : x + RD.iX i = y) : -y + RD.iX i = -x := by
  rw [← h]; abel

/-- **The twist of a Rouquier family** (KL III v1 §3.3.2, `ω̃`): objects `x ↦ obj (-x)`, `E' = F`,
`F' = E`, the left adjunctions `F ⊣ E` (Brundan Theorem 4.3), the downward dots (right mates of
the dots, equal to `dotDn` by `twist_dot`) and minus the right mates of the upward crossings. The
local Rouquier data are `RouqLoc.twist`. -/
def twist : RouqFamily (B := B) RD where
  obj x := S.obj (-x)
  E i _ _ h := S.F i (neg_reg i h)
  F i _ _ h := S.E i (neg_reg i h)
  adj i _ _ h := S.adjL i (neg_reg i h)
  dot i _ _ h := conjugateEquiv (S.adj i (neg_reg i h)) (S.adj i (neg_reg i h))
    (S.dot i (neg_reg i h))
  cross i j _ _ _ _ h₁ h₂ h₃ h₄ :=
    -conjugateEquiv ((S.adj i (neg_reg i h₂)).comp (S.adj j (neg_reg j h₁)))
      ((S.adj j (neg_reg j h₄)).comp (S.adj i (neg_reg i h₃)))
      (S.cross i j (neg_reg j h₄) (neg_reg i h₃) (neg_reg i h₂) (neg_reg j h₁))
  square i _ _ _ h₁ h₂ :=
    RouqSl2Generic.neg_rightMate_square _ _ _ (S.square i (neg_reg i h₂) (neg_reg i h₁))
  braid i _ _ _ _ h₁ h₂ h₃ :=
    RouqSl2Generic.neg_rightMate_braid _ _ _ _ _
      (S.braid i (neg_reg i h₃) (neg_reg i h₂) (neg_reg i h₁))
  loc i a b c h₁ h₂ := by
    rw [S.adjL_eq i (neg_reg i h₂) (neg_reg i h₁) (rfl : -a + RD.iX i = -a + RD.iX i),
      S.adjL_eq i (sub_add_cancel (-c) (RD.iX i)) (neg_reg i h₂) (neg_reg i h₁)]
    exact RouqLoc.twist (S.loc i (sub_add_cancel (-c) (RD.iX i)) (neg_reg i h₂))
      (S.loc i (neg_reg i h₂) (neg_reg i h₁)) (S.loc i (neg_reg i h₁) rfl)
      (pair_step i (neg_reg i h₂)) (pair_step i (neg_reg i h₁))
      (S.square i _ (neg_reg i h₂)) (S.square i (neg_reg i h₂) (neg_reg i h₁))
      (S.square i (neg_reg i h₁) rfl)
      (S.braid i _ (neg_reg i h₂) (neg_reg i h₁)) (S.braid i (neg_reg i h₂) (neg_reg i h₁) rfl)
      _ (by rw [map_neg, neg_neg])

@[simp] theorem twist_obj (x : X) : S.twist.obj x = S.obj (-x) := rfl

@[simp] theorem twist_E (i : I) {x y : X} (h : x + RD.iX i = y) :
    S.twist.E i h = S.F i (neg_reg i h) := rfl

@[simp] theorem twist_F (i : I) {x y : X} (h : x + RD.iX i = y) :
    S.twist.F i h = S.E i (neg_reg i h) := rfl

/-- The adjunction of the twist is the left adjunction `F ⊣ E` of Brundan's Theorem 4.3. -/
theorem twist_adj (i : I) {x y : X} (h : x + RD.iX i = y) :
    S.twist.adj i h = S.adjL i (neg_reg i h) := rfl

/-- The dot of the twist is the downward dot `dotDn`. -/
theorem twist_dot (i : I) {x y : X} (h : x + RD.iX i = y) :
    S.twist.dot i h = S.dotDn i (neg_reg i h) :=
  (S.dotDn_eq_rightMate i (neg_reg i h)).symm

/-- The crossing of the twist is minus the right mate of the upward crossing. -/
theorem twist_cross (i j : I) {a b c d : X} (h₁ : a + RD.iX j = b)
    (h₂ : b + RD.iX i = d) (h₃ : a + RD.iX i = c) (h₄ : c + RD.iX j = d) :
    S.twist.cross i j h₁ h₂ h₃ h₄ =
      -conjugateEquiv ((S.adj i (neg_reg i h₂)).comp (S.adj j (neg_reg j h₁)))
        ((S.adj j (neg_reg j h₄)).comp (S.adj i (neg_reg i h₃)))
        (S.cross i j (neg_reg j h₄) (neg_reg i h₃) (neg_reg i h₂) (neg_reg j h₁)) := rfl

end RouqFamily

end Categorification.TwoRep
