/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Coop
import Categorification.TwoRep.WordBounded

/-!
# The duality `K ↦ Kᶜᵒᵒᵖ` for strong 2-representations of `sl₂`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Definition 1.2 (`def_Qstrong`) and §3.

Let `K` be a strong 2-representation of `sl₂` (`StrongSl2 k B`). Its *dual* `D(K)` lives in the
bidual bicategory `Bᶜᵒᵒᵖ` (`Coop B`: 1-morphisms and 2-morphisms reversed, grading shift inverted,
so that `Hom'^d(X, Y) = Hom^d(Y, X)`), with the weights negated:

* the object of weight `μ` of `D(K)` is the object of weight `-μ` of `K`
  (`dual.obj r = obj (-r)`, `dual.n₀ = -n₀`);
* `E'1_μ : μ → μ + 2` is the 1-morphism `E1_{-μ-2} : -μ-2 → -μ` of `K`
  (`dual.E r = op (E (-(r + 1)))`), and `1_μF'` is `1_{-μ-2}F` (`dual.F r = op (F (-(r + 1)))`):
  an adjunction `u ⊣ v` of `B` is an adjunction `op u ⊣ op v` of `Bᶜᵒᵒᵖ` (`Coop.adjunction`), and
  the shift in `1_nF = (E1_n)_R⟨-n-1⟩` is inverted twice;
* condition (3) at the weight `μ ≥ 0` of `D(K)` is condition (3) at the weight `-μ ≤ 0` of `K`
  (the multiset of shifts of `⊕_{[μ]}` is symmetric);
* the dot is the dot, and the crossing is **minus** the crossing: horizontal composition is
  reversed, so the two strands of `E'E'` are exchanged, and vertical composition is reversed; the
  dot slide relation `r·1 = τ x₁ - x₂ τ` of `eq_nil_dotslide` then holds for `-τ` with the same
  scalar `r`.

So `D(K)` satisfies Definition 1.2 (for `sl₂`) whenever `K` does: `StrongSl2.dual`. The adjoint
induction hypothesis (3.2) at the weight `μ` of `D(K)` is (3.2) at the weight `-μ-2` of `K`
(`StrongSl2.dual_adjHyp_iff`). Hence every statement about (3.2) proved for all strong
2-representations at the weights `n > 0` yields the same statement at the weights `n < -2`, by
applying it to the dual.

## Main declarations

* `StrongSl2.Ec`, `Fc`, `dotc`, `crossc`: the data of `S` with a free index for the target of
  `E` (`E1_n : obj s ⟶ obj t` for `t = s + 1`), and the relations in this form;
* `StrongSl2.braid_conj`: the braid relation on `(E E) E`;
* `StrongSl2.dual : StrongSl2 k (Coop B)`;
* `StrongSl2.dual_wt`, `isZero_dual_id_iff`, `finrank_dual_id_shift`;
* `StrongSl2.dual_adjHyp_iff`, `StrongSl2.dual_adjHyp_neg_iff`, `StrongSl2.adjHyp_of_dual_gt`;
* `StrongSl2.word_of_dual_word`: the words in `E`, `F` of `D(K)` are words of `K`, read backwards;
* `StrongSl2.BBw.dual`: the hypothesis (BB_w) passes from `K` to `D(K)`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module Opposite
open KrullSchmidtCat (HomFinite)
open Pretriangulated.Opposite

universe w v u

/-! ## Shifted whiskering is additive -/

section WhiskerNeg

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] {a b c : B}

theorem shWhiskerLeft_neg (f : a ⟶ b) {g h : b ⟶ c} {n : ℤ} (θ : ShiftedHom g h n) :
    shWhiskerLeft f (-θ) = -shWhiskerLeft f θ := by
  unfold shWhiskerLeft ShiftedHom.map
  rw [Functor.map_neg, Preadditive.neg_comp]
  rfl

theorem shWhiskerRight_neg {f g : a ⟶ b} {n : ℤ} (η : ShiftedHom f g n) (h : b ⟶ c) :
    shWhiskerRight (-η) h = -shWhiskerRight η h := by
  unfold shWhiskerRight ShiftedHom.map
  rw [Functor.map_neg, Preadditive.neg_comp]
  rfl

end WhiskerNeg

theorem shiftedHom_neg_comp_neg {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] {X Y Z : C} {a b c : ℤ} (f : ShiftedHom X Y a)
    (g : ShiftedHom Y Z b) (h : b + a = c) : (-f).comp (-g) h = f.comp g h := by
  rw [ShiftedHom.neg_comp, ShiftedHom.comp_neg, neg_neg]

section NegSlide

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] {X : C} {a b : ℤ}

theorem shiftedHom_comp_neg_sub_neg_comp (x y : ShiftedHom X X a) (t : ShiftedHom X X b)
    (h₁ : b + a = 0) (h₂ : a + b = 0) :
    x.comp (-t) h₁ - (-t).comp y h₂ = t.comp y h₂ - x.comp t h₁ := by
  rw [ShiftedHom.comp_neg, ShiftedHom.neg_comp]
  abel

theorem shiftedHom_neg_comp_sub_comp_neg (x y : ShiftedHom X X a) (t : ShiftedHom X X b)
    (h₁ : b + a = 0) (h₂ : a + b = 0) :
    (-t).comp x h₂ - y.comp (-t) h₁ = y.comp t h₁ - t.comp x h₂ := by
  rw [ShiftedHom.comp_neg, ShiftedHom.neg_comp]
  abel

theorem shiftedHom_neg_comp_neg_comp_neg (A B : ShiftedHom X X a) {c d : ℤ} (h₁ : a + a = c)
    (h₂ : a + c = d) : ((-A).comp (-B) h₁).comp (-A) h₂ = -((A.comp B h₁).comp A h₂) := by
  simp only [ShiftedHom.neg_comp, ShiftedHom.comp_neg, neg_neg]

end NegSlide

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]

namespace StrongSl2

variable (S : StrongSl2 k B)

/-! ## The data of `S` with a free index for the target of `E` -/

/-- `E 1_n : obj s ⟶ obj t` for `t = s + 1` (the transport of `S.E s`). -/
def Ec (s t : ℤ) (h : s + 1 = t) : S.obj s ⟶ S.obj t := by
  subst h; exact S.E s

/-- `1_n F : obj t ⟶ obj s` for `t = s + 1` (the transport of `S.F s`). -/
def Fc (s t : ℤ) (h : s + 1 = t) : S.obj t ⟶ S.obj s := by
  subst h; exact S.F s

@[simp] theorem Ec_rfl (s : ℤ) : S.Ec s (s + 1) rfl = S.E s := rfl

@[simp] theorem Fc_rfl (s : ℤ) : S.Fc s (s + 1) rfl = S.F s := rfl

/-- `E 1_n ⊣ 1_n F ⟨n+1⟩`. -/
def adjc (s t : ℤ) (h : s + 1 = t) (m : ℤ) (hm : m = S.n₀ + 2 * s + 1) :
    S.Ec s t h ⊣ (S.Fc s t h)⟦m⟧ := by
  subst h hm; exact S.adj s

theorem exists_leftAdjc (s t : ℤ) (h : s + 1 = t) :
    ∃ L : S.obj t ⟶ S.obj s, Nonempty (L ⊣ S.Ec s t h) := by
  subst h; exact S.exists_leftAdj s

/-- Condition (3) at a weight `m = n₀ + 2 s ≥ 0`. -/
theorem EFc (s' s t : ℤ) (h' : s' + 1 = s) (h : s + 1 = t) (m : ℕ) (hw : 0 ≤ S.n₀ + 2 * s)
    (hm : m = (S.n₀ + 2 * s).toNat) :
    Nonempty (S.Fc s' s h' ≫ S.Ec s' s h' ≅
      (S.Ec s t h ≫ S.Fc s t h) ⊞ qsum 1 m (𝟙 (S.obj s))) := by
  subst h' h hm; exact S.EF s' hw

/-- Condition (3) at a weight `m = n₀ + 2 s ≤ 0`. -/
theorem FEc (s' s t : ℤ) (h' : s' + 1 = s) (h : s + 1 = t) (m : ℕ) (hw : S.n₀ + 2 * s ≤ 0)
    (hm : m = (-(S.n₀ + 2 * s)).toNat) :
    Nonempty (S.Ec s t h ≫ S.Fc s t h ≅
      (S.Fc s' s h' ≫ S.Ec s' s h') ⊞ qsum 1 m (𝟙 (S.obj s))) := by
  subst h' h hm; exact S.FE s' hw

/-- The dot on `E 1_n`. -/
def dotc (s t : ℤ) (h : s + 1 = t) : ShiftedHom (S.Ec s t h) (S.Ec s t h) (2 : ℤ) := by
  subst h; exact S.dot s

/-- The crossing on `E E 1_n`. -/
def crossc (s' s t : ℤ) (h' : s' + 1 = s) (h : s + 1 = t) :
    ShiftedHom (S.Ec s' s h' ≫ S.Ec s t h) (S.Ec s' s h' ≫ S.Ec s t h) (-2 : ℤ) := by
  subst h' h; exact S.cross s'

theorem cross_sqc (s' s t : ℤ) (h' : s' + 1 = s) (h : s + 1 = t) :
    (S.crossc s' s t h' h).comp (S.crossc s' s t h' h) (by norm_num : (-2 : ℤ) + -2 = -4) = 0 := by
  subst h' h; exact S.cross_sq s'

theorem dot_slide_leftc (s' s t : ℤ) (h' : s' + 1 = s) (h : s + 1 = t) :
    ShiftedHom.mk₀ (0 : ℤ) rfl ((S.rQ : k) • 𝟙 (S.Ec s' s h' ≫ S.Ec s t h)) =
      (shWhiskerLeft (S.Ec s' s h') (S.dotc s t h)).comp (S.crossc s' s t h' h)
          (by norm_num : (-2 : ℤ) + 2 = 0) -
        (S.crossc s' s t h' h).comp (shWhiskerRight (S.dotc s' s h') (S.Ec s t h))
          (by norm_num : (2 : ℤ) + -2 = 0) := by
  subst h' h; exact S.dot_slide_left s'

theorem dot_slide_rightc (s' s t : ℤ) (h' : s' + 1 = s) (h : s + 1 = t) :
    ShiftedHom.mk₀ (0 : ℤ) rfl ((S.rQ : k) • 𝟙 (S.Ec s' s h' ≫ S.Ec s t h)) =
      (S.crossc s' s t h' h).comp (shWhiskerLeft (S.Ec s' s h') (S.dotc s t h))
          (by norm_num : (2 : ℤ) + -2 = 0) -
        (shWhiskerRight (S.dotc s' s h') (S.Ec s t h)).comp (S.crossc s' s t h' h)
          (by norm_num : (-2 : ℤ) + 2 = 0) := by
  subst h' h; exact S.dot_slide_right s'

/-- **The braid relation on `(E E) E 1_n`**: with `V` the crossing of the two right strands
(`cross r ▷ E`) and `P` the crossing of the two left strands, conjugated by the associator,
`V P V = P V P`. (The field `StrongSl2.braid` is this relation on `E (E E) 1_n`.) -/
theorem braid_conj (r : ℤ) :
    (shWhiskerRight (S.cross r) (S.E (r + 1 + 1))).comp
        ((shConj (α_ (S.E r) (S.E (r + 1)) (S.E (r + 1 + 1))).symm
            (shWhiskerLeft (S.E r) (S.cross (r + 1)))).comp
          (shWhiskerRight (S.cross r) (S.E (r + 1 + 1))) (by norm_num : (-2 : ℤ) + -2 = -4))
        (by norm_num : (-4 : ℤ) + -2 = -6) =
      (shConj (α_ (S.E r) (S.E (r + 1)) (S.E (r + 1 + 1))).symm
          (shWhiskerLeft (S.E r) (S.cross (r + 1)))).comp
        ((shWhiskerRight (S.cross r) (S.E (r + 1 + 1))).comp
          (shConj (α_ (S.E r) (S.E (r + 1)) (S.E (r + 1 + 1))).symm
            (shWhiskerLeft (S.E r) (S.cross (r + 1)))) (by norm_num : (-2 : ℤ) + -2 = -4))
        (by norm_num : (-4 : ℤ) + -2 = -6) := by
  have h : ((shWhiskerLeft (S.E r) (S.cross (r + 1))).comp
        (shConj (α_ (S.E r) (S.E (r + 1)) (S.E (r + 1 + 1)))
          (shWhiskerRight (S.cross r) (S.E (r + 1 + 1))))
        (by norm_num : (-2 : ℤ) + -2 = -4)).comp
        (shWhiskerLeft (S.E r) (S.cross (r + 1))) (by norm_num : (-2 : ℤ) + -4 = -6) =
      ((shConj (α_ (S.E r) (S.E (r + 1)) (S.E (r + 1 + 1)))
          (shWhiskerRight (S.cross r) (S.E (r + 1 + 1)))).comp
        (shWhiskerLeft (S.E r) (S.cross (r + 1))) (by norm_num : (-2 : ℤ) + -2 = -4)).comp
        (shConj (α_ (S.E r) (S.E (r + 1)) (S.E (r + 1 + 1)))
          (shWhiskerRight (S.cross r) (S.E (r + 1 + 1))))
        (by norm_num : (-2 : ℤ) + -4 = -6) := S.braid r
  have h' := congrArg (shConj (α_ (S.E r) (S.E (r + 1)) (S.E (r + 1 + 1))).symm) h
  rw [shConj_comp, shConj_comp, shConj_comp, shConj_comp, shConj_symm_shConj] at h'
  exact ((ShiftedHom.comp_assoc _ _ _ (by norm_num : (-2 : ℤ) + -2 = -4)
      (by norm_num : (-2 : ℤ) + -2 = -4) (by norm_num : (-2 : ℤ) + -2 + -2 = -6)).symm.trans
    h'.symm).trans (ShiftedHom.comp_assoc _ _ _ (by norm_num : (-2 : ℤ) + -2 = -4)
      (by norm_num : (-2 : ℤ) + -2 = -4) (by norm_num : (-2 : ℤ) + -2 + -2 = -6))

theorem braid_conjc (s'' s' s t : ℤ) (h'' : s'' + 1 = s') (h' : s' + 1 = s) (h : s + 1 = t) :
    (shWhiskerRight (S.crossc s'' s' s h'' h') (S.Ec s t h)).comp
        ((shConj (α_ (S.Ec s'' s' h'') (S.Ec s' s h') (S.Ec s t h)).symm
            (shWhiskerLeft (S.Ec s'' s' h'') (S.crossc s' s t h' h))).comp
          (shWhiskerRight (S.crossc s'' s' s h'' h') (S.Ec s t h))
          (by norm_num : (-2 : ℤ) + -2 = -4))
        (by norm_num : (-4 : ℤ) + -2 = -6) =
      (shConj (α_ (S.Ec s'' s' h'') (S.Ec s' s h') (S.Ec s t h)).symm
          (shWhiskerLeft (S.Ec s'' s' h'') (S.crossc s' s t h' h))).comp
        ((shWhiskerRight (S.crossc s'' s' s h'' h') (S.Ec s t h)).comp
          (shConj (α_ (S.Ec s'' s' h'') (S.Ec s' s h') (S.Ec s t h)).symm
            (shWhiskerLeft (S.Ec s'' s' h'') (S.crossc s' s t h' h)))
          (by norm_num : (-2 : ℤ) + -2 = -4))
        (by norm_num : (-4 : ℤ) + -2 = -6) := by
  subst h'' h' h; exact S.braid_conj s''

/-- The adjoint induction hypothesis (3.2) in terms of `Ec`, `Fc`. -/
theorem adjHyp_iff_c (s t : ℤ) (h : s + 1 = t) (m : ℤ) (hm : m = -(S.wt s + 1)) :
    S.AdjHyp s ↔ Nonempty ((S.Fc s t h)⟦m⟧ ⊣ S.Ec s t h) := by
  subst h hm; rfl

/-! ## The data of the dual -/

/-- `E'1_μ`: the 1-morphism `E 1_{-μ-2}` of `K`, as a 1-morphism `μ → μ + 2` of the bidual. -/
def dualE (r : ℤ) : Coop.toCoop (S.obj (-r)) ⟶ Coop.toCoop (S.obj (-(r + 1))) :=
  Coop.op1 (S.Ec (-(r + 1)) (-r) (by omega))

/-- `1_μF'`: the 1-morphism `1_{-μ-2}F` of `K`, as a 1-morphism `μ + 2 → μ` of the bidual. -/
def dualF (r : ℤ) : Coop.toCoop (S.obj (-(r + 1))) ⟶ Coop.toCoop (S.obj (-r)) :=
  Coop.op1 (S.Fc (-(r + 1)) (-r) (by omega))

/-- The dot of the dual is the dot. -/
def dualDot (r : ℤ) : ShiftedHom (S.dualE r) (S.dualE r) (2 : ℤ) :=
  Coop.shOp (S.dotc (-(r + 1)) (-r) (by omega))

/-- The crossing of the dual is **minus** the crossing. -/
def dualCross (r : ℤ) :
    ShiftedHom (S.dualE r ≫ S.dualE (r + 1)) (S.dualE r ≫ S.dualE (r + 1)) (-2 : ℤ) :=
  -Coop.shOp (S.crossc (-(r + 1 + 1)) (-(r + 1)) (-r) (by omega) (by omega))

theorem dualCross_sq (r : ℤ) :
    (S.dualCross r).comp (S.dualCross r) (by norm_num : (-2 : ℤ) + -2 = -4) = 0 := by
  have h := congrArg Coop.shOp (S.cross_sqc (-(r + 1 + 1)) (-(r + 1)) (-r) (by omega) (by omega))
  rw [Coop.shOp_comp _ _ _ (by norm_num : (-2 : ℤ) + -2 = -4), Coop.shOp_zero] at h
  exact (shiftedHom_neg_comp_neg _ _ _).trans h

theorem dual_dot_slide_left (r : ℤ) :
    ShiftedHom.mk₀ (0 : ℤ) rfl ((S.rQ : k) • 𝟙 (S.dualE r ≫ S.dualE (r + 1))) =
      (shWhiskerLeft (S.dualE r) (S.dualDot (r + 1))).comp (S.dualCross r)
          (by norm_num : (-2 : ℤ) + 2 = 0) -
        (S.dualCross r).comp (shWhiskerRight (S.dualDot r) (S.dualE (r + 1)))
          (by norm_num : (2 : ℤ) + -2 = 0) := by
  have h := congrArg Coop.shOp
    (S.dot_slide_leftc (-(r + 1 + 1)) (-(r + 1)) (-r) (by omega) (by omega))
  rw [Coop.shOp_mk₀, Coop.shOp_sub, Coop.shOp_comp _ _ _ (by norm_num : (2 : ℤ) + -2 = 0),
    Coop.shOp_comp _ _ _ (by norm_num : (-2 : ℤ) + 2 = 0), Coop.shOp_shWhiskerLeft,
    Coop.shOp_shWhiskerRight] at h
  exact h.trans (shiftedHom_comp_neg_sub_neg_comp _ _ _ _ _).symm

theorem dual_dot_slide_right (r : ℤ) :
    ShiftedHom.mk₀ (0 : ℤ) rfl ((S.rQ : k) • 𝟙 (S.dualE r ≫ S.dualE (r + 1))) =
      (S.dualCross r).comp (shWhiskerLeft (S.dualE r) (S.dualDot (r + 1)))
          (by norm_num : (2 : ℤ) + -2 = 0) -
        (shWhiskerRight (S.dualDot r) (S.dualE (r + 1))).comp (S.dualCross r)
          (by norm_num : (-2 : ℤ) + 2 = 0) := by
  have h := congrArg Coop.shOp
    (S.dot_slide_rightc (-(r + 1 + 1)) (-(r + 1)) (-r) (by omega) (by omega))
  rw [Coop.shOp_mk₀, Coop.shOp_sub, Coop.shOp_comp _ _ _ (by norm_num : (-2 : ℤ) + 2 = 0),
    Coop.shOp_comp _ _ _ (by norm_num : (2 : ℤ) + -2 = 0), Coop.shOp_shWhiskerLeft,
    Coop.shOp_shWhiskerRight] at h
  exact h.trans (shiftedHom_neg_comp_sub_comp_neg _ _ _ _ _).symm

theorem dual_braid (r : ℤ) :
    let τ₁ : ShiftedHom (S.dualE r ≫ S.dualE (r + 1) ≫ S.dualE (r + 1 + 1))
        (S.dualE r ≫ S.dualE (r + 1) ≫ S.dualE (r + 1 + 1)) (-2 : ℤ) :=
      shWhiskerLeft (S.dualE r) (S.dualCross (r + 1))
    let τ₂ : ShiftedHom (S.dualE r ≫ S.dualE (r + 1) ≫ S.dualE (r + 1 + 1))
        (S.dualE r ≫ S.dualE (r + 1) ≫ S.dualE (r + 1 + 1)) (-2 : ℤ) :=
      (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ (S.dualE r) (S.dualE (r + 1)) (S.dualE (r + 1 + 1))).inv).comp
        ((shWhiskerRight (S.dualCross r) (S.dualE (r + 1 + 1))).comp
          (ShiftedHom.mk₀ (0 : ℤ) rfl (α_ (S.dualE r) (S.dualE (r + 1)) (S.dualE (r + 1 + 1))).hom)
          (by norm_num : (0 : ℤ) + -2 = -2)) (by norm_num : (-2 : ℤ) + 0 = -2)
    (τ₁.comp τ₂ (by norm_num : (-2 : ℤ) + -2 = -4)).comp τ₁ (by norm_num : (-2 : ℤ) + -4 = -6) =
      (τ₂.comp τ₁ (by norm_num : (-2 : ℤ) + -2 = -4)).comp τ₂ (by norm_num : (-2 : ℤ) + -4 = -6) := by
  intro τ₁ τ₂
  have hK := congrArg Coop.shOp (S.braid_conjc (-(r + 1 + 1 + 1)) (-(r + 1 + 1)) (-(r + 1)) (-r)
    (by omega) (by omega) (by omega))
  rw [Coop.shOp_comp _ _ _ (by norm_num : (-2 : ℤ) + -4 = -6),
    Coop.shOp_comp _ _ _ (by norm_num : (-2 : ℤ) + -2 = -4),
    Coop.shOp_comp _ _ _ (by norm_num : (-2 : ℤ) + -4 = -6),
    Coop.shOp_comp _ _ _ (by norm_num : (-2 : ℤ) + -2 = -4),
    Coop.shOp_shConj_symm, Coop.shOp_shWhiskerRight, Coop.shOp_shWhiskerLeft] at hK
  have e₁ : τ₁ = -shWhiskerLeft (Coop.op1 (S.Ec (-(r + 1)) (-r) (by omega)))
      (Coop.shOp (S.crossc (-(r + 1 + 1 + 1)) (-(r + 1 + 1)) (-(r + 1)) (by omega) (by omega))) :=
    shWhiskerLeft_neg _ _
  have e₂ : τ₂ = -shConj (α_ (S.Ec (-(r + 1 + 1 + 1)) (-(r + 1 + 1)) (by omega))
        (S.Ec (-(r + 1 + 1)) (-(r + 1)) (by omega)) (S.Ec (-(r + 1)) (-r) (by omega))).op
      (shWhiskerRight (Coop.shOp (S.crossc (-(r + 1 + 1)) (-(r + 1)) (-r) (by omega) (by omega)))
        (Coop.op1 (S.Ec (-(r + 1 + 1 + 1)) (-(r + 1 + 1)) (by omega)))) :=
    (congrArg (shConj (α_ (S.dualE r) (S.dualE (r + 1)) (S.dualE (r + 1 + 1))))
      (shWhiskerRight_neg _ _)).trans (shConj_neg _ _)
  rw [e₁, e₂]
  exact (shiftedHom_neg_comp_neg_comp_neg _ _ _ _).trans
    ((congrArg Neg.neg hK).trans (shiftedHom_neg_comp_neg_comp_neg _ _ _ _).symm)

/-! ## The dual strong 2-representation -/

variable [GradedBicategory.IsLinear B k]

/-- **The dual `D(K)` of a strong 2-representation of `sl₂`** (CL Definition 1.2 is invariant
under `K ↦ Kᶜᵒᵒᵖ`): the same data in the bidual bicategory, with the weights negated,
`E'1_μ = E1_{-μ-2}`, `1_μF' = 1_{-μ-2}F`, the same dot and scalar `r`, and the crossing negated.
See the module docstring. -/
def dual : StrongSl2 k (Coop B) where
  n₀ := -S.n₀
  obj r := Coop.toCoop (S.obj (-r))
  E := S.dualE
  F := S.dualF
  adj r := Coop.adjunction
    (S.adjc (-(r + 1)) (-r) (by omega) (-(-S.n₀ + 2 * r + 1)) (by ring))
  exists_leftAdj r := by
    obtain ⟨L, ⟨adj⟩⟩ := S.exists_leftAdjc (-(r + 1)) (-r) (by omega)
    exact ⟨Coop.op1 L, ⟨Coop.adjunction adj⟩⟩
  integrable := by
    obtain ⟨N, hN⟩ := S.integrable
    exact ⟨N, fun r hr => (Coop.isZero_op1_iff _).2 (hN (-r) (by rwa [abs_neg]))⟩
  hom_neg r l hl := (Coop.finrank_hom_shift k _ _ l).trans (S.hom_neg (-r) l hl)
  hom_zero r h :=
    (Coop.finrank_hom k _ _).trans (S.hom_zero (-r) fun hz => h ((Coop.isZero_op1_iff _).2 hz))
  EF r hr := by
    obtain ⟨e⟩ := S.FEc (-(r + 1 + 1)) (-(r + 1)) (-r) (by omega) (by omega)
      (-S.n₀ + 2 * (r + 1)).toNat (by omega) (by congr 1; ring)
    obtain ⟨q⟩ := nonempty_qsum_op_iso 1 (-S.n₀ + 2 * (r + 1)).toNat (𝟙 (S.obj (-(r + 1))))
    exact ⟨(e.symm.op ≪≫ biprod.opIso _ _ ≪≫ biprod.mapIso (Iso.refl _) q.symm :)⟩
  FE r hr := by
    obtain ⟨e⟩ := S.EFc (-(r + 1 + 1)) (-(r + 1)) (-r) (by omega) (by omega)
      (-(-S.n₀ + 2 * (r + 1))).toNat (by omega) (by congr 1; ring)
    obtain ⟨q⟩ := nonempty_qsum_op_iso 1 (-(-S.n₀ + 2 * (r + 1))).toNat (𝟙 (S.obj (-(r + 1))))
    exact ⟨(e.symm.op ≪≫ biprod.opIso _ _ ≪≫ biprod.mapIso (Iso.refl _) q.symm :)⟩
  rQ := S.rQ
  dot := S.dualDot
  cross := S.dualCross
  cross_sq := S.dualCross_sq
  dot_slide_left := S.dual_dot_slide_left
  dot_slide_right := S.dual_dot_slide_right
  braid := S.dual_braid

@[simp] theorem dual_n₀ : S.dual.n₀ = -S.n₀ := rfl

@[simp] theorem dual_obj (r : ℤ) : S.dual.obj r = Coop.toCoop (S.obj (-r)) := rfl

theorem dual_E (r : ℤ) : S.dual.E r = Coop.op1 (S.Ec (-(r + 1)) (-r) (by omega)) := rfl

theorem dual_F (r : ℤ) : S.dual.F r = Coop.op1 (S.Fc (-(r + 1)) (-r) (by omega)) := rfl

@[simp] theorem dual_rQ : S.dual.rQ = S.rQ := rfl

/-- The weight of the object `r` of the dual is minus the weight of the object `-r`. -/
theorem dual_wt (r : ℤ) : S.dual.wt r = -S.wt (-r) := by
  simp only [wt, dual_n₀]; ring

/-- `E'1_μ = E1_{-μ-2}`: the weight `μ` of the source of `dual.E r` and the weight `n` of the
source of `E (-(r + 1))` satisfy `μ = -n - 2`. -/
theorem dual_wt_eq (r : ℤ) : S.dual.wt r = -S.wt (-(r + 1)) - 2 := by
  simp only [wt, dual_n₀]; ring

/-- An object of the dual is zero iff the corresponding object is zero. -/
theorem isZero_dual_id_iff (r : ℤ) : IsZero (𝟙 (S.dual.obj r)) ↔ IsZero (𝟙 (S.obj (-r))) :=
  Coop.isZero_op1_iff _

/-- The graded endomorphism spaces of the identity 1-morphisms are those of `K`. -/
theorem finrank_dual_id_shift (r l : ℤ) :
    finrank k (𝟙 (S.dual.obj r) ⟶ (𝟙 (S.dual.obj r))⟦l⟧) =
      finrank k (𝟙 (S.obj (-r)) ⟶ (𝟙 (S.obj (-r)))⟦l⟧) :=
  Coop.finrank_hom_shift k _ _ l

/-- **The adjoint induction hypothesis under the duality** (CL (3.2), `eq:ind_hyp`): (3.2) for
`D(K)` at the weight `μ` is (3.2) for `K` at the weight `-μ-2`. -/
theorem dual_adjHyp_iff (r : ℤ) : S.dual.AdjHyp r ↔ S.AdjHyp (-(r + 1)) := by
  rw [S.adjHyp_iff_c (-(r + 1)) (-r) (by omega) (-(-(S.dual.wt r + 1)))
    (by rw [dual_wt]; simp only [wt]; ring)]
  constructor
  · rintro ⟨adj⟩
    exact ⟨Coop.adjunctionUnop adj⟩
  · rintro ⟨adj⟩
    exact ⟨Coop.adjunction adj⟩

/-- (3.2) for `K` at the object `s` is (3.2) for `D(K)` at the object `-(s + 1)`. -/
theorem dual_adjHyp_neg_iff (s : ℤ) : S.dual.AdjHyp (-(s + 1)) ↔ S.AdjHyp s := by
  rw [dual_adjHyp_iff, show -(-(s + 1) + 1) = s by ring]

/-- **Transport along the duality**: a property of (3.2) proved for the dual at the objects of
positive index range gives (3.2) for `K` at the mirror objects. If (3.2) holds for `D(K)` at
every object `r` with `c < r`, then it holds for `K` at every object `s` with `s < -(c + 1)`. -/
theorem adjHyp_of_dual_gt {c : ℤ} (h : ∀ r, c < r → S.dual.AdjHyp r) (s : ℤ)
    (hs : s < -(c + 1)) : S.AdjHyp s :=
  (S.dual_adjHyp_neg_iff s).1 (h _ (by omega))

/-! ## Words and the hypothesis (BB_w) under the duality -/

omit [GradedBicategory.IsLinear B k] in
theorem word_Ec (s t : ℤ) (h : s + 1 = t) : S.Word s t (S.Ec s t h) := by
  subst h; exact .E s

omit [GradedBicategory.IsLinear B k] in
theorem word_Fc (s t : ℤ) (h : s + 1 = t) : S.Word t s (S.Fc s t h) := by
  subst h; exact .F s

/-- A word `μ → ν` of `D(K)` is a word `-ν → -μ` of `K`. -/
theorem word_of_dual_word {r s : ℤ} {X : S.dual.obj r ⟶ S.dual.obj s} (h : S.dual.Word r s X) :
    S.Word (-s) (-r) X.unop := by
  induction h with
  | id r => exact .id (-r)
  | E r => exact S.word_Ec _ _ _
  | F r => exact S.word_Fc _ _ _
  | comp _ _ ihX ihY => exact .comp ihY ihX

/-- **(BB_w) passes to the dual**: if (BB_w) holds for `K`, it holds for `D(K)`
(`Hom'^d(X, Z) = Hom^d(Z, X)`, and words of `D(K)` are words of `K`). -/
theorem BBw.dual {S : StrongSl2 k B} (h : S.BBw) : S.dual.BBw := by
  intro r s X Z hX hZ
  obtain ⟨N, hN⟩ := h (S.word_of_dual_word hZ) (S.word_of_dual_word hX)
  exact ⟨N, fun d hd => (Coop.finrank_hom_shift k X.unop Z.unop d).trans (hN d hd)⟩

end StrongSl2

end Categorification.TwoRep
