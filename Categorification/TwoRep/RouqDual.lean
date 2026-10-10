/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqSl2
import Categorification.TwoRep.Coop

/-!
# The Chevalley involution for Rouquier's data

J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, §2, Theorem 2.3: the
isomorphism `T : U'(g) → U(g)^opp` (`λ ↦ -λ`, `E ↦ F`, the dot to the dot, the upward crossing
to minus the downward crossing). We realize it on Rouquier's data at one weight (`RouqLoc`): the
data at the weight `h` in a bicategory `C` give data at the weight `-h` in the bidual `Coop C`
(1-morphisms and 2-morphisms reversed), with `E₁' = op E₂`, `E₂' = op E₁`, the same dots and minus
the crossing (`RouqLoc.dual`). In the bidual the reversal of 2-morphisms is Brundan's `opp`, and
the reversal of 1-morphisms reflects pictures in a vertical axis, so an upward strand of `E₂'`
is the strand `E₁` of `C` read backwards; under this dictionary

* the rightward crossing becomes minus the rightward crossing (`dual_sig`; Brundan, proof of
  Theorem 2.3), the leftward crossing minus the leftward crossing (`dual_sigL`);
* the rightward caps with dots become the rightward cups with dots (`dual_capD`, `dual_cupD`), the
  `♠`-cups the `♣`-caps (`dual_cupN`, `dual_capN`; Brundan (3.4)), the leftward cup the leftward
  cap (`dual_cupL`, `dual_capL`);
* the counter-clockwise bubbles become the clockwise ones (`dual_ccw`, `dual_cw`; Brundan (3.10)).

Every relation proved for all Rouquier data at weights `h ≥ 0` thus gives its mirror image at the
weights `h ≤ 0`.

## Main declarations

* `SumInvTo.op`, `SumInvFrom.op`, `SumInvTo.neg`, `SumInvFrom.neg`, `SumInvTo.congr`,
  `SumInvFrom.congr`: explicit inverses in the opposite category, after a sign change, and along
  equalities;
* `Coop.additiveWhiskering`: whiskering in the bidual is additive;
* `RouqLoc.dual`, and the dictionary `dual_sig`, `dual_capD`, `dual_cupD`, `dual_sigL`,
  `dual_cupN`, `dual_capN`, `dual_cupL`, `dual_capL`, `dual_ccw`, `dual_cw`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory Opposite

universe w v u

/-! ## Explicit inverses: opposite category, signs, equalities -/

section SumInv

variable {D : Type*} [Category D] [Preadditive D] {X Y Z : D}

/-- An explicit inverse into a direct sum is an explicit inverse out of a direct sum in the
opposite category. -/
def SumInvTo.op {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)} {n : ℕ} (I : SumInvTo f g n) :
    SumInvFrom f.op (fun m => (g m).op) n where
  f' := I.f'.op
  g' m := (I.g' m).op
  total := by
    apply Quiver.Hom.unop_inj
    simpa using I.total
  ff := by
    apply Quiver.Hom.unop_inj
    simpa using I.ff
  fg m hm := by
    apply Quiver.Hom.unop_inj
    simpa using I.gf m hm
  gf m hm := by
    apply Quiver.Hom.unop_inj
    simpa using I.fg m hm
  gg m m' hm hm' := by
    apply Quiver.Hom.unop_inj
    rw [unop_comp, Quiver.Hom.unop_op, Quiver.Hom.unop_op, I.gg m' m hm' hm]
    by_cases hmm : m = m'
    · subst hmm; simp
    · rw [ite_eq_right (Ne.symm hmm), ite_eq_right hmm]; rfl

/-- An explicit inverse out of a direct sum is an explicit inverse into a direct sum in the
opposite category. -/
def SumInvFrom.op {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)} {n : ℕ} (I : SumInvFrom f g n) :
    SumInvTo f.op (fun m => (g m).op) n where
  f' := I.f'.op
  g' m := (I.g' m).op
  total := by
    apply Quiver.Hom.unop_inj
    simpa using I.total
  ff := by
    apply Quiver.Hom.unop_inj
    simpa using I.ff
  fg m hm := by
    apply Quiver.Hom.unop_inj
    simpa using I.gf m hm
  gf m hm := by
    apply Quiver.Hom.unop_inj
    simpa using I.fg m hm
  gg m m' hm hm' := by
    apply Quiver.Hom.unop_inj
    rw [unop_comp, Quiver.Hom.unop_op, Quiver.Hom.unop_op, I.gg m' m hm' hm]
    by_cases hmm : m = m'
    · subst hmm; simp
    · rw [ite_eq_right (Ne.symm hmm), ite_eq_right hmm]; rfl

/-- Changing the sign of the first component. -/
def SumInvTo.neg {f : X ⟶ Y} {g : ℕ → (X ⟶ Z)} {n : ℕ} (I : SumInvTo f g n) :
    SumInvTo (-f) g n where
  f' := -I.f'
  g' := I.g'
  total := by rw [Preadditive.neg_comp_neg, I.total]
  ff := by rw [Preadditive.neg_comp_neg, I.ff]
  fg m hm := by rw [Preadditive.neg_comp, I.fg m hm, neg_zero]
  gf m hm := by rw [Preadditive.comp_neg, I.gf m hm, neg_zero]
  gg := I.gg

/-- Changing the sign of the first component. -/
def SumInvFrom.neg {f : Y ⟶ X} {g : ℕ → (Z ⟶ X)} {n : ℕ} (I : SumInvFrom f g n) :
    SumInvFrom (-f) g n where
  f' := -I.f'
  g' := I.g'
  total := by rw [Preadditive.neg_comp_neg, I.total]
  ff := by rw [Preadditive.neg_comp_neg, I.ff]
  fg m hm := by rw [Preadditive.neg_comp, I.fg m hm, neg_zero]
  gf m hm := by rw [Preadditive.comp_neg, I.gf m hm, neg_zero]
  gg := I.gg

/-- Transport along equalities of the components. -/
def SumInvTo.congr {f f₂ : X ⟶ Y} {g g₂ : ℕ → (X ⟶ Z)} {n n₂ : ℕ} (I : SumInvTo f g n)
    (hf : f = f₂) (hg : g = g₂) (hn : n = n₂) : SumInvTo f₂ g₂ n₂ where
  f' := I.f'
  g' := I.g'
  total := by subst hf hg hn; exact I.total
  ff := by subst hf; exact I.ff
  fg m hm := by subst hg hn; exact I.fg m hm
  gf m hm := by subst hf hn; exact I.gf m hm
  gg m m' hm hm' := by subst hg hn; exact I.gg m m' hm hm'

/-- Transport along equalities of the components. -/
def SumInvFrom.congr {f f₂ : Y ⟶ X} {g g₂ : ℕ → (Z ⟶ X)} {n n₂ : ℕ} (I : SumInvFrom f g n)
    (hf : f = f₂) (hg : g = g₂) (hn : n = n₂) : SumInvFrom f₂ g₂ n₂ where
  f' := I.f'
  g' := I.g'
  total := by subst hf hg hn; exact I.total
  ff := by subst hf; exact I.ff
  fg m hm := by subst hf hn; exact I.fg m hm
  gf m hm := by subst hg hn; exact I.gf m hm
  gg m m' hm hm' := by subst hg hn; exact I.gg m m' hm hm'

omit [Preadditive D] in
theorem powComp_one {X : D} (f : X ⟶ X) : powComp f 1 = f := by
  rw [powComp_succ, powComp_zero, Category.id_comp]

omit [Preadditive D] in
theorem powComp_comp_powComp {X : D} (f : X ⟶ X) (m n : ℕ) :
    powComp f m ≫ powComp f n = powComp f (m + n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [powComp_succ, ← Category.assoc, ih, ← add_assoc, powComp_succ]

omit [Preadditive D] in
theorem comp_powComp {X : D} (f : X ⟶ X) (n : ℕ) : f ≫ powComp f n = powComp f (n + 1) := by
  calc f ≫ powComp f n = powComp f 1 ≫ powComp f n := by rw [powComp_one]
    _ = powComp f (n + 1) := by rw [powComp_comp_powComp, add_comm]

omit [Preadditive D] in
theorem unop_powComp {X : Dᵒᵖ} (f : X ⟶ X) (n : ℕ) : (powComp f n).unop = powComp f.unop n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [powComp_succ, unop_comp, ih, comp_powComp]

end SumInv

/-! ## Additive whiskering in the bidual -/

namespace Coop

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]

section Lemmas

variable {a b : B}

omit [∀ a b : B, Preadditive (a ⟶ b)] in
@[simp] theorem unop_op1 {a b : B} (f : a ⟶ b) : (op1 f).unop = f := rfl

omit [∀ a b : B, Preadditive (a ⟶ b)] in
@[simp] theorem unop_op2 {f g : a ⟶ b} (η : f ⟶ g) : (op2 η).unop = η := rfl

omit [∀ a b : B, Preadditive (a ⟶ b)] in
theorem adjunction_unit {u : a ⟶ b} {v : b ⟶ a} (adj : u ⊣ v) :
    (Coop.adjunction adj).unit = op2 adj.counit := rfl

omit [∀ a b : B, Preadditive (a ⟶ b)] in
theorem adjunction_counit {u : a ⟶ b} {v : b ⟶ a} (adj : u ⊣ v) :
    (Coop.adjunction adj).counit = op2 adj.unit := rfl

omit [∀ a b : B, Preadditive (a ⟶ b)] in
@[simp] theorem adjunction_unit_unop {u : a ⟶ b} {v : b ⟶ a} (adj : u ⊣ v) :
    (Coop.adjunction adj).unit.unop = adj.counit := rfl

omit [∀ a b : B, Preadditive (a ⟶ b)] in
@[simp] theorem adjunction_counit_unop {u : a ⟶ b} {v : b ⟶ a} (adj : u ⊣ v) :
    (Coop.adjunction adj).counit.unop = adj.unit := rfl

variable {a b : Coop B} {f g : a ⟶ b}

@[simp] theorem unop_add₂ (η θ : f ⟶ g) : (η + θ).unop = η.unop + θ.unop := rfl

@[simp] theorem unop_neg₂ (η : f ⟶ g) : (-η).unop = -η.unop := rfl

@[simp] theorem unop_sub₂ (η θ : f ⟶ g) : (η - θ).unop = η.unop - θ.unop := rfl

@[simp] theorem unop_zero₂ : (0 : f ⟶ g).unop = 0 := rfl

/-- `unop` on the 2-morphisms of the bidual, as an additive map. -/
def unopAddHom₂ (f g : a ⟶ b) : (f ⟶ g) →+ (g.unop ⟶ f.unop) where
  toFun := Quiver.Hom.unop
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem unop_sum₂ {ι : Type*} (s : Finset ι) (η : ι → (f ⟶ g)) :
    (∑ i ∈ s, η i).unop = ∑ i ∈ s, (η i).unop :=
  map_sum (unopAddHom₂ f g) η s

end Lemmas

instance additiveWhiskering [AdditiveWhiskering B] : AdditiveWhiskering (Coop B) where
  whiskerLeft_add f _ _ η θ := Quiver.Hom.unop_inj (by
    simp only [Coop.unop_whiskerLeft, unop_add₂]
    exact AdditiveWhiskering.add_whiskerRight _ _ _)
  add_whiskerRight η θ h := Quiver.Hom.unop_inj (by
    simp only [Coop.unop_whiskerRight, unop_add₂]
    exact AdditiveWhiskering.whiskerLeft_add _ _ _)

end Coop

/-! ## The dual of Rouquier's data at one weight -/

namespace RouqLoc

open Coop

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a b c : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ}

/-- The crossing of the dual data: minus the crossing, read in the bidual. -/
def dualτ (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) : op1 E₂ ≫ op1 E₁ ⟶ op1 E₂ ≫ op1 E₁ := -op2 τ

omit [AdditiveWhiskering C] in
@[simp] theorem unop_dualτ (τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) : (dualτ τ).unop = -τ := rfl

theorem dual_sigma :
    RightwardCrossing.sigma (Coop.adjunction adj₁).unit (dualτ τ) (Coop.adjunction adj₂).counit =
      -(RightwardCrossing.sigma adj₂.unit τ adj₁.counit).op := by
  rw [RightwardCrossing.sigma_eq]
  apply Quiver.Hom.unop_inj
  simp only [Coop.unop_comp₂, Coop.unop_whiskerLeft, Coop.unop_whiskerRight,
    Coop.associator_hom_unop, Coop.associator_inv_unop, Coop.leftUnitor_hom_unop,
    Coop.rightUnitor_inv_unop, unop_dualτ,
    Coop.adjunction_unit_unop, Coop.adjunction_counit_unop]
  change ((((((((ρ_ (R₁ ≫ E₁)).inv ≫ (R₁ ≫ E₁) ◁ adj₂.unit) ≫ (α_ (R₁ ≫ E₁) E₂ R₂).inv) ≫
      (α_ R₁ E₁ E₂).hom ▷ R₂) ≫ (R₁ ◁ (-τ)) ▷ R₂) ≫ (α_ R₁ E₁ E₂).inv ▷ R₂) ≫
      (α_ (R₁ ≫ E₁) E₂ R₂).hom) ≫ adj₁.counit ▷ (E₂ ≫ R₂)) ≫ (λ_ (E₂ ≫ R₂)).hom =
    -RightwardCrossing.sigma adj₂.unit τ adj₁.counit
  simp only [AdditiveWhiskering.whiskerLeft_neg, AdditiveWhiskering.neg_whiskerRight,
    Preadditive.comp_neg, Preadditive.neg_comp, neg_inj, RightwardCrossing.sigma_eq]
  bicategory

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
theorem dual_capD_fun :
    (fun n => op1 R₂ ◁ powComp (op2 x₂) n ≫ (Coop.adjunction adj₂).counit) =
      fun n => (adj₂.unit ≫ powComp x₂ n ▷ R₂).op := by
  funext n
  apply Quiver.Hom.unop_inj
  rw [Coop.unop_comp₂, Coop.unop_whiskerLeft, unop_powComp]
  rfl

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
theorem dual_cupD_fun :
    (fun n => (Coop.adjunction adj₁).unit ≫ powComp (op2 x₁) n ▷ op1 R₁) =
      fun n => (R₁ ◁ powComp x₁ n ≫ adj₁.counit).op := by
  funext n
  apply Quiver.Hom.unop_inj
  rw [Coop.unop_comp₂, Coop.unop_whiskerRight, unop_powComp]
  rfl

/-- **The dual of Rouquier's data** (Brundan, Theorem 2.3): data at the weight `h` in `C` give
data at the weight `-h` in the bidual, with `E₁' = op E₂`, `E₂' = op E₁`, the same dots and minus
the crossing. -/
def dual (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) :
    RouqLoc (Coop.adjunction adj₂) (Coop.adjunction adj₁) (op2 x₂) (op2 x₁) (dualτ τ) (-h) where
  slide_left := by
    apply Quiver.Hom.unop_inj
    change (-τ) ≫ x₁ ▷ E₂ - E₁ ◁ x₂ ≫ (-τ) = 𝟙 (E₁ ≫ E₂)
    rw [Preadditive.neg_comp, Preadditive.comp_neg, ← L.slide_left]
    abel
  slide_right := by
    apply Quiver.Hom.unop_inj
    change x₁ ▷ E₂ ≫ (-τ) - (-τ) ≫ E₁ ◁ x₂ = 𝟙 (E₁ ≫ E₂)
    rw [Preadditive.neg_comp, Preadditive.comp_neg, ← L.slide_right]
    abel
  invPos hh := (((L.invNeg (by omega)).op).neg).congr dual_sigma.symm dual_capD_fun.symm rfl
  invNeg hh := (((L.invPos (by omega)).op).neg).congr dual_sigma.symm dual_cupD_fun.symm
    (by rw [neg_neg])

/-! ### The dictionary -/

variable (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

theorem dual_sig : L.dual.sig = -L.sig.op := dual_sigma

theorem dual_capD (n : ℕ) : L.dual.capD n = (L.cupD n).op := congrFun dual_capD_fun n

theorem dual_cupD (n : ℕ) : L.dual.cupD n = (L.capD n).op := congrFun dual_cupD_fun n

theorem dual_sigL : L.dual.sigL = -L.sigL.op := by
  rcases le_or_gt h 0 with hh | hh
  · rw [sigL_of_nonneg (L := L.dual) (by omega), sigL_of_nonpos hh]
    rfl
  · rw [sigL_of_nonpos (L := L.dual) (by omega), sigL_of_nonneg hh.le]
    rfl

theorem dual_cupN (n : ℕ) : L.dual.cupN n = (L.capN n).op := by
  rcases le_or_gt h 0 with hh | hh
  · rw [cupN_of_nonneg (L := L.dual) (by omega), capN_of_nonpos hh]
    rfl
  · rw [cupN_of_neg (L := L.dual) (by omega), capN_of_pos hh]
    rfl

theorem dual_capN (n : ℕ) : L.dual.capN n = (L.cupN n).op := by
  rcases le_or_gt 0 h with hh | hh
  · rw [capN_of_nonpos (L := L.dual) (by omega), cupN_of_nonneg hh]
    rfl
  · rw [capN_of_pos (L := L.dual) (by omega), cupN_of_neg hh]
    rfl

theorem dual_cupL : L.dual.cupL = L.capL.op := by
  rcases lt_or_ge h 0 with hh | hh
  · rw [cupL_of_pos (L := L.dual) (by omega), capL_of_neg hh, dual_cupN]
  · rw [cupL_of_nonpos (L := L.dual) (by omega), capL_of_nonneg hh, dual_cupD, dual_sigL, neg_neg]
    apply Quiver.Hom.unop_inj
    change (-L.sigL) ≫ L.capD h.toNat = -(L.sigL ≫ L.capD h.toNat)
    exact Preadditive.neg_comp _ _

theorem dual_capL : L.dual.capL = L.cupL.op := by
  rcases lt_or_ge 0 h with hh | hh
  · rw [capL_of_neg (L := L.dual) (by omega), cupL_of_pos hh, dual_capN]
    congr 2
    omega
  · rw [capL_of_nonneg (L := L.dual) (by omega), cupL_of_nonpos hh, dual_capD, dual_sigL]
    apply Quiver.Hom.unop_inj
    change -(L.cupD (-h).toNat ≫ (-L.sigL)) = L.cupD (-h).toNat ≫ L.sigL
    rw [Preadditive.comp_neg, neg_neg]

/-- Brundan (3.10): the dual exchanges the counter-clockwise and clockwise bubbles. -/
theorem dual_ccw (k : ℤ) : L.dual.ccw k = (L.cw k).op := by
  rcases le_or_gt 0 k with hk | hk
  · rw [ccw_of_nonneg hk, cw_of_nonneg hk, dual_cupL, dual_capD]
    rfl
  · rcases lt_trichotomy (-h - 1) k with hk' | hk' | hk'
    · rw [ccw_of_neg_of_gt (L := L.dual) hk (by omega), cw_of_neg_of_gt hk hk', dual_cupD,
        dual_capN, neg_neg]
      rfl
    · rw [ccw_of_neg_of_eq (L := L.dual) hk (by omega), cw_of_neg_of_eq hk hk'.symm]
      rfl
    · rw [ccw_of_neg_of_lt (L := L.dual) hk (by omega), cw_of_neg_of_lt hk hk']
      rfl

/-- Brundan (3.10): the dual exchanges the clockwise and counter-clockwise bubbles. -/
theorem dual_cw (k : ℤ) : L.dual.cw k = (L.ccw k).op := by
  rcases le_or_gt 0 k with hk | hk
  · rw [cw_of_nonneg hk, ccw_of_nonneg hk, dual_capL, dual_cupD]
    rfl
  · rcases lt_trichotomy (h - 1) k with hk' | hk' | hk'
    · rw [cw_of_neg_of_gt (L := L.dual) hk (by omega), ccw_of_neg_of_gt hk hk', dual_capD,
        dual_cupN]
      rfl
    · rw [cw_of_neg_of_eq (L := L.dual) hk (by omega), ccw_of_neg_of_eq hk hk'.symm]
      rfl
    · rw [cw_of_neg_of_lt (L := L.dual) hk (by omega), ccw_of_neg_of_lt hk hk']
      rfl

end RouqLoc

end Categorification.TwoRep
