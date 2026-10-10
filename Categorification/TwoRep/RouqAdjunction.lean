/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqTriangleE

/-!
# Left adjunction from Rouquier data

Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, Theorem 4.3.
The headline construction `RouqLoc.leftAdjunction` proves that the prescribed leftward
cup and cap form an adjunction. It uses adjacent Rouquier data and the nilHecke squares
and braid, with no grading, finiteness, or scalar-endomorphism assumption.

The upward triangle is supplied by `RouqTriangleE`. To obtain the downward triangle,
`RouqLoc.mirror` reflects the data into the horizontal opposite, replaces dots and
crossings by right mates, and leaves the inverse components and leftward cup/cap unchanged.
The reflected upward triangle is precisely the required downward triangle.

This adjunction supplies the left mates needed by the cyclicity relations.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
universe w v u

/-- The horizontal opposite with unchanged Hom categories. -/
structure HOp (C : Type u) where
  obj : C
namespace HOp
variable {C : Type u} [Bicategory.{w, v} C]
instance : Bicategory.{w, v} (HOp C) where
  Hom a b := obj b ⟶ obj a
  id a := 𝟙 (obj a)
  comp f g := g ≫ f
  homCategory _ _ := inferInstance
  whiskerLeft f _ _ η := η ▷ f
  whiskerRight η h := h ◁ η
  associator f g h := (α_ h g f).symm
  leftUnitor f := ρ_ f
  rightUnitor f := λ_ f
  whiskerLeft_id _ _ := by simp
  whiskerLeft_comp _ _ _ _ _ _ := by simp
  id_whiskerLeft _ := by simp
  comp_whiskerLeft _ _ _ _ _ := by simp
  id_whiskerRight _ _ := by simp
  comp_whiskerRight _ _ _ := by simp
  whiskerRight_id _ := by simp
  whiskerRight_comp _ _ _ := by simp
  whisker_assoc _ _ _ _ _ := by simp
  whisker_exchange _ _ := by simp [whisker_exchange]
  pentagon _ _ _ _ := by simp
  triangle _ _ := by simp
abbrev op1 {a b : C} (f : a ⟶ b) : mk b ⟶ mk a := f
instance [∀ a b : C, Preadditive (a ⟶ b)] (a b : HOp C) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (obj b ⟶ obj a))
instance [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] : AdditiveWhiskering (HOp C) where
  whiskerLeft_add _ _ _ _ _ := AdditiveWhiskering.add_whiskerRight _ _ _
  add_whiskerRight _ _ _ := AdditiveWhiskering.whiskerLeft_add _ _ _
/-- A right adjunction reflects to an adjunction with left and right adjoints exchanged. -/
def adjunction {a b : C} {E : a ⟶ b} {R : b ⟶ a} (A : E ⊣ R) : op1 R ⊣ op1 E where
  unit := A.unit
  counit := A.counit
  left_triangle := by
    rw [leftZigzag_eq]
    change R ◁ A.unit ≫ (α_ R E R).inv ≫ A.counit ▷ R = _
    rw [← rightZigzag_eq]
    exact A.right_triangle
  right_triangle := by
    rw [rightZigzag_eq]
    change A.unit ▷ E ≫ (α_ E R E).hom ≫ E ◁ A.counit = _
    rw [← leftZigzag_eq]
    exact A.left_triangle
/-- Reflection turns a mates equivalence into its inverse. -/
theorem mateEquiv_reflect {a b c d : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a}
    {E₂ : c ⟶ d} {R₂ : d ⟶ c} (A : E₁ ⊣ R₁) (B : E₂ ⊣ R₂)
    {g : c ⟶ a} {h : d ⟶ b} (t : R₂ ≫ g ⟶ h ≫ R₁) :
    mateEquiv (adjunction A) (adjunction B) (g := op1 g) (h := op1 h) t =
      (mateEquiv B A).symm t := by
  dsimp [Bicategory.mateEquiv, Adjunction.homEquiv₁, Adjunction.homEquiv₂, adjunction,
    Iso.homCongr]
  simp only [Category.id_comp]
  change (((λ_ g).inv ≫ B.unit ▷ g ≫ (α_ E₂ R₂ g).hom ≫ E₂ ◁ t) ≫
      (α_ E₂ h R₁).inv) ▷ E₁ ≫ (α_ (E₂ ≫ h) R₁ E₁).hom ≫
      (E₂ ≫ h) ◁ A.counit ≫ (ρ_ (E₂ ≫ h)).hom = _
  rfl
end HOp

namespace RouqSl2Generic
variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a b : C} {E : a ⟶ b} {R : b ⟶ a}
/-- Ordinary right mates form an additive equivalence. -/
def rightMateAddEquiv (A : E ⊣ R) : (E ⟶ E) ≃+ (R ⟶ R) where
  toEquiv := conjugateEquiv A A
  map_add' x y := by
    change conjugateEquiv A A (x + y) = conjugateEquiv A A x + conjugateEquiv A A y
    simp only [Bicategory.conjugateEquiv_apply', AdditiveWhiskering.whiskerLeft_add,
      AdditiveWhiskering.add_whiskerRight, Preadditive.comp_add, Preadditive.add_comp]

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
/-- Right mates take powers to powers. -/
theorem rightMate_pow (A : E ⊣ R) (x : E ⟶ E) (n : ℕ) :
    conjugateEquiv A A (powComp x n) = powComp (conjugateEquiv A A x) n := by
  induction n with
  | zero => simp only [powComp_zero, Bicategory.conjugateEquiv_id]
  | succ n ih =>
    rw [powComp_succ, ← Bicategory.conjugateEquiv_comp, ih]
    conv_lhs => lhs; rw [← powComp_one (conjugateEquiv A A x)]
    rw [powComp_comp_powComp, Nat.add_comm]

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
/-- The rightward crossing is the partial right mate of the upward crossing. -/
theorem sigma_eq_mate {c : C} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
    (A : E ⊣ R) (B : E₂ ⊣ R₂) (t : E ≫ E₂ ⟶ E ≫ E₂) :
    RightwardCrossing.sigma B.unit t A.counit = mateEquiv A B t := by
  rw [RightwardCrossing.sigma_def, mateEquiv_apply']
  bicategory

omit [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C] in
/-- The full right mate is obtained by the two partial mates. -/
theorem rightMate_eq_iterated {c : C} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
    (A : E ⊣ R) (B : E₂ ⊣ R₂) (t : E ≫ E₂ ⟶ E ≫ E₂) :
    conjugateEquiv (A.comp B) (A.comp B) t = mateEquiv B A (mateEquiv A B t) := by
  exact (iterated_mateEquiv_conjugateEquiv A B A B t).symm

end RouqSl2Generic

namespace RouqSl2Generic

/-- The right mate of an inverse associator reverses the adjoints. -/
theorem rightMate_associator_inv {D : Type*} [Bicategory D]
    {a b c d : D} {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}
    {f₃ : c ⟶ d} {g₃ : d ⟶ c}
    (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) (adj₃ : f₃ ⊣ g₃) :
    conjugateEquiv ((adj₁.comp adj₂).comp adj₃)
      (adj₁.comp (adj₂.comp adj₃)) (α_ f₁ f₂ f₃).inv = (α_ g₃ g₂ g₁).inv := by
  apply (cancel_epi (α_ g₃ g₂ g₁).hom).mp
  rw [← Bicategory.conjugateEquiv_associator_hom adj₁ adj₂ adj₃,
    Bicategory.conjugateEquiv_comp, Iso.inv_hom_id, Bicategory.conjugateEquiv_id,
    Bicategory.conjugateEquiv_associator_hom, Iso.hom_inv_id]

/-- Reassociation before taking right mates becomes reverse reassociation afterwards. -/
theorem rightMate_reassociate {D : Type*} [Bicategory D]
    {a b c d : D} {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}
    {f₃ : c ⟶ d} {g₃ : d ⟶ c}
    (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) (adj₃ : f₃ ⊣ g₃)
    (φ : (f₁ ≫ f₂) ≫ f₃ ⟶ (f₁ ≫ f₂) ≫ f₃) :
    conjugateEquiv (adj₁.comp (adj₂.comp adj₃)) (adj₁.comp (adj₂.comp adj₃))
      ((α_ f₁ f₂ f₃).inv ≫ φ ≫ (α_ f₁ f₂ f₃).hom) =
      (α_ g₃ g₂ g₁).hom ≫
        conjugateEquiv ((adj₁.comp adj₂).comp adj₃) ((adj₁.comp adj₂).comp adj₃) φ ≫
        (α_ g₃ g₂ g₁).inv := by
  rw [← Bicategory.conjugateEquiv_comp _ ((adj₁.comp adj₂).comp adj₃),
    ← Bicategory.conjugateEquiv_comp _ ((adj₁.comp adj₂).comp adj₃),
    Bicategory.conjugateEquiv_associator_hom, rightMate_associator_inv]
  simp only [Category.assoc]
end RouqSl2Generic

namespace RouqLoc
open RouqSl2Generic
variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a b c : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ}
  (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

/-- The crossing of the reflected Rouquier data. -/
abbrev mirrorTau (_L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) :
    (HOp.op1 R₁ ≫ HOp.op1 R₂) ⟶ (HOp.op1 R₁ ≫ HOp.op1 R₂) :=
  conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ

omit [AdditiveWhiskering C] in
/-- The rightward crossing is unchanged by reflection through right mates. -/
theorem mirror_sigma : RightwardCrossing.sigma (HOp.adjunction adj₂).unit
    L.mirrorTau (HOp.adjunction adj₁).counit = L.sig := by
  rw [sigma_eq_mate, HOp.mateEquiv_reflect]
  unfold mirrorTau
  rw [rightMate_eq_iterated, Equiv.symm_apply_apply, ← sigma_eq_mate]
  rfl

omit [AdditiveWhiskering C] in
/-- The reflected dotted cap is the original dotted cap. -/
theorem mirror_capD (n : ℕ) : powComp L.dotD₁ n ▷ E₁ ≫ adj₁.counit = L.capD n := by
  rw [dotD₁, ← rightMate_pow, conjugateEquiv_whiskerRight_counit]
  rfl

omit [AdditiveWhiskering C] in
/-- The reflected dotted cup is the original dotted cup. -/
theorem mirror_cupD (n : ℕ) : adj₂.unit ≫ E₂ ◁ powComp L.dotD₂ n = L.cupD n := by
  rw [dotD₂, ← rightMate_pow, unit_whiskerLeft_conjugateEquiv]
  rfl

/-- Right-mate reflection preserves local Rouquier data and the weight. -/
def mirror : RouqLoc (HOp.adjunction adj₁) (HOp.adjunction adj₂)
    (E₁ := HOp.op1 R₁) (R₁ := HOp.op1 E₁) (E₂ := HOp.op1 R₂) (R₂ := HOp.op1 E₂)
    L.dotD₁ L.dotD₂ L.mirrorTau h where
  slide_left := by
    have hh := congrArg (rightMateAddEquiv (adj₁.comp adj₂)) L.slide_right
    simp only [map_sub] at hh
    change conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) (τ ≫ E₁ ◁ x₂) -
      conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) (x₁ ▷ E₂ ≫ τ) =
      conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) (𝟙 _) at hh
    rw [← Bicategory.conjugateEquiv_comp (adj₁.comp adj₂) (adj₁.comp adj₂) (adj₁.comp adj₂),
      ← Bicategory.conjugateEquiv_comp (adj₁.comp adj₂) (adj₁.comp adj₂) (adj₁.comp adj₂),
      Bicategory.conjugateEquiv_whiskerLeft, Bicategory.conjugateEquiv_whiskerRight,
      Bicategory.conjugateEquiv_id] at hh
    exact hh
  slide_right := by
    have hh := congrArg (rightMateAddEquiv (adj₁.comp adj₂)) L.slide_left
    simp only [map_sub] at hh
    change conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) (E₁ ◁ x₂ ≫ τ) -
      conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) (τ ≫ x₁ ▷ E₂) =
      conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) (𝟙 _) at hh
    rw [← Bicategory.conjugateEquiv_comp (adj₁.comp adj₂) (adj₁.comp adj₂) (adj₁.comp adj₂),
      ← Bicategory.conjugateEquiv_comp (adj₁.comp adj₂) (adj₁.comp adj₂) (adj₁.comp adj₂),
      Bicategory.conjugateEquiv_whiskerLeft, Bicategory.conjugateEquiv_whiskerRight,
      Bicategory.conjugateEquiv_id] at hh
    exact hh
  invPos hh := by
    change SumInvTo _ (fun n => powComp L.dotD₁ n ▷ E₁ ≫ adj₁.counit) _
    exact (L.ip hh).congr L.mirror_sigma.symm (funext fun n => (L.mirror_capD n).symm) rfl
  invNeg hh := by
    change SumInvFrom _ (fun n => adj₂.unit ≫ E₂ ◁ powComp L.dotD₂ n) _
    exact (L.iN hh).congr L.mirror_sigma.symm (funext fun n => (L.mirror_cupD n).symm) rfl

@[simp] theorem mirror_sigL : L.mirror.sigL = L.sigL := rfl
@[simp] theorem mirror_cupN (n : ℕ) : L.mirror.cupN n = L.cupN n := rfl
@[simp] theorem mirror_capN (n : ℕ) : L.mirror.capN n = L.capN n := rfl
@[simp] theorem mirror_cupL : L.mirror.cupL = L.cupL := by
  unfold cupL
  split_ifs
  · rfl
  · change (adj₂.unit ≫ E₂ ◁ powComp L.dotD₂ (-h).toNat) ≫ L.sigL = _
    rw [L.mirror_cupD]
@[simp] theorem mirror_capL : L.mirror.capL = L.capL := by
  unfold capL
  split_ifs
  · rfl
  · change -(L.sigL ≫ powComp L.dotD₁ h.toNat ▷ E₁ ≫ adj₁.counit) = _
    rw [L.mirror_capD]

/-- The nilHecke square is preserved by right-mate reflection. -/
theorem mirror_square (hs : τ ≫ τ = 0) : L.mirrorTau ≫ L.mirrorTau = 0 := by
  change conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ ≫
    conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ = 0
  rw [Bicategory.conjugateEquiv_comp, hs]
  exact (rightMateAddEquiv (adj₁.comp adj₂)).map_zero
variable {d : C} {E₃ : c ⟶ d} {R₃ : d ⟶ c} {adj₃ : E₃ ⊣ R₃} {x₃ : E₃ ⟶ E₃}
  {τ₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃} {h' : ℤ}
  (U : RouqLoc adj₂ adj₃ x₂ x₃ τ₂₃ h')

omit [AdditiveWhiskering C] in
/-- The adjacent braid relation is preserved by right-mate reflection. -/
theorem mirror_braid
    (hb : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom)) :
    HOp.op1 R₁ ◁ U.mirrorTau ≫
        ((α_ (HOp.op1 R₁) (HOp.op1 R₂) (HOp.op1 R₃)).inv ≫
          L.mirrorTau ▷ HOp.op1 R₃ ≫ (α_ (HOp.op1 R₁) (HOp.op1 R₂) (HOp.op1 R₃)).hom) ≫
        HOp.op1 R₁ ◁ U.mirrorTau =
      ((α_ (HOp.op1 R₁) (HOp.op1 R₂) (HOp.op1 R₃)).inv ≫
          L.mirrorTau ▷ HOp.op1 R₃ ≫ (α_ (HOp.op1 R₁) (HOp.op1 R₂) (HOp.op1 R₃)).hom) ≫
        HOp.op1 R₁ ◁ U.mirrorTau ≫
      ((α_ (HOp.op1 R₁) (HOp.op1 R₂) (HOp.op1 R₃)).inv ≫
          L.mirrorTau ▷ HOp.op1 R₃ ≫ (α_ (HOp.op1 R₁) (HOp.op1 R₂) (HOp.op1 R₃)).hom) := by
  let A := adj₁.comp (adj₂.comp adj₃)
  have hh := congrArg (conjugateEquiv A A) hb
  simp only [← Bicategory.conjugateEquiv_comp A A A] at hh
  dsimp only [A] at hh
  rw [rightMate_reassociate, Bicategory.conjugateEquiv_whiskerRight,
    Bicategory.conjugateEquiv_whiskerLeft] at hh
  change conjugateEquiv (adj₂.comp adj₃) (adj₂.comp adj₃) τ₂₃ ▷ R₁ ≫
      ((α_ R₃ R₂ R₁).hom ≫ R₃ ◁ conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ ≫
        (α_ R₃ R₂ R₁).inv) ≫ conjugateEquiv (adj₂.comp adj₃) (adj₂.comp adj₃) τ₂₃ ▷ R₁ =
    ((α_ R₃ R₂ R₁).hom ≫ R₃ ◁ conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ ≫
      (α_ R₃ R₂ R₁).inv) ≫ conjugateEquiv (adj₂.comp adj₃) (adj₂.comp adj₃) τ₂₃ ▷ R₁ ≫
    ((α_ R₃ R₂ R₁).hom ≫ R₃ ◁ conjugateEquiv (adj₁.comp adj₂) (adj₁.comp adj₂) τ ≫
      (α_ R₃ R₂ R₁).inv)
  simpa only [Category.assoc] using hh

/-- The downward-strand triangle, obtained by reflection from the upward triangle. -/
theorem leftZigzag_left (hw : h' = h + 2)
    (hsq : τ ≫ τ = 0) (hsq' : τ₂₃ ≫ τ₂₃ = 0)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom)) :
    leftZigzag U.cupL L.capL = (λ_ R₂).hom ≫ (ρ_ R₂).inv := by
  have ht : rightZigzag (B := HOp C) (f := HOp.op1 E₂) (g := HOp.op1 R₂)
      U.mirror.cupL L.mirror.capL = (ρ_ (HOp.op1 R₂)).hom ≫ (λ_ (HOp.op1 R₂)).inv :=
    L.mirror.rightZigzag_left U.mirror hw (L.mirror_square hsq)
      (U.mirror_square hsq') (L.mirror_braid U hB)
  rw [rightZigzag_eq, L.mirror_capL, U.mirror_cupL] at ht
  change U.cupL ▷ R₂ ≫ (α_ R₂ E₂ R₂).hom ≫ R₂ ◁ L.capL = _ at ht
  rw [← leftZigzag_eq] at ht
  exact ht

/-- Brundan Theorem 4.3: the prescribed leftward cup and cap form a left adjunction. -/
def leftAdjunction (hw : h' = h + 2)
    (hsq : τ ≫ τ = 0) (hsq' : τ₂₃ ≫ τ₂₃ = 0)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom)) : R₂ ⊣ E₂ where
  unit := U.cupL
  counit := L.capL
  left_triangle := L.leftZigzag_left U hw hsq hsq' hB
  right_triangle := L.rightZigzag_left U hw hsq hsq' hB

end RouqLoc
end Categorification.TwoRep
