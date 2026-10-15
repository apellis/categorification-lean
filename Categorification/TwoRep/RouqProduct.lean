/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqYoneda
import Categorification.TwoRep.RouqReverse
import Categorification.QuantumGroup.RootDatumSum

/-!
# Rouquier families on categories of 1-morphisms

Let `W` and `T` be Rouquier families in a bicategory `B` (J. Brundan, *On the definition of
Kac–Moody 2-category*, arXiv:1501.00350v1, Definition 1.1), for root data `RD₁` and `RD₂`. On
the categories

`X(x₁, x₂) = Hom_B(T(-x₂), W(x₁))`

the colours of `RD₁` act by postcomposition with the 1-morphisms of `W`
(`RouqFamily.yoneda`), and the colours of `RD₂` act by precomposition with those of `T`, that
is, by postcomposition in the horizontal opposite with the reverse family (`RouqFamily.reverse`).
Colours of different sides commute through the associators. This is a Rouquier family
`RouqFamily.homProduct W T` for the product root datum (`WeightDatum.prod`).

When `W` is lowest weight and `T` is lowest weight (for instance both cyclotomic), `RD₁`
colours act as on a lowest-weight representation and `RD₂` colours as on a highest-weight one.
These are the test representations of B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*,
arXiv:1603.06311v3, proof of Theorem `nondegenerate` (the representations `X^{μ₊, μ₋}`, with
the labels `Ĩ₋` and `Ĩ₊`), here realized on categories of 1-morphisms.

## Weights

The weight `(x₁, x₂)` has two components, and a colour of one side does not change the other
component. Since `x₂ + 0 = y₂` is not a definitional equality, the 1-morphisms are transported
along the equality of the unchanged component (`tgtCast`, `srcCast`). The transports are trivial
once the unchanged components are identified, so every field reduces to a field of `W` or of
the reverse of `T`.

## Main declarations

* `RouqFamily.homProduct`: the Rouquier family on `Hom_B(T(-x₂), W(x₁))`;
* `RouqFamily.prodE_inl`, `RouqFamily.prodE_inr`: its 1-morphisms at weights whose unchanged
  component is literally the same, which are those of `W` and of the reverse of `T`;
* `WeightDatum.prod` (in `QuantumGroup.RootDatumSum`): the product weight datum.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w' w v u u₁

namespace RouqLoc

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  {a b c : B} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}

/-- Rouquier's data with the weight replaced by an equal one. -/
def ofWeight {h h' : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) (e : h = h') :
    RouqLoc adj₁ adj₂ x₁ x₂ τ h' := by
  subst e
  exact L

end RouqLoc

namespace RouqFamily

open Yoneda QuantumGroup UDot

section Family

variable (k : Type w') [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  {I₁ I₂ : Type*} {C₁ : CartanDatum I₁} {C₂ : CartanDatum I₂}
  {X₁ Y₁ X₂ Y₂ : Type u₁} [AddCommGroup X₁] [AddCommGroup Y₁] [AddCommGroup X₂]
  [AddCommGroup Y₂] {RD₁ : WeightDatum C₁ X₁ Y₁} {RD₂ : WeightDatum C₂ X₂ Y₂}
  (W : RouqFamily (B := B) RD₁) (T : RouqFamily (B := B) RD₂)

/-- The category `Hom_B(T(-x₂), W(x₁))` at the weight `(x₁, x₂)`. -/
abbrev homObj (x : X₁ × X₂) : LinearCat.{w', w, v} k := yObj k (T.obj (-x.2)) (W.obj x.1)

/-- The `RD₁` colours: postcomposition with `W`, at the second weight `x₂`. -/
abbrev leftFamily (x₂ : X₂) : RouqFamily (B := LinearCat.{w', w, v} k) RD₁ :=
  W.yoneda k (T.obj (-x₂))

/-- The `RD₂` colours: precomposition with `T`, at the first weight `x₁`. -/
abbrev rightFamily (x₁ : X₁) : RouqFamily (B := LinearCat.{w', w, v} k) RD₂ :=
  T.reverse.yoneda k (HOp.mk (W.obj x₁))

variable {k W T}

/-- Transport of the target of a 1-morphism along an equality of weights. -/
def tgtCast {x z z' : X₁ × X₂} (e : z = z') (f : homObj k W T x ⟶ homObj k W T z) :
    homObj k W T x ⟶ homObj k W T z' := e ▸ f

/-- Transport of the source of a 1-morphism along an equality of weights. -/
def srcCast {x z z' : X₁ × X₂} (e : z = z') (f : homObj k W T z ⟶ homObj k W T x) :
    homObj k W T z' ⟶ homObj k W T x := e ▸ f

/-- Transport of an adjunction. -/
def adjCast {x z z' : X₁ × X₂} (e : z = z') {f : homObj k W T x ⟶ homObj k W T z}
    {g : homObj k W T z ⟶ homObj k W T x} (A : f ⊣ g) : tgtCast e f ⊣ srcCast e g := by
  subst e
  exact A

/-- Transport of an endomorphism. -/
def endCast {x z z' : X₁ × X₂} (e : z = z') {f : homObj k W T x ⟶ homObj k W T z}
    (d : f ⟶ f) : tgtCast e f ⟶ tgtCast e f := by
  subst e
  exact d

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem fst_step (i : I₁) {x y : X₁ × X₂} (h : x + (RD₁.prod RD₂).iX (.inl i) = y) :
    x.1 + RD₁.iX i = y.1 := congrArg Prod.fst h

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem snd_step (i : I₂) {x y : X₁ × X₂} (h : x + (RD₁.prod RD₂).iX (.inr i) = y) :
    x.2 + RD₂.iX i = y.2 := congrArg Prod.snd h

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem snd_eq (i : I₁) {x y : X₁ × X₂} (h : x + (RD₁.prod RD₂).iX (.inl i) = y) :
    (y.1, x.2) = y := by
  rw [← h]
  exact Prod.ext rfl (add_zero x.2).symm

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem fst_eq (i : I₂) {x y : X₁ × X₂} (h : x + (RD₁.prod RD₂).iX (.inr i) = y) :
    (x.1, y.2) = y := by
  rw [← h]
  exact Prod.ext (add_zero x.1).symm rfl

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem inl_snd (i : I₁) {a₁ b₁ : X₁} {a₂ b₂ : X₂}
    (h : (a₁, a₂) + (RD₁.prod RD₂).iX (.inl i) = (b₁, b₂)) : a₂ = b₂ := by
  have := congrArg Prod.snd h
  simp only [Prod.snd_add, WeightDatum.prod_iX_inl, add_zero] at this
  exact this

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem inr_fst (i : I₂) {a₁ b₁ : X₁} {a₂ b₂ : X₂}
    (h : (a₁, a₂) + (RD₁.prod RD₂).iX (.inr i) = (b₁, b₂)) : a₁ = b₁ := by
  have := congrArg Prod.fst h
  simp only [Prod.fst_add, WeightDatum.prod_iX_inr, add_zero] at this
  exact this

variable (k W T)

/-- The 1-morphism of a colour: postcomposition with `W` for `RD₁` colours, precomposition with
`T` for `RD₂` colours. -/
def prodE : ∀ (c : I₁ ⊕ I₂) {x y : X₁ × X₂}, x + (RD₁.prod RD₂).iX c = y →
    (homObj k W T x ⟶ homObj k W T y)
  | .inl i, x, y, h => tgtCast (snd_eq i h)
      ((leftFamily k W T x.2).E i (fst_step (RD₂ := RD₂) (y := y) i h))
  | .inr i, x, y, h => tgtCast (fst_eq i h)
      (show homObj k W T x ⟶ homObj k W T (x.1, y.2) from
        (rightFamily k W T x.1).E i (snd_step (RD₁ := RD₁) (y := y) i h))

/-- The adjoint 1-morphism of a colour. -/
def prodF : ∀ (c : I₁ ⊕ I₂) {x y : X₁ × X₂}, x + (RD₁.prod RD₂).iX c = y →
    (homObj k W T y ⟶ homObj k W T x)
  | .inl i, x, y, h => srcCast (snd_eq i h)
      ((leftFamily k W T x.2).F i (fst_step (RD₂ := RD₂) (y := y) i h))
  | .inr i, x, y, h => srcCast (fst_eq i h)
      (show homObj k W T (x.1, y.2) ⟶ homObj k W T x from
        (rightFamily k W T x.1).F i (snd_step (RD₁ := RD₁) (y := y) i h))

/-- The adjunctions of the colours. -/
def prodAdj : ∀ (c : I₁ ⊕ I₂) {x y : X₁ × X₂} (h : x + (RD₁.prod RD₂).iX c = y),
    prodE k W T c h ⊣ prodF k W T c h
  | .inl i, x, y, h => adjCast (snd_eq i h)
      ((leftFamily k W T x.2).adj i (fst_step (RD₂ := RD₂) (y := y) i h))
  | .inr i, x, y, h => adjCast (fst_eq i h)
      (show (show homObj k W T x ⟶ homObj k W T (x.1, y.2) from
          (rightFamily k W T x.1).E i (snd_step (RD₁ := RD₁) (y := y) i h)) ⊣
        (show homObj k W T (x.1, y.2) ⟶ homObj k W T x from
          (rightFamily k W T x.1).F i (snd_step (RD₁ := RD₁) (y := y) i h)) from
        (rightFamily k W T x.1).adj i (snd_step (RD₁ := RD₁) (y := y) i h))

/-- The dots of the colours. -/
def prodDot : ∀ (c : I₁ ⊕ I₂) {x y : X₁ × X₂} (h : x + (RD₁.prod RD₂).iX c = y),
    prodE k W T c h ⟶ prodE k W T c h
  | .inl i, x, y, h => endCast (snd_eq i h)
      ((leftFamily k W T x.2).dot i (fst_step (RD₂ := RD₂) (y := y) i h))
  | .inr i, x, y, h => endCast (fst_eq i h)
      (show (show homObj k W T x ⟶ homObj k W T (x.1, y.2) from
          (rightFamily k W T x.1).E i (snd_step (RD₁ := RD₁) (y := y) i h)) ⟶ _ from
        (rightFamily k W T x.1).dot i (snd_step (RD₁ := RD₁) (y := y) i h))

/-- The crossings: those of `W` for two `RD₁` colours, those of the reverse of `T` for two `RD₂`
colours, and the associators `(f ≫ X) ≫ g ≅ f ≫ (X ≫ g)` for colours of different sides. -/
def prodCross : ∀ (c d : I₁ ⊕ I₂) {a b c' d' : X₁ × X₂} (h₁ : a + (RD₁.prod RD₂).iX d = b)
    (h₂ : b + (RD₁.prod RD₂).iX c = d') (h₃ : a + (RD₁.prod RD₂).iX c = c')
    (h₄ : c' + (RD₁.prod RD₂).iX d = d'),
    prodE k W T d h₁ ≫ prodE k W T c h₂ ⟶ prodE k W T c h₃ ≫ prodE k W T d h₄
  | .inl i, .inl j, (a₁, a₂), (b₁, b₂), (c₁, c₂), (d₁, d₂), h₁, h₂, h₃, h₄ => by
    obtain rfl := inl_snd j h₁
    obtain rfl := inl_snd i h₃
    obtain rfl := inl_snd i h₂
    exact (leftFamily k W T a₂).cross i j (fst_step (RD₂ := RD₂) j h₁)
      (fst_step (RD₂ := RD₂) i h₂) (fst_step (RD₂ := RD₂) i h₃) (fst_step (RD₂ := RD₂) j h₄)
  | .inr i, .inr j, (a₁, a₂), (b₁, b₂), (c₁, c₂), (d₁, d₂), h₁, h₂, h₃, h₄ => by
    obtain rfl := inr_fst j h₁
    obtain rfl := inr_fst i h₃
    obtain rfl := inr_fst i h₂
    exact (rightFamily k W T a₁).cross i j (snd_step (RD₁ := RD₁) j h₁)
      (snd_step (RD₁ := RD₁) i h₂) (snd_step (RD₁ := RD₁) i h₃) (snd_step (RD₁ := RD₁) j h₄)
  | .inl i, .inr j, (a₁, a₂), (b₁, b₂), (c₁, c₂), (d₁, d₂), h₁, h₂, h₃, h₄ => by
    obtain rfl := inr_fst j h₁
    obtain rfl := inl_snd i h₂
    obtain rfl := inl_snd i h₃
    obtain rfl := inr_fst j h₄
    exact ObjectProperty.homMk (associatorNatIsoMiddle
      (T.E j (neg_reg j (snd_step (RD₁ := RD₁) j h₁))) (W.E i (fst_step (RD₂ := RD₂) i h₃))).hom
  | .inr i, .inl j, (a₁, a₂), (b₁, b₂), (c₁, c₂), (d₁, d₂), h₁, h₂, h₃, h₄ => by
    obtain rfl := inl_snd j h₁
    obtain rfl := inr_fst i h₂
    obtain rfl := inr_fst i h₃
    obtain rfl := inl_snd j h₄
    exact ObjectProperty.homMk (associatorNatIsoMiddle
      (T.E i (neg_reg i (snd_step (RD₁ := RD₁) i h₃))) (W.E j (fst_step (RD₂ := RD₂) j h₁))).inv

variable {k W T}

theorem prodE_inl (i : I₁) {x₁ y₁ : X₁} {x₂ : X₂}
    (h : (x₁, x₂) + (RD₁.prod RD₂).iX (.inl i) = (y₁, x₂)) :
    prodE k W T (.inl i) h = (leftFamily k W T x₂).E i (fst_step i h) := rfl

theorem prodE_inr (i : I₂) {x₁ : X₁} {x₂ y₂ : X₂}
    (h : (x₁, x₂) + (RD₁.prod RD₂).iX (.inr i) = (x₁, y₂)) :
    prodE k W T (.inr i) h = (rightFamily k W T x₁).E i (snd_step i h) := rfl

variable (k W T) in
/-- **The Rouquier family on the categories `Hom_B(T(-x₂), W(x₁))`**, for the product root datum:
`RD₁` colours act by postcomposition with `W`, `RD₂` colours by precomposition with `T`. -/
def homProduct : RouqFamily (B := LinearCat.{w', w, v} k) (RD₁.prod RD₂) where
  obj := homObj k W T
  E := prodE k W T
  F := prodF k W T
  adj := prodAdj k W T
  dot := prodDot k W T
  cross := prodCross k W T
  square := by
    rintro (i | i) ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ h₁ h₂
    · obtain rfl := inl_snd i h₁
      obtain rfl := inl_snd i h₂
      exact (leftFamily k W T a₂).square i (fst_step (RD₂ := RD₂) i h₁)
        (fst_step (RD₂ := RD₂) i h₂)
    · obtain rfl := inr_fst i h₁
      obtain rfl := inr_fst i h₂
      exact (rightFamily k W T a₁).square i (snd_step (RD₁ := RD₁) i h₁)
        (snd_step (RD₁ := RD₁) i h₂)
  braid := by
    rintro (i | i) ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ h₁ h₂ h₃
    · obtain rfl := inl_snd i h₁
      obtain rfl := inl_snd i h₂
      obtain rfl := inl_snd i h₃
      exact (leftFamily k W T a₂).braid i (fst_step (RD₂ := RD₂) i h₁)
        (fst_step (RD₂ := RD₂) i h₂) (fst_step (RD₂ := RD₂) i h₃)
    · obtain rfl := inr_fst i h₁
      obtain rfl := inr_fst i h₂
      obtain rfl := inr_fst i h₃
      exact (rightFamily k W T a₁).braid i (snd_step (RD₁ := RD₁) i h₁)
        (snd_step (RD₁ := RD₁) i h₂) (snd_step (RD₁ := RD₁) i h₃)
  loc := by
    rintro (i | i) ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ h₁ h₂
    · obtain rfl := inl_snd i h₁
      obtain rfl := inl_snd i h₂
      exact ((leftFamily k W T a₂).loc i (fst_step (RD₂ := RD₂) i h₁)
        (fst_step (RD₂ := RD₂) i h₂)).ofWeight (by simp)
    · obtain rfl := inr_fst i h₁
      obtain rfl := inr_fst i h₂
      exact ((rightFamily k W T a₁).loc i (snd_step (RD₁ := RD₁) i h₁)
        (snd_step (RD₁ := RD₁) i h₂)).ofWeight (by simp)

end Family

end RouqFamily

end Categorification.TwoRep
