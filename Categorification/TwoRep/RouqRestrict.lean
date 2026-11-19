/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqFullCL

/-!
# Restricting a Rouquier family to a subdatum

Brundan, arXiv:1501.00350v1, Definition 1.1. Let `S` be a Rouquier family for a
weight datum `W` of a Cartan datum `C'` on `I'`, let `e : I → I'` and let `RD` be a
weight datum of a Cartan datum `C` on `I` whose roots are those of `W` along `e`.
For a base weight `o` with `⟨i, o + x⟩_W = ⟨i, x⟩_RD` for all `i` and `x`, the
objects `S.obj (o + x)`, the 1-morphisms `E_{e i}` and the dots and crossings of
colours in the image of `e` form a Rouquier family for `RD` (`RouqFamily.restrict`).
Its left adjunctions are those of `S` (`restrict_adjL`).

This is used for Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29: the black
part of the cyclotomic action of the enlarged Cartan datum.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory QuantumGroup UDot

universe w v u u₁

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  {I I' : Type*} {C : CartanDatum I} {C' : CartanDatum I'} {X Y : Type u₁}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y} {W : WeightDatum C' X Y}

/-- The data of a restriction: the colour map, the roots, the base weight and the pairings. -/
structure RestrictData (RD : WeightDatum C X Y) (W : WeightDatum C' X Y) where
  /-- The colour map. -/
  e : I → I'
  /-- The base weight. -/
  o : X
  /-- The roots agree. -/
  iX : ∀ i, RD.iX i = W.iX (e i)
  /-- The pairings agree after the shift by `o`. -/
  pair : ∀ i x, RD.pair (RD.iY i) x = W.pair (W.iY (e i)) (o + x)
  /-- Distinct colours stay distinct. -/
  inj : Function.Injective e

namespace RestrictData

variable (D : RestrictData RD W)

theorem step (i : I) {x y : X} (h : x + RD.iX i = y) : D.o + x + W.iX (D.e i) = D.o + y := by
  rw [← h, D.iX, add_assoc]

end RestrictData

namespace RouqLoc

variable {a b c : B} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}

/-- Transport of the weight of local Rouquier data. -/
def cast {h h' : ℤ} (e : h = h') (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) :
    RouqLoc adj₁ adj₂ x₁ x₂ τ h' :=
  e ▸ L

variable [AdditiveWhiskering B] {d : B} {E₃ : c ⟶ d} {R₃ : d ⟶ c} {adj₃ : E₃ ⊣ R₃}
  {x₃ : E₃ ⟶ E₃} {τ₂₃ : E₂ ≫ E₃ ⟶ E₂ ≫ E₃}

/-- The left adjunction does not see transports of the weights. -/
theorem leftAdjunction_cast {h h' g g' : ℤ} (e : h = h') (e' : g = g')
    (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h) (U : RouqLoc adj₂ adj₃ x₂ x₃ τ₂₃ g)
    (hw : g = h + 2) (hw' : g' = h' + 2) (hsq : τ ≫ τ = 0) (hsq' : τ₂₃ ≫ τ₂₃ = 0)
    (hB : E₁ ◁ τ₂₃ ≫ ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ =
      ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom) ≫ E₁ ◁ τ₂₃ ≫
        ((α_ E₁ E₂ E₃).inv ≫ τ ▷ E₃ ≫ (α_ E₁ E₂ E₃).hom)) :
    (L.cast e).leftAdjunction (U.cast e') hw' hsq hsq' hB = L.leftAdjunction U hw hsq hsq' hB := by
  subst e e'
  rfl

end RouqLoc

namespace RouqFamily

variable (S : RouqFamily (B := B) W) (D : RestrictData RD W)

/-- **The restriction of a Rouquier family** along a restriction datum. -/
def restrict : RouqFamily (B := B) RD where
  obj x := S.obj (D.o + x)
  E i _ _ h := S.E (D.e i) (D.step i h)
  dot i _ _ h := S.dot (D.e i) (D.step i h)
  cross i j _ _ _ _ h₁ h₂ h₃ h₄ :=
    S.cross (D.e i) (D.e j) (D.step j h₁) (D.step i h₂) (D.step i h₃) (D.step j h₄)
  F i _ _ h := S.F (D.e i) (D.step i h)
  adj i _ _ h := S.adj (D.e i) (D.step i h)
  square i _ _ _ h₁ h₂ := S.square (D.e i) (D.step i h₁) (D.step i h₂)
  braid i _ _ _ _ h₁ h₂ h₃ := S.braid (D.e i) (D.step i h₁) (D.step i h₂) (D.step i h₃)
  loc i _ b _ h₁ h₂ := RouqLoc.cast (D.pair i b).symm (S.loc (D.e i) (D.step i h₁) (D.step i h₂))

variable [AdditiveWhiskering B]

/-- The left adjunctions of the restriction are those of the family. -/
theorem restrict_adjL (i : I) {x y : X} (h : x + RD.iX i = y) :
    (S.restrict D).adjL i h = S.adjL (D.e i) (D.step i h) := by
  rw [S.adjL_eq (D.e i) (D.step i (sub_add_cancel x (RD.iX i))) (D.step i h)
    (D.step i (rfl : y + RD.iX i = y + RD.iX i))]
  exact RouqLoc.leftAdjunction_cast _ _ _ _ _ _ _ _ _

end RouqFamily

section KLR

variable {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  (S : RouqFamily (B := B) W) (D : RestrictData RD W)

/-- Brundan's upward KLR equations (arXiv:1501.00350v1, Definition 1.1) restrict along an
injective colour map, with the restricted polynomials. -/
theorem RouqUpKLR.restrict {Q' : I' → I' → MvPolynomial (Fin 2) k}
    {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q')
    (hQ : ∀ i j, i ≠ j → Q' (D.e i) (D.e j) = Q i j) :
    RouqUpKLR (S.restrict D) Q where
  square i j hij _ _ _ _ h₁ h₂ h₃ h₄ := by
    rw [← hQ i j hij]
    exact H.square (D.e i) (D.e j) (D.inj.ne hij) _ _ _ _
  slide_left i j hij _ _ _ _ h₁ h₂ h₃ h₄ :=
    H.slide_left (D.e i) (D.e j) (D.inj.ne hij) _ _ _ _
  slide_right i j hij _ _ _ _ h₁ h₂ h₃ h₄ :=
    H.slide_right (D.e i) (D.e j) (D.inj.ne hij) _ _ _ _
  braid i j c hb _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 :=
    H.braid (D.e i) (D.e j) (D.e c) (D.inj.ne hb) _ _ _ _ _ _ _ _ _ _ _ _
  braidQ i j hij _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ := by
    rw [← hQ i j hij]
    exact H.braidQ (D.e i) (D.e j) (D.inj.ne hij) _ _ _ _ _ _ _

/-- Invertibility of the mixed sideways crossings restricts. -/
theorem BrundanMixedInversion.restrict (M : BrundanMixedInversion S) :
    BrundanMixedInversion (S.restrict D) :=
  fun i j hij _ _ _ _ _ _ _ _ => M (D.e i) (D.e j) (D.inj.ne hij) _ _ _ _

end KLR

end Categorification.TwoRep
