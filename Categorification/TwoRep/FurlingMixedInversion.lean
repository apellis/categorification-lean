/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.FurlingIntertwine
import Categorification.KLR.NcEvalHom
import Categorification.TwoRep.RouqFullCL

/-!
# Mixed inversion on the cover blocks of the furled action

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3,
Lemma `lem:g-action` and the crossing formulas `com0new`–`com0newerer`;
Brundan, *On the definition of Kac-Moody 2-category*, arXiv:1501.00350v1,
Definition 1.1, (1.6)–(1.7).

The right mate of a polynomial-weighted crossing is the cover mixed crossing
followed by the same polynomial in an upward dot and a right-adjoint dot.
Nilpotence survives taking right mates, so a unit constant term gives a unit
also on the mixed word. The formula is proved for inverse coefficients as well.

`Furling.isIso_mate_swapCell` handles distinct cover labels in both cases:
* distinct base colours: the coefficient is `P°`;
* equal base colours: it is the negative inverse of `ϖ_a(y₀) - ϖ_b(y₁)`.

`Furling.sameColour_mixedInversion` supplies exactly the pointwise hypothesis
needed by the mixed blocks of the same-colour Rouquier inversion matrices.
The assumptions are upward KLR relations, mixed inversion and nilpotent dots
of the **cover**. No mixed inversion of the furled action is assumed. Assembly
of the blocks, including discarded paths, is a separate step.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory

section Mate
variable {B : Type*} [Bicategory B]
  {a b c d : B} {g : a ⟶ c} {h : b ⟶ d}
  {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c}

/-- Moving an endomorphism of the bent strand around the upper cup. -/
theorem rightMate_pre_bent (A₁ : l₁ ⊣ r₁) (A₂ : l₂ ⊣ r₂)
    (τ : g ≫ l₂ ⟶ l₁ ≫ h) (x : l₂ ⟶ l₂) :
    mateEquiv A₁ A₂ (g ◁ x ≫ τ) =
      mateEquiv A₁ A₂ τ ≫ h ◁ conjugateEquiv A₂ A₂ x := by
  simp only [mateEquiv_apply', whiskerLeft_comp, comp_whiskerRight]
  symm
  calc
    _ = 𝟙 _ ⊗≫ (r₁ ≫ g) ◁ A₂.unit ⊗≫ r₁ ◁ τ ▷ r₂ ⊗≫
        (A₁.counit ▷ (h ≫ r₂) ≫ 𝟙 b ◁ (h ◁ conjugateEquiv A₂ A₂ x)) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (r₁ ≫ g) ◁ A₂.unit ⊗≫ r₁ ◁ τ ▷ r₂ ⊗≫
        ((r₁ ≫ l₁) ◁ (h ◁ conjugateEquiv A₂ A₂ x) ≫ A₁.counit ▷ (h ≫ r₂)) ⊗≫ 𝟙 _ := by
      rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ (r₁ ≫ g) ◁ A₂.unit ⊗≫
        r₁ ◁ (τ ▷ r₂ ≫ (l₁ ≫ h) ◁ conjugateEquiv A₂ A₂ x) ⊗≫
        A₁.counit ▷ (h ≫ r₂) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (r₁ ≫ g) ◁ A₂.unit ⊗≫
        r₁ ◁ ((g ≫ l₂) ◁ conjugateEquiv A₂ A₂ x ≫ τ ▷ r₂) ⊗≫
        A₁.counit ▷ (h ≫ r₂) ⊗≫ 𝟙 _ := by rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ (r₁ ≫ g) ◁ (A₂.unit ≫ l₂ ◁ conjugateEquiv A₂ A₂ x) ⊗≫
        r₁ ◁ τ ▷ r₂ ⊗≫ A₁.counit ▷ (h ≫ r₂) ⊗≫ 𝟙 _ := by bicategory
    _ = 𝟙 _ ⊗≫ (r₁ ≫ g) ◁ (A₂.unit ≫ x ▷ r₂) ⊗≫
        r₁ ◁ τ ▷ r₂ ⊗≫ A₁.counit ▷ (h ≫ r₂) ⊗≫ 𝟙 _ := by
      rw [unit_whiskerLeft_conjugateEquiv]
    _ = _ := by bicategory
variable [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]

/-- The mates equivalence is linear over the scalars. -/
def rightMateLinear (A₁ : l₁ ⊣ r₁) (A₂ : l₂ ⊣ r₂) :
    (g ≫ l₂ ⟶ l₁ ≫ h) →ₗ[k] (r₁ ≫ g ⟶ h ≫ r₂) where
  toFun := mateEquiv A₁ A₂
  map_add' x y := by
    simp only [Bicategory.mateEquiv_apply, Adjunction.homEquiv₁_apply,
      Adjunction.homEquiv₂_apply, AdditiveWhiskering.whiskerLeft_add,
      AdditiveWhiskering.add_whiskerRight, Preadditive.comp_add, Preadditive.add_comp]
  map_smul' c x := by
    simp only [Bicategory.mateEquiv_apply, Adjunction.homEquiv₁_apply,
      Adjunction.homEquiv₂_apply, source_whiskerLeft_smul, source_smul_whiskerRight,
      Linear.comp_smul, Linear.smul_comp, RingHom.id_apply]

/-- A polynomial in the two output dots passes through the mate, bending exactly
its second variable. The dot-slide hypothesis is the distinct-label KLR slide. -/
theorem rightMate_post_polynomial (A₁ : l₁ ⊣ r₁) (A₂ : l₂ ⊣ r₂)
    (x₁ : l₁ ⟶ l₁) (x₂ : l₂ ⟶ l₂) (z : h ⟶ h)
    (φ : MvPolynomial (Fin 2) k →ₐ[k] End (l₁ ≫ h))
    (ψ : MvPolynomial (Fin 2) k →ₐ[k] End (h ≫ r₂))
    (hφ₀ : φ (MvPolynomial.X 0) = l₁ ◁ z)
    (hφ₁ : φ (MvPolynomial.X 1) = x₁ ▷ h)
    (hψ₀ : ψ (MvPolynomial.X 0) = z ▷ r₂)
    (hψ₁ : ψ (MvPolynomial.X 1) = h ◁ conjugateEquiv A₂ A₂ x₂)
    (p : MvPolynomial (Fin 2) k) (τ : g ≫ l₂ ⟶ l₁ ≫ h)
    (hs : g ◁ x₂ ≫ τ = τ ≫ x₁ ▷ h) :
    mateEquiv A₁ A₂ (τ ≫ φ p) = mateEquiv A₁ A₂ τ ≫ ψ p := by
  induction p using MvPolynomial.induction_on generalizing τ with
  | C c =>
      rw [show φ (MvPolynomial.C c) = c • 𝟙 _ from φ.commutes c,
        show ψ (MvPolynomial.C c) = c • 𝟙 _ from ψ.commutes c]
      change mateEquiv A₁ A₂ (τ ≫ (c • 𝟙 _)) = mateEquiv A₁ A₂ τ ≫ (c • 𝟙 _)
      simp only [Linear.comp_smul, Category.comp_id]
      exact (rightMateLinear (k := k) A₁ A₂).map_smul c τ
  | add p q hp hq =>
      simp only [map_add]
      change mateEquiv A₁ A₂ (τ ≫ (φ p + φ q)) = mateEquiv A₁ A₂ τ ≫ (ψ p + ψ q)
      rw [Preadditive.comp_add, Preadditive.comp_add]
      exact ((rightMateLinear (k := k) A₁ A₂).map_add _ _).trans
        (congrArg₂ (· + ·) (hp τ hs) (hq τ hs))
  | mul_X p j ih =>
      rw [mul_comm p, map_mul, map_mul]
      change mateEquiv A₁ A₂ (τ ≫ (φ p ≫ φ (MvPolynomial.X j))) =
        mateEquiv A₁ A₂ τ ≫ (ψ p ≫ ψ (MvPolynomial.X j))
      rw [← Category.assoc, ← Category.assoc]
      have hs' : g ◁ x₂ ≫ (τ ≫ φ p) = (τ ≫ φ p) ≫ x₁ ▷ h := by
        rw [← Category.assoc, hs, Category.assoc]
        have hc := congrArg φ (mul_comm p (MvPolynomial.X 1))
        simp only [map_mul, hφ₁] at hc
        exact congrArg (τ ≫ ·) hc |>.trans (Category.assoc _ _ _).symm
      rw [← ih τ hs]
      fin_cases j
      · exact (congrArg (fun q : End (l₁ ≫ h) => mateEquiv A₁ A₂ ((τ ≫ φ p) ≫ q)) hφ₀).trans
          ((rightMate_post A₁ A₂ (τ ≫ φ p) z).trans
            (congrArg (fun q : End (h ≫ r₂) => mateEquiv A₁ A₂ (τ ≫ φ p) ≫ q) hψ₀.symm))
      · exact (congrArg (fun q : End (l₁ ≫ h) => mateEquiv A₁ A₂ ((τ ≫ φ p) ≫ q)) hφ₁).trans
          ((congrArg (mateEquiv A₁ A₂) hs'.symm).trans
            ((rightMate_pre_bent A₁ A₂ (τ ≫ φ p) x₂).trans
              (congrArg (fun q : End (h ≫ r₂) => mateEquiv A₁ A₂ (τ ≫ φ p) ≫ q) hψ₁.symm)))

/-- Units in the polynomial coefficient may be inverted before bending. -/
theorem rightMate_post_polynomial_inverse (A₁ : l₁ ⊣ r₁) (A₂ : l₂ ⊣ r₂)
    (x₁ : l₁ ⟶ l₁) (x₂ : l₂ ⟶ l₂) (z : h ⟶ h)
    (φ : MvPolynomial (Fin 2) k →ₐ[k] End (l₁ ≫ h))
    (ψ : MvPolynomial (Fin 2) k →ₐ[k] End (h ≫ r₂))
    (hφ₀ : φ (MvPolynomial.X 0) = l₁ ◁ z)
    (hφ₁ : φ (MvPolynomial.X 1) = x₁ ▷ h)
    (hψ₀ : ψ (MvPolynomial.X 0) = z ▷ r₂)
    (hψ₁ : ψ (MvPolynomial.X 1) = h ◁ conjugateEquiv A₂ A₂ x₂)
    (p : MvPolynomial (Fin 2) k) (hp : IsUnit (φ p)) (hq : IsUnit (ψ p))
    (τ : g ≫ l₂ ⟶ l₁ ≫ h) (hs : g ◁ x₂ ≫ τ = τ ≫ x₁ ▷ h) :
    mateEquiv A₁ A₂ (τ ≫ (Ring.inverse (φ p) : End (l₁ ≫ h))) =
      mateEquiv A₁ A₂ τ ≫ (Ring.inverse (ψ p) : End (h ≫ r₂)) := by
  have hc : Commute (φ (MvPolynomial.X 1)) (φ p) :=
    (Commute.all _ _).map φ.toRingHom
  have hc' : Commute (φ (MvPolynomial.X 1)) (Ring.inverse (φ p)) := by
    obtain ⟨u, hu⟩ := hp
    rw [← hu, Ring.inverse_unit]
    rw [← hu] at hc
    exact hc.units_inv_right
  have hs' : g ◁ x₂ ≫ (τ ≫ (Ring.inverse (φ p) : End (l₁ ≫ h))) =
      (τ ≫ (Ring.inverse (φ p) : End (l₁ ≫ h))) ≫ x₁ ▷ h := by
    rw [← Category.assoc, hs, Category.assoc]
    rw [hφ₁] at hc'
    exact congrArg (τ ≫ ·) hc'.eq.symm |>.trans (Category.assoc _ _ _).symm
  have H := rightMate_post_polynomial A₁ A₂ x₁ x₂ z φ ψ hφ₀ hφ₁ hψ₀ hψ₁ p _ hs'
  have hcancel : (Ring.inverse (φ p) : End (l₁ ≫ h)) ≫ φ p = 𝟙 _ :=
    congrArg End.asHom (Ring.mul_inverse_cancel _ hp)
  rw [Category.assoc, hcancel, Category.comp_id] at H
  have hcancel' : (ψ p : h ≫ r₂ ⟶ h ≫ r₂) ≫ (Ring.inverse (ψ p) : End (h ≫ r₂)) = 𝟙 _ :=
    congrArg End.asHom (Ring.inverse_mul_cancel _ hq)
  calc
    _ = (_ ≫ ψ p) ≫ (Ring.inverse (ψ p) : End (h ≫ r₂)) := by
      rw [Category.assoc, hcancel', Category.comp_id]
    _ = _ := by rw [← H]

end Mate

section Nilpotence
variable {B : Type*} [Bicategory B]
  [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {a b : B} {l : a ⟶ b} {r : b ⟶ a}

/-- Bending a nilpotent dot preserves nilpotence. -/
theorem isNilpotent_conjugate (A : l ⊣ r) (x : l ⟶ l)
    (hx : IsNilpotent (End.of x)) : IsNilpotent (End.of (conjugateEquiv A A x)) := by
  obtain ⟨N, hN⟩ := hx
  refine ⟨N, ?_⟩
  change (End.of (conjugateEquiv A A x) ^ N).asHom = 0
  rw [← powComp_eq_end_pow, ← RouqSl2Generic.rightMate_pow, powComp_eq_end_pow, hN]
  exact (RouqSl2Generic.rightMateAddEquiv A).map_zero

end Nilpotence

section PolynomialMates
variable {B : Type*} [Bicategory B]
  [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  {a b c d : B} {g : a ⟶ c} {h : b ⟶ d}
  {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c}

private theorem pair_commute {A : Type*} [Monoid A] {x y : A} (hc : Commute x y) :
    ∀ i j, Commute (![x, y] i) (![x, y] j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact hc
  · exact hc.symm
  · exact Commute.refl _

/-- Evaluation after bending: the first dot remains upward and the second is its
right-adjoint mate. -/
theorem rightMate_post_ncEval (A₁ : l₁ ⊣ r₁) (A₂ : l₂ ⊣ r₂)
    (x₁ : l₁ ⟶ l₁) (x₂ : l₂ ⟶ l₂) (z : h ⟶ h)
    (p : MvPolynomial (Fin 2) k) (τ : g ≫ l₂ ⟶ l₁ ≫ h)
    (hs : g ◁ x₂ ≫ τ = τ ≫ x₁ ▷ h) :
    mateEquiv A₁ A₂ (τ ≫ (KLR.ncEval ![End.of (l₁ ◁ z), End.of (x₁ ▷ h)] p : End _)) =
      mateEquiv A₁ A₂ τ ≫ (KLR.ncEval
        ![End.of (z ▷ r₂), End.of (h ◁ conjugateEquiv A₂ A₂ x₂)] p : End _) := by
  obtain ⟨φ, hφ, eφ⟩ := KLR.exists_algHom_ncEval (k := k)
    ![End.of (l₁ ◁ z), End.of (x₁ ▷ h)] (pair_commute (whisker_exchange x₁ z).symm)
  obtain ⟨ψ, hψ, eψ⟩ := KLR.exists_algHom_ncEval (k := k)
    ![End.of (z ▷ r₂), End.of (h ◁ conjugateEquiv A₂ A₂ x₂)]
    (pair_commute (whisker_exchange z (conjugateEquiv A₂ A₂ x₂)))
  exact (congrArg (fun q : End _ => mateEquiv A₁ A₂ (τ ≫ q)) (eφ p)).trans
    ((rightMate_post_polynomial A₁ A₂ x₁ x₂ z φ ψ (hφ 0) (hφ 1) (hψ 0) (hψ 1) p τ hs).trans
      (congrArg (fun q : End _ => mateEquiv A₁ A₂ τ ≫ q) (eψ p).symm))

/-- The coefficient dots on a mixed word are commuting and nilpotent. -/
theorem mixedDots_nilpotent (A₂ : l₂ ⊣ r₂) (x₂ : l₂ ⟶ l₂) (z : h ⟶ h)
    (hx : IsNilpotent (End.of x₂)) (hz : IsNilpotent (End.of z)) :
    ∀ i, IsNilpotent (![End.of (z ▷ r₂), End.of (h ◁ conjugateEquiv A₂ A₂ x₂)] i) := by
  intro i
  fin_cases i
  · obtain ⟨N, hN⟩ := hz
    refine ⟨N, ?_⟩
    change End.of (z ▷ r₂) ^ N = 0
    rw [whiskerRight_pow, hN]
    exact AdditiveWhiskering.zero_whiskerRight _ _ _
  · obtain ⟨N, hN⟩ := isNilpotent_conjugate A₂ x₂ hx
    refine ⟨N, ?_⟩
    change End.of (h ◁ conjugateEquiv A₂ A₂ x₂) ^ N = 0
    rw [whiskerLeft_pow, hN]
    exact AdditiveWhiskering.whiskerLeft_zero _ _ _

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- Unit constant terms remain units after bending the nilpotent dot variables. -/
theorem isUnit_mixed_ncEval (A₂ : l₂ ⊣ r₂) (x₂ : l₂ ⟶ l₂) (z : h ⟶ h)
    (hx : IsNilpotent (End.of x₂)) (hz : IsNilpotent (End.of z))
    (p : MvPolynomial (Fin 2) k) (hp : IsUnit (MvPolynomial.constantCoeff p)) :
    IsUnit (KLR.ncEval ![End.of (z ▷ r₂), End.of (h ◁ conjugateEquiv A₂ A₂ x₂)] p) :=
  KLR.isUnit_ncEval _ (pair_commute (A := End (h ≫ r₂))
    (whisker_exchange z (conjugateEquiv A₂ A₂ x₂)))
    (mixedDots_nilpotent A₂ x₂ z hx hz) p hp

/-- The same formula for the inverse of a polynomial unit. -/
theorem rightMate_post_ncEval_inverse (A₁ : l₁ ⊣ r₁) (A₂ : l₂ ⊣ r₂)
    (x₁ : l₁ ⟶ l₁) (x₂ : l₂ ⟶ l₂) (z : h ⟶ h)
    (p : MvPolynomial (Fin 2) k)
    (hp : IsUnit (KLR.ncEval ![End.of (l₁ ◁ z), End.of (x₁ ▷ h)] p))
    (hq : IsUnit (KLR.ncEval ![End.of (z ▷ r₂),
      End.of (h ◁ conjugateEquiv A₂ A₂ x₂)] p))
    (τ : g ≫ l₂ ⟶ l₁ ≫ h) (hs : g ◁ x₂ ≫ τ = τ ≫ x₁ ▷ h) :
    mateEquiv A₁ A₂ (τ ≫ (Ring.inverse
      (KLR.ncEval ![End.of (l₁ ◁ z), End.of (x₁ ▷ h)] p) : End _)) =
      mateEquiv A₁ A₂ τ ≫ (Ring.inverse (KLR.ncEval
        ![End.of (z ▷ r₂), End.of (h ◁ conjugateEquiv A₂ A₂ x₂)] p) : End _) := by
  obtain ⟨φ, hφ, eφ⟩ := KLR.exists_algHom_ncEval (k := k)
    ![End.of (l₁ ◁ z), End.of (x₁ ▷ h)] (pair_commute (whisker_exchange x₁ z).symm)
  obtain ⟨ψ, hψ, eψ⟩ := KLR.exists_algHom_ncEval (k := k)
    ![End.of (z ▷ r₂), End.of (h ◁ conjugateEquiv A₂ A₂ x₂)]
    (pair_commute (whisker_exchange z (conjugateEquiv A₂ A₂ x₂)))
  exact (congrArg (fun q : End (l₁ ≫ h) => mateEquiv A₁ A₂ (τ ≫ (Ring.inverse q : End (l₁ ≫ h)))) (eφ p)).trans
    ((rightMate_post_polynomial_inverse A₁ A₂ x₁ x₂ z φ ψ
      (hφ 0) (hφ 1) (hψ 0) (hψ 1) p ((eφ p) ▸ hp) ((eψ p) ▸ hq) τ hs).trans
      (congrArg (fun q : End (h ≫ r₂) => mateEquiv A₁ A₂ τ ≫ (Ring.inverse q : End (h ≫ r₂))) (eψ p).symm))

end PolynomialMates

namespace Furling
universe ux
open KLR.Unfurling
variable {k : Type*} [Field k]
  {J I : Type*} [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J}
  {Xc Yc : Type ux} [AddCommGroup Xc] [AddCommGroup Yc]
  {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc}
  {B : Type*} [Bicategory B] [∀ a b : B, Preadditive (a ⟶ b)] [AdditiveWhiskering B]
  [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  (S : RouqFamily (B := B) RDc)
  {P : I → I → MvPolynomial (Fin 2) k} (D : UnfurlingDatum k P J)

omit [DecidableEq J]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- The `P°` coefficient is still invertible on the mixed word. This is the
unit-series step in Webster, arXiv:1603.06311v3, Lemma `lem:g-action`, using
Brundan's distinct-label inversion (1.7) only for the cover action. -/
theorem isUnit_mixed_P (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y),
    IsNilpotent (End.of (S.dot c h)))
    {a b : J} (hab : D.π a ≠ D.π b) {x y z : Xc}
    (h₂ : y + RDc.iX b = z) (h₄ : x + RDc.iX a = z) :
    IsUnit (KLR.ncEval ![End.of (S.dot a h₄ ▷ S.F b h₂),
      End.of (S.E a h₄ ◁ conjugateEquiv (S.adj b h₂) (S.adj b h₂) (S.dot b h₂))]
        (D.unit a b)) :=
  isUnit_mixed_ncEval (S.adj b h₂) (S.dot b h₂) (S.dot a h₄) (hnil b h₂) (hnil a h₄)
    (D.unit a b) (isUnit_iff_ne_zero.mpr (D.unit_constantCoeff a b hab))

end Furling

namespace Furling
open KLR.Unfurling
universe ux' uk' uv' uo'
variable {k : Type uk'} [Field k] {J I : Type*} [DecidableEq J]
  {Cc : QuantumGroup.CartanDatum J} {Xc Yc : Type ux'}
  [AddCommGroup Xc] [AddCommGroup Yc] {RDc : QuantumGroup.UDot.WeightDatum Cc Xc Yc}
  (S : RouqFamily (B := LinearCat.{uk', uv', uo'} k) RDc)
  {P : I → I → MvPolynomial (Fin 2) k} (D : UnfurlingDatum k P J)
  (H : RouqUpKLR S (unfQ (k := k) D.arrows)) (hmix : BrundanMixedInversion S)
  (hnil : ∀ (c : J) {x y : Xc} (h : x + RDc.iX c = y), IsNilpotent (End.of (S.dot c h)))

include H hmix hnil in
/-- Each off-diagonal cover block of the mixed crossing of the furled action is
invertible. Distinct base colours use `P°`; distinct labels of the same base
colour use the negative inverse of the difference of their dot series.

Webster, arXiv:1603.06311v3, Lemma `lem:g-action` and formulas `com0new`–`com0newerer`;
Brundan, arXiv:1501.00350v1, (1.7). Mixed inversion is assumed only for the cover. -/
theorem isIso_mate_swapCell (same : Prop) [Decidable same] {a b : J}
    (hsame : same ↔ D.π a = D.π b) (hab : a ≠ b) {x y y' z : Xc}
    (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX b = z)
    (h₃ : x + RDc.iX b = y') (h₄ : y' + RDc.iX a = z) :
    IsIso (mateEquiv (S.adj b h₃) (S.adj b h₂) (swapCell S D same h₁ h₂ h₃ h₄)) := by
  have : IsIso (mateEquiv (S.adj b h₃) (S.adj b h₂) (S.cross b a h₁ h₂ h₃ h₄)) :=
    hmix b a hab.symm h₁ h₂ h₃ h₄
  have hs := H.slide_left b a hab.symm h₁ h₂ h₃ h₄
  by_cases hc : same
  · let p : MvPolynomial (Fin 2) k := pwAt D.pw a 0 - pwAt D.pw b 1
    have hp := isUnit_constantCoeff_pwAt_sub D (hsame.mp hc) hab
    have hp' : IsUnit (pairEval S h₃ h₄ p) :=
      KLR.isUnit_ncEval _ (pair_commute (pair_dots_commute S h₃ h₄))
        (pair_dots_nilpotent S hnil h₃ h₄) p hp
    have hq := isUnit_mixed_ncEval (S.adj b h₂) (S.dot b h₂) (S.dot a h₄)
      (hnil b h₂) (hnil a h₄) p hp
    have he := rightMate_post_ncEval_inverse (S.adj b h₃) (S.adj b h₂)
      (S.dot b h₃) (S.dot b h₂) (S.dot a h₄) p hp' hq (S.cross b a h₁ h₂ h₃ h₄) hs
    have := (isUnit_iff_isIso _).mp hq.ringInverse
    simp only [swapCell, ite_eq_left hc, ite_eq_right hab]
    change IsIso (mateEquiv (S.adj b h₃) (S.adj b h₂)
      (S.cross b a h₁ h₂ h₃ h₄ ≫ (-(Ring.inverse (pairEval S h₃ h₄ p) : End _))))
    rw [Preadditive.comp_neg]
    rw [show mateEquiv (S.adj b h₃) (S.adj b h₂)
        (-(S.cross b a h₁ h₂ h₃ h₄ ≫ (Ring.inverse (pairEval S h₃ h₄ p) : End _))) =
        -mateEquiv (S.adj b h₃) (S.adj b h₂)
          (S.cross b a h₁ h₂ h₃ h₄ ≫ (Ring.inverse (pairEval S h₃ h₄ p) : End _)) from
      (rightMateLinear (k := k) (S.adj b h₃) (S.adj b h₂)).map_neg _]
    apply (congrArg (fun f => IsIso (-f)) he).mpr
    have : IsIso (mateEquiv (S.adj b h₃) (S.adj b h₂) (S.cross b a h₁ h₂ h₃ h₄) ≫
        (Ring.inverse (KLR.ncEval ![End.of (S.dot a h₄ ▷ S.F b h₂),
          End.of (S.E a h₄ ◁ conjugateEquiv (S.adj b h₂) (S.adj b h₂) (S.dot b h₂))] p) : End _)) :=
      inferInstance
    have negIso {U V : S.obj y' ⟶ S.obj y} (f : U ⟶ V) [IsIso f] : IsIso (-f) := by
      refine ⟨⟨-inv f, ?_, ?_⟩⟩ <;> simp
    exact negIso _
  · have hd : D.π a ≠ D.π b := fun e => hc (hsame.mpr e)
    have hq := isUnit_mixed_P S D hnil hd h₂ h₄
    have := (isUnit_iff_isIso _).mp hq
    simp only [swapCell, ite_eq_right hc, pairEval]
    rw [rightMate_post_ncEval (S.adj b h₃) (S.adj b h₂)
      (S.dot b h₃) (S.dot b h₂) (S.dot a h₄) (D.unit a b) _ hs]
    infer_instance

include H hmix hnil in
/-- The pointwise unit–crossing–counit form of the preceding block inversion. -/
theorem isIso_mate_swapCell_app (same : Prop) [Decidable same] {a b : J}
    (hsame : same ↔ D.π a = D.π b) (hab : a ≠ b) {x y y' z : Xc}
    (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX b = z)
    (h₃ : x + RDc.iX b = y') (h₄ : y' + RDc.iX a = z) (M : (S.obj y' : Type uo')) :
    IsIso ((S.adj b h₂).unit.hom.app ((S.E a h₁).obj.obj ((S.F b h₃).obj.obj M)) ≫
      (S.F b h₂).obj.map ((swapCell S D same h₁ h₂ h₃ h₄).hom.app ((S.F b h₃).obj.obj M) ≫
        (S.E a h₄).obj.map ((S.adj b h₃).counit.hom.app M))) := by
  have := isIso_mate_swapCell S D H hmix hnil same hsame hab h₁ h₂ h₃ h₄
  have hi : IsIso ((mateEquiv (S.adj b h₃) (S.adj b h₂)
      (swapCell S D same h₁ h₂ h₃ h₄)).hom.app M) := inferInstance
  have e : (mateEquiv (S.adj b h₃) (S.adj b h₂)
      (swapCell S D same h₁ h₂ h₃ h₄)).hom.app M =
      (S.adj b h₂).unit.hom.app ((S.E a h₁).obj.obj ((S.F b h₃).obj.obj M)) ≫
        (S.F b h₂).obj.map ((swapCell S D same h₁ h₂ h₃ h₄).hom.app ((S.F b h₃).obj.obj M) ≫
          (S.E a h₄).obj.map ((S.adj b h₃).counit.hom.app M)) := by
    rw [mateEquiv_eq_comp]
    change (𝟙 _ ≫ _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _) = _
    simp only [Category.id_comp]
    change (S.adj b h₂).unit.hom.app ((S.E a h₁).obj.obj ((S.F b h₃).obj.obj M)) ≫
        (S.F b h₂).obj.map ((swapCell S D same h₁ h₂ h₃ h₄).hom.app ((S.F b h₃).obj.obj M)) ≫
        (S.F b h₂).obj.map ((S.E a h₄).obj.map ((S.adj b h₃).counit.hom.app M)) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact congrArg ((S.adj b h₂).unit.hom.app
      ((S.E a h₁).obj.obj ((S.F b h₃).obj.obj M)) ≫ ·)
      ((S.F b h₂).obj.map_comp
        ((swapCell S D same h₁ h₂ h₃ h₄).hom.app ((S.F b h₃).obj.obj M))
        ((S.E a h₄).obj.map ((S.adj b h₃).counit.hom.app M))).symm
  exact e ▸ hi

include H hmix hnil in
/-- The precise same-base-colour cover hypothesis for the mixed block in the
Rouquier inversion matrices. The two cover labels are distinct, although their
images under `π` coincide. This is not the distinct-base-colour assertion. -/
theorem sameColour_mixedInversion [DecidableEq I] (π : J → I) (hπ : ∀ a, π a = D.π a) :
    ∀ (j : I) (a b : J), a ≠ b → π a = j → π b = j → ∀ {x y y' z : Xc}
      (h₁ : x + RDc.iX a = y) (h₂ : y + RDc.iX b = z)
      (h₃ : x + RDc.iX b = y') (h₄ : y' + RDc.iX a = z) (M : (S.obj y' : Type uo')),
      IsIso ((S.adj b h₂).unit.hom.app ((S.E a h₁).obj.obj ((S.F b h₃).obj.obj M)) ≫
        (S.F b h₂).obj.map ((swapCell S D (j = j) h₁ h₂ h₃ h₄).hom.app ((S.F b h₃).obj.obj M) ≫
          (S.E a h₄).obj.map ((S.adj b h₃).counit.hom.app M))) := by
  intro j a b hab ha hb x y y' z h₁ h₂ h₃ h₄ M
  have hc : D.π a = D.π b := (hπ a).symm.trans ((ha.trans hb.symm).trans (hπ b))
  exact isIso_mate_swapCell_app S D H hmix hnil (j = j)
    ⟨fun _ => hc, fun _ => rfl⟩ hab h₁ h₂ h₃ h₄ M

end Furling
end Categorification.TwoRep

