/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.GradedHomBicategory
import Categorification.TwoRep.Zigzag

/-!
# Adjunction bijections in each shifted degree

The finite-sum graded-Hom bicategory transports any given adjunction in degree zero.
Its ordinary adjunction identities then prove, degree by degree, the mutually inverse maps
`Hom(v ≫ u, y⟦d⟧) ≃ Hom(v, (y ≫ v)⟦d⟧)` for `u ⊣ v`. The forward map closes with the unit,
the inverse closes with the counit. Naturality holds even for a further shifted morphism.
This is a shifted-adjunction consumer of the actual bicategory, not a new coherence mixin.

The input adjunction is explicit. No new adjunction for a strong 2-representation, low-weight
foothold, or CL Prop. 3.9 is claimed. In particular the per-summand lower bound on gradedEnd
required by the boundedness route is neither assumed here nor deduced from weight bounds.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B]

namespace GradedHomBicat

variable {a b : B} {f : a ⟶ b} {g : b ⟶ a}

/-- The degree-zero inclusion preserves the left zigzag. -/
theorem leftZigzag_incl₂ (η : 𝟙 a ⟶ f ≫ g) (ε₀ : g ≫ f ⟶ 𝟙 b) :
    leftZigzag (f := of₁ f) (g := of₁ g) (incl₂ η : 𝟙 (of a) ⟶ of₁ f ≫ of₁ g)
      (incl₂ ε₀ : of₁ g ≫ of₁ f ⟶ 𝟙 (of b)) = incl₂ (leftZigzag η ε₀) := by
  rw [leftZigzag_eq, leftZigzag_eq]
  rw [incl₂_whiskerRight, associator_hom_eq, whiskerLeft_incl₂,
    ← incl₂_comp, ← incl₂_comp]

/-- The degree-zero inclusion preserves the right zigzag. -/
theorem rightZigzag_incl₂ (η : 𝟙 a ⟶ f ≫ g) (ε₀ : g ≫ f ⟶ 𝟙 b) :
    rightZigzag (f := of₁ f) (g := of₁ g) (incl₂ η : 𝟙 (of a) ⟶ of₁ f ≫ of₁ g)
      (incl₂ ε₀ : of₁ g ≫ of₁ f ⟶ 𝟙 (of b)) = incl₂ (rightZigzag η ε₀) := by
  rw [rightZigzag_eq, rightZigzag_eq]
  rw [whiskerLeft_incl₂, associator_inv_eq, incl₂_whiskerRight,
    ← incl₂_comp, ← incl₂_comp]

/-- An actual adjunction in the finite-sum graded-Hom bicategory, with unit and counit
in degree zero, obtained from the given adjunction of `B`. -/
def mapAdjunction (adj : f ⊣ g) : of₁ f ⊣ of₁ g where
  unit := incl₂ adj.unit
  counit := incl₂ adj.counit
  left_triangle := by
    rw [leftZigzag_incl₂, adj.left_triangle, incl₂_comp,
      leftUnitor_hom_eq, rightUnitor_inv_eq]
  right_triangle := by
    rw [rightZigzag_incl₂, adj.right_triangle, incl₂_comp,
      rightUnitor_hom_eq, leftUnitor_inv_eq]

end GradedHomBicat

open GradedHomBicat

variable {a b : B} {u : a ⟶ b} {v : b ⟶ a} (adj : u ⊣ v) {y : b ⟶ b}

/-- Close a shifted 2-morphism with the unit, without changing its degree. -/
def Θsh {d : ℤ} (φ : ShiftedHom (v ≫ u) y d) : ShiftedHom v (y ≫ v) d :=
  (ShiftedHom.mk₀ (0 : ℤ) rfl
    ((ρ_ v).inv ≫ v ◁ adj.unit ≫ (α_ v u v).inv)).comp
    (shWhiskerRight φ v) (add_zero d)

/-- Close a shifted 2-morphism with the counit, without changing its degree. -/
def Ξsh {d : ℤ} (ψ : ShiftedHom v (y ≫ v) d) : ShiftedHom (v ≫ u) y d :=
  (shWhiskerRight ψ u).comp
    (ShiftedHom.mk₀ (0 : ℤ) rfl
      ((α_ y v u).hom ≫ y ◁ adj.counit ≫ (ρ_ y).hom)) (zero_add d)

/-- The shifted construction is the ordinary adjunction map in the graded-Hom bicategory. -/
theorem of₂_Θsh {d : ℤ} (φ : ShiftedHom (v ≫ u) y d) :
    of₂ d (Θsh adj φ) = Θ₀ (mapAdjunction adj) (of₂ d φ) := by
  rw [Θsh, ← of₂_comp_of₂, ← incl₂_eq_of₂, incl₂_comp, incl₂_comp,
    ← of₂_whiskerRight]
  change (incl₂ (ρ_ v).inv ≫ incl₂ (v ◁ adj.unit) ≫ incl₂ (α_ v u v).inv) ≫
      of₂ d φ ▷ of₁ v = _
  rw [← rightUnitor_inv_eq, ← whiskerLeft_incl₂, ← associator_inv_eq]
  simp only [Θ₀, mapAdjunction, Category.assoc]

/-- The inverse shifted construction is also computed in the graded-Hom bicategory. -/
theorem of₂_Ξsh {d : ℤ} (ψ : ShiftedHom v (y ≫ v) d) :
    of₂ d (Ξsh adj ψ) = Ξ₀ (mapAdjunction adj) (of₂ d ψ) := by
  rw [Ξsh, ← of₂_comp_of₂, ← incl₂_eq_of₂, incl₂_comp, incl₂_comp,
    ← of₂_whiskerRight]
  rw [← associator_hom_eq, ← whiskerLeft_incl₂, ← rightUnitor_hom_eq]
  rfl

/-- The two shifted adjunction maps are mutually inverse, from the actual triangle identities. -/
theorem Ξsh_Θsh {d : ℤ} (φ : ShiftedHom (v ≫ u) y d) :
    Ξsh adj (Θsh adj φ) = φ := by
  apply of₂_injective d
  rw [of₂_Ξsh, of₂_Θsh, Ξ₀_Θ₀]

/-- The other inverse identity in every integer degree. -/
theorem Θsh_Ξsh {d : ℤ} (ψ : ShiftedHom v (y ≫ v) d) :
    Θsh adj (Ξsh adj ψ) = ψ := by
  apply of₂_injective d
  rw [of₂_Θsh, of₂_Ξsh, Θ₀_Ξ₀]

/-- The degree-preserving adjunction bijection for shifted 2-morphisms. -/
def shiftedHomEquiv (d : ℤ) : ShiftedHom (v ≫ u) y d ≃ ShiftedHom v (y ≫ v) d where
  toFun := Θsh adj
  invFun := Ξsh adj
  left_inv := Ξsh_Θsh adj
  right_inv := Θsh_Ξsh adj

/-- Closing against the identity gives shifted endomorphisms of the right adjoint.
This is the degree-`d` cap-to-endomorphism bijection needed for shifted mate calculus. -/
def shiftedEndEquiv (d : ℤ) : ShiftedHom (v ≫ u) (𝟙 b) d ≃ ShiftedHom v v d :=
  (shiftedHomEquiv (y := 𝟙 b) adj d).trans
    (Iso.homCongr (Iso.refl v) ((shiftFunctor (b ⟶ a) d).mapIso (λ_ v)))

/-- Naturality includes composition with a morphism of an arbitrary shifted degree. -/
theorem Θsh_comp {y' : b ⟶ b} {d e s : ℤ} (φ : ShiftedHom (v ≫ u) y d)
    (z : ShiftedHom y y' e) (h : e + d = s) :
    Θsh adj (φ.comp z h) = (Θsh adj φ).comp (shWhiskerRight z v) h := by
  apply of₂_injective s
  rw [of₂_Θsh, ← of₂_comp_of₂, Θ₀_comp, ← of₂_Θsh,
    of₂_whiskerRight, of₂_comp_of₂]

end Categorification.TwoRep
