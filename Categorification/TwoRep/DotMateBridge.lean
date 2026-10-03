import Categorification.TwoRep.StepLemmasNeg

/-!
# The original upward dot and its downward mate at the supplied cup

This is a local mate identity, not dot nondegeneracy. All shift removal is
through the published homogeneous shift isomorphism. The only adjunction
used is the supplied `S.adj`; no `AdjHyp` is manufactured.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
universe w v u

private theorem unit_conjugate {D : Type*} [Bicategory D] {a b : D}
    {f : a ⟶ b} {g : b ⟶ a} (adj : f ⊣ g) (t : f ⟶ f) :
    adj.unit ≫ f ◁ (Bicategory.conjugateEquiv adj adj t) =
      adj.unit ≫ t ▷ g := by
  have h := (Bicategory.mateEquiv_eq_iff adj adj
    ((λ_ f).hom ≫ t ≫ (ρ_ f).inv)
    (Bicategory.mateEquiv adj adj ((λ_ f).hom ≫ t ≫ (ρ_ f).inv))).mp rfl
  rw [Adjunction.homEquiv₁_symm_apply, Adjunction.homEquiv₂_apply] at h
  rw [Bicategory.conjugateEquiv_apply]
  calc
    _ = ((λ_ (𝟙 a)).inv ≫ adj.unit ▷ 𝟙 a ≫ (α_ f g (𝟙 a)).hom ≫
        f ◁ (Bicategory.mateEquiv adj adj ((λ_ f).hom ≫ t ≫ (ρ_ f).inv))) ≫
        f ◁ (λ_ g).hom := by bicategory
    _ = (((ρ_ (𝟙 a)).inv ≫ 𝟙 a ◁ adj.unit ≫ (α_ (𝟙 a) f g).inv ≫
        ((λ_ f).hom ≫ t ≫ (ρ_ f).inv) ▷ g) ≫ (α_ f (𝟙 b) g).hom) ≫
        f ◁ (λ_ g).hom := congrArg (fun z => z ≫ f ◁ (λ_ g).hom) h
    _ = _ := by bicategory

private theorem unit_conjugate_transport {D : Type*} [Bicategory D] {a b : D}
    {f : a ⟶ b} {g g' : b ⟶ a} (adj : f ⊣ g) (t : f ⟶ f) (e : g' ≅ g) :
    (adj.unit ≫ f ◁ e.inv) ≫ t ▷ g' =
      (adj.unit ≫ f ◁ e.inv) ≫
        f ◁ (e.hom ≫ Bicategory.conjugateEquiv adj adj t ≫ e.inv) := by
  simp only [whiskerLeft_comp, Category.assoc, whiskerLeft_inv_hom_assoc]
  rw [whisker_exchange, ← Category.assoc, ← unit_conjugate, Category.assoc]

private theorem whisker_unit_slide {D : Type*} [Bicategory D] {a b c : D}
    {f : a ⟶ b} {g : b ⟶ a} (v : a ⟶ c) (η : 𝟙 a ⟶ f ≫ g)
    (x : f ≫ g ⟶ f ≫ g) (y : g ⟶ g) (h : η ≫ x = η ≫ f ◁ y) :
    η ▷ v ≫ x ▷ v ≫ (α_ f g v).hom =
      η ▷ v ≫ (α_ f g v).hom ≫ f ◁ (y ▷ v) := by
  rw [← comp_whiskerRight_assoc, h, comp_whiskerRight_assoc,
    associator_naturality_middle]

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B]

open GradedHomBicat ShiftRemoval

/-- A homogeneous endomorphism slides through the supplied unit to its right mate. -/
theorem unit_mateSh {a b : B} {f : a ⟶ b} {g : b ⟶ a} (adj : f ⊣ g)
    {d : ℤ} (t : ShiftedHom f f d) :
    incl₂ adj.unit ≫ of₁ f ◁ of₂ d (mateSh adj t) =
      incl₂ adj.unit ≫ of₂ d t ▷ of₁ g := by
  rw [of₂_mateSh]
  exact unit_conjugate (mapAdjunction adj) (of₂ d t)

namespace StrongSl2
open CategoryTheory.Limits
variable {k : Type*} [Field k] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  (S : StrongSl2 k B)

/-- The original upward `dotFE` slides, at the supplied cup, to the actual
unshifted downward `fDot`. The homogeneous shift isomorphism is displayed;
no equality of the two endomorphisms of `FE` is asserted. -/
theorem suppliedCup_dotFE (r : ℤ) :
    (incl₂ (S.adj (r + 1)).unit ≫ of₁ (S.E (r + 1)) ◁
      (shiftIso (S.F (r + 1)) (S.n₀ + 2 * (r + 1) + 1)).inv) ≫
        of₂ 2 (S.dotFE r) =
    (incl₂ (S.adj (r + 1)).unit ≫ of₁ (S.E (r + 1)) ◁
      (shiftIso (S.F (r + 1)) (S.n₀ + 2 * (r + 1) + 1)).inv) ≫
        of₁ (S.E (r + 1)) ◁ of₂ 2 (S.fDot (r + 1)) := by
  have hf : of₂ 2 (S.fDot (r + 1)) =
      (shiftIso (S.F (r + 1)) (S.n₀ + 2 * (r + 1) + 1)).hom ≫
        of₂ 2 (S.mateDot (r + 1)) ≫
      (shiftIso (S.F (r + 1)) (S.n₀ + 2 * (r + 1) + 1)).inv := by
    simpa [fDot, removeIso, of₂] using
      homOf_remove (Iso.refl (S.adjointF (r + 1))) (S.mateDot (r + 1))
  rw [hf, dotFE, ← of₂_whiskerRight]
  change _ = _ ≫ of₁ (S.E (r + 1)) ◁ (_ ≫
    of₂ 2 (mateSh (S.adj (r + 1)) (S.dot (r + 1))) ≫ _)
  rw [of₂_mateSh]
  exact unit_conjugate_transport (mapAdjunction (S.adj (r + 1)))
    (of₂ 2 (S.dot (r + 1)))
    (shiftIso (S.F (r + 1)) (S.n₀ + 2 * (r + 1) + 1))

/-- After right whiskering by `F r`, the original upward dot on `FE` becomes
exactly the first-factor downward dot on `FF` at the supplied cup. The latter
is the map in `exists_F2_dot`. This is an equality in the actual graded-Hom
bicategory, with its actual associator; it is not an equality on arbitrary
summand inclusions of a chosen `FEDecomp`. -/
theorem suppliedCup_dotFE_whisker_F (r : ℤ) :
    (incl₂ (S.adj (r + 1)).unit ≫ of₁ (S.E (r + 1)) ◁
      (shiftIso (S.F (r + 1)) (S.n₀ + 2 * (r + 1) + 1)).inv) ▷ of₁ (S.F r) ≫
      of₂ 2 (shWhiskerRight (S.dotFE r) (S.F r)) ≫
      (α_ (of₁ (S.E (r + 1))) (of₁ (S.F (r + 1))) (of₁ (S.F r))).hom =
    (incl₂ (S.adj (r + 1)).unit ≫ of₁ (S.E (r + 1)) ◁
      (shiftIso (S.F (r + 1)) (S.n₀ + 2 * (r + 1) + 1)).inv) ▷ of₁ (S.F r) ≫
      (α_ (of₁ (S.E (r + 1))) (of₁ (S.F (r + 1))) (of₁ (S.F r))).hom ≫
      of₁ (S.E (r + 1)) ◁ of₂ 2 (shWhiskerRight (S.fDot (r + 1)) (S.F r)) := by
  rw [← of₂_whiskerRight, ← of₂_whiskerRight]
  exact whisker_unit_slide (of₁ (S.F r)) _ _ _ (S.suppliedCup_dotFE r)

end StrongSl2
end Categorification.TwoRep
