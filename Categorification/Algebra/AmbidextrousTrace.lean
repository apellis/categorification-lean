/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Traces from ambidextrous adjunctions

Let `F : C ⥤ D` be both left and right adjoint to `G`. For an object `P` of `C`, closing an
endomorphism `a` of `F P` with the unit of `F ⊣ G` and the counit of `G ⊣ F` gives an
endomorphism `closeTrace a` of `P`. This is the trace used by Webster, arXiv:1309.3796v3,
proof of Theorem 3.18: there `P` is the cyclotomic quotient at the highest weight, whose
endomorphism ring is the ground field, and the trace closes a diagram on the right.

The trace of a composite is a composite of the two adjunction transposes
(`closeTrace_comp`). If every object `G Y` is a retract of a finite family of copies of `P`,
the pairing `(a, b) ↦ closeTrace (a ≫ b)` kills no nonzero morphism on either side
(`exists_closeTrace_comp_ne_zero_left`, `exists_closeTrace_comp_ne_zero_right`). Webster
derives Theorem 3.18 in the same way, from biadjointness of `E` and `F`.
-/

namespace Categorification.AmbidextrousTrace

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj₁ : F ⊣ G) (adj₂ : G ⊣ F)

/-- The trace of an endomorphism of `F P`: the unit of `F ⊣ G`, then `G a`, then the counit
of `G ⊣ F`. -/
def closeTrace (P : C) (a : F.obj P ⟶ F.obj P) : P ⟶ P :=
  adj₁.unit.app P ≫ G.map a ≫ adj₂.counit.app P

/-- The trace of `a ≫ b` is the composite of the transpose of `a` along `F ⊣ G` with the
transpose of `b` along `G ⊣ F`. -/
theorem closeTrace_comp (P : C) (Y : D) (a : F.obj P ⟶ Y) (b : Y ⟶ F.obj P) :
    closeTrace adj₁ adj₂ P (a ≫ b) =
      adj₁.homEquiv P Y a ≫ (adj₂.homEquiv Y P).symm b := by
  simp [closeTrace, Adjunction.homEquiv_unit, Adjunction.homEquiv_counit]

variable [Preadditive C]

/-- A morphism out of a retract of a finite family of copies of `P` is zero when all its
composites with the copies vanish. -/
theorem eq_zero_of_retract_left {P X Z : C} {n : ℕ} (ι : Fin n → (P ⟶ X))
    (π : Fin n → (X ⟶ P)) (h : ∑ k, π k ≫ ι k = 𝟙 X) (f : X ⟶ Z)
    (hf : ∀ k, ι k ≫ f = 0) : f = 0 := by
  calc f = 𝟙 X ≫ f := (Category.id_comp f).symm
    _ = 0 := by rw [← h, Preadditive.sum_comp]; simp [hf]

/-- A morphism into a retract of a finite family of copies of `P` is zero when all its
composites with the projections vanish. -/
theorem eq_zero_of_retract_right {P X Z : C} {n : ℕ} (ι : Fin n → (P ⟶ X))
    (π : Fin n → (X ⟶ P)) (h : ∑ k, π k ≫ ι k = 𝟙 X) (f : Z ⟶ X)
    (hf : ∀ k, f ≫ π k = 0) : f = 0 := by
  calc f = f ≫ 𝟙 X := (Category.comp_id f).symm
    _ = 0 := by rw [← h, Preadditive.comp_sum]; simp [← Category.assoc, hf]

variable [Preadditive D]

/-- Left nondegeneracy: if `G Y` is a retract of finitely many copies of `P`, every nonzero
`a : F P ⟶ Y` has `closeTrace (a ≫ b) ≠ 0` for some `b`. -/
theorem exists_closeTrace_comp_ne_zero_left (P : C) (Y : D) {n : ℕ}
    (ι : Fin n → (P ⟶ G.obj Y)) (π : Fin n → (G.obj Y ⟶ P))
    (h : ∑ k, π k ≫ ι k = 𝟙 (G.obj Y)) (a : F.obj P ⟶ Y) (ha : a ≠ 0) :
    ∃ b : Y ⟶ F.obj P, closeTrace adj₁ adj₂ P (a ≫ b) ≠ 0 := by
  have hA : adj₁.homEquiv P Y a ≠ 0 := by
    have : F.IsLeftAdjoint := ⟨_, ⟨adj₁⟩⟩
    intro h0
    apply ha
    have := congrArg (adj₁.homEquiv P Y).symm h0
    simpa [Adjunction.homEquiv_counit] using this
  by_contra hb
  push Not at hb
  apply hA
  refine eq_zero_of_retract_right ι π h _ (fun k => ?_)
  have := hb ((adj₂.homEquiv Y P) (π k))
  rw [closeTrace_comp, Equiv.symm_apply_apply] at this
  exact this

/-- Right nondegeneracy: if `G Y` is a retract of finitely many copies of `P`, every nonzero
`b : Y ⟶ F P` has `closeTrace (a ≫ b) ≠ 0` for some `a`. -/
theorem exists_closeTrace_comp_ne_zero_right (P : C) (Y : D) {n : ℕ}
    (ι : Fin n → (P ⟶ G.obj Y)) (π : Fin n → (G.obj Y ⟶ P))
    (h : ∑ k, π k ≫ ι k = 𝟙 (G.obj Y)) (b : Y ⟶ F.obj P) (hb : b ≠ 0) :
    ∃ a : F.obj P ⟶ Y, closeTrace adj₁ adj₂ P (a ≫ b) ≠ 0 := by
  have hB : (adj₂.homEquiv Y P).symm b ≠ 0 := by
    have : F.IsRightAdjoint := ⟨_, ⟨adj₂⟩⟩
    intro h0
    apply hb
    have := congrArg (adj₂.homEquiv Y P) h0
    simpa [Adjunction.homEquiv_unit] using this
  by_contra ha
  push Not at ha
  apply hB
  refine eq_zero_of_retract_left ι π h _ (fun k => ?_)
  have := ha ((adj₁.homEquiv P Y).symm (ι k))
  rw [closeTrace_comp, Equiv.apply_symm_apply] at this
  exact this

/-- An additive map `τ` on `End X` with values in `End P` is nondegenerate against the objects
`Y` with `S Y`: for nonzero `a : X ⟶ Y` some `τ (a ≫ b)` is nonzero, and for nonzero
`b : Y ⟶ X` some `τ (a ≫ b)` is nonzero. -/
def IsNondegTrace (P : C) (X : D) (τ : (X ⟶ X) →+ (P ⟶ P)) (S : D → Prop) : Prop :=
  (∀ (Y : D), S Y → ∀ a : X ⟶ Y, a ≠ 0 → ∃ b : Y ⟶ X, τ (a ≫ b) ≠ 0) ∧
    ∀ (Y : D), S Y → ∀ b : Y ⟶ X, b ≠ 0 → ∃ a : X ⟶ Y, τ (a ≫ b) ≠ 0

/-- A zero object carries the zero trace, vacuously nondegenerate. -/
theorem isNondegTrace_zero_of_id_eq_zero (P : C) {X : D} (hX : 𝟙 X = 0) (S : D → Prop) :
    IsNondegTrace P X 0 S := by
  refine ⟨fun Y _ a ha => (ha ?_).elim, fun Y _ b hb => (hb ?_).elim⟩
  · rw [← Category.id_comp a, hX, Limits.zero_comp]
  · rw [← Category.comp_id b, hX, Limits.comp_zero]

/-- The closing trace on `End X`, for an isomorphism `F P ≅ X`. -/
def closeTraceIso [G.Additive] (P : C) {X : D} (e : F.obj P ≅ X) : (X ⟶ X) →+ (P ⟶ P) where
  toFun a := closeTrace adj₁ adj₂ P (e.hom ≫ a ≫ e.inv)
  map_zero' := by simp [closeTrace]
  map_add' a b := by simp [closeTrace, Preadditive.add_comp, Preadditive.comp_add]

/-- **Frobenius property from an ambidextrous adjunction** (Webster, arXiv:1309.3796v3, proof
of Theorem 3.18). If `F ⊣ G ⊣ F`, `X ≅ F P` and the identity of `G Y` factors through finitely
many copies of `P` whenever `S Y`, the closing trace on `End X` is nondegenerate against the
objects `Y` with `S Y`. -/
theorem isNondegTrace_closeTraceIso [G.Additive] (P : C) {X : D} (e : F.obj P ≅ X)
    (S : D → Prop) (hgen : ∀ Y : D, S Y → ∃ (n : ℕ) (π : Fin n → (G.obj Y ⟶ P))
      (ι : Fin n → (P ⟶ G.obj Y)), ∑ k, π k ≫ ι k = 𝟙 (G.obj Y)) :
    IsNondegTrace P X (closeTraceIso adj₁ adj₂ P e) S := by
  refine ⟨fun Y hY a ha => ?_, fun Y hY b hb => ?_⟩
  · obtain ⟨n, π, ι, h⟩ := hgen Y hY
    have ha' : e.hom ≫ a ≠ 0 := fun h0 => ha (by simpa using congrArg (e.inv ≫ ·) h0)
    obtain ⟨b, hb⟩ := exists_closeTrace_comp_ne_zero_left adj₁ adj₂ P Y ι π h _ ha'
    refine ⟨b ≫ e.hom, ?_⟩
    simpa [closeTraceIso] using hb
  · obtain ⟨n, π, ι, h⟩ := hgen Y hY
    have hb' : b ≫ e.inv ≠ 0 := fun h0 => hb (by simpa using congrArg (· ≫ e.hom) h0)
    obtain ⟨a, ha⟩ := exists_closeTrace_comp_ne_zero_right adj₁ adj₂ P Y ι π h _ hb'
    refine ⟨e.inv ≫ a, ?_⟩
    simpa [closeTraceIso] using ha

end Categorification.AmbidextrousTrace
