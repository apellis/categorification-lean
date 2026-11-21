/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.AmbidextrousTrace

/-!
# Nondegenerate closing traces from separating morphisms

A variant of `AmbidextrousTrace.isNondegTrace_closeTraceIso` (Webster, arXiv:1309.3796v3,
proof of Theorem 3.18): instead of asking that each `G Y` be a retract of copies of `P`, it
suffices that the morphisms between `P` and `G Y` separate: every nonzero `P ⟶ G Y` has a
nonzero composite with some `G Y ⟶ P`, and every nonzero `G Y ⟶ P` has a nonzero composite with
some `P ⟶ G Y`. This holds for instance when `P` has endomorphism ring a field and all morphisms
are linear maps of vector spaces.
-/

namespace Categorification.AmbidextrousTrace

open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj₁ : F ⊣ G) (adj₂ : G ⊣ F)
  [Preadditive C] [Preadditive D]

/-- **Frobenius property from separating morphisms.** If the morphisms between `P` and each
`G Y` (with `S Y`) separate, the closing trace on `End X`, for `F P ≅ X`, is nondegenerate
against these `Y`. -/
theorem isNondegTrace_closeTraceIso_of_separating [G.Additive] (P : C) {X : D}
    (e : F.obj P ≅ X) (S : D → Prop)
    (hl : ∀ Y : D, S Y → ∀ f : P ⟶ G.obj Y, f ≠ 0 → ∃ π : G.obj Y ⟶ P, f ≫ π ≠ 0)
    (hr : ∀ Y : D, S Y → ∀ g : G.obj Y ⟶ P, g ≠ 0 → ∃ ι : P ⟶ G.obj Y, ι ≫ g ≠ 0) :
    IsNondegTrace P X (closeTraceIso adj₁ adj₂ P e) S := by
  refine ⟨fun Y hY a ha => ?_, fun Y hY b hb => ?_⟩
  · have ha' : e.hom ≫ a ≠ 0 := fun h0 => ha (by simpa using congrArg (e.inv ≫ ·) h0)
    have hA : adj₁.homEquiv P Y (e.hom ≫ a) ≠ 0 := by
      have : F.IsLeftAdjoint := ⟨_, ⟨adj₁⟩⟩
      intro h0
      apply ha'
      have := congrArg (adj₁.homEquiv P Y).symm h0
      simpa [Adjunction.homEquiv_counit] using this
    obtain ⟨π, hπ⟩ := hl Y hY _ hA
    refine ⟨adj₂.homEquiv Y P π ≫ e.hom, ?_⟩
    have := closeTrace_comp adj₁ adj₂ P Y (e.hom ≫ a) (adj₂.homEquiv Y P π)
    rw [Equiv.symm_apply_apply] at this
    simpa [closeTraceIso, ← this] using hπ
  · have hb' : b ≫ e.inv ≠ 0 := fun h0 => hb (by simpa using congrArg (· ≫ e.hom) h0)
    have hB : (adj₂.homEquiv Y P).symm (b ≫ e.inv) ≠ 0 := by
      have : F.IsRightAdjoint := ⟨_, ⟨adj₂⟩⟩
      intro h0
      apply hb'
      have := congrArg (adj₂.homEquiv Y P) h0
      simpa [Adjunction.homEquiv_unit] using this
    obtain ⟨ι, hι⟩ := hr Y hY _ hB
    refine ⟨e.inv ≫ (adj₁.homEquiv P Y).symm ι, ?_⟩
    have := closeTrace_comp adj₁ adj₂ P Y ((adj₁.homEquiv P Y).symm ι) (b ≫ e.inv)
    rw [Equiv.apply_symm_apply] at this
    simpa [closeTraceIso, ← this] using hι

end Categorification.AmbidextrousTrace
