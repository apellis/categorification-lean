/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Localization.LocallySmall
import Categorification.CategoryTheory.PiAbelian
import DG.Derived.ComparisonRing
import DG.Derived.Coproducts
import DG.Derived.KProjective

/-!
# Idempotent completeness of derived categories of rings

M. Bökstedt and A. Neeman, *Homotopy limits in triangulated categories*, Compositio Math. 86
(1993), Proposition 3.2 (see also A. Neeman, *Triangulated categories*, Ann. of Math. Studies
148 (2001), Proposition 1.6.8): in a pretriangulated category with countable coproducts,
idempotents split.

* `Pretriangulated.isIdempotentComplete_of_hasCountableCoproducts`: the general statement. For an
  idempotent `e` of `X`, let `d = 1 - s` on `T = ∐_n X`, where `s` sends the summand `n` to the
  summand `n + 1` by `e`, and complete `d` to a distinguished triangle `T → T → Y → T⟦1⟧`.
  The morphism `d` has a left inverse, so the third morphism of the triangle vanishes. The
  morphism `T → X` which is `e` on every summand kills `d`, hence factors through `Y`, and
  together with the inclusion of the summand `0` it splits `e` through `Y`.
* `DerivedCategory.moduleCat_hasCoproducts`: the derived category of modules over a ring has
  coproducts indexed by the universe of the ring, through the comparison with the derived
  category of dg modules (`DG.DegreeZero.derivedComparisonEquivalence`, `DG.DerivedCategory`).
* `DerivedCategory.moduleCat_isIdempotentComplete`: hence it is idempotent complete.
* `DerivedCategory.smallModuleCat`: a model of the derived category of modules over a ring in
  `Type u` whose morphisms lie in `Type u` (Mathlib's standard construction has morphisms in
  `Type (u + 1)`), from the local smallness of the derived category of dg modules.
* `Pi.isIdempotentComplete`, `Pi.hasFiniteBiproducts`: both properties pass to products of
  categories.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category CategoryTheory.Preadditive

universe w v u

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Split

variable {X : C} (e : X ⟶ X) [HasCoproduct fun _ : ℕ => X]

/-- The shift `∐_n X ⟶ ∐_n X`, which is `e` from the summand `n` to the summand `n + 1`. -/
noncomputable def idemShift : (∐ fun _ : ℕ => X) ⟶ ∐ fun _ : ℕ => X :=
  Sigma.desc fun n => e ≫ Sigma.ι (fun _ : ℕ => X) (n + 1)

/-- A left inverse of `1 - idemShift e`, for an idempotent `e`: on the summand `m` it is
`(1 - e) ι_m - ∑_{n < m} e ι_n`. -/
noncomputable def idemShiftRetraction : (∐ fun _ : ℕ => X) ⟶ ∐ fun _ : ℕ => X :=
  Sigma.desc fun m => (𝟙 X - e) ≫ Sigma.ι (fun _ : ℕ => X) m -
    ∑ n ∈ Finset.range m, e ≫ Sigma.ι (fun _ : ℕ => X) n

omit [Preadditive C] in
theorem ι_idemShift (n : ℕ) :
    Sigma.ι (fun _ : ℕ => X) n ≫ idemShift e = e ≫ Sigma.ι (fun _ : ℕ => X) (n + 1) :=
  Sigma.ι_comp_desc _ _

theorem ι_idemShiftRetraction (m : ℕ) :
    Sigma.ι (fun _ : ℕ => X) m ≫ idemShiftRetraction e =
      (𝟙 X - e) ≫ Sigma.ι (fun _ : ℕ => X) m -
        ∑ n ∈ Finset.range m, e ≫ Sigma.ι (fun _ : ℕ => X) n :=
  Sigma.ι_comp_desc _ _

theorem sub_idemShift_comp_retraction (he : e ≫ e = e) :
    (𝟙 _ - idemShift e) ≫ idemShiftRetraction e = 𝟙 _ := by
  refine Sigma.hom_ext _ _ fun m => ?_
  rw [← assoc, comp_sub, comp_id, sub_comp, ι_idemShift, assoc, ι_idemShiftRetraction,
    ι_idemShiftRetraction]
  simp only [Finset.sum_range_succ, comp_sub, comp_add, comp_sum, sub_comp, ← assoc, he,
    id_comp, sub_self]
  abel

end Split

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- **Idempotents split in a pretriangulated category with countable coproducts** (Bökstedt and
Neeman, Compositio Math. 86 (1993), Proposition 3.2; Neeman, *Triangulated categories*,
Proposition 1.6.8). -/
theorem isIdempotentComplete_of_hasCountableCoproducts [HasCountableCoproducts C] :
    IsIdempotentComplete C := by
  refine ⟨fun X e he => ?_⟩
  let ι := Sigma.ι (fun _ : ℕ => X)
  obtain ⟨Y, π, δ, hT⟩ := distinguished_cocone_triangle (𝟙 _ - idemShift e)
  let σ : (∐ fun _ : ℕ => X) ⟶ X := Sigma.desc fun _ => e
  have hσ : (𝟙 _ - idemShift e) ≫ σ = 0 := by
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [comp_zero, ← assoc, comp_sub, comp_id, ι_idemShift, sub_comp, assoc]
    simp only [σ, Sigma.ι_comp_desc, he, sub_self]
  obtain ⟨r, hr⟩ : ∃ r : Y ⟶ X, σ = π ≫ r := Triangle.yoneda_exact₂ _ hT σ hσ
  have hδ : δ = 0 := by
    have h := comp_distTriang_mor_zero₃₁ _ hT
    calc δ = δ ≫ (shiftFunctor C (1 : ℤ)).map
          ((𝟙 _ - idemShift e) ≫ idemShiftRetraction e) := by
            rw [sub_idemShift_comp_retraction e he, Functor.map_id, comp_id]
      _ = 0 := by
            rw [Functor.map_comp, ← assoc]
            exact (congrArg (· ≫ _) h).trans (zero_comp)
  have hπ : ∀ n, ι n ≫ π = e ≫ ι (n + 1) ≫ π := by
    intro n
    have h := congrArg (ι n ≫ ·) (comp_distTriang_mor_zero₁₂ _ hT)
    simp only [comp_zero] at h
    change ι n ≫ (𝟙 _ - idemShift e) ≫ π = 0 at h
    rw [← assoc, comp_sub, comp_id, ι_idemShift, sub_comp, assoc, sub_eq_zero] at h
    exact h
  have heπ : ∀ n, e ≫ ι n ≫ π = ι n ≫ π := by
    intro n
    rw [hπ n, ← assoc, he]
  have hall : ∀ n, ι n ≫ π = ι 0 ≫ π := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [← heπ (n + 1), ← hπ n, ih]
  have hri : r ≫ ι 0 ≫ π = 𝟙 Y := by
    have h0 : π ≫ (r ≫ ι 0 ≫ π - 𝟙 Y) = 0 := by
      refine Sigma.hom_ext _ _ fun n => ?_
      change ι n ≫ π ≫ (r ≫ ι 0 ≫ π - 𝟙 Y) = ι n ≫ 0
      rw [comp_zero, comp_sub, comp_sub, comp_id, ← assoc π, ← hr, ← assoc, Sigma.ι_comp_desc,
        heπ 0, hall n, sub_self]
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ hT _ h0
    change _ = δ ≫ g at hg
    rw [hδ, zero_comp, sub_eq_zero] at hg
    exact hg
  refine ⟨Y, r, ι 0 ≫ π, hri, ?_⟩
  rw [assoc, ← hr]
  exact Sigma.ι_comp_desc _ _

end CategoryTheory.Pretriangulated

namespace CategoryTheory.Pi

variable {J : Type w} {C : J → Type u} [∀ j, Category.{v} (C j)]

/-- A product of idempotent complete categories is idempotent complete. -/
theorem isIdempotentComplete [∀ j, IsIdempotentComplete (C j)] :
    IsIdempotentComplete (∀ j, C j) := by
  refine ⟨fun X p hp => ?_⟩
  choose Y i e h₁ h₂ using fun j =>
    IsIdempotentComplete.idempotents_split (X j) (p j) (congrFun hp j)
  exact ⟨Y, i, e, funext h₁, funext h₂⟩

/-- A product of categories with finite products has finite products, componentwise. -/
theorem hasFiniteProducts_of_hasFiniteProducts [∀ j, HasFiniteProducts (C j)] :
    HasFiniteProducts (∀ j, C j) :=
  ⟨fun _ => ⟨fun _ => hasLimit_of_hasLimit_comp_eval _⟩⟩

end CategoryTheory.Pi

namespace DerivedCategory

open DG.DegreeZero

variable (S : Type u) [Ring S]

/-- **Coproducts in the derived category of modules over a ring**, indexed by the universe of
the ring, through the comparison with the derived category of dg modules
(`DG.DegreeZero.derivedComparisonEquivalence`, `DG.DerivedCategory.hasCoproducts`). -/
theorem moduleCat_hasCoproducts [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
    HasCoproducts.{u} (DerivedCategory (ModuleCat.{u} S)) := by
  let _ : DG.HasDerivedCategory S := DG.HasDerivedCategory.standard S
  intro J
  exact Adjunction.hasColimitsOfShape_of_equivalence (derivedComparisonEquivalence S).inverse

/-- **The derived category of modules over a ring is idempotent complete** (Bökstedt and Neeman,
Compositio Math. 86 (1993), Proposition 3.2): it has countable coproducts
(`moduleCat_hasCoproducts`). -/
theorem moduleCat_isIdempotentComplete [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
    IsIdempotentComplete (DerivedCategory (ModuleCat.{u} S)) :=
  have := moduleCat_hasCoproducts.{w} S
  Pretriangulated.isIdempotentComplete_of_hasCountableCoproducts

/-- The derived category of modules over a ring in `Type u` is locally `u`-small, by the
comparison with the derived category of dg modules (`DG.DerivedCategory.locallySmall`). -/
theorem moduleCat_locallySmall [HasDerivedCategory.{w} (ModuleCat.{u} S)] :
    LocallySmall.{u} (DerivedCategory (ModuleCat.{u} S)) := by
  let _ : DG.HasDerivedCategory S := DG.HasDerivedCategory.standard S
  have := DG.DerivedCategory.locallySmall.{_, u, u} (A := S)
  exact (locallySmall_congr (derivedComparisonEquivalence S)).1 this

/-- **A derived category of modules with small morphisms**: for a ring `S` in `Type u`, a
derived category of `S`-modules whose morphisms lie in `Type u`, obtained by shrinking the
morphisms of the standard construction (`moduleCat_locallySmall`). -/
@[instance_reducible]
noncomputable def smallModuleCat : HasDerivedCategory.{u} (ModuleCat.{u} S) :=
  letI : HasDerivedCategory (ModuleCat.{u} S) := HasDerivedCategory.standard _
  have := moduleCat_locallySmall S
  MorphismProperty.hasLocalizationOfLocallySmall _ DerivedCategory.Q

end DerivedCategory
