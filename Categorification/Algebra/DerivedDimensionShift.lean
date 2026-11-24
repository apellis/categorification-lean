/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Category.Derived.Basic
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Cohomological dimension shift for Webster's derived tensor calculation

In the proof of (6.21) in Lemma 6.8, Webster uses the cohomology long exact sequence
for a triangle obtained by applying the derived braid functor to a short exact sequence.
Pointwise in the dg category, concentration in degree zero for the first two terms
and a monomorphism on their degree-zero cohomology imply concentration in degree zero
for the third term.

Reference: B. Webster, *Knot invariants and higher representation theory*,
[arXiv:1309.3796v2](https://arxiv.org/abs/1309.3796v2), Lemma 6.8, proof of (6.21).
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DG.CatModule.DerivedCategory

universe w' w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [∀ X Y : C, DG.DGAddCommGroup (X ⟶ Y)] [DG.DGCategory C] [HasDerivedCategory.{w', w} C]

noncomputable local instance (X : C) : (cohomologyFunctor (C := C) X 0).ShiftSequence ℤ := by
  letI : (HomotopyCategory.cohomologyFunctor.{w} X 0).ShiftSequence ℤ := by
    change (HomotopyCategory.eval.{w} X ⋙
      _root_.HomotopyCategory.homologyFunctor AddCommGrpCat.{w} (ComplexShape.up ℤ) 0).ShiftSequence ℤ
    infer_instance
  exact Functor.ShiftSequence.induced (cohomologyFunctorFactorsh X 0) ℤ
    (cohomologyFunctor X) (cohomologyFunctorFactorsh X)

/-- Pointwise dimension shift for Webster, arXiv:1309.3796v2, Lemma 6.8, proof of (6.21). A
triangle with the first two terms concentrated in degree zero has its third term concentrated
in degree zero when the induced map in degree zero is a monomorphism. -/
theorem isZero_cohomology_obj₃_of_concentrated_triangle (X : C)
    (T : Triangle (DerivedCategory.{w', w} C)) (hT : T ∈ distTriang (DerivedCategory.{w', w} C))
    (hK : ∀ n : ℤ, n ≠ 0 → IsZero ((cohomologyFunctor X n).obj T.obj₁))
    (hP : ∀ n : ℤ, n ≠ 0 → IsZero ((cohomologyFunctor X n).obj T.obj₂))
    (h₀ : Mono ((cohomologyFunctor X 0).map T.mor₁))
    (n : ℤ) (hn : n ≠ 0) : IsZero ((cohomologyFunctor X n).obj T.obj₃) := by
  let F := cohomologyFunctor (C := C) X 0
  have e (j : ℤ) : F.shift j = cohomologyFunctor X j := rfl
  rw [← e]
  apply (F.homologySequence_exact₃ T hT n (n + 1) rfl).isZero_X₂
  · change (F.shift n).map T.mor₂ = 0
    rw [e]
    exact (hP n hn).eq_of_src _ _
  · change F.homologySequenceδ T n (n + 1) rfl = 0
    by_cases h : n + 1 = 0
    · apply (F.homologySequence_mono_shift_map_mor₁_iff T hT n (n + 1) rfl).1
      rwa [e, h]
    · have h' : IsZero ((F.shift (n + 1)).obj T.obj₁) := by rw [e]; exact hK _ h
      exact h'.eq_of_tgt _ _

end DG.CatModule.DerivedCategory
