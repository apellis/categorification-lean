/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedSequence

/-!
# Degree minus one of a braided partial standard

Webster, arXiv:1309.3796v2, Lemma 6.8 and (6.21).
The projective middle term and the degree-zero kernel monomorphism
give vanishing in degree minus one for a loading partial standard.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DG DG.DerivedCategory
open scoped DG.DegreeZero

universe w v u

section Triangle

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]
  [HasDerivedCategory.{w, v} A] [Algebra ℤ A] [DGAlgebra ℤ A]

private theorem isZero_homology_negOne_of_distinguished
    (T : Triangle (DerivedCategory.{w, v} A)) (hT : T ∈ distTriang (DerivedCategory.{w, v} A))
    (hP : IsZero ((homologyFunctor ℤ (-1)).obj T.obj₂))
    (h₀ : Mono ((homologyFunctor ℤ 0).map T.mor₁)) :
    IsZero ((homologyFunctor ℤ (-1)).obj T.obj₃) := by
  let H := homologyFunctor (A := A) ℤ 0
  let : (DG.HomotopyCategory.homologyFunctor.{v} ℤ A 0).ShiftSequence ℤ := by
    change (DG.HomotopyCategory.forget.{v} ℤ A ⋙
      _root_.HomotopyCategory.homologyFunctor (ModuleCat.{v} ℤ) (ComplexShape.up ℤ) 0).ShiftSequence ℤ
    infer_instance
  let : H.ShiftSequence ℤ := Functor.ShiftSequence.induced (homologyFunctorFactorsh ℤ 0) ℤ
    (homologyFunctor ℤ) (homologyFunctorFactorsh ℤ)
  have he (j : ℤ) : H.shift j = homologyFunctor ℤ j := rfl
  rw [← he]
  apply (H.homologySequence_exact₃ T hT (-1 : ℤ) 0 (by decide)).isZero_X₂
  · change (H.shift (-1)).map T.mor₂ = 0
    rw [he]
    exact hP.eq_of_src _ _
  · apply (H.homologySequence_mono_shift_map_mor₁_iff T hT (-1 : ℤ) 0 (by decide)).1
    rwa [he]

end Triangle

open KLR
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

section Loading

variable {I : Type u} {k : Type v} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
  (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ) (κ : List (Fin ℓ))

local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν κ)

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary balanced injectivity gives vanishing in degree minus one for
the braid of the actual loading partial standard. -/
theorem blockPartialStandard_braid_homology_negOne_vanish
    [HasDerivedCategory.{w, max u v} Tᵐᵒᵖ] [HasDerivedCategory.{w, max u v} Uᵐᵒᵖ]
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ t a b κ)) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ (-1)).obj
      ((braidingFunctor k Q Λ ν (redWord t) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj
          (blockLoadingShortComplex Q Λ t a b).X₃)))) := by
  let S := blockLoadingShortComplex Q Λ t a b
  let G := degreeZeroModuleFunctor Tᵐᵒᵖ
  let F := braidingFunctor k Q Λ ν (redWord t) κ
  let : F.CommShift ℤ := braidingFunctor_commShift k Q Λ ν (redWord t) κ
  have : F.IsTriangulated := braidingFunctor_isTriangulated k Q Λ ν (redWord t) κ
  have hS : (S.map G).ShortExact :=
    degreeZeroModuleFunctor_shortExact S (blockLoadingShortComplex_shortExact Q Λ t a b)
  obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact (S.map G) hS
  exact isZero_homology_negOne_of_distinguished _ (F.map_distinguished _ hT)
    (blockLoadingProjective_braid_homology_vanish Q Λ t κ (-1) (by decide))
    (blockKernelDerivedHomology_mono Q Λ t a b κ hbal)

end Loading

end Categorification.Stendhal.BraidedStendhalAlgebra
