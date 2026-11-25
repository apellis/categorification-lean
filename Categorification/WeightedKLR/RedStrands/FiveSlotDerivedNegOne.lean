/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedSequence
import Categorification.WeightedKLR.RedStrands.FiveSlotAllTopsBoundedSpectator

/-!
# Degree minus one of the five-slot braid

Webster, arXiv:1309.3796v2, Lemma 6.8 and (6.21).
The projective middle term and the degree-zero kernel monomorphism
give vanishing in degree minus one for every five-slot partial standard.
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

open QuantumGroup KL3.Diagram

variable {k : Type} [Field k] (D : CartanDatum Unit) (Λ : Fin 3 → Unit →₀ ℕ)
local notation "Qstd" => CL.qCL (CL.CLScalars.kl : CL.CLScalars D k)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "κ" => ([0, 2, 1] : List (Fin 3))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Qstd Λ ν₀ κ)

set_option backward.isDefEq.respectTransparency false in
/-- In the exchanged red order, degree minus one vanishes for every
five-slot source loading and arbitrary red weights at standard parameters. -/
theorem fiveSlot_partialStandard_braid_homology_negOne_all_tops_standard
    (t : Seq (stendhalWeight 3 ν₀))
    [HasDerivedCategory.{w, 0}
      (isIdempotentElem_violMk_redProj k Qstd Λ ν₀ (redWord t)).Cornerᵐᵒᵖ]
    [HasDerivedCategory.{w, 0} Uᵐᵒᵖ] (horder : redWord t = [0, 1, 2]) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ (-1)).obj
      ((braidingFunctor k Qstd Λ ν₀ (redWord t) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor
          (isIdempotentElem_violMk_redProj k Qstd Λ ν₀ (redWord t)).Cornerᵐᵒᵖ).obj
          (blockLoadingShortComplex Qstd Λ t 1 2).X₃)))) :=
  blockPartialStandard_braid_homology_negOne_vanish Qstd Λ t 1 2 κ
    (fiveSlot_blockKernelTensorInclusion_injective_all_tops_standard D Λ t horder)

end Categorification.Stendhal.BraidedStendhalAlgebra
