/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DG.Derived.DimensionShift

/-!
# Connecting morphisms for derived cohomology

The homology sequence of a distinguished triangle identifies the
connecting morphism with an isomorphism or with the inclusion of a
kernel when the relevant cohomology objects of the middle term vanish.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DG.DerivedCategory

universe w v u r

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{w, v} A]
  (R : Type r) [CommRing R] [Algebra R A] [DGAlgebra R A]

noncomputable local instance : (homologyFunctor (A := A) R 0).ShiftSequence ℤ := by
  let : (HomotopyCategory.homologyFunctor.{v} R A 0).ShiftSequence ℤ := by
    change (HomotopyCategory.forget.{v} R A ⋙
      _root_.HomotopyCategory.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) 0).ShiftSequence ℤ
    infer_instance
  exact Functor.ShiftSequence.induced (homologyFunctorFactorsh R 0) ℤ
    (homologyFunctor R) (homologyFunctorFactorsh R)

variable (T : Triangle (DerivedCategory.{w, v} A))
  (hT : T ∈ distTriang (DerivedCategory.{w, v} A))

/-- The connecting morphism is an isomorphism when both neighboring
cohomology objects of the middle term vanish. -/
noncomputable def homologyShiftIso (n : ℤ)
    (h₀ : IsZero ((homologyFunctor R n).obj T.obj₂))
    (h₁ : IsZero ((homologyFunctor R (n + 1)).obj T.obj₂)) :
    (homologyFunctor R n).obj T.obj₃ ≅ (homologyFunctor R (n + 1)).obj T.obj₁ := by
  let F := homologyFunctor (A := A) R 0
  let δ := F.homologySequenceδ T n (n + 1) rfl
  have : Mono δ := (F.homologySequence_exact₃ T hT n (n + 1) rfl).mono_g_iff.mpr
    (h₀.eq_of_src _ _)
  have : Epi δ := (F.homologySequence_exact₁ T hT n (n + 1) rfl).epi_f_iff.mpr
    (h₁.eq_of_tgt _ _)
  letI : IsIso δ := isIso_of_mono_of_epi δ
  exact (asIso δ : (F.shift n).obj T.obj₃ ≅ (F.shift (n + 1)).obj T.obj₁)

/-- If the middle term has zero cohomology in degree `n`, the connecting morphism
identifies the third term's degree-`n` cohomology with the kernel of the next map. -/
noncomputable def homologyShiftKernelIso (n : ℤ)
    (h₀ : IsZero ((homologyFunctor R n).obj T.obj₂)) :
    (homologyFunctor R n).obj T.obj₃ ≅
      kernel ((homologyFunctor R (n + 1)).map T.mor₁) := by
  let F := homologyFunctor (A := A) R 0
  let δ := F.homologySequenceδ T n (n + 1) rfl
  have : Mono δ := (F.homologySequence_exact₃ T hT n (n + 1) rfl).mono_g_iff.mpr
    (h₀.eq_of_src _ _)
  let h := (F.homologySequence_exact₁ T hT n (n + 1) rfl).fIsKernel
  exact IsLimit.conePointUniqueUpToIso h (limit.isLimit _)

/-- The two homology maps of a distinguished triangle form an exact pair. -/
theorem homology_distinguished_pair_exact (T : Triangle (DerivedCategory.{w, v} A))
    (hT : T ∈ distTriang _) (n : ℤ)
    (hzero : (homologyFunctor R n).map T.mor₁ ≫ (homologyFunctor R n).map T.mor₂ = 0) :
    (ShortComplex.mk ((homologyFunctor R n).map T.mor₁)
      ((homologyFunctor R n).map T.mor₂) hzero).Exact :=
  (homologyFunctor (A := A) R 0).homologySequence_exact₂ T hT n

/-- Vanishing of the underlying integral homology implies vanishing over
any chosen central scalar ring. -/
theorem isZero_homology_of_isZero_intHomology
    (D : DerivedCategory.{w, v} A) (n : ℤ)
    (h : IsZero ((homologyFunctor (A := A) ℤ n).obj D)) :
    IsZero ((homologyFunctor R n).obj D) := by
  let : (Qh (A := A)).EssSurj := Localization.essSurj _ (HomotopyCategory.quasiIso A)
  let : (Q (A := A)).EssSurj := by unfold Q; infer_instance
  let X := (Q (A := A)).objPreimage D
  let e : Q.obj X ≅ D := (Q (A := A)).objObjPreimageIso D
  have hZ : IsZero ((homologyFunctor ℤ n).obj (Q.obj X)) :=
    h.of_iso ((homologyFunctor ℤ n).mapIso e)
  let : Subsingleton ((homologyFunctor ℤ n).obj (Q.obj X)) :=
    ModuleCat.isZero_iff_subsingleton.mp hZ
  let : Subsingleton (cohomology X n) := (cohomologyAddEquiv ℤ X n).injective.subsingleton
  have hs : Subsingleton ((homologyFunctor R n).obj (Q.obj X)) :=
    (cohomologyAddEquiv R X n).symm.injective.subsingleton
  exact (ModuleCat.isZero_iff_subsingleton.mpr hs).of_iso
    ((homologyFunctor R n).mapIso e).symm

end DG.DerivedCategory
