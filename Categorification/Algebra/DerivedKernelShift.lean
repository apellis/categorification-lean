/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorFiltration

/-!
# Dimension shift to the kernel of a short exact sequence

For a triangulated functor `F` and a short exact sequence `0 → K → P → N → 0` of modules in
degree zero: if `F N` and `F P` are concentrated in degree zero and `F P → F N` is onto in degree
zero, then `F K` is concentrated in degree zero and `F K → F P` is injective in degree zero.
Iterating this along a finite projective resolution of `N` shows that applying `F` (for example
a derived tensor product with a bimodule) keeps every short exact sequence of the resolution
exact once `F N` is concentrated in degree zero. Webster uses this to compute the braiding
functor on Grothendieck groups from its values on standard modules (arXiv:1309.3796v2, §6.1,
proof of Corollary 6.10).

## Main results

* `DG.DerivedCategory.isZero_homology_obj₁_of_concentrated_triangle`
* `DG.DerivedCategory.mono_homology_mor₁_of_isZero_obj₃`
* `DG.DerivedCategory.isZero_homology_kernel_of_shortExact`,
  `DG.DerivedCategory.mono_homology_kernel_of_shortExact`: the two statements for the image of a
  short exact sequence of modules in degree zero.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

namespace DG.DerivedCategory

universe w v u r

section Triangle

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{w, v} A]
  (R : Type r) [CommRing R] [Algebra R A] [DGAlgebra R A]

noncomputable local instance : (homologyFunctor (A := A) R 0).ShiftSequence ℤ := by
  letI : (HomotopyCategory.homologyFunctor.{v} R A 0).ShiftSequence ℤ := by
    change (HomotopyCategory.forget.{v} R A ⋙
      _root_.HomotopyCategory.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) 0).ShiftSequence ℤ
    infer_instance
  exact Functor.ShiftSequence.induced (homologyFunctorFactorsh R 0) ℤ
    (homologyFunctor R) (homologyFunctorFactorsh R)

/-- A triangle whose second and third terms are concentrated in degree zero, with the second map
onto in degree zero, has its first term concentrated in degree zero. -/
theorem isZero_homology_obj₁_of_concentrated_triangle
    (T : Triangle (DerivedCategory.{w, v} A)) (hT : T ∈ distTriang (DerivedCategory.{w, v} A))
    (hP : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor R n).obj T.obj₂))
    (hN : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor R n).obj T.obj₃))
    (h₀ : Epi ((homologyFunctor R 0).map T.mor₂))
    (n : ℤ) (hn : n ≠ 0) : IsZero ((homologyFunctor R n).obj T.obj₁) := by
  let F := homologyFunctor (A := A) R 0
  have e (j : ℤ) : F.shift j = homologyFunctor R j := rfl
  rw [← e]
  apply (F.homologySequence_exact₁ T hT (n - 1) n (by lia)).isZero_X₂
  · by_cases h : n - 1 = 0
    · have h₀' : Epi ((F.shift (n - 1)).map T.mor₂) := by rw [e, h]; exact h₀
      exact (F.homologySequence_epi_shift_map_mor₂_iff T hT (n - 1) n (by lia)).1 h₀'
    · have h' : IsZero ((F.shift (n - 1)).obj T.obj₃) := by rw [e]; exact hN _ h
      exact h'.eq_of_src _ _
  · change (F.shift n).map T.mor₁ = 0
    rw [e]
    exact (hP n hn).eq_of_tgt _ _

/-- In a triangle whose third term has no cohomology in degree `-1`, the first map is injective in
degree zero. -/
theorem mono_homology_mor₁_of_isZero_obj₃
    (T : Triangle (DerivedCategory.{w, v} A)) (hT : T ∈ distTriang (DerivedCategory.{w, v} A))
    (hN : IsZero ((homologyFunctor R (-1)).obj T.obj₃)) :
    Mono ((homologyFunctor R 0).map T.mor₁) := by
  let F := homologyFunctor (A := A) R 0
  have e (j : ℤ) : F.shift j = homologyFunctor R j := rfl
  change Mono ((F.shift (0 : ℤ)).map T.mor₁)
  apply (F.homologySequence_mono_shift_map_mor₁_iff T hT (-1) 0 (by lia)).2
  have h' : IsZero ((F.shift (-1)).obj T.obj₃) := by rw [e]; exact hN
  exact h'.eq_of_src _ _

end Triangle

section ShortExact

variable {A B : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] [HasDerivedCategory.{w, v} A]
  [Ring B] [DGAddCommGroup B] [DGRing B] [HasDerivedCategory.{w, v} B]
  (R : Type r) [CommRing R] [Algebra R A] [DGAlgebra R A]

/-- Dimension shift to the kernel: for a short exact sequence `K → P → N` of dg modules, if `F P`
and `F N` are concentrated in degree zero and `F P → F N` is onto in degree zero, then `F K` is
concentrated in degree zero. -/
theorem isZero_homology_kernel_of_shortExact
    (F : DerivedCategory.{w, v} B ⥤ DerivedCategory.{w, v} A)
    [F.CommShift ℤ] [F.IsTriangulated] (S : ShortComplex (DGModuleCat.{v} B)) (hS : S.ShortExact)
    (hP : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor R n).obj (F.obj (Q.obj S.X₂))))
    (hN : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor R n).obj (F.obj (Q.obj S.X₃))))
    (h₀ : Epi ((homologyFunctor R 0).map (F.map (Q.map S.g))))
    (n : ℤ) (hn : n ≠ 0) : IsZero ((homologyFunctor R n).obj (F.obj (Q.obj S.X₁))) := by
  obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact S hS
  exact isZero_homology_obj₁_of_concentrated_triangle R _ (F.map_distinguished _ hT) hP hN h₀ n hn

/-- For a short exact sequence `K → P → N` of dg modules with `F N` having no cohomology in degree
`-1`, the map `F K → F P` is injective in degree zero. -/
theorem mono_homology_kernel_of_shortExact
    (F : DerivedCategory.{w, v} B ⥤ DerivedCategory.{w, v} A)
    [F.CommShift ℤ] [F.IsTriangulated] (S : ShortComplex (DGModuleCat.{v} B)) (hS : S.ShortExact)
    (hN : IsZero ((homologyFunctor R (-1)).obj (F.obj (Q.obj S.X₃)))) :
    Mono ((homologyFunctor R 0).map (F.map (Q.map S.f))) := by
  obtain ⟨δ, hT⟩ := exists_distinguished_of_shortExact S hS
  exact mono_homology_mor₁_of_isZero_obj₃ R _ (F.map_distinguished _ hT) hN

end ShortExact

end DG.DerivedCategory
