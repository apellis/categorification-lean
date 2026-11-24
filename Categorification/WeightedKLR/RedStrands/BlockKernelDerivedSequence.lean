/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedHomology
import Categorification.Algebra.ProjectiveKProjective
import Categorification.Algebra.DerivedTensorFiltration
import Mathlib.LinearAlgebra.Quotient.Basic

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w u v

variable {I : Type u} {k : Type v} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ) (κ : List (Fin ℓ))

local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν κ)
local notation "P" => rIdeal (orderedLoadingIdem Q Λ t)
local notation "K" => blockLoadingKernel Q Λ t a b
local notation "F" => braidingFunctor k Q Λ ν (redWord t) κ

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary short exact presentation of the partial standard at `t`,
using the retained boundaries of the paired red block. -/
def blockLoadingShortComplex : ShortComplex (ModuleCat Tᵐᵒᵖ) :=
  let : AddCommGroup P := Submodule.addCommGroup P
  let : Module Tᵐᵒᵖ P := Submodule.module P
  let sub : K →ₗ[Tᵐᵒᵖ] P := (K).subtype
  let quot : (P : Type (max u v)) →ₗ[Tᵐᵒᵖ] ((P : Type (max u v)) ⧸ K) := (K).mkQ
  ShortComplex.mk (ModuleCat.ofHom sub) (ModuleCat.ofHom quot)
    (by
      rw [← ModuleCat.ofHom_comp]
      have h : quot.comp sub = 0 := (LinearMap.exact_subtype_mkQ K).linearMap_comp_eq_zero
      rw [h, ModuleCat.ofHom_zero])

set_option backward.isDefEq.respectTransparency false in
theorem blockLoadingShortComplex_shortExact :
    (blockLoadingShortComplex Q Λ t a b).ShortExact := by
  let : AddCommGroup P := Submodule.addCommGroup P
  let : Module Tᵐᵒᵖ P := Submodule.module P
  let S := blockLoadingShortComplex Q Λ t a b
  let : Mono S.f := (ModuleCat.mono_iff_injective _).mpr (K).subtype_injective
  let : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr (K).mkQ_surjective
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
    (LinearMap.exact_subtype_mkQ K)⟩

variable [HasDerivedCategory.{w, max u v}
    (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t)).Cornerᵐᵒᵖ]
  [HasDerivedCategory.{w, max u v}
    (isIdempotentElem_violMk_redProj k Q Λ ν κ).Cornerᵐᵒᵖ]

set_option backward.isDefEq.respectTransparency false in
/-- Applying the braid to the projective middle term of (6.21) has no
cohomology outside degree zero. -/
theorem blockLoadingProjective_braid_homology_vanish (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      ((F).obj (DG.DerivedCategory.Q.obj (DGModuleCat.of Tᵐᵒᵖ (InDegreeZero P))))) := by
  let : Module.Projective Tᵐᵒᵖ P := blockLoading_projective Q Λ t
  let M := OpBimodule T (braidingBimodule k Q Λ ν (redWord t) κ)
  let e := derivedTensorObjIso (A := Uᵐᵒᵖ) (B := Tᵐᵒᵖ) (M := M)
    («P» := DGModuleCat.of Tᵐᵒᵖ (InDegreeZero P))
    (show IsKProjective Tᵐᵒᵖ (InDegreeZero P) from InDegreeZero.isKProjective)
  let Z := DGModuleCat.of Uᵐᵒᵖ (TensorProductOver Tᵐᵒᵖ (InDegreeZero M) (InDegreeZero P))
  have hZ : IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj (DG.DerivedCategory.Q.obj Z)) := by
    let : Subsingleton (cocycles Z n) := ⟨fun x y => by
      apply Subtype.ext
      have hx := TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn (mem_cocycles.mp x.2).1
      have hy := TensorProductOver.eq_zero_of_mem_grading_inDegreeZero hn (mem_cocycles.mp y.2).1
      exact hx.trans hy.symm⟩
    let : Subsingleton (cohomology Z n) := (cohomology.mk_surjective Z n).subsingleton
    exact ModuleCat.isZero_iff_subsingleton.mpr
      ((cohomologyAddEquiv ℤ Z n).surjective.subsingleton)
  exact hZ.of_iso ((homologyFunctor ℤ n).mapIso e)

set_option backward.isDefEq.respectTransparency false in
/-- The (6.21) vanishing argument for the actual loading projective and its
partial-standard quotient. The geometric inputs are a higher-layer filtration
of the loading kernel and injectivity of its ordinary balanced map. -/
theorem blockPartialStandard_braid_homology_vanish {ι : Type*}
    {L : ι → ModuleCat (Tᵐᵒᵖ)} {m : List ι}
    (hK : ModuleFiltration.HasFiltration L m (ModuleCat.of Tᵐᵒᵖ K))
    (hL : ∀ c ∈ m, ∀ n : ℤ, n ≠ 0 → IsZero
      ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
        ((F).obj (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj (L c))))))
    (hi : Function.Injective (blockKernelTensorInclusion Q Λ t a b κ))
    (n : ℤ) (hn : n ≠ 0) : IsZero
      ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
        ((F).obj (DG.DerivedCategory.Q.obj
          ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj (blockLoadingShortComplex Q Λ t a b).X₃)))) := by
  apply isZero_derivedHomology_quotient_of_filtered_kernel (F)
    (blockLoadingShortComplex Q Λ t a b) (blockLoadingShortComplex_shortExact Q Λ t a b)
    hK hL (blockLoadingProjective_braid_homology_vanish Q Λ t κ) _ n hn
  exact blockKernelDerivedHomology_mono Q Λ t a b κ hi

set_option backward.isDefEq.respectTransparency false in
/-- The initial loading case of the induction in (6.21). When the higher
kernel is zero, the partial-standard quotient itself is projective. -/
theorem blockPartialStandard_braid_homology_vanish_of_bot
    (hK : K = ⊥) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      ((F).obj (DG.DerivedCategory.Q.obj
        ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj (blockLoadingShortComplex Q Λ t a b).X₃)))) := by
  let : AddCommGroup P := Submodule.addCommGroup P
  let : Module Tᵐᵒᵖ P := Submodule.module P
  let e := ((K).quotEquivOfEqBot hK).toModuleIso
  let G := degreeZeroModuleFunctor Tᵐᵒᵖ ⋙ DG.DerivedCategory.Q ⋙ F ⋙
    DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n
  have hp : IsZero (G.obj (ModuleCat.of Tᵐᵒᵖ (P : Type (max u v)))) :=
    blockLoadingProjective_braid_homology_vanish Q Λ t κ n hn
  change IsZero (G.obj (ModuleCat.of Tᵐᵒᵖ ((P : Type (max u v)) ⧸ K)))
  exact hp.of_iso (G.mapIso e)

end Categorification.Stendhal.BraidedStendhalAlgebra


