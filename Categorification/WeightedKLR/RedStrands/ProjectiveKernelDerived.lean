/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedSequence

/-!
# Derived braid vanishing when the retained kernel is projective

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
A projective kernel already has vanishing outside degree zero, so the
dimension shift uses just the ordinary balanced inclusion at the source.
-/


open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w u v

variable {I : Type u} {k : Type v} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
variable (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ) (κ : List (Fin ℓ))

local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν κ)
local notation "K" => blockLoadingKernel Q Λ t a b
local notation "F" => braidingFunctor k Q Λ ν (redWord t) κ

variable [HasDerivedCategory.{w, max u v}
    (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t)).Cornerᵐᵒᵖ]
  [HasDerivedCategory.{w, max u v}
    (isIdempotentElem_violMk_redProj k Q Λ ν κ).Cornerᵐᵒᵖ]

set_option backward.isDefEq.respectTransparency false in
/-- A projective loading kernel is braid-acyclic away from zero. -/
theorem blockLoadingKernel_braid_homology_vanish_of_projective
    (hP : Module.Projective Tᵐᵒᵖ K) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      ((F).obj (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj
        (ModuleCat.of Tᵐᵒᵖ K))))) := by
  let : Module.Projective Tᵐᵒᵖ K := hP
  let M := OpBimodule T (braidingBimodule k Q Λ ν (redWord t) κ)
  let e := derivedTensorObjIso (A := Uᵐᵒᵖ) (B := Tᵐᵒᵖ) (M := M)
    («P» := DGModuleCat.of Tᵐᵒᵖ (InDegreeZero K))
    (show IsKProjective Tᵐᵒᵖ (InDegreeZero K) from InDegreeZero.isKProjective)
  let Z := DGModuleCat.of Uᵐᵒᵖ (TensorProductOver Tᵐᵒᵖ (InDegreeZero M) (InDegreeZero K))
  have hZ : IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      (DG.DerivedCategory.Q.obj Z)) := by
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
/-- With a projective kernel, the ordinary balanced inclusion suffices for
braid cohomology of the actual partial standard to be concentrated in degree zero. -/
theorem blockPartialStandard_braid_homology_vanish_of_projective_kernel
    (hP : Module.Projective Tᵐᵒᵖ K)
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ t a b κ))
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      ((F).obj (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj
        (blockLoadingShortComplex Q Λ t a b).X₃)))) := by
  refine blockPartialStandard_braid_homology_vanish Q Λ t a b κ
    (L := fun _ : Unit => ModuleCat.of Tᵐᵒᵖ K) (m := [()])
    (ModuleFiltration.HasFiltration.single (LinearEquiv.refl _ _)) ?_ hbal n hn
  intro _ _ j hj
  exact blockLoadingKernel_braid_homology_vanish_of_projective Q Λ t a b κ hP j hj

end Categorification.Stendhal.BraidedStendhalAlgebra
