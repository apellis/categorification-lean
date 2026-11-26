/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorCoefficientCovers
import Categorification.Algebra.DerivedTensorDegreeZero
import Categorification.Algebra.ExactDerivedTensor
import Categorification.Algebra.ProjectiveResolutionDGProjective

/-!
# Derived tensor products with a projective coefficient

If the coefficient `M` is projective as a right `B`-module, then `M ⊗ᴸ_B X` of an ordinary
module `X` is the ordinary tensor product, concentrated in degree `0`
(`isZero_derivedTensorHomology_projective_coefficient`).

Combined with `isZero_derivedTensorHomology_of_orderedStandardCovers`, this gives the Tor
vanishing of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, proof of Lemma 6.11 (step `f_n → s_n`) from its degree-zero part:
`isZero_derivedTensorHomology_of_orderedStandardCovers_resolution`.
-/

open CategoryTheory CategoryTheory.Limits DG DG.DegreeZero DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w u

section Projective

variable {A B : Type u} [Ring A] [Ring B] [HasDerivedCategory.{w, u} A]
  [HasDerivedCategory.{w, u} B]
  (M : Type u) [AddCommGroup M] [Module A M] [Module Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [Module.Projective Bᵐᵒᵖ M]

/-- **A projective coefficient gives no higher Tor**: for `M` projective as a right
`B`-module and a dg module `P` quasi-isomorphic to an ordinary module `X`, the derived tensor
`M ⊗ᴸ P` vanishes in every nonzero degree. -/
theorem isZero_derivedTensorHomology_projective_coefficient {P : DGModuleCat.{u} B}
    (X : Type u) [AddCommGroup X] [Module B X] (f : P ⟶ DGModuleCat.of B (InDegreeZero X))
    (hf : f.hom.IsQuasiIso) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor ℤ n).obj ((derivedTensor.{w} A B M).obj (Q.obj P))) := by
  have : IsIso (Q.map f) := (isIso_Q_map_iff f).mpr hf
  let Z := (DGModuleCat.tensorFunctor A (InDegreeZero M)).obj (DGModuleCat.of B (InDegreeZero X))
  let e : (derivedTensor.{w} A B M).obj (Q.obj P) ≅ Q.obj Z :=
    (derivedTensor.{w} A B M).mapIso (asIso (Q.map f)) ≪≫
      (QCompDerivedTensorIso.{w} A B M).app (DGModuleCat.of B (InDegreeZero X))
  refine IsZero.of_iso ?_ ((homologyFunctor ℤ n).mapIso e)
  let : Subsingleton (cocycles Z n) := ⟨fun x y => by
    apply Subtype.ext
    have hx := Categorification.TensorProductOver.eq_zero_of_mem_grading_inDegreeZero (B := B) (M := M)
      (N := X) hn (mem_cocycles.mp x.2).1
    have hy := Categorification.TensorProductOver.eq_zero_of_mem_grading_inDegreeZero (B := B) (M := M)
      (N := X) hn (mem_cocycles.mp y.2).1
    exact hx.trans hy.symm⟩
  let : Subsingleton (cohomology Z n) := (cohomology.mk_surjective Z n).subsingleton
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ((cohomologyAddEquiv ℤ Z n).surjective.subsingleton)

end Projective

variable {B : Type} [Ring B] [HasDerivedCategory.{w, 0} ℤ] [HasDerivedCategory.{w, 0} B]

/-- **Tor vanishing from degree zero along ordered covers of the coefficient**: let `X` have a
projective resolution `R`, and let the coefficients `S c` have ordered covers. On a set `G` of
labels closed under `above`, if `S c ⊗ X` vanishes in degree zero, then `S c ⊗ᴸ X` vanishes in
every degree. -/
theorem isZero_derivedTensorHomology_of_orderedStandardCovers_resolution {ι : Type*}
    {S : ι → ModuleCat.{0} Bᵐᵒᵖ} {e : ι → Bᵐᵒᵖ} {above : ι → ι → Prop}
    (D : ModuleFiltration.OrderedStandardCovers S e above)
    (hwf : WellFounded fun a b => above b a) (G : Set ι)
    (hG : ∀ c d, c ∈ G → above c d → d ∈ G) {X : ModuleCat.{0} B} (R : ProjectiveResolution X)
    (h₀ : ∀ c ∈ G, IsZero ((homologyFunctor ℤ 0).obj
      ((derivedTensor.{w} ℤ B (S c)).obj (Q.obj (projectiveResolutionDGModel R)))))
    (c : ι) (hc : c ∈ G) (n : ℤ) : IsZero ((homologyFunctor ℤ n).obj
        ((derivedTensor.{w} ℤ B (S c)).obj (Q.obj (projectiveResolutionDGModel R)))) :=
  isZero_derivedTensorHomology_of_orderedStandardCovers
    (projectiveResolutionDGModel_kProjective R) D hwf G hG h₀
    (fun d _ j hj => by
      have := D.projective d
      exact isZero_derivedTensorHomology_projective_coefficient _ X
        (projectiveResolutionDGAugToOrdinary R) (projectiveResolutionDGAugToOrdinary_quasiIso R)
        j hj)
    c hc n

end Categorification
