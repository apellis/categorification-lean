/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorFiltration
import Categorification.Algebra.DerivedTensorProjectiveCoefficient

/-!
# Derived tensor products of two filtered modules

If the coefficient `M` (a right module) is filtered by modules `S c` and the ordinary module
`Y` by modules `L d`, and every `S c ⊗ᴸ L d` vanishes in degree `n`, then so does `M ⊗ᴸ Y`
(`isZero_derivedTensorHomology_of_filtrations`). The filtration of `Y` uses that the derived
tensor product is triangulated in the module argument, that of `M` the coefficient long exact
sequence.

This is the argument of B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, proof of Lemma 6.11 (steps `f_n → s_n` and `s_n + f_n → p_{n+1}`): the
higher Tor between modules with standard filtrations vanish.
-/

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification

universe w

variable {B : Type} [Ring B] [HasDerivedCategory.{w, 0} ℤ] [HasDerivedCategory.{w, 0} B]

/-- **Filtered coefficient and filtered module**: vanishing of `S c ⊗ᴸ L d` in degree `n` for
all layers gives vanishing of `M ⊗ᴸ Y` in degree `n`. -/
theorem isZero_derivedTensorHomology_of_filtrations {ι κ : Type*}
    {S : ι → ModuleCat.{0} Bᵐᵒᵖ} {m : List ι} {M : ModuleCat.{0} Bᵐᵒᵖ}
    (hM : ModuleFiltration.HasFiltration S m M)
    {L : κ → ModuleCat.{0} B} {m' : List κ} {Y : ModuleCat.{0} B}
    (hY : ModuleFiltration.HasFiltration L m' Y) (n : ℤ)
    (hSL : ∀ c ∈ m, ∀ d ∈ m', IsZero ((homologyFunctor ℤ n).obj
      ((derivedTensor.{w} ℤ B (S c)).obj
        (Q.obj ((degreeZeroModuleFunctor B).obj (L d)))))) :
    IsZero ((homologyFunctor ℤ n).obj ((derivedTensor.{w} ℤ B M).obj
      (Q.obj ((degreeZeroModuleFunctor B).obj Y)))) := by
  refine ModuleFiltration.HasFiltration.isZero_derivedHomology (derivedTensor.{w} ℤ B M) n hY fun d hd => ?_
  let R : ProjectiveResolution (L d) := projectiveResolution (L d)
  have : IsIso (Q.map (projectiveResolutionDGAugToOrdinary R)) :=
    (isIso_Q_map_iff _).mpr (projectiveResolutionDGAugToOrdinary_quasiIso R)
  let I := asIso (Q.map (projectiveResolutionDGAugToOrdinary R))
  let E (N : ModuleCat.{0} Bᵐᵒᵖ) :
      (homologyFunctor ℤ n).obj ((derivedTensor.{w} ℤ B N).obj
        (Q.obj (projectiveResolutionDGModel R))) ≅
      (homologyFunctor ℤ n).obj ((derivedTensor.{w} ℤ B N).obj
        (Q.obj ((degreeZeroModuleFunctor B).obj (L d)))) :=
    (homologyFunctor ℤ n).mapIso ((derivedTensor.{w} ℤ B N).mapIso I)
  exact (hM.isZero_derivedTensorHomology_coefficient
    (projectiveResolutionDGModel_kProjective R) n fun c hc =>
      (hSL c hc d hd).of_iso (E (S c))).of_iso (E M).symm

end Categorification
