/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorHomology
import Categorification.WeightedKLR.RedStrands.TwoRedPartialStandardBase

open CategoryTheory DG
open scoped DG.DegreeZero

namespace Categorification.Stendhal.BraidedStendhalAlgebra

universe w u v

variable {I : Type u} {k : Type v} [DecidableEq I] [CommRing k] {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 2 → I →₀ ℕ)

local notation "C" => fun κ : List (Fin 2) =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν κ)

set_option backward.isDefEq.respectTransparency false in
/-- In the two-red initial case of Webster's Lemma 6.8, the natural comparison
identifies the braid of a loading partial standard with its ordinary tensor in
degree zero, as an object with its module action in the derived category. -/
noncomputable def twoRedPartialStandardBraidIsoOrdinary
    (s : KLR.Seq (stendhalWeight 2 ν)) (κ : List (Fin 2))
    [source : HasDerivedCategory.{w, max u v} (C (redWord s))ᵐᵒᵖ]
    [target : HasDerivedCategory.{w, max u v} (C κ)ᵐᵒᵖ] :
    let T := C (redWord s)
    let U := C κ
    let M := OpBimodule T (braidingBimodule k Q Λ ν (redWord s) κ)
    let X := (blockLoadingShortComplex Q Λ s 0 1).X₃
    let qs := @DG.DerivedCategory.Q.{w, max u v, max u v} Tᵐᵒᵖ _ _ _ source
    let qt := @DG.DerivedCategory.Q.{w, max u v, max u v} Uᵐᵒᵖ _ _ _ target
    let F := @braidingFunctor.{w, u, v} I _ k _ 2 Q Λ ν (redWord s) κ source target
    F.obj (qs.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj X)) ≅
      qt.obj (DGModuleCat.of Uᵐᵒᵖ
        (TensorProductOver Tᵐᵒᵖ (InDegreeZero M) (InDegreeZero X))) := by
  dsimp only
  exact derivedTensorIsoOrdinaryOfVanishing (A := (C κ)ᵐᵒᵖ)
    (B := (C (redWord s))ᵐᵒᵖ)
    (M := OpBimodule (C (redWord s)) (braidingBimodule k Q Λ ν (redWord s) κ))
    (blockLoadingShortComplex Q Λ s 0 1).X₃
    (fun n hn => blockPartialStandard_twoRed_braid_homology_vanish Q Λ s κ n hn)

end Categorification.Stendhal.BraidedStendhalAlgebra
