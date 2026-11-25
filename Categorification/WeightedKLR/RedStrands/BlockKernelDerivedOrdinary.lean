/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedSequence
import Categorification.Algebra.DerivedTensorHomology

/-!
# Ordinary models of concentrated partial-standard braids

Webster, arXiv:1309.3796v2, Lemma 6.8 after (6.21). The comparison uses the
ordinary partial-standard quotient and preserves the full target red-order
corner action.
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
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ) (κ : List (Fin ℓ))

local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν κ)
local notation "Braid" => OpBimodule T (braidingBimodule k Q Λ ν (redWord t) κ)
set_option quotPrecheck false in
local notation "X" => (blockLoadingShortComplex Q Λ t a b).X₃

set_option backward.isDefEq.respectTransparency false in
/-- Webster, arXiv:1309.3796v2, Lemma 6.8 at (6.21). A loading partial
standard whose derived braid is concentrated in degree zero has the ordinary
braid tensor as its model, with the full target corner action. -/
def blockPartialStandard_braidIsoOrdinary_of_vanishing
    [HasDerivedCategory.{w, max u v} Tᵐᵒᵖ] [HasDerivedCategory.{w, max u v} Uᵐᵒᵖ]
    (hv : ∀ n : ℤ, n ≠ 0 → IsZero
      ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
        ((braidingFunctor.{w} k Q Λ ν (redWord t) κ).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj X))))) :
    (braidingFunctor.{w} k Q Λ ν (redWord t) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj X)) ≅
      DG.DerivedCategory.Q.obj (DGModuleCat.of Uᵐᵒᵖ
        (TensorProductOver Tᵐᵒᵖ (InDegreeZero Braid) (InDegreeZero X))) :=
  derivedTensorIsoOrdinaryOfVanishing (A := Uᵐᵒᵖ) (B := Tᵐᵒᵖ) (M := Braid) X hv

end Categorification.Stendhal.BraidedStendhalAlgebra
