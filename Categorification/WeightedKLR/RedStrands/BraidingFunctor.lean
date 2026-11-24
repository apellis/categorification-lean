/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedViolatedIdentity
import Categorification.Algebra.CornerBimodule
import Categorification.Algebra.DerivedTensorTriangulated

set_option backward.isDefEq.respectTransparency false

/-!
# The braiding functors `𝔅_w = - ⊗ᴸ B_w`

Webster (arXiv:1309.3796v2, §6) defines `B_w` as the quotient of the bimodule `B̃_w` of
`w`-Stendhal diagrams by the violated ones, and (Definition 6.6) the functor
`𝔅_w = - ⊗ᴸ B_w` on derived categories of right modules.

In this library `B_w` is the corner `e_{κ'} (A / J) e_κ` of the quotient of the braided
Stendhal algebra by violated idempotents (`BraidedStendhalAlgebra.ViolQuotient`), where `κ'`
and `κ` are the two red orders. It is a bimodule over the corner rings `e_{κ'} (A / J) e_{κ'}`
(on the left) and `e_κ (A / J) e_κ` (on the right); for the order `λ_1, …, λ_ℓ` the corner
ring is Webster's `T^λ` (`BraidedStendhalAlgebra.violCornerEquiv`).

## Main definitions

* `BraidedStendhalAlgebra.braidingBimodule κ' κ` : the bimodule `e_{κ'} (A / J) e_κ`.
* `BraidedStendhalAlgebra.braidingFunctor κ' κ` : **Webster, Definition 6.6**, the derived
  tensor product `- ⊗ᴸ B(κ', κ)` from right modules over the corner at `κ'` to right modules
  over the corner at `κ`.

The functor is defined on the unbounded derived category of ungraded dg modules of `dg-lean`
(rings in degree `0`), computed on K-projective resolutions; Webster works with the bounded
above derived category of graded modules.
-/

namespace Categorification.Stendhal

open KLR TypeA CategoryTheory DG DG.DegreeZero

universe w

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

namespace BraidedStendhalAlgebra

variable (k Q Λ ν) in
/-- The idempotent `e_κ` in the quotient by violated idempotents. -/
theorem isIdempotentElem_violMk_redProj (κ : List (Fin ℓ)) :
    IsIdempotentElem (violMk k Q Λ ν (redProj k Q Λ ν κ)) :=
  (isIdempotentElem_redProj κ).map _

local notation "hE" => isIdempotentElem_violMk_redProj k Q Λ ν

variable (k Q Λ ν) in
/-- **The bimodule `B(κ', κ) = e_{κ'} (A / J) e_κ`** (arXiv:1309.3796v2, §6, before Lemma
6.5): Webster's `B_w` for the red orders `κ'` and `κ` related by `w`. -/
noncomputable abbrev braidingBimodule (κ' κ : List (Fin ℓ)) :
    AddSubgroup (ViolQuotient k Q Λ ν) :=
  cornerBimodule (violMk k Q Λ ν (redProj k Q Λ ν κ')) (violMk k Q Λ ν (redProj k Q Λ ν κ))

variable (k Q Λ ν) in
/-- **Webster, Definition 6.6**: the functor `- ⊗ᴸ B(κ', κ)` from the derived category of right
modules over the corner at `κ'` to that over the corner at `κ`. -/
noncomputable def braidingFunctor (κ' κ : List (Fin ℓ))
    [HasDerivedCategory.{w} (hE κ').Cornerᵐᵒᵖ] [HasDerivedCategory.{w} (hE κ).Cornerᵐᵒᵖ] :
    DG.DerivedCategory.{w} (hE κ').Cornerᵐᵒᵖ ⥤ DG.DerivedCategory.{w} (hE κ).Cornerᵐᵒᵖ :=
  derivedRightTensor.{w} (hE κ').Corner (hE κ).Corner (braidingBimodule k Q Λ ν κ' κ)

variable (k Q Λ ν) in
noncomputable instance braidingFunctor_commShift (κ' κ : List (Fin ℓ))
    [HasDerivedCategory.{w} (hE κ').Cornerᵐᵒᵖ] [HasDerivedCategory.{w} (hE κ).Cornerᵐᵒᵖ] :
    (braidingFunctor.{w} k Q Λ ν κ' κ).CommShift ℤ := by
  unfold braidingFunctor
  infer_instance

variable (k Q Λ ν) in
instance braidingFunctor_isTriangulated (κ' κ : List (Fin ℓ))
    [HasDerivedCategory.{w} (hE κ').Cornerᵐᵒᵖ] [HasDerivedCategory.{w} (hE κ).Cornerᵐᵒᵖ] :
    (braidingFunctor.{w} k Q Λ ν κ' κ).IsTriangulated := by
  unfold braidingFunctor
  infer_instance

end BraidedStendhalAlgebra

end Categorification.Stendhal
