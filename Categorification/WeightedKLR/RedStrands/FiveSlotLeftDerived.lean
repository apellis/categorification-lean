/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopIdeal
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedSequence
import Categorification.Algebra.DerivedTensorHomology

/-!
# The derived braid at the maximal five-slot loading

The higher kernel vanishes at the maximal retained cut in the five-slot
example for Webster, arXiv:1309.3796v2, Lemma 6.8 and (6.21). The braid of
the loading partial standard is the ordinary braid tensor in degree zero.
-/

open CategoryTheory DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR

noncomputable section

attribute [local instance 1200] Ring.toIntAlgebra

universe w

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "t" => fixedTopFourExitCut 0
local notation "C" => fun κ : List (Fin 3) =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₀ κ)

/-- At the left-extreme loading the higher kernel of the loading standard quotient is zero. -/
theorem fiveSlotLeftExtreme_blockLoadingKernel_eq_bot :
    blockLoadingKernel Q Λ t 1 2 = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  change x.1.1 ∈ blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 t) (redWord t) at hx
  rw [fiveSlotLeftExtreme_blockUpperIdeal_eq_bot Q Λ] at hx
  rw [Submodule.mem_bot]
  apply Subtype.ext
  apply Subtype.ext
  exact (TwoSidedIdeal.mem_bot _).1 hx

set_option backward.isDefEq.respectTransparency false in
/-- The left-extreme loading partial standard has its ordinary braid model in
degree zero, with the action of the full target red-order corner. -/
def fiveSlotLeftExtreme_partialStandardBraidIsoOrdinary (κ : List (Fin 3))
    [source : HasDerivedCategory.{w, 0} (C (redWord t))ᵐᵒᵖ]
    [target : HasDerivedCategory.{w, 0} (C κ)ᵐᵒᵖ] :
    let T := C (redWord t)
    let U := C κ
    let M := OpBimodule T (braidingBimodule k Q Λ ν₀ (redWord t) κ)
    let X := (blockLoadingShortComplex Q Λ t 1 2).X₃
    let qs := @DG.DerivedCategory.Q.{w, 0, 0} Tᵐᵒᵖ _ _ _ source
    let qt := @DG.DerivedCategory.Q.{w, 0, 0} Uᵐᵒᵖ _ _ _ target
    let F := @braidingFunctor.{w, 0, 0} Unit _ k _ 3 Q Λ ν₀ (redWord t) κ source target
    F.obj (qs.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj X)) ≅
      qt.obj (DGModuleCat.of Uᵐᵒᵖ
        (TensorProductOver Tᵐᵒᵖ (InDegreeZero M) (InDegreeZero X))) := by
  dsimp only
  exact derivedTensorIsoOrdinaryOfVanishing (A := (C κ)ᵐᵒᵖ) (B := (C (redWord t))ᵐᵒᵖ)
    (M := OpBimodule (C (redWord t)) (braidingBimodule k Q Λ ν₀ (redWord t) κ))
    (blockLoadingShortComplex Q Λ t 1 2).X₃
    (fun n hn => blockPartialStandard_braid_homology_vanish_of_bot Q Λ t 1 2 κ
      (fiveSlotLeftExtreme_blockLoadingKernel_eq_bot Q Λ) n hn)

end

end Categorification.Stendhal.BraidedStendhalAlgebra
