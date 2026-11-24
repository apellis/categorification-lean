/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.InteriorSpectatorKernel
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedSequence
import Categorification.WeightedKLR.RedStrands.FirstWeightBlockKernel

/-!
# Derived braid cohomology of the two retained spectator layers

Webster, arXiv:1309.3796v2, Lemma 6.8 at (6.21). The two actual retained
layers arise from crossing the two spectators. The maximal quotient is
projective. The intermediate quotient then follows by the dimension shift
with its ordinary balanced kernel test.
-/

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory

open scoped DG.DegreeZero

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack

open KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 4 → Unit →₀ ℕ)
  (κ : List (Fin 4))

local notation "ν₀" => ({()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 4 ν₀
local notation "T" => IsIdempotentElem.Corner
  (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord source))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₀ κ)

private theorem higherMaximal (t : Seq μ₀) (ht : redWord t = redWord higher)
    (hlt : adjacentBlockRoot 0 1 higher < adjacentBlockRoot 0 1 t) : IsViolated t := by
  apply isViolated_of_strictly_higher_beforeSpectators (M := [2, 3])
    (by decide) ht ⟨2, by decide⟩ rfl ?_ hlt
  intro r hr₀ hr₁ q hq
  fin_cases r
  · exact (hr₀ rfl).elim
  · exact (hr₁ rfl).elim
  · fin_cases q <;> revert hq <;> decide
  · fin_cases q <;> revert hq <;> decide

variable [sourceDerived : HasDerivedCategory.{w, 0}
    (isIdempotentElem_violMk_redProj k Q Λ ({()} : Multiset Unit) (redWord source)).Cornerᵐᵒᵖ]
  [targetDerived : HasDerivedCategory.{w, 0}
    (isIdempotentElem_violMk_redProj k Q Λ ({()} : Multiset Unit) κ).Cornerᵐᵒᵖ]

local notation "F" => braidingFunctor k Q Λ ν₀ (redWord source) κ
local notation "H" n:arg => DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n
set_option quotPrecheck false in
local notation "G" n:arg => degreeZeroModuleFunctor Tᵐᵒᵖ ⋙ DG.DerivedCategory.Q ⋙ F ⋙ H n

/-- The maximal surviving retained layer, before both spectators, is projective. -/
theorem maximalLayer_braid_homology_vanish (n : ℤ) (hn : n ≠ 0) :
    IsZero ((G n).obj (twoSpectatorLayer Q Λ true)) := by
  let E := blockPartialStandardAt_equiv_projective Q Λ higher 0 1 (redWord source)
    (by decide) higherMaximal
  let : HasDerivedCategory.{w,0}
    (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord higher)).Cornerᵐᵒᵖ := sourceDerived
  have hp : IsZero ((G n).obj (ModuleCat.of Tᵐᵒᵖ
      (rIdeal (orderedLoadingIdemAt Q Λ (redWord source) higher (by decide))))) :=
    blockLoadingProjective_braid_homology_vanish Q Λ higher κ n hn
  exact hp.of_iso ((G n).mapIso E.toModuleIso)

/-- The kernel of the intermediate retained loading is braid-acyclic when the
interior crossing is injective. -/
theorem intermediateKernel_braid_homology_vanish
    (hinterior : Function.Injective (interiorCrossingMap Q Λ)) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((G n).obj (blockLoadingKernelObjAt Q Λ source terminalHigher 0 1 (by decide))) := by
  let E := LinearEquiv.ofBijective (interiorCrossingMap Q Λ)
    ⟨hinterior, interiorCrossingMap_surjective Q Λ⟩
  let : HasDerivedCategory.{w,0}
    (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord higher)).Cornerᵐᵒᵖ := sourceDerived
  have hp : IsZero ((G n).obj (ModuleCat.of Tᵐᵒᵖ
      (rIdeal (orderedLoadingIdemAt Q Λ (redWord source) higher (by decide))))) :=
    blockLoadingProjective_braid_homology_vanish Q Λ higher κ n hn
  exact hp.of_iso ((G n).mapIso E.toModuleIso.symm)

/-- The intermediate partial standard follows by the dimension shift, with the
balanced kernel test at the intermediate loading as its geometric input. -/
theorem intermediateLayer_braid_homology_vanish
    (hinterior : Function.Injective (interiorCrossingMap Q Λ))
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ terminalHigher 0 1 κ))
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((G n).obj (twoSpectatorLayer Q Λ false)) := by
  let : HasDerivedCategory.{w,0}
    (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord terminalHigher)).Cornerᵐᵒᵖ := sourceDerived
  refine blockPartialStandard_braid_homology_vanish Q Λ terminalHigher 0 1 κ
    (L := fun _ : Unit => blockLoadingKernelObjAt Q Λ source terminalHigher 0 1 (by decide)) (m := [()])
    (ModuleFiltration.HasFiltration.single (LinearEquiv.refl _ _)) ?_ hbal n hn
  intro _ _ j hj
  exact intermediateKernel_braid_homology_vanish Q Λ κ hinterior j hj

/-- Both actual higher partial-standard layers in the two-spectator filtration
are braid-acyclic outside degree zero. -/
theorem twoSpectatorLayer_braid_homology_vanish
    (hinterior : Function.Injective (interiorCrossingMap Q Λ))
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ terminalHigher 0 1 κ))
    (c : Bool) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((G n).obj (twoSpectatorLayer Q Λ c)) := by
  cases c
  · exact intermediateLayer_braid_homology_vanish Q Λ κ hinterior hbal n hn
  · exact maximalLayer_braid_homology_vanish Q Λ κ n hn

/-- Apply Webster's (6.21) to the filtration with both retained layers. -/
theorem twoSpectatorPartialStandard_braid_homology_vanish
    (hterminal : Function.Injective (terminalCrossingMap Q Λ))
    (hinterior : Function.Injective (interiorCrossingMap Q Λ))
    (hmid : Function.Injective (blockKernelTensorInclusion Q Λ terminalHigher 0 1 κ))
    (hsource : Function.Injective (blockKernelTensorInclusion Q Λ source 0 1 κ))
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((G n).obj (blockLoadingShortComplex Q Λ source 0 1).X₃) := by
  refine blockPartialStandard_braid_homology_vanish Q Λ source 0 1 κ
    (kernel_hasTwoHigherLayers_of_crossings_injective Q Λ hterminal hinterior) ?_ hsource n hn
  intro c _ j hj
  exact twoSpectatorLayer_braid_homology_vanish Q Λ κ hinterior hmid c j hj


/-- The terminal crossing identifies the entire source kernel with an
intermediate loading projective, so source vanishing only needs the source
balanced kernel test. -/
theorem twoSpectatorPartialStandard_braid_homology_vanish_of_terminal_crossing
    (hterminal : Function.Injective (terminalCrossingMap Q Λ))
    (hsource : Function.Injective (blockKernelTensorInclusion Q Λ source 0 1 κ))
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((G n).obj (blockLoadingShortComplex Q Λ source 0 1).X₃) := by
  let E := LinearEquiv.ofBijective (terminalCrossingMap Q Λ)
    ⟨hterminal, terminalCrossingMap_surjective Q Λ⟩
  let : HasDerivedCategory.{w,0}
    (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord terminalHigher)).Cornerᵐᵒᵖ := sourceDerived
  refine blockPartialStandard_braid_homology_vanish Q Λ source 0 1 κ
    (L := fun _ : Unit => ModuleCat.of Tᵐᵒᵖ (blockLoadingKernel Q Λ source 0 1)) (m := [()])
    (ModuleFiltration.HasFiltration.single (LinearEquiv.refl _ _)) ?_ hsource n hn
  intro _ _ j hj
  have hp : IsZero ((G j).obj (ModuleCat.of Tᵐᵒᵖ
      (rIdeal (orderedLoadingIdemAt Q Λ (redWord source) terminalHigher (by decide))))) :=
    blockLoadingProjective_braid_homology_vanish Q Λ terminalHigher κ j hj
  exact hp.of_iso ((G j).mapIso E.toModuleIso.symm)


section Standard
open QuantumGroup KL3.Diagram

variable {F₀ : Type} [Field F₀] {C₀ : CartanDatum Unit}
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C₀ F₀)

/-- At the standard parameters the two retained layers need only the balanced
kernel inclusion at the intermediate loading. -/
theorem twoSpectatorLayer_braid_homology_vanish_standard
    (hR : IsRouquierQ C₀ QL) (hQ : KLRSymm QL) (weights : Fin 4 → Unit →₀ ℕ)
    (target : List (Fin 4))
    [HasDerivedCategory.{w, 0}
      (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ (redWord source)).Cornerᵐᵒᵖ]
    [HasDerivedCategory.{w, 0}
      (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ target).Cornerᵐᵒᵖ]
    (hmid : Function.Injective (blockKernelTensorInclusion QL weights terminalHigher 0 1 target))
    (c : Bool) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor
        (A := (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ target).Cornerᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor F₀ QL weights ν₀ (redWord source) target).obj
        (DG.DerivedCategory.Q.obj
          ((degreeZeroModuleFunctor
            (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ (redWord source)).Cornerᵐᵒᵖ).obj
            (twoSpectatorLayer QL weights c))))) :=
  twoSpectatorLayer_braid_homology_vanish QL weights target
    (interiorCrossingMap_standard_injective hR hQ weights) hmid c n hn

/-- The source partial standard at standard parameters needs only the ordinary
balanced inclusion at the source loading. -/
theorem twoSpectatorPartialStandard_braid_homology_vanish_standard
    (hR : IsRouquierQ C₀ QL) (hQ : KLRSymm QL) (weights : Fin 4 → Unit →₀ ℕ)
    (target : List (Fin 4))
    [HasDerivedCategory.{w, 0}
      (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ (redWord source)).Cornerᵐᵒᵖ]
    [HasDerivedCategory.{w, 0}
      (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ target).Cornerᵐᵒᵖ]
    (hsource : Function.Injective (blockKernelTensorInclusion QL weights source 0 1 target))
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor
        (A := (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ target).Cornerᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor F₀ QL weights ν₀ (redWord source) target).obj
        (DG.DerivedCategory.Q.obj
          ((degreeZeroModuleFunctor
            (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ (redWord source)).Cornerᵐᵒᵖ).obj
            (blockLoadingShortComplex QL weights source 0 1).X₃)))) :=
  twoSpectatorPartialStandard_braid_homology_vanish_of_terminal_crossing QL weights target
    (terminalCrossingMap_standard_injective hR hQ weights) hsource n hn

end Standard


section Standard
open QuantumGroup KL3.Diagram

variable {F₀ : Type} [Field F₀] {C₀ : CartanDatum Unit}
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C₀ F₀)

/-- Both actual partial-standard layers are concentrated in degree zero in the
one-black case at the standard parameters. -/
theorem twoSpectatorLayer_braid_homology_vanish_firstWeight
    (hR : IsRouquierQ C₀ QL) (hQ : KLRSymm QL) (weights : Fin 4 → Unit →₀ ℕ)
    (target : List (Fin 4))
    [HasDerivedCategory.{w, 0}
      (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ (redWord source)).Cornerᵐᵒᵖ]
    [HasDerivedCategory.{w, 0}
      (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ target).Cornerᵐᵒᵖ]
    (c : Bool) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor
        (A := (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ target).Cornerᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor F₀ QL weights ν₀ (redWord source) target).obj
        (DG.DerivedCategory.Q.obj
          ((degreeZeroModuleFunctor
            (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ (redWord source)).Cornerᵐᵒᵖ).obj
            (twoSpectatorLayer QL weights c))))) :=
  twoSpectatorLayer_braid_homology_vanish_standard hR hQ weights target
    (firstWeight_blockKernelTensorInclusion_injective () QL weights 0 1 terminalHigher target hQ) c n hn

/-- The source partial standard is concentrated in degree zero in the one-black
case at the standard parameters. -/
theorem twoSpectatorPartialStandard_braid_homology_vanish_firstWeight
    (hR : IsRouquierQ C₀ QL) (hQ : KLRSymm QL) (weights : Fin 4 → Unit →₀ ℕ)
    (target : List (Fin 4))
    [HasDerivedCategory.{w, 0}
      (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ (redWord source)).Cornerᵐᵒᵖ]
    [HasDerivedCategory.{w, 0}
      (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ target).Cornerᵐᵒᵖ]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor
        (A := (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ target).Cornerᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor F₀ QL weights ν₀ (redWord source) target).obj
        (DG.DerivedCategory.Q.obj
          ((degreeZeroModuleFunctor
            (isIdempotentElem_violMk_redProj F₀ QL weights ν₀ (redWord source)).Cornerᵐᵒᵖ).obj
            (blockLoadingShortComplex QL weights source 0 1).X₃)))) :=
  twoSpectatorPartialStandard_braid_homology_vanish_standard hR hQ weights target
    (firstWeight_blockKernelTensorInclusion_injective () QL weights 0 1 source target hQ) n hn

end Standard

end Categorification.Stendhal.BraidedStendhalAlgebra.TwoSpectatorOneBlack
