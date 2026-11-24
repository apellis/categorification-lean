/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftTopPrincipal
import Categorification.WeightedKLR.RedStrands.FiveSlotSpectatorWeight
import Categorification.WeightedKLR.RedStrands.HigherKernelCrossingAt
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedSequence

/-!
# The principal higher layer at the next retained five-slot top

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 at (6.21). At the next retained
loading, the principal higher crossing comes from the maximal loading
projective. Quotient factorization makes this a surjection onto the
retained kernel. The dimension shift then applies if the ordinary crossing
and the ordinary balanced kernel inclusion are both injective.
-/

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory Equiv MulOpposite
open scoped DG.DegreeZero

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA CornerEndomorphism

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν₀
local notation "n₀" => Multiset.card μ
local notation "v₀" => fixedTopFourExitCut 0
local notation "jA" => sadj n₀ 2 • v₀

private theorem order : redWord v₀ = redWord jA := by decide

private theorem higher : adjacentBlockRoot 1 2 jA < adjacentBlockRoot 1 2 v₀ := by
  constructor
  · intro r i; fin_cases r <;> cases i <;> decide
  · intro h
    have bad := h (1 : Fin 3) ()
    have : ¬ adjacentBlockRoot 1 2 v₀ 1 () ≤ adjacentBlockRoot 1 2 jA 1 () := by decide
    exact this bad

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "V" => ViolQuotient k Q Λ ν₀
local notation "π" => AlgHom.comp (violMk k Q Λ ν₀) (ofKLR k Q Λ ν₀)
local notation "E" => violMk k Q Λ ν₀ (redProj k Q Λ ν₀ (redWord jA))
local notation "C" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord jA))
local notation "d" => orderedLoadingIdemAt Q Λ (redWord jA) v₀ order
local notation "K" => blockLoadingKernel Q Λ jA 1 2

/-- The maximal loading projective maps onto the next retained kernel via the
single crossing in the principal higher ideal. -/
theorem fiveSlotNextRetainedCrossing_surjective (hQ : KLRSymm Q) :
    Function.Surjective (crossingIntoKernelMap Q Λ 1 2 order higher 2) := by
  intro x
  have hcut : π (KLRAlgebra.e jA) * x.1.1.1 = x.1.1.1 := congrArg Subtype.val x.1.2
  obtain ⟨y, hy, hyx⟩ := fiveSlot_jA_higher_exists_leftFactor Q Λ hQ x.1.1.1 x.2 hcut
  let yC : C := ⟨E * y * E, y, rfl⟩
  have hd : IsIdempotentElem d := orderedLoadingIdem_idem Q Λ v₀
  let z : rIdeal d := rIdealProj hd yC
  have hz : z.1.1 = y * E := by
    have hE : d.1 * E = d.1 := corner_mul_right _ d
    change d.1 * (E * y * E) = y * E
    rw [← mul_assoc, ← mul_assoc, hE]
    change π (KLRAlgebra.e v₀) * y * E = y * E
    rw [hy]
  refine ⟨z, ?_⟩
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  rw [crossingIntoKernelMap_val Q Λ 1 2 order higher 2 rfl, hz, ← mul_assoc, hyx]
  exact corner_mul_right _ x.1.1


variable (κ : List (Fin 3))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν₀ κ)

/-- If the principal crossing into the next retained kernel is injective,
the kernel is braid-acyclic by the maximal loading projective comparison. -/
theorem fiveSlotNextRetainedKernel_braid_homology_vanish (hQ : KLRSymm Q)
    (hi : Function.Injective (crossingIntoKernelMap Q Λ 1 2 order higher 2))
    [sourceDerived : HasDerivedCategory.{w,0} Cᵐᵒᵖ] [HasDerivedCategory.{w,0} Uᵐᵒᵖ]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Q Λ ν₀ (redWord jA) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Cᵐᵒᵖ).obj (ModuleCat.of Cᵐᵒᵖ K))))) := by
  let P := rIdeal d
  let G := degreeZeroModuleFunctor Cᵐᵒᵖ ⋙ DG.DerivedCategory.Q ⋙
    braidingFunctor k Q Λ ν₀ (redWord jA) κ ⋙ DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n
  let f := LinearEquiv.ofBijective (crossingIntoKernelMap Q Λ 1 2 order higher 2)
    ⟨hi, fiveSlotNextRetainedCrossing_surjective Q Λ hQ⟩
  let : HasDerivedCategory.{w,0}
    (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord v₀)).Cornerᵐᵒᵖ := sourceDerived
  have hp : IsZero (G.obj (ModuleCat.of Cᵐᵒᵖ P)) :=
    blockLoadingProjective_braid_homology_vanish Q Λ v₀ κ n hn
  exact hp.of_iso (G.mapIso f.toModuleIso.symm)


/-- The next retained partial standard is braid-acyclic once the principal crossing
and the ordinary balanced kernel inclusion are injective. -/
theorem fiveSlotNextRetainedPartialStandard_braid_homology_vanish (hQ : KLRSymm Q)
    (hcross : Function.Injective (crossingIntoKernelMap Q Λ 1 2 order higher 2))
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ jA 1 2 κ))
    [HasDerivedCategory.{w,0} Cᵐᵒᵖ] [HasDerivedCategory.{w,0} Uᵐᵒᵖ]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Q Λ ν₀ (redWord jA) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Cᵐᵒᵖ).obj
          (blockLoadingShortComplex Q Λ jA 1 2).X₃)))) := by
  refine blockPartialStandard_braid_homology_vanish Q Λ jA 1 2 κ
    (L := fun _ : Unit => ModuleCat.of Cᵐᵒᵖ K) (m := [()])
    (ModuleFiltration.HasFiltration.single (LinearEquiv.refl _ _)) ?_ hbal n hn
  intro _ _ j hj
  exact fiveSlotNextRetainedKernel_braid_homology_vanish Q Λ κ hQ hcross j hj

/-- The next retained kernel vanishes when the spectator weight is at most one. -/
theorem fiveSlotNextRetainedKernel_eq_bot_of_spectatorWeight_le_one
    (h : Λ 0 () ≤ 1) : K = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  change x.1.1 ∈ blockUpperIdeal k Q Λ ν₀ 1 2 (adjacentBlockRoot 1 2 jA) (redWord jA) at hx
  rw [fiveSlot_oneBlackBeforePair_upperIdeal_eq_bot_of_spectatorWeight_le_one Q Λ h jA (Or.inr rfl)] at hx
  rw [Submodule.mem_bot]
  apply Subtype.ext; apply Subtype.ext
  exact (TwoSidedIdeal.mem_bot _).1 hx

/-- The next retained partial standard is braid-acyclic at spectator weight at most one. -/
theorem fiveSlotNextRetainedPartialStandard_braid_homology_vanish_of_spectatorWeight_le_one
    (h : Λ 0 () ≤ 1)
    [HasDerivedCategory.{w,0} Cᵐᵒᵖ] [HasDerivedCategory.{w,0} Uᵐᵒᵖ]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Q Λ ν₀ (redWord jA) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Cᵐᵒᵖ).obj
          (blockLoadingShortComplex Q Λ jA 1 2).X₃)))) :=
  blockPartialStandard_braid_homology_vanish_of_bot Q Λ jA 1 2 κ
    (fiveSlotNextRetainedKernel_eq_bot_of_spectatorWeight_le_one Q Λ h) n hn

end Categorification.Stendhal.BraidedStendhalAlgebra
