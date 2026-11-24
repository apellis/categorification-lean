/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotRightmostDerived
import Categorification.WeightedKLR.RedStrands.FiveSlotPrincipalHigherDerived
import Categorification.WeightedKLR.RedStrands.FiveSlotLastRedKernel

/-!
# Derived concentration with the final red strand on the right

Webster, arXiv:1309.3796v2, Lemma 6.8 at (6.21).
The kernel of the second nearby crossing is a split nilHecke kernel from
the left-extreme projective. The balanced monomorphism at the nearby cut
gives concentration of its image. The top nilHecke splitting and the
balanced monomorphism at the final cut complete the dimension shift.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA CornerEndomorphism MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [CommRing k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)
  (Λ : Fin 3 → Unit →₀ ℕ)
local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "F" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "p" => fun t => F (e t)
local notation "E₀" => fixedTopFourExitCut 0
local notation "E₁" => fiveSlotHigherLoading 2
local notation "E₂" => fiveSlotRightLoading 2
local notation "E" => violMk k Q Λ ν (redProj k Q Λ ν (redWord E₀))
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord E₂))
private theorem lastRedOrder₀ : redWord E₀ = redWord E₂ := by decide
private theorem lastRedOrder₁ : redWord E₁ = redWord E₂ := by decide
local notation "f₀" => orderedLoadingIdemAt Q Λ (redWord E₂) E₀ lastRedOrder₀
local notation "f₁" => orderedLoadingIdemAt Q Λ (redWord E₂) E₁ lastRedOrder₁
local notation "P₀" => rIdeal f₀
local notation "P₁" => rIdeal f₁
local notation "K₁" => blockLoadingKernel Q Λ E₁ 1 2
local notation "K₂" => blockLoadingKernel Q Λ E₂ 1 2
local notation "u₀" => F (ψw [2] * e E₀)
local notation "c₀" => F (ψw [1] * e E₁)
local notation "c₁" => F (ψw [2,1] * e E₁)
local notation "δ₀" => F (ψ 1 : R)
local notation "x₂" => F (x (⟨2, by decide⟩ : Fin N) : R)

private theorem aboveNearby : adjacentBlockRoot 1 2 E₁ < adjacentBlockRoot 1 2 E₀ := by
  constructor
  · intro r i; fin_cases r <;> cases i <;> decide
  · intro h
    exact (by decide : ¬ adjacentBlockRoot 1 2 E₀ 1 () ≤ adjacentBlockRoot 1 2 E₁ 1 ()) (h 1 ())

private theorem nearbyAboveTop : adjacentBlockRoot 1 2 E₂ < adjacentBlockRoot 1 2 E₁ := by
  constructor
  · intro r i; fin_cases r <;> cases i <;> decide
  · intro h
    exact (by decide : ¬ adjacentBlockRoot 1 2 E₁ 1 () ≤ adjacentBlockRoot 1 2 E₂ 1 ()) (h 1 ())

private theorem leftExtremeAboveOrder : redWord E₀ = redWord E₁ := by decide

private def principalMap :=
  crossingIntoKernelMap Q Λ 1 2 leftExtremeAboveOrder aboveNearby 2

private def leftExtremeToNearby : P₀ →ₗ[Tᵐᵒᵖ] P₁ :=
  (blockLoadingKernel Q Λ E₁ 1 2).subtype.comp (principalMap Q Λ)

private theorem leftExtremeToNearby_val (a : P₀) :
    (leftExtremeToNearby Q Λ a).1.1 = u₀ * a.1.1 := by
  simpa only [ψw_cons, ψw_nil, mul_one] using
    crossingIntoKernelMap_val Q Λ 1 2 leftExtremeAboveOrder aboveNearby 2 (by decide) a

private theorem leftExtremeToNearby_injective (hQ : KLRSymm Q) :
    Function.Injective (leftExtremeToNearby Q Λ) := by
  intro a b h
  apply Subtype.ext; apply Subtype.ext; apply sub_eq_zero.mp
  apply fiveSlotNearby_leftWord_cancel_of_leftSupport Q Λ hQ
  · rw [mul_sub, leftExtreme_support Q Λ a, leftExtreme_support Q Λ b]
  · have hv := congrArg (fun z : P₁ => z.1.1) h
    rw [leftExtremeToNearby_val, leftExtremeToNearby_val] at hv
    simp only [ψw_cons, ψw_nil, mul_one] at hv
    simp only [mul_sub, hv, sub_self]

private def lastRed_firstNearbyMap : P₁ →ₗ[Tᵐᵒᵖ] K₂ :=
  crossingIntoKernelMap Q Λ 1 2 lastRedOrder₁ nearbyAboveTop 1

private theorem lastRed_firstNearbyMap_val (a : P₁) :
    (lastRed_firstNearbyMap Q Λ a).1.1.1 = c₀ * a.1.1 := by
  simpa only [ψw_cons, ψw_nil, mul_one] using
    crossingIntoKernelMap_val Q Λ 1 2 lastRedOrder₁ nearbyAboveTop 1 (by decide) a

private theorem nearby_support (a : P₁) : p E₁ * a.1.1 = a.1.1 := by
  have h := a.2
  change f₁ * a.1 = a.1 at h
  exact congrArg (fun x : T => x.1) h

private theorem lastRed_firstNearbyMap_injective (hQ : KLRSymm Q) :
    Function.Injective (lastRed_firstNearbyMap Q Λ) := by
  intro a b h
  apply Subtype.ext; apply Subtype.ext; apply sub_eq_zero.mp
  apply FiveSlotFlag.fiveSlotLastRed_firstCrossing_cancel Q Λ hQ
  · rw [mul_sub, nearby_support Q Λ a, nearby_support Q Λ b]
  · have ha : a.1.1 * E = a.1.1 := corner_mul_right _ a.1
    have hb : b.1.1 * E = b.1.1 := corner_mul_right _ b.1
    change (a.1.1 - b.1.1) * E = a.1.1 - b.1.1
    rw [sub_mul, ha, hb]
  · have hv := congrArg (fun z : K₂ => z.1.1.1) h
    rw [lastRed_firstNearbyMap_val, lastRed_firstNearbyMap_val] at hv
    simpa only [mul_sub, hv, sub_self]

section Second
variable (hQ : KLRSymm Q)

private def nearbyToLastRedSecond : P₁ →ₗ[Tᵐᵒᵖ] K₂ :=
  (fiveSlotLastRedKernel_nilHecke Q Λ).comp (lastRed_firstNearbyMap Q Λ)

private theorem nearbyToLastRedSecond_val (a : P₁) :
    (nearbyToLastRedSecond Q Λ a).1.1.1 = c₁ * a.1.1 := by
  change (fiveSlotLastRedKernel_nilHecke Q Λ (lastRed_firstNearbyMap Q Λ a)).1.1.1 = _
  rw [fiveSlotLastRedKernel_nilHecke_val, lastRed_firstNearbyMap_val, ← mul_assoc]
  congr 1
  rw [← map_mul, ψw_cons 2 [1], mul_assoc]

include hQ in
private theorem nearbyToLastRedSecond_kernel_contained :
    LinearMap.ker (nearbyToLastRedSecond Q Λ) ≤ LinearMap.range (leftExtremeToNearby Q Λ) := by
  intro a ha
  have ha' : nearbyToLastRedSecond Q Λ a = 0 := ha
  have hz := congrArg (fun z : K₂ => z.1.1.1) ha'
  change (nearbyToLastRedSecond Q Λ a).1.1.1 = (0 : V) at hz
  rw [nearbyToLastRedSecond_val] at hz
  obtain ⟨b,hb₁,hb₂,hb⟩ := FiveSlotFlag.fiveSlotLastRed_secondCrossing_mem_leftExtremeImage
    Q Λ hQ a.1.1 (nearby_support Q Λ a) (corner_mul_right _ a.1) hz
  let a₀ : P₀ := blockLoadingRep Q Λ E₀ b
  have ha₀ : a₀.1.1 = b := by
    exact (blockLoadingRep_val Q Λ E₀ b).trans ((congrArg (· * E) hb₁).trans hb₂)
  refine ⟨a₀, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  rw [leftExtremeToNearby_val, ha₀]
  exact hb.symm

private theorem nearbyToLastRedSecond_on_principal (a : P₀) :
    nearbyToLastRedSecond Q Λ (leftExtremeToNearby Q Λ a) =
      lastRed_firstNearbyMap Q Λ
        (leftExtremeToNearby Q Λ (leftExtremeDelta Q Λ a)) := by
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  rw [nearbyToLastRedSecond_val, leftExtremeToNearby_val,
    lastRed_firstNearbyMap_val, leftExtremeToNearby_val, leftExtremeDelta_val]
  have bottom : F (ψw [1] * e E₀) * a.1.1 = δ₀ * a.1.1 := by
    rw [ψw_cons, ψw_nil, mul_one, map_mul F (ψ 1), mul_assoc δ₀,
      leftExtreme_support Q Λ a]
  have h := FiveSlotFlag.fiveSlotLastRed_secondCrossing_on_leftExtreme Q Λ a.1.1
  change c₁ * (u₀ * a.1.1) = c₀ * (u₀ * (F (ψw [1] * e E₀) * a.1.1)) at h
  rwa [bottom] at h

include hQ in
private theorem nearbyToLastRedSecond_on_principal_zero (a : P₀) :
    nearbyToLastRedSecond Q Λ (leftExtremeToNearby Q Λ a) = 0 ↔ leftExtremeDelta Q Λ a = 0 := by
  rw [nearbyToLastRedSecond_on_principal Q Λ]
  constructor
  · intro h
    apply leftExtremeToNearby_injective Q Λ hQ
    apply lastRed_firstNearbyMap_injective Q Λ hQ
    simpa only [map_zero] using h
  · intro h
    simp only [h, map_zero]

include hQ in
private theorem lastRedSecond_range_eq_nilHecke_range :
    LinearMap.range (nearbyToLastRedSecond Q Λ) = LinearMap.range (fiveSlotLastRedKernel_nilHecke Q Λ) := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    exact ⟨lastRed_firstNearbyMap Q Λ a, rfl⟩
  · rintro _ ⟨a,rfl⟩
    obtain ⟨b,hb₁,hb₂,hb⟩ :=
      fiveSlotLastRedKernel_crossing_mem_secondImage Q Λ hQ a.1 a.2
    let z : P₁ := blockLoadingRep Q Λ E₁ b
    have hz : z.1.1 = b :=
      (blockLoadingRep_val Q Λ E₁ b).trans ((congrArg (· * E) hb₁).trans hb₂)
    refine ⟨z, ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    rw [nearbyToLastRedSecond_val, fiveSlotLastRedKernel_nilHecke_val, hz]
    exact hb.symm

end Second




section SecondKernelEquiv
variable (hQ : KLRSymm Q)

local notation "g₂" => nearbyToLastRedSecond Q Λ
local notation "u" => leftExtremeToNearby Q Λ
local notation "d₀" => leftExtremeDelta Q Λ

private def lastRedSecondKernelMap :
    LinearMap.ker d₀ →ₗ[Tᵐᵒᵖ] LinearMap.ker g₂ where
  toFun a := ⟨u a.1, (nearbyToLastRedSecond_on_principal_zero Q Λ hQ a.1).2 a.2⟩
  map_add' a b := Subtype.ext (map_add u a.1 b.1)
  map_smul' r a := Subtype.ext (map_smul u r a.1)

private theorem lastRedSecondKernelMap_injective :
    Function.Injective (lastRedSecondKernelMap Q Λ hQ) := by
  intro a b h
  have hv : u a.1 = u b.1 :=
    congrArg (fun z : LinearMap.ker g₂ => z.1) h
  exact Subtype.ext (leftExtremeToNearby_injective Q Λ hQ hv)

private theorem lastRedSecondKernelMap_surjective :
    Function.Surjective (lastRedSecondKernelMap Q Λ hQ) := by
  intro a
  have hsource : a.1 ∈ LinearMap.range u :=
    nearbyToLastRedSecond_kernel_contained Q Λ hQ a.2
  obtain ⟨b, hb⟩ := hsource
  have hz : g₂ (u b) = 0 := hb.symm ▸ a.2
  have hd := (nearbyToLastRedSecond_on_principal_zero Q Λ hQ b).1 hz
  exact ⟨⟨b, hd⟩, Subtype.ext hb⟩

private def lastRedSecondKernelEquiv :
    LinearMap.ker d₀ ≃ₗ[Tᵐᵒᵖ] LinearMap.ker g₂ :=
  LinearEquiv.ofBijective (lastRedSecondKernelMap Q Λ hQ)
    ⟨lastRedSecondKernelMap_injective Q Λ hQ, lastRedSecondKernelMap_surjective Q Λ hQ⟩

private theorem lastRedSecondKernelEquiv_val (a : LinearMap.ker d₀) :
    (lastRedSecondKernelEquiv Q Λ hQ a).1 = u a.1 := rfl

private def lastRedSecondKernelInclusion :
    LinearMap.ker g₂ →ₗ[Tᵐᵒᵖ] P₀ :=
  (LinearMap.ker d₀).subtype.comp (lastRedSecondKernelEquiv Q Λ hQ).symm.toLinearMap

private def lastRedSecondKernelRetraction :
    P₀ →ₗ[Tᵐᵒᵖ] LinearMap.ker g₂ :=
  (lastRedSecondKernelEquiv Q Λ hQ).toLinearMap.comp (leftExtremeKernelProjection Q Λ)

private theorem lastRedSecondKernelInclusion_factor :
    (u).comp (lastRedSecondKernelInclusion Q Λ hQ) = (LinearMap.ker g₂).subtype := by
  let e := lastRedSecondKernelEquiv Q Λ hQ
  apply LinearMap.ext
  intro a
  change u (e.symm a).1 = a.1
  calc
    _ = (e (e.symm a)).1 := (lastRedSecondKernelEquiv_val Q Λ hQ (e.symm a)).symm
    _ = _ := congrArg Subtype.val (e.apply_symm_apply a)

private theorem lastRedSecondKernelInclusion_split :
    (lastRedSecondKernelRetraction Q Λ hQ).comp (lastRedSecondKernelInclusion Q Λ hQ) =
      LinearMap.id := by
  let e := lastRedSecondKernelEquiv Q Λ hQ
  apply LinearMap.ext
  intro a
  change e (leftExtremeKernelProjection Q Λ (e.symm a).1) = a
  exact (congrArg e (leftExtremeKernelProjection_apply Q Λ (e.symm a))).trans (e.apply_symm_apply a)

end SecondKernelEquiv

section Derived
open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero
attribute [local instance 1200] Ring.toIntAlgebra

universe w
variable (target : List (Fin 3))
variable [sourceDerived : HasDerivedCategory.{w,0}
    (isIdempotentElem_violMk_redProj k Q Λ ν (redWord E₂)).Cornerᵐᵒᵖ]
  [HasDerivedCategory.{w,0} (isIdempotentElem_violMk_redProj k Q Λ ν target).Cornerᵐᵒᵖ]
variable (hQ : KLRSymm Q)

local notation "g₂" => nearbyToLastRedSecond Q Λ
local notation "d₂" => fiveSlotLastRedKernel_nilHecke Q Λ
local notation "u" => leftExtremeToNearby Q Λ
local notation "d₀" => leftExtremeDelta Q Λ

private abbrev lastRedHomologyFun (n : ℤ) :=
  degreeZeroModuleFunctor Tᵐᵒᵖ ⋙ DG.DerivedCategory.Q ⋙
    braidingFunctor.{w} k Q Λ ν (redWord E₂) target ⋙ homologyFunctor ℤ n


private def leftExtremeToNearbyHom :
    ModuleCat.of Tᵐᵒᵖ P₀ ⟶ ModuleCat.of Tᵐᵒᵖ P₁ :=
  let : AddCommGroup P₀ := Submodule.addCommGroup P₀
  let : AddCommGroup P₁ := Submodule.addCommGroup P₁
  let : Module Tᵐᵒᵖ P₀ := Submodule.module P₀
  let : Module Tᵐᵒᵖ P₁ := Submodule.module P₁
  ModuleCat.ofHom u

set_option backward.isDefEq.respectTransparency false in
include hQ in
private theorem leftExtremeToNearby_homology_mono
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ E₁ 1 2 target)) :
    Mono ((lastRedHomologyFun.{w} Q Λ target 0).map (leftExtremeToNearbyHom Q Λ)) := by
  let : HasDerivedCategory.{w,0} (isIdempotentElem_violMk_redProj k Q Λ ν (redWord E₁)).Cornerᵐᵒᵖ := sourceDerived
  let e := LinearEquiv.ofBijective (principalMap Q Λ)
    ⟨fun a b h => leftExtremeToNearby_injective Q Λ hQ (congrArg Subtype.val h),
      fiveSlotNextRetainedCrossing_surjective Q Λ hQ⟩
  have iso : leftExtremeToNearbyHom Q Λ = e.toModuleIso.hom ≫ (blockLoadingShortComplex Q Λ E₁ 1 2).f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rfl
  let hmono : Mono ((lastRedHomologyFun.{w} Q Λ target 0).map ((blockLoadingShortComplex Q Λ E₁ 1 2).f)) :=
    blockKernelDerivedHomology_mono Q Λ E₁ 1 2 target hbal
  rw [iso, Functor.map_comp]
  infer_instance

private theorem leftExtremeLastRed_projective_braid_homology_vanish (j : ℤ) (hj : j ≠ 0) :
    IsZero ((lastRedHomologyFun.{w} Q Λ target j).obj (ModuleCat.of Tᵐᵒᵖ P₀)) := by
  let : HasDerivedCategory.{w,0} (isIdempotentElem_violMk_redProj k Q Λ ν (redWord E₀)).Cornerᵐᵒᵖ :=
    sourceDerived
  exact blockLoadingProjective_braid_homology_vanish Q Λ E₀ target j hj

private theorem nearby_projective_braid_homology_vanish (j : ℤ) (hj : j ≠ 0) :
    IsZero ((lastRedHomologyFun.{w} Q Λ target j).obj (ModuleCat.of Tᵐᵒᵖ P₁)) := by
  let : HasDerivedCategory.{w,0} (isIdempotentElem_violMk_redProj k Q Λ ν (redWord E₁)).Cornerᵐᵒᵖ :=
    sourceDerived
  exact blockLoadingProjective_braid_homology_vanish Q Λ E₁ target j hj

include hQ in
private theorem lastRedSecond_range_braid_homology_vanish
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ E₁ 1 2 target)) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((lastRedHomologyFun.{w} Q Λ target n).obj (ModuleCat.of Tᵐᵒᵖ (LinearMap.range g₂))) := by
  let : (braidingFunctor.{w} k Q Λ ν (redWord E₂) target).Additive := by
    unfold braidingFunctor
    infer_instance
  let : (braidingFunctor.{w} k Q Λ ν (redWord E₂) target).CommShift ℤ :=
    braidingFunctor_commShift.{w} k Q Λ ν (redWord E₂) target
  let : (braidingFunctor.{w} k Q Λ ν (redWord E₂) target).IsTriangulated :=
    braidingFunctor_isTriangulated.{w} k Q Λ ν (redWord E₂) target
  let H := braidingFunctor.{w} k Q Λ ν (redWord E₂) target
  let : AddCommGroup P₀ := Submodule.addCommGroup P₀
  let : AddCommGroup P₁ := Submodule.addCommGroup P₁
  let : AddCommGroup K₂ := blockKernelAddGroup Q Λ E₂ 1 2
  let : Module Tᵐᵒᵖ P₀ := Submodule.module P₀
  let : Module Tᵐᵒᵖ P₁ := Submodule.module P₁
  have hmono : Mono ((lastRedHomologyFun.{w} Q Λ target 0).map (ModuleCat.ofHom (u))) :=
    leftExtremeToNearby_homology_mono Q Λ target hQ hbal
  change IsZero ((lastRedHomologyFun.{w} Q Λ target n).obj (ModuleCat.of Tᵐᵒᵖ (LinearMap.range g₂)))
  apply crossingRange_homology_vanish_of_retract
    (B := Tᵐᵒᵖ) (M := ↥P₁) («N» := ↥K₂) (L := ↥P₀) H g₂ u
    (lastRedSecondKernelInclusion Q Λ hQ) (lastRedSecondKernelRetraction Q Λ hQ)
    (lastRedSecondKernelInclusion_factor Q Λ hQ) (lastRedSecondKernelInclusion_split Q Λ hQ)
    (leftExtremeLastRed_projective_braid_homology_vanish Q Λ target)
    (nearby_projective_braid_homology_vanish Q Λ target) hmono n hn

include hQ in
/-- The entire rightmost loading kernel has braid cohomology concentrated
in degree zero, using the ordinary balanced injection at E1. -/
theorem fiveSlotLastRed_kernel_braid_homology_vanish
    (hbal : Function.Injective (blockKernelTensorInclusion Q Λ E₁ 1 2 target))
    (n : ℤ) (hn : n ≠ 0) : IsZero ((lastRedHomologyFun.{w} Q Λ target n).obj (ModuleCat.of Tᵐᵒᵖ K₂)) := by
  have h := lastRedSecond_range_braid_homology_vanish Q Λ target hQ hbal n hn
  have hD : IsZero ((lastRedHomologyFun.{w} Q Λ target n).obj
      (ModuleCat.of Tᵐᵒᵖ (LinearMap.range d₂))) :=
    (lastRedSecond_range_eq_nilHecke_range Q Λ hQ) ▸ h
  let : (braidingFunctor.{w} k Q Λ ν (redWord E₂) target).Additive := by
    unfold braidingFunctor
    infer_instance
  let : (braidingFunctor.{w} k Q Λ ν (redWord E₂) target).CommShift ℤ :=
    braidingFunctor_commShift.{w} k Q Λ ν (redWord E₂) target
  let : (braidingFunctor.{w} k Q Λ ν (redWord E₂) target).IsTriangulated :=
    braidingFunctor_isTriangulated.{w} k Q Λ ν (redWord E₂) target
  have hProd := crossingProd_homology_vanish (braidingFunctor.{w} k Q Λ ν (redWord E₂) target) n hD
  let : AddCommGroup (LinearMap.range d₂) := Submodule.addCommGroup (LinearMap.range d₂)
  let : Module Tᵐᵒᵖ (LinearMap.range d₂) := Submodule.module (LinearMap.range d₂)
  let : AddCommGroup K₂ := blockKernelAddGroup Q Λ E₂ 1 2
  let e := (fiveSlotLastRedKernel_equiv_nilHeckeRangeProd Q Λ).toModuleIso
  exact hProd.of_iso ((lastRedHomologyFun.{w} Q Λ target n).mapIso e)

include hQ in
/-- The rightmost partial standard follows by Webster's (6.21) from the two
ordinary balanced injections at the central and rightmost loadings. -/
theorem fiveSlotLastRed_partialStandard_braid_homology_vanish
    (hcentral : Function.Injective (blockKernelTensorInclusion Q Λ E₁ 1 2 target))
    (hright : Function.Injective (blockKernelTensorInclusion Q Λ E₂ 1 2 target))
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((lastRedHomologyFun.{w} Q Λ target n).obj (blockLoadingShortComplex Q Λ E₂ 1 2).X₃) := by
  apply blockPartialStandard_braid_homology_vanish Q Λ E₂ 1 2 target
    (L := fun _ : Unit => ModuleCat.of Tᵐᵒᵖ K₂) (m := [()])
    (ModuleFiltration.HasFiltration.single (LinearEquiv.refl _ _)) _ hright n hn
  exact fun _ _ j hj => fiveSlotLastRed_kernel_braid_homology_vanish Q Λ target hQ hcentral j hj

end Derived

end Categorification.Stendhal.BraidedStendhalAlgebra
