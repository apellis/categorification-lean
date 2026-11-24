/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelPalette
import Categorification.WeightedKLR.RedStrands.FiveSlotAllTops

/-!
# Webster's five-slot kernel map in a single supported colour

The standard-parameter kernel inclusion of Webster v2, (6.21) in the
three-red example with two equal black strands transports from the singleton
palette to any colour in a Cartan datum. The top red order is `[0,1,2]`;
the full bottom order is `[0,2,1]`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA QuantumGroup KL3.Diagram DG CategoryTheory MulOpposite DG.DerivedCategory
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w

private def FiveSlotTensorInjective {S K : Type} [DecidableEq S] [CommRing K]
    {ν : Multiset S} (Q : S → S → MvPolynomial (Fin 2) K) (Λ : Fin 3 → S →₀ ℕ)
    (t : Seq (stendhalWeight 3 ν)) : Prop :=
  Function.Injective (blockKernelTensorInclusion Q Λ t 1 2 [0,2,1]).toFun

private def FiveSlotColumnInjective {S K : Type} [DecidableEq S] [CommRing K]
    {ν : Multiset S} (Q : S → S → MvPolynomial (Fin 2) K) (Λ : Fin 3 → S →₀ ℕ)
    (t s : Seq (stendhalWeight 3 ν)) : Prop :=
  Function.Injective (blockKernelColumnInclusion Q Λ t 1 2 s).toFun

private theorem fiveSlotColumn_of_tensor {S K : Type} [DecidableEq S] [CommRing K]
    {ν : Multiset S} (Q : S → S → MvPolynomial (Fin 2) K) (Λ : Fin 3 → S →₀ ℕ)
    (t s : Seq (stendhalWeight 3 ν)) (hs : redWord s=[0,2,1])
    (h : FiveSlotTensorInjective Q Λ t) : FiveSlotColumnInjective Q Λ t s := by
  apply blockKernelColumnInclusion_injective_of_tensor Q Λ t 1 2 s
  let P (order : List (Fin 3)) :=
    Function.Injective (blockKernelTensorInclusion Q Λ t 1 2 order).toFun
  exact (congrArg P hs).mpr h

variable {I k : Type} [DecidableEq I] [Field k] (C : CartanDatum I)
  (Λ : Fin 3 → I →₀ ℕ) (i : I)

private def onlyColour (i : I) : Unit → I := fun _ => i
omit [DecidableEq I] in
private theorem onlyColour_injective (i : I) : Function.Injective (onlyColour i) :=
  fun _ _ _ => Subsingleton.elim _ _

private def onlyColourCartan (C : CartanDatum I) (i : I) : CartanDatum Unit where
  dot _ _ := C.dot i i
  symm _ _ := rfl
  dot_self_pos _ := C.dot_self_pos i
  dot_self_even _ := C.dot_self_even i
  dot_nonpos u v uneq := (uneq (Subsingleton.elim u v)).elim
  dvd_two_mul _ _ := C.dvd_two_mul i i

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + Singleton.singleton i)
local notation "μᵢ" => stendhalWeight 3 νᵢ
local notation "Qᵢ" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "Q₀" => CL.qCL (CL.CLScalars.kl : CL.CLScalars (onlyColourCartan C i) k)
local notation "Λ₀" => pullBlackWeights Λ (onlyColour i) (onlyColour_injective i)
local notation "κ" => ([0,2,1] : List (Fin 3))

omit [DecidableEq I] in
private theorem onlyColour_map : Multiset.map (onlyColour i) ν₀=νᵢ := by
  simp [onlyColour]

private theorem fiveSlot_singleColour_mapped_tensor_injective
    (t : Seq (stendhalWeight 3 (Multiset.map (onlyColour i) ν₀))) (ht : redWord t=[0,1,2]) :
    FiveSlotTensorInjective Qᵢ Λ t := by
  obtain ⟨u,rfl⟩ := (paletteLoading (ℓ := 3) (ν := ν₀) (onlyColour i)
    (onlyColour_injective i)).surjective t
  have hu : redWord u=[0,1,2] := (paletteLoading_redWord (onlyColour i)
    (onlyColour_injective i) u).symm.trans ht
  apply (blockKernelTensorInclusion_injective_palette_iff (onlyColour i)
    (onlyColour_injective i) Qᵢ Λ u 1 2 κ).mpr
  exact fiveSlot_blockKernelTensorInclusion_injective_standard_allTops
    (onlyColourCartan C i) Λ₀ u hu

/-- At standard parameters and black weight `[i,i]`, the kernel inclusion
is injective for every top of red order `[0,1,2]` over the bottom red order
`[0,2,1]`. -/
theorem fiveSlot_singleColour_blockKernelTensorInclusion_injective
    (t : Seq μᵢ) (ht : redWord t=[0,1,2]) :
    FiveSlotTensorInjective Qᵢ Λ t := by
  have transport (ν : Multiset I) (hν : ν=Multiset.map (onlyColour i) ν₀)
      (u : Seq (stendhalWeight 3 ν)) (hu : redWord u=[0,1,2]) :
      FiveSlotTensorInjective Qᵢ Λ u := by
    subst ν
    exact fiveSlot_singleColour_mapped_tensor_injective C Λ i u hu
  exact transport νᵢ (onlyColour_map (i := i)).symm t ht

/-- The same conclusion on each loading column in the bottom red order. -/
theorem fiveSlot_singleColour_blockKernelColumnInclusion_injective
    (t s : Seq μᵢ) (ht : redWord t=[0,1,2]) (hs : redWord s=κ) :
    FiveSlotColumnInjective Qᵢ Λ t s := by
  exact fiveSlotColumn_of_tensor Qᵢ Λ t s hs
    (fiveSlot_singleColour_blockKernelTensorInclusion_injective C Λ i t ht)

attribute [local instance 1200] Ring.toIntAlgebra

variable (t : KLR.Seq (stendhalWeight 3 ((Singleton.singleton i : Multiset I) + Singleton.singleton i)))

local notation "T" => IsIdempotentElem.Corner
  (isIdempotentElem_violMk_redProj k Qᵢ Λ νᵢ (redWord t))
local notation "U" => IsIdempotentElem.Corner
  (isIdempotentElem_violMk_redProj k Qᵢ Λ νᵢ κ)

set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero derived kernel map for the complete bottom order, with
the two black strands of any one colour. -/
theorem fiveSlot_singleColour_blockKernelDerivedHomology_mono
    (ht : redWord t=[0,1,2])
    [DG.HasDerivedCategory.{w,0} Tᵐᵒᵖ] [DG.HasDerivedCategory.{w,0} Uᵐᵒᵖ] :
    Mono ((homologyFunctor (A := Uᵐᵒᵖ) ℤ 0).map
      ((braidingFunctor (k := k) (Q := Qᵢ) (Λ := Λ) (ν := νᵢ) (redWord t) κ).map
        (DG.DerivedCategory.Q.map (blockLoadingKernelInclusionDG Qᵢ Λ t 1 2)))) := by
  exact blockKernelDerivedHomology_mono Qᵢ Λ t 1 2 κ
    (fiveSlot_singleColour_blockKernelTensorInclusion_injective C Λ i t ht)

end Categorification.Stendhal.BraidedStendhalAlgebra
