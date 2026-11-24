/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelPalette
import Categorification.WeightedKLR.RedStrands.FiveSlotPrincipalAllBottoms

/-!
# Principal five-slot columns over a supported colour

In the proof of Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 after (6.21),
the two principal columns for two equal black strands transport along the
singleton black palette. This preserves the arbitrary commutative ground ring,
the red pairings, and the unrestricted bottom loading from the singleton case.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [CommRing k]

private def principalColour (i : I) : Unit → I := fun _ => i

omit [DecidableEq I] in
private theorem principalColour_injective (i : I) : Function.Injective (principalColour i) :=
  fun _ _ _ => Subsingleton.elim _ _

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀

private def principalCentral : Seq μ₀ := fixedTopFourExitCut 1
private def principalNearby : Seq μ₀ := sadj (Multiset.card μ₀) 2 • fixedTopFourExitCut 0

local notation "νᵢ" i => ((Singleton.singleton i : Multiset I) + Singleton.singleton i)
private abbrev principalLoading (i : I) :=
  paletteLoading (ℓ := 3) (ν := ν₀) (principalColour i) (principalColour_injective i)

omit [DecidableEq I] in
private theorem principalColour_map (i : I) : Multiset.map (principalColour i) ν₀=νᵢ i := by
  simp [principalColour]

private def reindexPrincipalTop (i : I) {ν : Multiset I}
    (hν : Multiset.map (principalColour i) ν₀=ν) (u : Seq μ₀) :
    Seq (stendhalWeight 3 ν) :=
  hν ▸ principalLoading i u

/-- The principal top `[0,i,1,2,i]` of the exchanged pair. -/
def fiveSlotPrincipalCentralTop (i : I) : Seq (stendhalWeight 3 (νᵢ i)) :=
  reindexPrincipalTop i (principalColour_map i) principalCentral

/-- The principal top `[0,i,1,i,2]` of the exchanged pair. -/
def fiveSlotPrincipalNearbyTop (i : I) : Seq (stendhalWeight 3 (νᵢ i)) :=
  reindexPrincipalTop i (principalColour_map i) principalNearby

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 3 → I →₀ ℕ)

private def PrincipalColumnInjective {ν : Multiset I}
    (t s : Seq (stendhalWeight 3 ν)) : Prop :=
  Function.Injective (blockKernelColumnInclusion Q Λ t 1 2 s).toFun

private theorem principalColumn_relabel_mapped (i : I) (u v : Seq μ₀)
    (hu : u=principalCentral ∨ u=principalNearby) :
    PrincipalColumnInjective Q Λ (principalLoading i u) (principalLoading i v) :=
  (blockKernelColumnInclusion_injective_palette_iff
      (principalColour i) (principalColour_injective i) Q Λ u 1 2 v).mpr
    (fiveSlot_oneBlackBeforePair_columnInclusion
      (fun a b => Q (principalColour i a) (principalColour i b))
      (pullBlackWeights Λ (principalColour i) (principalColour_injective i))
      (fun a b h => (h (Subsingleton.elim a b)).elim) u v hu)

private theorem principalColumn_relabel (i : I) (u : Seq μ₀)
    (hu : u=principalCentral ∨ u=principalNearby)
    {ν : Multiset I} (hν : Multiset.map (principalColour i) ν₀=ν)
    (s : Seq (stendhalWeight 3 ν)) :
    PrincipalColumnInjective Q Λ (reindexPrincipalTop i hν u) s := by
  subst ν
  obtain ⟨v,rfl⟩ := (principalLoading i).surjective s
  exact principalColumn_relabel_mapped Q Λ i u v hu

/-- Either of the two principal tops gives an injective ordinary kernel-column
inclusion for every bottom loading of the same weight, in any red order. -/
theorem fiveSlot_singleColour_oneBlackBeforePair_columnInclusion (i : I)
    (t s : Seq (stendhalWeight 3 (νᵢ i)))
    (ht : t=fiveSlotPrincipalCentralTop i ∨ t=fiveSlotPrincipalNearbyTop i) :
    PrincipalColumnInjective Q Λ t s := by
  rcases ht with rfl|rfl
  · exact principalColumn_relabel Q Λ i principalCentral (Or.inl rfl)
      (principalColour_map i) s
  · exact principalColumn_relabel Q Λ i principalNearby (Or.inr rfl)
      (principalColour_map i) s

end Categorification.Stendhal.BraidedStendhalAlgebra
