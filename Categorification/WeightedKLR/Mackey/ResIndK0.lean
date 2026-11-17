/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.ResIndPieceProjective
import Categorification.WeightedKLR.Mackey.ResIndRestriction

/-!
# The Mackey identity `Res ∘ Ind` on Grothendieck groups

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.19 (the Mackey filtration of Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18).
Let `ν₁ + ν₂ = ν' + ν''`, and let `P`, `Q` be finitely generated projective modules over
`W_{ν'}` and `W_{ν''}`. Under Webster's standing hypothesis, over any commutative ring `k`,
the class of `Res_{ν₁;ν₂} Ind_{ν';ν''} (P ⊠ Q)` in `K₀(W_{ν₁} ⊗ W_{ν₂})` is the sum, over the
shuffle types of `(ν', ν''; ν₁, ν₂)`, of the classes of the pieces
`ResIndPiece L ⊗_{W_{ν'} ⊗ W_{ν''}} (P ⊠ Q)` (`exists_resK0_indK0_eq_sum`).

The identity is between ungraded Grothendieck groups, so no grading shift appears; the shift
by the bilinear form of the shuffle type belongs to a graded version.

## Main results

* `castW_symm_val`: the inverse of `castW` on underlying gallery elements.
* `exists_resK0_indK0_eq_sum`: the Mackey identity on the generators `[P]`, `[Q]`.
-/

noncomputable section

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose InductionAlong MulOpposite
open scoped TensorProduct

universe u v w

variable {I : Type u} [DecidableEq I] {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type w} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

theorem castW_symm_val {μ ν : I →₀ ℕ} (h : μ = ν) (a : WeightedKLRAlgebra k Γ μ) :
    ((castW k Γ h.symm).symm a).1 = castGallery k Γ h a.1 := by
  subst h
  rfl

variable {ν₁ ν₂ ν' ν'' : I →₀ ℕ}

/-- **The Mackey identity on Grothendieck groups** (Webster, arXiv:1209.2463v4, proof of
Theorem 2.19). For `ν₁ + ν₂ = ν' + ν''`, under the standing hypothesis and over any
commutative ring `k`, there are shuffle layouts `L i`, one for each shuffle type of
`(ν', ν''; ν₁, ν₂)`, such that for all finitely generated projective `P` over `W_{ν'}` and
`Q` over `W_{ν''}`,
`[Res_{ν₁;ν₂} Ind_{ν';ν''} (P ⊠ Q)] = ∑ᵢ [ResIndPiece (L i) ⊗_{W_{ν'} ⊗ W_{ν''}} (P ⊠ Q)]`
in `K₀(W_{ν₁} ⊗ W_{ν₂})`. Here `W_{ν'+ν''}` is identified with `W_{ν₁+ν₂}` by `castW`. -/
theorem exists_resK0_indK0_eq_sum (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    (hν₁ : ν₁ + ν₂ = ν' + ν'') :
    ∃ (n : ℕ) (L : Fin n → ShuffleLayout ν' ν'' ν₁ ν₂),
      Function.Injective (fun i => ⇑(L i).c) ∧
      Set.range (fun i => ⇑(L i).c) = Set.range (shuffleType (ν := ν' + ν'') ν' ν₁) ∧
      ∀ (P : FGProj k (WeightedKLRAlgebra k Γ ν')) (Q : FGProj k (WeightedKLRAlgebra k Γ ν'')),
        ∃ (_ : ∀ i, Module.Finite (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
            (BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
              (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') (ResIndPiece k Γ (L i))
              (ExtTensor k P.carrier Q.carrier)))
          (_ : ∀ i, Module.Projective (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
            (BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
              (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') (ResIndPiece k Γ (L i))
              (ExtTensor k P.carrier Q.carrier))),
          resK0 ν₁ ν₂ hD hZ hS
              (ProjK0.map (castW k Γ hν₁.symm) (indK0 ν' ν'' (ProjK0.of P) (ProjK0.of Q))) =
            ∑ i, ProjK0.of (FGProj.of (k := k)
              (A := WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
              (BalancedTensor k (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
                (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
                (ResIndPiece k Γ (L i)) (ExtTensor k P.carrier Q.carrier))) := by
  choose Pc hP using fun C E : FullChamber Γ (ν' + ν'') => exists_isChamberSegment hD hZ C E
  obtain ⟨n, L, hinj, hrange, h⟩ := exists_resInd_balancedTensor_eq_sum (k := k) hP hD hZ
    hS.psymm (fun w => hS.isRegular_factor w) hS.isRegular_loopFactor' rfl hν₁
  refine ⟨n, L, hinj, hrange, fun P Q => ?_⟩
  have : Module.Projective (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (ExtTensor k P.carrier Q.carrier) := ExtTensor.projective
  have : Module.Finite (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
      (ExtTensor k P.carrier Q.carrier) := ExtTensor.finite
  have hfin := fun i => ResIndPiece.balancedTensor_finite (L i) (ExtTensor k P.carrier Q.carrier)
    hD hZ hS
  have hproj := fun i => ResIndPiece.balancedTensor_projective (L i)
    (ExtTensor k P.carrier Q.carrier) hD hZ hS
  obtain ⟨_, _, hsum⟩ := h (ExtTensor k P.carrier Q.carrier)
  refine ⟨hfin, hproj, ?_⟩
  rw [indK0_of, ProjK0.map_of, resK0_of, ← hsum]
  exact ProjK0.of_eq_of_iso (resIndTensorEquiv hP hD hZ hS.psymm (fun w => hS.isRegular_factor w)
    hS.isRegular_loopFactor' hν₁ (ExtTensor k P.carrier Q.carrier)
    (castW k Γ hν₁.symm).symm (castW_symm_val hν₁)).symm

end Categorification.WeightedKLR

end
