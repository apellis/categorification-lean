/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.TypeBalanced
import Categorification.WeightedKLR.Mackey.ConjugateEmbedding

/-!
# Balancedness of the four-block shuffle for conjugate elements

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4). Let `μ` be a shuffle type with
four-block chambers `χ q` whose shuffles are sent by a relabelling `ρ` to the rank-ordered
chambers `χ' q`. If `z` relabels strands only within the four blocks and `z'` is locally conjugate
to `z` along `ρ` (`GalleryAlgebra.IsLocalConj`), then for all `q, q'` the four-block shuffle
passes from `e (χ q) z e (χ q')` to `e (χ' q) z' e (χ' q')` up to terms of lower shuffle type
(`GalleryAlgebra.fourShuffle_mul_sub_mul_fourShuffle_mem_mackeyFilt_of_isLocalConj`).

This is the algebra form of `GalleryAlgebra.fourShuffle_mul_sub_mul_fourShuffle_mem_mackeyFilt`
in which the operator hypotheses are replaced by block support and local conjugacy, the two
properties enjoyed by juxtaposed diagrams of the middle parabolic.

## Main definitions

* `GalleryAlgebra.blockStab X Z`: the relabellings preserving the two strand labellings `X`, `Z`.

## Main results

* `GalleryAlgebra.blockOp_e_mul_mul_e`: cutting down to a corner does not change its block.
* `GalleryAlgebra.fourShuffle_mul_sub_mul_fourShuffle_mem_mackeyFilt_of_isLocalConj`.
-/

namespace Categorification.WeightedKLR

open MvPolynomial FullChamber GalleryAlgebra Juxtapose

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

namespace GalleryAlgebra

variable (ν) in
/-- The relabellings of `ν` preserving the two strand labellings `X` and `Z`. -/
def blockStab (X Z : Strand ν → Bool) : Submonoid (ColPerm ν) where
  carrier := {y | ∀ t, X (y.1 t) = X t ∧ Z (y.1 t) = Z t}
  one_mem' := fun _ => ⟨rfl, rfl⟩
  mul_mem' := fun {_ b} ha hb t =>
    ⟨(ha (b.1 t)).1.trans (hb t).1, (ha (b.1 t)).2.trans (hb t).2⟩

omit [DecidableEq I] in
theorem mem_blockStab {X Z : Strand ν → Bool} {y : ColPerm ν} :
    y ∈ blockStab ν X Z ↔ ∀ t, X (y.1 t) = X t ∧ Z (y.1 t) = Z t := Iff.rfl

variable (hΓ : Γ.PSymm)

/-- Cutting `z` down to the corner `e D _ e C` does not change its block from `C` to `D`. -/
theorem blockOp_e_mul_mul_e (D C : FullChamber Γ ν) (z : GalleryAlgebra k Γ ν) :
    blockOp k hΓ D C (e D * z * e C) = blockOp k hΓ D C z := by
  refine _root_.LinearMap.ext fun f => ?_
  simp only [blockOp_apply, map_mul, galleryRep_e, Module.End.mul_apply, blk_apply,
    Pi.single_eq_same, LinearMap.id_apply]

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

/-- **Balancedness of the four-block shuffle for locally conjugate elements.** Let `μ` be a
shuffle type, `Z = blockLeft ν' ν₁ μ`, `χ q` four-block chambers for the strands of `ν'` and `Z`,
and `ρ` a relabelling sending `shuffleTop Z (χ q)` to the rank-ordered chamber `χ' q`. Let `z`
relabel strands only among the four blocks, and let `z'` be locally conjugate to `z` along `ρ`.
Then `fourShuffle Z (χ q) * (e (χ q) z e (χ q')) - (e (χ' q) z' e (χ' q')) * fourShuffle Z (χ q')`
lies in the step of the filtration of the shuffle types strictly below `μ`.

A step of the proof of Webster, arXiv:1209.2463v4, Theorem 2.19. -/
theorem fourShuffle_mul_sub_mul_fourShuffle_mem_mackeyFilt_of_isLocalConj (hν' : ν' + ν'' = ν)
    (hν₁ : ν₁ + ν₂ = ν) {μ : I → ℕ} (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁))
    {Q : Type*} {χ χ' : Q → FullChamber Γ ν}
    (hχ : ∀ q, IsFourBlock (fun t => decide (t.IsLeft ν')) (blockLeft ν' ν₁ μ) (χ q))
    {ρ : ColPerm ν} (hχ' : ∀ q, ρ • shuffleTop (blockLeft ν' ν₁ μ) (χ q) = χ' q)
    (hχr : ∀ q, (χ' q).IsRankOrdered) {z z' : GalleryAlgebra k Γ ν}
    (hz : IsBlockSupported hΓ (blockStab ν (fun t => decide (t.IsLeft ν'))
      (blockLeft ν' ν₁ μ)) z)
    (hzz : IsLocalConj k hΓ χ χ' ρ z' z) (q q' : Q) :
    fourShuffle k hD hZ (blockLeft ν' ν₁ μ) (χ q) * (e (χ q) * z * e (χ q')) -
        (e (χ' q) * z' * e (χ' q')) * fourShuffle k hD hZ (blockLeft ν' ν₁ μ) (χ q') ∈
      mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ (χ' q) (χ q') (Set.Iio μ) := by
  have hcorner : ∀ D C (x : GalleryAlgebra k Γ ν), e D * x * e C ∈ cornerSpace k D C :=
    fun D C x => mem_cornerSpace_iff.2 (by
      simp only [mul_assoc, e_mul_e_self]
      rw [← mul_assoc, e_mul_e_self])
  have h := fourShuffle_mul_sub_mul_fourShuffle_mem_mackeyFilt (k := k) hP hD hZ hΓ hW hL
    hν' hν₁ hμ (hχ q') (hχ q) (ρ := ρ) ((hχ' q').symm ▸ hχr q')
    (u := e (χ q) * z * e (χ q')) (u'' := e (χ' q) * z' * e (χ' q'))
    (hcorner _ _ _) (by rw [hχ', hχ']; exact hcorner _ _ _)
    ((((IsBlockSupported.e (χ q)).mul hz).mul (IsBlockSupported.e (χ q'))) (χ q) (χ q'))
    (by rw [hχ', hχ', blockOp_e_mul_mul_e, blockOp_e_mul_mul_e]; exact hzz.2.2 q q')
  rwa [hχ'] at h

end GalleryAlgebra

end Categorification.WeightedKLR
