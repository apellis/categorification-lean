/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.ShuffleRigidity
import Categorification.WeightedKLR.Mackey.TypeFiltration

/-!
# The leading term of a four-block shuffle has the top shuffle type

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). Let `μ` be a shuffle type, `Z = blockLeft ν' ν₁ μ`, `B` a
four-block chamber for the strands of `ν'` and `Z`, and `ρ` the relabelling that rank-orders the
top chamber `shuffleTop Z B`. Then `ρ` sends exactly the strands of `Z` into the first block of
`ν₁` and has shuffle type `μ` (`GalleryAlgebra.isLeft_iff_blockLeft_of_isRankOrdered`).

In the polynomial representation the four-block shuffle `r ρ (shuffleTop Z B) * galList B w`
acts through `ren ρ ∘ opList B w`. Combining this with the rigidity of the four-block shuffle
(`GalleryAlgebra.exists_isTwisted_opList_shuffleTop`), its coefficient at `ρ` is
`ρ(galNum / galDen)`, and every other relabelling occurring in it has shuffle type strictly
below `μ` (`GalleryAlgebra.exists_isTwisted_ren_opList_shuffleType_lt`).

## Main results

* `GalleryAlgebra.isLeft_iff_blockLeft_of_isRankOrdered`: the rank-ordering relabelling of the
  top chamber has shuffle type `μ` and sends `Z` into the first block.
* `GalleryAlgebra.exists_isTwisted_ren_opList_shuffleType_lt`: the operator of a four-block
  shuffle has a single term of shuffle type `μ`, at `ρ`, with coefficient `ρ(galNum / galDen)`.
-/

namespace Categorification.WeightedKLR

open MvPolynomial FullChamber GalleryAlgebra Juxtapose

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

namespace GalleryAlgebra

/-- **The rank-ordering of the top chamber of a four-block shuffle.** Let `μ` be a shuffle
type, `Z = blockLeft ν' ν₁ μ` and `B` a four-block chamber for the strands of `ν'` and `Z`. A
relabelling `ρ` rank-ordering `shuffleTop Z B` sends exactly the strands of `Z` into the first
block of `ν₁`, and has shuffle type `μ`.

A step of the proof of Webster, arXiv:1209.2463v4, Theorem 2.19. -/
theorem isLeft_iff_blockLeft_of_isRankOrdered (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {μ : I → ℕ} (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) {B : FullChamber Γ ν}
    (hB : IsFourBlock (fun t => decide (t.IsLeft ν')) (blockLeft ν' ν₁ μ) B) {ρ : ColPerm ν}
    (hρ : (ρ • shuffleTop (blockLeft ν' ν₁ μ) B).IsRankOrdered) :
    (∀ t, (ρ.1 t).IsLeft ν₁ ↔ blockLeft ν' ν₁ μ t = true) ∧ shuffleType ν' ν₁ ρ = μ := by
  obtain ⟨g, rfl⟩ := hμ
  obtain ⟨y, hyZ, hyT⟩ := exists_colPerm_isLeft_eq_blockLeft (Γ := Γ) hν' hν₁ g hB.isSeparated
  have hR := isRankOrdered_rankShuffleTop (k := k) hν₁ y B
  rw [rankShuffleTop, hyZ] at hR
  set T := shuffleTop (blockLeft ν' ν₁ (shuffleType ν' ν₁ g)) B
  set u := blockSort hν₁ (y • T)
  have hρ' : ρ = u * y := by
    have h1 : ((u * y) * ρ⁻¹) • (ρ • T) = u • y • T := by
      rw [smul_smul, inv_mul_cancel_right, mul_smul]
    rw [← h1] at hR
    have := eq_one_of_isRankOrdered_smul hρ hR
    rw [mul_inv_eq_one] at this
    exact this.symm
  have hu := blockSort_mem_leftBlockStab (Γ := Γ) hν₁ (y • T)
  refine ⟨fun t => ?_, ?_⟩
  · rw [hρ']
    show (u.1 (y.1 t)).IsLeft ν₁ ↔ _
    rw [(mem_leftBlockStab.1 hu) (y.1 t), ← hyZ]
    simp
  · rw [hρ', shuffleType_mul_of_image_left ν' ν₁ (image_leftStrands_of_mem hu), hyT]

/-- **The four-block shuffle has a single term of top shuffle type.** Let `μ` be a shuffle type,
`Z = blockLeft ν' ν₁ μ`, `B` a four-block chamber for the strands of `ν'` and `Z`, `w` a good word
from `B` to `shuffleTop Z B`, and `ρ` the relabelling rank-ordering `shuffleTop Z B`. In the
polynomial representation `ren ρ ∘ opList B w` is twisted with a non-zero-divisor denominator
`M`, its coefficient of `ρ` is `M * ρ(galNum) / ρ(galDen)`, and every other relabelling occurring
in it has shuffle type strictly below `μ`.

A step of the proof of Webster, arXiv:1209.2463v4, Theorem 2.19. -/
theorem exists_isTwisted_ren_opList_shuffleType_lt (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {μ : I → ℕ} (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) {B : FullChamber Γ ν}
    (hB : IsFourBlock (fun t => decide (t.IsLeft ν')) (blockLeft ν' ν₁ μ) B)
    {w : List (Hyp Γ ν)} (hw : GoodWord B.1 w) (hT : B.flips w = shuffleTop (blockLeft ν' ν₁ μ) B)
    {ρ : ColPerm ν} (hρ : (ρ • shuffleTop (blockLeft ν' ν₁ μ) B).IsRankOrdered) :
    ∃ (M : PolyRing ν k) (a : ColPerm ν → PolyRing ν k), IsRegular M ∧
      IsTwisted (ren ρ ∘ₗ opList k Γ B w) M a ∧
      a ρ * rename ⇑ρ.1 (galDen k B w) = M * rename ⇑ρ.1 (galNum k B w) ∧
      ∀ x, a x ≠ 0 → x ≠ ρ → shuffleType ν' ν₁ x < μ := by
  classical
  obtain ⟨hZ, hρμ⟩ := isLeft_iff_blockLeft_of_isRankOrdered (k := k) hν' hν₁ hμ hB hρ
  obtain ⟨M, a, hM, hTw, h1, hlt⟩ := exists_isTwisted_opList_shuffleTop (k := k) hB hw hT
  refine ⟨rename ⇑ρ.1 M, fun y => rename ⇑ρ.1 (a (ρ⁻¹ * y)), isRegular_rename_colPerm hM ρ,
    hTw.rename ρ, ?_, fun x hx hxρ => ?_⟩
  · simp only [inv_mul_cancel]
    rw [← map_mul, h1, map_mul]
  set x' := ρ⁻¹ * x with hx'
  have hax : a x' ≠ 0 := fun h => hx (by simp only [← hx', h, map_zero])
  have hx1 : x' ≠ 1 := fun h => hxρ (by rw [hx', inv_mul_eq_one] at h; exact h.symm)
  have hxx : ρ * x' = x := mul_inv_cancel_left ρ x
  have hdom : IsDominated (shuffleTop (blockLeft ν' ν₁ μ) B) x' := by
    by_contra hnd
    rw [← hT] at hnd
    exact hax ((isSupported_opList_isDominated (k := k) hB.1 hw).coeff_eq_zero hTw hnd)
  have hle := shuffleType_mul_le ν' ν₁ hρ (g := ρ) (x := x') (by rwa [inv_smul_smul])
  rw [hxx] at hle
  obtain ⟨c, hc⟩ := hlt x' hax hx1
  refine Pi.lt_def.2 ⟨fun i => hρμ ▸ hle i, c.1, ?_⟩
  have e1 : shuffleType ν' ν₁ x c.1 = (Finset.univ.filter fun t : Strand ν => t.1 = c ∧
      decide (t.IsLeft ν') = false ∧ blockLeft ν' ν₁ μ (x'.1 t) = true).card := by
    unfold shuffleType
    congr 1
    refine Finset.filter_congr fun t _ => ?_
    rw [← hxx]
    show _ ∧ _ ∧ (ρ.1 (x'.1 t)).IsLeft ν₁ ↔ _
    rw [hZ, Subtype.ext_iff]
    simp
  have e2 : μ c.1 = (Finset.univ.filter fun t : Strand ν => t.1 = c ∧
      decide (t.IsLeft ν') = false ∧ blockLeft ν' ν₁ μ t = true).card := by
    conv_lhs => rw [← hρμ]
    unfold shuffleType
    congr 1
    refine Finset.filter_congr fun t _ => ?_
    rw [hZ, Subtype.ext_iff]
    simp
  rw [e1, e2]
  exact hc

end GalleryAlgebra

end Categorification.WeightedKLR
