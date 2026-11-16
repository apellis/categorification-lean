/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.TypeLeading

/-!
# Balancedness of the four-block shuffle modulo lower shuffle types

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). Let `μ` be a shuffle type, `Z = blockLeft ν' ν₁ μ`, `B` and
`B'` four-block chambers for the strands of `ν'` and `Z`, with good words `w`, `w'` to their
shuffles, and `ρ` the relabelling rank-ordering `shuffleTop Z B`. In the polynomial
representation, an operator `U` supported in the relabellings preserving the four blocks passes
through the four-block shuffle up to terms of lower shuffle type:
`opList B' w' ∘ U - U ∘ opList B w` is supported in the relabellings `x` with `ρ * x` of shuffle
type strictly below `μ` (`GalleryAlgebra.isSupported_opList_comp_sub_comp_opList`).

The proof compares coefficients. Every term of `opList B w` other than the identity has lower
shuffle type after `ρ` (`GalleryAlgebra.exists_isTwisted_opList_shuffleType_lt`), and composing
with a block-preserving relabelling does not change the shuffle type, on either side. The two
remaining coefficients are the identity coefficients `galNum / galDen` of the two shuffles,
which agree (`GalleryAlgebra.galNum_galDen_eq_of_isFourBlock`) and are fixed by block-preserving
relabellings (`GalleryAlgebra.rename_galNum_galDen_of_isFourBlock`).

## Main results

* `IsTwisted.comp`: the twisted presentation of a composite.
* `GalleryAlgebra.isSupported_opList_comp_sub_comp_opList`: balancedness of the four-block
  shuffle modulo lower shuffle types, in the polynomial representation.
-/

namespace Categorification.WeightedKLR

open MvPolynomial FullChamber GalleryAlgebra Juxtapose

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

namespace IsTwisted

omit [IsStrictOrderedRing 𝕜] in
/-- **Composition of twisted operators.** If `M₁ * Op₁ f = ∑ a₁ x * x(f)` and
`M₂ * Op₂ f = ∑ a₂ x * x(f)`, then `Op₂ ∘ Op₁` is twisted with denominator
`(∏ y, y(M₁)) * M₂` and coefficient of `z` equal to `∑ y, a₂ y * (∏_{y' ≠ y} y'(M₁)) *
y(a₁ (y⁻¹ z))`. -/
theorem comp {Op₁ Op₂ : PolyRing ν k →ₗ[k] PolyRing ν k} {M₁ M₂ : PolyRing ν k}
    {a₁ a₂ : ColPerm ν → PolyRing ν k} (h₂ : IsTwisted Op₂ M₂ a₂) (h₁ : IsTwisted Op₁ M₁ a₁) :
    IsTwisted (Op₂ ∘ₗ Op₁) ((∏ y' : ColPerm ν, MvPolynomial.rename ⇑y'.1 M₁) * M₂)
      (fun z => ∑ y, a₂ y * (∏ y' ∈ Finset.univ.erase y, MvPolynomial.rename ⇑(y' : ColPerm ν).1 M₁) *
        MvPolynomial.rename ⇑y.1 (a₁ (y⁻¹ * z))) := by
  classical
  intro f
  set P : PolyRing ν k := ∏ y' : ColPerm ν, MvPolynomial.rename ⇑y'.1 M₁
  set N : ColPerm ν → PolyRing ν k := fun y =>
    ∏ y' ∈ Finset.univ.erase y, MvPolynomial.rename ⇑(y' : ColPerm ν).1 M₁
  have hN : ∀ y, N y * MvPolynomial.rename ⇑y.1 M₁ = P :=
    fun y => Finset.prod_erase_mul _ _ (Finset.mem_univ y)
  have key : ∀ y : ColPerm ν, P * MvPolynomial.rename ⇑y.1 (Op₁ f) =
      N y * ∑ z, MvPolynomial.rename ⇑y.1 (a₁ (y⁻¹ * z)) * MvPolynomial.rename ⇑z.1 f := by
    intro y
    rw [← hN y, mul_assoc, ← map_mul, h₁ f, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, rename_colPerm_mul]
  calc P * M₂ * (Op₂ ∘ₗ Op₁) f
      = ∑ y, a₂ y * (P * MvPolynomial.rename ⇑y.1 (Op₁ f)) := by
        rw [mul_assoc, LinearMap.comp_apply, h₂ (Op₁ f), Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ z, (∑ y, a₂ y * N y * MvPolynomial.rename ⇑y.1 (a₁ (y⁻¹ * z))) * MvPolynomial.rename ⇑z.1 f := by
        simp only [key, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring

end IsTwisted

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

namespace GalleryAlgebra

/-- **Balancedness of the four-block shuffle modulo lower shuffle types.** Let `μ` be a shuffle
type, `Z = blockLeft ν' ν₁ μ`, `B`, `B'` four-block chambers for the strands of `ν'` and `Z`,
`w`, `w'` good words from them to their shuffles, and `ρ` the relabelling rank-ordering
`shuffleTop Z B`. If `U` is supported in the relabellings preserving the strands of `ν'` and the
strands of `Z`, then `opList B' w' ∘ U - U ∘ opList B w` is supported in the relabellings `x`
with `ρ * x` of shuffle type strictly below `μ`.

A step of the proof of Webster, arXiv:1209.2463v4, Theorem 2.19. -/
theorem isSupported_opList_comp_sub_comp_opList (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {μ : I → ℕ} (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) {B B' : FullChamber Γ ν}
    (hB : IsFourBlock (fun t => decide (t.IsLeft ν')) (blockLeft ν' ν₁ μ) B)
    (hB' : IsFourBlock (fun t => decide (t.IsLeft ν')) (blockLeft ν' ν₁ μ) B')
    {w w' : List (Hyp Γ ν)} (hw : GoodWord B.1 w) (hw' : GoodWord B'.1 w')
    (hT : B.flips w = shuffleTop (blockLeft ν' ν₁ μ) B)
    (hT' : B'.flips w' = shuffleTop (blockLeft ν' ν₁ μ) B')
    {ρ : ColPerm ν} (hρ : (ρ • shuffleTop (blockLeft ν' ν₁ μ) B).IsRankOrdered)
    {U : PolyRing ν k →ₗ[k] PolyRing ν k}
    (hU : IsSupported U {y | ∀ t, decide ((y.1 t).IsLeft ν') = decide (t.IsLeft ν') ∧
      blockLeft ν' ν₁ μ (y.1 t) = blockLeft ν' ν₁ μ t}) :
    IsSupported (opList k Γ B' w' ∘ₗ U - U ∘ₗ opList k Γ B w)
      {x | shuffleType ν' ν₁ (ρ * x) < μ} := by
  classical
  obtain ⟨hZ, -⟩ := isLeft_iff_blockLeft_of_isRankOrdered (k := k) hν' hν₁ hμ hB hρ
  have hρ' := isRankOrdered_smul_shuffleTop_of_isRankOrdered hB.1 hB'.1 hρ
  obtain ⟨M, a, hM, hTa, h1, hlt⟩ :=
    exists_isTwisted_opList_shuffleType_lt (k := k) hν' hν₁ hμ hB hw hT hρ
  obtain ⟨M', a', hM', hTa', h1', hlt'⟩ :=
    exists_isTwisted_opList_shuffleType_lt (k := k) hν' hν₁ hμ hB' hw' hT' hρ'
  obtain ⟨MU, u, hMU, hTU, hu⟩ := hU
  obtain ⟨hn, hd⟩ := galNum_galDen_eq_of_isFourBlock (k := k) hB hB' hw hw' hT hT'
  rw [← hn, ← hd] at h1'
  set n := galNum k B w
  set d := galDen k B w
  have hdreg : IsRegular d := isRegular_galDen B w
  have hc1 := IsTwisted.comp hTa' hTU
  have hc2 := IsTwisted.comp hTU hTa
  set P1 : PolyRing ν k := ∏ y' : ColPerm ν, rename ⇑y'.1 MU
  set P2 : PolyRing ν k := ∏ y' : ColPerm ν, rename ⇑y'.1 M
  set N1 : ColPerm ν → PolyRing ν k := fun y =>
    ∏ y' ∈ Finset.univ.erase y, rename ⇑(y' : ColPerm ν).1 MU
  set N2 : ColPerm ν → PolyRing ν k := fun y =>
    ∏ y' ∈ Finset.univ.erase y, rename ⇑(y' : ColPerm ν).1 M
  set c1 : ColPerm ν → PolyRing ν k := fun z => ∑ y, a' y * N1 y * rename ⇑y.1 (u (y⁻¹ * z))
  set c2 : ColPerm ν → PolyRing ν k := fun z => ∑ y, u y * N2 y * rename ⇑y.1 (a (y⁻¹ * z))
  have hreg1 : IsRegular P1 := IsRegular.prod fun y _ => isRegular_rename_colPerm hMU y
  have hreg2 : IsRegular P2 := IsRegular.prod fun y _ => isRegular_rename_colPerm hM y
  refine ⟨P1 * M' * (P2 * MU), fun z => P2 * MU * c1 z - P1 * M' * c2 z,
    (hreg1.mul hM').mul (hreg2.mul hMU), fun f => ?_, fun z hz => ?_⟩
  · have e1 := hc1 f
    have e2 := hc2 f
    simp only [LinearMap.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_assoc,
      ← Finset.mul_sum]
    rw [← mul_assoc P1, ← mul_assoc P2, ← e1, ← e2]
    ring
  by_contra hzlt
  change ¬ shuffleType ν' ν₁ (ρ * z) < μ at hzlt
  apply hz
  -- the block-preserving relabellings do not change the shuffle type on either side
  have hright : ∀ y g : ColPerm ν, u g ≠ 0 →
      shuffleType ν' ν₁ (ρ * y * g) = shuffleType ν' ν₁ (ρ * y) := fun y g hg =>
    shuffleType_mul_of_image_right ν' ν₁ (y := g) (fun i => image_rightStrands_of_mem
      (mem_leftBlockStab.2 fun t => by simpa using ((hu g hg) t).1) i) (ρ * y)
  have hconj : ∀ g : ColPerm ν, u g ≠ 0 → ρ * g * ρ⁻¹ ∈ leftBlockStab ν ν₁ := by
    intro g hg
    refine mem_leftBlockStab.2 fun t => ?_
    have e : ρ.1 ((ρ⁻¹).1 t) = t := by
      change (ρ * ρ⁻¹).1 t = t
      simp
    calc ((ρ * g * ρ⁻¹).1 t).IsLeft ν₁ ↔ blockLeft ν' ν₁ μ (g.1 ((ρ⁻¹).1 t)) = true :=
          hZ (g.1 ((ρ⁻¹).1 t))
      _ ↔ blockLeft ν' ν₁ μ ((ρ⁻¹).1 t) = true := by rw [((hu g hg) _).2]
      _ ↔ (ρ.1 ((ρ⁻¹).1 t)).IsLeft ν₁ := (hZ _).symm
      _ ↔ t.IsLeft ν₁ := by rw [e]
  have hleft : ∀ g y : ColPerm ν, u g ≠ 0 →
      shuffleType ν' ν₁ (ρ * y) = shuffleType ν' ν₁ (ρ * (g⁻¹ * y)) := fun g y hg => by
    have e : ρ * y = (ρ * g * ρ⁻¹) * (ρ * (g⁻¹ * y)) := by group
    rw [e]
    exact shuffleType_mul_of_image_left ν' ν₁ (image_leftStrands_of_mem (hconj g hg)) _
  -- the first composite: only the identity term of `opList B' w'` contributes
  have hc1z : c1 z = a' 1 * N1 1 * u z := by
    refine (Finset.sum_eq_single 1 (fun y _ hy1 => ?_) (fun h => absurd (Finset.mem_univ _) h)).trans
      (by simp only [inv_one, one_mul, rename_colPerm_one])
    by_cases hay : a' y = 0
    · rw [hay, zero_mul, zero_mul]
    by_cases huy : u (y⁻¹ * z) = 0
    · rw [huy, map_zero, mul_zero]
    exfalso
    apply hzlt
    have := hright y (y⁻¹ * z) huy
    rw [mul_assoc ρ y, mul_inv_cancel_left] at this
    rw [this]
    exact hlt' y hay hy1
  -- the second composite: only the identity term of `opList B w` contributes
  have hc2z : c2 z = u z * N2 z * rename ⇑z.1 (a 1) := by
    refine (Finset.sum_eq_single z (fun y _ hyz => ?_) (fun h => absurd (Finset.mem_univ _) h)).trans
      (by simp only [inv_mul_cancel])
    by_cases huy : u y = 0
    · rw [huy, zero_mul, zero_mul]
    by_cases hay : a (y⁻¹ * z) = 0
    · rw [hay, map_zero, mul_zero]
    exfalso
    apply hzlt
    rw [hleft y z huy]
    exact hlt _ hay fun h => hyz (by rw [inv_mul_eq_one] at h; exact h)
  show P2 * MU * c1 z - P1 * M' * c2 z = 0
  rw [hc1z, hc2z]
  by_cases huz : u z = 0
  · rw [huz]; ring
  obtain ⟨hzn, hzd⟩ := rename_galNum_galDen_of_isFourBlock (k := k) hB hw hT (g := z)
    (fun t => ((hu z huz) t).1) (fun t => ((hu z huz) t).2)
  have e2 : rename ⇑z.1 (a 1) * d = rename ⇑z.1 M * n := by
    have e := congrArg (rename ⇑z.1) h1
    rw [map_mul, map_mul, show rename ⇑z.1 d = d from hzd,
      show rename ⇑z.1 n = n from hzn] at e
    exact e
  have e3 : N1 1 * MU = P1 := by
    have := Finset.prod_erase_mul (Finset.univ : Finset (ColPerm ν))
      (fun y' : ColPerm ν => rename ⇑y'.1 MU) (Finset.mem_univ 1)
    rwa [rename_colPerm_one] at this
  have e4 : N2 z * rename ⇑z.1 M = P2 :=
    Finset.prod_erase_mul (Finset.univ : Finset (ColPerm ν))
      (fun y' : ColPerm ν => rename ⇑y'.1 M) (Finset.mem_univ z)
  refine hdreg.left ?_
  show d * _ = d * 0
  linear_combination (P2 * MU * N1 1 * u z) * h1' - (P1 * M' * u z * N2 z) * e2 +
    (P2 * u z * M' * n) * e3 - (P1 * M' * u z * n) * e4

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- In the polynomial representation, the four-block shuffle `r ρ T * galList B w` acts from
`B` to `ρ • T` by `ren ρ ∘ opList B w`. -/
theorem blockOp_r_mul_galList {B T : FullChamber Γ ν} {w : List (Hyp Γ ν)}
    (hT : B.flips w = T) (ρ : ColPerm ν) :
    blockOp k hΓ (ρ • T) B (r ρ T * galList k B w) = ren ρ ∘ₗ opList k Γ B w := by
  refine blockOp_of_galleryRep_eq_blk hΓ ?_
  rw [map_mul, galleryRep_r, galleryRep_galList, hT, Module.End.mul_eq_comp, blk_comp_blk]

/-- **Balancedness of the four-block shuffle modulo lower shuffle types**, in the algebra. Let
`μ` be a shuffle type, `Z = blockLeft ν' ν₁ μ`, `B`, `B'` four-block chambers for the strands of
`ν'` and `Z`, and `ρ` the relabelling rank-ordering `shuffleTop Z B`. Let `u ∈ e B' A e B` act
in the polynomial representation by an operator `U` supported in the block-preserving
relabellings, and `u'' ∈ e (ρ • shuffleTop Z B') A e (ρ • shuffleTop Z B)` act by the conjugate
`ρ U ρ⁻¹`. Then `fourShuffle Z B' * u - u'' * fourShuffle Z B` lies in the step of the
filtration of the shuffle types strictly below `μ`.

A step of the proof of Webster, arXiv:1209.2463v4, Theorem 2.19. -/
theorem fourShuffle_mul_sub_mul_fourShuffle_mem_mackeyFilt (hν' : ν' + ν'' = ν)
    (hν₁ : ν₁ + ν₂ = ν) {μ : I → ℕ} (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁))
    {B B' : FullChamber Γ ν}
    (hB : IsFourBlock (fun t => decide (t.IsLeft ν')) (blockLeft ν' ν₁ μ) B)
    (hB' : IsFourBlock (fun t => decide (t.IsLeft ν')) (blockLeft ν' ν₁ μ) B')
    {ρ : ColPerm ν} (hρ : (ρ • shuffleTop (blockLeft ν' ν₁ μ) B).IsRankOrdered)
    {u u'' : GalleryAlgebra k Γ ν} (hu : u ∈ cornerSpace k B' B)
    (hu'' : u'' ∈ cornerSpace k (ρ • shuffleTop (blockLeft ν' ν₁ μ) B')
      (ρ • shuffleTop (blockLeft ν' ν₁ μ) B))
    (hUs : IsSupported (blockOp k hΓ B' B u)
      {y | ∀ t, decide ((y.1 t).IsLeft ν') = decide (t.IsLeft ν') ∧
        blockLeft ν' ν₁ μ (y.1 t) = blockLeft ν' ν₁ μ t})
    (hU'' : blockOp k hΓ (ρ • shuffleTop (blockLeft ν' ν₁ μ) B')
      (ρ • shuffleTop (blockLeft ν' ν₁ μ) B) u'' =
        ren ρ ∘ₗ blockOp k hΓ B' B u ∘ₗ ren ρ⁻¹) :
    fourShuffle k hD hZ (blockLeft ν' ν₁ μ) B' * u -
        u'' * fourShuffle k hD hZ (blockLeft ν' ν₁ μ) B ∈
      mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ (ρ • shuffleTop (blockLeft ν' ν₁ μ) B') B
        (Set.Iio μ) := by
  classical
  set Zμ := blockLeft ν' ν₁ μ
  set T := shuffleTop Zμ B
  set T' := shuffleTop Zμ B'
  have hρ' : (ρ • T').IsRankOrdered :=
    isRankOrdered_smul_shuffleTop_of_isRankOrdered hB.1 hB'.1 hρ
  obtain ⟨w, hw, hT⟩ := exists_goodWord hD hZ B T
  obtain ⟨w', hw', hT'⟩ := exists_goodWord hD hZ B' T'
  rw [fourShuffle_eq (k := k) hD hZ Zμ B hρ hw hT, fourShuffle_eq (k := k) hD hZ Zμ B' hρ' hw' hT']
  set F := r ρ T * galList k B w
  set F' := r ρ T' * galList k B' w'
  have heF : e (ρ • T) * F = F := by
    simp only [F, ← mul_assoc, e_mul_r, ↓reduceIte]
  have heF' : e (ρ • T') * F' = F' := by
    simp only [F', ← mul_assoc, e_mul_r, ↓reduceIte]
  have hFe : F * e B = F := by simp only [F, mul_assoc, galList_mul_e]
  have hu1 := mem_cornerSpace_iff.1 hu
  have hu2 := mem_cornerSpace_iff.1 hu''
  have heu : e B' * u = u := by
    rw [← hu1, ← mul_assoc, ← mul_assoc, e_mul_e, ite_eq_left rfl]
  have hue : u * e B = u := by rw [← hu1, mul_assoc, e_mul_e, ite_eq_left rfl]
  have heu'' : e (ρ • T') * u'' = u'' := by
    rw [← hu2, ← mul_assoc, ← mul_assoc, e_mul_e, ite_eq_left rfl]
  have hmem : F' * u - u'' * F ∈ cornerSpace k (ρ • T') B := by
    refine mem_cornerSpace_iff.2 ?_
    have : e (ρ • T') * (F' * u - u'' * F) * e B =
        (e (ρ • T') * F') * (u * e B) - (e (ρ • T') * u'') * (F * e B) := by
      simp only [mul_sub, sub_mul, mul_assoc]
    rw [this, heF', hue, heu'', hFe]
  rw [mem_mackeyFilt_iff hP hD hZ hΓ hW hL ν' ν₁ hB.1 hρ' (isLowerSet_Iio μ) hmem]
  have hsub : ∀ a b : GalleryAlgebra k Γ ν,
      blockOp k hΓ (ρ • T') B (a - b) = blockOp k hΓ (ρ • T') B a - blockOp k hΓ (ρ • T') B b :=
    fun a b => LinearMap.ext fun f => by
      simp only [blockOp_apply, map_sub, LinearMap.sub_apply, Pi.sub_apply]
  have hrr : ren (k := k) ρ⁻¹ ∘ₗ ren ρ = LinearMap.id := LinearMap.ext fun f => by
    show rename ⇑(ρ⁻¹).1 (rename ⇑ρ.1 f) = f
    rw [← rename_colPerm_mul, inv_mul_cancel, rename_colPerm_one]
  rw [hsub, blockOp_mul hΓ F' heu, blockOp_mul hΓ u'' heF, hU'',
    blockOp_r_mul_galList hΓ hT ρ, blockOp_r_mul_galList hΓ hT' ρ]
  have key : (ren ρ ∘ₗ opList k Γ B' w') ∘ₗ blockOp k hΓ B' B u -
      (ren ρ ∘ₗ blockOp k hΓ B' B u ∘ₗ ren ρ⁻¹) ∘ₗ (ren ρ ∘ₗ opList k Γ B w) =
      ren ρ ∘ₗ (opList k Γ B' w' ∘ₗ blockOp k hΓ B' B u -
        blockOp k hΓ B' B u ∘ₗ opList k Γ B w) := by
    refine LinearMap.ext fun f => ?_
    have e := LinearMap.congr_fun hrr (opList k Γ B w f)
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply] at e ⊢
    rw [e, map_sub]
  rw [key]
  refine ((isSupported_opList_comp_sub_comp_opList (k := k) hν' hν₁ hμ hB hB' hw hw' hT hT' hρ
    hUs).rename ρ).mono ?_
  rintro y ⟨x, hx, rfl⟩
  exact hx

end GalleryAlgebra

end Categorification.WeightedKLR
