/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Twisted.Leading
import Categorification.WeightedKLR.Twisted.Spanning

/-!
# Linear independence of the straight-line basis of the twisted gallery algebra

Linear-independence half of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, §2.5, Proposition 2.20 (b), proved as Theorem 2.8. Fix for each pair of
chambers `C, E` of the arrangement of positions and weights a simple segment `P C E` from a
generic point of `C` to a generic point of `E` (`IsChamberSegment`). The elements

  `basisElt k P C E g m = r g E * segGallery P C E * poly (y^m)`

are linearly independent over `k` (`linearIndependent_basisElt`).

In the representation `twGalleryRep`, from the copy of `C₀` to the copy of `D₀`, the elements with
`C = C₀` and `g • E = D₀` act by `f ↦ ren g (twOpList (word) (y^m f))`. By
`exists_isTwisted_twOpList`, after multiplication by a non-zero-divisor such an operator is
`∑ₓ aₓ · x(f)` with a non-zero-divisor top coefficient at `x = g` and lower terms for the number
of hyperplanes separating `C₀` from `x⁻¹ • D₀`; Dedekind independence of the relabellings
(`eq_zero_of_forall_sum_twisted_eq_zero`) forces all coefficients to vanish.

## Main definitions

* `TwGalleryAlgebra.basisElt k P C E g m`: the basis element.

## Main results

* `TwGalleryAlgebra.twGalleryRep_basisElt`: its action in the polynomial representation.
* `TwGalleryAlgebra.linearIndependent_basisElt`: the basis elements are linearly independent.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv TwChamber Segment

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

namespace TwGalleryAlgebra

variable (P : TwChamber Γ ν → TwChamber Γ ν → (Strand ν ⊕ Γ.E → 𝕜) × (Strand ν ⊕ Γ.E → 𝕜))

variable (k) in
/-- The basis element: the chosen gallery from `C` to `E`, then the relabelling `g`, with the
monomial `y^m` in the dots at the bottom. -/
noncomputable def basisElt (C E : TwChamber Γ ν) (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    TwGalleryAlgebra k Γ ν :=
  r g E * segGallery P C E * poly (monomial m 1)

variable {P} (hP : ∀ C E, IsChamberSegment C E (P C E))
include hP

/-- The word of the chosen segment is good from `C`. -/
theorem twGoodWord_segWord (C E : TwChamber Γ ν) :
    TwGoodWord C.1 (word (twAff (Γ := Γ) (ν := ν)) (P C E).1 (P C E).2) :=
  (goodWord_flips_word (hP C E).1 (hP C E).2.1).1

/-- The action of a basis element in the polynomial representation. -/
theorem twGalleryRep_basisElt (hΓ : Γ.PSymm) (C E : TwChamber Γ ν) (g : ColPerm ν)
    (m : Strand ν →₀ ℕ) :
    twGalleryRep k hΓ (basisElt k P C E g m) = blk k C (g • E)
      (ren g ∘ₗ twOpList k Γ C (word (twAff (Γ := Γ) (ν := ν)) (P C E).1 (P C E).2) ∘ₗ
        LinearMap.mulLeft k (monomial m 1)) := by
  rw [basisElt, segGallery, map_mul, map_mul, twGalleryRep_r, twGalleryRep_galList,
    flips_segWord hP, twGalleryRep_poly, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    blk_comp_blk, blk_comp_diagOp, LinearMap.comp_assoc]

/-- The relabelled gallery operator from `C` to `D` through `g⁻¹ • D` is twisted, with top term
at `g` for the number of hyperplanes separating `C` from `x⁻¹ • D`. -/
theorem exists_isTwisted_ren_twOpList (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (P : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some P → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor P a b))
    (C D : TwChamber Γ ν) (g : ColPerm ν) :
    ∃ (M : PolyRing ν k) (a : ColPerm ν → PolyRing ν k), IsRegular M ∧
      IsTwisted (ren g ∘ₗ twOpList k Γ C
        (word (twAff (Γ := Γ) (ν := ν)) (P C (g⁻¹ • D)).1 (P C (g⁻¹ • D)).2)) M a ∧
      IsRegular (a g) ∧
      ∀ x, a x ≠ 0 → x ≠ g → sepCard C.1 (x⁻¹ • D).1 < sepCard C.1 (g⁻¹ • D).1 := by
  obtain ⟨M, a, hM, hT, ha1, hlt⟩ :=
    exists_isTwisted_twOpList hW hL (twGoodWord_segWord hP C (g⁻¹ • D))
  rw [flips_segWord hP] at hlt
  refine ⟨rename ⇑g.1 M, fun y => rename ⇑g.1 (a (g⁻¹ * y)), isRegular_rename_colPerm hM g,
    hT.rename g, ?_, fun x hx hxg => ?_⟩
  · simpa only [inv_mul_cancel] using isRegular_rename_colPerm ha1 g
  · have hax : a (g⁻¹ * x) ≠ 0 := fun h0 => hx (by simp only [h0, map_zero])
    have hne : g⁻¹ * x ≠ 1 := fun h1 => hxg (inv_mul_eq_one.1 h1).symm
    have := hlt _ hax hne
    rwa [mul_inv_rev, inv_inv, mul_smul, smul_inv_smul] at this

/-- **Webster, Proposition 2.20 (b), linear-independence half**: if the wall polynomials and the
loop polynomials are non-zero-divisors and the loop polynomials are symmetric, the elements
`r g E * segGallery P C E * poly (y^m)` of the twisted gallery algebra are linearly
independent. -/
theorem linearIndependent_basisElt (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (P : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some P → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor P a b)) :
    LinearIndependent k (fun i : TwChamber Γ ν × TwChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ) =>
      basisElt k P i.1 i.2.1 i.2.2.1 i.2.2.2) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  refine Finsupp.ext fun i₀ => ?_
  obtain ⟨C₀, E₀, g₀, m₀⟩ := i₀
  rw [Finsupp.coe_zero, Pi.zero_apply]
  set D₀ := g₀ • E₀ with hD₀
  -- the operators from the copy of `C₀` to the copy of `D₀`
  set Y : ColPerm ν → PolyRing ν k →ₗ[k] PolyRing ν k := fun g => ren g ∘ₗ twOpList k Γ C₀
    (word (twAff (Γ := Γ) (ν := ν)) (P C₀ (g⁻¹ • D₀)).1 (P C₀ (g⁻¹ • D₀)).2) with hY
  -- the coefficient polynomial of the relabelling `g`
  set F : ColPerm ν → PolyRing ν k := fun g =>
    ∑ i ∈ l.support.filter (fun i => i.1 = C₀ ∧ i.2.2.1 = g ∧ g • i.2.1 = D₀),
      monomial i.2.2.2 (l i) with hFdef
  -- the action of each basis element, evaluated at `f` in the copy of `C₀`, at the copy of `D₀`
  set T : (TwChamber Γ ν × TwChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ)) →
      PolyRing ν k → PolyRing ν k := fun i f =>
    if i.1 = C₀ ∧ i.2.2.1 • i.2.1 = D₀ then
      ren i.2.2.1 (twOpList k Γ C₀ (word (twAff (Γ := Γ) (ν := ν)) (P C₀ i.2.1).1
        (P C₀ i.2.1).2) (monomial i.2.2.2 1 * f))
    else 0 with hTdef
  have hv : ∀ i f, twGalleryRep k hΓ (basisElt k P i.1 i.2.1 i.2.2.1 i.2.2.2)
      (Pi.single C₀ f) D₀ = T i f := by
    rintro ⟨C, E, g, m⟩ f
    rw [twGalleryRep_basisElt hP, blk_apply]
    simp only [hTdef]
    by_cases hC : C = C₀
    · subst hC
      by_cases hD : g • E = D₀
      · rw [Pi.single_apply, ite_eq_left_iff.2 fun h => absurd hD.symm h,
          ite_eq_left_iff.2 fun h => absurd ⟨rfl, hD⟩ h, Pi.single_eq_same]
        rfl
      · rw [Pi.single_apply, ite_eq_right_iff.2 fun h => absurd h.symm hD,
          ite_eq_right_iff.2 fun h => absurd h.2 hD]
    · simp [Pi.single_apply, hC]
  have hsum : ∀ f, ∑ i ∈ l.support, l i • T i f = 0 := by
    intro f
    have := congrArg (fun x => twGalleryRep k hΓ x (Pi.single C₀ f) D₀) hl
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, map_zero] at this
    rw [LinearMap.sum_apply, Finset.sum_apply] at this
    simpa only [LinearMap.smul_apply, Pi.smul_apply, hv, LinearMap.zero_apply,
      Pi.zero_apply] using this
  have hF : ∀ f, ∑ g, Y g (F g * f) = 0 := by
    intro f
    rw [← hsum f]
    simp only [hFdef, Finset.sum_mul, map_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : i.1 = C₀ ∧ i.2.2.1 • i.2.1 = D₀
    · rw [Finset.sum_eq_single i.2.2.1]
      · rw [ite_eq_left_iff.2 fun h => absurd ⟨h1.1, rfl, h1.2⟩ h]
        have hE : i.2.2.1⁻¹ • D₀ = i.2.1 := inv_smul_eq_iff.2 h1.2.symm
        simp only [hY, hTdef, ite_eq_left_iff.2 fun h => absurd h1 h, LinearMap.comp_apply, hE]
        rw [← map_smul, ← map_smul, ← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
      · intro g _ hg
        rw [ite_eq_right_iff.2 fun (h : i.1 = C₀ ∧ i.2.2.1 = g ∧ g • i.2.1 = D₀) =>
          absurd h.2.1.symm hg, zero_mul, map_zero]
      · exact fun h => absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_zero fun g _ => by
        rw [ite_eq_right_iff.2 fun (h : i.1 = C₀ ∧ i.2.2.1 = g ∧ g • i.2.1 = D₀) =>
          absurd ⟨h.1, by rw [h.2.1]; exact h.2.2⟩ h1, zero_mul, map_zero]]
      simp only [hTdef, ite_eq_right_iff.2 fun h => absurd h h1, smul_zero]
  choose M a hM hT ha hlt using fun g =>
    exists_isTwisted_ren_twOpList (k := k) hP hW hL C₀ D₀ g
  have hF0 := eq_zero_of_forall_sum_twisted_eq_zero (Y := Y)
    (fun x => sepCard C₀.1 (x⁻¹ • D₀).1) hM hT ha hlt hF
  by_cases hmem : (C₀, E₀, g₀, m₀) ∈ l.support
  · have h0 : (F g₀).coeff m₀ = 0 := by simp [congrFun hF0 g₀]
    simp only [hFdef, coeff_sum, coeff_monomial] at h0
    rw [Finset.sum_eq_single_of_mem (C₀, E₀, g₀, m₀)] at h0
    · simpa only [ite_true] using h0
    · exact Finset.mem_filter.2 ⟨hmem, rfl, rfl, rfl⟩
    · rintro ⟨C, E, g, m⟩ hb hne
      obtain ⟨-, hC, hg, hE⟩ := Finset.mem_filter.1 hb
      simp only at hC hg hE
      subst hC hg
      have hE' : E = E₀ := (smul_left_cancel_iff g).1 hE
      subst hE'
      exact ite_eq_right_iff.2 fun (hm : m = m₀) => absurd (by rw [hm]) hne
  · exact Finsupp.notMem_support_iff.1 hmem

end TwGalleryAlgebra

end Categorification.WeightedKLR
