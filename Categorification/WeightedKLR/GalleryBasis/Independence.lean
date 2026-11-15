/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GalleryBasis.Leading

/-!
# Linear independence of the straight-line gallery basis

Linear-independence half of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.8 (the basis theorem). Fix for each pair of full chambers `C, E` a
simple segment `P C E` from a generic point of `C` to a generic point of `E`. The elements

  `basisElt k P C E g m = r g E * galList C (word (P C E)) * poly (y^m)`,

the gallery of the segment from `C` to `E`, followed by the relabelling `g`, with a monomial in
the dots at the bottom, are linearly independent over `k` (`linearIndependent_basisElt`).
The hypothesis `hP` on the segments and the gallery `galList C (word (P C E))` are, by
definition, `GalleryAlgebra.IsChamberSegment` and `GalleryAlgebra.segGallery` of the spanning
half (`GallerySpan.Spanning`); they are written out here so that this file only needs the
segment API.

The proof is Webster's. In the polynomial representation, from the copy of `C₀` to the copy of
`D₀`, the elements with `C = C₀` and `g • E = D₀` act by `f ↦ ren g (opList (word) (y^m f))`. By
`exists_isTwisted_opList`, after multiplication by a non-zero-divisor such an operator is
`∑ₓ aₓ · x(f)`, whose top term `x = g` has a non-zero-divisor coefficient and whose other terms are
lower for the number of hyperplanes separating `C₀` from `x⁻¹ • D₀`. Dedekind independence of
the relabellings (`eq_zero_of_forall_sum_twisted_eq_zero`) then forces all coefficients to vanish.

The hypotheses are that the wall polynomials `Q_e(y_a, y_b)` and the loop polynomials
`P_i(y_a, y_b)` are non-zero-divisors, and that the loop polynomials are symmetric
(`Γ.PSymm`, needed for the polynomial representation).

## Main definitions

* `GalleryAlgebra.basisElt k P C E g m`: the basis element.

## Main results

* `GalleryAlgebra.galleryRep_basisElt`: its action in the polynomial representation.
* `GalleryAlgebra.linearIndependent_basisElt`: the basis elements are linearly independent.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

namespace GalleryAlgebra

variable (P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜))

variable (k) in
/-- The basis element: the chosen gallery from `C` to `E`, then the relabelling `g`, with the
monomial `y^m` in the dots at the bottom. -/
noncomputable def basisElt (C E : FullChamber Γ ν) (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    GalleryAlgebra k Γ ν :=
  r g E * galList k C (word (hypAff (Γ := Γ)) (P C E).1 (P C E).2) * poly (monomial m 1)

variable {P} (hP : ∀ C E, Simple (hypAff (Γ := Γ)) (P C E).1 (P C E).2 ∧
  fullSigns (P C E).1 = C.1 ∧ fullSigns (P C E).2 = E.1)
include hP

/-- The word of the chosen segment is good from `C`. -/
theorem goodWord_segWord (C E : FullChamber Γ ν) :
    GoodWord C.1 (word (hypAff (Γ := Γ)) (P C E).1 (P C E).2) :=
  (hP C E).2.1 ▸ goodWord_word (hP C E).1

/-- The gallery of the chosen segment from `C` ends in `E`. -/
theorem flips_segWord_eq (C E : FullChamber Γ ν) :
    C.flips (word (hypAff (Γ := Γ)) (P C E).1 (P C E).2) = E := by
  have hw := goodWord_segWord hP C E
  refine Subtype.ext ?_
  rw [← (hP C E).2.2, flips_val hw]
  have h1 := (hP C E).2.1
  rw [← h1]
  exact flipSigns_word (f := hypAff (Γ := Γ))

/-- The action of a basis element in the polynomial representation. -/
theorem galleryRep_basisElt (hΓ : Γ.PSymm) (C E : FullChamber Γ ν) (g : ColPerm ν)
    (m : Strand ν →₀ ℕ) :
    galleryRep k hΓ (basisElt k P C E g m) = blk k C (g • E)
      (ren g ∘ₗ opList k Γ C (word (hypAff (Γ := Γ)) (P C E).1 (P C E).2) ∘ₗ
        LinearMap.mulLeft k (monomial m 1)) := by
  rw [basisElt, map_mul, map_mul, galleryRep_r, galleryRep_galList,
    flips_segWord_eq hP, galleryRep_poly, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    blk_comp_blk, blk_comp_diagOp, LinearMap.comp_assoc]

/-- The relabelled gallery operator from `C` to `D` through `g⁻¹ • D` is twisted, with top term
at `g` for the number of hyperplanes separating `C` from `x⁻¹ • D`. -/
theorem exists_isTwisted_ren_opList (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (P : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some P → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor P a b))
    (C D : FullChamber Γ ν) (g : ColPerm ν) :
    ∃ (M : PolyRing ν k) (a : ColPerm ν → PolyRing ν k), IsRegular M ∧
      IsTwisted (ren g ∘ₗ
        opList k Γ C (word (hypAff (Γ := Γ)) (P C (g⁻¹ • D)).1 (P C (g⁻¹ • D)).2)) M a ∧
      IsRegular (a g) ∧
      ∀ x, a x ≠ 0 → x ≠ g → sepCard C.1 (x⁻¹ • D).1 < sepCard C.1 (g⁻¹ • D).1 := by
  obtain ⟨M, a, hM, hT, ha1, hlt⟩ := exists_isTwisted_opList hW hL (goodWord_segWord hP C (g⁻¹ • D))
  rw [flips_segWord_eq hP] at hlt
  refine ⟨rename ⇑g.1 M, fun y => rename ⇑g.1 (a (g⁻¹ * y)), isRegular_rename_colPerm hM g,
    hT.rename g, ?_, fun x hx hxg => ?_⟩
  · simpa only [inv_mul_cancel] using isRegular_rename_colPerm ha1 g
  · have hax : a (g⁻¹ * x) ≠ 0 := fun h0 => hx (by simp only [h0, map_zero])
    have hne : g⁻¹ * x ≠ 1 := fun h1 => hxg (inv_mul_eq_one.1 h1).symm
    have := hlt _ hax hne
    rwa [mul_inv_rev, inv_inv, mul_smul, smul_inv_smul] at this

/-- **Webster, Theorem 2.8, linear-independence half**, for the gallery algebra: if the wall
polynomials and the loop polynomials are non-zero-divisors and the loop polynomials are
symmetric, the elements `r g E * galList C (word (P C E)) * poly (y^m)` are linearly independent. -/
theorem linearIndependent_basisElt (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (P : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some P → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor P a b)) :
    LinearIndependent k (fun i : FullChamber Γ ν × FullChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ) =>
      basisElt k P i.1 i.2.1 i.2.2.1 i.2.2.2) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  refine Finsupp.ext fun i₀ => ?_
  obtain ⟨C₀, E₀, g₀, m₀⟩ := i₀
  rw [Finsupp.coe_zero, Pi.zero_apply]
  set D₀ := g₀ • E₀ with hD₀
  -- the operators from the copy of `C₀` to the copy of `D₀`
  set Y : ColPerm ν → PolyRing ν k →ₗ[k] PolyRing ν k := fun g => ren g ∘ₗ
    opList k Γ C₀ (word (hypAff (Γ := Γ)) (P C₀ (g⁻¹ • D₀)).1 (P C₀ (g⁻¹ • D₀)).2) with hY
  -- the coefficient polynomial of the relabelling `g`
  set F : ColPerm ν → PolyRing ν k := fun g =>
    ∑ i ∈ l.support.filter (fun i => i.1 = C₀ ∧ i.2.2.1 = g ∧ g • i.2.1 = D₀),
      monomial i.2.2.2 (l i) with hFdef
  -- the action of each basis element, evaluated at `f` in the copy of `C₀`, at the copy of `D₀`
  set T : (FullChamber Γ ν × FullChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ)) →
      PolyRing ν k → PolyRing ν k := fun i f =>
    if i.1 = C₀ ∧ i.2.2.1 • i.2.1 = D₀ then
      ren i.2.2.1 (opList k Γ C₀ (word (hypAff (Γ := Γ)) (P C₀ i.2.1).1 (P C₀ i.2.1).2)
        (monomial i.2.2.2 1 * f))
    else 0 with hTdef
  have hv : ∀ i f, galleryRep k hΓ (basisElt k P i.1 i.2.1 i.2.2.1 i.2.2.2) (Pi.single C₀ f) D₀ =
      T i f := by
    rintro ⟨C, E, g, m⟩ f
    rw [galleryRep_basisElt hP, blk_apply]
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
    have := congrArg (fun x => galleryRep k hΓ x (Pi.single C₀ f) D₀) hl
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
  choose M a hM hT ha hlt using fun g => exists_isTwisted_ren_opList (k := k) hP hW hL C₀ D₀ g
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

end GalleryAlgebra

end Categorification.WeightedKLR
