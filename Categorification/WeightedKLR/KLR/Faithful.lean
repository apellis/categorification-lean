/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GalleryBasis.Basis

/-!
# Faithfulness of the polynomial representation of the gallery algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.8 and Proposition 2.14.

The proof of the basis theorem (`GalleryAlgebra.linearIndependent_basisElt`) shows that the
basis elements act by linearly independent operators in the polynomial representation; since they
form a basis, the representation is faithful. Proposition 2.14 of the paper identifies the
weighted KLR algebra of the evenly spaced loadings with a KLR algebra by comparing polynomial
representations, for which faithfulness is the input used here.

## Main results

* `GalleryAlgebra.linearIndependent_galleryRep_basisElt`: the operators of the basis elements
  are linearly independent.
* `GalleryAlgebra.galleryRep_injective`: under the hypotheses of the basis theorem, the
  polynomial representation `galleryRep` is injective.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

namespace GalleryAlgebra

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, Simple (hypAff (Γ := Γ)) (P C E).1 (P C E).2 ∧
    fullSigns (P C E).1 = C.1 ∧ fullSigns (P C E).2 = E.1)
include hP

/-- The operators of the basis elements in the polynomial representation are linearly
independent (the argument of `linearIndependent_basisElt`). -/
theorem linearIndependent_galleryRep_basisElt (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (P : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some P → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor P a b)) :
    LinearIndependent k (fun i : FullChamber Γ ν × FullChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ) =>
      galleryRep k hΓ (basisElt k P i.1 i.2.1 i.2.2.1 i.2.2.2)) := by
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
    have := congrArg (fun x => x (Pi.single C₀ f) D₀) hl
    simp only [Finsupp.linearCombination_apply, Finsupp.sum] at this
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

omit hP in
/-- **Faithfulness of the polynomial representation.** Under the hypotheses of the basis theorem
(Webster's condition (†), no loops of weight `0`, symmetric loop polynomials, and wall and loop
polynomials that are non-zero-divisors), `galleryRep` is injective. -/
theorem galleryRep_injective (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b)) :
    Function.Injective (galleryRep k hΓ (ν := ν)) := by
  obtain ⟨P, hP, -⟩ := exists_span_segGallery (k := k) (ν := ν) hD hZ
  set b := basisOfSegments hP hD hZ hΓ hW hL
  have hb : ⇑b = fun i => basisElt k P i.1 i.2.1 i.2.2.1 i.2.2.2 := by
    funext i
    obtain ⟨C, E, g, m⟩ := i
    simp [b, basisElt, segGallery]
  have hli := linearIndependent_galleryRep_basisElt (fun C E => hP C E) hΓ hW hL
  have h' : ∀ z, galleryRep k hΓ (Finsupp.linearCombination k b z) =
      Finsupp.linearCombination k (fun i : FullChamber Γ ν × FullChamber Γ ν × ColPerm ν ×
        (Strand ν →₀ ℕ) => galleryRep k hΓ (basisElt k P i.1 i.2.1 i.2.2.1 i.2.2.2)) z := by
    intro z
    have := Finsupp.apply_linearCombination k (galleryRep k hΓ).toLinearMap (⇑b) z
    rw [hb] at this ⊢
    exact this
  intro x y hxy
  rw [← b.linearCombination_repr x, ← b.linearCombination_repr y] at hxy ⊢
  rw [h', h'] at hxy
  rw [hli hxy]

end GalleryAlgebra

end Categorification.WeightedKLR
