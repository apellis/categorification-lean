/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicLowerExactZero

/-!
# Polynomial splittings of the genuine cyclotomic columns

For `β = {i} + γ`, the actual restricted maps `eiB` and `eiC` have explicit
polynomial right sections `eiBSection` and `eiCSection`. The existing ambient
sections first satisfy both required colour cuts: the full first-strand crossing
moves the initial `i` to the last position, while `cLL` has the last-colour cut
on both sides. Only then are the sections transported through the canonical
quotient-to-balanced-tensor maps. Their complete forward compositions are
`eiB_eiBSection` and `eiC_eiCSection`.

Together with the explicit kernel inverses, these give `eiBSplitEquiv` and
`eiCSplitEquiv`: the genuine lower tensor times `R^Λ(β)[t]` is k-linearly
equivalent to the actual cut tensor. The inverse subtracts the polynomial
section of the existing `B` or `C` coordinate and applies the kernel decoder.
Both summand inclusions and the polynomial projections retain these actual maps.

This is the k-linear splitting of the columns in Kang–Kashiwara,
arXiv:1102.4677v4, §5.2, using Prop. 3.3 and Cor. 3.8. The source's graded
bimodule assertions are stronger; no graded or bimodule splitting is claimed.
The existing ψ-normalization of `B` and the convention `ψ = −τ` are unchanged.

The cuts and sections require only a commutative base ring. The right-inverse
and decomposition theorems retain the coordinate hypotheses: a domain with
nonzero off-diagonal factors of `Q`. The cyclotomic polynomials are arbitrary,
including the constant-one family, and `γ = 0` is included. No flatness,
monicity, quotient nontriviality or Cartan-degree hypothesis is added.
Absent-colour blocks, snake connecting maps and the final bimodule inverses
of Theorems 5.1–5.2 remain separate.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open scoped TensorProduct
open TypeA
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β" => (Si + γ)
variable (a : I → Polynomial k)
local notation "Rl" => CycKLR k Q a β

/-- A full crossing transports the initial-colour cut to the final-colour cut. -/
theorem cL_one_mul_fullCrossing :
    cL Q i γ 1 * ψw (descRun 0 (Multiset.card γ)) =
      ψw (descRun 0 (Multiset.card γ)) * cR Q i γ 1 := by
  have hw : wordProd (Multiset.card (Si + γ)) (descRun 0 (Multiset.card γ)) =
      cP (Multiset.card (Si + γ)) (Multiset.card γ) := by
    simp only [wordProd, descRun, List.range_eq_range', cP]
  rw [cL_one, cR_one_eq, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [ψw_mul_e, hw, cP_smul_cons1]

/-- The ambient B-section has the required right initial-colour cut. -/
theorem bSection_rightCut (p : Polynomial Rl) :
    kOneRightCut Q i β a (by simp) (bSection i β a (by simp)
      (zero_lt_card_single_add i γ) p) = bSection i β a (by simp)
        (zero_lt_card_single_add i γ) p := by
  obtain ⟨t, rfl⟩ := thetaL_surjective i β a p
  rw [bSection_thetaL, kOneRightCut_mk, mul_assoc, concat_mul_oneConcat]

/-- The ambient B-section has the required left final-colour cut. -/
theorem bSection_leftCut (p : Polynomial Rl) :
    cL Q i β 1 • bSection i β a (by simp) (zero_lt_card_single_add i γ) p =
      bSection i β a (by simp) (zero_lt_card_single_add i γ) p := by
  obtain ⟨t, rfl⟩ := thetaL_surjective i β a p
  rw [bSection_thetaL]
  change Submodule.Quotient.mk (cL Q i β 1 * (ψw _ * concat Q Si β t)) = _
  rw [← mul_assoc, cL_one_mul_fullCrossing, mul_assoc, cR_one, oneConcat_mul_concat]

def eiBSectionUncut : Polynomial Rl →ₗ[k] KOneTensor Q i β a :=
  ((kOneToTensor Q i β a (by simp) (zero_lt_card_single_add i γ)).restrictScalars k).comp
    (bSection i β a (by simp) (zero_lt_card_single_add i γ))

theorem eiBSectionUncut_mem (p : Polynomial Rl) :
    eiBSectionUncut Q i γ a p ∈
      Graded.idemSubspace k (KOneTensor Q i β a) (cL Q i β 1) := by
  change cL Q i β 1 • kOneToTensor Q i β a (by simp) (zero_lt_card_single_add i γ) _ = _
  rw [← map_smul, bSection_leftCut]
  rfl

/-- The explicit full-crossing section in the actual left-cut balanced tensor. -/
def eiBSection : Polynomial Rl →ₗ[k] EIKOne Q i β a :=
  (eiBSectionUncut Q i γ a).codRestrict _ (eiBSectionUncut_mem Q i γ a)

/-- Canonical tensor multiplication recovers the original ambient B-section. -/
theorem eiBSection_coordinates (p : Polynomial Rl) :
    tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ)
      (eiBSection Q i γ a p) =
      bSection i β a (by simp) (zero_lt_card_single_add i γ) p := by
  change tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ)
    (kOneToTensor Q i β a (by simp) (zero_lt_card_single_add i γ) _) = _
  rw [tensorToKOne_kOneToTensor, bSection_rightCut]

/-- The ambient C-section has the required right final-colour cut. -/
theorem cSection_rightCut (p : Polynomial Rl) :
    act0 Q i β a 1 (cSection i β a (zero_lt_card_single_add i γ) p) =
      cSection i β a (zero_lt_card_single_add i γ) p := by
  obtain ⟨t, rfl⟩ := thetaL0_surjective i β a p
  rw [cSection_thetaL0, act0_mk, cLL_mul_cL_one]

/-- The ambient C-section has the required left final-colour cut. -/
theorem cSection_leftCut (p : Polynomial Rl) :
    cL Q i β 1 • cSection i β a (zero_lt_card_single_add i γ) p =
      cSection i β a (zero_lt_card_single_add i γ) p := by
  obtain ⟨t, rfl⟩ := thetaL0_surjective i β a p
  rw [cSection_thetaL0]
  change Submodule.Quotient.mk (cL Q i β 1 * cLL Q i β t) = _
  rw [cL_one_mul_cLL]

/-- Multiset transport and its inverse cancel on the quotient. -/
theorem lowerQuotientCast_uncast
    (z : KZero Q (Si + β) a (zero_lt_card_single_add i β)) :
    lowerQuotientCast Q i γ a (lowerQuotientUncast Q i γ a z) = z := by
  induction z using Submodule.Quotient.induction_on with
  | _ r =>
    change Submodule.Quotient.mk (castKLR Q (add_comm β Si)
      (castKLR Q (add_comm β Si).symm r)) = _
    rw [castKLR_castAlg_symm]

theorem lowerQuotientUncast_leftCut
    (z : KZero Q (Si + β) a (zero_lt_card_single_add i β)) :
    lowerQuotientUncast Q i γ a (cL Q i β 1 • z) =
      oneConcat Q β Si • lowerQuotientUncast Q i γ a z := by
  apply lowerQuotientCast_injective Q i γ a
  rw [lowerQuotientCast_uncast, lowerQuotientCast_leftCut, lowerQuotientCast_uncast]

def eiCSectionUncut : Polynomial Rl →ₗ[k] KZeroTensor Q i β a :=
  (lowerZeroDecode Q i γ a).comp (cSection i β a (zero_lt_card_single_add i γ))

theorem eiCSectionUncut_mem (p : Polynomial Rl) :
    eiCSectionUncut Q i γ a p ∈
      Graded.idemSubspace k (KZeroTensor Q i β a) (oneConcat Q β Si) := by
  change oneConcat Q β Si • kZeroToTensor Q i β a (by simp)
    (zero_lt_card_single_add i γ) (lowerQuotientUncast Q i γ a
      (cSection i β a (zero_lt_card_single_add i γ) p)) = _
  rw [← map_smul, ← lowerQuotientUncast_leftCut, cSection_leftCut]
  rfl

/-- The explicit polynomial section in the actual left-cut balanced tensor. -/
def eiCSection : Polynomial Rl →ₗ[k] EIKZero Q i β a :=
  (eiCSectionUncut Q i γ a).codRestrict _ (eiCSectionUncut_mem Q i γ a)

/-- Canonical tensor multiplication and transport recover the ambient C-section. -/
theorem eiCSection_coordinates (p : Polynomial Rl) :
    eiZeroCoordinates Q i γ a (eiCSection Q i γ a p) =
      cSection i β a (zero_lt_card_single_add i γ) p := by
  change lowerQuotientCast Q i γ a (tensorToKZero Q i β a (by simp) (zero_lt_card_single_add i γ)
    (kZeroToTensor Q i β a (by simp) (zero_lt_card_single_add i γ) (lowerQuotientUncast Q i γ a _))) = _
  rw [tensorToKZero_kZeroToTensor, lowerQuotientCast_rightCut,
    lowerQuotientCast_uncast, cSection_rightCut]

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ j l, j ≠ l → Q j l = P l j * MvPolynomial.rename ![1, 0] (P j l))
  (hP : ∀ j l, j ≠ l → P j l ≠ 0)

@[simp] theorem eiB_eiBSection (p : Polynomial Rl) :
    eiB Q i γ a hPQ hP (eiBSection Q i γ a p) = p := by
  change bMap i β hPQ hP a (by simp) (zero_lt_card_single_add i γ)
    (tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ)
      (eiBSection Q i γ a p : KOneTensor Q i β a)) = _
  rw [eiBSection_coordinates, bMap_bSection]

@[simp] theorem eiC_eiCSection (p : Polynomial Rl) :
    eiC Q i γ a hPQ hP (eiCSection Q i γ a p) = p := by
  change cMap i β hPQ hP a (zero_lt_card_single_add i γ) (eiZeroCoordinates Q i γ a _) = _
  rw [eiCSection_coordinates, cMap_cSection]

theorem eiB_surjective : Function.Surjective (eiB Q i γ a hPQ hP) :=
  fun p => ⟨eiBSection Q i γ a p, eiB_eiBSection Q i γ a hPQ hP p⟩

theorem eiC_surjective : Function.Surjective (eiC Q i γ a hPQ hP) :=
  fun p => ⟨eiCSection Q i γ a p, eiC_eiCSection Q i γ a hPQ hP p⟩

/-- Remove the explicit polynomial summand, retaining an element of the actual kernel. -/
def eiBKernelPart : EIKOne Q i β a →ₗ[k] LinearMap.ker (eiB Q i γ a hPQ hP) :=
  (LinearMap.id - (eiBSection Q i γ a).comp (eiB Q i γ a hPQ hP)).codRestrict _ (by
    intro z
    change eiB Q i γ a hPQ hP (z - eiBSection Q i γ a (eiB Q i γ a hPQ hP z)) = 0
    rw [map_sub, eiB_eiBSection, sub_self])

/-- The lower tensor coordinate uses the previously constructed kernel inverse. -/
def eiBLowerProjection : EIKOne Q i β a →ₗ[k] KOnePrime Q i γ a :=
  (lowerVerticalKernelInv Q i γ a hPQ hP).comp (eiBKernelPart Q i γ a hPQ hP)

theorem lowerVertical_eiBLowerProjection (z : EIKOne Q i β a) :
    lowerVertical Q i γ a (eiBLowerProjection Q i γ a hPQ hP z) =
      z - eiBSection Q i γ a (eiB Q i γ a hPQ hP z) :=
  lowerVertical_kernelInv Q i γ a hPQ hP (eiBKernelPart Q i γ a hPQ hP z)

@[simp] theorem eiBLowerProjection_lowerVertical (t : KOnePrime Q i γ a) :
    eiBLowerProjection Q i γ a hPQ hP (lowerVertical Q i γ a t) = t := by
  have hk : eiBKernelPart Q i γ a hPQ hP (lowerVertical Q i γ a t) =
      ⟨lowerVertical Q i γ a t, eiB_lowerVertical Q i γ a hPQ hP t⟩ := by
    apply Subtype.ext
    change lowerVertical Q i γ a t - eiBSection Q i γ a (eiB Q i γ a hPQ hP _) = _
    rw [eiB_lowerVertical, map_zero, sub_zero]
  change lowerVerticalKernelInv Q i γ a hPQ hP (eiBKernelPart Q i γ a hPQ hP _) = _
  rw [hk, lowerVerticalKernelInv_forward]

@[simp] theorem eiBLowerProjection_section (p : Polynomial Rl) :
    eiBLowerProjection Q i γ a hPQ hP (eiBSection Q i γ a p) = 0 := by
  have hk : eiBKernelPart Q i γ a hPQ hP (eiBSection Q i γ a p) = 0 := by
    apply Subtype.ext
    change eiBSection Q i γ a p - eiBSection Q i γ a (eiB Q i γ a hPQ hP _) = 0
    rw [eiB_eiBSection, sub_self]
  change lowerVerticalKernelInv Q i γ a hPQ hP (eiBKernelPart Q i γ a hPQ hP _) = _
  rw [hk, map_zero]

/-- The actual cut tensor is the k-linear sum of its lower tensor and polynomial parts.
This does not assert a graded or bimodule splitting. -/
def eiBSplitEquiv : (KOnePrime Q i γ a × Polynomial Rl) ≃ₗ[k] EIKOne Q i β a where
  toFun x := lowerVertical Q i γ a x.1 + eiBSection Q i γ a x.2
  invFun z := (eiBLowerProjection Q i γ a hPQ hP z, eiB Q i γ a hPQ hP z)
  left_inv x := by
    apply Prod.ext
    · simp only [map_add, eiBLowerProjection_lowerVertical, eiBLowerProjection_section, add_zero]
    · simp only [map_add, eiB_lowerVertical, eiB_eiBSection, zero_add]
  right_inv z := by
    change lowerVertical Q i γ a (eiBLowerProjection Q i γ a hPQ hP z) +
      eiBSection Q i γ a (eiB Q i γ a hPQ hP z) = z
    rw [lowerVertical_eiBLowerProjection, sub_add_cancel]
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
  map_smul' c x := by simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, RingHom.id_apply]

@[simp] theorem eiBSplitEquiv_apply (t : KOnePrime Q i γ a) (p : Polynomial Rl) :
    eiBSplitEquiv Q i γ a hPQ hP (t, p) = lowerVertical Q i γ a t + eiBSection Q i γ a p := rfl

@[simp] theorem eiBSplitEquiv_symm_apply (z : EIKOne Q i β a) :
    (eiBSplitEquiv Q i γ a hPQ hP).symm z =
      (eiBLowerProjection Q i γ a hPQ hP z, eiB Q i γ a hPQ hP z) := rfl

theorem eiBSplitEquiv_lower (t : KOnePrime Q i γ a) :
    eiBSplitEquiv Q i γ a hPQ hP (t, 0) = lowerVertical Q i γ a t := by
  rw [eiBSplitEquiv_apply, map_zero, add_zero]

theorem eiBSplitEquiv_polynomial (p : Polynomial Rl) :
    eiBSplitEquiv Q i γ a hPQ hP (0, p) = eiBSection Q i γ a p := by
  rw [eiBSplitEquiv_apply, map_zero, zero_add]

theorem eiBSplitEquiv_projection (x : KOnePrime Q i γ a × Polynomial Rl) :
    eiB Q i γ a hPQ hP (eiBSplitEquiv Q i γ a hPQ hP x) = x.2 := by
  change eiB Q i γ a hPQ hP (lowerVertical Q i γ a x.1 + eiBSection Q i γ a x.2) = _
  rw [map_add, eiB_lowerVertical, eiB_eiBSection, zero_add]

/-- Remove the explicit polynomial summand, retaining an element of the actual kernel. -/
def eiCKernelPart : EIKZero Q i β a →ₗ[k] LinearMap.ker (eiC Q i γ a hPQ hP) :=
  (LinearMap.id - (eiCSection Q i γ a).comp (eiC Q i γ a hPQ hP)).codRestrict _ (by
    intro z
    change eiC Q i γ a hPQ hP (z - eiCSection Q i γ a (eiC Q i γ a hPQ hP z)) = 0
    rw [map_sub, eiC_eiCSection, sub_self])

/-- The lower tensor coordinate uses the previously constructed kernel inverse. -/
def eiCLowerProjection : EIKZero Q i β a →ₗ[k] KZeroPrime Q i γ a :=
  (lowerFKernelInv Q i γ a hPQ hP).comp (eiCKernelPart Q i γ a hPQ hP)

theorem lowerF_eiCLowerProjection (z : EIKZero Q i β a) :
    lowerF Q i γ a (eiCLowerProjection Q i γ a hPQ hP z) =
      z - eiCSection Q i γ a (eiC Q i γ a hPQ hP z) :=
  lowerF_kernelInv Q i γ a hPQ hP (eiCKernelPart Q i γ a hPQ hP z)

@[simp] theorem eiCLowerProjection_lowerF (t : KZeroPrime Q i γ a) :
    eiCLowerProjection Q i γ a hPQ hP (lowerF Q i γ a t) = t := by
  have hk : eiCKernelPart Q i γ a hPQ hP (lowerF Q i γ a t) =
      ⟨lowerF Q i γ a t, eiC_lowerF Q i γ a hPQ hP t⟩ := by
    apply Subtype.ext
    change lowerF Q i γ a t - eiCSection Q i γ a (eiC Q i γ a hPQ hP _) = _
    rw [eiC_lowerF, map_zero, sub_zero]
  change lowerFKernelInv Q i γ a hPQ hP (eiCKernelPart Q i γ a hPQ hP _) = _
  rw [hk, lowerFKernelInv_forward]

@[simp] theorem eiCLowerProjection_section (p : Polynomial Rl) :
    eiCLowerProjection Q i γ a hPQ hP (eiCSection Q i γ a p) = 0 := by
  have hk : eiCKernelPart Q i γ a hPQ hP (eiCSection Q i γ a p) = 0 := by
    apply Subtype.ext
    change eiCSection Q i γ a p - eiCSection Q i γ a (eiC Q i γ a hPQ hP _) = 0
    rw [eiC_eiCSection, sub_self]
  change lowerFKernelInv Q i γ a hPQ hP (eiCKernelPart Q i γ a hPQ hP _) = _
  rw [hk, map_zero]

/-- The actual cut tensor is the k-linear sum of its lower tensor and polynomial parts.
This does not assert a graded or bimodule splitting. -/
def eiCSplitEquiv : (KZeroPrime Q i γ a × Polynomial Rl) ≃ₗ[k] EIKZero Q i β a where
  toFun x := lowerF Q i γ a x.1 + eiCSection Q i γ a x.2
  invFun z := (eiCLowerProjection Q i γ a hPQ hP z, eiC Q i γ a hPQ hP z)
  left_inv x := by
    apply Prod.ext
    · simp only [map_add, eiCLowerProjection_lowerF, eiCLowerProjection_section, add_zero]
    · simp only [map_add, eiC_lowerF, eiC_eiCSection, zero_add]
  right_inv z := by
    change lowerF Q i γ a (eiCLowerProjection Q i γ a hPQ hP z) +
      eiCSection Q i γ a (eiC Q i γ a hPQ hP z) = z
    rw [lowerF_eiCLowerProjection, sub_add_cancel]
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
  map_smul' c x := by simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, RingHom.id_apply]

@[simp] theorem eiCSplitEquiv_apply (t : KZeroPrime Q i γ a) (p : Polynomial Rl) :
    eiCSplitEquiv Q i γ a hPQ hP (t, p) = lowerF Q i γ a t + eiCSection Q i γ a p := rfl

@[simp] theorem eiCSplitEquiv_symm_apply (z : EIKZero Q i β a) :
    (eiCSplitEquiv Q i γ a hPQ hP).symm z =
      (eiCLowerProjection Q i γ a hPQ hP z, eiC Q i γ a hPQ hP z) := rfl

theorem eiCSplitEquiv_lower (t : KZeroPrime Q i γ a) :
    eiCSplitEquiv Q i γ a hPQ hP (t, 0) = lowerF Q i γ a t := by
  rw [eiCSplitEquiv_apply, map_zero, add_zero]

theorem eiCSplitEquiv_polynomial (p : Polynomial Rl) :
    eiCSplitEquiv Q i γ a hPQ hP (0, p) = eiCSection Q i γ a p := by
  rw [eiCSplitEquiv_apply, map_zero, zero_add]

theorem eiCSplitEquiv_projection (x : KZeroPrime Q i γ a × Polynomial Rl) :
    eiC Q i γ a hPQ hP (eiCSplitEquiv Q i γ a hPQ hP x) = x.2 := by
  change eiC Q i γ a hPQ hP (lowerF Q i γ a x.1 + eiCSection Q i γ a x.2) = _
  rw [map_add, eiC_lowerF, eiC_eiCSection, zero_add]

/-- The explicit lower/polynomial decoder followed by reconstruction is the identity. -/
theorem eiBSplitEquiv_forward_inverse (z : EIKOne Q i β a) :
    eiBSplitEquiv Q i γ a hPQ hP
      (eiBLowerProjection Q i γ a hPQ hP z, eiB Q i γ a hPQ hP z) = z :=
  (eiBSplitEquiv Q i γ a hPQ hP).apply_symm_apply z

/-- Reconstruction followed by the explicit lower/polynomial decoder is the identity. -/
theorem eiBSplitEquiv_inverse_forward (x : KOnePrime Q i γ a × Polynomial Rl) :
    (eiBLowerProjection Q i γ a hPQ hP (lowerVertical Q i γ a x.1 + eiBSection Q i γ a x.2),
      eiB Q i γ a hPQ hP (lowerVertical Q i γ a x.1 + eiBSection Q i γ a x.2)) = x :=
  (eiBSplitEquiv Q i γ a hPQ hP).symm_apply_apply x

/-- The explicit lower/polynomial decoder followed by reconstruction is the identity. -/
theorem eiCSplitEquiv_forward_inverse (z : EIKZero Q i β a) :
    eiCSplitEquiv Q i γ a hPQ hP
      (eiCLowerProjection Q i γ a hPQ hP z, eiC Q i γ a hPQ hP z) = z :=
  (eiCSplitEquiv Q i γ a hPQ hP).apply_symm_apply z

/-- Reconstruction followed by the explicit lower/polynomial decoder is the identity. -/
theorem eiCSplitEquiv_inverse_forward (x : KZeroPrime Q i γ a × Polynomial Rl) :
    (eiCLowerProjection Q i γ a hPQ hP (lowerF Q i γ a x.1 + eiCSection Q i γ a x.2),
      eiC Q i γ a hPQ hP (lowerF Q i γ a x.1 + eiCSection Q i γ a x.2)) = x :=
  (eiCSplitEquiv Q i γ a hPQ hP).symm_apply_apply x

end Categorification.KLR.KLRAlgebra
