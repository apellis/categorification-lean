/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicRowCokernels
import Categorification.KLR.CyclotomicDegree
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The nonnegative cyclotomic commutator

For a present-colour block `β = {i} + γ` and nonnegative weight `h`, the actual
signed crossing and the canonical last-dot/unit inclusions give a k-linear
isomorphism from the lower cyclotomic tensor plus `h` copies of `R^Λ(β)` onto
the middle cyclotomic corner. The finite polynomial model and its coefficient
model are explicitly equivalent. Both inverse roundtrips and a remainder
formula on arbitrary middle representatives are proved.

The polynomial matrix entry remains `eiA = (-1)^|β| • aMap`. Its existing
triangularity and remainder theorems supply the complement; no splitting or
exactness hypothesis is introduced. The hypotheses are `KLRSymm Q` over a
commutative ring `k`, unit constant leading coefficients of the `Q_{jl}`, monic
`a_j` and the Cartan-degree condition. Neither
`γ = 0` nor a zero cyclotomic quotient is excluded. Only k-linearity is asserted;
there is no graded, bimodule, functorial, negative-weight or absent-colour claim.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open Polynomial
open scoped TensorProduct
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β" => (Si + γ)
variable (a : I → Polynomial k)
local notation "Rl" => CycKLR k Q a β

/-- The canonical polynomial dot-unit inclusion in the cyclotomic corner. -/
def cyclotomicDotUnit : Polynomial Rl →ₗ[k] MiddleCyclotomic Q i γ a :=
  (middleCyclotomicProj Q i γ a).comp (eiCSection Q i γ a)

/-- A finite coefficient-polynomial model for the correction summands. -/
abbrev CyclotomicCorrection (h : ℕ) := Polynomial.degreeLT Rl h

/-- The prescribed crossing together with the canonical finite polynomial inclusion. -/
def cyclotomicCommutator (h : ℕ) :
    (LowerCyclotomic Q i γ a × CyclotomicCorrection Q i γ a h) →ₗ[k]
      MiddleCyclotomic Q i γ a :=
  (cyclotomicSigma Q i γ a).comp (LinearMap.fst k _ _) +
    (cyclotomicDotUnit Q i γ a).comp
      (((Polynomial.degreeLT Rl h).subtype.restrictScalars k).comp (LinearMap.snd k _ _))

theorem cyclotomicCommutator_apply (h : ℕ) (l : LowerCyclotomic Q i γ a)
    (r : CyclotomicCorrection Q i γ a h) :
    cyclotomicCommutator Q i γ a h (l, r) =
      cyclotomicSigma Q i γ a l + cyclotomicDotUnit Q i γ a r := rfl

/-- The finite polynomial model is exactly the finite family of coefficients. -/
def cyclotomicCorrectionEquiv (h : ℕ) :
    CyclotomicCorrection Q i γ a h ≃ₗ[k] (Fin h → Rl) :=
  (Polynomial.degreeLTEquiv Rl h).restrictScalars k

theorem cyclotomicCorrectionEquiv_symm (h : ℕ) (v : Fin h → Rl) :
    ((cyclotomicCorrectionEquiv Q i γ a h).symm v : Polynomial Rl) =
      ∑ d : Fin h, Polynomial.monomial d (v d) := rfl

/-- The polynomial inclusion is the actual concatenation of quotient coefficients. -/
theorem cyclotomicDotUnit_thetaL0
    (t : KLRAlgebra k Q β ⊗[k] KLRAlgebra k Q Si) :
    (cyclotomicDotUnit Q i γ a (thetaL0 Q i β a t) : CycKLR k Q a (Si + β)) =
      CycKLR.mk k Q a (Si + β) (cLL Q i β t) := by
  change middleQuotient Q i γ a (eiZeroCoordinates Q i γ a (eiCSection Q i γ a _)) = _
  rw [eiCSection_coordinates, cSection_thetaL0, middleQuotient_mk]

/-- Each finite summand is a power of the last dot applied to the canonical unit. -/
theorem cyclotomicDotUnit_monomial (b : KLRAlgebra k Q β) (d : ℕ) :
    (cyclotomicDotUnit Q i γ a (Polynomial.monomial d (CycKLR.mk k Q a β b)) :
        CycKLR k Q a (Si + β)) =
      CycKLR.mk k Q a (Si + β)
        (cL Q i β b * (x ⟨Multiset.card β, lastPos_lt i β⟩) ^ d * cL Q i β 1) := by
  let xd : KLRAlgebra k Q Si := (x ⟨0, by rw [card_single']; omega⟩) ^ d
  have ht : thetaL0 Q i β a (b ⊗ₜ xd) = Polynomial.monomial d (CycKLR.mk k Q a β b) := by
    rw [thetaL0_apply, Algebra.TensorProduct.comm_tmul, thetaL, AlgHom.comp_apply,
      theta_tmul]
    simp only [xd, map_pow, singlePoly_x, Polynomial.aeval_X,
      Polynomial.coe_mapAlgHom, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    rw [(Polynomial.commute_X_pow _ _).eq, Polynomial.C_mul_X_pow_eq_monomial]
    rfl
  rw [← ht, cyclotomicDotUnit_thetaL0, cLL_tmul, cLL_one_tmul]
  simp only [xd, map_pow, singlePoly_x, Polynomial.aeval_X, mul_assoc]

variable (hsym : KLRSymm Q)
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) =
    -RD.pair (RD.iY i) (RD.iX j))
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX β))
local notation "Amap" => aMap i β a (by simp) (zero_lt_card_single_add i γ) hsym
local notation "sgn" => ((-1 : k) ^ Multiset.card β)

private theorem neg_one_pow_mul_self (n : ℕ) : ((-1 : k) ^ n) * (-1) ^ n = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

include hsym hQ ha hΛ hdeg in
theorem eiA_injective_of_pair_nonneg (hwt : 0 ≤ wt) :
    Function.Injective (eiA Q i γ a hsym) := by
  intro p q hpq
  have he : Amap p = Amap q := by
    have := congrArg (fun z : Polynomial Rl => sgn • z) hpq
    simpa only [eiA, LinearMap.smul_apply, smul_smul, neg_one_pow_mul_self, one_smul] using this
  exact aMap_injective_of_pair_nonneg i β a RD Λ hsym
    (zero_lt_card_single_add i γ) hQ ha (by simp) hΛ hdeg hwt he

include hsym hQ ha hΛ hdeg in
theorem eiA_exists_small_remainder (hwt : 0 ≤ wt) (q : Polynomial Rl) :
    ∃ p, (q - eiA Q i γ a hsym p).degree < (wt).toNat := by
  rcases subsingleton_or_nontrivial Rl with h | h
  · exact ⟨0, by rw [Subsingleton.elim q 0, map_zero, sub_self, degree_zero]; exact WithBot.bot_lt_coe _⟩
  · obtain ⟨p, hp⟩ := aMap_exists_remainder i β a hsym
      (zero_lt_card_single_add i γ) hQ ha (by simp) q
    have hd := aMonicL_degree_gap i β a RD Λ hsym hQ (ha i) hΛ hdeg
    have he : (aMonicL Q i β a).natDegree - (sPoly (Q := Q) i β a).natDegree = (wt).toNat := by omega
    refine ⟨sgn • p, ?_⟩
    simpa only [eiA, LinearMap.smul_apply, map_smul, smul_smul, neg_one_pow_mul_self, one_smul, he] using hp

include hsym hQ ha hΛ hdeg in
theorem eiA_eq_small (hwt : 0 ≤ wt) (p r : Polynomial Rl)
    (hr : r.degree < (wt).toNat) (he : eiA Q i γ a hsym p = r) : p = 0 ∧ r = 0 := by
  rcases subsingleton_or_nontrivial Rl with h | h
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · obtain ⟨c, hc⟩ := isUnit_lamA (Q := Q) i β hQ
    obtain ⟨hlow, hhigh⟩ := aMap_phi_spec i β a hsym
      (zero_lt_card_single_add i γ) hQ ha (by simp)
    rw [← hc, Ring.inverse_unit] at hhigh
    have hd := aMonicL_degree_gap i β a RD Λ hsym hQ (ha i) hΛ hdeg
    have he0 : (sPoly (Q := Q) i β a).natDegree - (aMonicL Q i β a).natDegree = 0 := by omega
    have heh : (aMonicL Q i β a).natDegree - (sPoly (Q := Q) i β a).natDegree = (wt).toNat := by omega
    let A0 : Polynomial Rl →ₗ[k] Polynomial Rl := Amap
    have hC : ∀ p (r : Rl), A0.toAddMonoidHom (p * Polynomial.C r) =
        A0.toAddMonoidHom p * Polynomial.C r :=
      aMap_mul_C i β a (by simp) (zero_lt_card_single_add i γ) hsym
    have hz := PhiAlg.degree_lt_of_apply_add_eq_zero A0.toAddMonoidHom c
      ((sPoly (Q := Q) i β a).natDegree - (aMonicL Q i β a).natDegree)
      ((aMonicL Q i β a).natDegree - (sPoly (Q := Q) i β a).natDegree) hC hlow hhigh
      (p := sgn • p) (r := -r) (by simpa only [degree_neg, heh] using hr)
      (by change Amap (sgn • p) + -r = 0; rw [map_smul]; exact sub_eq_zero.mpr he)
    rw [he0, Nat.cast_zero] at hz
    have hz' : sgn • p = 0 := by simpa only [Polynomial.zero_le_degree_iff, not_not] using (not_le.mpr hz)
    have hp : p = 0 := by
      have := congrArg (fun z : Polynomial Rl => sgn • z) hz'
      simpa only [smul_smul, neg_one_pow_mul_self, one_smul, smul_zero] using this
    exact ⟨hp, by rw [hp, map_zero] at he; exact he.symm⟩

include hsym hQ ha hΛ hdeg in
theorem cyclotomicSigma_injective_of_pair_nonneg (hwt : 0 ≤ wt) :
    Function.Injective (cyclotomicSigma Q i γ a) := by
  have hA := eiA_injective_of_pair_nonneg Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt
  have hF : Function.Injective (lowerFCoker Q i γ a) := by
    apply LinearMap.ker_eq_bot.mp
    rw [← range_snakeDelta Q i γ a hsym]
    apply le_antisymm _ bot_le
    rintro z ⟨p, rfl⟩
    have hp : p = 0 := Subtype.ext (hA (by
      change eiA Q i γ a hsym p.val = eiA Q i γ a hsym 0
      rw [map_zero]; exact p.2))
    rw [hp, map_zero]
    exact Submodule.zero_mem _
  intro l m he
  apply (lowerPCokerEquiv Q i γ a).symm.injective
  apply hF
  apply (eiPCokerEquiv Q i γ a).injective
  exact he

/-- On actual lower representatives the prescribed map is the middle projection. -/
theorem cyclotomicCommutator_representative (h : ℕ) (u : KZeroPrime Q i γ a)
    (r : CyclotomicCorrection Q i γ a h) :
    cyclotomicCommutator Q i γ a h
      (lowerPCokerEquiv Q i γ a (Submodule.Quotient.mk u), r) =
      middleCyclotomicProj Q i γ a (lowerF Q i γ a u + eiCSection Q i γ a r) := by
  rw [cyclotomicCommutator_apply, cyclotomicSigma_lowerPCoker, lowerFCoker_mk, eiPCokerEquiv_mk, map_add]
  rfl

include hsym hQ ha hΛ hdeg in
theorem cyclotomicCommutator_injective (hwt : 0 ≤ wt) :
    Function.Injective (cyclotomicCommutator Q i γ a (wt).toNat) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  rintro ⟨l, r⟩ hz
  obtain ⟨v, rfl⟩ := (lowerPCokerEquiv Q i γ a).surjective l
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have he : middleCyclotomicProj Q i γ a
      (lowerF Q i γ a u + eiCSection Q i γ a r) = 0 := by
    rwa [← cyclotomicCommutator_representative Q i γ a]
  have hm : lowerF Q i γ a u + eiCSection Q i γ a r ∈ LinearMap.range (eiP Q i γ a) := by
    rw [← ker_middleCyclotomicProj]; exact he
  obtain ⟨z, hz⟩ := hm
  have hc := congrArg (eiC Q i γ a hsym) hz
  rw [eiC_eiP, map_add, eiC_lowerF, eiC_eiCSection, zero_add] at hc
  obtain ⟨_, hr⟩ := eiA_eq_small Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt
    (eiB Q i γ a hsym z) r (Polynomial.mem_degreeLT.mp r.2) hc
  have hr' : r = 0 := Subtype.ext hr
  subst r
  have hl : lowerPCokerEquiv Q i γ a (Submodule.Quotient.mk u) = 0 := by
    apply cyclotomicSigma_injective_of_pair_nonneg Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt
    rw [map_zero, cyclotomicSigma_lowerPCoker, lowerFCoker_mk, eiPCokerEquiv_mk]
    simpa only [ZeroMemClass.coe_zero, map_zero, add_zero] using he
  exact Prod.ext hl rfl

include hsym hQ ha hΛ hdeg in
theorem cyclotomicCommutator_surjective (hwt : 0 ≤ wt) :
    Function.Surjective (cyclotomicCommutator Q i γ a (wt).toNat) := by
  intro m
  obtain ⟨z, rfl⟩ := middleCyclotomicProj_surjective Q i γ a m
  let q := eiC Q i γ a hsym z
  obtain ⟨p, hp⟩ := eiA_exists_small_remainder Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt q
  let u := eiCLowerProjection Q i γ a hsym z - eiPOffDiagonal Q i γ a hsym p
  let r : CyclotomicCorrection Q i γ a (wt).toNat := ⟨q - eiA Q i γ a hsym p, mem_degreeLT.mpr hp⟩
  refine ⟨(lowerPCokerEquiv Q i γ a (Submodule.Quotient.mk u), r), ?_⟩
  rw [cyclotomicCommutator_representative]
  have he : lowerF Q i γ a u + eiCSection Q i γ a r =
      z - eiP Q i γ a (eiBSection Q i γ a p) := by
    change lowerF Q i γ a (eiCLowerProjection Q i γ a hsym z - eiPOffDiagonal Q i γ a hsym p) +
      eiCSection Q i γ a (q - eiA Q i γ a hsym p) = _
    rw [map_sub, lowerF_eiCLowerProjection, lowerF_eiPOffDiagonal, map_sub]
    dsimp only [q]
    abel
  rw [he, map_sub, middleCyclotomicProj_eiP, sub_zero]

/-- The actual nonnegative-weight k-linear commutator decomposition. -/
def cyclotomicCommutatorEquiv (hwt : 0 ≤ wt) :
    (LowerCyclotomic Q i γ a × CyclotomicCorrection Q i γ a (wt).toNat) ≃ₗ[k]
      MiddleCyclotomic Q i γ a :=
  LinearEquiv.ofBijective (cyclotomicCommutator Q i γ a (wt).toNat)
    ⟨cyclotomicCommutator_injective Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt,
      cyclotomicCommutator_surjective Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt⟩

theorem cyclotomicCommutatorEquiv_apply (hwt : 0 ≤ wt)
    (l : LowerCyclotomic Q i γ a) (r : CyclotomicCorrection Q i γ a (wt).toNat) :
    cyclotomicCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt (l, r) =
      cyclotomicSigma Q i γ a l + cyclotomicDotUnit Q i γ a r := rfl

theorem cyclotomicCommutator_inverse_forward (hwt : 0 ≤ wt)
    (z : LowerCyclotomic Q i γ a × CyclotomicCorrection Q i γ a (wt).toNat) :
    (cyclotomicCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm
      (cyclotomicCommutator Q i γ a (wt).toNat z) = z :=
  (cyclotomicCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm_apply_apply z

theorem cyclotomicCommutator_forward_inverse (hwt : 0 ≤ wt) (z : MiddleCyclotomic Q i γ a) :
    cyclotomicCommutator Q i γ a (wt).toNat
      ((cyclotomicCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm z) = z :=
  (cyclotomicCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).apply_symm_apply z

/-- The inverse on any actual representative with a low-degree polynomial part. -/
theorem cyclotomicCommutator_inverse_representative (hwt : 0 ≤ wt)
    (u : KZeroPrime Q i γ a) (r : CyclotomicCorrection Q i γ a (wt).toNat) :
    (cyclotomicCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm
      (middleCyclotomicProj Q i γ a (lowerF Q i γ a u + eiCSection Q i γ a r)) =
      (lowerPCokerEquiv Q i γ a (Submodule.Quotient.mk u), r) := by
  rw [← cyclotomicCommutator_representative, cyclotomicCommutator_inverse_forward]

include hsym hQ ha hΛ hdeg in
theorem cyclotomicSigma_bijective_of_pair_zero (hwt : wt = 0) :
    Function.Bijective (cyclotomicSigma Q i γ a) := by
  have hnonneg : 0 ≤ wt := by omega
  refine ⟨cyclotomicSigma_injective_of_pair_nonneg Q i γ a hsym hQ ha RD Λ hΛ hdeg hnonneg, ?_⟩
  intro z
  obtain ⟨⟨l, r⟩, hr⟩ := cyclotomicCommutator_surjective Q i γ a hsym hQ ha RD Λ hΛ hdeg hnonneg z
  have hp := mem_degreeLT.mp r.2
  have hp0 : (r : Polynomial Rl).degree < (0 : WithBot ℕ) := by
    simpa only [hwt, Int.toNat_zero, Nat.cast_zero] using hp
  have hz : (r : Polynomial Rl) = 0 := by
    simpa only [Polynomial.zero_le_degree_iff, not_not] using (not_le.mpr hp0)
  refine ⟨l, ?_⟩
  rwa [cyclotomicCommutator_apply, hz, map_zero, add_zero] at hr

/-- At weight zero the actual signed crossing is itself a linear equivalence. -/
def cyclotomicSigmaEquivOfPairZero (hwt : wt = 0) :
    LowerCyclotomic Q i γ a ≃ₗ[k] MiddleCyclotomic Q i γ a :=
  LinearEquiv.ofBijective (cyclotomicSigma Q i γ a)
    (cyclotomicSigma_bijective_of_pair_zero Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt)

/-- Finite coefficient families, with exactly the prescribed forward map. -/
def cyclotomicCommutatorFinEquiv (hwt : 0 ≤ wt) :
    (LowerCyclotomic Q i γ a × (Fin (wt).toNat → Rl)) ≃ₗ[k] MiddleCyclotomic Q i γ a :=
  ((LinearEquiv.refl k (LowerCyclotomic Q i γ a)).prodCongr
    (cyclotomicCorrectionEquiv Q i γ a (wt).toNat).symm).trans
      (cyclotomicCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt)

theorem cyclotomicCommutatorFinEquiv_apply (hwt : 0 ≤ wt)
    (l : LowerCyclotomic Q i γ a) (v : Fin (wt).toNat → Rl) :
    cyclotomicCommutatorFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt (l, v) =
      cyclotomicSigma Q i γ a l +
        ∑ d : Fin (wt).toNat, cyclotomicDotUnit Q i γ a (Polynomial.monomial d (v d)) := by
  change cyclotomicSigma Q i γ a l + cyclotomicDotUnit Q i γ a
    ((cyclotomicCorrectionEquiv Q i γ a (wt).toNat).symm v : Polynomial Rl) = _
  rw [cyclotomicCorrectionEquiv_symm, map_sum]

theorem cyclotomicCommutatorFin_inverse_forward (hwt : 0 ≤ wt)
    (z : LowerCyclotomic Q i γ a × (Fin (wt).toNat → Rl)) :
    (cyclotomicCommutatorFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm
      (cyclotomicCommutatorFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt z) = z :=
  (cyclotomicCommutatorFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm_apply_apply z

theorem cyclotomicCommutatorFin_forward_inverse (hwt : 0 ≤ wt) (z : MiddleCyclotomic Q i γ a) :
    cyclotomicCommutatorFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt
      ((cyclotomicCommutatorFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm z) = z :=
  (cyclotomicCommutatorFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).apply_symm_apply z

/-- Any polynomial remainder computes the same inverse of an actual middle representative. -/
theorem cyclotomicCommutator_inverse_remainder (hwt : 0 ≤ wt)
    (z : EIKZero Q i β a) (p : Polynomial Rl)
    (hp : (eiC Q i γ a hsym z - eiA Q i γ a hsym p).degree < (wt).toNat) :
    (cyclotomicCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm
      (middleCyclotomicProj Q i γ a z) =
      (lowerPCokerEquiv Q i γ a (Submodule.Quotient.mk
        (eiCLowerProjection Q i γ a hsym z - eiPOffDiagonal Q i γ a hsym p)),
       ⟨eiC Q i γ a hsym z - eiA Q i γ a hsym p, mem_degreeLT.mpr hp⟩) := by
  apply (cyclotomicCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).injective
  rw [LinearEquiv.apply_symm_apply]
  change middleCyclotomicProj Q i γ a z = cyclotomicCommutator Q i γ a (wt).toNat _
  rw [cyclotomicCommutator_representative]
  have he : lowerF Q i γ a
      (eiCLowerProjection Q i γ a hsym z - eiPOffDiagonal Q i γ a hsym p) +
      eiCSection Q i γ a (eiC Q i γ a hsym z - eiA Q i γ a hsym p) =
      z - eiP Q i γ a (eiBSection Q i γ a p) := by
    rw [map_sub, lowerF_eiCLowerProjection, lowerF_eiPOffDiagonal, map_sub]
    abel
  change middleCyclotomicProj Q i γ a z = middleCyclotomicProj Q i γ a
    (lowerF Q i γ a _ + eiCSection Q i γ a (eiC Q i γ a hsym z - eiA Q i γ a hsym p))
  rw [he, map_sub, middleCyclotomicProj_eiP, sub_zero]

theorem cyclotomicSigmaEquivOfPairZero_apply (hwt : wt = 0) (z : LowerCyclotomic Q i γ a) :
    cyclotomicSigmaEquivOfPairZero Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt z =
      cyclotomicSigma Q i γ a z := rfl

theorem cyclotomicSigma_zero_inverse_forward (hwt : wt = 0) (z : LowerCyclotomic Q i γ a) :
    (cyclotomicSigmaEquivOfPairZero Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm
      (cyclotomicSigma Q i γ a z) = z :=
  (cyclotomicSigmaEquivOfPairZero Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm_apply_apply z

theorem cyclotomicSigma_zero_forward_inverse (hwt : wt = 0) (z : MiddleCyclotomic Q i γ a) :
    cyclotomicSigma Q i γ a
      ((cyclotomicSigmaEquivOfPairZero Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm z) = z :=
  (cyclotomicSigmaEquivOfPairZero Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).apply_symm_apply z

end Categorification.KLR.KLRAlgebra
