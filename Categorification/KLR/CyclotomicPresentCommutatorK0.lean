/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicCommutatorGrading
import Categorification.KLR.CyclotomicAbsentCommutatorK0
/-!
# The graded cyclotomic commutator at a present colour

Kang–Kashiwara, arXiv:1102.4677v4, Theorem 5.2. For both signs of the
coroot pairing, the actual cyclotomic crossing, dotted units and dotted
counits identify EF and shifted FE with the indicated identity summands.
The corresponding Laurent-polynomial identities hold on all projective classes.
-/

noncomputable section
namespace Categorification.KLR.CycKLR
open KLRAlgebra KLRAlgebra.AbsentColour KLRAlgebra.AbsentColour.InductionCalculus
open Categorification.Graded QuantumGroup QuantumGroup.UDot
variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (i : I) (β : Multiset I)
    (hsym : KLRSymm Q)
    (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)
    {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (highest : X) (hΛ : (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
local notation "aΛ" => (fun j => (Polynomial.X : Polynomial k) ^ Λ j)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β₁" => (Si + β)
local notation "U" => (Si + β₁)
local notation "Rl" => CycKLR k Q aΛ β
local notation "Su" => CycKLR k Q aΛ β₁
local notation "Tu" => CycKLR k Q aΛ U
local notation "wt" => RD.pair (RD.iY i) (highest - Multiset.sum (Multiset.map RD.iX β₁))
local notation "cor" => Graded.submodule (grade G Λ β₁) (lIdeal (lastIdem Q i aΛ β))
local notation "upCor" => Graded.submodule (grade G Λ U) (lIdeal (lastIdem Q i aΛ β₁))
variable (P : GProj (grade G Λ ((Singleton.singleton i : Multiset I) + β)))
local notation "FE" => PresentColour.FE Q i β aΛ P.carrier
local notation "EF" => AbsentColour.EF Q i aΛ β₁ P.carrier
local notation "resGr" => (Graded.idem P.grading (lastIdem Q i aΛ β) :
  ℤ → Submodule k (AbsentColour.Res Q i aΛ β P.carrier))
local notation "feGr" => balancedGrading (N := AbsentColour.Res Q i aΛ β P.carrier) Su Rl cor resGr
local notation "efGr" => Graded.idem (balancedGrading Tu Su upCor P.grading) (lastIdem Q i aΛ β₁)
local notation "mid" => PresentColour.efMiddleEquiv Q i β aΛ P.carrier

private def presentCrossMap : FE →ₗ[Su] EF :=
  (mid).symm.toLinearMap ∘ₗ BalancedTensor.mapLeft (sigmaOuter Q i aΛ β)
    (cyclotomicSigma_op_smul Q i β aΛ) ∘ₗ PresentColour.feToLower Q i β aΛ P.carrier

private theorem crossMap_grade {d : ℤ} {z : FE} (hz : z ∈ feGr d) :
    presentCrossMap G Λ i β P z ∈ efGr (d - G.degX i) := by
  apply balancedGrading_map_mem (N := AbsentColour.Res Q i aΛ β P.carrier) (ℳ := cor) (𝒩 := resGr) (Graded.shift efGr (G.degX i))
    ((presentCrossMap G Λ i β P).restrictScalars k) _ hz
  intro j l x y hx hy
  let c := cyclotomicSigma Q i β aΛ (PresentColour.insertIdem Q i β aΛ x)
  change BalancedTensor.tmul (cornerToInd Q i aΛ β₁ c) y.1 ∈
    balancedGrading Tu Su upCor P.grading (j + l - G.degX i)
  have hc : cornerToInd Q i aΛ β₁ c ∈ upCor (j - G.degX i) := sigma_insert_mem_grade G Λ i β hx
  have h := tmul_mem_balancedGrading (B := Tu) (A := Su) hc (show y.1 ∈ P.grading l from hy)
  rwa [show j - G.degX i + l = j + l - G.degX i by abel] at h

private theorem midDot_grade (r : ℕ) {l : ℤ} {y : P.carrier} (hy : y ∈ P.grading l) :
    (mid).symm (BalancedTensor.tmul (cyclotomicDotUnit Q i β aΛ (Polynomial.monomial r 1)) y) ∈
      efGr (r • G.degX i + l) := by
  let c := cyclotomicDotUnit Q i β aΛ (Polynomial.monomial r 1)
  change BalancedTensor.tmul (cornerToInd Q i aΛ β₁ c) y ∈ balancedGrading Tu Su upCor P.grading _
  have hc : cornerToInd Q i aΛ β₁ c ∈ upCor (r • G.degX i) := by
    change (cyclotomicDotUnit Q i β aΛ (Polynomial.monomial r 1) : Tu) ∈ grade G Λ U _
    rw [cyclotomicDotUnit_monomial_canonical, map_pow]
    have h := dotUnitTerm_mem_grade G Λ i β₁ r (x := 1) SetLike.GradedOne.one_mem
    rw [zero_add] at h
    exact h
  exact tmul_mem_balancedGrading hc hy

omit [DecidableEq I] in
private theorem natDegree_highest {Λ : I → ℕ} {i : I} {z : ℤ} (h : (Λ i : ℤ) = z) :
    (((Polynomial.X : Polynomial k) ^ Λ i).natDegree : ℤ) = z := by simpa using h

local notation "Pos" => PresentColour.positiveEquiv Q i β aΛ P.carrier hsym hQ
  (fun _ => Polynomial.monic_X_pow _) RD highest (natDegree_highest hΛ) hdeg
local notation "Neg" => PresentColour.negativeEquiv Q i β aΛ P.carrier hsym hQ
  (fun _ => Polynomial.monic_X_pow _) RD highest (natDegree_highest hΛ) hdeg

private theorem pos_crossing (hp : 0 ≤ wt) (z : FE) : Pos hp (z, 0) = presentCrossMap G Λ i β P z := by
  let f := (Pos hp).toLinearMap.comp (LinearMap.inl Su FE (Fin (wt).toNat → P.carrier))
  let e := PresentColour.indResEquiv Q i β aΛ P.carrier
  have H : f.comp e.symm.toLinearMap = (presentCrossMap G Λ i β P).comp e.symm.toLinearMap := by
    apply BalancedTensor.extB
    intro t y
    change Pos hp (PresentColour.lowerToFE Q i β aΛ P.carrier (BalancedTensor.tmul t y), 0) = _
    rw [PresentColour.positiveEquiv_crossing]
    change _ = (mid).symm (BalancedTensor.mapLeft (sigmaOuter Q i aΛ β) (cyclotomicSigma_op_smul Q i β aΛ)
      (PresentColour.feToLower Q i β aΛ P.carrier (PresentColour.lowerToFE Q i β aΛ P.carrier _)))
    rw [PresentColour.feToLower_lowerToFE]
    rfl
  have Hz := LinearMap.congr_fun H (e z)
  change f z = _
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using Hz

private theorem pos_dots_grade (hp : 0 ≤ wt) (d : ℤ) (v : Fin (wt).toNat → P.carrier)
    (hv : ∀ r : Fin (wt).toNat, v r ∈ P.grading (d - (r : ℕ) • G.degX i)) :
    Pos hp (0, v) ∈ efGr d := by
  rw [PresentColour.positiveEquiv_dots, map_sum]
  apply Submodule.sum_mem
  intro r _
  rw [PresentColour.positiveEquiv_dot_coefficient]
  have h := midDot_grade G Λ i β P r (hv r)
  rwa [show (r : ℕ) • G.degX i + (d - (r : ℕ) • G.degX i) = d by abel] at h

private theorem pos_preserves (hp : 0 ≤ wt) (d : ℤ) (z : FE × (Fin (wt).toNat → P.carrier))
    (hz : z.1 ∈ feGr (d - (-G.degX i)) ∧ ∀ r : Fin (wt).toNat, z.2 r ∈ P.grading (d - (r : ℕ) • G.degX i)) :
    Pos hp z ∈ efGr d := by
  have he : z = (z.1, 0) + (0, z.2) := Prod.ext (add_zero _).symm (zero_add _).symm
  rw [he, map_add, pos_crossing G Λ i β hsym hQ RD highest hΛ hdeg P hp]
  apply Submodule.add_mem
  · have h := crossMap_grade G Λ i β P hz.1
    rw [sub_neg_eq_add, add_sub_cancel_right] at h
    exact h
  · exact pos_dots_grade G Λ i β hsym hQ RD highest hΛ hdeg P hp d z.2 hz.2

local notation "FeP" => gradedIndProj G Λ i β (gradedResProj G Λ i β hsym hQ P)
local notation "EfP" => gradedResProj G Λ i β₁ hsym hQ (gradedIndProj G Λ i β₁ P)

/-- The nonnegative-weight case of Kang–Kashiwara, Theorem 5.2(a), on graded projectives. -/
def positiveCommutatorIso (hp : 0 ≤ wt) :
    (((FeP).shift (-G.degX i)).prod (GProj.pi fun r : Fin (wt).toNat => P.shift ((r : ℕ) • G.degX i))).Iso EfP :=
  GradedEquiv.ofPreserves (Pos hp) (pos_preserves G Λ i β hsym hQ RD highest hΛ hdeg P hp)

local notation "negGr" => Graded.prod efGr (piGrading fun r : Fin (-wt).toNat =>
  Graded.shift P.grading (-(((r : ℕ) + 1) • G.degX i)))

private theorem neg_preserves (hn : wt ≤ 0) {d : ℤ} {z : FE} (hz : z ∈ feGr d) :
    Neg hn z ∈ negGr (d - G.degX i) := by
  apply balancedGrading_map_mem (N := AbsentColour.Res Q i aΛ β P.carrier) (ℳ := cor) (𝒩 := resGr) (Graded.shift negGr (G.degX i))
    ((Neg hn).toLinearMap.restrictScalars k) _ hz
  intro j l x y hx hy
  have he := PresentColour.negativeEquiv_tmul Q i β aΛ P.carrier hsym hQ
    (fun _ => Polynomial.monic_X_pow _) RD highest (natDegree_highest hΛ) hdeg hn
    (PresentColour.insertIdem Q i β aΛ x) y.1
  rw [← PresentColour.feToLower_tmul, PresentColour.lowerToFE_feToLower] at he
  change Neg hn (BalancedTensor.tmul x y) ∈ negGr (j + l - G.degX i)
  rw [he]
  constructor
  · have h := crossMap_grade G Λ i β P
      (tmul_mem_balancedGrading (N := AbsentColour.Res Q i aΛ β P.carrier) (B := Su) (A := Rl) (ℳ := cor)
        (𝒩 := resGr) hx hy)
    exact h
  · intro r
    have h := SetLike.GradedSMul.smul_mem (A := grade G Λ β₁) (B := P.grading)
      (counit_insert_mem_grade G Λ i β hx (r : ℕ)) (show y.1 ∈ P.grading l from hy)
    change _ ∈ P.grading (j + l - G.degX i - -(((r : ℕ) + 1) • G.degX i))
    rw [show j + l - G.degX i - -(((r : ℕ) + 1) • G.degX i) =
        j + (r : ℕ) • G.degX i + l by rw [add_nsmul, one_nsmul]; abel]
    exact h

/-- The nonpositive-weight case of Kang–Kashiwara, Theorem 5.2(b), on graded projectives. -/
def negativeCommutatorIso (hn : wt ≤ 0) :
    ((FeP).shift (-G.degX i)).Iso
      ((EfP).prod (GProj.pi fun r : Fin (-wt).toNat => P.shift (-(((r : ℕ) + 1) • G.degX i)))) := by
  refine GradedEquiv.ofPreserves (Neg hn) ?_
  intro d z hz
  have h := neg_preserves G Λ i β hsym hQ RD highest hΛ hdeg P hn (d := d - -G.degX i) hz
  rwa [sub_neg_eq_add, add_sub_cancel_right] at h

local notation "LP" => LaurentPolynomial ℤ
local notation "EFK" => LinearMap.comp (resK0 G Λ i β₁ hsym hQ) (indK0 G Λ i β₁)
local notation "FEK" => LinearMap.comp (indK0 G Λ i β) (resK0 G Λ i β hsym hQ)

include hΛ hdeg in
/-- The projective weight-group identity induced by Theorem 5.2(a). -/
theorem positiveCommutatorK0 (hp : 0 ≤ wt) (x : K0 (grade G Λ β₁)) :
    EFK x = (LaurentPolynomial.T (-G.degX i) : LP) • FEK x +
      (∑ r : Fin (wt).toNat, (LaurentPolynomial.T ((r : ℕ) • G.degX i) : LP)) • x := by
  induction x using K0.induction_on with
  | of N =>
    simp only [LinearMap.comp_apply, resK0_of, indK0_of]
    rw [← K0.of_eq_of_iso (positiveCommutatorIso G Λ i β hsym hQ RD highest hΛ hdeg N hp),
      K0.of_prod, K0.of_pi, K0.T_smul_of, Finset.sum_smul]
    exact congrArg (_ + ·) (Finset.sum_congr rfl fun r _ => (K0.T_smul_of _ N).symm)
  | zero => simp only [map_zero, smul_zero, add_zero]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]; ac_rfl
  | neg y hy => simp only [map_neg, smul_neg, hy, neg_add_rev]; ac_rfl

include hΛ hdeg in
/-- The projective weight-group identity induced by Theorem 5.2(b). -/
theorem negativeCommutatorK0 (hn : wt ≤ 0) (x : K0 (grade G Λ β₁)) :
    (LaurentPolynomial.T (-G.degX i) : LP) • FEK x = EFK x +
      (∑ r : Fin (-wt).toNat, (LaurentPolynomial.T (-(((r : ℕ) + 1) • G.degX i)) : LP)) • x := by
  induction x using K0.induction_on with
  | of N =>
    simp only [LinearMap.comp_apply, resK0_of, indK0_of, K0.T_smul_of]
    rw [K0.of_eq_of_iso (negativeCommutatorIso G Λ i β hsym hQ RD highest hΛ hdeg N hn),
      K0.of_prod, K0.of_pi, Finset.sum_smul]
    exact congrArg (_ + ·) (Finset.sum_congr rfl fun r _ => (K0.T_smul_of _ N).symm)
  | zero => simp only [map_zero, smul_zero, add_zero]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]; ac_rfl
  | neg y hy => simp only [map_neg, smul_neg, hy, neg_add_rev]; exact add_comm _ _

end Categorification.KLR.CycKLR
