/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.ScalarK0
import Categorification.KLR.CyclotomicTorus
import Categorification.KLR.CyclotomicWordSpan
import Categorification.KLR.K0Free
import Categorification.QuantumGroup.GabberKacBridge
import LieLean.Algebra.QuantumGroup.Basic

/-!
# Rational cyclotomic Chevalley generators

We extend the ordinary cyclotomic projective lattice along the existing
Khovanov–Lauda specialization sending the shift to the inverse indeterminate.
The quantum-group parameter is the image of the grading shift.
-/

noncomputable section
namespace Categorification.KLR.CycKLR
open KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded QuantumGroup QuantumGroup.UDot
open KLGamma LieLean
open scoped TensorProduct
attribute [local instance] KLGamma.qToVAlgebra
local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "T" => LaurentPolynomial.T (R := ℤ)

/-- The parameter of the projective action, the image of the grading shift. -/
abbrev projectiveParameter : L := ((vQ⁻¹ : Lˣ) : L)

theorem parameter_eval_T (n : ℤ) : qToV (T n) = projectiveParameter ^ n := by
  rw [qToV, laurentEval_T, Units.val_zpow_eq_zpow_val]

theorem parameter_pow_ne_one (n : ℕ) (hn : 0 < n) : projectiveParameter ^ n ≠ 1 := by
  change ((vQ⁻¹ : Lˣ) : L) ^ n ≠ 1
  rw [Units.val_inv_eq_inv_val, inv_pow, ne_eq, inv_eq_one, ← Units.val_pow_eq_pow_val,
    Units.val_eq_one]
  exact vQ_pow_ne_one hn

private theorem monomial_mul_qIntU (d n : ℤ) :
    (T d - T (-d)) * LieLean.QuantumGroup.qIntU (qUnitLP ^ d) n = T (d*n) - T (-(d*n)) := by
  apply qToV_injective
  simp only [map_mul, map_sub, parameter_eval_T]
  have H := LieLean.QuantumGroup.sub_mul_map_qIntU (qUnitLP ^ d) qToV n
  rw [val_qUnitLP_zpow, parameter_eval_T] at H
  simpa only [zpow_neg, ← zpow_mul] using H

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ)
    {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (highest : X)

/-- The root datum of the LieLean quantum group corresponding to a KLR weight datum. -/
def projectiveRootDatum : C.toLusztig.RootDatum Y where
  coroot := RD.iY
  root i := RD.pair.flip (RD.iX i)
  root_coroot := RD.pair_iY_iX

/-- The scalar extension of the ordinary cyclotomic projective lattice. -/
abbrev projectiveK0Q := L ⊗[LP] projectiveK0 G Λ

variable (hsym : KLRSymm Q)
    (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)

local notation "D" => C.toLusztig
local notation "R" => projectiveRootDatum RD
local notation "P" => projectiveK0 G Λ
local notation "M" => projectiveK0Q G Λ
local notation "ι" => DirectSum.lof LP (Multiset I) (fun ν => K0 (grade G Λ ν))
local notation "B" => Module.End.baseChangeHom LP L P
local notation "K" => toral G Λ RD highest
local notation "E" => fun i => raise G Λ i hsym hQ C
local notation "F" => lower G Λ
local notation "q" => projectiveParameter

/-- The rational torus representation. -/
def torusQ : Multiplicative Y →* Module.End L M :=
  (B).toMonoidHom.comp (torus G Λ RD highest)

private theorem extend_smul (r : LP) (f : Module.End LP P) : B (r • f) = qToV r • B f := by
  rw [map_smul, ← IsScalarTower.algebraMap_smul L]
  rfl

theorem torusQ_lower (y : Y) (i : I) :
    torusQ G Λ RD highest (.ofAdd y) * B (F i) = q ^ (-((R).root i y)) •
      (B (F i) * torusQ G Λ RD highest (.ofAdd y)) := by
  change B (K y) * B (F i) = _ • (B (F i) * B (K y))
  rw [← map_mul, toral_lower, extend_smul, parameter_eval_T, map_mul]
  rfl

theorem torusQ_raise (y : Y) (i : I) :
    torusQ G Λ RD highest (.ofAdd y) * B (E i) = q ^ ((R).root i y) •
      (B (E i) * torusQ G Λ RD highest (.ofAdd y)) := by
  change B (K y) * B (E i) = _ • (B (E i) * B (K y))
  rw [← map_mul, toral_raise, extend_smul, parameter_eval_T, map_mul]
  rfl

omit [DecidableEq I] in
private theorem d_eq_di (i : I) : ((D).d i : ℤ) = di C i := Int.toNat_of_nonneg (di_pos C i).le

variable (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
    (hdot : ∀ i, G.degX i = 2 * di C i)

include hΛ hdeg hdot in
/-- The equal-colour quantum commutator, with denominators cleared over the Laurent ring. -/
theorem integral_commutator (i : I) :
    (T (di C i) - T (-(di C i))) • (E i * F i - F i * E i) =
      K (LieLean.QuantumGroup.ktilde R i) - K (-LieLean.QuantumGroup.ktilde R i) := by
  apply DirectSum.linearMap_ext
  intro β
  apply LinearMap.ext
  intro x
  change (T _ - T _) • (E i (F i (ι β x)) - F i (E i (ι β x))) = K _ (ι β x) - K _ (ι β x)
  rw [raise_lower_sub_lower_raise G Λ i β hsym hQ RD highest (hΛ i) (hdeg i) (hdot i),
    smul_smul, monomial_mul_qIntU, sub_smul, toral_lof, toral_lof]
  simp [LieLean.QuantumGroup.ktilde, projectiveRootDatum, d_eq_di]

include hΛ hdeg hdot in
/-- The rational equal-colour Chevalley relation in the presentation of LieLean. -/
theorem rational_commutator (i : I) :
    B (E i) * B (F i) - B (F i) * B (E i) =
      (q ^ (D).d i - (q ^ (D).d i)⁻¹)⁻¹ •
      (torusQ G Λ RD highest (.ofAdd (LieLean.QuantumGroup.ktilde R i)) -
       torusQ G Λ RD highest (.ofAdd (-LieLean.QuantumGroup.ktilde R i))) := by
  have hne : q ^ (D).d i - (q ^ (D).d i)⁻¹ ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    have hq : q ^ (D).d i ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
    have h1 : (q ^ (D).d i) * q ^ (D).d i = 1 := by
      nth_rw 1 [he]
      exact inv_mul_cancel₀ hq
    exact parameter_pow_ne_one _ (add_pos ((D).d_pos i) ((D).d_pos i)) (by rwa [pow_add])
  have H := congrArg B (integral_commutator G Λ RD highest hsym hQ hΛ hdeg hdot i)
  rw [extend_smul, map_sub, parameter_eval_T, parameter_eval_T, ← d_eq_di, zpow_neg,
    zpow_natCast, map_sub, map_mul, map_mul, map_sub] at H
  change _ = _ • (B (K (LieLean.QuantumGroup.ktilde R i)) - B (K (-LieLean.QuantumGroup.ktilde R i)))
  rw [← H, smul_smul, inv_mul_cancel₀ hne, one_smul]


/-- The highest-weight vector, the scalar extension of the empty projective. -/
def projectiveVacuum : M := 1 ⊗ₜ[LP] totalQuotientK0 G Λ 1

private theorem vacuum_integral_lof :
    totalQuotientK0 G Λ 1 = ι 0 (quotientK0 G Λ 0 (K0.of (GProj.regular (G.grade 0)))) := by
  rw [G.K0R_one]
  exact totalQuotientK0_lof _ _ _ _

/-- The cyclotomic vacuum is the regular module in the empty block. -/
theorem projectiveVacuum_eq : projectiveVacuum G Λ =
    (1 : L) ⊗ₜ[LP] ι 0 (K0.of (GProj.regular (grade G Λ 0))) := by
  rw [projectiveVacuum, vacuum_integral_lof]
  congr 2
  rw [← K0.of_eq_of_iso (𝒜 := G.grade 0) GProj.ofIdempotentOneIso,
    quotientK0_ofIdempotent]
  exact (K0.of_ofIdempotent_congr (map_one _) _ IsIdempotentElem.one _ SetLike.GradedOne.one_mem).trans
    (K0.of_eq_of_iso GProj.ofIdempotentOneIso)

/-- Nonvanishing of the vacuum follows from the empty block being the base field
(Kang–Kashiwara, Theorem 6.2). -/
theorem projectiveVacuum_ne_zero : projectiveVacuum G Λ ≠ 0 := by
  let e := scalarK0Equiv (grade G Λ 0) (cyclotomicZeroEquiv Q (fun i => Polynomial.X ^ Λ i)).symm
  let p := DirectSum.component LP (Multiset I) (fun β => K0 (grade G Λ β)) 0
  have he : e (K0.of (GProj.regular (grade G Λ 0))) = 1 := by
    apply e.symm.injective
    rw [LinearEquiv.symm_apply_apply]
    exact (scalarK0Equiv_symm_apply _ _ 1).trans (one_smul _ _ ) |>.symm
  intro hz
  have H := congrArg (fun x => TensorProduct.rid LP L (((e.toLinearMap.comp p).baseChange L) x)) hz
  rw [projectiveVacuum_eq, LinearMap.baseChange_tmul, TensorProduct.rid_tmul,
    LinearMap.comp_apply] at H
  have hp (x : K0 (grade G Λ 0)) : p (ι 0 x) = x := by simp [p]
  rw [hp, LinearEquiv.coe_coe, he, one_smul, map_zero, map_zero] at H
  exact one_ne_zero H

/-- The empty projective is primitive for normalized restriction. -/
theorem raiseQ_vacuum (i : I) : B (E i) (projectiveVacuum G Λ) = 0 := by
  change (1 : L) ⊗ₜ[LP] E i (totalQuotientK0 G Λ 1) = 0
  rw [vacuum_integral_lof, raise_lof_of_notMem _ _ _ _ _ _ _ (Multiset.notMem_zero i),
    TensorProduct.tmul_zero]

/-- The empty projective has torus weight Λ (Kang–Kashiwara, Theorem 6.2). -/
theorem torusQ_vacuum (y : Y) :
    torusQ G Λ RD highest (.ofAdd y) (projectiveVacuum G Λ) =
      q ^ RD.pair y highest • projectiveVacuum G Λ := by
  change (1 : L) ⊗ₜ[LP] K y (totalQuotientK0 G Λ 1) =
    q ^ RD.pair y highest • ((1 : L) ⊗ₜ[LP] totalQuotientK0 G Λ 1)
  rw [vacuum_integral_lof, toral_lof]
  simp only [Multiset.map_zero, Multiset.sum_zero, sub_zero, TensorProduct.tmul_smul]
  rw [← IsScalarTower.algebraMap_smul L, ← parameter_eval_T]
  rfl

private theorem parameter_eval_qbinom (d : ℤ) (n a : ℕ) :
    qToV (qbinom (KL2.tUnit d) n a) = LieLean.QuantumGroup.qBinomial (q ^ d) n a := by
  induction n generalizing a with
  | zero => cases a <;> simp
  | succ n ih =>
    cases a with
    | zero => simp
    | succ a =>
      by_cases h : a ≤ n
      · rw [qbinom_succ_succ, LieLean.QuantumGroup.qBinomial_succ_succ, map_add, map_mul,
          map_mul, ih, ih, KL2.val_tUnit_zpow, KL2.val_tUnit_zpow, parameter_eval_T,
          parameter_eval_T, zpow_mul, zpow_mul, zpow_neg, ← Nat.cast_succ a,
          zpow_natCast, inv_pow, ← Nat.cast_sub h, zpow_natCast]
      · rw [qbinom_eq_zero_of_lt _ (by omega), LieLean.QuantumGroup.qBinomial_eq_zero_of_lt _ (by omega), map_zero]

/-- The lowering functors satisfy the quantum Serre relations after scalar extension
(Kang–Kashiwara, arXiv:1102.4677v4, Lemma 6.1). -/
theorem rational_lower_serre (hP : IsRouquierQ C Q) {i j : I} (hij : i ≠ j) :
    LieLean.QuantumGroup.qSerre (q ^ (D).d i) (1 - (D).cartanMatrix i j).toNat
      ((Module.End.baseChangeHom LP L _) (lower hP.gradingDatum Λ i))
      ((Module.End.baseChangeHom LP L _) (lower hP.gradingDatum Λ j)) = 0 := by
  let b := Module.End.baseChangeHom LP L (projectiveK0 hP.gradingDatum Λ)
  have ht := congrArg b (lower_serre hP Λ hij)
  change b _ = b 0 at ht
  have hs (c : LP) (f : Module.End LP (projectiveK0 hP.gradingDatum Λ)) :
      b (c • f) = qToV c • b f := extend_smul _ _ _ _
  simp only [map_sum, hs, map_mul, map_pow, map_neg, map_one, map_zero, parameter_eval_qbinom] at ht
  change (∑ a ∈ Finset.range (C.serreN i j + 1), _ • _) = 0
  have hi : C.dot i i / 2 = ((D).d i : ℤ) := (d_eq_di i).symm
  have hn : (1 - (D).cartanMatrix i j).toNat = C.serreN i j := rfl
  simpa only [hi, hn, zpow_natCast, b] using ht

section RankOne
variable [Subsingleton I]

omit [DecidableEq I] in
private theorem singleColourSymm : KLRSymm Q := fun i j hij => False.elim (hij (Subsingleton.elim i j))

omit [DecidableEq I] in
private theorem singleColourLeading (s t : I) (hst : s ≠ t) :
    ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c :=
  False.elim (hst (Subsingleton.elim s t))

local notation "E₁" => fun i => raise G Λ i singleColourSymm singleColourLeading C

include hΛ hdot in
/-- All Chevalley and Serre relations for the actual projective functors in rank one. -/
theorem rankOneRelations :
    LieLean.QuantumGroup.Relations R q (fun i => B (E₁ i)) (fun i => B (F i))
      (torusQ G Λ RD highest) where
  K_mul_E := torusQ_raise G Λ RD highest singleColourSymm singleColourLeading
  K_mul_F := torusQ_lower G Λ RD highest
  E_mul_F i j := by
    obtain rfl := Subsingleton.elim i j
    rw [ite_eq_left rfl]
    exact rational_commutator G Λ RD highest _ _ hΛ
      (fun a b hab => False.elim (hab (Subsingleton.elim b a))) hdot i
  serre_E i j hij := False.elim (hij (Subsingleton.elim i j))
  serre_F i j hij := False.elim (hij (Subsingleton.elim i j))

/-- The action of the rank-one quantum group on the scalar-extended ordinary
cyclotomic projective Grothendieck group (Kang–Kashiwara, Theorem 6.2). -/
def rankOneRepresentation : LieLean.QuantumGroup R q →ₐ[L] Module.End L M :=
  LieLean.QuantumGroup.lift (rankOneRelations G Λ RD highest hΛ hdot)

@[simp] theorem rankOneRepresentation_E (i : I) :
    rankOneRepresentation G Λ RD highest hΛ hdot (LieLean.QuantumGroup.E R q i) = B (E₁ i) :=
  LieLean.QuantumGroup.lift_E _ _

@[simp] theorem rankOneRepresentation_F (i : I) :
    rankOneRepresentation G Λ RD highest hΛ hdot (LieLean.QuantumGroup.F R q i) = B (F i) :=
  LieLean.QuantumGroup.lift_F _ _

@[simp] theorem rankOneRepresentation_K (y : Y) :
    rankOneRepresentation G Λ RD highest hΛ hdot (LieLean.QuantumGroup.K R q y) =
      torusQ G Λ RD highest (.ofAdd y) := LieLean.QuantumGroup.lift_K _ _

end RankOne

end Categorification.KLR.CycKLR
