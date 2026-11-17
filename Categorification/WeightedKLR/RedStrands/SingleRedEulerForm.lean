/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleRedEulerAdjunction
import Categorification.KLR.TightMonomials
import Categorification.KLR.BarGamma

/-!
# The Euler form of the cyclotomic highest-weight categorification

Webster, arXiv:1309.3796v2, §3.4, Corollary 3.22. Graded Frobenius
reciprocity computes the Hom out of an ordinary induction word. The
Cartan quantum factorials of the divided projectives are nonzero over
the rational-function field, so their integral spanning theorem extends
the comparison to arbitrary pairs of virtual projectives in each weight.
-/

noncomputable section
namespace Categorification.KLR.CycKLR

open KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded QuantumGroup QuantumGroup.UDot
open KLGamma LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open Categorification.Stendhal.SingleBlack
open scoped TensorProduct RatFunc
attribute [local instance] KLGamma.qToVAlgebra

local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
private abbrev reciprocalLaurent : LP ≃+* LP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair reciprocalLaurent.toRingHom reciprocalLaurent.toRingHom :=
  RingHomInvPair.of_ringEquiv reciprocalLaurent

local notation "series" => algebraMap L (LaurentSeries ℚ)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

private theorem bar_qToV (p : LP) : RatFunc.bar (qToV p) = barQ (qToV p) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single n m =>
    have hT : (AddMonoidAlgebra.single n m : LP) = m • LaurentPolynomial.T n := by
      rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.smul_eq_C_mul]
    rw [hT, map_zsmul, map_zsmul, map_zsmul, qToV_T, Units.val_zpow_eq_zpow_val,
      map_zpow₀, map_zpow₀, vQ_val, RatFunc.bar_X, barQ_X]

variable {k I : Type*} [Field k] [Finite I] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    {C : CartanDatum I} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (highest : X)
    (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hR : (projectiveRootDatum RD).IsXRegular)

local notation "G" => hP.gradingDatum
local notation "R" => projectiveRootDatum RD
local notation "wt" => dominantWeight Λ RD highest hΛ
local notation "η" => projectiveIntegralEquiv hP Λ RD highest hΛ hR
local notation "eQ" => projectiveHighestWeightEquiv Λ RD highest hΛ hP hR
local notation "ι" => DirectSum.lof LP _ (fun ν => K0 (grade G Λ ν))
local notation "B" => websterForm wt hR
local notation "empty" => K0.of (GProj.regular (grade G Λ 0))

private local instance blockHasGdim (β : Multiset I) : HasGdim (grade G Λ β) := by
  let := module_finite (ν := β) (fun i j hij => by
    obtain ⟨c, hc, h⟩ := hP.polyInY_leading i j hij
    rw [h]
    exact hc.map Polynomial.C) (fun j => show ((Polynomial.X : Polynomial k) ^ Λ j).Monic from Polynomial.monic_X_pow _)
  exact HasGdim.of_finiteDimensional _

private theorem integralEquiv_smul_scalar (p : LP) (x : projectiveK0 G Λ) :
    (η (p • x)).val = qToV p • (η x).val := by
  rw [projectiveIntegralEquiv_val, projectiveIntegralEquiv_val, TensorProduct.tmul_smul,
    ← IsScalarTower.algebraMap_smul L]
  exact (eQ).map_smul (qToV p) _

private def agrees (β : Multiset I) (x y : K0 (grade G Λ β)) : Prop :=
  lsCast (K0.homForm (grade G Λ β) x y) = series (B (η (ι β y)).val (η (ι β x)).val)

private theorem agrees_smul_iff (β : Multiset I) (x y : K0 (grade G Λ β)) (p : LP)
    (hp : qToV p ≠ 0) :
    agrees hP Λ RD highest hΛ hR β (p • x) y ↔ agrees hP Λ RD highest hΛ hR β x y := by
  unfold agrees
  rw [lsCast_homForm_smul_left, map_smul, integralEquiv_smul_scalar, websterForm_smul_right,
    map_mul, ← barQ_qToV, vToLS, RingHom.comp_apply, barQ_barQ]
  exact mul_right_inj' ((map_ne_zero series).mpr hp)

omit [Finite I] in
private theorem agrees_vacuum_norm :
    K0.homForm (grade G Λ 0) empty empty = 1 := by
  let A := CycKLR k Q (fun i => (Polynomial.X : Polynomial k) ^ Λ i) 0
  let e := (cyclotomicZeroEquiv Q (fun i => (Polynomial.X : Polynomial k) ^ Λ i)).symm
  let g := grade G Λ 0
  let f (d : ℤ) : homGrade A g g d ≃ₗ[k] g d :=
    { toFun := fun h => ⟨h.1 1, by simpa using (mem_homGrade.mp h.2) (SetLike.one_mem_graded g)⟩
      invFun := fun a => ⟨LinearMap.toSpanSingleton A A a, mem_homGrade.mpr fun j u hu =>
        SetLike.GradedMul.mul_mem hu a.2⟩
      left_inv := fun h => Subtype.ext (LinearMap.ext fun u => by
        change u • h.1 1 = h.1 u
        rw [← map_smul]
        exact congrArg h.1 (mul_one u))
      right_inv := fun a => Subtype.ext (one_smul A (a : A))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [K0.homForm_of]
  change gdim (homGrade A g g) = 1
  rw [gdim_eq_of_finrank_eq fun d => (f d).finrank_eq]
  ext d
  rw [coeff_gdim, HahnSeries.coeff_one]
  split_ifs with hd
  · subst d
    have hg : g 0 = ⊤ := top_unique fun a _ => mem_scalarGrade g e a
    rw [hg, finrank_top, ← e.toLinearEquiv.finrank_eq]
    simp
  · have hg : g d = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro a ha
      by_contra hn
      exact hd (DirectSum.degree_eq_of_mem_mem g ha (mem_scalarGrade g e a) hn)
    rw [hg, finrank_bot, Nat.cast_zero]

private theorem agrees_vacuum (y : K0 (grade G Λ 0)) : agrees hP Λ RD highest hΛ hR 0 empty y := by
  let e := scalarK0Equiv (grade G Λ 0) (cyclotomicZeroEquiv Q (fun i => Polynomial.X ^ Λ i)).symm
  let p := e y
  have hy : y = p • empty := (e.symm_apply_apply y).symm.trans (scalarK0Equiv_symm_apply _ _ p)
  have hv : (η (ι 0 empty)).val = IrreducibleModule.hwv R v (Subtype.val wt) := by
    rw [projectiveIntegralEquiv_val, ← projectiveVacuum_eq]
    exact projectiveHighestWeightEquiv_vacuum Λ RD highest hΛ hP hR
  rw [agrees, hy, lsCast_homForm_smul_right, agrees_vacuum_norm, map_one, mul_one,
    map_smul, integralEquiv_smul_scalar, hv, websterForm_smul_left, websterForm_hwv, mul_one,
    bar_qToV]
  rfl


private def wordInBlock (w : List I) (β : Multiset I) (h : (w : Multiset I) = β) :
    K0 (grade G Λ β) :=
  quotientK0 G Λ β (K0.of ((G).projP (Seq.ofList w h)))

omit [Finite I] in
private theorem wordInBlock_lof (w : List I) (β : Multiset I) (h : (w : Multiset I) = β) :
    ι β (wordInBlock hP Λ w β h) = totalQuotientK0 G Λ ((G).clsW w) := by
  rw [(G).clsW_eq w h]
  exact (totalQuotientK0_lof G Λ β _).symm

omit [Finite I] in
private theorem wordInBlock_nil : wordInBlock hP Λ [] 0 Multiset.coe_nil = empty := by
  apply DirectSum.of_injective (β := fun ν => K0 (grade G Λ ν)) 0
  change ι 0 _ = ι 0 _
  apply projectiveRationalization_injective hP Λ
  change (1 : L) ⊗ₜ[LP] ι 0 (wordInBlock hP Λ [] 0 Multiset.coe_nil) =
    (1 : L) ⊗ₜ[LP] ι 0 empty
  rw [wordInBlock_lof hP Λ [] 0 Multiset.coe_nil, (G).clsW_nil, ← projectiveVacuum_eq]
  rfl

private theorem agrees_word (w : List I) (β : Multiset I) (h : (w : Multiset I) = β)
    (y : K0 (grade G Λ β)) : agrees hP Λ RD highest hΛ hR β (wordInBlock hP Λ w β h) y := by
  induction w using List.reverseRecOn generalizing β with
  | nil =>
    rw [Multiset.coe_nil] at h
    subst β
    change agrees hP Λ RD highest hΛ hR 0 (wordInBlock hP Λ [] 0 Multiset.coe_nil) y
    rw [wordInBlock_nil hP Λ]
    exact agrees_vacuum hP Λ RD highest hΛ hR y
  | append_singleton w i ih =>
    have he : β = {i} + (w : Multiset I) := by rw [← h, ← Multiset.coe_add, add_comm]; rfl
    obtain rfl := he
    have step : wordInBlock hP Λ (w ++ [i]) _ h =
        indK0 G Λ i (w : Multiset I) (wordInBlock hP Λ w _ rfl) := by
      apply DirectSum.of_injective (β := fun ν => K0 (grade G Λ ν)) ({i} + (w : Multiset I))
      change ι _ _ = ι _ _
      rw [wordInBlock_lof, ← lower_lof, wordInBlock_lof, (G).clsW_append,
        lower_totalQuotientK0 G Λ i (fun a b hab => (hP.symm a b hab).symm) C.dot_self_pos]
    rw [step, agrees, homForm_ind_res G Λ i (w : Multiset I) hP.klrSymm hP.polyInY_leading,
      websterForm_ind_res]
    exact ih _ rfl _

/-- The whole single-red Euler form, in any cyclotomic weight block and
over any coefficient field. The rational Shapovalov value is expanded at
`q = 0`; its Laurent series equals the graded Hom of the corresponding
left projective classes in reversed order. Webster, arXiv:1309.3796v2,
Corollary 3.22. -/
theorem homForm_eq_websterForm (β : Multiset I) (x y : K0 (grade G Λ β)) :
    lsCast (K0.homForm (grade G Λ β) x y) =
      series (B (η (ι β y)).val (η (ι β x)).val) := by
  have hz : (η 0).val = 0 := congrArg Subtype.val ((η).toAddEquiv.map_zero)
  have hadd (a b : projectiveK0 G Λ) : (η (a+b)).val = (η a).val + (η b).val :=
    congrArg Subtype.val ((η).toAddEquiv.map_add a b)
  change agrees hP Λ RD highest hΛ hR β x y
  have hx : x ∈ Submodule.span LP {z | ∃ (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = β),
      z = K0.of (dividedProjective G (fun i j => congrArg Neg.neg (C.symm i j)) C Λ β d h)} := by
    rw [span_dividedProjective_of_rouquier C Λ β hP]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d, h, rfl⟩ := hz
    apply (agrees_smul_iff hP Λ RD highest hΛ hR β _ y (KL2.divQFact2 C d)
      (KL2Gamma.qToV_divQFact2_ne_zero C d)).mp
    have hd : wordInBlock hP Λ (expandDiv d) β h = KL2.divQFact2 C d •
        K0.of (dividedProjective G (fun i j => congrArg Neg.neg (C.symm i j)) C Λ β d h) := by
      apply DirectSum.of_injective (β := fun ν => K0 (grade G Λ ν)) β
      change ι β _ = ι β _
      rw [wordInBlock_lof, map_smul, word_eq_factorial hP Λ β d h]
    rw [← hd]
    exact agrees_word hP Λ RD highest hΛ hR _ _ h y
  | zero =>
    rw [agrees, map_zero (ι β), hz]
    simp [websterForm]
  | add a b _ _ ha hb =>
    unfold agrees at ha hb ⊢
    rw [map_add (ι β), hadd]
    simpa [websterForm] using congrArg₂ (· + ·) ha hb
  | smul p a _ ha =>
    by_cases hp : qToV p = 0
    · have hp' : p = 0 := qToV_injective (hp.trans (map_zero qToV).symm)
      rw [hp', zero_smul, agrees, map_zero (ι β), hz]
      simp [websterForm]
    · exact (agrees_smul_iff hP Λ RD highest hΛ hR β a y p hp).mpr ha

end Categorification.KLR.CycKLR
