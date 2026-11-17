/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleBlackLattice
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorBar

import Categorification.WeightedKLR.RedStrands.SingleBlackEuler

/-!
# The one-factor Euler and Shapovalov forms in the first lowering weight

Webster, arXiv:1309.3796v2, §3.4, (3.24) and Corollary 3.22, and §4.7,
Lemma 4.36. The normalized contravariant sesquilinear form evaluated on
the first lowering vector is the graded dimension of its projective's endomorphisms.
-/

noncomputable section

namespace Categorification.Stendhal.SingleBlack

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open LieLean.QuantumGroup.Sl2.RankOne LusztigF Categorification.Graded

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local notation "LP" => LaurentPolynomial ℤ
local notation "hvt" => transcendental_ratFunc_X
local instance : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y} (highest : Dom R) (hR : R.IsXRegular)

local notation "V" => IrreducibleModule R 𝕍 (Subtype.val highest)
local notation "vλ" => IrreducibleModule.hwv R 𝕍 (Subtype.val highest)
local notation "B" => IrreducibleModule.form (Subtype.val highest) hR hvn_ratFunc

/-- Webster's one-factor form, arXiv:1309.3796v2, Corollary 3.22 and (3.24).
Taking the bar of the value of Lusztig's contravariant form with its second
vector barred makes the first argument semilinear. -/
def websterForm (x y : V) : 𝕂 := RatFunc.bar (B x (hwBar hR highest y))

/-- The adjoint is the bar of Lusztig's contravariant antiautomorphism. -/
theorem websterForm_adjoint (u : QuantumGroup R 𝕍) (x y : V) :
    websterForm highest hR (u • x) y =
      websterForm highest hR x (barHom R (rho R 𝕍 u) • y) := by
  rw [websterForm, websterForm, IrreducibleModule.isContravariant_form,
    hwBar_smul_U, barHom_barHom]

/-- Linearity in the second argument, as in Webster §3.4. -/
theorem websterForm_smul_right (c : 𝕂) (x y : V) :
    websterForm highest hR x (c • y) = c * websterForm highest hR x y := by
  simp [websterForm, smul_eq_mul, RatFunc.bar_bar]

/-- Antilinearity in the first argument. -/
theorem websterForm_smul_left (c : 𝕂) (x y : V) :
    websterForm highest hR (c • x) y = RatFunc.bar c * websterForm highest hR x y := by
  simp [websterForm, smul_eq_mul]

/-- The highest weight vector has norm one. -/
theorem websterForm_hwv : websterForm highest hR vλ vλ = 1 := by
  simp [websterForm, hwBar_hwv]

variable (i : I)
local notation "fλ" => F R 𝕍 i • vλ
local notation "qᵢ" => 𝕍 ^ D.d i

omit [Finite I] in
include hR in
private theorem E_lower_hwv : E R 𝕍 i • fλ =
    qIntZ qᵢ (highest.1 (R.coroot i)) • vλ := by
  have hE := (nodeSl2 R 𝕍 V hvn_ratFunc (isInt hvt hR highest) i).E_F_sub
    (mem_nodeWt_of_mem (i := i) (IrreducibleModule.hwv_mem_weightSpace (R := R) (v := 𝕍)
      (Λ := highest.1)))
  change E R 𝕍 i • fλ - F R 𝕍 i • (E R 𝕍 i • vλ) = _ at hE
  simpa only [IrreducibleModule.E_smul_hwv, smul_zero, sub_zero] using hE

/-- The norm of the first lowering vector for the normalized form (3.24). -/
theorem websterForm_lowered :
    websterForm highest hR fλ fλ =
      qᵢ ^ (highest.1 (R.coroot i) - 1) * qIntZ qᵢ (highest.1 (R.coroot i)) := by
  have hτ : barHom R (rho R 𝕍 (F R 𝕍 i)) = qᵢ⁻¹ • (Kt R 𝕍 i * E R 𝕍 i) := by
    rw [rho_F, rhoF, barHom_smul, map_mul, barHom_K, barHom_E, neg_neg, Kt]
    simp [inv_pow]
  rw [websterForm_adjoint, hτ, smul_assoc, mul_smul, E_lower_hwv highest hR i, smul_comm (Kt R 𝕍 i),
    Kt_smul_of_mem_weightSpace IrreducibleModule.hwv_mem_weightSpace i]
  rw [websterForm_smul_right, websterForm_smul_right, websterForm_smul_right, websterForm_hwv, mul_one]
  rw [zpow_sub₀ (pow_ne_zero _ RatFunc.X_ne_zero), zpow_one, div_eq_mul_inv]
  ring

private theorem scaled_qInt (q : 𝕂) (hq : q ≠ 0) (hnr : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (m : ℕ) :
    q ^ ((m : ℤ) - 1) * qIntZ q m = ∑ a : Fin m, q ^ (2 * (a.val : ℤ)) := by
  rw [qIntZ_natCast (sub_inv_ne_zero_of_pow_ne_one hq hnr), qInt,
    ← Finset.sum_range_reflect (fun a => q ^ (m - 1 - a) * q⁻¹ ^ a) m, Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun a : ℕ => q ^ (2 * (a : ℤ))) m]
  apply Finset.sum_congr rfl
  intro a ha
  have ham := Finset.mem_range.mp ha
  simp only [← zpow_natCast, inv_zpow', ← zpow_add₀ hq]
  congr 1
  omega

variable {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    {Λ : Fin 1 → I →₀ ℕ} (G : KLR.GradingDatum (stendhalQ Q Λ))
local notation "𝒯" => TensorProductAlgebra k Q Λ (Singleton.singleton i : Multiset I)
local notation "𝒜" => tensorProductGrade G (Singleton.singleton i : Multiset I)

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- The one-factor first-weight case of Webster, arXiv:1309.3796v2, Corollary 3.22
and Lemma 4.36. With black dots in degree `2dᵢ`, the graded Hom polynomial of
the regular projective equals the normalized Shapovalov norm of `Fᵢvλ`.
This includes the zero block at multiplicity zero. -/
theorem regular_homGdimPoly_eq_shapovalov
    (hwt : highest.1 (R.coroot i) = (Λ 0 i : ℤ)) (hdeg : G.degX (.inl i) = 2 * (D.d i : ℤ)) :
    integralLaurentEval (gdimPoly (homGrade 𝒯 𝒜 𝒜)) = websterForm highest hR fλ fλ := by
  rw [regular_homGdimPoly, map_sum, websterForm_lowered, hwt,
    scaled_qInt qᵢ (pow_ne_zero _ RatFunc.X_ne_zero) (vd_pow_ne_one (D := D) hvn_ratFunc i)]
  apply Finset.sum_congr rfl
  intro a _
  rw [integralLaurentEval_T, hdeg, nsmul_eq_mul, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

/-- The shifted comparison for Corollary 3.22. Webster's projectives are
right modules, while the library uses left projectives. Reversing the
endpoints here gives the factor `q^(a-b)` for the reciprocal-shift
lattice equivalence of §1.2. -/
theorem regular_shift_homGdimPoly_eq_shapovalov
    (hwt : highest.1 (R.coroot i) = (Λ 0 i : ℤ)) (hdeg : G.degX (.inl i) = 2 * (D.d i : ℤ))
    (hi : 0 < Λ 0 i) (a b : ℤ) :
    integralLaurentEval (gdimPoly (homGrade 𝒯 (shift 𝒜 b) (shift 𝒜 a))) =
      websterForm highest hR
        (oneBlackLatticeEquiv highest i G hR hwt hi (K0.of ((GProj.regular 𝒜).shift a)))
        (oneBlackLatticeEquiv highest i G hR hwt hi (K0.of ((GProj.regular 𝒜).shift b))) := by
  rw [regular_shift_homGdimPoly, map_mul, integralLaurentEval_T,
    regular_homGdimPoly_eq_shapovalov highest hR i G hwt hdeg,
    oneBlackLatticeEquiv_regular_shift, oneBlackLatticeEquiv_regular_shift,
    websterForm_smul_left, websterForm_smul_right, bar_X_zpow, neg_neg,
    ← mul_assoc, ← zpow_add₀ RatFunc.X_ne_zero, sub_eq_add_neg]

end Categorification.Stendhal.SingleBlack
