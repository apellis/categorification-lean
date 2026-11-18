/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorModuleIdentification
import Categorification.WeightedKLR.RedStrands.TensorFormOrdered
import Categorification.KLR.TightMonomials
import Categorification.KLR.BarGamma
import Categorification.Algebra.Graded.HomFormPolynomial

/-!
# Extending the tensor Hom comparison from diagram boundaries

For Webster, arXiv:1309.3796v2, §4.7, Lemmas 4.36–4.37 and Theorem 4.38,
the boundary comparison at fixed black content determines the graded Hom
form on all virtual projectives. The tensor form acts on the reversed pair
because the diagram algebras act on the left.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped RatFunc
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "series" => algebraMap L (LaurentSeries ℚ)
local instance : NeZero (RatFunc.X : L) := ⟨RatFunc.X_ne_zero⟩
private abbrev invLP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair invLP.toRingHom invLP.toRingHom := RingHomInvPair.of_ringEquiv invLP

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}
  (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
  (ν : Multiset I)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "𝓣" => tensorProductGrade G ν
local notation "K" => tensorProjectiveGroup C hQ Λ
local notation "ι" => DirectSum.lof LP _ K ν
local notation "η" => tensorModuleEquiv C hQ hR Λ wt hwt
local notation "B" => TensorPairing.orderedForm hR wt

private local instance blockGdim : HasGdim 𝓣 := by
  let := tensorProductAlgebra_finite Λ ν hQ
  exact HasGdim.of_finiteDimensional _

private def vec : K ν →+ TensorSpace wt :=
  ((integralTensor wt).subtype.toAddMonoidHom.comp (η).toAddEquiv.toAddMonoidHom).comp (ι).toAddMonoidHom

/-- Equality of the graded Hom series and the expansion of the corrected tensor
form at an ordered pair of virtual projectives of the same content. -/
def tensorHomAgrees (x y : K ν) : Prop :=
  lsCast (K0.homForm 𝓣 x y) = series (B (vec C hQ hR Λ wt hwt ν y) (vec C hQ hR Λ wt hwt ν x))

theorem tensorHomAgrees_iff (x y : K ν) :
    tensorHomAgrees C hQ hR Λ wt hwt ν x y ↔
      lsCast (K0.homForm 𝓣 x y) = series (B (η (ι y)).val (η (ι x)).val) := Iff.rfl

private theorem vec_smul (p : LP) (x : K ν) :
    vec C hQ hR Λ wt hwt ν (p • x) = qToV p • vec C hQ hR Λ wt hwt ν x := by
  change (η (ι (p • x))).val = qToV p • (η (ι x)).val
  rw [map_smul, LinearEquiv.map_smulₛₗ, Submodule.coe_smul, tensor_laurent_smul]
  exact congrArg (· • _) (CycKLR.integralEval_invert p)

private theorem bar_scalar (p : LP) : RatFunc.bar (qToV p) = barQ (qToV p) := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single n m =>
    have h : (AddMonoidAlgebra.single n m : LP) = m • LaurentPolynomial.T n := by
      rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.smul_eq_C_mul]
    rw [h, map_zsmul, map_zsmul, map_zsmul, qToV_T, Units.val_zpow_eq_zpow_val,
      map_zpow₀, map_zpow₀, vQ_val, RatFunc.bar_X, barQ_X]

local notation "A" => tensorHomAgrees C hQ hR Λ wt hwt ν

private theorem agrees_smul_left (p : LP) (hp : qToV p ≠ 0) (x y : K ν) :
    A (p • x) y ↔ A x y := by
  unfold tensorHomAgrees
  rw [lsCast_homForm_smul_left, vec_smul, map_smul, smul_eq_mul, map_mul, ← barQ_qToV, vToLS,
    RingHom.comp_apply, barQ_barQ]
  exact mul_right_inj' ((map_ne_zero series).mpr hp)

private theorem agrees_smul_right (p : LP) (hp : qToV p ≠ 0) (x y : K ν) :
    A x (p • y) ↔ A x y := by
  unfold tensorHomAgrees
  rw [lsCast_homForm_smul_right, vec_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul]
  change series (barQ (qToV p)) * _ = series (RatFunc.bar (qToV p)) * _ ↔ _
  rw [bar_scalar]
  exact mul_right_inj' ((map_ne_zero series).mpr ((map_ne_zero barQ).mpr hp))

omit [Finite I] in
private theorem from_boundaries (P : K ν → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x+y))
    (hsmul : ∀ p, qToV p ≠ 0 → ∀ x, P (p • x) ↔ P x)
    (hs : ∀ (s : KLR.Seq (stendhalWeight ℓ ν)) (ho : IsRedOrdered s), P (K0.of (sequenceProj G s ho)))
    (x : K ν) : P x := by
  have hx : x ∈ Submodule.span LP {z : K ν | ∃ (w : TensorWord I ℓ)
      (h : w.content.toMultiset = ν), z = h ▸ K0.of (tensorWordProjective Λ C hQ w)} := by
    rw [span_tensorWordProjective]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, h, rfl⟩ := hz
    subst ν
    apply (hsmul _ (KL2Gamma.qToV_divQFact2_ne_zero C w.blackBlocks) _).mp
    rw [← tensorWordProjective_factorial]
    exact hs _ _
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul p x _ hx =>
    by_cases hp : qToV p = 0
    · have h : p = 0 := qToV_injective (hp.trans (map_zero _).symm)
      simpa only [h, zero_smul] using h0
    · exact (hsmul p hp x).mpr hx

/-- At fixed black content, agreement on every pair of undivided ordered
boundary projectives suffices for agreement on all virtual projectives.
The divided-word quantum factorials cancel in the rational-function field. -/
theorem tensorHomAgrees_of_sequenceProj
    (h : ∀ (s t : KLR.Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) (ht : IsRedOrdered t),
      A (K0.of (sequenceProj G s hs)) (K0.of (sequenceProj G t ht))) (x y : K ν) : A x y := by
  apply from_boundaries C hQ Λ ν (fun a => A a y) (by simp [tensorHomAgrees])
    (fun a b ha hb => by simpa [tensorHomAgrees] using congrArg₂ (· + ·) ha hb)
    (fun p hp a => agrees_smul_left C hQ hR Λ wt hwt ν p hp a y) _ x
  intro s hs
  let z := K0.of (sequenceProj G s hs)
  exact from_boundaries C hQ Λ ν (fun b => A z b) (by simp [tensorHomAgrees])
    (fun a b ha hb => by simpa [tensorHomAgrees] using congrArg₂ (· + ·) ha hb)
    (fun p hp b => agrees_smul_right C hQ hR Λ wt hwt ν p hp z b) (fun t ht => h s t hs ht) y

private theorem expand_integralEval (p : LP) :
    lsCast (toLaurentSeries p) = series (integralLaurentEval p) := by
  rw [lsCast_toLaurentSeries, vToLS, RingHom.comp_apply, barQ_qToV, ← CycKLR.integralEval_invert]
  exact congrArg (fun t => series (integralLaurentEval t)) (LaurentPolynomial.invert.symm_apply_apply _)

/-- On actual projectives the comparison gives their ordinary graded Hom
dimension polynomial evaluated at the indeterminate. -/
theorem tensorHomAgrees_iff_homGdimPoly (P Q' : GProj 𝓣) :
    A (K0.of P) (K0.of Q') ↔
      integralLaurentEval (gdimPoly (homGrade (TensorProductAlgebra k Q Λ ν) P.grading Q'.grading)) =
        B (η (ι (K0.of Q'))).val (η (ι (K0.of P))).val := by
  let := tensorProductAlgebra_finite Λ ν hQ
  rw [tensorHomAgrees_iff, K0.homForm_of, ← GProj.toLaurentSeries_homGdimPoly 𝓣 P Q', expand_integralEval]
  exact (algebraMap L (LaurentSeries ℚ)).injective.eq_iff

end Categorification.Stendhal.FirstWeight
