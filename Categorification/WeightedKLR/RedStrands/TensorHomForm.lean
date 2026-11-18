/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorHomInduction

/-!
# The Euler form on the full tensor product categorification

Webster, arXiv:1309.3796v2, Lemma 4.36 and Theorem 4.38, with the repair to
the form preceding Proposition 4.33. Distinct black contents have distinct
torus weights, so the corrected tensor form makes different blocks orthogonal.
The canonical integral identification carries the graded Hom form on the
direct sum of all projective groups to the corrected tensor form. For left
projectives the target of a Hom occupies the first tensor slot.
-/
noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped RatFunc
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
local notation "series" => algebraMap L (LaurentSeries ℚ)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩
private abbrev invLP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair invLP.toRingHom invLP.toRingHom := RingHomInvPair.of_ringEquiv invLP

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "K" => tensorProjectiveGroup C hQ Λ
local notation "M" => DirectSum (Multiset I) (tensorProjectiveGroup C hQ Λ)
local notation "ι" => DirectSum.lof LP _ K
local notation "η" => tensorModuleEquiv C hQ hR Λ wt hwt
local notation "B" => TensorPairing.orderedForm hR wt

private local instance blockGdim (ν : Multiset I) : HasGdim (tensorProductGrade G ν) := by
  let := tensorProductAlgebra_finite Λ ν hQ
  exact HasGdim.of_finiteDimensional _

/-- Graded Hom on the projective group of Webster's tensor product algebra,
summing the blockwise forms on the finitely many supported contents. -/
def tensorProjectiveHomForm : M →+ M →+ LaurentSeries ℤ :=
  DirectSum.toAddMonoid fun ν =>
    { toFun := fun x => (K0.homForm (tensorProductGrade G ν) x).comp
        (DirectSum.component LP _ K ν).toAddMonoidHom
      map_zero' := by ext z; simp only [map_zero, AddMonoidHom.zero_apply, AddMonoidHom.comp_apply]
      map_add' := fun x y => by
        ext z
        simp only [map_add, AddMonoidHom.add_apply, AddMonoidHom.comp_apply] }

omit [Finite I] in
private theorem homForm_lof (ν : Multiset I) (x : K ν) (y : M) :
    tensorProjectiveHomForm C hQ Λ (ι ν x) y = K0.homForm (tensorProductGrade G ν) x (y ν) := by
  unfold tensorProjectiveHomForm
  dsimp only [DirectSum.lof_eq_of]
  rw [DirectSum.toAddMonoid_of]
  rfl

/-- The corrected form pairs distinct contents to zero, as required in the
first step of Webster's proof of Lemma 4.36. -/
theorem orderedForm_block_orthogonal {β γ : Multiset I} (h : β ≠ γ) (x : K β) (y : K γ) :
    B (η (ι β x)).val (η (ι γ y)).val = 0 := by
  let μ (s : Multiset I) : Y →+ ℤ := (∑ r, (wt r).1) - R.rootSum s.toFinsupp
  have hμ : μ β ≠ μ γ := by
    intro he
    have hc := R.rootSum_injective hR (sub_right_injective he)
    exact h (by simpa using congrArg Finsupp.toMultiset hc)
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp hμ
  have ht := TensorPairing.orderedForm_adjoint hR wt (LieLean.QuantumGroup.K R v a)
    (η (ι β x)).val (η (ι γ y)).val
  simp only [rho_K, barHom_K] at ht
  rw [tensorModuleEquiv_torus_block, tensorModuleEquiv_torus_block,
    map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at ht
  change barRingHom (v ^ μ β a) * _ = v ^ (μ γ (-a)) * _ at ht
  rw [map_neg, map_zpow₀, show barRingHom v = v⁻¹ from RatFunc.bar_X, inv_zpow'] at ht
  by_contra hn
  exact ha (neg_injective (zpow_injective_of_not_root RatFunc.X_ne_zero hvn_ratFunc
    (mul_right_cancel₀ hn ht)))

/-- Theorem 4.38 with the corrected ordered tensor form. The equality holds on
arbitrary finitely supported virtual projectives across all black contents. -/
theorem tensorModuleEquiv_homForm (x y : M) :
    lsCast (tensorProjectiveHomForm C hQ Λ x y) = series (B (η y).val (η x).val) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply, Submodule.coe_zero]
  | add x z hx hz => simp only [map_add, AddMonoidHom.add_apply, Submodule.coe_add, hx, hz]
  | of β x =>
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero, Submodule.coe_zero, LinearMap.zero_apply]
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, Submodule.coe_add, hy, hz]
    | of γ y =>
      change lsCast (tensorProjectiveHomForm C hQ Λ (ι β x) (ι γ y)) =
        series (B (η (ι γ y)).val (η (ι β x)).val)
      rw [homForm_lof]
      by_cases he : β = γ
      · subst γ
        rw [DirectSum.lof_apply]
        exact (tensorHomAgrees_iff C hQ hR Λ wt hwt β x y).mp
          (tensorHomAgrees_all C hQ hR Λ wt hwt β x y)
      · change lsCast (K0.homForm _ x (DirectSum.component LP _ K β (ι γ y))) = _
        rw [DirectSum.component.of, dite_eq_right (Ne.symm he), map_zero, map_zero,
          orderedForm_block_orthogonal C hQ hR Λ wt hwt (Ne.symm he), map_zero]

/-- Lemma 4.36 for arbitrary graded projectives in a tensor product block:
the evaluated graded Hom polynomial is the repaired form on their images. -/
theorem tensorModuleEquiv_homGdimPoly (ν : Multiset I) (P Q' : GProj (tensorProductGrade G ν)) :
    integralLaurentEval (gdimPoly (homGrade (TensorProductAlgebra k Q Λ ν) P.grading Q'.grading)) =
      B (η (ι ν (K0.of Q'))).val (η (ι ν (K0.of P))).val :=
  (tensorHomAgrees_iff_homGdimPoly C hQ hR Λ wt hwt ν P Q').mp
    (tensorHomAgrees_all C hQ hR Λ wt hwt ν (K0.of P) (K0.of Q'))

end Categorification.Stendhal.FirstWeight
