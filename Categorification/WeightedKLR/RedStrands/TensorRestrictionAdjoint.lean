/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorHomGeneration
import Categorification.WeightedKLR.RedStrands.TensorModuleRaising
import Categorification.WeightedKLR.RedStrands.BlackHomAdjunction
import Categorification.WeightedKLR.RedStrands.TensorFormOrdered

/-!
# The adjoint shift of raw black restriction

Webster, arXiv:1309.3796v2, (3.24) and §4.7, Lemma 4.36. A block's
torus weight accounts for the difference between the projective
normalization of E and the unshifted adjoint of black induction.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR Categorification.Graded QuantumGroup QuantumGroup.UDot LieLean LieLean.QuantumGroup
  LieLean.QuantumGroup.GrandLoop LusztigF

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩
variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}
  (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R)
  (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
local notation "η" => tensorModuleEquiv C hQ hR Λ wt hwt
local notation "ι" => DirectSum.lof LP _ (tensorProjectiveGroup C hQ Λ)
local notation "Kact" => tensorRepresentation wt
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

/-- The toral action on the image of a virtual class in a single black content. -/
theorem tensorModuleEquiv_torus_block (ν : Multiset I) (x : tensorProjectiveGroup C hQ Λ ν) (a : Y) :
    Kact (K R v a) (η (ι ν x) : TensorSpace wt) =
      v ^ (((∑ r, (wt r).1) - R.rootSum ν.toFinsupp) a) • (η (ι ν x) : TensorSpace wt) := by
  have hx : x ∈ Submodule.span LP {z | ∃ (w : TensorWord I ℓ) (e : w.content.toMultiset = ν),
      z = e ▸ K0.of (tensorWordProjective Λ C hQ w)} := by
    rw [span_tensorWordProjective Λ C hQ ν]
    trivial
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, rfl, rfl⟩ := hz
    change Kact _ (η (tensorWordProjectiveClass Λ C hQ w) : TensorSpace wt) = _
    rw [show ι _ (K0.of (tensorWordProjective Λ C hQ w)) = tensorWordProjectiveClass Λ C hQ w from rfl,
      tensorModuleEquiv_word]
    rw [Finsupp.toMultiset_toFinsupp]
    exact tensorWordVector_torus w wt a
  | zero =>
    rw [map_zero, (η).map_zero, Submodule.coe_zero, map_zero, smul_zero]
  | add x y _ _ hx hy => simp only [map_add, Submodule.coe_add, smul_add, hx, hy]
  | smul p x _ hx =>
    simp only [map_smul, map_smulₛₗ, SetLike.val_smul, tensor_laurent_smul]
    rw [hx, smul_comm]

omit [Finite I] in
private theorem rootSum_coroot (ν : Multiset I) (i : I) :
    R.rootSum ν.toFinsupp (R.coroot i) = (ν.map (A C i)).sum := by
  induction ν using Multiset.induction_on with
  | empty => simp [LusztigCartanDatum.RootDatum.rootSum]
  | cons j ν ih =>
    rw [← Multiset.singleton_add, map_add, R.rootSum_add, AddMonoidHom.add_apply,
      Multiset.toFinsupp_singleton, R.rootSum_single, Multiset.map_add, Multiset.sum_add, ih]
    simp [R.root_coroot, A, LusztigCartanDatum.cartanMatrix]
    rfl

omit [Finite I] in
include hwt in
private theorem negative_torus_weight (ν : Multiset I) (i : I) :
    ((∑ r, (wt r).1) - R.rootSum ν.toFinsupp) (-ktilde R i) =
      -(C.toLusztig.d i : ℤ) *
        ((∑ r, (Λ r i : ℤ)) - (ν.map (A C i)).sum) := by
  rw [map_neg, ktilde, map_nsmul, nsmul_eq_mul, AddMonoidHom.sub_apply,
    rootSum_coroot C]
  simp only [AddMonoidHom.finsetSum_apply, ← hwt]
  ring

private theorem equiv_shift (n : ℤ) (x : DirectSum (Multiset I) (tensorProjectiveGroup C hQ Λ)) :
    (η ((LaurentPolynomial.T n : LP) • x) : TensorSpace wt) = v ^ (-n) • (η x : TensorSpace wt) := by
  rw [LinearEquiv.map_smulₛₗ, Submodule.coe_smul, tensor_laurent_smul]
  simp [integralLaurentEval_T]

/-- Raw restriction corresponds to the inverse adjoint of F in (3.24). -/
theorem tensorModuleEquiv_blackResK0 (ν : Multiset I) (i : I)
    (y : tensorProjectiveGroup C hQ Λ ((Singleton.singleton i : Multiset I) + ν)) :
    (η (ι ν (blackResK0 G i ν C hQ y)) : TensorSpace wt) =
      Kact (rho R v (F R v i)) (η (ι _ y) : TensorSpace wt) := by
  have he := tensorModuleEquiv_E C hQ hR Λ wt hwt i (ι _ y)
  let z := blackResK0 G i ν C hQ y
  let d := CycKLR.raiseShift (fun j => ∑ r, Λ r j) i ν C
  have he' : v ^ (-d) • (η (ι ν z) : TensorSpace wt) =
      Kact (E R v i) (η (ι _ y) : TensorSpace wt) := by
    rw [blackRaise_lof, blackRaiseK0, LinearMap.smul_apply, map_smul, equiv_shift] at he
    exact he
  change (η (ι ν z) : TensorSpace wt) = _
  rw [rho_F, rhoF, map_smul, LinearMap.smul_apply, map_mul, Module.End.mul_apply,
    ← he', map_smul, tensorModuleEquiv_torus_block C hQ hR Λ wt hwt, negative_torus_weight C Λ wt hwt,
    smul_smul, smul_smul]
  suffices h : v ^ C.toLusztig.d i * (v ^ (-d) *
      v ^ (-(C.toLusztig.d i : ℤ) * ((∑ r, (Λ r i : ℤ)) - (ν.map (A C i)).sum))) = 1 by
    rw [mul_assoc, h, one_smul]
  have hd : di C i = (C.toLusztig.d i : ℤ) := by
    have h₁ := two_mul_di C i
    have h₂ := C.toLusztig.two_mul_d i
    change 2 * (C.toLusztig.d i : ℤ) = C.dot i i at h₂
    omega
  rw [← zpow_natCast, ← zpow_add₀ RatFunc.X_ne_zero, ← zpow_add₀ RatFunc.X_ne_zero]
  simp only [d, CycKLR.raiseShift, hd, Nat.cast_sum]
  ring_nf
  exact zpow_zero _

/-- When induction adds a terminal black strand to the first projective,
graded Frobenius reciprocity and (3.24) reduce the comparison to the
lower block, as in Webster, arXiv:1309.3796v2, Lemma 4.36. -/
theorem tensorHomAgrees_blackInd (i : I) (ν : Multiset I)
    (ih : ∀ x y : tensorProjectiveGroup C hQ Λ ν, tensorHomAgrees C hQ hR Λ wt hwt ν x y)
    (x : tensorProjectiveGroup C hQ Λ ν) (y : tensorProjectiveGroup C hQ Λ ({i} + ν)) :
    tensorHomAgrees C hQ hR Λ wt hwt ({i} + ν) (blackIndK0 G i ν x) y := by
  let := tensorProductAlgebra_finite Λ ν hQ
  let := tensorProductAlgebra_finite Λ ({i} + ν) hQ
  let := HasGdim.of_finiteDimensional (tensorProductGrade G ν)
  let := HasGdim.of_finiteDimensional (tensorProductGrade G ({i} + ν))
  rw [tensorHomAgrees_iff, homForm_blackInd_blackRes G i ν C hQ,
    (tensorHomAgrees_iff C hQ hR Λ wt hwt ν _ _).mp (ih x (blackResK0 G i ν C hQ y))]
  rw [tensorModuleEquiv_blackResK0 C hQ hR Λ wt hwt ν i y, TensorPairing.orderedForm_adjoint]
  simp only [rho_rho, barHom_F]
  rw [← blackLower_lof, tensorModuleEquiv_F]

end Categorification.Stendhal.FirstWeight
