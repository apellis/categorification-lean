/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicLowerCrossing
import Categorification.KLR.CyclotomicProjective
import Categorification.KLR.Examples.Small

/-!
# The genuine lower-rank cyclotomic map P′

The top horizontal map in Kang–Kashiwara, arXiv:1102.4677v4, §5.2,
is right multiplication by `a^Λ(x₁) τ₁ ⋯ τ_{n-1}` on the first factor
of `K₁′`. Here `τ=-ψ`, so the positive-crossing multiplier `tauW` is
scaled by `(-1)^|γ|`. Balancing is proved in the actual tensor over `R(γ)`;
the cyclotomic error terms vanish in the coefficient `e(γ,i)R^Λ(β)`.
The empty lower rank is handled using `R(0) ≃ k`. No domain, factorization
or monicity assumption is needed.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open scoped TensorProduct
open MulOpposite
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
  (a : I → Polynomial k)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β" => (Si + γ)
local notation "Rb" => KLRAlgebra k Q β
local notation "Rl" => CycKLR k Q a β
local notation "L" => CornerTensor.Left (lowerLast Q i γ)
local notation "N" => LowerCoefficient Q i γ a

/-- Project an ambient element to the lower last-colour left ideal. -/
def lowerLastProj : Rb →ₗ[Rb] L :=
  Graded.leftIdealProj (by
    change lowerLast Q i γ 1 * lowerLast Q i γ 1 = lowerLast Q i γ 1
    rw [← map_mul, one_mul])

/-- The lower tensor with its first factor projected to the prescribed colour cut. -/
def lowerZeroElem (r : Rb) (y : N) : KZeroPrime Q i γ a :=
  BalancedTensor.tmul (lowerLastProj Q i γ r) y

theorem lowerZeroElem_balance (r : Rb) (b : KLRAlgebra k Q γ) (y : N) :
    lowerZeroElem Q i γ a (r * cL Q i γ b) y =
      lowerZeroElem Q i γ a r (b • y) := by
  change BalancedTensor.tmul _ y = BalancedTensor.tmul _ (b • y)
  rw [← BalancedTensor.op_smul_tmul]
  congr 1
  apply Subtype.ext
  change (r * cL Q i γ b) * cL Q i γ 1 = (r * cL Q i γ 1) * cL Q i γ b
  simp only [mul_assoc, ← cL_mul, mul_one, one_mul]

private theorem lowerZeroElem_zero_right (r : Rb) : lowerZeroElem Q i γ a r 0 = 0 :=
  BalancedTensor.tmul_zero _

private theorem lowerZeroElem_cyc (r : Rb) (b : KLRAlgebra k Q γ)
    (hb : b ∈ cycIdeal Q a γ) (y : N) :
    lowerZeroElem Q i γ a (r * cL Q i γ b) y = 0 := by
  rw [lowerZeroElem_balance]
  have h : b • y = 0 := by
    apply Subtype.ext
    change CycKLR.mk k Q a β (cL Q i γ b) * (y : Rl) = 0
    rw [(CycKLR.mk_eq_zero_iff _).2 (cL_mem_cycIdeal i γ a hb), zero_mul]
  rw [h, lowerZeroElem_zero_right]

private theorem lowerZeroElem_cycL0 (hγ : 0 < Multiset.card γ) (r : Rb)
    (hr : r ∈ cycL0 a (zero_lt_card_single_add i γ)) (y : N) :
    lowerZeroElem Q i γ a r y = 0 := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨w, hw, rfl⟩ := hr
    obtain ⟨t, ht⟩ := exists_cLL_of_subR0 i γ hw
    have he : lowerZeroElem Q i γ a (cycAt a ⟨0, zero_lt_card_single_add i γ⟩ * w) y =
        lowerZeroElem Q i γ a (cLL Q i γ ((cycAt a ⟨0, hγ⟩ ⊗ₜ 1) * t)) y := by
      unfold lowerZeroElem
      congr 1
      apply Subtype.ext
      change (cycAt a _ * w) * cL Q i γ 1 =
        cLL Q i γ ((cycAt a ⟨0, hγ⟩ ⊗ₜ 1) * t) * cL Q i γ 1
      rw [mul_assoc, ht, cLL_mul_cL_one, cLL_mul, cLL_tmul_one,
        ← cL_one_mul_cLL i γ t, ← mul_assoc, cycAt_mul_cL_one i γ a hγ]
      rw [cL_one_mul_cLL, cLL_tmul_one]
    rw [he]
    clear he ht w hw
    induction t using TensorProduct.inductionOn with
    | add t u ht hu =>
      simp only [mul_add, map_add, lowerZeroElem, BalancedTensor.add_tmul] at *
      rw [ht, hu, add_zero]
    | tmul b c =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have hc : cLL Q i γ ((cycAt a ⟨0, hγ⟩ * b) ⊗ₜ c) =
          cLL Q i γ (1 ⊗ₜ c) * cL Q i γ (cycAt a ⟨0, hγ⟩ * b) := by
        rw [← cLL_tmul_one, ← cLL_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [hc]
      exact lowerZeroElem_cyc Q i γ a _ _
        (TwoSidedIdeal.mul_mem_right _ _ _ (cycAt_mem_cycIdeal a hγ)) y
  | zero => simp only [lowerZeroElem, map_zero, BalancedTensor.zero_tmul]
  | add r s _ _ hr hs =>
    simp only [lowerZeroElem, map_add, BalancedTensor.add_tmul] at *
    rw [hr, hs, add_zero]
  | smul r s _ hs =>
    change BalancedTensor.tmul (lowerLastProj Q i γ (r • s)) y = 0
    rw [map_smul, ← BalancedTensor.smul_tmul']
    change r • lowerZeroElem Q i γ a s y = 0
    rw [hs, smul_zero]

/-- The lower cyclotomic multiplier with the library's positive crossing convention. -/
def lowerPBil : CornerTensor.Left (lowerFirst Q i γ) →ₗ[k] N →ₗ[k] KZeroPrime Q i γ a :=
  LinearMap.mk₂ k (fun x y => lowerZeroElem Q i γ a
    ((x : Rb) * tauW a (zero_lt_card_single_add i γ) (Multiset.card γ)) y)
    (fun x z y => by
      change lowerZeroElem Q i γ a (((x : Rb) + (z : Rb)) * _) y = _
      simp only [add_mul, lowerZeroElem, map_add, BalancedTensor.add_tmul])
    (fun c x y => by
      change lowerZeroElem Q i γ a ((c • (x : Rb)) * _) y = _
      simp only [smul_mul_assoc, lowerZeroElem, LinearMap.map_smul_of_tower, BalancedTensor.smul_tmul])
    (fun x y z => BalancedTensor.tmul_add _ _ _)
    (fun c x y => BalancedTensor.tmul_smul _ _ _)

private theorem lowerPBil_balance_pos (hγ : 0 < Multiset.card γ)
    (x : CornerTensor.Left (lowerFirst Q i γ)) (r : KLRAlgebra k Q γ) (y : N) :
    lowerPBil Q i γ a (op r • x) y = lowerPBil Q i γ a x (r • y) := by
  change lowerZeroElem Q i γ a (((x : Rb) * cR Q i γ r) * _) y =
    lowerZeroElem Q i γ a ((x : Rb) * _) (r • y)
  rw [← lowerZeroElem_balance]
  have hz := lowerZeroElem_cycL0 Q i γ a hγ
    ((x : Rb) * (cR Q i γ r * tauW a (zero_lt_card_single_add i γ) (Multiset.card γ) -
      tauW a (zero_lt_card_single_add i γ) (Multiset.card γ) * cL Q i γ r))
    (Submodule.smul_mem _ (x : Rb) (cR_mul_tauW_sub_mem i γ a r)) y
  simp only [mul_sub, ← mul_assoc, lowerZeroElem, map_sub, BalancedTensor.tmul,
    TensorProduct.sub_tmul] at hz
  exact sub_eq_zero.mp hz

/-- Balancing at rank zero uses `R(0)=k`, not a fictitious positive lower rank. -/
theorem lowerPBil_balance (x : CornerTensor.Left (lowerFirst Q i γ))
    (r : KLRAlgebra k Q γ) (y : N) :
    lowerPBil Q i γ a (op r • x) y = lowerPBil Q i γ a x (r • y) := by
  by_cases hγ : 0 < Multiset.card γ
  · exact lowerPBil_balance_pos Q i γ a hγ x r y
  · have hg : γ = 0 := Multiset.card_eq_zero.mp (by omega)
    subst γ
    obtain ⟨c, rfl⟩ := (zeroEquiv I k Q).symm.surjective r
    rw [zeroEquiv_symm_apply, Algebra.algebraMap_eq_smul_one]
    have hx : op (c • (1 : KLRAlgebra k Q 0)) • x = c • x := by
      rw [op_smul, smul_assoc, op_one, one_smul]
    have hy : (c • (1 : KLRAlgebra k Q 0)) • y = c • y := by
      rw [smul_assoc, one_smul]
    rw [hx, hy, map_smul, LinearMap.smul_apply, map_smul]

/-- The actual lower `P′` of §5.2, translated using `τ=-ψ`.
The multiplier is the cyclotomic polynomial, not a single dot. -/
def lowerP : KOnePrime Q i γ a →ₗ[k] KZeroPrime Q i γ a :=
  ((-1 : k) ^ Multiset.card γ) •
    BalancedTensor.lift (lowerPBil Q i γ a) (lowerPBil_balance Q i γ a)

/-- The representative formula on the genuine source tensor. -/
theorem lowerP_tmul (x : CornerTensor.Left (lowerFirst Q i γ)) (y : N) :
    lowerP Q i γ a (BalancedTensor.tmul x y) =
      ((-1 : k) ^ Multiset.card γ) • lowerZeroElem Q i γ a
        ((x : Rb) * tauW a (zero_lt_card_single_add i γ) (Multiset.card γ)) y := rfl

/-- The lower multiplier moves the initial colour cut to the final colour cut. -/
theorem lower_tauW_cut :
    cR Q i γ 1 * tauW a (zero_lt_card_single_add i γ) (Multiset.card γ) =
      tauW a (zero_lt_card_single_add i γ) (Multiset.card γ) * cL Q i γ 1 := by
  rw [cL_one, cR_one_eq, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [e_mul_tauW, cP_smul_cons1]

/-- The right projection in the construction does not alter the specified multiplier. -/
theorem lowerP_factor_val (x : CornerTensor.Left (lowerFirst Q i γ)) :
    (lowerLastProj Q i γ ((x : Rb) * tauW a (zero_lt_card_single_add i γ) (Multiset.card γ)) : Rb) =
      (x : Rb) * tauW a (zero_lt_card_single_add i γ) (Multiset.card γ) := by
  change ((x : Rb) * _) * cL Q i γ 1 = _
  rw [mul_assoc, ← lower_tauW_cut, ← mul_assoc]
  exact congrArg (· * tauW a (zero_lt_card_single_add i γ) (Multiset.card γ))
    (CornerTensor.left_mem (lowerFirst Q i γ) x)

end Categorification.KLR.KLRAlgebra
