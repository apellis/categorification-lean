/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicLower
import Categorification.KLR.CyclotomicBalanced

/-!
# The crossing on the genuine lower-rank source

The crossing in Kang–Kashiwara, arXiv:1102.4677v4, §5.2 is `τ_n = -ψ_{n-1}`
in the conventions of this library. The lower-rank action must commute with this
crossing on the double last-colour summand.
-/
noncomputable section
namespace Categorification.KLR.KLRAlgebra
open scoped TensorProduct
open TypeA
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β" => (Si + γ)
local notation "R" => KLRAlgebra k Q (Si + β)

private theorem doubleLast_e_commute (s : Seq γ) :
    Commute (cL Q i β (cL Q i γ (e s))) (ψ (Multiset.card γ) : R) := by
  rw [cL_e, cL_e]
  apply show ∀ t : Seq (Si + β),
    t.1 ⟨Multiset.card γ, by simp⟩ =
      t.1 ⟨Multiset.card γ + 1, by simp⟩ → Commute (e t : R) (ψ (Multiset.card γ)) from ?_
  · simp only [Seq.cast_apply]
    rw [Seq.append_apply_lt _ _ _ (by change Multiset.card γ < Multiset.card (Si + γ); simp), Seq.cast_apply,
      Seq.append_apply_ge _ _ _ (by change Multiset.card γ ≤ Multiset.card γ; rfl),
      Seq.append_apply_ge _ _ _ (by change Multiset.card (Si + γ) ≤ Multiset.card γ + 1; simp)]
    exact (Multiset.mem_singleton.1 (Seq.mem _ _)).trans
      (Multiset.mem_singleton.1 (Seq.mem _ _)).symm
  · intro t ht
    exact show (e t : R) * ψ (Multiset.card γ) = ψ (Multiset.card γ) * e t by
      rw [e_mul_ψ, sadj_smul_eq_self (by simp) ht]

/-- The actual lower-rank inclusion commutes with the final crossing; all idempotents
here lie in the two-last-strands-colour-`i` summand. -/
theorem doubleLast_commute (r : KLRAlgebra k Q γ) :
    Commute (cL Q i β (cL Q i γ r)) (ψ (Multiset.card γ) : R) := by
  have hone : Commute (cL Q i β (cL Q i γ 1)) (ψ (Multiset.card γ) : R) := by
    rw [← sum_e (k := k) (Q := Q) (ν := γ)]
    change Commute (((cLLinear (Q := Q) i β).comp (cLLinear i γ)) (∑ s : Seq γ, e s)) _
    rw [map_sum]
    exact Commute.sum_left _ _ _ (fun s _ => doubleLast_e_commute Q i γ s)
  induction r using klr_induction with
  | hadd u v hu hv => rw [cL_add, cL_add]; exact hu.add_left hv
  | hmul u v hu hv => rw [cL_mul, cL_mul]; exact hu.mul_left hv
  | hr c =>
    rw [Algebra.algebraMap_eq_smul_one, cL_smul, cL_smul]
    exact hone.smul_left c
  | he s => exact doubleLast_e_commute Q i γ s
  | hx b =>
    rw [cL_x, cL_mul, cL_x]
    have hx : Commute (x (Fin.cast (congrArg Multiset.card (add_comm β Si))
      (Seq.posL Si (Fin.cast (congrArg Multiset.card (add_comm γ Si)) (Seq.posL Si b)))) : R)
      (ψ (Multiset.card γ)) := by
      exact x_mul_ψ _ _ (by change b.val ≠ Multiset.card γ; omega)
        (by change b.val ≠ Multiset.card γ + 1; omega)
    have hunit : cL Q i β 1 * cL Q i β (cL Q i γ 1) = cL Q i β (cL Q i γ 1) := by
      rw [← cL_mul, one_mul]
    rw [mul_assoc, hunit]
    exact hx.mul_left hone
  | hψ j =>
    by_cases hj : j + 1 < Multiset.card γ
    · rw [cL_ψ i γ hj, cL_mul, cL_ψ i β (by simp; omega), mul_assoc,
        ← cL_mul, one_mul]
      exact (show Commute (ψ j : R) (ψ (Multiset.card γ)) from
        ψ_mul_ψ j (Multiset.card γ) (by omega)).mul_left hone
    · rw [ψ_eq_zero j (by omega), cL_zero, cL_zero]
      exact Commute.zero_left _

/-- Appending the final strand in the ambient algebra without changing its multiset index. -/
def lowerAppend : KLRAlgebra k Q β →ₙₐ[k] KLRAlgebra k Q (β + Si) where
  toFun x := concat Q β Si (x ⊗ₜ 1)
  map_zero' := by rw [TensorProduct.zero_tmul, map_zero]
  map_add' x y := by rw [TensorProduct.add_tmul, map_add]
  map_mul' x y := by rw [← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  map_smul' c x := by rw [← TensorProduct.smul_tmul', map_smul]; rfl

private theorem lowerAppend_commute (r : KLRAlgebra k Q γ) :
    Commute (lowerAppend Q i γ (lowerLast Q i γ r))
      (-(ψ (Multiset.card γ)) : KLRAlgebra k Q (β + Si)) := by
  apply Commute.neg_right
  change _ * _ = _ * _
  apply (castKLR Q (add_comm β Si)).injective
  rw [map_mul, map_mul, castKLR_ψ]
  change cL Q i β (cL Q i γ r) * ψ (Multiset.card γ) =
    ψ (Multiset.card γ) * cL Q i β (cL Q i γ r)
  exact (doubleLast_commute Q i γ r).eq

variable (a : I → Polynomial k)
local notation "Rb" => KLRAlgebra k Q β
local notation "Ru" => KLRAlgebra k Q (β + Si)
local notation "Rl" => CycKLR k Q a β
local notation "L" => CornerTensor.Left (lowerLast Q i γ)
local notation "N" => LowerCoefficient Q i γ a

/-- The first factor in the crossing formula, including the target's right colour cut. -/
def lowerCrossingFactor : L →ₗ[k] IndBimod Q β Si where
  toFun x := Graded.leftIdealProj oneConcat_idem
    (lowerAppend Q i γ (x : Rb) * -(ψ (Multiset.card γ)))
  map_add' x y := by
    apply Subtype.ext
    change (lowerAppend Q i γ ((x : Rb) + (y : Rb)) * -ψ (Multiset.card γ)) * _ = _
    rw [map_add, add_mul, add_mul]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    change (lowerAppend Q i γ (c • (x : Rb)) * -ψ (Multiset.card γ)) * _ = _
    rw [map_smul, smul_mul_assoc, smul_mul_assoc]
    rfl

private theorem lowerCrossingFactor_balance (x : L) (r : KLRAlgebra k Q γ) :
    lowerCrossingFactor Q i γ (MulOpposite.op r • x) =
      ⟨(lowerCrossingFactor Q i γ x : Ru) * lowerAppend Q i γ (lowerLast Q i γ r),
        mul_concat_mem (lowerCrossingFactor Q i γ x) _⟩ := by
  apply Subtype.ext
  change ((lowerAppend Q i γ ((x : Rb) * lowerLast Q i γ r) * -ψ (Multiset.card γ)) *
    oneConcat Q β Si) =
    ((lowerAppend Q i γ (x : Rb) * -ψ (Multiset.card γ)) * oneConcat Q β Si) *
      lowerAppend Q i γ (lowerLast Q i γ r)
  rw [map_mul, mul_assoc (lowerAppend Q i γ (x : Rb)),
    (lowerAppend_commute Q i γ r).eq]
  change (_ * (_ * concat Q β Si (_ ⊗ₜ 1))) * _ = (_ * _) * _ * concat Q β Si (_ ⊗ₜ 1)
  simp only [mul_assoc, concat_mul_oneConcat, oneConcat_mul_concat]

/-- The inclusion of the cut cyclotomic coefficient. -/
def lowerCoefficientVal : N →ₗ[k] Rl where
  toFun y := (y : Rl)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The prescribed crossing formula before passing through the lower balancing relation. -/
def lowerFBil : L →ₗ[k] N →ₗ[k] KZeroTensor Q i β a :=
  ((kZeroTensorBilinear Q i β a).compl₂ (lowerCoefficientVal Q i γ a)).comp
    (lowerCrossingFactor Q i γ)

/-- The crossing is balanced over `R(γ)`, with its actual concatenation actions. -/
theorem lowerFBil_balance (x : L) (r : KLRAlgebra k Q γ) (y : N) :
    lowerFBil Q i γ a (MulOpposite.op r • x) y = lowerFBil Q i γ a x (r • y) := by
  change kZeroTensorElem Q i β a (lowerCrossingFactor Q i γ (MulOpposite.op r • x)) (y : Rl) =
    kZeroTensorElem Q i β a (lowerCrossingFactor Q i γ x)
      (CycKLR.mk k Q a β (lowerLast Q i γ r) * (y : Rl))
  rw [lowerCrossingFactor_balance]
  exact kZeroTensor_balance Q i β a _ _ _

/-- The actual map `x ⊗ y ↦ x τ_n y`, with `τ_n = -ψ_{n-1}`. -/
def lowerFUncut : KZeroPrime Q i γ a →ₗ[k] KZeroTensor Q i β a :=
  BalancedTensor.lift (lowerFBil Q i γ a) (lowerFBil_balance Q i γ a)

theorem lowerFUncut_tmul (x : L) (y : N) :
    lowerFUncut Q i γ a (BalancedTensor.tmul x y) =
      kZeroTensorElem Q i β a (lowerCrossingFactor Q i γ x) (y : Rl) := rfl

/-- The crossing already lands in the source's left colour cut. -/
theorem lowerFUncut_mem (t : KZeroPrime Q i γ a) :
    lowerFUncut Q i γ a t ∈ Graded.idemSubspace k (KZeroTensor Q i β a) (oneConcat Q β Si) := by
  change oneConcat Q β Si • lowerFUncut Q i γ a t = lowerFUncut Q i γ a t
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add t u ht hu => simp only [map_add, smul_add, ht, hu]
  | tmul x y =>
    rw [lowerFUncut_tmul, kZeroTensor_smul_elem]
    congr 1
    apply Subtype.ext
    change oneConcat Q β Si * ((concat Q β Si ((x : Rb) ⊗ₜ 1) * -ψ (Multiset.card γ)) *
      oneConcat Q β Si) = _
    rw [← mul_assoc, ← mul_assoc, oneConcat_mul_concat]
    rfl

/-- The source map `F : K₀′ → E_i K₀` into the genuine left-cut tensor. -/
def lowerF : KZeroPrime Q i γ a →ₗ[k] EIKZero Q i β a :=
  (lowerFUncut Q i γ a).codRestrict _ (lowerFUncut_mem Q i γ a)

/-- The coordinate-quotient realization retains the exact crossing formula. -/
theorem lowerF_quotient_tmul (x : L) (y : N) (b : Rb)
    (hy : (y : Rl) = CycKLR.mk k Q a β b) :
    tensorToKZero Q i β a (by simp) (zero_lt_card_single_add i γ)
      (lowerF Q i γ a (BalancedTensor.tmul x y)) =
      Submodule.Quotient.mk (lowerAppend Q i γ (x : Rb) * -ψ (Multiset.card γ) *
        lowerAppend Q i γ b) := by
  change tensorToKZero Q i β a _ _
    (kZeroTensorElem Q i β a (lowerCrossingFactor Q i γ x) (y : Rl)) = _
  rw [hy, tensorToKZero_elem_mk]
  congr 1
  change ((_ * _) * oneConcat Q β Si) * concat Q β Si (b ⊗ₜ 1) = _
  rw [mul_assoc _ (oneConcat Q β Si), oneConcat_mul_concat]
  rfl

/-- Transport only the multiset index of the uncut quotient, for comparison with existing
coordinates. The cyclotomic submodule is transported, not replaced by a larger ideal. -/
def lowerQuotientCast : KZero Q (β + Si) a (by simp) →ₗ[k]
    KZero Q (Si + β) a (zero_lt_card_single_add i β) :=
  ((cycL0 a (by simp : 0 < Multiset.card (β + Si))).restrictScalars k).liftQ
    (((cycL0 a (zero_lt_card_single_add i β)).mkQ.restrictScalars k).comp
      (castKLR Q (add_comm β Si)).toLinearMap)
    (fun z hz => Submodule.Quotient.mk_eq_zero _ |>.2
      ((castKLR_mem_cycL0 a (add_comm β Si) (by simp) _ z).2 hz)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k (cycL0 a (by simp))).toLinearMap

/-- The genuine tensor map as an input to the existing `C` and free `F` coordinates. -/
def lowerFCoordinates : KZeroPrime Q i γ a →ₗ[k]
    KZero Q (Si + β) a (zero_lt_card_single_add i β) :=
  (lowerQuotientCast Q i γ a).comp
    ((tensorToKZero Q i β a (by simp) (zero_lt_card_single_add i γ)).restrictScalars k |>.comp
      (lowerFUncut Q i γ a))

/-- Compatibility is with `x τ_n y` itself, not an abstract tensor equivalence. -/
theorem lowerFCoordinates_tmul (x : L) (y : N) (b : Rb)
    (hy : (y : Rl) = CycKLR.mk k Q a β b) :
    lowerFCoordinates Q i γ a (BalancedTensor.tmul x y) =
      Submodule.Quotient.mk (cL Q i β (x : Rb) * -ψ (Multiset.card γ) * cL Q i β b) := by
  change lowerQuotientCast Q i γ a
    (tensorToKZero Q i β a _ _ (lowerF Q i γ a (BalancedTensor.tmul x y))) = _
  rw [lowerF_quotient_tmul Q i γ a x y b hy]
  change Submodule.Quotient.mk (castKLR Q (add_comm β Si)
    (lowerAppend Q i γ (x : Rb) * -(ψ (Multiset.card γ)) * lowerAppend Q i γ b)) = _
  rw [map_mul, map_mul, map_neg, castKLR_ψ]
  rfl

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ c d, c ≠ d → Q c d = P d c * MvPolynomial.rename ![1, 0] (P c d))
  (hP : ∀ c d, c ≠ d → P c d ≠ 0)

/-- The existing cokernel coordinate annihilates the actual lower-rank crossing map. -/
theorem cMap_lowerF (t : KZeroPrime Q i γ a) :
    cMap i β hPQ hP a (zero_lt_card_single_add i γ) (lowerFCoordinates Q i γ a t) = 0 := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | add t u ht hu => rw [map_add, map_add, ht, hu, add_zero]
  | tmul x y =>
    obtain ⟨b, hb⟩ := CycKLR.mk_surjective (y : Rl)
    rw [lowerFCoordinates_tmul Q i γ a x y b hb.symm]
    have hn : Multiset.card β - 1 = Multiset.card γ := by simp
    rw [mul_neg, neg_mul, Submodule.Quotient.mk_neg, map_neg]
    rw [← hn, cMap_cL_crossing i β (zero_lt_card_single_add i γ) hPQ hP a, neg_zero]

end Categorification.KLR.KLRAlgebra
