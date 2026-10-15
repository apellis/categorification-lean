/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicLowerP

/-!
# The lower-rank commuting square

For `β={i}+γ`, the actual inclusion `K₁′ → E_iK₁` appends an `i` strand
in the first factor. Its balance follows from associativity of concatenation.
Together with the actual `lowerP` and `lowerF`, it gives the square in
Kang–Kashiwara, arXiv:1102.4677v4, §5.2. The bottom map `eiP` is the
existing quotient multiplication `pMap`, transported through the canonical
representative maps and multiplied by `(-1)^|β|`: the library uses `ψ=-τ`.

`lowerP_tensor_square` is an equality on the genuine four tensor objects,
not an assumed square or a square between arbitrarily chosen coordinates.
Its quotient formula is `lowerP_square`. All map and square constructions
work over a commutative ring, including `γ=0`. Only the concluding
`bMap_lowerVertical_zero` uses the existing domain, factorization and
nonzero-factor hypotheses of the first-strand coordinates.

No kernel exhaustion, injectivity of the vertical map, snake connecting map,
bimodule inverse or proof of Theorems 5.1–5.2 is asserted here.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open scoped TensorProduct
open MulOpposite TypeA
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β" => (Si + γ)
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "Rb" => KLRAlgebra k Q β

private theorem concat_cast_right {μ μ' ν : Multiset I} (h : μ = μ')
    (u : KLRAlgebra k Q ν) (v : KLRAlgebra k Q μ) :
    concat Q ν μ' (u ⊗ₜ castKLR Q h v) =
      castKLR Q (congrArg (ν + ·) h) (concat Q ν μ (u ⊗ₜ v)) := by
  subst μ'; rfl

private theorem lower_cast_trans {μ μ' μ'' : Multiset I} (h : μ = μ') (h' : μ' = μ'')
    (u : KLRAlgebra k Q μ) : castKLR Q h' (castKLR Q h u) = castKLR Q (h.trans h') u := by
  subst μ'; subst μ''; rfl

/-- The lower action in the middle block is independent of the parenthesization. -/
theorem lower_cL_cR (r : KLRAlgebra k Q γ) :
    cL Q i β (cR Q i γ r) = cR Q i β (cL Q i γ r) := by
  unfold cL cR
  rw [concat_cast_right, ← concat_assoc, lower_cast_trans]

variable (a : I → Polynomial k)
local notation "Rl" => CycKLR k Q a β
local notation "L" => CornerTensor.Left (lowerFirst Q i γ)
local notation "N" => LowerCoefficient Q i γ a

/-- Append the final `i` strand to a lower first-colour factor. -/
def lowerVerticalFactor : L →ₗ[k] IndBimod Q Si β where
  toFun x := Graded.leftIdealProj oneConcat_idem (cL Q i β (x : Rb))
  map_add' x z := by
    apply Subtype.ext
    change cL Q i β ((x : Rb) + (z : Rb)) * _ = _
    rw [cL_add, add_mul]
    rfl
  map_smul' c x := by
    apply Subtype.ext
    change cL Q i β (c • (x : Rb)) * _ = _
    rw [cL_smul, smul_mul_assoc]
    rfl

/-- The right cut in the construction does not alter the appended representative. -/
theorem lowerVerticalFactor_val (x : L) :
    (lowerVerticalFactor Q i γ x : R) = cL Q i β (x : Rb) := by
  have hx := CornerTensor.left_mem (lowerFirst Q i γ) x
  change (x : Rb) * cR Q i γ 1 = (x : Rb) at hx
  change cL Q i β (x : Rb) * oneConcat Q Si β = _
  calc
    _ = cL Q i β ((x : Rb) * cR Q i γ 1) * oneConcat Q Si β := by rw [hx]
    _ = cL Q i β ((x : Rb) * cR Q i γ 1) := by
      rw [cL_mul, lower_cL_cR, mul_assoc]
      congr 1
      exact concat_mul_oneConcat _
    _ = cL Q i β (x : Rb) := by rw [hx]

private theorem lowerVerticalFactor_balance (x : L) (r : KLRAlgebra k Q γ) :
    lowerVerticalFactor Q i γ (op r • x) =
      ⟨(lowerVerticalFactor Q i γ x : R) * cR Q i β (cL Q i γ r),
        mul_concat_mem (lowerVerticalFactor Q i γ x) _⟩ := by
  apply Subtype.ext
  change cL Q i β ((x : Rb) * cR Q i γ r) * oneConcat Q Si β =
    (cL Q i β (x : Rb) * oneConcat Q Si β) * cR Q i β (cL Q i γ r)
  rw [cL_mul, lower_cL_cR]
  change (_ * concat Q Si β (_ ⊗ₜ _)) * _ = (_ * _) * concat Q Si β (_ ⊗ₜ _)
  simp only [mul_assoc, concat_mul_oneConcat, oneConcat_mul_concat]

/-- The actual bilinear inclusion, without a chosen coordinate isomorphism. -/
def lowerVerticalBil : L →ₗ[k] N →ₗ[k] KOneTensor Q i β a :=
  ((kOneTensorBilinear Q i β a).compl₂ (lowerCoefficientVal Q i γ a)).comp
    (lowerVerticalFactor Q i γ)

theorem lowerVerticalBil_balance (x : L) (r : KLRAlgebra k Q γ) (y : N) :
    lowerVerticalBil Q i γ a (op r • x) y = lowerVerticalBil Q i γ a x (r • y) := by
  change kOneTensorElem Q i β a (lowerVerticalFactor Q i γ (op r • x)) (y : Rl) =
    kOneTensorElem Q i β a (lowerVerticalFactor Q i γ x)
      (CycKLR.mk k Q a β (cL Q i γ r) * (y : Rl))
  rw [lowerVerticalFactor_balance]
  exact kOneTensor_balance Q i β a _ _ _

/-- The lower vertical map before the left colour cut. -/
def lowerVerticalUncut : KOnePrime Q i γ a →ₗ[k] KOneTensor Q i β a :=
  BalancedTensor.lift (lowerVerticalBil Q i γ a) (lowerVerticalBil_balance Q i γ a)

theorem lowerVerticalUncut_tmul (x : L) (y : N) :
    lowerVerticalUncut Q i γ a (BalancedTensor.tmul x y) =
      kOneTensorElem Q i β a (lowerVerticalFactor Q i γ x) (y : Rl) := rfl

/-- Appending already imposes the target's left `e(β,i)` cut. -/
theorem lowerVerticalUncut_mem (t : KOnePrime Q i γ a) :
    lowerVerticalUncut Q i γ a t ∈ Graded.idemSubspace k (KOneTensor Q i β a) (cL Q i β 1) := by
  change cL Q i β 1 • lowerVerticalUncut Q i γ a t = lowerVerticalUncut Q i γ a t
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add t u ht hu => simp only [map_add, smul_add, ht, hu]
  | tmul x y =>
    rw [lowerVerticalUncut_tmul, kOneTensor_smul_elem]
    congr 1
    apply Subtype.ext
    change cL Q i β 1 * (cL Q i β (x : Rb) * oneConcat Q Si β) = _
    rw [← mul_assoc, ← cL_mul, one_mul]
    rfl

/-- The actual source inclusion `K₁′ → E_i K₁`, represented by
`x ⊗ y ↦ (x ⊗ 1_i) ⊗ y`. -/
def lowerVertical : KOnePrime Q i γ a →ₗ[k] EIKOne Q i β a :=
  (lowerVerticalUncut Q i γ a).codRestrict _ (lowerVerticalUncut_mem Q i γ a)

/-- The quotient comparison for the actual vertical, with the actual shifted coefficient. -/
def lowerVerticalCoordinates : KOnePrime Q i γ a →ₗ[k]
    KOne Q (Si + β) a (by simp) :=
  ((tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ)).restrictScalars k).comp
    (lowerVerticalUncut Q i γ a)

theorem lowerVerticalCoordinates_tmul (x : L) (y : N) (b : Rb)
    (hy : (y : Rl) = CycKLR.mk k Q a β b) :
    lowerVerticalCoordinates Q i γ a (BalancedTensor.tmul x y) =
      Submodule.Quotient.mk (cL Q i β (x : Rb) * cR Q i β b) := by
  change tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ)
    (kOneTensorElem Q i β a (lowerVerticalFactor Q i γ x) (y : Rl)) = _
  rw [hy, tensorToKOne_elem_mk]
  congr 1
  change (cL Q i β (x : Rb) * oneConcat Q Si β) * concat Q Si β (1 ⊗ₜ b) = _
  rw [mul_assoc, oneConcat_mul_concat]
  rfl

/-- Appending preserves the lower multiplier before the final crossing. -/
theorem lower_cL_tauW :
    cL Q i β (tauW a (zero_lt_card_single_add i γ) (Multiset.card γ)) =
      cycAt a ⟨0, zero_lt_card_single_add i β⟩ *
        (tauProd (Multiset.card γ) : R) * cL Q i β 1 := by
  have hc : cL Q i β (cycAt a ⟨0, zero_lt_card_single_add i γ⟩) =
      cycAt a ⟨0, zero_lt_card_single_add i β⟩ * cL Q i β 1 :=
    (cycAt_mul_cL_one i β a (zero_lt_card_single_add i γ)).symm
  have ht : cL Q i β (tauProd (Multiset.card γ)) =
      (tauProd (Multiset.card γ) : R) * cL Q i β 1 := by
    apply cL_ψw
    intro j hj
    have := List.mem_range.mp hj
    simp
    omega
  rw [tauW, cL_mul, hc]
  change (_ * _) * cL Q i β (tauProd (Multiset.card γ)) = _
  rw [mul_assoc, ← cL_mul, one_mul, ht, ← mul_assoc]

private theorem lower_cL_mul_tauW (x : Rb) :
    cL Q i β (x * tauW a (zero_lt_card_single_add i γ) (Multiset.card γ)) *
        (ψ (Multiset.card γ) : R) =
      cL Q i β x * tauW a (zero_lt_card_single_add i β) (Multiset.card β) := by
  have hc : (cycAt a ⟨0, zero_lt_card_single_add i β⟩ * tauProd (Multiset.card γ) : R) ∈
      subR0 (Si + β) :=
    Subalgebra.mul_mem _ (by
      unfold cycAt
      exact Subalgebra.sum_mem _ fun s _ => Subalgebra.mul_mem _
        (pol_mem_subR0 _) (e_mem_subR0 s))
      (tauProd_mem_subR0 _ (by simp))
  rw [cL_mul, lower_cL_tauW, mul_assoc (cL Q i β x),
    commute_cL_one_subR0 i β hc]
  simp only [← mul_assoc]
  rw [← cL_mul, mul_one]
  simp only [tauW, show Multiset.card β = Multiset.card γ + 1 by simp,
    tauProd_succ, mul_assoc]

/-- The actual commuting square, in the canonical quotient presentations.
The bottom map is the source-normalized `(-1)^|β| pMap`; the existing `pMap`
uses positive `ψ` crossings, while both `lowerP` and `lowerF` use `τ=-ψ`. -/
theorem lowerP_square (t : KOnePrime Q i γ a) :
    lowerFCoordinates Q i γ a (lowerP Q i γ a t) =
      ((-1 : k) ^ Multiset.card β) •
        pMap a (zero_lt_card_single_add i β) (by simp) (Multiset.card β)
          (card_single_add i β).symm (lowerVerticalCoordinates Q i γ a t) := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add t u ht hu => simp only [map_add, smul_add, ht, hu]
  | tmul x y =>
    obtain ⟨b, hb⟩ := CycKLR.mk_surjective (y : Rl)
    rw [lowerP_tmul, map_smul, lowerVerticalCoordinates_tmul Q i γ a x y b hb.symm, pMap_mk]
    change ((-1 : k) ^ Multiset.card γ) •
      lowerFCoordinates Q i γ a (BalancedTensor.tmul
        (lowerLastProj Q i γ ((x : Rb) * tauW a (zero_lt_card_single_add i γ) (Multiset.card γ))) y) = _
    rw [lowerFCoordinates_tmul Q i γ a _ y b hb.symm, lowerP_factor_val, mul_neg, neg_mul,
      lower_cL_mul_tauW, Submodule.Quotient.mk_neg, smul_neg]
    have he : (Submodule.Quotient.mk
        ((cL Q i β (x : Rb) * cR Q i β b) * tauW a (zero_lt_card_single_add i β) (Multiset.card β)) :
        KZero Q (Si + β) a (zero_lt_card_single_add i β)) =
      Submodule.Quotient.mk
        ((cL Q i β (x : Rb) * tauW a (zero_lt_card_single_add i β) (Multiset.card β)) * cL Q i β b) := by
      rw [Submodule.Quotient.eq]
      have hm := Submodule.smul_mem (cycL0 a (zero_lt_card_single_add i β))
        (cL Q i β (x : Rb)) (cR_mul_tauW_sub_mem i β a b)
      simpa only [smul_eq_mul, mul_sub, mul_assoc] using hm
    rw [he, show Multiset.card β = Multiset.card γ + 1 by simp, pow_succ, mul_smul,
      neg_one_smul, smul_neg]

/-- Undo only the ambient multiset transport in the quotient presentation. -/
def lowerQuotientUncast : KZero Q (Si + β) a (zero_lt_card_single_add i β) →ₗ[k]
    KZero Q (β + Si) a (by simp) :=
  ((cycL0 a (zero_lt_card_single_add i β)).restrictScalars k).liftQ
    (((cycL0 a (by simp : 0 < Multiset.card (β + Si))).mkQ.restrictScalars k).comp
      (castKLR Q (add_comm β Si).symm).toLinearMap)
    (fun z hz => Submodule.Quotient.mk_eq_zero _ |>.2
      ((castKLR_mem_cycL0 a (add_comm β Si).symm _ _ z).2 hz)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k (cycL0 a (zero_lt_card_single_add i β))).toLinearMap

private theorem lowerQuotientUncast_cast (z : KZero Q (β + Si) a (by simp)) :
    lowerQuotientUncast Q i γ a (lowerQuotientCast Q i γ a z) = z := by
  induction z using Submodule.Quotient.induction_on with
  | _ r =>
    change Submodule.Quotient.mk (castKLR Q (add_comm β Si).symm (castKLR Q (add_comm β Si) r)) = _
    rw [castKLR_symm_castAlg]

/-- The canonical representative decoder, not a chosen coordinate inverse. -/
def lowerZeroDecode : KZero Q (Si + β) a (zero_lt_card_single_add i β) →ₗ[k]
    KZeroTensor Q i β a :=
  ((kZeroToTensor Q i β a (by simp) (zero_lt_card_single_add i γ)).restrictScalars k).comp
    (lowerQuotientUncast Q i γ a)

private theorem lowerZeroDecode_smul (r : R)
    (z : KZero Q (Si + β) a (zero_lt_card_single_add i β)) :
    lowerZeroDecode Q i γ a (r • z) =
      castKLR Q (add_comm β Si).symm r • lowerZeroDecode Q i γ a z := by
  induction z using Submodule.Quotient.induction_on with
  | _ s =>
    change kZeroToTensor Q i β a (by simp) (zero_lt_card_single_add i γ) (Submodule.Quotient.mk (castKLR Q (add_comm β Si).symm (r * s))) = _
    rw [map_mul]
    change kZeroToTensor Q i β a (by simp) (zero_lt_card_single_add i γ) (castKLR Q (add_comm β Si).symm r •
      (Submodule.Quotient.mk (castKLR Q (add_comm β Si).symm s))) = _
    rw [map_smul]
    rfl

private theorem lowerZeroDecode_lowerF (t : KZeroPrime Q i γ a) :
    lowerZeroDecode Q i γ a (lowerFCoordinates Q i γ a t) = (lowerF Q i γ a t : KZeroTensor Q i β a) := by
  change kZeroToTensor Q i β a (by simp) (zero_lt_card_single_add i γ)
    (lowerQuotientUncast Q i γ a (lowerQuotientCast Q i γ a
      (tensorToKZero Q i β a (by simp) (zero_lt_card_single_add i γ) (lowerFUncut Q i γ a t)))) = _
  rw [lowerQuotientUncast_cast, kZeroToTensor_tensorToKZero]
  rfl

/-- Existing `pMap` transported by the actual tensor/quotient multiplication maps,
with the source's `τ=-ψ` normalization. -/
def eiPUncut : EIKOne Q i β a →ₗ[k] KZeroTensor Q i β a :=
  ((-1 : k) ^ Multiset.card β) • (lowerZeroDecode Q i γ a).comp
    (((pMap a (zero_lt_card_single_add i β) (by simp) (Multiset.card β)
      (card_single_add i β).symm).restrictScalars k).comp
      (((tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ)).restrictScalars k).comp
        (Graded.idemSubspace k (KOneTensor Q i β a) (cL Q i β 1)).subtype))

/-- The transported multiplication retains the genuine left colour cut. -/
theorem eiPUncut_mem (t : EIKOne Q i β a) :
    eiPUncut Q i γ a t ∈ Graded.idemSubspace k (KZeroTensor Q i β a) (oneConcat Q β Si) := by
  change oneConcat Q β Si • (((-1 : k) ^ Multiset.card β) •
    lowerZeroDecode Q i γ a (pMap a (zero_lt_card_single_add i β) (by simp) (Multiset.card β) (card_single_add i β).symm (tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ) t))) = _
  rw [smul_comm]
  congr 1
  have hc : oneConcat Q β Si = castKLR Q (add_comm β Si).symm (cL Q i β 1) := by
    rw [cL_one_eq_cast, castKLR_symm_castAlg]
  conv_lhs => arg 1; rw [hc]
  rw [← lowerZeroDecode_smul, ← map_smul, ← map_smul]
  exact congrArg (fun z => lowerZeroDecode Q i γ a (pMap a (zero_lt_card_single_add i β) (by simp) (Multiset.card β) (card_single_add i β).symm (tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ) z))) t.2

/-- The source-normalized bottom horizontal map `P : E_iK₁ → E_iK₀`. -/
def eiP : EIKOne Q i β a →ₗ[k] EIKZero Q i β a :=
  (eiPUncut Q i γ a).codRestrict _ (eiPUncut_mem Q i γ a)

/-- The commuting square on the actual four tensor objects. -/
theorem lowerP_tensor_square (t : KOnePrime Q i γ a) :
    lowerF Q i γ a (lowerP Q i γ a t) = eiP Q i γ a (lowerVertical Q i γ a t) := by
  apply Subtype.ext
  have h := congrArg (lowerZeroDecode Q i γ a) (lowerP_square Q i γ a t)
  rw [lowerZeroDecode_lowerF, map_smul] at h
  exact h

/-- Append the last strand in the coefficient block. -/
def lowerCoefficientAppend : KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q γ →ₗ[k]
    KLRAlgebra k Q Si ⊗[k] Rb :=
  TensorProduct.map LinearMap.id (cLLinear (Q := Q) i γ)

theorem lower_cL_concat (t : KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q γ) :
    cL Q i β (concat Q Si γ t) = concat Q Si β (lowerCoefficientAppend Q i γ t) := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu => simp only [map_add, cL_add, ht, hu]
  | tmul c r =>
    change cL Q i β (concat Q Si γ (c ⊗ₜ r)) = concat Q Si β (c ⊗ₜ cL Q i γ r)
    unfold cL
    rw [concat_cast_right, ← concat_assoc, lower_cast_trans]

variable (hsym : KLRSymm Q)

private theorem bCoord_lower_shuffle (b : Fin (Multiset.card γ + 1))
    (c : KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q γ) :
    bCoord i β hsym
      (cL Q i β (ψw (descRun 0 b.val) * concat Q Si γ c)) = 0 := by
  have hb : ∀ j ∈ descRun 0 b.val, j + 1 < Multiset.card β := by
    intro j hj
    have := List.mem_range'.mp (List.mem_reverse.mp hj)
    have := b.isLt
    simp only [card_single_add]
    omega
  rw [cL_mul, cL_ψw i β _ hb, mul_assoc, ← cL_mul, one_mul, lower_cL_concat]
  rw [← firstFree_single (Q := Q) i β ⟨b.val, by have := b.isLt; simp at *⟩]
  simp only [bCoord, LinearMap.comp_apply, LinearMap.proj_apply, firstCoord_firstFree]
  apply Pi.single_eq_of_ne
  intro he
  have hv := congrArg Fin.val he
  have := b.isLt
  simp only [Fin.val_last, card_single_add] at hv
  simp only [card_single_add] at *
  omega

/-- The terminal first-strand coordinate vanishes on the actual appended lower factor. -/
theorem bCoord_lowerVerticalFactor (x : L) : bCoord i β hsym (cL Q i β (x : Rb)) = 0 := by
  have hx : (x : Rb) = firstFree i γ (firstCoord i γ hsym (x : Rb)) := by
    rw [firstFree_firstCoord]
    have hh := (CornerTensor.left_mem (lowerFirst Q i γ) x).symm
    change (x : Rb) = (x : Rb) * cR Q i γ 1 at hh
    simpa only [cR_one] using hh
  rw [hx, firstFree]
  have hl : cL Q i β (∑ b, ψw (descRun 0 b.val) *
      concat Q Si γ (firstCoord i γ hsym (x : Rb) b)) =
      ∑ b, cL Q i β (ψw (descRun 0 b.val) * concat Q Si γ (firstCoord i γ hsym (x : Rb) b)) :=
    map_sum (cLLinear (Q := Q) i β) _ _
  rw [hl, map_sum]
  simp only [bCoord_lower_shuffle Q i γ hsym, Finset.sum_const_zero]

/-- `B` annihilates the vertical image. The domain and factorization hypotheses
are those of the existing first-coordinate `bMap`, not assumptions of exactness. -/
theorem bMap_lowerVertical_zero (t : KOnePrime Q i γ a) :
    bMap i β hsym a (by simp) (zero_lt_card_single_add i γ) (lowerVerticalCoordinates Q i γ a t) = 0 := by
  induction t using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero]
  | add t u ht hu => rw [map_add, map_add, ht, hu, add_zero]
  | tmul x y =>
    obtain ⟨b, hb⟩ := CycKLR.mk_surjective (y : Rl)
    rw [lowerVerticalCoordinates_tmul Q i γ a x y b hb.symm, bMap_mk]
    have hc : bCoord i β hsym (cL Q i β (x : Rb) * cR Q i β b) = 0 := by
      change firstCoord i β hsym (cL Q i β (x : Rb) * concat Q Si β (1 ⊗ₜ b)) _ = 0
      rw [firstCoord_mul_concat]
      change bCoord i β hsym (cL Q i β (x : Rb)) * (1 ⊗ₜ b) = 0
      rw [bCoord_lowerVerticalFactor Q i γ hsym, zero_mul]
    change thetaL Q i β a (bCoord i β hsym _) = 0
    rw [hc, map_zero]

end Categorification.KLR.KLRAlgebra
