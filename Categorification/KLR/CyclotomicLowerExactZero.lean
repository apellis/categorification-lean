/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicLowerExactOne
import Categorification.KLR.CyclotomicLowerCoordinates

/-!
# The genuine lower crossing column

For `β = {i} + γ`, `lowerF_injective` and `range_lowerF_eq_ker_eiC`
identify the actual tensor `KZeroPrime` over `R(γ)` with the kernel of the
existing `C` restricted to `EIKZero`. The inverse `lowerFKernelInv` decodes
the full crossing coordinates using actual last-strand basis vectors and
projects the cyclotomic coefficient to `e(γ,i) R^Λ(β)`.

The construction realizes the crossing decomposition of Kang–Kashiwara,
arXiv:1102.4677v4, Proposition 3.3 and its application to the middle column
of the diagram in §5.2. Quotient descent is coefficientwise; source
reconstruction uses actual balancing over `R(γ)`, and target reconstruction
uses the last-colour cut identity on the crossing. The full free coordinate
space is not identified with the lower tensor without that cut.

The maps and colour identities use a commutative base ring; coordinate
extraction assumes `KLRSymm Q`. Cyclotomic polynomials are arbitrary, with no
monicity, nontrivial quotient, Cartan-degree or flatness assumption. The
case `γ = 0` tensors over the genuine algebra `R(0)`.

`lowerFKernelEquiv` is a k-linear equivalence, not the paper's graded
bimodule equivalence. The source convention `τ = -ψ`, the existing `C`,
and the source-normalized `lowerP/eiP` square are unchanged. Right-end
surjectivity, polynomial-summand decompositions, absent-colour extensions,
snake maps and the final specified bimodule inverses remain separate.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open scoped TensorProduct
open MulOpposite TypeA
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β" => (Si + γ)
local notation "Ri" => KLRAlgebra k Q Si
local notation "Rg" => KLRAlgebra k Q γ
local notation "Rb" => KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "L" => CornerTensor.Left (lowerLast Q i γ)
local notation "D" => Fin (Multiset.card β)

/-- An actual last-strand free vector in the lower right-colour corner. -/
def lowerLastBasis (d : D) : Ri →ₗ[k] L where
  toFun c := ⟨ψw (upW d.val (Multiset.card γ)) * cLL Q i γ (1 ⊗ₜ c), by
    change (_ * _) * cL Q i γ 1 = _
    rw [mul_assoc, cLL_mul_cL_one]⟩
  map_add' c c' := Subtype.ext (by
    simp only [TensorProduct.tmul_add, map_add, mul_add]; rfl)
  map_smul' s c := Subtype.ext (by
    simp only [TensorProduct.tmul_smul, map_smul, mul_smul_comm]; rfl)

/-- Appending a strand transports polynomial evaluation with its unit cut. -/
theorem lower_cL_aeval (b : Fin (Multiset.card β)) (p : Polynomial k) :
    cL Q i β (Polynomial.aeval (x b : Rb) p) =
      Polynomial.aeval (x ⟨b.val, by have := b.isLt; simp at *; omega⟩ : R) p * cL Q i β 1 := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
  change (cLLinear i β) _ = _
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_smul, smul_mul_assoc]
  exact congrArg (p.coeff d • ·) (cL_x_pow i β b d)

/-- The appended lower basis has the prescribed two-last-colour cut. -/
theorem lowerLastBasis_append (d : D) (c : Ri) :
    cL Q i β (lowerLastBasis Q i γ d c : Rb) =
      ψw (upW d.val (Multiset.card γ)) *
        Polynomial.aeval (x ⟨Multiset.card γ, by simp⟩ : R) (singlePoly Q i c) *
          cL Q i β (cL Q i γ 1) := by
  change cL Q i β (ψw _ * cLL Q i γ _) = _
  have hw : ∀ j ∈ upW d.val (Multiset.card γ), j + 1 < Multiset.card β := by
    intro j hj
    rw [upW, List.mem_range'_1] at hj
    simp only [Multiset.card_add, Multiset.card_singleton]
    omega
  rw [cL_mul, cL_ψw i β _ hw, mul_assoc, ← cL_mul, one_mul,
    cLL_one_tmul, cL_mul, lower_cL_aeval]
  rw [mul_assoc _ (cL Q i β 1), ← cL_mul, one_mul, ← mul_assoc]

variable (a : I → Polynomial k)
local notation "Rl" => CycKLR k Q a β
local notation "N" => LowerCoefficient Q i γ a

/-- Reconstruct a genuine lower tensor from a free crossing coefficient. -/
def lowerLastDecode (d : D) : Rb ⊗[k] Ri →ₗ[k] KZeroPrime Q i γ a :=
  (TensorProduct.lift
    ((((BalancedTensor.mkBil k Rb Rg L N).compl₂
      ((lowerCoefficientProj Q i γ a).comp (CycKLR.mk k Q a β).toLinearMap)).comp
      (lowerLastBasis Q i γ d)))).comp (TensorProduct.comm k Rb Ri).toLinearMap

/-- The decoder uses the actual coefficient projection and elementary tensor. -/
theorem lowerLastDecode_tmul (d : D) (b : Rb) (c : Ri) :
    lowerLastDecode Q i γ a d (b ⊗ₜ c) =
      BalancedTensor.tmul (lowerLastBasis Q i γ d c)
        (lowerCoefficientProj Q i γ a (CycKLR.mk k Q a β b)) := rfl

/-- Coefficientwise cyclotomic descent, without tensor-product exactness. -/
theorem lowerLastDecode_eq_zero (d : D) {t : Rb ⊗[k] Ri}
    (ht : t ∈ tJ0 (Q := Q) i β a) : lowerLastDecode Q i γ a d t = 0 := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨b, c, hb, rfl⟩ := ht
    rw [lowerLastDecode_tmul, (CycKLR.mk_eq_zero_iff b).2 hb, map_zero,
      BalancedTensor.tmul_zero]
  | zero => exact map_zero _
  | add t u _ _ ht hu => rw [map_add, ht, hu, add_zero]
  | smul s t _ ht => rw [map_smul, ht, smul_zero]

/-- The genuine crossing on a lower basis tensor is the negative free F term. -/
theorem lowerFCoordinates_lastBasis (d : D) (c : Ri) (y : N) (b : Rb)
    (hy : (y : Rl) = CycKLR.mk k Q a β b) :
    lowerFCoordinates Q i γ a (BalancedTensor.tmul (lowerLastBasis Q i γ d c) y) =
      -Submodule.Quotient.mk (fT Q i β d.val ((cL Q i γ 1 * b) ⊗ₜ c)) := by
  rw [lowerFCoordinates_tmul Q i γ a _ y b hy, lowerLastBasis_append,
    mul_neg, neg_mul, Submodule.Quotient.mk_neg]
  congr 2
  rw [fT_tmul, cL_mul]
  simp only [Multiset.card_add, Multiset.card_singleton, Nat.add_sub_cancel_left]
  change ψw (upW d.val (Multiset.card γ)) * _ * _ * _ * _ =
    ψw (upW d.val (Multiset.card γ)) * _ * _ * (_ * _)
  have hc := (doubleLast_commute Q i γ 1).eq
  simp only [mul_assoc]
  rw [← mul_assoc (cL Q i β (cL Q i γ 1)), hc, mul_assoc]

variable (hsym : KLRSymm Q)

/-- Decode the full F coordinates with the source crossing sign. -/
def lowerFDecodeRep : R →ₗ[k] KZeroPrime Q i γ a :=
  -∑ d : D, (lowerLastDecode Q i γ a d).comp
    ((LinearMap.proj d).comp ((LinearMap.fst k _ _).comp (kkCoord i β hsym)))

theorem lowerFDecodeRep_apply (r : R) :
    lowerFDecodeRep Q i γ a hsym r =
      -∑ d : D, lowerLastDecode Q i γ a d ((kkCoord i β hsym r).1 d) := by
  simp only [lowerFDecodeRep, LinearMap.neg_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.fst_apply]

/-- The explicit representative decoder kills the actual cyclotomic submodule. -/
theorem lowerFDecodeRep_eq_zero {r : R}
    (hr : r ∈ cycL0 a (zero_lt_card_single_add i β)) :
    lowerFDecodeRep Q i γ a hsym r = 0 := by
  have hr' : kkF i β (kkCoord i β hsym r).1 (kkCoord i β hsym r).2 ∈
      cycL0 a (zero_lt_card_single_add i β) := by
    change kkExpand i β (kkCoord i β hsym r) ∈ _
    rw [kkExpand_kkCoord]
    exact mul_mem_cycL0 a hr (cL_one_mem_subR0 i β)
  have hc := ((kkF_mem_cycL0_iff i β a hsym
    (zero_lt_card_single_add i γ) _ _).1 hr').1
  rw [lowerFDecodeRep_apply, Finset.sum_eq_zero (fun d _ =>
    lowerLastDecode_eq_zero Q i γ a d (hc d)), neg_zero]

/-- The descended decoder on the actual ambient quotient. -/
def lowerFDecode : KZero Q (Si + β) a (zero_lt_card_single_add i β) →ₗ[k]
    KZeroPrime Q i γ a :=
  ((cycL0 a (zero_lt_card_single_add i β)).restrictScalars k).liftQ
    (lowerFDecodeRep Q i γ a hsym)
    (fun _ hr => LinearMap.mem_ker.2 (lowerFDecodeRep_eq_zero Q i γ a hsym hr)) ∘ₗ
  (Submodule.Quotient.restrictScalarsEquiv k (cycL0 a _)).symm.toLinearMap

@[simp] theorem lowerFDecode_mk (r : R) :
    lowerFDecode Q i γ a hsym (Submodule.Quotient.mk r) =
      lowerFDecodeRep Q i γ a hsym r := rfl

theorem lowerFDecodeRep_fT (d : D) (t : Rb ⊗[k] Ri) :
    lowerFDecodeRep Q i γ a hsym (fT Q i β d.val t) =
      -lowerLastDecode Q i γ a d t := by
  have he : fT Q i β d.val t = kkF i β (Pi.single d t) 0 := by
    simp only [kkF, map_zero, add_zero]
    rw [Finset.sum_eq_single d]
    · rw [Pi.single_eq_same]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero]
    · exact fun h => (h (Finset.mem_univ d)).elim
  rw [he, lowerFDecodeRep_apply, kkCoord_kkF]
  change -(∑ b : D, lowerLastDecode Q i γ a b ((Pi.single d t : D → Rb ⊗[k] Ri) b)) = _
  congr 1
  rw [Finset.sum_eq_single d]
  · rw [Pi.single_eq_same]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, map_zero]
  · exact fun h => (h (Finset.mem_univ d)).elim

/-- The source roundtrip on elementary last-strand basis tensors. -/
theorem lowerFDecode_lastBasis (d : D) (c : Ri) (y : N) :
    lowerFDecode Q i γ a hsym
      (lowerFCoordinates Q i γ a (BalancedTensor.tmul (lowerLastBasis Q i γ d c) y)) =
      BalancedTensor.tmul (lowerLastBasis Q i γ d c) y := by
  obtain ⟨b, hb⟩ := CycKLR.mk_surjective (y : Rl)
  rw [lowerFCoordinates_lastBasis Q i γ a d c y b hb.symm, map_neg,
    lowerFDecode_mk, lowerFDecodeRep_fT, neg_neg, lowerLastDecode_tmul,
    map_mul, hb, show CycKLR.mk k Q a β (cL Q i γ 1) * (y : Rl) = y from y.2,
    lowerCoefficientProj_coe]

/-- A lower last-free summand with its actual right colour cut. -/
def lowerLastTerm (d : D) : Rg ⊗[k] Ri →ₗ[k] L where
  toFun t := ⟨ψw (upW d.val (Multiset.card γ)) * cLL Q i γ t, by
    change (_ * _) * cL Q i γ 1 = _
    rw [mul_assoc, cLL_mul_cL_one]⟩
  map_add' t u := Subtype.ext (by simp only [map_add, mul_add]; rfl)
  map_smul' s t := Subtype.ext (by simp only [map_smul, mul_smul_comm]; rfl)

/-- The lower coefficient moves by the actual R(γ) action. -/
theorem lowerLastTerm_tmul (d : D) (r : Rg) (c : Ri) :
    lowerLastTerm Q i γ d (r ⊗ₜ c) = op r • lowerLastBasis Q i γ d c := by
  apply Subtype.ext
  change ψw _ * cLL Q i γ (r ⊗ₜ c) =
    (ψw _ * cLL Q i γ (1 ⊗ₜ c)) * cL Q i γ r
  rw [mul_assoc, ← cLL_mul_cL, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

include hsym in
/-- The genuine lower corner is spanned by its last-free summands, also at γ=0. -/
theorem lowerLastTerm_span (x : L) : ∃ t : D → Rg ⊗[k] Ri,
    ∑ d, lowerLastTerm Q i γ d (t d) = x := by
  obtain ⟨t, ht⟩ := lastFree_span i γ hsym (x : Rb)
  have hn : Multiset.card γ + 1 = Multiset.card β := by simp
  refine ⟨fun d => t (Fin.cast hn.symm d), ?_⟩
  apply Subtype.ext
  rw [show (∑ d, lowerLastTerm Q i γ d (t (Fin.cast hn.symm d)) : L).val =
      ∑ d, (lowerLastTerm Q i γ d (t (Fin.cast hn.symm d)) : Rb) from
    map_sum (Graded.leftIdeal ((lowerLast Q i γ) 1)).subtype _ _]
  change (∑ d : D, ψw (upW d.val (Multiset.card γ)) *
    cLL Q i γ (t (Fin.cast hn.symm d))) = (x : Rb)
  have hs := Equiv.sum_comp (finCongr hn.symm)
    (fun d : Fin (Multiset.card γ + 1) =>
      (ψw (upW d.val (Multiset.card γ)) : Rb) * cLL Q i γ (t d))
  change (∑ d : D, ψw (upW d.val (Multiset.card γ)) *
    cLL Q i γ (t (Fin.cast hn.symm d))) = lastFree i γ t at hs
  rw [hs, ← ht]
  exact CornerTensor.left_mem (lowerLast Q i γ) x

/-- The decoder is a left inverse on the genuine balanced tensor K₀′. -/
theorem lowerFDecode_leftInverse (t : KZeroPrime Q i γ a) :
    lowerFDecode Q i γ a hsym (lowerFCoordinates Q i γ a t) = t := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul x y =>
    obtain ⟨p, hp⟩ := lowerLastTerm_span Q i γ hsym x
    rw [← hp]
    rw [show BalancedTensor.tmul (∑ d, lowerLastTerm Q i γ d (p d)) y =
        ∑ d, BalancedTensor.tmul (lowerLastTerm Q i γ d (p d)) y from
      map_sum ((BalancedTensor.mkBil k Rb Rg L N).flip y) _ _]
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro d _
    induction p d using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, BalancedTensor.add_tmul, hu, hv]
    | tmul r c =>
      rw [lowerLastTerm_tmul, BalancedTensor.op_smul_tmul]
      exact lowerFDecode_lastBasis Q i γ a hsym d c (r • y)

include hsym in
/-- The actual source crossing into E_i K₀ is injective. -/
theorem lowerF_injective : Function.Injective (lowerF Q i γ a) := by
  intro t u h
  have hc : lowerFCoordinates Q i γ a t = lowerFCoordinates Q i γ a u := by
    change lowerQuotientCast Q i γ a (tensorToKZero Q i β a _ _ (lowerF Q i γ a t)) =
      lowerQuotientCast Q i γ a (tensorToKZero Q i β a _ _ (lowerF Q i γ a u))
    rw [h]
  have hd := congrArg (lowerFDecode Q i γ a hsym) hc
  simpa only [lowerFDecode_leftInverse] using hd

/-- The last-colour cut across the crossing is exactly the double-last-colour cut. -/
theorem lowerLastCut_crossing :
    cL Q i β 1 * ψ (Multiset.card γ) * cL Q i β 1 =
      ψ (Multiset.card γ) * cL Q i β (cL Q i γ 1) := by
  have hsum : cL Q i γ 1 = ∑ s : Seq β, cL Q i γ 1 * e s := by
    rw [← Finset.mul_sum, sum_e, mul_one]
  have hsum' : cL Q i β (cL Q i γ 1) =
      ∑ s : Seq β, cL Q i β (cL Q i γ 1 * e s) := by
    change (cLLinear i β) _ = _
    nth_rw 1 [hsum]
    rw [map_sum]
    rfl
  rw [hsum']
  nth_rw 2 [cL_one]
  rw [Finset.mul_sum, Finset.mul_sum]
  change (∑ s : Seq β, cL Q i β 1 * ψ (Multiset.card γ) *
      e (Seq.cast (add_comm β Si) (s.append default))) =
    ∑ s : Seq β, ψ (Multiset.card γ) * cL Q i β (cL Q i γ 1 * e s)
  apply Finset.sum_congr rfl
  intro s _
  let t : Seq (Si + β) := Seq.cast (add_comm β Si) (s.append default)
  have hs : (sadj (Multiset.card (Si + β)) (Multiset.card γ) • t).1
      ⟨Multiset.card β, by simp⟩ = s.1 ⟨Multiset.card γ, by simp⟩ := by
    rw [Seq.smul_apply, ← Equiv.Perm.inv_def, sadj_inv]
    have hp : (⟨Multiset.card β, by simp⟩ : Fin (Multiset.card (Si + β))) =
        ⟨Multiset.card γ + 1, by simp⟩ := Fin.ext (by simp)
    rw [hp, sadj_apply_right (by simp)]
    simp only [t, Seq.cast_apply]
    rw [Seq.append_apply_lt _ _ _ (by change Multiset.card γ < Multiset.card β; simp)]
    congr 1
  change cL Q i β 1 * ψ (Multiset.card γ) * e t = _
  rw [mul_assoc, ψ_mul_e, ← mul_assoc, lowerLastCut_mul_e, hs,
    lowerLastCut_mul_e]
  split_ifs with h
  · rw [cL_e, ← ψ_mul_e]
  · rw [zero_mul, cL_zero, mul_zero]

/-- Left-cutting a free crossing term cuts precisely its lower coefficient. -/
theorem lowerLastCut_fT_tmul (d : D) (b : Rb) (c : Ri) :
    cL Q i β 1 * fT Q i β d.val (b ⊗ₜ c) =
      fT Q i β d.val ((cL Q i γ 1 * b) ⊗ₜ c) := by
  let w : R := ψw (upW d.val (Multiset.card β - 1)) *
    Polynomial.aeval (x ⟨Multiset.card β - 1, penPos_lt i β⟩ : R) (singlePoly Q i c)
  have hw : w ∈ subR0 (k := k) (Q := Q) (Si + β) := by
    apply Subalgebra.mul_mem _
    · exact ψw_mem_subR0 _ (fun j hj => by
        rw [upW, List.mem_range'_1] at hj
        simp only [Multiset.card_add, Multiset.card_singleton] at *
        omega)
    · rw [Polynomial.aeval_eq_sum_range]
      exact Subalgebra.sum_mem _ fun n _ =>
        Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (x_mem_subR0 _) _) _
  have hc := commute_cL_one_subR0 i β hw
  have hn : Multiset.card β - 1 = Multiset.card γ := by simp
  rw [fT_tmul, fT_tmul, cL_mul]
  change cL Q i β 1 * (w * ψ (Multiset.card β - 1) * cL Q i β b) =
    w * ψ (Multiset.card β - 1) * (cL Q i β (cL Q i γ 1) * cL Q i β b)
  rw [hn, ← mul_assoc, ← mul_assoc, ← hc]
  have he : cL Q i β b = cL Q i β 1 * cL Q i β b := by rw [← cL_mul, one_mul]
  conv_lhs => rw [he]
  simp only [← mul_assoc]
  rw [mul_assoc w (cL Q i β 1) (ψ (Multiset.card γ)),
    mul_assoc w (cL Q i β 1 * ψ (Multiset.card γ)) (cL Q i β 1),
    lowerLastCut_crossing]
  simp only [mul_assoc]

/-- Forward reconstruction is the actual left projection of each free term. -/
theorem lowerFCoordinates_decode (d : D) (t : Rb ⊗[k] Ri) :
    lowerFCoordinates Q i γ a (lowerLastDecode Q i γ a d t) =
      -Submodule.Quotient.mk (cL Q i β 1 * fT Q i β d.val t) := by
  induction t using TensorProduct.inductionOn with
  | tmul b c =>
    rw [lowerLastDecode_tmul, lowerFCoordinates_lastBasis Q i γ a d c _
      (cL Q i γ 1 * b) (by change _ * _ = _; rw [map_mul]),
      ← mul_assoc, ← cL_mul, one_mul, lowerLastCut_fT_tmul]
  | add t u ht hu =>
    rw [map_add, map_add, ht, hu, map_add, mul_add, Submodule.Quotient.mk_add, neg_add]

/-- Forward reconstruction on the quotient is the cut of the full F part. -/
theorem lowerFCoordinates_decode_eq (z : KZero Q (Si + β) a (zero_lt_card_single_add i β)) :
    lowerFCoordinates Q i γ a (lowerFDecode Q i γ a hsym z) =
      cL Q i β 1 • fSection i β a (zero_lt_card_single_add i γ)
        (fCoords i β a hsym (zero_lt_card_single_add i γ) z) := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [lowerFDecode_mk, lowerFDecodeRep_apply, map_neg, map_sum]
  simp only [lowerFCoordinates_decode, Finset.sum_neg_distrib, neg_neg]
  rw [fCoords_mk]
  change _ = cL Q i β 1 • fSection i β a (zero_lt_card_single_add i γ)
    (fun d => thetaL0 Q i β a ((kkCoord i β hsym r).1 d))
  rw [fSection_thetaL0]
  change _ = Submodule.Quotient.mk (cL Q i β 1 * kkF i β (kkCoord i β hsym r).1 0)
  rw [kkF, map_zero, add_zero, Finset.mul_sum]
  exact (map_sum (cycL0 a (zero_lt_card_single_add i β)).mkQ _ _).symm

/-- Both colour cuts and C=0 give the target roundtrip in the actual quotient. -/
theorem lowerFCoordinates_decode_kernel
    (z : KZero Q (Si + β) a (zero_lt_card_single_add i β))
    (hr : act0 Q i β a 1 z = z) (hl : cL Q i β 1 • z = z)
    (hz : cMap i β hsym a (zero_lt_card_single_add i γ) z = 0) :
    lowerFCoordinates Q i γ a (lowerFDecode Q i γ a hsym z) = z := by
  have he := fSection_add_cSection i β a hsym (zero_lt_card_single_add i γ) z
  rw [hz, map_zero, add_zero, hr] at he
  rw [lowerFCoordinates_decode_eq, he, hl]

/-- Canonical tensor-to-quotient multiplication followed only by multiset transport. -/
def eiZeroCoordinates : EIKZero Q i β a →ₗ[k]
    KZero Q (Si + β) a (zero_lt_card_single_add i β) :=
  (lowerQuotientCast Q i γ a).comp
    (((tensorToKZero Q i β a (by simp) (zero_lt_card_single_add i γ)).restrictScalars k).comp
      (Graded.idemSubspace k (KZeroTensor Q i β a) (oneConcat Q β Si)).subtype)

theorem eiZeroCoordinates_lowerF (t : KZeroPrime Q i γ a) :
    eiZeroCoordinates Q i γ a (lowerF Q i γ a t) = lowerFCoordinates Q i γ a t := rfl

/-- The existing C restricted to the genuine left-cut tensor E_i K₀. -/
def eiC : EIKZero Q i β a →ₗ[k] Polynomial Rl :=
  (cMap i β hsym a (zero_lt_card_single_add i γ)).comp (eiZeroCoordinates Q i γ a)

theorem eiC_lowerF (t : KZeroPrime Q i γ a) :
    eiC Q i γ a hsym (lowerF Q i γ a t) = 0 :=
  cMap_lowerF Q i γ a hsym t

/-- Explicit reconstruction from the actual restricted kernel into K₀′. -/
def lowerFKernelInv : LinearMap.ker (eiC Q i γ a hsym) →ₗ[k] KZeroPrime Q i γ a :=
  (lowerFDecode Q i γ a hsym).comp
    ((eiZeroCoordinates Q i γ a).comp (LinearMap.ker (eiC Q i γ a hsym)).subtype)

/-- The kernel reconstruction after the genuine crossing is the source identity. -/
theorem lowerFKernelInv_forward (t : KZeroPrime Q i γ a) :
    lowerFKernelInv Q i γ a hsym
      ⟨lowerF Q i γ a t, eiC_lowerF Q i γ a hsym t⟩ = t :=
  lowerFDecode_leftInverse Q i γ a hsym t

/-- Multiset transport does not lose information in the quotient. -/
theorem lowerQuotientCast_injective : Function.Injective (lowerQuotientCast Q i γ a) := by
  have he : Function.LeftInverse (lowerQuotientUncast Q i γ a) (lowerQuotientCast Q i γ a) := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | _ r =>
      change Submodule.Quotient.mk (castKLR Q (add_comm β Si).symm
        (castKLR Q (add_comm β Si) r)) = _
      rw [castKLR_symm_castAlg]
  exact he.injective

/-- Canonical coordinates distinguish actual left-cut tensors. -/
theorem eiZeroCoordinates_injective : Function.Injective (eiZeroCoordinates Q i γ a) := by
  intro t u h
  apply Subtype.ext
  apply (kZeroTensorEquiv Q i β a (by simp) (zero_lt_card_single_add i γ)).injective
  apply Subtype.ext
  exact lowerQuotientCast_injective Q i γ a h

theorem lowerQuotientCast_rightCut (z : KZero Q (β + Si) a (by simp)) :
    lowerQuotientCast Q i γ a (kZeroRightCut Q i β a (by simp) z) =
      act0 Q i β a 1 (lowerQuotientCast Q i γ a z) := by
  induction z using Submodule.Quotient.induction_on with
  | _ r =>
    change Submodule.Quotient.mk (castKLR Q (add_comm β Si) (r * oneConcat Q β Si)) =
      Submodule.Quotient.mk (castKLR Q (add_comm β Si) r * cL Q i β 1)
    rw [map_mul, ← cL_one_eq_cast]

theorem lowerQuotientCast_leftCut (z : KZero Q (β + Si) a (by simp)) :
    lowerQuotientCast Q i γ a (oneConcat Q β Si • z) =
      cL Q i β 1 • lowerQuotientCast Q i γ a z := by
  induction z using Submodule.Quotient.induction_on with
  | _ r =>
    change Submodule.Quotient.mk (castKLR Q (add_comm β Si) (oneConcat Q β Si * r)) =
      Submodule.Quotient.mk (cL Q i β 1 * castKLR Q (add_comm β Si) r)
    rw [map_mul, ← cL_one_eq_cast]

theorem eiZeroCoordinates_rightCut (z : EIKZero Q i β a) :
    act0 Q i β a 1 (eiZeroCoordinates Q i γ a z) = eiZeroCoordinates Q i γ a z := by
  change act0 Q i β a 1 (lowerQuotientCast Q i γ a (tensorToKZero Q i β a _ _ z)) = _
  rw [← lowerQuotientCast_rightCut, ← tensorToKZero_kZeroToTensor Q i β a
    (by simp) (zero_lt_card_single_add i γ), kZeroToTensor_tensorToKZero]
  rfl

theorem eiZeroCoordinates_leftCut (z : EIKZero Q i β a) :
    cL Q i β 1 • eiZeroCoordinates Q i γ a z = eiZeroCoordinates Q i γ a z := by
  change cL Q i β 1 • lowerQuotientCast Q i γ a (tensorToKZero Q i β a _ _ z) = _
  rw [← lowerQuotientCast_leftCut, ← map_smul]
  exact congrArg (fun t => lowerQuotientCast Q i γ a
    (tensorToKZero Q i β a (by simp) (zero_lt_card_single_add i γ) t)) z.2

/-- The actual crossing after kernel reconstruction is the target identity. -/
theorem lowerF_kernelInv (z : LinearMap.ker (eiC Q i γ a hsym)) :
    lowerF Q i γ a (lowerFKernelInv Q i γ a hsym z) = z := by
  apply eiZeroCoordinates_injective Q i γ a
  rw [eiZeroCoordinates_lowerF]
  exact lowerFCoordinates_decode_kernel Q i γ a hsym (eiZeroCoordinates Q i γ a z.val)
    (eiZeroCoordinates_rightCut Q i γ a z.val) (eiZeroCoordinates_leftCut Q i γ a z.val) z.2

/-- The genuine middle column is exact at E_i K₀. -/
theorem range_lowerF_eq_ker_eiC :
    LinearMap.range (lowerF Q i γ a) = LinearMap.ker (eiC Q i γ a hsym) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact eiC_lowerF Q i γ a hsym t
  · intro hz
    exact ⟨lowerFKernelInv Q i γ a hsym ⟨z, hz⟩,
      lowerF_kernelInv Q i γ a hsym ⟨z, hz⟩⟩

/-- The actual crossing and explicit cut-tensor decoder form a k-linear equivalence. -/
def lowerFKernelEquiv : KZeroPrime Q i γ a ≃ₗ[k] LinearMap.ker (eiC Q i γ a hsym) where
  toFun t := ⟨lowerF Q i γ a t, eiC_lowerF Q i γ a hsym t⟩
  invFun := lowerFKernelInv Q i γ a hsym
  left_inv := lowerFKernelInv_forward Q i γ a hsym
  right_inv z := Subtype.ext (lowerF_kernelInv Q i γ a hsym z)
  map_add' t u := Subtype.ext (map_add _ t u)
  map_smul' s t := Subtype.ext (map_smul _ s t)

end Categorification.KLR.KLRAlgebra
