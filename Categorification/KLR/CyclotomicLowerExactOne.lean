/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicLowerSquare
import Categorification.KLR.Crystal.Delta

/-!
# The genuine lower vertical column

For `β = {i} + γ`, `lowerVertical_injective` and
`range_lowerVertical_eq_ker_eiB` identify the actual tensor `KOnePrime` over
`R(γ)` with the kernel of the existing first-coordinate map `B` restricted
to `EIKOne`. The inverse `lowerVerticalKernelInv` uses the nonterminal
first-strand coordinates, the actual left colour projection on the
cyclotomic coefficient, and elementary tensors in `KOnePrime`.

This realizes the first-coordinate argument of Kang–Kashiwara,
arXiv:1102.4677v4, Proposition 3.7 and Corollary 3.8, on the genuine
left column of the diagram in §5.2. No tensor-product exactness is assumed:
the explicit quotient descent `lowerVerticalDecodeRep_eq_zero` and both inverse identities are
proved using the actual balancing relation. In particular, the full free
coordinate space is never identified with a lower tensor without its cut.

The colour identities and forward maps work over a commutative ring.
Coordinate extraction retains the existing domain and nonzero off-diagonal
factorization hypotheses. There are no monicity, cyclotomic nontriviality,
Cartan-degree or flatness hypotheses. The case `γ = 0` is included.
`eiB` is the existing ψ-normalized `B`, with its domain restricted by the
canonical tensor-to-quotient map. No crossing signs are changed.

The other column (`lowerF/C`), polynomial-summand decompositions, extensions
to absent-colour blocks, snake connecting maps and the final bimodule
inverses of Theorems 5.1–5.2 remain separate.
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
local notation "L" => CornerTensor.Left (lowerFirst Q i γ)
local notation "D" => Fin (Multiset.card γ + 1)

theorem lowerLastCut_mul_e (s : Seq β) :
    cL Q i γ 1 * e s = if s.1 ⟨Multiset.card γ, by simp⟩ = i then e s else 0 := by
  let h : γ + Si = β := add_comm γ Si
  let s' := Seq.cast h.symm s
  have ht : s' ∈ concatSet γ Si ↔ s.1 ⟨Multiset.card γ, by simp⟩ = i := by
    rw [mem_concatSet_iff_hasTail (fun j hj => Multiset.mem_singleton.1 hj)]
    constructor
    · intro hs
      exact hs.2 ⟨Multiset.card γ, by simp⟩ (by simp)
    · intro hs
      refine ⟨by simp, fun j hj => ?_⟩
      have hj' : j.val = Multiset.card γ := by
        have := j.isLt
        simp only [Multiset.card_add, Multiset.card_singleton] at *
        omega
      change s.1 (Fin.cast (congrArg Multiset.card h) j) = i
      rw [show Fin.cast (congrArg Multiset.card h) j = ⟨Multiset.card γ, by simp⟩ from Fin.ext hj']
      exact hs
  have he := congrArg (castKLR Q h) (eSum_mul_e (Q := Q) (concatSet γ Si) s')
  rw [map_mul, ← oneConcat, ← cL_one_eq_cast] at he
  have hs : castKLR Q h (e s') = e s := by
    rw [castKLR_e]
    congr 1
  rw [hs] at he
  split_ifs with hsi
  · rw [ite_eq_left (ht.2 hsi), hs] at he
    exact he
  · rw [ite_eq_right (fun hc => hsi (ht.1 hc)), map_zero] at he
    exact he

theorem lowerLastCut_firstCut :
    cL Q i β 1 * oneConcat Q Si β = cR Q i β (cL Q i γ 1) := by
  have hr : cR Q i β (cL Q i γ 1) =
      ∑ s : Seq β, cR Q i β (cL Q i γ 1 * e s) := by
    change (lowerFirst Q i β) _ = ∑ s : Seq β, (lowerFirst Q i β) _
    rw [← map_sum, ← Finset.mul_sum, sum_e, mul_one]
  rw [hr, ← cR_one, cR_one_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hl : (cons1 i β s).1 ⟨Multiset.card β, by simp⟩ =
      s.1 ⟨Multiset.card γ, by simp⟩ := by
    simpa only [card_single_add, Nat.add_comm 1] using
      cons1_succ i β s (Multiset.card γ) (by simp)
  rw [lowerLastCut_mul_e, lowerLastCut_mul_e, hl]
  split_ifs
  · exact (cR_e i β s).symm
  · exact (cR_zero i β).symm

theorem lowerLastCut_concat (c : Ri) (b : Rb) :
    cL Q i β 1 * concat Q Si β (c ⊗ₜ b) =
      concat Q Si β (c ⊗ₜ (cL Q i γ 1 * b)) := by
  calc
    _ = (cL Q i β 1 * oneConcat Q Si β) * concat Q Si β (c ⊗ₜ b) := by
      rw [mul_assoc, oneConcat_mul_concat]
    _ = _ := by
      rw [lowerLastCut_firstCut]
      change concat Q Si β (1 ⊗ₜ cL Q i γ 1) * concat Q Si β (c ⊗ₜ b) = _
      rw [← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- A first-strand basis vector with its genuine right colour cut. -/
def lowerFirstBasis (d : D) : Ri →ₗ[k] L where
  toFun c := ⟨ψw (descRun 0 d.val) * concat Q Si γ (c ⊗ₜ 1), by
    change (_ * _) * cR Q i γ 1 = _
    rw [cR_one, mul_assoc, concat_mul_oneConcat]⟩
  map_add' c c' := Subtype.ext (by
    simp only [TensorProduct.add_tmul, map_add, mul_add]; rfl)
  map_smul' s c := Subtype.ext (by
    simp only [← TensorProduct.smul_tmul', map_smul, mul_smul_comm]; rfl)

variable (a : I → Polynomial k)
local notation "Rl" => CycKLR k Q a β
local notation "N" => LowerCoefficient Q i γ a

/-- Projection to the actual coefficient `e(γ,i) R^Λ(β)`. -/
def lowerCoefficientProj : Rl →ₗ[k] N where
  toFun y := ⟨CycKLR.mk k Q a β (cL Q i γ 1) * y, by
    change CycKLR.mk k Q a β (cL Q i γ 1) * (CycKLR.mk k Q a β (cL Q i γ 1) * y) = _
    rw [← mul_assoc, ← map_mul, ← cL_mul, one_mul]⟩
  map_add' y z := Subtype.ext (mul_add _ _ _)
  map_smul' s y := Subtype.ext (mul_smul_comm _ _ _)

theorem lowerCoefficientProj_coe (y : N) : lowerCoefficientProj Q i γ a (y : Rl) = y :=
  Subtype.ext y.2

/-- Reconstruct one lower summand from a first-strand tensor coefficient. -/
def lowerFirstDecode (d : D) : Ri ⊗[k] Rb →ₗ[k] KOnePrime Q i γ a :=
  TensorProduct.lift
    ((((BalancedTensor.mkBil k Rb Rg L N).compl₂
      ((lowerCoefficientProj Q i γ a).comp (CycKLR.mk k Q a β).toLinearMap)).comp
      (lowerFirstBasis Q i γ d)))

theorem lowerFirstDecode_tmul (d : D) (c : Ri) (b : Rb) :
    lowerFirstDecode Q i γ a d (c ⊗ₜ b) =
      BalancedTensor.tmul (lowerFirstBasis Q i γ d c)
        (lowerCoefficientProj Q i γ a (CycKLR.mk k Q a β b)) := rfl

theorem lowerFirstDecode_eq_zero (d : D) {t : Ri ⊗[k] Rb}
    (ht : t ∈ tJ (Q := Q) i β a) : lowerFirstDecode Q i γ a d t = 0 := by
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨c, b, hb, rfl⟩ := ht
    rw [lowerFirstDecode_tmul, (CycKLR.mk_eq_zero_iff b).2 hb, map_zero,
      BalancedTensor.tmul_zero]
  | zero => exact map_zero _
  | add t u _ _ ht hu => rw [map_add, ht, hu, add_zero]
  | smul s t _ ht => rw [map_smul, ht, smul_zero]

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ j l, j ≠ l → Q j l = P l j * MvPolynomial.rename ![1, 0] (P j l))
  (hP : ∀ j l, j ≠ l → P j l ≠ 0)

/-- Reconstruct the lower tensor from the nonterminal first-strand coordinates. -/
def lowerVerticalDecodeRep : R →ₗ[k] KOnePrime Q i γ a :=
  ∑ d : D, (lowerFirstDecode Q i γ a d).comp
    ((LinearMap.proj ⟨d.val, by have := d.isLt; simp at *⟩).comp
      (firstCoord i β hPQ hP))

theorem lowerVerticalDecodeRep_apply (r : R) :
    lowerVerticalDecodeRep Q i γ a hPQ hP r =
      ∑ d : D, lowerFirstDecode Q i γ a d
        (firstCoord i β hPQ hP r ⟨d.val, by have := d.isLt; simp at *⟩) := by
  simp only [lowerVerticalDecodeRep, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

theorem lowerVerticalDecodeRep_eq_zero {r : R} (hr : r ∈ cycL1 a (by simp)) :
    lowerVerticalDecodeRep Q i γ a hPQ hP r = 0 := by
  have hc : ∀ d, firstCoord i β hPQ hP r d ∈ tJ (Q := Q) i β a := by
    apply (firstFree_mem_cycL1_iff i β hPQ hP a (by simp)
      (zero_lt_card_single_add i γ) _).1
    rw [firstFree_firstCoord]
    exact mul_mem_cycL1 a hr (oneConcat_mem_subR1 i β)
  rw [lowerVerticalDecodeRep_apply]
  exact Finset.sum_eq_zero (fun d _ => lowerFirstDecode_eq_zero Q i γ a d (hc _))

/-- A map out of the actual cyclotomic quotient, not a chosen inverse. -/
def lowerVerticalDecode : KOne Q (Si + β) a (by simp) →ₗ[k] KOnePrime Q i γ a :=
  ((cycL1 a (by simp)).restrictScalars k).liftQ
    (lowerVerticalDecodeRep Q i γ a hPQ hP)
    (fun _ hr => LinearMap.mem_ker.2 (lowerVerticalDecodeRep_eq_zero Q i γ a hPQ hP hr)) ∘ₗ
  (Submodule.Quotient.restrictScalarsEquiv k (cycL1 a (by simp))).symm.toLinearMap

@[simp] theorem lowerVerticalDecode_mk (r : R) :
    lowerVerticalDecode Q i γ a hPQ hP (Submodule.Quotient.mk r) =
      lowerVerticalDecodeRep Q i γ a hPQ hP r := rfl

theorem lowerVerticalDecodeRep_single (d : D) (t : Ri ⊗[k] Rb) :
    lowerVerticalDecodeRep Q i γ a hPQ hP
      (ψw (descRun 0 d.val) * concat Q Si β t) = lowerFirstDecode Q i γ a d t := by
  let d' : Fin (Multiset.card β + 1) := ⟨d.val, by have := d.isLt; simp at *⟩
  rw [← firstFree_single (Q := Q) i β d' t, lowerVerticalDecodeRep_apply,
    firstCoord_firstFree]
  rw [Finset.sum_eq_single d]
  · rw [Pi.single_eq_same]
  · intro e _ he
    rw [Pi.single_eq_of_ne, map_zero]
    intro h
    have hv := congrArg (fun z : Fin (Multiset.card β + 1) => z.val) h
    exact he (Fin.ext hv)
  · simp

omit hPQ hP [IsDomain k] in
theorem lowerVerticalCoordinates_firstBasis (d : D) (c : Ri) (y : N) (b : Rb)
    (hb : (y : Rl) = CycKLR.mk k Q a β b) :
    lowerVerticalCoordinates Q i γ a (BalancedTensor.tmul (lowerFirstBasis Q i γ d c) y) =
      Submodule.Quotient.mk (ψw (descRun 0 d.val) *
        concat Q Si β (c ⊗ₜ (cL Q i γ 1 * b))) := by
  rw [lowerVerticalCoordinates_tmul Q i γ a _ y b hb]
  congr 1
  change cL Q i β (ψw (descRun 0 d.val) * concat Q Si γ (c ⊗ₜ 1)) * cR Q i β b = _
  have hd : ∀ j ∈ descRun 0 d.val, j + 1 < Multiset.card β := by
    intro j hj
    have := List.mem_range'.mp (List.mem_reverse.mp hj)
    have := d.isLt
    simp only [card_single_add]
    omega
  rw [cL_mul, cL_ψw i β _ hd, mul_assoc (ψw _) (cL Q i β 1), ← cL_mul, one_mul, lower_cL_concat]
  change (ψw _ * concat Q Si β (c ⊗ₜ cL Q i γ 1)) * concat Q Si β (1 ⊗ₜ b) = _
  rw [mul_assoc, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem lowerVerticalDecode_firstBasis (d : D) (c : Ri) (y : N) :
    lowerVerticalDecode Q i γ a hPQ hP
      (lowerVerticalCoordinates Q i γ a (BalancedTensor.tmul (lowerFirstBasis Q i γ d c) y)) =
      BalancedTensor.tmul (lowerFirstBasis Q i γ d c) y := by
  obtain ⟨b, hb⟩ := CycKLR.mk_surjective (y : Rl)
  rw [lowerVerticalCoordinates_firstBasis Q i γ a d c y b hb.symm,
    lowerVerticalDecode_mk, lowerVerticalDecodeRep_single, lowerFirstDecode_tmul]
  congr 1
  rw [map_mul, hb]
  change lowerCoefficientProj Q i γ a (lowerCoefficientProj Q i γ a (y : Rl) : Rl) = y
  rw [lowerCoefficientProj_coe, lowerCoefficientProj_coe]

omit a hPQ hP [IsDomain k] in
/-- The actual lower first-strand summand, retaining its colour cut. -/
def lowerFirstTerm (d : D) : Ri ⊗[k] Rg →ₗ[k] L where
  toFun t := ⟨ψw (descRun 0 d.val) * concat Q Si γ t, by
    change (_ * _) * cR Q i γ 1 = _
    rw [cR_one, mul_assoc, concat_mul_oneConcat]⟩
  map_add' t u := Subtype.ext (by
    change ψw _ * concat Q Si γ (t + u) = _ + _
    rw [map_add, mul_add])
  map_smul' s t := Subtype.ext (by
    change ψw _ * concat Q Si γ (s • t) = s • _
    rw [map_smul, mul_smul_comm])

omit a hPQ hP [IsDomain k] in
theorem lowerFirstTerm_tmul (d : D) (c : Ri) (r : Rg) :
    lowerFirstTerm Q i γ d (c ⊗ₜ r) = op r • lowerFirstBasis Q i γ d c := by
  apply Subtype.ext
  change ψw _ * concat Q Si γ (c ⊗ₜ r) =
    (ψw _ * concat Q Si γ (c ⊗ₜ 1)) * concat Q Si γ (1 ⊗ₜ r)
  rw [mul_assoc, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

omit a in
theorem lowerFirstTerm_sum (x : L) :
    ∑ d : D, lowerFirstTerm Q i γ d (firstCoord i γ hPQ hP (x : Rb) d) = x := by
  apply Subtype.ext
  rw [show (∑ d : D, lowerFirstTerm Q i γ d (firstCoord i γ hPQ hP (x : Rb) d) : L).val =
      ∑ d : D, (lowerFirstTerm Q i γ d (firstCoord i γ hPQ hP (x : Rb) d) : Rb) from
    map_sum (Graded.leftIdeal ((lowerFirst Q i γ) 1)).subtype _ _]
  change firstFree i γ (firstCoord i γ hPQ hP (x : Rb)) = (x : Rb)
  rw [firstFree_firstCoord]
  have hx := CornerTensor.left_mem (lowerFirst Q i γ) x
  change (x : Rb) * cR Q i γ 1 = x at hx
  simpa only [cR_one] using hx

/-- The explicit quotient reconstruction is a left inverse of the actual vertical. -/
theorem lowerVerticalDecode_leftInverse (t : KOnePrime Q i γ a) :
    lowerVerticalDecode Q i γ a hPQ hP (lowerVerticalCoordinates Q i γ a t) = t := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul x y =>
    have hs := lowerFirstTerm_sum Q i γ hPQ hP x
    conv_rhs => rw [← hs]
    conv_lhs => rw [← hs]
    rw [show (BalancedTensor.tmul (∑ d : D, lowerFirstTerm Q i γ d
        (firstCoord i γ hPQ hP (x : Rb) d)) y : KOnePrime Q i γ a) =
        ∑ d : D, BalancedTensor.tmul (lowerFirstTerm Q i γ d
          (firstCoord i γ hPQ hP (x : Rb) d)) y from
      map_sum ((BalancedTensor.mkBil k Rb Rg L N).flip y) _ _]
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro d _
    generalize firstCoord i γ hPQ hP (x : Rb) d = v
    induction v using TensorProduct.inductionOn with
    | add v w hv hw =>
      simp only [map_add, BalancedTensor.add_tmul, hv, hw]
    | tmul c r =>
      rw [lowerFirstTerm_tmul, BalancedTensor.op_smul_tmul]
      exact lowerVerticalDecode_firstBasis Q i γ a hPQ hP d c (r • y)

include hPQ hP in
/-- Injectivity is proved in the genuine balanced source, not assumed from free coordinates. -/
theorem lowerVertical_injective : Function.Injective (lowerVertical Q i γ a) := by
  intro t u h
  have hc : lowerVerticalCoordinates Q i γ a t = lowerVerticalCoordinates Q i γ a u :=
    congrArg (fun z : EIKOne Q i β a =>
      tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ) z) h
  have hd := congrArg (lowerVerticalDecode Q i γ a hPQ hP) hc
  simpa only [lowerVerticalDecode_leftInverse] using hd

omit hPQ hP [IsDomain k] in
/-- Forward reconstruction is the actual left colour projection on each lower summand. -/
theorem lowerVerticalCoordinates_decode (d : D) (t : Ri ⊗[k] Rb) :
    lowerVerticalCoordinates Q i γ a (lowerFirstDecode Q i γ a d t) =
      Submodule.Quotient.mk (cL Q i β 1 * (ψw (descRun 0 d.val) * concat Q Si β t)) := by
  induction t using TensorProduct.inductionOn with
  | add t u ht hu =>
    simp only [map_add, mul_add, Submodule.Quotient.mk_add, ht, hu]
  | tmul c b =>
    rw [lowerFirstDecode_tmul, lowerVerticalCoordinates_firstBasis Q i γ a d c _
      (cL Q i γ 1 * b) (by change _ * _ = _; rw [map_mul])]
    congr 1
    rw [← mul_assoc (cL Q i γ 1), ← cL_mul, one_mul]
    have hc : (ψw (descRun 0 d.val) : R) * cL Q i β 1 =
        cL Q i β 1 * ψw (descRun 0 d.val) := by
      apply commute_cL_one_subR0
      apply ψw_mem_subR0
      intro j hj
      have := List.mem_range'.mp (List.mem_reverse.mp hj)
      have := d.isLt
      simp only [card_single_add]
      omega
    rw [← mul_assoc, ← hc, mul_assoc, lowerLastCut_concat]

omit [DecidableEq I] in
private theorem sum_firstLower {A : Type*} [AddCommMonoid A]
    (f : Fin (Multiset.card β + 1) → A) :
    ∑ d, f d = (∑ d : D, f ⟨d.val, by have := d.isLt; simp at *⟩) +
      f (Fin.last (Multiset.card β)) := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  exact Fintype.sum_equiv (finCongr (by simp : Multiset.card β = Multiset.card γ + 1))
    _ _ (fun d => rfl)

/-- The reconstruction exhausts the kernel on the correctly left-cut quotient. -/
theorem lowerVerticalCoordinates_decode_kernel
    (z : KOne Q (Si + β) a (by simp))
    (hr : kOneRightCut Q i β a (by simp) z = z)
    (hl : cL Q i β 1 • z = z)
    (hz : bMap i β hPQ hP a (by simp) (zero_lt_card_single_add i γ) z = 0) :
    lowerVerticalCoordinates Q i γ a (lowerVerticalDecode Q i γ a hPQ hP z) = z := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨t, ht, he⟩ := (bMap_mk_eq_zero_iff i β hPQ hP a (by simp)
    (zero_lt_card_single_add i γ) r).1 hz
  have heq : (Submodule.Quotient.mk (firstFree i β t) : KOne Q (Si + β) a (by simp)) =
      Submodule.Quotient.mk r := by
    have hh : (Submodule.Quotient.mk (r * oneConcat Q Si β) : KOne Q (Si + β) a (by simp)) =
        Submodule.Quotient.mk (firstFree i β t) := (Submodule.Quotient.eq _).2 he
    exact hh.symm.trans hr
  rw [← heq, lowerVerticalDecode_mk, lowerVerticalDecodeRep_apply, firstCoord_firstFree, map_sum]
  simp only [lowerVerticalCoordinates_decode]
  have hsum : (∑ d : D, (ψw (descRun 0 d.val) : R) * concat Q Si β
      (t ⟨d.val, by have := d.isLt; simp at *⟩)) = firstFree i β t := by
    rw [firstFree, sum_firstLower i γ]
    simp only [ht, map_zero, mul_zero, add_zero]
  have hh : (∑ d : D, (Submodule.Quotient.mk
      (cL Q i β 1 * (ψw (descRun 0 d.val) * concat Q Si β
        (t ⟨d.val, by have := d.isLt; simp at *⟩))) : KOne Q (Si + β) a (by simp))) =
      cL Q i β 1 • (Submodule.Quotient.mk (firstFree i β t) : KOne Q (Si + β) a (by simp)) := by
    rw [← hsum]
    change _ = Submodule.Quotient.mk (cL Q i β 1 * _)
    rw [Finset.mul_sum]
    exact (map_sum (cycL1 a (by simp)).mkQ _ _).symm
  rw [hh, heq]
  exact hl

/-- The existing `B` restricted to the genuine left-cut tensor. -/
def eiB : EIKOne Q i β a →ₗ[k] Polynomial Rl :=
  (bMap i β hPQ hP a (by simp) (zero_lt_card_single_add i γ)).comp
    (((tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ)).restrictScalars k).comp
      (Graded.idemSubspace k (KOneTensor Q i β a) (cL Q i β 1)).subtype)

/-- An explicit map from the actual kernel into the lower-rank tensor over `R(γ)`. -/
def lowerVerticalKernelInv : LinearMap.ker (eiB Q i γ a hPQ hP) →ₗ[k] KOnePrime Q i γ a :=
  (lowerVerticalDecode Q i γ a hPQ hP).comp
    (((tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ)).restrictScalars k).comp
      ((Graded.idemSubspace k (KOneTensor Q i β a) (cL Q i β 1)).subtype.comp
        (LinearMap.ker (eiB Q i γ a hPQ hP)).subtype))

/-- The explicit kernel reconstruction, followed by the genuine vertical, is the identity. -/
theorem lowerVertical_kernelInv (z : LinearMap.ker (eiB Q i γ a hPQ hP)) :
    lowerVertical Q i γ a (lowerVerticalKernelInv Q i γ a hPQ hP z) = z := by
  apply Subtype.ext
  apply (kOneTensorEquiv Q i β a (by simp) (zero_lt_card_single_add i γ)).injective
  apply Subtype.ext
  change lowerVerticalCoordinates Q i γ a
    (lowerVerticalDecode Q i γ a hPQ hP
      (tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ) z.val.val)) = _
  apply lowerVerticalCoordinates_decode_kernel Q i γ a hPQ hP
  · rw [← tensorToKOne_kOneToTensor Q i β a (by simp) (zero_lt_card_single_add i γ),
      kOneToTensor_tensorToKOne]
  · rw [← map_smul]
    exact congrArg (tensorToKOne Q i β a (by simp) (zero_lt_card_single_add i γ)) z.val.2
  · exact z.2

theorem eiB_lowerVertical (t : KOnePrime Q i γ a) :
    eiB Q i γ a hPQ hP (lowerVertical Q i γ a t) = 0 :=
  bMap_lowerVertical_zero Q i γ a hPQ hP t

/-- The backward-forward identity also holds in the genuine lower-rank tensor. -/
theorem lowerVerticalKernelInv_forward (t : KOnePrime Q i γ a) :
    lowerVerticalKernelInv Q i γ a hPQ hP
      ⟨lowerVertical Q i γ a t, eiB_lowerVertical Q i γ a hPQ hP t⟩ = t :=
  lowerVerticalDecode_leftInverse Q i γ a hPQ hP t

/-- The genuine left column in the source diagram is exact at `E_i K₁`. -/
theorem range_lowerVertical_eq_ker_eiB :
    LinearMap.range (lowerVertical Q i γ a) = LinearMap.ker (eiB Q i γ a hPQ hP) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact eiB_lowerVertical Q i γ a hPQ hP t
  · intro hz
    exact ⟨lowerVerticalKernelInv Q i γ a hPQ hP ⟨z, hz⟩,
      lowerVertical_kernelInv Q i γ a hPQ hP ⟨z, hz⟩⟩

/-- The actual vertical, with the explicit cut-tensor reconstruction as its inverse. -/
def lowerVerticalKernelEquiv :
    KOnePrime Q i γ a ≃ₗ[k] LinearMap.ker (eiB Q i γ a hPQ hP) where
  toFun t := ⟨lowerVertical Q i γ a t, eiB_lowerVertical Q i γ a hPQ hP t⟩
  invFun := lowerVerticalKernelInv Q i γ a hPQ hP
  left_inv := lowerVerticalKernelInv_forward Q i γ a hPQ hP
  right_inv z := Subtype.ext (lowerVertical_kernelInv Q i γ a hPQ hP z)
  map_add' t u := Subtype.ext (map_add _ t u)
  map_smul' s t := Subtype.ext (map_smul _ s t)

end Categorification.KLR.KLRAlgebra
