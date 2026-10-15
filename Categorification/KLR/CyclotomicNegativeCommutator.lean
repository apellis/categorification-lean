/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicPositiveCommutator

/-!
# The nonpositive cyclotomic commutator

For a present-colour block `β = {i} + γ` of nonpositive weight, the actual
crossing and the canonical dotted multiplication counits give the k-linear
isomorphism `cyclotomicNegativeCommutatorEquiv`. This is the ungraded k-linear
content of the nonpositive branch of Kang–Kashiwara, arXiv:1102.4677v4,
Theorem 5.2; the source asserts a graded bimodule isomorphism.

The counits descend through the genuine cyclotomic lower tensor. Their
restriction to the actual connecting kernel is computed from the dot
recurrence (5.14). The finite matrix is zero below its anti-diagonal and
has the unit scalar `(-1)^|β| * lamA` on that anti-diagonal, retaining the
normalization `τ = -ψ` and `eiA = (-1)^|β| • aMap`. Finite elimination over
an arbitrary coefficient module proves invertibility without a field or
root-separation assumption. The specified forward map, tensor representative
formulas, both inverse roundtrips and an inverse correction formula are proved.

The hypotheses are `KLRSymm Q` over a commutative ring `k`, unit constant
leading coefficients of the `Q_{jl}`, monic `a_j` and the Cartan-degree condition.
No global nontriviality assumption on the cyclotomic quotient is imposed, and
`γ = 0` is included. No graded, bimodule, functorial, absent-colour or full
categorical commutator assertion is made here.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra
open MulOpposite
private theorem finite_triangular_bijective {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} (f : (Fin n → M) →ₗ[R] (Fin n → M))
    (u : Rˣ) (hz : ∀ j l b, l < j → f (Pi.single j b) l = 0)
    (hd : ∀ j b, f (Pi.single j b) j = (u : R) • b) : Function.Bijective f := by
  classical
  have hprefix (v : Fin n → M) (j : Fin n) (hv : ∀ l < j, v l = 0) :
      f v j = (u : R) • v j := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · exact hd j (v j)
    · intro l _ hlj
      rcases lt_or_gt_of_ne hlj with hl | hl
      · rw [hv l hl, Pi.single_zero, map_zero, Pi.zero_apply]
      · exact hz l j (v l) hl
    · simp
  constructor
  · apply (LinearMap.ker_eq_bot).1
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    change v = 0
    have hall : ∀ m : ℕ, ∀ l : Fin n, l.val < m → v l = 0 := by
      intro m
      induction m with
      | zero => intro l hl; omega
      | succ m ih =>
        intro l hl
        have he := hprefix v l (by intro t ht; exact ih t (by omega))
        rw [hv, Pi.zero_apply] at he
        exact (u.isUnit.smul_eq_zero).1 he.symm
    exact funext fun j => hall n j j.isLt
  · intro y
    have hpartial : ∀ m : ℕ, m ≤ n → ∃ v, ∀ j : Fin n, j.val < m → f v j = y j := by
      intro m
      induction m with
      | zero => intro _; exact ⟨0, by intro j hj; omega⟩
      | succ m ih =>
        intro hm
        obtain ⟨v, hv⟩ := ih (by omega)
        let j : Fin n := ⟨m, by omega⟩
        let b : M := (↑(u⁻¹) : R) • (y j - f v j)
        refine ⟨v + Pi.single j b, ?_⟩
        intro l hl
        rw [map_add, Pi.add_apply]
        by_cases he : l = j
        · subst l
          rw [hd]
          change f v j + (u : R) • ((↑(u⁻¹) : R) • (y j - f v j)) = y j
          rw [smul_smul, Units.mul_inv, one_smul]
          abel
        · have hl' : l < j := by
            apply Fin.mk_lt_mk.mpr
            have := (Fin.ne_iff_vne l j).1 he
            dsimp [j] at this
            omega
          rw [hz j l b hl', add_zero]
          exact hv l hl'
    obtain ⟨v, hv⟩ := hpartial n le_rfl
    exact ⟨v, funext fun j => hv j j.isLt⟩

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
  (a : I → Polynomial k)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β" => (Si + γ)
local notation "Rb" => KLRAlgebra k Q β
local notation "Rl" => CycKLR k Q a β
local notation "N" => LowerCoefficient Q i γ a

/-- The canonical dotted multiplication counit on the actual cyclotomic tensor. -/
def cyclotomicDotCounit (d : ℕ) : LowerCyclotomic Q i γ a →ₗ[k] Rl :=
  BalancedTensor.lift
    (LinearMap.mk₂ k
      (fun u y => (u : Rl) * CycKLR.mk k Q a β
        ((x (Q := Q) ⟨Multiset.card γ, lastPos_lt i γ⟩ : Rb) ^ d) * (y : Rl))
      (fun x x' y => by change ((x : Rl) + (x' : Rl)) * _ * _ = _; rw [add_mul, add_mul])
      (fun c x y => by change (c • (x : Rl)) * _ * _ = _; rw [smul_mul_assoc, smul_mul_assoc])
      (fun x y y' => mul_add _ _ _)
      (fun c x y => mul_smul_comm _ _ _))
    (by
      intro u r y
      change ((u : Rl) * CycKLR.mk k Q a β (cL Q i γ r)) * _ * (y : Rl) =
        (u : Rl) * _ * (CycKLR.mk k Q a β (cL Q i γ r) * (y : Rl))
      have hc := ((commute_x_last_cL (Q := Q) i γ r).pow_left d).map (CycKLR.mk k Q a β)
      rw [mul_assoc (u : Rl), ← hc.eq]
      simp only [mul_assoc])

/-- The representative formula inserts the actual last dot between the two factors. -/
theorem cyclotomicDotCounit_tmul (d : ℕ)
    (u : CornerTensor.Left (lowerLastCyc Q i γ a)) (y : N) :
    cyclotomicDotCounit Q i γ a d (BalancedTensor.tmul u y) =
      (u : Rl) * CycKLR.mk k Q a β
        ((x ⟨Multiset.card γ, lastPos_lt i γ⟩ : Rb) ^ d) * (y : Rl) := rfl

/-- Right multiplication by the last dot on the genuine lower left ideal. -/
def lowerLeftDot (d : ℕ) : CornerTensor.Left (lowerLast Q i γ) →ₗ[k]
    CornerTensor.Left (lowerLast Q i γ) where
  toFun u := ⟨(u : Rb) * (x ⟨Multiset.card γ, lastPos_lt i γ⟩) ^ d, by
    change ((u : Rb) * _) * cL Q i γ 1 = _
    have hu : (u : Rb) * cL Q i γ 1 = u := CornerTensor.left_mem (lowerLast Q i γ) u
    rw [mul_assoc, ((commute_x_last_cL (Q := Q) i γ 1).pow_left d).eq,
      ← mul_assoc, hu]⟩
  map_add' u v := Subtype.ext (add_mul _ _ _)
  map_smul' c u := Subtype.ext (smul_mul_assoc _ _ _)

/-- The last dot acts on the first factor of the actual balanced tensor. -/
def lowerDot (d : ℕ) : KZeroPrime Q i γ a →ₗ[k] KZeroPrime Q i γ a :=
  BalancedTensor.lift
    ((BalancedTensor.mkBil k Rb (KLRAlgebra k Q γ)
      (CornerTensor.Left (lowerLast Q i γ)) N).comp (lowerLeftDot Q i γ d))
    (by
      intro u r y
      have he : lowerLeftDot Q i γ d (op r • u) = op r • lowerLeftDot Q i γ d u := by
        apply Subtype.ext
        change ((u : Rb) * cL Q i γ r) * _ = ((u : Rb) * _) * cL Q i γ r
        rw [mul_assoc, ← ((commute_x_last_cL (Q := Q) i γ r).pow_left d).eq, ← mul_assoc]
      rw [LinearMap.comp_apply, he]
      exact BalancedTensor.op_smul_tmul _ r _)

theorem lowerDot_tmul (d : ℕ) (u : CornerTensor.Left (lowerLast Q i γ)) (y : N) :
    lowerDot Q i γ a d (BalancedTensor.tmul u y) =
      BalancedTensor.tmul (lowerLeftDot Q i γ d u) y := rfl

/-- The dotted counit descends through the actual cyclotomic projection. -/
theorem cyclotomicDotCounit_proj (d : ℕ) (t : KZeroPrime Q i γ a) :
    cyclotomicDotCounit Q i γ a d (lowerCyclotomicProj Q i γ a t) =
      lowerE Q i γ a (lowerDot Q i γ a d t) := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul u y =>
    rw [lowerCyclotomicProj_tmul, cyclotomicDotCounit_tmul, lowerDot_tmul, lowerE_tmul]
    change _ = CycKLR.mk k Q a β ((u : Rb) * _) * (y : Rl)
    rw [map_mul]
    rfl

/-- Dotted multiplication annihilates the genuine lower horizontal relation. -/
theorem lowerE_lowerDot_lowerP (d : ℕ) (t : KOnePrime Q i γ a) :
    lowerE Q i γ a (lowerDot Q i γ a d (lowerP Q i γ a t)) = 0 := by
  rw [← cyclotomicDotCounit_proj, lowerCyclotomicProj_lowerP, map_zero]

variable (hsym : KLRSymm Q)
local notation "sgn" => ((-1 : k) ^ Multiset.card β)
local notation "FC" => fCoords i β a hsym (zero_lt_card_single_add i γ)
local notation "FS" => fSection i β a (zero_lt_card_single_add i γ)
local notation "EC" => eCoords i β a hsym (zero_lt_card_single_add i γ)
local notation "PS" => psiCoords i β a hsym (zero_lt_card_single_add i γ) (by simp)

/-- The actual off-diagonal lift has the signed source psi coordinates. -/
theorem lowerFCoordinates_offDiagonal (p : Polynomial Rl) :
    lowerFCoordinates Q i γ a (eiPOffDiagonal Q i γ a hsym p) =
      sgn • FS (PS p) := by
  rw [← eiZeroCoordinates_lowerF, lowerF_eiPOffDiagonal, map_sub,
    eiP_coordinates, eiBSection_coordinates, eiCSection_coordinates]
  change sgn • act0 Q i β a 1 (pLift i β a (zero_lt_card_single_add i γ) (by simp) p) -
    cSection i β a (zero_lt_card_single_add i γ) (sgn •
      aMap i β a (by simp) (zero_lt_card_single_add i γ) hsym p) = _
  rw [act0_one_pLift, pLift_decomposition i β a hsym, smul_add, map_smul, add_sub_cancel_right]

/-- Multiplication on the genuine connecting lift agrees with the signed constant correction. -/
theorem lowerE_offDiagonal (p : Polynomial Rl) :
    lowerE Q i γ a (eiPOffDiagonal Q i γ a hsym p) = sgn • EC (PS p) := by
  rw [← eCoords_lowerF Q i γ a hsym, lowerFCoordinates_offDiagonal,
    map_smul, fCoords_fSection, map_smul]

/-- The last-dot identity retains the actual lower tensor and multiplication error. -/
theorem lastDot_lowerFCoordinates (t : KZeroPrime Q i γ a) :
    lastDot0 i β a (lowerFCoordinates Q i γ a t) =
      lowerFCoordinates Q i γ a (lowerDot Q i γ a 1 t) +
        cSection i β a (zero_lt_card_single_add i γ) (Polynomial.C (lowerE Q i γ a t)) := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero, add_zero]
  | add t u ht hu => simp only [map_add, ht, hu]; abel
  | tmul u y =>
    obtain ⟨b, hb⟩ := CycKLR.mk_surjective (y : Rl)
    rw [lowerFCoordinates_tmul Q i γ a u y b hb.symm, lastDot0_mk,
      lower_crossing_last_dot, Submodule.Quotient.mk_add, lowerDot_tmul,
      lowerFCoordinates_tmul Q i γ a _ y b hb.symm]
    congr 1
    · change Submodule.Quotient.mk (_ * _ * _) =
        Submodule.Quotient.mk (cL Q i β ((u : Rb) * (x _) ^ 1) * _ * _)
      rw [pow_one]
    · rw [lowerE_tmul, ← hb, ← map_mul, ← thetaL0_tmul_one i β a,
        cSection_thetaL0, cLL_tmul_one]

/-- On the true crossing image, dot action advances the existing free coordinates. -/
theorem fCoords_lowerDot_one (t : KZeroPrime Q i γ a) :
    FC (lowerFCoordinates Q i γ a (lowerDot Q i γ a 1 t)) =
      fun b => FC (lowerFCoordinates Q i γ a t) b * Polynomial.X := by
  have he := lastDot_lowerFCoordinates Q i γ a t
  rw [← fSection_lowerF Q i γ a hsym t,
    lastDot0_fSection i β a hsym, eCoords_lowerF] at he
  have hf : FS (fun b => FC (lowerFCoordinates Q i γ a t) b * Polynomial.X) =
      lowerFCoordinates Q i γ a (lowerDot Q i γ a 1 t) := add_right_cancel he
  rw [← hf, fCoords_fSection]

theorem lowerDot_zero (t : KZeroPrime Q i γ a) : lowerDot Q i γ a 0 t = t := by
  induction t using BalancedTensor.induction_on with
  | zero => exact map_zero _
  | add t u ht hu => rw [map_add, ht, hu]
  | tmul u y =>
    rw [lowerDot_tmul]
    have he : lowerLeftDot Q i γ 0 u = u := by
      apply Subtype.ext
      change (u : Rb) * _ ^ 0 = u
      rw [pow_zero, mul_one]
    rw [he]

theorem lowerDot_succ (d : ℕ) (t : KZeroPrime Q i γ a) :
    lowerDot Q i γ a (d + 1) t = lowerDot Q i γ a 1 (lowerDot Q i γ a d t) := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul u y =>
    simp only [lowerDot_tmul]
    have he : lowerLeftDot Q i γ (d + 1) u = lowerLeftDot Q i γ 1 (lowerLeftDot Q i γ d u) := by
      apply Subtype.ext
      change (u : Rb) * _ ^ (d + 1) = ((u : Rb) * _ ^ d) * _ ^ 1
      rw [pow_succ, pow_one, mul_assoc]
    rw [he]

/-- Every power of the actual dot agrees with polynomial multiplication in the psi coordinates. -/
theorem fCoords_lowerDot_offDiagonal (d : ℕ) (p : Polynomial Rl) :
    FC (lowerFCoordinates Q i γ a (lowerDot Q i γ a d (eiPOffDiagonal Q i γ a hsym p))) =
      sgn • PS (p * Polynomial.X ^ d) := by
  induction d with
  | zero => rw [lowerDot_zero, lowerFCoordinates_offDiagonal, map_smul, fCoords_fSection,
      pow_zero, mul_one]
  | succ d ih =>
    rw [lowerDot_succ, fCoords_lowerDot_one, ih, pow_succ, ← mul_assoc, psiCoords_mul_X]
    funext b
    change (sgn • PS (p * Polynomial.X ^ d) b) * Polynomial.X =
      sgn • (PS (p * Polynomial.X ^ d) b * Polynomial.X)
    exact smul_mul_assoc sgn _ _

/-- The dotted counits on the actual connecting representative are the signed recurrence entries. -/
theorem cyclotomicDotCounit_offDiagonal (d : ℕ) (p : Polynomial Rl) :
    cyclotomicDotCounit Q i γ a d
      (lowerCyclotomicProj Q i γ a (eiPOffDiagonal Q i γ a hsym p)) =
        sgn • EC (PS (p * Polynomial.X ^ d)) := by
  rw [cyclotomicDotCounit_proj, ← eCoords_lowerF Q i γ a hsym,
    fCoords_lowerDot_offDiagonal, map_smul]

/-- The restriction is on the genuine connecting kernel, not an auxiliary family of maps. -/
theorem cyclotomicDotCounit_snakeDelta (d : ℕ)
    (p : LinearMap.ker (eiA Q i γ a hsym)) :
    cyclotomicDotCounit Q i γ a d
      (lowerPCokerEquiv Q i γ a (snakeDelta Q i γ a hsym p)) =
        sgn • EC (PS (p.val * Polynomial.X ^ d)) := by
  rw [snakeDelta_offDiagonal]
  exact cyclotomicDotCounit_offDiagonal Q i γ a hsym d p.val

/-- The recurrence identifies dotted multiplication with the constant coefficient of signed A. -/
theorem cyclotomicDotCounit_offDiagonal_coeff (d : ℕ) (p : Polynomial Rl) :
    cyclotomicDotCounit Q i γ a d
      (lowerCyclotomicProj Q i γ a (eiPOffDiagonal Q i γ a hsym p)) =
        (eiA Q i γ a hsym (p * Polynomial.X ^ (d + 1))).coeff 0 := by
  rw [cyclotomicDotCounit_offDiagonal, pow_succ, ← mul_assoc]
  change _ = (sgn • aMap i β a (by simp) (zero_lt_card_single_add i γ) hsym
    ((p * Polynomial.X ^ d) * Polynomial.X)).coeff 0
  rw [aMap_mul_X_eq, Polynomial.coeff_smul, Polynomial.coeff_add,
    Polynomial.coeff_mul_X_zero, Polynomial.coeff_C_zero, zero_add]

def cyclotomicNegativeCommutator (h : ℕ) : LowerCyclotomic Q i γ a →ₗ[k]
    MiddleCyclotomic Q i γ a × (Fin h → Rl) :=
  (cyclotomicSigma Q i γ a).prod (LinearMap.pi fun d => cyclotomicDotCounit Q i γ a d)

/-- The specified forward map is the crossing together with the canonical dotted counits. -/
theorem cyclotomicNegativeCommutator_apply (h : ℕ) (t : LowerCyclotomic Q i γ a) :
    cyclotomicNegativeCommutator Q i γ a h t =
      (cyclotomicSigma Q i γ a t, fun d : Fin h => cyclotomicDotCounit Q i γ a d t) := rfl

variable
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.RootDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) =
    -RD.pair (RD.iY i) (RD.iX j))
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX β))
local notation "Amap" => aMap i β a (by simp) (zero_lt_card_single_add i γ) hsym

include hsym hQ ha hΛ hdeg in
/-- Below the anti-diagonal the entries of the actual dotted connecting matrix vanish. -/
theorem cyclotomicDotCounit_offDiagonal_X_pow_zero (d j : ℕ) (hj : wt + (j + d + 1) < 0) :
    cyclotomicDotCounit Q i γ a d
      (lowerCyclotomicProj Q i γ a (eiPOffDiagonal Q i γ a hsym (Polynomial.X ^ j))) = 0 := by
  rw [cyclotomicDotCounit_offDiagonal_coeff, ← pow_add]
  have hz := aMap_X_pow_eq_zero_of_pair_neg i β a RD Λ hsym
    (zero_lt_card_single_add i γ) hQ ha (by simp) hΛ hdeg (j + (d + 1)) (by omega)
  change (sgn • Amap (Polynomial.X ^ (j + (d + 1)))).coeff 0 = 0
  rw [hz, smul_zero, Polynomial.coeff_zero]

include hsym hQ ha hΛ hdeg in
/-- The anti-diagonal is the determined unit scalar, with the unchanged psi normalization. -/
theorem cyclotomicDotCounit_offDiagonal_X_pow_antidiagonal (d j : ℕ)
    (hj : wt + (j + d + 1) = 0) :
    cyclotomicDotCounit Q i γ a d
      (lowerCyclotomicProj Q i γ a (eiPOffDiagonal Q i γ a hsym (Polynomial.X ^ j))) =
        (sgn * lamA Q i β) • (1 : Rl) := by
  rcases subsingleton_or_nontrivial Rl with h | h
  · exact Subsingleton.elim _ _
  · rw [cyclotomicDotCounit_offDiagonal_coeff, ← pow_add]
    obtain ⟨hm, hd⟩ := aMap_X_pow_monic_degree_of_pair_nonneg i β a RD Λ hsym
      (zero_lt_card_single_add i γ) hQ ha (by simp) hΛ hdeg (j + (d + 1)) (by omega)
    have hd0 : (Ring.inverse (lamA Q i β) • Amap (Polynomial.X ^ (j + (d + 1)))).natDegree = 0 := by omega
    have he : Ring.inverse (lamA Q i β) • Amap (Polynomial.X ^ (j + (d + 1))) = 1 :=
      Polynomial.eq_one_of_monic_natDegree_zero hm hd0
    have hv : Amap (Polynomial.X ^ (j + (d + 1))) = lamA Q i β • (1 : Polynomial Rl) := by
      have he' := congrArg (fun p : Polynomial Rl => lamA Q i β • p) he
      simpa only [smul_smul, Ring.mul_inverse_cancel _ (isUnit_lamA i β hQ), one_smul] using he'
    change (sgn • Amap (Polynomial.X ^ (j + (d + 1)))).coeff 0 = _
    rw [hv, smul_smul, Polynomial.coeff_smul, Polynomial.coeff_one_zero]

include hsym hQ ha hΛ hdeg in
theorem eiA_surjective_of_pair_nonpos (hwt : wt ≤ 0) :
    Function.Surjective (eiA Q i γ a hsym) := by
  intro q
  obtain ⟨p, hp⟩ := aMap_surjective_of_pair_nonpos i β a RD Λ hsym
    (zero_lt_card_single_add i γ) hQ ha (by simp) hΛ hdeg hwt (sgn • q)
  refine ⟨p, ?_⟩
  change sgn • Amap p = q
  rw [hp, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

include hsym hQ ha hΛ hdeg in
/-- The actual crossing is surjective at nonpositive weight. -/
theorem cyclotomicSigma_surjective_of_pair_nonpos (hwt : wt ≤ 0) :
    Function.Surjective (cyclotomicSigma Q i γ a) := by
  intro m
  obtain ⟨z, rfl⟩ := middleCyclotomicProj_surjective Q i γ a m
  obtain ⟨p, hp⟩ := eiA_surjective_of_pair_nonpos Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt
    (eiC Q i γ a hsym z)
  let u := eiCLowerProjection Q i γ a hsym z - eiPOffDiagonal Q i γ a hsym p
  refine ⟨lowerPCokerEquiv Q i γ a (Submodule.Quotient.mk u), ?_⟩
  rw [cyclotomicSigma_lowerPCoker, lowerFCoker_mk, eiPCokerEquiv_mk]
  have he : lowerF Q i γ a u = z - eiP Q i γ a (eiBSection Q i γ a p) := by
    change lowerF Q i γ a (_ - _) = _
    rw [map_sub, lowerF_eiCLowerProjection, lowerF_eiPOffDiagonal, hp]
    abel
  rw [he, map_sub, middleCyclotomicProj_eiP, sub_zero]

include hsym hQ ha hΛ hdeg in
/-- The signed polynomial kernel is exactly the finite negative-weight polynomial space. -/
theorem eiA_eq_zero_iff_degree_lt (p : Polynomial Rl) :
    eiA Q i γ a hsym p = 0 ↔ p.degree < (-wt).toNat := by
  rcases subsingleton_or_nontrivial Rl with h | h
  · have hp : p = 0 := Subsingleton.elim _ _
    simp only [hp, map_zero, Polynomial.degree_zero, true_iff]
    exact WithBot.bot_lt_coe _
  · have hs : eiA Q i γ a hsym p = 0 ↔ Amap p = 0 := by
      constructor
      · intro he
        have he' := congrArg (fun q : Polynomial Rl => sgn • q) he
        change sgn • (sgn • Amap p) = sgn • (0 : Polynomial Rl) at he'
        simpa only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, smul_zero] using he'
      · intro he
        change sgn • Amap p = 0
        rw [he, smul_zero]
    rw [hs, aMap_eq_zero_iff i β a hsym (zero_lt_card_single_add i γ) hQ ha (by simp)]
    have hd := aMonicL_degree_gap i β a RD Λ hsym hQ (ha i) hΛ hdeg
    have he : (sPoly (Q := Q) i β a).natDegree - (aMonicL Q i β a).natDegree = (-wt).toNat := by omega
    rw [he]

/-- The genuine polynomial kernel in finite coefficient coordinates. -/
def negativeKernelFinEquiv : LinearMap.ker (eiA Q i γ a hsym) ≃ₗ[k]
    (Fin (-wt).toNat → Rl) :=
  (LinearEquiv.ofEq (LinearMap.ker (eiA Q i γ a hsym))
    ((Polynomial.degreeLT Rl (-wt).toNat).restrictScalars k) (by
      ext p
      change eiA Q i γ a hsym p = 0 ↔ p ∈ Polynomial.degreeLT Rl (-wt).toNat
      rw [Polynomial.mem_degreeLT]
      exact eiA_eq_zero_iff_degree_lt Q i γ a hsym hQ ha RD Λ hΛ hdeg p)).trans
      (cyclotomicCorrectionEquiv Q i γ a (-wt).toNat)

include hQ in
/-- The actual anti-diagonal scalar is a unit of the base ring, without division hypotheses. -/
theorem isUnit_negativeCounitScalar : IsUnit (sgn * lamA Q i β) :=
  (isUnit_neg_one.pow _).mul (isUnit_lamA i β hQ)

/-- The actual recurrence is right-linear in each coefficient. -/
theorem cyclotomicDotCounit_offDiagonal_monomial (d j : ℕ) (b : Rl) :
    cyclotomicDotCounit Q i γ a d
      (lowerCyclotomicProj Q i γ a (eiPOffDiagonal Q i γ a hsym (Polynomial.monomial j b))) =
        cyclotomicDotCounit Q i γ a d
          (lowerCyclotomicProj Q i γ a (eiPOffDiagonal Q i γ a hsym (Polynomial.X ^ j))) * b := by
  rw [cyclotomicDotCounit_offDiagonal_coeff, cyclotomicDotCounit_offDiagonal_coeff]
  rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.X_pow_mul_C,
    mul_assoc, ← Polynomial.X_pow_mul_C, ← mul_assoc]
  change (sgn • Amap ((Polynomial.X ^ j * Polynomial.X ^ (d + 1)) * Polynomial.C b)).coeff 0 = _
  rw [aMap_mul_C, ← smul_mul_assoc, Polynomial.coeff_mul_C]
  rfl

/-- The finite dotted map is the restriction to the actual connecting kernel. -/
def negativeCounitMatrix : (Fin (-wt).toNat → Rl) →ₗ[k] (Fin (-wt).toNat → Rl) :=
  (LinearMap.pi fun d : Fin (-wt).toNat => cyclotomicDotCounit Q i γ a d).comp
    ((lowerPCokerEquiv Q i γ a).toLinearMap.comp
      ((snakeDelta Q i γ a hsym).comp
        (negativeKernelFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg).symm.toLinearMap))

theorem negativeCounitMatrix_single (j d : Fin (-wt).toNat) (b : Rl) :
    negativeCounitMatrix Q i γ a hsym hQ ha RD Λ hΛ hdeg (Pi.single j b) d =
      cyclotomicDotCounit Q i γ a d
        (lowerCyclotomicProj Q i γ a (eiPOffDiagonal Q i γ a hsym (Polynomial.monomial j b))) := by
  classical
  change cyclotomicDotCounit Q i γ a d (lowerPCokerEquiv Q i γ a
    (snakeDelta Q i γ a hsym ((negativeKernelFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg).symm (Pi.single j b)))) = _
  rw [snakeDelta_offDiagonal]
  change cyclotomicDotCounit Q i γ a d (lowerCyclotomicProj Q i γ a
    (eiPOffDiagonal Q i γ a hsym _)) = _
  congr 3
  change (∑ l : Fin (-wt).toNat, Polynomial.monomial l (Pi.single j b l)) = _
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro l _ hl
    rw [Pi.single_eq_of_ne hl, map_zero]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

include hQ ha hΛ hdeg in
/-- The finite matrix of canonical dotted counits on the genuine kernel is invertible. -/
theorem negativeCounitMatrix_bijective (hwt : wt ≤ 0) :
    Function.Bijective (negativeCounitMatrix Q i γ a hsym hQ ha RD Λ hΛ hdeg) := by
  classical
  let D := negativeCounitMatrix Q i γ a hsym hQ ha RD Λ hΛ hdeg
  let r : (Fin (-wt).toNat → Rl) ≃ₗ[k] (Fin (-wt).toNat → Rl) :=
    LinearEquiv.funCongrLeft k Rl (Fin.revPerm)
  have hr (v : Fin (-wt).toNat → Rl) : r v = fun j => v j.rev := rfl
  have hs (j : Fin (-wt).toNat) (b : Rl) : r (Pi.single j b) = Pi.single j.rev b := by
    funext l
    simp only [hr, Pi.single_apply]
    congr 1
    apply propext
    constructor <;> intro he <;> simpa only [Fin.rev_rev] using congrArg Fin.rev he
  obtain ⟨u, hu⟩ := isUnit_negativeCounitScalar Q i γ hQ
  have hf : Function.Bijective (D.comp r.toLinearMap) := by
    apply finite_triangular_bijective _ u
    · intro j l b hlj
      change D (r (Pi.single j b)) l = 0
      rw [hs, negativeCounitMatrix_single, cyclotomicDotCounit_offDiagonal_monomial,
        cyclotomicDotCounit_offDiagonal_X_pow_zero Q i γ a hsym hQ ha RD Λ hΛ hdeg,
        zero_mul]
      have hj := j.isLt
      simp only [Fin.val_rev]
      omega
    · intro j b
      change D (r (Pi.single j b)) j = (u : k) • b
      rw [hs, negativeCounitMatrix_single, cyclotomicDotCounit_offDiagonal_monomial,
        cyclotomicDotCounit_offDiagonal_X_pow_antidiagonal Q i γ a hsym hQ ha RD Λ hΛ hdeg]
      · rw [smul_mul_assoc, one_mul, hu]
      · have hj := j.isLt
        simp only [Fin.val_rev]
        omega
  exact (Function.Bijective.of_comp_iff D r.bijective).1 hf

/-- The connecting kernel embedded in the actual cyclotomic lower tensor. -/
def negativeConnecting : (Fin (-wt).toNat → Rl) →ₗ[k] LowerCyclotomic Q i γ a :=
  (lowerPCokerEquiv Q i γ a).toLinearMap.comp ((snakeDelta Q i γ a hsym).comp
    (negativeKernelFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg).symm.toLinearMap)

theorem cyclotomicSigma_negativeConnecting (v : Fin (-wt).toNat → Rl) :
    cyclotomicSigma Q i γ a (negativeConnecting Q i γ a hsym hQ ha RD Λ hΛ hdeg v) = 0 := by
  change cyclotomicSigma Q i γ a (lowerPCokerEquiv Q i γ a (snakeDelta Q i γ a hsym _)) = 0
  rw [cyclotomicSigma_lowerPCoker]
  have he : lowerFCoker Q i γ a (snakeDelta Q i γ a hsym
      ((negativeKernelFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg).symm v)) = 0 := by
    apply LinearMap.mem_ker.1
    rw [← range_snakeDelta Q i γ a hsym]
    exact ⟨_, rfl⟩
  exact (congrArg (eiPCokerEquiv Q i γ a) he).trans (map_zero _)

theorem range_negativeConnecting :
    LinearMap.range (negativeConnecting Q i γ a hsym hQ ha RD Λ hΛ hdeg) =
      LinearMap.ker (cyclotomicSigma Q i γ a) := by
  ext t
  constructor
  · rintro ⟨v, rfl⟩
    exact cyclotomicSigma_negativeConnecting Q i γ a hsym hQ ha RD Λ hΛ hdeg v
  · intro ht
    have he : (lowerPCokerEquiv Q i γ a).symm t ∈ LinearMap.ker (lowerFCoker Q i γ a) := by
      apply LinearMap.mem_ker.2
      apply (eiPCokerEquiv Q i γ a).injective
      rw [map_zero, ← cyclotomicSigma_lowerPCoker, LinearEquiv.apply_symm_apply]
      exact ht
    rw [← range_snakeDelta Q i γ a hsym] at he
    obtain ⟨p, hp⟩ := he
    refine ⟨negativeKernelFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg p, ?_⟩
    change lowerPCokerEquiv Q i γ a (snakeDelta Q i γ a hsym
      ((negativeKernelFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg).symm
        (negativeKernelFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg p))) = t
    rw [LinearEquiv.symm_apply_apply, hp, LinearEquiv.apply_symm_apply]

include hsym hQ ha hΛ hdeg in
/-- The actual crossing and canonical dotted counits are jointly bijective. -/
theorem cyclotomicNegativeCommutator_bijective (hwt : wt ≤ 0) :
    Function.Bijective (cyclotomicNegativeCommutator Q i γ a (-wt).toNat) := by
  let K := negativeConnecting Q i γ a hsym hQ ha RD Λ hΛ hdeg
  let D := negativeCounitMatrix Q i γ a hsym hQ ha RD Λ hΛ hdeg
  let E : LowerCyclotomic Q i γ a →ₗ[k] (Fin (-wt).toNat → Rl) :=
    LinearMap.pi fun d => cyclotomicDotCounit Q i γ a d
  have hD : Function.Bijective D := negativeCounitMatrix_bijective Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt
  have hEK (v) : E (K v) = D v := rfl
  constructor
  · apply (LinearMap.ker_eq_bot).1
    rw [Submodule.eq_bot_iff]
    intro t ht
    have ht₁ : cyclotomicSigma Q i γ a t = 0 := congrArg Prod.fst ht
    have ht₂ : E t = 0 := congrArg Prod.snd ht
    have hm : t ∈ LinearMap.range K := by
      rw [range_negativeConnecting]
      exact ht₁
    obtain ⟨v, rfl⟩ := hm
    have hv : v = 0 := hD.1 (by rw [map_zero]; exact (hEK v).symm.trans ht₂)
    rw [hv, map_zero]
  · rintro ⟨m, v⟩
    obtain ⟨t, ht⟩ := cyclotomicSigma_surjective_of_pair_nonpos Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt m
    obtain ⟨w, hw⟩ := hD.2 (v - E t)
    refine ⟨t + K w, ?_⟩
    apply Prod.ext
    · change cyclotomicSigma Q i γ a (t + K w) = m
      rw [map_add, cyclotomicSigma_negativeConnecting, add_zero, ht]
    · change E (t + K w) = v
      rw [map_add, hEK, hw]
      abel

/-- The nonpositive-weight present-colour k-linear commutator decomposition.
The forward map is precisely the actual crossing and the canonical dotted counits. -/
def cyclotomicNegativeCommutatorEquiv (hwt : wt ≤ 0) :
    LowerCyclotomic Q i γ a ≃ₗ[k] MiddleCyclotomic Q i γ a × (Fin (-wt).toNat → Rl) :=
  LinearEquiv.ofBijective (cyclotomicNegativeCommutator Q i γ a (-wt).toNat)
    (cyclotomicNegativeCommutator_bijective Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt)

theorem cyclotomicNegativeCommutatorEquiv_apply (hwt : wt ≤ 0) (t : LowerCyclotomic Q i γ a) :
    cyclotomicNegativeCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt t =
      (cyclotomicSigma Q i γ a t, fun d : Fin (-wt).toNat => cyclotomicDotCounit Q i γ a d t) := rfl

theorem cyclotomicNegativeCommutator_left_inv (hwt : wt ≤ 0) (t : LowerCyclotomic Q i γ a) :
    (cyclotomicNegativeCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm
      (cyclotomicNegativeCommutator Q i γ a (-wt).toNat t) = t :=
  (cyclotomicNegativeCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm_apply_apply t

theorem cyclotomicNegativeCommutator_right_inv (hwt : wt ≤ 0)
    (z : MiddleCyclotomic Q i γ a × (Fin (-wt).toNat → Rl)) :
    cyclotomicNegativeCommutator Q i γ a (-wt).toNat
      ((cyclotomicNegativeCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm z) = z :=
  (cyclotomicNegativeCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).apply_symm_apply z

/-- The inverse of the actual finite dotted-kernel matrix. -/
def negativeCounitMatrixEquiv (hwt : wt ≤ 0) :
    (Fin (-wt).toNat → Rl) ≃ₗ[k] (Fin (-wt).toNat → Rl) :=
  LinearEquiv.ofBijective (negativeCounitMatrix Q i γ a hsym hQ ha RD Λ hΛ hdeg)
    (negativeCounitMatrix_bijective Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt)

/-- Both components on lower tensor representatives are the prescribed crossing and dotted products. -/
theorem cyclotomicNegativeCommutatorEquiv_tmul (hwt : wt ≤ 0)
    (u : CornerTensor.Left (lowerLast Q i γ)) (y : N) (b : Rb)
    (hy : (y : Rl) = CycKLR.mk k Q a β b) :
    ((cyclotomicNegativeCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt
      (BalancedTensor.tmul (lowerLeftQuotient Q i γ a u) y)).1 : CycKLR k Q a (Si + β)) =
        CycKLR.mk k Q a (Si + β) (cL Q i β (u : Rb) * -ψ (Multiset.card γ) * cL Q i β b) ∧
    (∀ d : Fin (-wt).toNat,
      (cyclotomicNegativeCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt
        (BalancedTensor.tmul (lowerLeftQuotient Q i γ a u) y)).2 d =
          CycKLR.mk k Q a β ((u : Rb) * (x ⟨Multiset.card γ, lastPos_lt i γ⟩) ^ (d : ℕ) * b)) := by
  constructor
  · exact cyclotomicSigma_tmul Q i γ a u y b hy
  · intro d
    change cyclotomicDotCounit Q i γ a d (BalancedTensor.tmul (lowerLeftQuotient Q i γ a u) y) = _
    rw [cyclotomicDotCounit_tmul, hy, map_mul, map_mul]
    rfl

/-- The inverse can use any actual crossing lift, corrected by the finite dotted-kernel inverse.
Such a lift exists by `cyclotomicSigma_surjective_of_pair_nonpos`. -/
theorem cyclotomicNegativeCommutator_inverse_representative (hwt : wt ≤ 0)
    (m : MiddleCyclotomic Q i γ a) (v : Fin (-wt).toNat → Rl)
    (t : LowerCyclotomic Q i γ a) (ht : cyclotomicSigma Q i γ a t = m) :
    (cyclotomicNegativeCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm (m, v) =
      t + negativeConnecting Q i γ a hsym hQ ha RD Λ hΛ hdeg
        ((negativeCounitMatrixEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm
          (v - fun d : Fin (-wt).toNat => cyclotomicDotCounit Q i γ a d t)) := by
  apply (cyclotomicNegativeCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).injective
  rw [LinearEquiv.apply_symm_apply, cyclotomicNegativeCommutatorEquiv_apply]
  apply Prod.ext
  · rw [map_add, cyclotomicSigma_negativeConnecting, add_zero, ht]
  · symm
    let E : LowerCyclotomic Q i γ a →ₗ[k] (Fin (-wt).toNat → Rl) :=
      LinearMap.pi fun d => cyclotomicDotCounit Q i γ a d
    change E (t + _) = v
    rw [map_add]
    change E t + negativeCounitMatrixEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt
      ((negativeCounitMatrixEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hwt).symm (v - E t)) = v
    rw [LinearEquiv.apply_symm_apply]
    abel

end Categorification.KLR.KLRAlgebra
