/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAbsentColour
import Categorification.KLR.CyclotomicLowerExactOne

/-!
# The absent-colour polynomial cokernel and finite dot-unit equivalence

For `i ∉ β`, the two-cut `K₀` has inverse coordinates `C` and `cSection`:
the lower crossing coordinates vanish after the last-colour cut. The general
identity `AB = CP` and `range P = ker π` identify the cyclotomic corner with
`coker A`, without introducing a lower object with a negative multiplicity.
Polynomial triangularity then proves bijectivity of the prescribed finite
dot-unit sum. Both outer actions are the quotient multiplications.

This is the absent-colour case of Kang–Kashiwara, arXiv:1102.4677v4, §5.2.
The base ring `k` is any commutative ring and `Q` satisfies `KLRSymm Q`; the
bijectivity statements also assume unit constant leading coefficients of the
`Q_{ij}`, monic `a_i` and the Cartan-degree condition. No nontriviality
assumption is made on any cyclotomic quotient.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour
open scoped TensorProduct
open TypeA
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (β : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "Rb" => KLRAlgebra k Q β
local notation "Ri" => KLRAlgebra k Q Si

theorem cut_crossing_zero (hi : i ∉ β) (hβ : 0 < Multiset.card β) :
    cL Q i β 1 * ψ (Multiset.card β - 1) * cL Q i β 1 = (0 : R) := by
  nth_rw 2 [cL_one]
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro s _
  let t : Seq (Si + β) := Seq.cast (add_comm β Si) (s.append default)
  have hs : (sadj (Multiset.card (Si + β)) (Multiset.card β - 1) • t).1
      ⟨Multiset.card β, by simp⟩ = s.1 ⟨Multiset.card β - 1, by omega⟩ := by
    rw [Seq.smul_apply, ← Equiv.Perm.inv_def, sadj_inv]
    have hp : (⟨Multiset.card β, by simp⟩ : Fin (Multiset.card (Si + β))) =
        ⟨(Multiset.card β - 1) + 1, by simp; omega⟩ := Fin.ext (by change Multiset.card β = Multiset.card β - 1 + 1; omega)
    rw [hp, sadj_apply_right (by simp; omega)]
    simp only [t, Seq.cast_apply]
    rw [Seq.append_apply_lt _ _ _ (by simp only [Fin.val_cast]; omega)]
    congr 1
  change cL Q i β 1 * ψ (Multiset.card β - 1) * e t = 0
  have hsi : s.1 ⟨Multiset.card β - 1, by omega⟩ ≠ i := fun h => hi (h ▸ s.mem _)
  rw [mul_assoc, ψ_mul_e, ← mul_assoc, lowerLastCut_mul_e, hs,
    ite_eq_right hsi, zero_mul]

theorem cut_fT_zero (hi : i ∉ β) (d : Fin (Multiset.card β)) (t : Rb ⊗[k] Ri) :
    cL Q i β 1 * fT Q i β d.val t = 0 := by
  have hβ : 0 < Multiset.card β := Nat.zero_lt_of_lt d.isLt
  induction t using TensorProduct.inductionOn with
  | add u v hu hv => rw [map_add, mul_add, hu, hv, add_zero]
  | tmul b c =>
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
    rw [fT_tmul]
    change cL Q i β 1 * (w * ψ (Multiset.card β - 1) * cL Q i β b) = 0
    rw [← mul_assoc, ← mul_assoc, ← hc]
    have he : cL Q i β b = cL Q i β 1 * cL Q i β b := by rw [← cL_mul, one_mul]
    conv_lhs => rw [he]
    simp only [← mul_assoc]
    rw [mul_assoc w (cL Q i β 1) (ψ (Multiset.card β - 1)),
      mul_assoc w (cL Q i β 1 * ψ (Multiset.card β - 1)) (cL Q i β 1),
      cut_crossing_zero Q i β hi hβ, mul_zero, zero_mul]

theorem cut_kkF_zero (hi : i ∉ β) (p : Fin (Multiset.card β) → Rb ⊗[k] Ri) :
    cL Q i β 1 * kkF i β p 0 = 0 := by
  simp only [kkF, map_zero, add_zero, Finset.mul_sum, cut_fT_zero Q i β hi,
    Finset.sum_const_zero]

variable (hsym : KLRSymm Q)
  (a : I → Polynomial k) (hβ : 0 < Multiset.card β)

theorem cut_kkExpand (hi : i ∉ β) (r : R) :
    cL Q i β 1 * r * cL Q i β 1 =
      cLL Q i β (kkCoord i β hsym r).2 := by
  rw [mul_assoc, ← kkExpand_kkCoord i β hsym r]
  change cL Q i β 1 * kkF i β _ _ = _
  rw [kkF, mul_add, Finset.mul_sum, cL_one_mul_cLL]
  simp only [cut_fT_zero Q i β hi, Finset.sum_const_zero, zero_add]

theorem cSection_cMap_mk (hi : i ∉ β) (r : R) :
    cSection i β a hβ (cMap i β hsym a hβ (Submodule.Quotient.mk r)) =
      Submodule.Quotient.mk (cL Q i β 1 * r * cL Q i β 1) := by
  change cSection i β a hβ (thetaL0 Q i β a (kkCoord i β hsym r).2) = _
  rw [cSection_thetaL0, cut_kkExpand Q i β hsym hi]

theorem cSection_cMap (hi : i ∉ β)
    (z : KZero Q (Si + β) a (zero_lt_card_single_add i β)) :
    cSection i β a hβ (cMap i β hsym a hβ z) =
      cL Q i β 1 • act0 Q i β a 1 z := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [cSection_cMap_mk Q i β hsym a hβ hi, act0_mk]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [mul_assoc]
  rfl

theorem cMap_injective_on_cut (hi : i ∉ β)
    {z w : KZero Q (Si + β) a (zero_lt_card_single_add i β)}
    (hz : cL Q i β 1 • act0 Q i β a 1 z = z)
    (hw : cL Q i β 1 • act0 Q i β a 1 w = w)
    (he : cMap i β hsym a hβ z = cMap i β hsym a hβ w) : z = w := by
  have h := congrArg (cSection i β a hβ) he
  rw [cSection_cMap Q i β hsym a hβ hi, cSection_cMap Q i β hsym a hβ hi,
    hz, hw] at h
  exact h

local notation "S" => CycKLR k Q a (Si + β)
local notation "Rl" => CycKLR k Q a β
local notation "K0" => KZero Q (Si + β) a (zero_lt_card_single_add i β)

def quotientMap : K0 →ₗ[k] S :=
  ((cycL0 a (zero_lt_card_single_add i β)).restrictScalars k).liftQ
    (CycKLR.mk k Q a (Si + β)).toLinearMap
    (by intro r hr; exact (CycKLR.mk_eq_zero_iff r).2 (cycL0_le a _ hr)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k (cycL0 a _)).symm.toLinearMap

theorem quotientMap_mk (r : R) :
    quotientMap Q i β a (Submodule.Quotient.mk r) = CycKLR.mk k Q a (Si + β) r := rfl

theorem quotientMap_cut (z : K0) :
    quotientMap Q i β a (cL Q i β 1 • act0 Q i β a 1 z) =
      CycKLR.mk k Q a (Si + β) (cL Q i β 1) * quotientMap Q i β a z *
        CycKLR.mk k Q a (Si + β) (cL Q i β 1) := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change CycKLR.mk k Q a (Si + β) (cL Q i β 1 * (r * cL Q i β 1)) = _
  simp only [map_mul, quotientMap_mk, mul_assoc]

def polynomialToCorner : Polynomial Rl →ₗ[k] Corner Q i a β :=
  ((quotientMap Q i β a).comp (cSection i β a hβ)).codRestrict _ (by
    intro p
    obtain ⟨t, rfl⟩ := thetaL0_surjective i β a p
    change quotientMap Q i β a (cSection i β a hβ (thetaL0 Q i β a t)) ∈ _
    rw [cSection_thetaL0, quotientMap_mk]
    constructor
    · rw [← map_mul, cL_one_mul_cLL]
    · rw [← map_mul, cLL_mul_cL_one])

include hsym in
theorem polynomialToCorner_surjective (hi : i ∉ β) :
    Function.Surjective (polynomialToCorner Q i β a hβ) := by
  intro z
  obtain ⟨r, hr⟩ := CycKLR.mk_surjective (z : S)
  refine ⟨cMap i β hsym a hβ (Submodule.Quotient.mk r), ?_⟩
  apply Subtype.ext
  change quotientMap Q i β a (cSection i β a hβ (cMap i β hsym a hβ _)) = _
  rw [cSection_cMap Q i β hsym a hβ hi, quotientMap_cut, quotientMap_mk, hr]
  rw [z.2.1, z.2.2]

variable (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))

include h1 in
theorem quotientMap_pMap (z : KOne Q (Si + β) a h1) :
    quotientMap Q i β a ((pMap (Q := Q) a (zero_lt_card_single_add i β) h1 (Multiset.card β) (card_single_add i β).symm) z) = 0 := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [pMap_mk, quotientMap_mk]
  apply (CycKLR.mk_eq_zero_iff _).2
  exact TwoSidedIdeal.mul_mem_left _ _ _
    (TwoSidedIdeal.mul_mem_right _ _ _ (cycAt_mem_cycIdeal a _))

include h1 in
theorem ker_polynomialToCorner (hi : i ∉ β) :
    LinearMap.ker (polynomialToCorner Q i β a hβ) = LinearMap.range (aMap i β a h1 hβ hsym) := by
  ext p
  constructor
  · intro hp
    have hz : quotientMap Q i β a (cSection i β a hβ p) = 0 := congrArg Subtype.val hp
    have hpi : piMap a (zero_lt_card_single_add i β) (cSection i β a hβ p) = 0 := by
      obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (cSection i β a hβ p)
      rw [← hr, quotientMap_mk] at hz
      rw [← hr]
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact (CycKLR.mk_eq_zero_iff r).1 hz
    have hm : cSection i β a hβ p ∈ LinearMap.range (pMap (Q := Q) a (zero_lt_card_single_add i β) h1 (Multiset.card β) (card_single_add i β).symm) := by
      rw [range_pMap]
      exact hpi
    obtain ⟨z, hz⟩ := hm
    refine ⟨bMap i β hsym a h1 hβ z, ?_⟩
    rw [aMap_bMap, hz, cMap_cSection]
  · rintro ⟨q, rfl⟩
    apply Subtype.ext
    change quotientMap Q i β a (cSection i β a hβ ((aMap i β a h1 hβ hsym) q)) = 0
    change quotientMap Q i β a (cSection i β a hβ
      (cMap i β hsym a hβ ((pMap (Q := Q) a (zero_lt_card_single_add i β) h1 (Multiset.card β) (card_single_add i β).symm) (bSection i β a h1 hβ q)))) = 0
    rw [cSection_cMap Q i β hsym a hβ hi, quotientMap_cut, quotientMap_pMap,
      mul_zero, zero_mul]

def polynomialCokernelEquiv (hi : i ∉ β) :
    (Polynomial Rl ⧸ LinearMap.range (aMap i β a h1 hβ hsym)) ≃ₗ[k] Corner Q i a β :=
  (Submodule.quotEquivOfEq _ _ (ker_polynomialToCorner Q i β hsym a hβ h1 hi).symm).trans
    ((polynomialToCorner Q i β a hβ).quotKerEquivOfSurjective
      (polynomialToCorner_surjective Q i β hsym a hβ hi))

theorem polynomialToCorner_monomial (b : Rb) (d : ℕ) :
    polynomialToCorner Q i β a hβ (Polynomial.monomial d (CycKLR.mk k Q a β b)) =
      dotUnitTerm Q i a β d (CycKLR.mk k Q a β b) := by
  let xd : Ri := (x ⟨0, by rw [card_single']; omega⟩) ^ d
  have ht : thetaL0 Q i β a (b ⊗ₜ xd) = Polynomial.monomial d (CycKLR.mk k Q a β b) := by
    rw [thetaL0_apply, Algebra.TensorProduct.comm_tmul, thetaL, AlgHom.comp_apply, theta_tmul]
    simp only [xd, map_pow, singlePoly_x, Polynomial.aeval_X,
      Polynomial.coe_mapAlgHom, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    rw [(Polynomial.commute_X_pow _ _).eq, Polynomial.C_mul_X_pow_eq_monomial]
    rfl
  apply Subtype.ext
  change quotientMap Q i β a (cSection i β a hβ _) = _
  rw [← ht, cSection_thetaL0, quotientMap_mk, cLL_tmul, cLL_one_tmul]
  simp only [xd, map_pow, singlePoly_x, Polynomial.aeval_X, map_mul]
  change _ = cyclotomicLast Q i a β (CycKLR.mk k Q a β b) * _ * cyclotomicLast Q i a β 1
  rw [cyclotomicLast_mk, cyclotomicLast_one, mul_assoc]

theorem dotUnitSum_eq_polynomial (n : ℕ) (v : Fin n → Rl) :
    dotUnitSum Q i a β n v = polynomialToCorner Q i β a hβ
      ((Polynomial.degreeLTEquiv Rl n).symm v : Polynomial Rl) := by
  change _ = polynomialToCorner Q i β a hβ (∑ d : Fin n, Polynomial.monomial d (v d))
  rw [map_sum]
  simp only [dotUnitSum, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  apply Finset.sum_congr rfl
  intro d _
  obtain ⟨b, hb⟩ := CycKLR.mk_surjective (v d)
  rw [← hb, polynomialToCorner_monomial]

variable
  (hQ : ∀ i j : I, i ≠ j → ∃ c : k, IsUnit c ∧ (polyInY (Q i j)).leadingCoeff = Polynomial.C c)
  (ha : ∀ i, (a i).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) =
    -RD.pair (RD.iY i) (RD.iX j))
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX β))

include hsym hQ ha hΛ hdeg h1 hβ in
theorem exists_small_remainder (q : Polynomial Rl) :
    ∃ p, (q - aMap i β a h1 hβ hsym p).degree < ((wt).toNat : ℕ) := by
  rcases subsingleton_or_nontrivial Rl with h | h
  · refine ⟨0, ?_⟩
    rw [Subsingleton.elim q 0, map_zero, sub_self, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · obtain ⟨p, hp⟩ := aMap_exists_remainder i β a hsym hβ hQ ha h1 q
    have hd := aMonicL_degree_gap i β a RD Λ hsym hQ (ha i) hΛ hdeg
    have he : (aMonicL Q i β a).natDegree - (sPoly (Q := Q) i β a).natDegree = (wt).toNat := by omega
    exact ⟨p, by simpa only [he] using hp⟩

include hsym hQ ha hΛ hdeg h1 hβ in
theorem range_eq_small_zero (r : Polynomial Rl) (hr : r.degree < ((wt).toNat : ℕ))
    (he : r ∈ LinearMap.range (aMap i β a h1 hβ hsym)) : r = 0 := by
  rcases subsingleton_or_nontrivial Rl with h | h
  · exact Subsingleton.elim _ _
  · obtain ⟨p, hp⟩ := he
    obtain ⟨c, hc⟩ := isUnit_lamA (Q := Q) i β hQ
    obtain ⟨hlow, hhigh⟩ := aMap_phi_spec i β a hsym hβ hQ ha h1
    rw [← hc, Ring.inverse_unit] at hhigh
    have hd := aMonicL_degree_gap i β a RD Λ hsym hQ (ha i) hΛ hdeg
    have heh : (aMonicL Q i β a).natDegree - (sPoly (Q := Q) i β a).natDegree = (wt).toNat := by omega
    have hz := PhiAlg.degree_lt_of_apply_add_eq_zero
      (aMap i β a h1 hβ hsym).toAddMonoidHom c
      ((sPoly (Q := Q) i β a).natDegree - (aMonicL Q i β a).natDegree)
      ((aMonicL Q i β a).natDegree - (sPoly (Q := Q) i β a).natDegree)
      (aMap_mul_C i β a h1 hβ hsym) hlow hhigh
      (p := p) (r := -r) (by simpa only [Polynomial.degree_neg, heh] using hr)
      (by change aMap i β a h1 hβ hsym p + -r = 0; rw [hp, add_neg_cancel])
    have hp0 := (aMap_eq_zero_iff i β a hsym hβ hQ ha h1 p).2 hz
    exact hp.symm.trans hp0

include hsym hQ ha hΛ hdeg h1 hβ in
theorem dotUnitSum_bijective_positive (hi : i ∉ β) :
    Function.Bijective (dotUnitSum Q i a β (wt).toNat) := by
  constructor
  · intro v w hvw
    let pv : Polynomial.degreeLT Rl (wt).toNat := (Polynomial.degreeLTEquiv Rl (wt).toNat).symm v
    let pw : Polynomial.degreeLT Rl (wt).toNat := (Polynomial.degreeLTEquiv Rl (wt).toNat).symm w
    have he : polynomialToCorner Q i β a hβ (pv - pw : Polynomial Rl) = 0 := by
      rw [map_sub, sub_eq_zero]
      simpa only [dotUnitSum_eq_polynomial Q i β a hβ] using hvw
    have hm : (pv - pw : Polynomial Rl) ∈ LinearMap.range (aMap i β a h1 hβ hsym) := by
      rw [← ker_polynomialToCorner Q i β hsym a hβ h1 hi]
      exact he
    have hz := range_eq_small_zero Q i β hsym a hβ h1 hQ ha RD Λ hΛ hdeg
      (pv - pw) (Polynomial.mem_degreeLT.1 (pv - pw).2) hm
    have heq : pv = pw := Subtype.ext (sub_eq_zero.1 hz)
    exact (Polynomial.degreeLTEquiv Rl (wt).toNat).symm.injective heq
  · intro z
    obtain ⟨q, hq⟩ := polynomialToCorner_surjective Q i β hsym a hβ hi z
    obtain ⟨p, hp⟩ := exists_small_remainder Q i β hsym a hβ h1 hQ ha RD Λ hΛ hdeg q
    let r : Polynomial.degreeLT Rl (wt).toNat := ⟨q - aMap i β a h1 hβ hsym p,
      Polynomial.mem_degreeLT.2 hp⟩
    refine ⟨Polynomial.degreeLTEquiv Rl (wt).toNat r, ?_⟩
    rw [dotUnitSum_eq_polynomial, LinearEquiv.symm_apply_apply]
    change polynomialToCorner Q i β a hβ (q - aMap i β a h1 hβ hsym p) = z
    have hz : polynomialToCorner Q i β a hβ (aMap i β a h1 hβ hsym p) = 0 := by
      have hm : aMap i β a h1 hβ hsym p ∈ LinearMap.range (aMap i β a h1 hβ hsym) := ⟨p, rfl⟩
      rw [← ker_polynomialToCorner Q i β hsym a hβ h1 hi] at hm
      exact hm
    rw [map_sub, hz, sub_zero, hq]

include hsym hQ ha hΛ hdeg in
/-- The prescribed finite dot-unit map is bijective for every absent colour, including rank zero. -/
theorem dotUnitSum_bijective (hi : i ∉ β) :
    Function.Bijective (dotUnitSum Q i a β (wt).toNat) := by
  by_cases hb : β = 0
  · subst β
    have hd : (RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX (0 : Multiset I)))).toNat =
        (a i).natDegree := by simp [← hΛ]
    rw [hd]
    have he : ⇑(zeroFinEquiv Q i a (ha i)) = dotUnitSum Q i a 0 (a i).natDegree :=
      funext (zeroFinEquiv_apply Q i a (ha i))
    rw [← he]
    exact (zeroFinEquiv Q i a (ha i)).bijective
  · have hb' : 0 < Multiset.card β := Multiset.card_pos.mpr hb
    exact dotUnitSum_bijective_positive Q i β hsym a hb' (by simpa only [card_single_add] using Nat.succ_lt_succ hb')
      hQ ha RD Λ hΛ hdeg hi

/-- The equivalence has the dot-unit sum as its forward map. -/
def finEquiv (hi : i ∉ β) : (Fin (wt).toNat → Rl) ≃ₗ[k] Corner Q i a β :=
  LinearEquiv.ofBijective (dotUnitSum Q i a β (wt).toNat)
    (dotUnitSum_bijective Q i β hsym a hQ ha RD Λ hΛ hdeg hi)

theorem finEquiv_apply (hi : i ∉ β) (v : Fin (wt).toNat → Rl) :
    finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi v = dotUnitSum Q i a β (wt).toNat v := rfl

theorem finEquiv_inverse_forward (hi : i ∉ β) (v : Fin (wt).toNat → Rl) :
    (finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi).symm
      (dotUnitSum Q i a β (wt).toNat v) = v :=
  (finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi).symm_apply_apply v

theorem finEquiv_forward_inverse (hi : i ∉ β) (z : Corner Q i a β) :
    dotUnitSum Q i a β (wt).toNat
      ((finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi).symm z) = z :=
  (finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi).apply_symm_apply z

theorem dotUnitSum_left (n : ℕ) (r : Rl) (v : Fin n → Rl) :
    dotUnitSum Q i a β n (fun d => r * v d) = r • dotUnitSum Q i a β n v := by
  apply Subtype.ext
  rw [corner_smul_val, dotUnitSum_apply, dotUnitSum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  simp only [map_mul, mul_assoc]

theorem dotUnitSum_right (n : ℕ) (r : Rl) (v : Fin n → Rl) :
    dotUnitSum Q i a β n (fun d => v d * r) = MulOpposite.op r • dotUnitSum Q i a β n v := by
  apply Subtype.ext
  rw [corner_op_smul_val, dotUnitSum_apply, dotUnitSum_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  obtain ⟨b, rfl⟩ := CycKLR.mk_surjective r
  have hc := ((commute_x_last_cL (Q := Q) i β b).pow_left (d : ℕ)).map (CycKLR.mk k Q a (Si + β))
  rw [map_pow, ← cyclotomicLast_mk] at hc
  change cyclotomicLast Q i a β (v d * CycKLR.mk k Q a β b) * _ * _ =
    _ * _ * _ * cyclotomicLast Q i a β (CycKLR.mk k Q a β b)
  simp only [map_mul, ← cyclotomicLast_one, mul_assoc]
  rw [← mul_assoc (cyclotomicLast Q i a β (CycKLR.mk k Q a β b)), ← hc.eq]
  simp only [mul_assoc, ← map_mul, mul_one, one_mul]

theorem finEquiv_left (hi : i ∉ β) (r : Rl) (v : Fin (wt).toNat → Rl) :
    finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi (fun d => r * v d) =
      r • finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi v :=
  dotUnitSum_left Q i β a _ r v

theorem finEquiv_right (hi : i ∉ β) (r : Rl) (v : Fin (wt).toNat → Rl) :
    finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi (fun d => v d * r) =
      MulOpposite.op r • finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi v :=
  dotUnitSum_right Q i β a _ r v

theorem finEquiv_symm_left (hi : i ∉ β) (r : Rl) (z : Corner Q i a β) :
    (finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi).symm (r • z) =
      fun d => r * (finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi).symm z d := by
  apply (finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi).injective
  rw [LinearEquiv.apply_symm_apply, finEquiv_left, LinearEquiv.apply_symm_apply]

theorem finEquiv_symm_right (hi : i ∉ β) (r : Rl) (z : Corner Q i a β) :
    (finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi).symm (MulOpposite.op r • z) =
      fun d => (finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi).symm z d * r := by
  apply (finEquiv Q i β hsym a hQ ha RD Λ hΛ hdeg hi).injective
  rw [LinearEquiv.apply_symm_apply, finEquiv_right, LinearEquiv.apply_symm_apply]

end Categorification.KLR.KLRAlgebra.AbsentColour
