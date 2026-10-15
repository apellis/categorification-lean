/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicB

/-!
# The cyclotomic cokernel coordinate C

The direct sum in Kang–Kashiwara, arXiv:1102.4677v4, §5.2 has a
projection onto `R^Λ(β)[t]`. Here it is constructed from `kkF`, with its kernel,
section and right `R(β)`-linearity. This supplies the projection `C` for the
polynomial map `A = C P B⁻¹` in the subsequent diagram chase. The notation `B⁻¹`
here means a section of `B`, not an inverse.
-/

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (i : I) (β : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rb" => KLRAlgebra k Q β
local notation "T0" => Rb ⊗[k] KLRAlgebra k Q Si
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "N" => Fin (Multiset.card β)

/-- The two coordinates of the `F` direct-sum decomposition. -/
noncomputable def kkExpand : ((N → T0) × T0) →ₗ[k] R where
  toFun t := kkF i β t.1 t.2
  map_add' t u := by
    simp only [kkF, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add,
      Finset.sum_add_distrib]
    abel
  map_smul' c t := by
    simp only [kkF, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul,
      Finset.smul_sum, smul_add, RingHom.id_apply]

theorem kkExpand_apply (p : N → T0) (q : T0) : kkExpand i β (p, q) = kkF i β p q := rfl

theorem kkF_mul_cL_one (p : N → T0) (q : T0) :
    kkF i β p q * cL Q i β 1 = kkF i β p q := by
  rw [← kkF_mul_cL, ← Algebra.TensorProduct.one_def]
  simp only [mul_one]

variable (hsym : KLRSymm Q)

include hsym in
theorem kkExpand_injective : Function.Injective (kkExpand (Q := Q) i β) := by
  intro s t h
  have hz : kkExpand i β (s - t) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨hp, hq⟩ := kkF_inj i β hsym hz
  exact Prod.ext (sub_eq_zero.1 hp) (sub_eq_zero.1 hq)

include hsym in
theorem kkExpand_span (r : R) : ∃ t : (N → T0) × T0,
    r * cL Q i β 1 = kkExpand i β t := by
  obtain ⟨p, q, hpq⟩ := kkF_surj i β hsym r
  exact ⟨(p, q), hpq⟩

/-- Both `F`-coordinates of the right projection to `e(β,i)`. -/
noncomputable def kkCoord : R →ₗ[k] ((N → T0) × T0) where
  toFun r := (kkExpand_span i β hsym r).choose
  map_add' r s := kkExpand_injective i β hsym (by
    rw [← (kkExpand_span i β hsym (r + s)).choose_spec, map_add,
      ← (kkExpand_span i β hsym r).choose_spec,
      ← (kkExpand_span i β hsym s).choose_spec, add_mul])
  map_smul' c r := kkExpand_injective i β hsym (by
    rw [← (kkExpand_span i β hsym (c • r)).choose_spec, map_smul,
      ← (kkExpand_span i β hsym r).choose_spec, smul_mul_assoc, RingHom.id_apply])

theorem kkExpand_kkCoord (r : R) :
    kkExpand i β (kkCoord i β hsym r) = r * cL Q i β 1 :=
  (kkExpand_span i β hsym r).choose_spec.symm

@[simp] theorem kkCoord_kkF (p : N → T0) (q : T0) :
    kkCoord i β hsym (kkF i β p q) = (p, q) := by
  apply kkExpand_injective i β hsym
  rw [kkExpand_kkCoord, kkF_mul_cL_one]
  rfl

theorem kkCoord_mul_cL (r : R) (y : Rb) :
    kkCoord i β hsym (r * cL Q i β y) =
      ((fun b => (kkCoord i β hsym r).1 b * (y ⊗ₜ 1)),
        (kkCoord i β hsym r).2 * (y ⊗ₜ 1)) := by
  apply kkExpand_injective i β hsym
  rw [kkExpand_kkCoord, kkExpand_apply, kkF_mul_cL]
  change (r * cL Q i β y) * cL Q i β 1 =
    kkExpand i β (kkCoord i β hsym r) * cL Q i β y
  rw [kkExpand_kkCoord, mul_assoc, ← cL_mul, mul_one,
    mul_assoc, ← cL_mul, one_mul]

/-- The complementary tensor coordinate of `F`. -/
noncomputable def cCoord : R →ₗ[k] T0 :=
  (LinearMap.snd k (N → T0) T0).comp (kkCoord i β hsym)

@[simp] theorem cCoord_kkF (p : N → T0) (q : T0) :
    cCoord i β hsym (kkF i β p q) = q := by
  change (kkCoord i β hsym (kkF i β p q)).2 = q
  rw [kkCoord_kkF]

theorem cCoord_mul_cL (r : R) (y : Rb) :
    cCoord i β hsym (r * cL Q i β y) = cCoord i β hsym r * (y ⊗ₜ 1) := by
  change (kkCoord i β hsym (r * cL Q i β y)).2 = _
  rw [kkCoord_mul_cL]
  rfl

variable (a : I → Polynomial k) (hβ : 0 < Multiset.card β)

/-- Reduce the complementary coordinate modulo the cyclotomic ideal. -/
noncomputable def cPoly : R →ₗ[k] Polynomial (CycKLR k Q a β) :=
  (thetaL0 Q i β a).toLinearMap.comp (cCoord i β hsym)

theorem cPoly_kkF (p : N → T0) (q : T0) :
    cPoly i β hsym a (kkF i β p q) = thetaL0 Q i β a q := by
  change thetaL0 Q i β a (cCoord i β hsym (kkF i β p q)) = _
  rw [cCoord_kkF]

include hβ in
theorem cPoly_eq_zero {r : R} (hr : r ∈ cycL0 a (zero_lt_card_single_add i β)) :
    cPoly i β hsym a r = 0 := by
  have hr' : r * cL Q i β 1 ∈ cycL0 a (zero_lt_card_single_add i β) :=
    mul_mem_cycL0 a hr (cL_one_mem_subR0 i β)
  rw [← kkExpand_kkCoord i β hsym r] at hr'
  have h := (kkF_mem_cycL0_iff i β a hsym hβ
    (kkCoord i β hsym r).1 (kkCoord i β hsym r).2).1 hr'
  exact (thetaL0_eq_zero_iff i β a _).2 h.2

/-- The cokernel coordinate `C` on `K_0`, including right projection to `e(β,i)`. -/
noncomputable def cMap : KZero Q (Si + β) a (zero_lt_card_single_add i β) →ₗ[k]
    Polynomial (CycKLR k Q a β) :=
  ((cycL0 a (zero_lt_card_single_add i β)).restrictScalars k).liftQ (cPoly i β hsym a)
      (fun _ hr => LinearMap.mem_ker.2 (cPoly_eq_zero i β hsym a hβ hr)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k (cycL0 a _)).symm.toLinearMap

@[simp] theorem cMap_mk (r : R) :
    cMap i β hsym a hβ (Submodule.Quotient.mk r) = cPoly i β hsym a r := rfl

/-- `C` selects precisely the second summand of the cyclotomic `F` decomposition. -/
theorem cMap_kkF (p : N → T0) (q : T0) :
    cMap i β hsym a hβ (Submodule.Quotient.mk (kkF i β p q)) = thetaL0 Q i β a q := by
  rw [cMap_mk, cPoly_kkF]

theorem kkF_zero_left (q : T0) : kkF i β (0 : N → T0) q = cLL Q i β q := by
  simp only [kkF, Pi.zero_apply, map_zero, Finset.sum_const_zero, zero_add]

/-- The polynomial summand gives lifts of every value of `C`. -/
theorem cMap_cLL (q : T0) :
    cMap i β hsym a hβ (Submodule.Quotient.mk (cLL Q i β q)) = thetaL0 Q i β a q := by
  rw [← kkF_zero_left i β, cMap_kkF]

theorem cMap_surjective : Function.Surjective (cMap i β hsym a hβ) := by
  intro p
  obtain ⟨q, rfl⟩ := thetaL0_surjective i β a p
  exact ⟨_, cMap_cLL i β hsym a hβ q⟩

/-- The tensor realization of the polynomial summand in `K_0`. -/
noncomputable def cLift : T0 →ₗ[k] KZero Q (Si + β) a (zero_lt_card_single_add i β) :=
  ((cycL0 a (zero_lt_card_single_add i β)).mkQ.restrictScalars k).comp (cLL Q i β)

theorem cLift_apply (q : T0) : cLift i β a q = Submodule.Quotient.mk (cLL Q i β q) := rfl

include hβ in
theorem ker_thetaL0_le_cLift :
    LinearMap.ker (thetaL0 Q i β a).toLinearMap ≤ LinearMap.ker (cLift i β a) := by
  intro q hq
  rw [LinearMap.mem_ker, cLift_apply, Submodule.Quotient.mk_eq_zero]
  exact cLL_mem_cycL0 i β a hβ ((thetaL0_eq_zero_iff i β a q).1 hq)

/-- The polynomial inclusion complementary to `F`, independent of the chosen lift. -/
noncomputable def cSection : Polynomial (CycKLR k Q a β) →ₗ[k]
    KZero Q (Si + β) a (zero_lt_card_single_add i β) :=
  (LinearMap.ker (thetaL0 Q i β a).toLinearMap).liftQ (cLift i β a)
      (ker_thetaL0_le_cLift i β a hβ) ∘ₗ
    ((thetaL0 Q i β a).toLinearMap.quotKerEquivOfSurjective
      (thetaL0_surjective i β a)).symm.toLinearMap

theorem cSection_thetaL0 (q : T0) :
    cSection i β a hβ (thetaL0 Q i β a q) = Submodule.Quotient.mk (cLL Q i β q) := by
  have he := LinearMap.quotKerEquivOfSurjective_symm_apply
    (f := (thetaL0 Q i β a).toLinearMap) (thetaL0_surjective i β a) q
  change ((LinearMap.ker (thetaL0 Q i β a).toLinearMap).liftQ (cLift i β a)
    (ker_thetaL0_le_cLift i β a hβ))
      (((thetaL0 Q i β a).toLinearMap.quotKerEquivOfSurjective
        (thetaL0_surjective i β a)).symm ((thetaL0 Q i β a).toLinearMap q)) = _
  rw [he, Submodule.liftQ_apply]
  rfl

/-- `C` is split by the polynomial inclusion. -/
@[simp] theorem cMap_cSection (p : Polynomial (CycKLR k Q a β)) :
    cMap i β hsym a hβ (cSection i β a hβ p) = p := by
  obtain ⟨q, rfl⟩ := thetaL0_surjective i β a p
  rw [cSection_thetaL0, cMap_cLL]

include hsym in
theorem cSection_injective : Function.Injective (cSection (Q := Q) i β a hβ) := by
  intro p q h
  have := congrArg (cMap i β hsym a hβ) h
  simpa only [cMap_cSection] using this

/-- Right `R(β)`-linearity of `C`. -/
theorem cMap_act0 (b : Rb) (w : KZero Q (Si + β) a (zero_lt_card_single_add i β)) :
    cMap i β hsym a hβ (act0 Q i β a b w) =
      cMap i β hsym a hβ w * Polynomial.C (CycKLR.mk k Q a β b) := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [act0_mk, cMap_mk, cMap_mk]
  change thetaL0 Q i β a (cCoord i β hsym (r * cL Q i β b)) = _
  rw [cCoord_mul_cL, map_mul, thetaL0_tmul_one]
  rfl

/-- Exactness in coordinates: `C(r)=0` iff the right projection of `r` is an
`F`-expansion modulo the cyclotomic submodule. -/
theorem cMap_mk_eq_zero_iff (r : R) :
    cMap i β hsym a hβ (Submodule.Quotient.mk r) = 0 ↔
      ∃ p : N → T0, r * cL Q i β 1 - kkF i β p 0 ∈ cycL0 a (zero_lt_card_single_add i β) := by
  rw [cMap_mk]
  constructor
  · intro hr
    refine ⟨(kkCoord i β hsym r).1, ?_⟩
    rw [← kkExpand_kkCoord i β hsym r]
    change kkF i β (kkCoord i β hsym r).1 (kkCoord i β hsym r).2 -
      kkF i β (kkCoord i β hsym r).1 0 ∈ _
    have he : ∀ p : N → T0, ∀ q : T0, kkF i β p q - kkF i β p 0 = cLL Q i β q := by
      intro p q
      simp only [kkF, map_zero, add_zero, add_sub_cancel_left]
    rw [he]
    exact cLL_mem_cycL0 i β a hβ ((thetaL0_eq_zero_iff i β a _).1 hr)
  · rintro ⟨p, hr⟩
    have hz := cPoly_eq_zero i β hsym a hβ hr
    rw [map_sub, ← kkExpand_kkCoord i β hsym r] at hz
    change cPoly i β hsym a (kkF i β _ _) - cPoly i β hsym a (kkF i β p 0) = 0 at hz
    rw [cPoly_kkF, cPoly_kkF, map_zero, sub_zero] at hz
    exact hz

end Categorification.KLR.KLRAlgebra
