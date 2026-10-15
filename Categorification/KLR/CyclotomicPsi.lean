/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicRecursion

/-!
# The two cyclotomic coordinates and their dot recurrence

The coordinate realization of the decomposition used in Kang–Kashiwara,
arXiv:1102.4677v4, (5.13)–(5.14). The first coordinate takes values in a finite
family of cyclotomic polynomials, the coordinate model for the `F` summand.
-/

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (i : I) (β : Multiset I)
  (a : I → Polynomial k)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rb" => KLRAlgebra k Q β
local notation "Ri" => KLRAlgebra k Q Si
local notation "T0" => Rb ⊗[k] Ri
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "Rl" => CycKLR k Q a β
local notation "N" => Fin (Multiset.card β)
local notation "K0" => KZero Q (Si + β) a (zero_lt_card_single_add i β)

variable (hsym : KLRSymm Q)

/-- The cyclotomic first coordinates of the `F` decomposition. -/
noncomputable def fCoordsR : R →ₗ[k] (N → Polynomial Rl) :=
  LinearMap.pi fun b => (thetaL0 Q i β a).toLinearMap ∘ₗ
    (LinearMap.proj b) ∘ₗ (LinearMap.fst k (N → T0) T0) ∘ₗ kkCoord i β hsym

theorem fCoordsR_apply (r : R) (b : N) :
    fCoordsR i β a hsym r b = thetaL0 Q i β a ((kkCoord i β hsym r).1 b) := rfl

theorem fCoordsR_kkF (p : N → T0) (q : T0) :
    fCoordsR i β a hsym (kkF i β p q) = fun b => thetaL0 Q i β a (p b) := by
  funext b
  rw [fCoordsR_apply, kkCoord_kkF]

/-- A last dot advances each first coordinate by multiplication by `X`. -/
theorem fCoordsR_mul_last_dot (r : R) :
    fCoordsR i β a hsym (r * x ⟨Multiset.card β, lastPos_lt i β⟩) =
      fun b => fCoordsR i β a hsym r b * Polynomial.X := by
  obtain ⟨p, q, hpq⟩ := kkF_surj i β hsym r
  have hc : kkCoord i β hsym r = (p, q) := by
    apply kkExpand_injective i β hsym
    rw [kkExpand_kkCoord]
    exact hpq
  obtain ⟨y, hy⟩ := kkF_mul_last_dot i β p q
  have hd : kkCoord i β hsym (r * x ⟨Multiset.card β, lastPos_lt i β⟩) =
      ((fun b => p b * (1 ⊗ₜ x ⟨0, by rw [card_single']; omega⟩)),
        q * (1 ⊗ₜ x ⟨0, by rw [card_single']; omega⟩) + y ⊗ₜ 1) := by
    apply kkExpand_injective i β hsym
    rw [kkExpand_kkCoord]
    change (r * x _) * cL Q i β 1 = _
    rw [mul_assoc, (commute_x_last_cL i β 1).eq, ← mul_assoc, hpq]
    exact hy
  funext b
  rw [fCoordsR_apply, fCoordsR_apply, hc, hd, map_mul, thetaL0_one_tmul_x]

variable (hβ : 0 < Multiset.card β)

include hβ in
theorem fCoordsR_eq_zero {r : R} (hr : r ∈ cycL0 a (zero_lt_card_single_add i β)) :
    fCoordsR i β a hsym r = 0 := by
  have hr' := mul_mem_cycL0 a hr (cL_one_mem_subR0 i β)
  rw [← kkExpand_kkCoord i β hsym r] at hr'
  have hp := (kkF_mem_cycL0_iff i β a hsym hβ _ _).1 hr'
  funext b
  exact (thetaL0_eq_zero_iff i β a _).2 (hp.1 b)

/-- The first coordinates on `K_0`. -/
noncomputable def fCoords : K0 →ₗ[k] (N → Polynomial Rl) :=
  ((cycL0 a (zero_lt_card_single_add i β)).restrictScalars k).liftQ
      (fCoordsR i β a hsym)
      (fun _ hr => LinearMap.mem_ker.2 (fCoordsR_eq_zero i β a hsym hβ hr)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k (cycL0 a _)).symm.toLinearMap

@[simp] theorem fCoords_mk (r : R) :
    fCoords i β a hsym hβ (Submodule.Quotient.mk r) = fCoordsR i β a hsym r := rfl

/-- The `b`th `F` coordinate, before descent of its coefficient. -/
noncomputable def fLift (b : N) : T0 →ₗ[k] K0 :=
  ((cycL0 a (zero_lt_card_single_add i β)).mkQ.restrictScalars k).comp (fT Q i β b.val)

include hβ in
theorem ker_thetaL0_le_fLift (b : N) :
    LinearMap.ker (thetaL0 Q i β a).toLinearMap ≤ LinearMap.ker (fLift i β a b) := by
  intro t ht
  change Submodule.Quotient.mk (fT Q i β b.val t) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact fT_mem_cycL0 i β a hβ b.val ((thetaL0_eq_zero_iff i β a t).1 ht)

/-- The `b`th `F` summand with cyclotomic polynomial coefficients. -/
noncomputable def fSingle (b : N) : Polynomial Rl →ₗ[k] K0 :=
  (LinearMap.ker (thetaL0 Q i β a).toLinearMap).liftQ (fLift i β a b)
      (ker_thetaL0_le_fLift i β a hβ b) ∘ₗ
    ((thetaL0 Q i β a).toLinearMap.quotKerEquivOfSurjective
      (thetaL0_surjective i β a)).symm.toLinearMap

theorem fSingle_thetaL0 (b : N) (t : T0) :
    fSingle i β a hβ b (thetaL0 Q i β a t) = Submodule.Quotient.mk (fT Q i β b.val t) := by
  have he := LinearMap.quotKerEquivOfSurjective_symm_apply
    (f := (thetaL0 Q i β a).toLinearMap) (thetaL0_surjective i β a) t
  change ((LinearMap.ker (thetaL0 Q i β a).toLinearMap).liftQ (fLift i β a b)
    (ker_thetaL0_le_fLift i β a hβ b))
      (((thetaL0 Q i β a).toLinearMap.quotKerEquivOfSurjective
        (thetaL0_surjective i β a)).symm ((thetaL0 Q i β a).toLinearMap t)) = _
  rw [he, Submodule.liftQ_apply]
  rfl

/-- Inclusion of the `F` coordinate family in `K_0`. -/
noncomputable def fSection : (N → Polynomial Rl) →ₗ[k] K0 :=
  ∑ b, (fSingle i β a hβ b).comp (LinearMap.proj b)

theorem fSection_thetaL0 (p : N → T0) :
    fSection i β a hβ (fun b => thetaL0 Q i β a (p b)) =
      Submodule.Quotient.mk (kkF i β p 0) := by
  simp only [fSection, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    fSingle_thetaL0, kkF, map_zero, add_zero]
  exact (map_sum (cycL0 a (zero_lt_card_single_add i β)).mkQ _ _).symm

/-- Both coordinate families reconstruct the right projection of an element of `K_0`. -/
theorem fSection_add_cSection (w : K0) :
    fSection i β a hβ (fCoords i β a hsym hβ w) +
      cSection i β a hβ (cMap i β hsym a hβ w) = act0 Q i β a 1 w := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [fCoords_mk, cMap_mk, act0_mk]
  let t := kkCoord i β hsym r
  change fSection i β a hβ (fun b => thetaL0 Q i β a (t.1 b)) +
    cSection i β a hβ (thetaL0 Q i β a t.2) = _
  rw [fSection_thetaL0, cSection_thetaL0, ← Submodule.Quotient.mk_add]
  congr 1
  rw [← kkExpand_kkCoord i β hsym r]
  change kkF i β t.1 0 + cLL Q i β t.2 = kkF i β t.1 t.2
  simp only [kkF, map_zero, add_zero]

/-- The two coordinate families distinguish the `F` summand. -/
theorem fCoords_fSection (p : N → Polynomial Rl) :
    fCoords i β a hsym hβ (fSection i β a hβ p) = p := by
  choose t ht using fun b => thetaL0_surjective i β a (p b)
  have hp : p = fun b => thetaL0 Q i β a (t b) := funext fun b => (ht b).symm
  rw [hp, fSection_thetaL0, fCoords_mk, fCoordsR_kkF]

/-- Right multiplication by the last dot on `K_0`. -/
noncomputable def lastDot0 : K0 →ₗ[R] K0 :=
  (cycL0 a (zero_lt_card_single_add i β)).mapQ (cycL0 a _)
    (LinearMap.toSpanSingleton R R (x ⟨Multiset.card β, lastPos_lt i β⟩))
    (fun _ hw => mul_mem_cycL0 a hw (x_mem_subR0 _))

theorem lastDot0_mk (r : R) :
    lastDot0 i β a (Submodule.Quotient.mk r) =
      Submodule.Quotient.mk (r * x ⟨Multiset.card β, lastPos_lt i β⟩) := rfl

theorem fCoords_lastDot0 (w : K0) :
    fCoords i β a hsym hβ (lastDot0 i β a w) =
      fun b => fCoords i β a hsym hβ w b * Polynomial.X := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [lastDot0_mk, fCoords_mk, fCoords_mk, fCoordsR_mul_last_dot]

theorem cMap_fSection (p : N → Polynomial Rl) :
    cMap i β hsym a hβ (fSection i β a hβ p) = 0 := by
  choose t ht using fun b => thetaL0_surjective i β a (p b)
  have hp : p = fun b => thetaL0 Q i β a (t b) := funext fun b => (ht b).symm
  rw [hp, fSection_thetaL0, cMap_kkF, map_zero]

theorem lastDot0_cSection (s : Polynomial Rl) :
    lastDot0 i β a (cSection i β a hβ s) = cSection i β a hβ (s * Polynomial.X) := by
  obtain ⟨q, rfl⟩ := thetaL0_surjective i β a s
  rw [cSection_thetaL0, lastDot0_mk]
  have ht := cSection_thetaL0 i β a hβ (q * (1 ⊗ₜ x ⟨0, by rw [card_single']; omega⟩))
  rw [map_mul, thetaL0_one_tmul_x, cLL_mul_last_dot] at ht
  exact ht.symm

theorem lastDot0_fSection_exists (p : N → Polynomial Rl) :
    ∃ y : Rl, lastDot0 i β a (fSection i β a hβ p) =
      fSection i β a hβ (fun b => p b * Polynomial.X) + cSection i β a hβ (Polynomial.C y) := by
  choose t ht using fun b => thetaL0_surjective i β a (p b)
  have hp : p = fun b => thetaL0 Q i β a (t b) := funext fun b => (ht b).symm
  obtain ⟨y, hy⟩ := kkF_mul_last_dot i β t 0
  refine ⟨CycKLR.mk k Q a β y, ?_⟩
  rw [hp, fSection_thetaL0, lastDot0_mk, hy]
  simp only [zero_mul, zero_add]
  have hp' : (fun b => thetaL0 Q i β a (t b) * Polynomial.X) =
      fun b => thetaL0 Q i β a (t b * (1 ⊗ₜ x ⟨0, by rw [card_single']; omega⟩)) := by
    funext b
    rw [map_mul, thetaL0_one_tmul_x]
  rw [hp', fSection_thetaL0, ← thetaL0_tmul_one i β a y, cSection_thetaL0,
    ← Submodule.Quotient.mk_add]
  congr 1
  simp only [kkF, map_zero, add_zero]

/-- The constant correction of the last dot on the `F` summand. Its definition
uses the coefficient map; comparison with multiplication on a balanced tensor
product is a separate identification. -/
noncomputable def eCoords : (N → Polynomial Rl) →ₗ[k] Rl :=
  ((Polynomial.lcoeff Rl 0).restrictScalars k).comp ((cMap i β hsym a hβ).comp
    ((lastDot0 i β a).restrictScalars k)) ∘ₗ fSection i β a hβ

/-- The two summands in the last-dot recursion, with their determined correction. -/
theorem lastDot0_fSection (p : N → Polynomial Rl) :
    lastDot0 i β a (fSection i β a hβ p) =
      fSection i β a hβ (fun b => p b * Polynomial.X) +
        cSection i β a hβ (Polynomial.C (eCoords i β a hsym hβ p)) := by
  obtain ⟨y, hy⟩ := lastDot0_fSection_exists i β a hβ p
  have he : eCoords i β a hsym hβ p = y := by
    change (cMap i β hsym a hβ (lastDot0 i β a (fSection i β a hβ p))).coeff 0 = y
    rw [hy, map_add, cMap_fSection, cMap_cSection, zero_add, Polynomial.coeff_C_zero]
  rw [he]
  exact hy

variable (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))

/-- Apply `P` to the canonical full-crossing lift. -/
noncomputable def pLift : Polynomial Rl →ₗ[k] K0 :=
  ((pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β)
    (card_single_add i β).symm).restrictScalars k).comp (bSection i β a h1 hβ)

theorem pLift_thetaL (t : Ri ⊗[k] Rb) :
    pLift i β a hβ h1 (thetaL Q i β a t) = Submodule.Quotient.mk
      ((ψw (descRun 0 (Multiset.card β)) * concat Q Si β t) *
        tauW a (zero_lt_card_single_add i β) (Multiset.card β)) := by
  change pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β) (card_single_add i β).symm
    (bSection i β a h1 hβ (thetaL Q i β a t)) = _
  rw [bSection_thetaL, pMap_mk]

theorem pLift_mul_X (s : Polynomial Rl) :
    pLift i β a hβ h1 (s * Polynomial.X) = lastDot0 i β a (pLift i β a hβ h1 s) := by
  obtain ⟨t, rfl⟩ := thetaL_surjective i β a s
  rw [← thetaL_x_tmul_one i β a, ← map_mul, pLift_thetaL,
    pLift_thetaL, lastDot0_mk, concat_mul_first_dot, Submodule.Quotient.eq]
  have hz := Submodule.smul_mem (cycL0 (Q := Q) a (zero_lt_card_single_add i β))
    (ψw (descRun 0 (Multiset.card β)) * concat Q Si β t)
    (x_zero_mul_tauW a (zero_lt_card_single_add i β) (Multiset.card β)
      (card_single_add i β).symm)
  simpa only [smul_eq_mul, mul_sub, ← mul_assoc] using hz

theorem act0_one_pLift (s : Polynomial Rl) :
    act0 Q i β a 1 (pLift i β a hβ h1 s) = pLift i β a hβ h1 s := by
  change act0 Q i β a 1 (pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β)
    (card_single_add i β).symm (bSection i β a h1 hβ s)) = _
  rw [← pMap_act, ← bSection_mul_C, map_one, map_one, mul_one]
  rfl

/-- The first coordinates of `P` applied to the canonical lift. -/
noncomputable def psiCoords : Polynomial Rl →ₗ[k] (N → Polynomial Rl) :=
  (fCoords i β a hsym hβ).comp (pLift i β a hβ h1)

/-- The coordinate form of the decomposition (5.13), for every polynomial. -/
theorem pLift_decomposition (s : Polynomial Rl) :
    pLift i β a hβ h1 s = fSection i β a hβ (psiCoords i β a hsym hβ h1 s) +
      cSection i β a hβ (aMap i β a h1 hβ hsym s) := by
  have h := fSection_add_cSection i β a hsym hβ (pLift i β a hβ h1 s)
  rw [act0_one_pLift] at h
  exact h.symm

/-- The first-coordinate recurrence in (5.14), expressed in the free tensor coordinates. -/
theorem psiCoords_mul_X (s : Polynomial Rl) :
    psiCoords i β a hsym hβ h1 (s * Polynomial.X) =
      fun b => psiCoords i β a hsym hβ h1 s b * Polynomial.X := by
  change fCoords i β a hsym hβ (pLift i β a hβ h1 (s * Polynomial.X)) = _
  rw [pLift_mul_X, fCoords_lastDot0]
  rfl

/-- The `ψ_k` coordinates are generated from `ψ_0` by the polynomial variable. -/
theorem psiCoords_X_pow (m : ℕ) (b : N) :
    psiCoords i β a hsym hβ h1 (Polynomial.X ^ m) b =
      psiCoords i β a hsym hβ h1 1 b * Polynomial.X ^ m := by
  induction m with
  | zero => rw [pow_zero, mul_one]
  | succ m ih => simp only [pow_succ, psiCoords_mul_X, ih, mul_assoc]

/-- The second-coordinate recurrence in (5.14), with the determined constant correction. -/
theorem aMap_mul_X_eq (s : Polynomial Rl) :
    aMap i β a h1 hβ hsym (s * Polynomial.X) =
      aMap i β a h1 hβ hsym s * Polynomial.X +
        Polynomial.C (eCoords i β a hsym hβ (psiCoords i β a hsym hβ h1 s)) := by
  change cMap i β hsym a hβ (pLift i β a hβ h1 (s * Polynomial.X)) = _
  rw [pLift_mul_X, pLift_decomposition i β a hsym hβ h1 s, map_add,
    lastDot0_fSection, lastDot0_cSection, map_add, map_add,
    cMap_fSection, cMap_cSection, cMap_cSection, zero_add, add_comm]

end Categorification.KLR.KLRAlgebra
