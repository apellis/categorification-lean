/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicC

/-!
# The polynomial map A from the cyclotomic KLR maps

Construct `A(s) = C(P(ψ_{n-1}⋯ψ_0 ι'(s)))`, the polynomial map in
Kang–Kashiwara, arXiv:1102.4677v4, §5.2. The full-crossing lift is well-defined
on `R^Λ(β)[t]` and is a section of the first-strand coefficient map.

The construction uses the library's crossing convention in both `P` and the
section; the two length-`n` crossing signs cancel in `A`. The identity `AB = CP`,
the polynomial recursions, and the triangularity hypotheses of `CyclotomicPhi`
are not asserted here.
-/

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (i : I) (β : Multiset I)
  (a : I → Polynomial k)
  (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))
  (hβ : 0 < Multiset.card β)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "T" => KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q β
local notation "Rl" => CycKLR k Q a β
local notation "R" => KLRAlgebra k Q (Si + β)

/-- The full first-strand crossing with a tensor coefficient. -/
noncomputable def bLift : T →ₗ[k] KOne Q (Si + β) a h1 :=
  ((cycL1 a h1).mkQ.restrictScalars k).comp
    { toFun := fun t => ψw (descRun 0 (Multiset.card β)) * concat Q Si β t
      map_add' s t := by rw [map_add, mul_add]
      map_smul' c t := by rw [map_smul, mul_smul_comm, RingHom.id_apply] }

theorem bLift_apply (t : T) :
    bLift i β a h1 t = Submodule.Quotient.mk
      (ψw (descRun 0 (Multiset.card β)) * concat Q Si β t) := rfl

include hβ in
theorem ker_thetaL_le_bLift :
    LinearMap.ker (thetaL Q i β a).toLinearMap ≤ LinearMap.ker (bLift i β a h1) := by
  intro t ht
  rw [LinearMap.mem_ker, bLift_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem _ _ (concat_mem_cycL1 i β a h1 hβ
    ((thetaL_eq_zero_iff i β a t).1 ht))

/-- The canonical full-crossing section of the map `B`. -/
noncomputable def bSection : Polynomial Rl →ₗ[k] KOne Q (Si + β) a h1 :=
  (LinearMap.ker (thetaL Q i β a).toLinearMap).liftQ (bLift i β a h1)
      (ker_thetaL_le_bLift i β a h1 hβ) ∘ₗ
    ((thetaL Q i β a).toLinearMap.quotKerEquivOfSurjective
      (thetaL_surjective i β a)).symm.toLinearMap

theorem bSection_thetaL (t : T) :
    bSection i β a h1 hβ (thetaL Q i β a t) = Submodule.Quotient.mk
      (ψw (descRun 0 (Multiset.card β)) * concat Q Si β t) := by
  have he := LinearMap.quotKerEquivOfSurjective_symm_apply
    (f := (thetaL Q i β a).toLinearMap) (thetaL_surjective i β a) t
  change ((LinearMap.ker (thetaL Q i β a).toLinearMap).liftQ (bLift i β a h1)
    (ker_thetaL_le_bLift i β a h1 hβ))
      (((thetaL Q i β a).toLinearMap.quotKerEquivOfSurjective
        (thetaL_surjective i β a)).symm ((thetaL Q i β a).toLinearMap t)) = _
  rw [he, Submodule.liftQ_apply]
  rfl

/-- The section respects right multiplication by cyclotomic constant coefficients. -/
theorem bSection_mul_C (s : Polynomial Rl) (b : KLRAlgebra k Q β) :
    bSection i β a h1 hβ (s * Polynomial.C (CycKLR.mk k Q a β b)) =
      act1 Q i β a h1 b (bSection i β a h1 hβ s) := by
  obtain ⟨t, rfl⟩ := thetaL_surjective i β a s
  rw [← thetaL_one_tmul i β a b, ← map_mul, bSection_thetaL,
    bSection_thetaL, act1_mk, concat_mul, mul_assoc]
  rfl

variable (hsym : KLRSymm Q)

/-- The full-crossing lift is a genuine right inverse of the final-coordinate map. -/
@[simp] theorem bMap_bSection (s : Polynomial Rl) :
    bMap i β hsym a h1 hβ (bSection i β a h1 hβ s) = s := by
  obtain ⟨t, rfl⟩ := thetaL_surjective i β a s
  rw [bSection_thetaL, bMap_top]

include hsym in
theorem bSection_injective : Function.Injective (bSection (Q := Q) i β a h1 hβ) := by
  intro s t h
  have := congrArg (bMap i β hsym a h1 hβ) h
  simpa only [bMap_bSection] using this

/-- The polynomial map obtained by applying `P` to the full-crossing lift and then `C`. -/
noncomputable def aMap : Polynomial Rl →ₗ[k] Polynomial Rl :=
  (cMap i β hsym a hβ).comp
    ((pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β)
      (card_single_add i β).symm).restrictScalars k) ∘ₗ bSection i β a h1 hβ

/-- Formula for `A` on any tensor representative of a cyclotomic polynomial. -/
theorem aMap_thetaL (t : T) :
    aMap i β a h1 hβ hsym (thetaL Q i β a t) = cPoly i β hsym a
      ((ψw (descRun 0 (Multiset.card β)) * concat Q Si β t) *
        tauW a (zero_lt_card_single_add i β) (Multiset.card β)) := by
  change cMap i β hsym a hβ
    (pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β) (card_single_add i β).symm
      (bSection i β a h1 hβ (thetaL Q i β a t))) = _
  rw [bSection_thetaL, pMap_mk, cMap_mk]

/-- Right linearity in the coefficient algebra; no `k[t]`-linearity is claimed. -/
theorem aMap_mul_C (s : Polynomial Rl) (b : Rl) :
    aMap i β a h1 hβ hsym (s * Polynomial.C b) =
      aMap i β a h1 hβ hsym s * Polynomial.C b := by
  obtain ⟨y, rfl⟩ := CycKLR.mk_surjective b
  change cMap i β hsym a hβ
    (pMap a (zero_lt_card_single_add i β) h1 (Multiset.card β) (card_single_add i β).symm
      (bSection i β a h1 hβ (s * Polynomial.C (CycKLR.mk k Q a β y)))) = _
  rw [bSection_mul_C, pMap_act, cMap_act0]
  rfl

end Categorification.KLR.KLRAlgebra
