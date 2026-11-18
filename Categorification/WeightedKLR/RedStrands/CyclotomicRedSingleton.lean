/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicRedPullback
import Categorification.KLR.CyclotomicPolynomialTrace

/-!
# The two red crossings on the singleton cyclotomic block

Webster, arXiv:1309.3796v2, §4.5, Theorem 4.25 and (4.5).
On the vacuum induction edge the two crossings are the cyclotomic quotient
and multiplication of a polynomial lift by the new dot power. Their composites
give the two red/black bigons in §4.1, Definition 4.5, equation (4.2).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra Polynomial PolynomialTrace

variable {I k : Type*} [DecidableEq I] [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (n d : I → ℕ)

local notation "lo" => (fun j => (X ^ n j : Polynomial k))
local notation "hi" => (fun j => (X ^ (n j + d j) : Polynomial k))

omit [DecidableEq I] in
/-- The inclusion of defining ideals for an increase of highest weight. -/
theorem redPower_dvd (j : I) : (X ^ n j : Polynomial k) ∣ X ^ (n j + d j) :=
  ⟨_, pow_add _ _ _⟩

local notation "π" => cyclotomicRedProjection Q (redPower_dvd (k := k) n d) (Singleton.singleton i)

/-- The reverse red crossing on the singleton block. It raises the exponent
of each polynomial representative by the added coroot multiplicity. -/
def singletonRedDotCrossing : CycKLR k Q lo {i} →ₗ[k] CycKLR k Q hi {i} :=
  ((eval Q i hi).toLinearMap.comp (LinearMap.mulLeft k (X ^ d i))).comp
    ((AdjoinRoot.modByMonicHom (monic_X_pow (R := k) (n i))).comp
      (cyclotomicSingleEquiv Q i lo).toLinearMap)

theorem singletonRedDotCrossing_eval (p : Polynomial k) :
    singletonRedDotCrossing Q i n d (eval Q i lo p) = eval Q i hi (X ^ d i * p) := by
  change eval Q i hi (X ^ d i * AdjoinRoot.modByMonicHom (monic_X_pow (R := k) (n i))
    (cyclotomicSingleEquiv Q i lo (eval Q i lo p))) = _
  rw [eval_eq Q i lo, AlgEquiv.apply_symm_apply, AdjoinRoot.modByMonicHom_mk]
  apply (cyclotomicSingleEquiv Q i hi).injective
  simp only [eval_eq, AlgEquiv.apply_symm_apply, AdjoinRoot.mk_eq_mk]
  refine ⟨-(p /ₘ (X ^ n i)), ?_⟩
  rw [modByMonic_eq_sub_mul_div, pow_add]
  ring

private theorem redProjection_eval (p : Polynomial k) : π (eval Q i hi p) = eval Q i lo p :=
  cyclotomicRedProjection_mk Q _ _

/-- A bigon on the lower-weight side acts by the added dot power. -/
theorem singletonRedProjection_dotCrossing (z : CycKLR k Q lo {i}) :
    π (singletonRedDotCrossing Q i n d z) = dot Q i lo ^ d i * z := by
  obtain ⟨p, rfl⟩ := eval_surjective Q i lo z
  rw [singletonRedDotCrossing_eval, redProjection_eval, map_mul, map_pow, PolynomialTrace.eval_X]

/-- The bigon on the higher-weight side has the same dot power. -/
theorem singletonRedDotCrossing_projection (z : CycKLR k Q hi {i}) :
    singletonRedDotCrossing Q i n d (π z) = dot Q i hi ^ d i * z := by
  obtain ⟨p, rfl⟩ := eval_surjective Q i hi z
  rw [redProjection_eval, singletonRedDotCrossing_eval, map_mul, map_pow, PolynomialTrace.eval_X]

/-- The reverse crossing is linear for the higher cyclotomic algebra, acting
on the lower weight by pullback through the quotient. -/
theorem singletonRedDotCrossing_mul (r : CycKLR k Q hi {i}) (z : CycKLR k Q lo {i}) :
    singletonRedDotCrossing Q i n d (π r * z) = r * singletonRedDotCrossing Q i n d z := by
  obtain ⟨p, rfl⟩ := eval_surjective Q i hi r
  obtain ⟨q, rfl⟩ := eval_surjective Q i lo z
  rw [redProjection_eval, ← map_mul, singletonRedDotCrossing_eval, singletonRedDotCrossing_eval,
    ← map_mul, mul_left_comm]

end Categorification.Stendhal
