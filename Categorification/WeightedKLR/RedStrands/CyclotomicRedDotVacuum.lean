/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicRedSingleton

/-!
# The reverse red crossing on the vacuum induction edge

Webster, arXiv:1309.3796v2, §4.5, Theorem 4.25. On the edge from zero black
strands to one, the singleton polynomial coordinates show that the added dot
power kills the kernel of the red quotient. This is the annihilation required
for the reverse crossing on induced modules.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra CyclotomicAction Polynomial PolynomialTrace

variable {I k : Type*} [DecidableEq I] [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) {a b : I → Polynomial k} (hab : ∀ j, a j ∣ b j)

private theorem redProjection_cast {α β : Multiset I} (h : α = β) (z : CycKLR k Q b α) :
    cyclotomicRedProjection Q hab β (castCyc Q b h z) =
      castCyc Q a h (cyclotomicRedProjection Q hab α z) := by
  subst h
  rfl

private theorem singleton_dotPower_kills_kernel (i : I) (d : ℕ) (hi : b i = X ^ d * a i)
    (z : CycKLR k Q b {i}) (hz : cyclotomicRedProjection Q hab {i} z = 0) :
    z * PolynomialTrace.dot Q i b ^ d = 0 := by
  obtain ⟨p, rfl⟩ := eval_surjective Q i b z
  have hp : cyclotomicRedProjection Q hab {i} (eval Q i b p) = eval Q i a p :=
    cyclotomicRedProjection_mk Q hab _
  rw [hp] at hz
  have hRoot := congrArg (cyclotomicSingleEquiv Q i a) hz
  rw [eval_eq, AlgEquiv.apply_symm_apply, map_zero] at hRoot
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_eq_zero.mp hRoot
  have hProd : b i ∣ p * X ^ d := ⟨q, by rw [hi, hq]; ac_rfl⟩
  rw [← PolynomialTrace.eval_X, ← map_pow, ← map_mul, eval_eq,
    AdjoinRoot.mk_eq_zero.mpr hProd, map_zero]

/-- On the vacuum induction edge, the last dot power annihilates the kernel
of the cyclotomic red projection (Webster, arXiv:1309.3796v2, §4.5,
Theorem 4.25). The displayed equality of parameters gives the power of the
new dot at the colour of the added strand. -/
theorem cyclotomicRedDotKernel_zero (i : I) (d : ℕ) (hi : b i = X ^ d * a i)
    (z : CycKLR k Q b ({i} + (0 : Multiset I)))
    (hz : cyclotomicRedProjection Q hab ({i} + 0) z = 0) :
    z * dotElt Q b i (β := 0) rfl ^ d = 0 := by
  let he : ({i} : Multiset I) + 0 = {i} := add_zero _
  apply (castCyc Q b he).injective
  have hd : castCyc Q b he (dotElt Q b i (β := 0) rfl) = PolynomialTrace.dot Q i b := by
    rw [dotElt, castCyc_mk, castKLR_x, PolynomialTrace.dot]
    rfl
  rw [map_mul, map_pow, hd, map_zero]
  apply singleton_dotPower_kills_kernel Q hab i d hi
  rw [redProjection_cast Q hab he, hz, map_zero]

end Categorification.Stendhal
