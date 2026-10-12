/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicAdjunction
import Categorification.KLR.CyclotomicMixedInversionDescent

/-!
# Cyclotomic weight transport

Actual quotient weight equivalences identify the last inclusion with the concatenation
inclusion used by the distinct-colour crossing equivalence.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.MixedTransport
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)

/-- Equality transport of the actual cyclotomic algebra. -/
def weightEquiv {β δ : Multiset I} (h : β = δ) : CycKLR k Q a β ≃ₐ[k] CycKLR k Q a δ := by
  subst δ
  exact AlgEquiv.refl

@[simp] theorem weightEquiv_mk {β δ : Multiset I} (h : β = δ) (x : KLRAlgebra k Q β) :
    weightEquiv Q a h (CycKLR.mk k Q a β x) =
      CycKLR.mk k Q a δ (castKLR Q h x) := by
  subst δ
  rfl

/-- The accepted quotient inclusion is the original inclusion after weight transport. -/
theorem last_eq_weight_inc (γ : Multiset I) (i : I) (r : CycKLR k Q a γ) :
    cyclotomicLast Q i a γ r =
      weightEquiv Q a (add_comm γ {i}) (MixedCyclotomic.quotientInc Q a γ i r) := by
  obtain ⟨r, rfl⟩ := CycKLR.mk_surjective r
  rw [cyclotomicLast_mk, MixedCyclotomic.quotientInc_mk, weightEquiv_mk]
  rfl

end Categorification.KLR.KLRAlgebra.AbsentColour.MixedTransport
