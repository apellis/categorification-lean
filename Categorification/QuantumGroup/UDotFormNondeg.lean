/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotKL3

/-!
# The statement of KL III Proposition 2.5 over `ℚ(q)`

Khovanov–Lauda III, arXiv:0807.3250v1, §2.1.3, **Proposition 2.5** (TeX label `prop_nondeg`):
"The bilinear form `( , )` and the semilinear form `⟨ , ⟩` are both nondegenerate on `U̇`"
(KL III: "Nondegeneracy of `( , )` is implicit throughout [Lusztig, Chapter 26] and follows for
instance from Theorem 26.3.1").

This file only records the statement, as a proposition about the root datum, so that results
depending on it (KL III Theorem 1.2, `Categorification.Diagrams.KL3.Injectivity`) can take it as
an explicit hypothesis:

* `UDot.KL3.FormNondeg RD` — `( , )` (`UDot.KL3.form RD`) has zero left radical on `U̇`;
* `UDot.KL3.sform_nondeg` — then `⟨ , ⟩` (`UDot.KL3.sform RD`) has zero left radical too (the
  second half of Proposition 2.5, from `UDot.nondegenerate_hform_of_formUD`).

Since `( , )` is symmetric (property (v)), zero left radical is the same as nondegeneracy.
-/

noncomputable section

namespace Categorification.QuantumGroup

namespace UDot

namespace KL3

variable {I : Type*} {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-- **KL III Proposition 2.5 for `( , )` over `ℚ(q)`** (as a statement): the bilinear form
`( , )` of Proposition 2.2 on `U̇` is nondegenerate, i.e. `(x, y) = 0` for all `y` forces
`x = 0`. -/
def FormNondeg (RD : RootDatum C X Y) : Prop :=
  ∀ x : UD RD qK, (∀ y : UD RD qK, form RD x y = 0) → x = 0

theorem formNondeg_iff (RD : RootDatum C X Y) :
    FormNondeg RD ↔ Nondegenerate (form RD) := Iff.rfl

/-- **KL III Proposition 2.5 for `⟨ , ⟩`, given the statement for `( , )`**. -/
theorem sform_nondeg {RD : RootDatum C X Y} (h : FormNondeg RD) (x : UD RD qK)
    (hx : ∀ y, sform RD x y = 0) : x = 0 :=
  nondegenerate_hform_of_formUD RD qK (cK C) hqK barQ barQ_vQ barQ_barQ h x hx

end KL3

end UDot

end Categorification.QuantumGroup
