/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.TwistTensor
import Categorification.KLR.BarK0

/-!
# KL I's form on `K₀(R(ν))` as `gdim (P^ψ ⊗_{R(ν)} Q)`

Khovanov–Lauda I (arXiv:0803.4121v2), §2.5, equations `eq_bil_pair2`, `eq-bil-ten` (TeX lines
~1558–1580): the bilinear form on `K₀(R(ν))` is `([P], [Q]) = gdim (P^ψ ⊗_{R(ν)} Q)`, and
`([P_j], [P_i]) = gdim (_jP ⊗_{R(ν)} P_i) = gdim (1_j R(ν) 1_i)`.

By `Categorification.Algebra.Graded.TwistTensor`, `P^ψ ⊗_{R(ν)} Q ≅ HOM(P̄, Q)` as graded vector
spaces, so the paper's form is the library's `K0.pform (G.grade ν) (G.psi hsymm ν)` on all of
`K₀(R(ν))` (`K0.pform_of_eq_gdim_twistTensor`, `K0.eq_pform_of_gdim_twistTensor`); it is
`ℤ[q, q⁻¹]`-bilinear and symmetric, and `homForm x y = pform x̄ y`. Here we record the values on
the modules `P_i`:

* `GradingDatum.gdim_twistTensor_projP` : `gdim (P_j^ψ ⊗_{R(ν)} P_i) = gdim (1_j R(ν) 1_i)`;
* `KL1.gdim_twistTensor_projP` : for KL I, the explicit value
  `∑_{w • i = j} q^{-∑_{(a,b) ∈ inv(w)} i_a · i_b} (1 - q²)^{-m}`.
-/

noncomputable section

namespace Categorification.KLR

open Categorification.Graded KLRAlgebra TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}

namespace GradingDatum

variable (G : GradingDatum Q) (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a) {ν : Multiset I}
  [HasGdim (G.grade ν)]

/-- **KL I, §2.5** (display after `eq-bil-ten`):
`([P_j], [P_i]) = gdim (P_j^ψ ⊗_{R(ν)} P_i) = gdim (1_j R(ν) 1_i)`. -/
theorem gdim_twistTensor_projP (j i : Seq ν) :
    gdim (twistTensorGrading (G.psi hsymm ν) (G.projP j).grading (G.projP i).grading) =
      gdim (G.cornerGrade j i) := by
  rw [← K0.pform_of_eq_gdim_twistTensor, pform_projP]

end GradingDatum

namespace KL1

variable {Γ : SimpleGraph I} [DecidableRel Γ.Adj]

/-- **KL I, §2.5**: `gdim (P_j^ψ ⊗_{R(ν)} P_i) = ∑_{w • i = j} q^{-∑_{inv(w)} i_a · i_b}
(1 - q²)^{-m}`. -/
theorem gdim_twistTensor_projP {ν : Multiset I} (j i : Seq ν) :
    gdim (twistTensorGrading (psi k Γ ν) ((klGradingDatum k Γ).projP j).grading
      ((klGradingDatum k Γ).projP i).grading) =
      ∑ w ∈ Finset.univ.filter (fun w => w • i = j),
        HahnSeries.single (-∑ p ∈ invSet (Multiset.card ν) w, cartan Γ (i.lbl p.1) (i.lbl p.2)) 1 *
          geomSeries 2 ^ Multiset.card ν := by
  rw [← K0.pform_of_eq_gdim_twistTensor, pform_projP]

end KL1

end Categorification.KLR
