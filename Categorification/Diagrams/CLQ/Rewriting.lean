/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.SlideCalculus
import Categorification.Diagrams.KL3.Rewriting

/-!
# The braid relation on upward strands of `U_Q(g)`, in normal form

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1, for the
Cautis–Lauda scalars (S. Cautis, A. D. Lauda, arXiv:1111.1431v3, Definition 1.1, `r = 1`).

`dg_braid`: the braid relation of `R(ν)` (KL III `eq_r3_easy-gen`, `eq_r3_hard-gen` without
correction term) on upward strands, in normal form. The positional rewriting front end
(`NF.dg_swapLR_at`, `NF.dg_step_at`, the tactics `dswapQ`, `datQ`, `NF.dg_interchange`) is in
`Categorification.Diagrams.KL3.NormalForm`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]

/-! ## The braid relation on upward strands -/

variable (RD k sc) in
/-- **KL III `eq_r3_easy-gen`, `eq_r3_hard-gen`** (the cases without correction term, i.e.
unless `c = e ≠ d`): the braid relation `ψ₀ ψ₁ ψ₀ = ψ₁ ψ₀ ψ₁` on upward strands `E_c E_d E_e`,
in normal form (bottom to top). -/
theorem dg_braid (μ : X) (c d e : I) (h : ¬ (c = e ∧ c ≠ d)) :
    NF.dg (pres RD k sc) μ [up c, up d, up e] [up e, up d, up c]
        [([], .cross true c d, [up e]), ([up d], .cross true c e, []),
          ([], .cross true d e, [up c])] =
      NF.dg (pres RD k sc) μ [up c, up d, up e] [up e, up d, up c]
        [([up c], .cross true d e, []), ([], .cross true c e, [up d]),
          ([up e], .cross true c d, [])] := by
  have key := (KLR.Diagram.pres k (CL.qCL sc)).diag_eq_of_rel (.braid c d e h) rfl
  have key' := congrArg (upFunctor RD k sc μ).map key
  rw [upFunctor_diag, upFunctor_diag, upDiag_eq_dg, upDiag_eq_dg] at key'
  exact key'

end Categorification.KL3.Diagram.CLQ
