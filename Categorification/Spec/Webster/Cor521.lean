/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StandardStratificationStd

/-!
# Specification: Webster, arXiv:1309.3796v2, Corollary 5.21

Source: B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§5.4, Corollary 5.21 (with Definition 5.1 for standard modules and the preorder preceding it,
and Proposition 5.20). In arXiv:1309.3796v3 the same statement is Corollary 5.22.

Paraphrase of the source. `T^λ` is standardly stratified: the standard modules are the
standard quotients `S^κ_i` of the indecomposable projectives `P^κ_i` (Definition 5.1), and the
preorder is dominance of root functions (the preorder preceding Definition 5.1). The defining
condition on projectives is that the kernel of `P^κ_i → S^κ_i` has a finite filtration whose
subquotients are standard modules for strictly higher indices.

The library proves the condition on projectives, which is what this file binds, in this form:
* modules are left `T^λ`-modules; the projective attached to a red-ordered loading `s` is
  `T^λ e(s)`, its standard quotient is `S_s = T^λ e(s) / U_s` with `U_s` spanned by the
  `e(t) a e(s)` for `t` strictly above `s` (card `standard-module.md`);
* standard modules and the order are indexed by loadings (Stendhal triples) rather than by
  isomorphism classes of indecomposable projectives;
* the parameters are the standard Khovanov–Lauda ones, `Q = CL.qCL KL`, with the symmetry
  `hQs`.
See `docs/Faithfulness/DEVIATIONS.md`.

Nothing in the library imports this file. Changes to it need the maintainer's approval.

## Trusted base

* `TensorProductAlgebra`, `stendhalWeight`, `Seq`, `IsRedOrdered`, `seqIdem`: the algebra
  `T^λ_ν` and the idempotents `e(s)` of red-ordered loadings (card `tensor-product-algebra.md`).
* `StendhalLE`, `StendhalLT`: Webster's preorder and its strict part (card `standard-module.md`).
* `leftUpper`, `stdModule`, `lIdeal`: `U_s`, `S_s` and `T^λ e(s)` (card `standard-module.md`).
* `ModuleFiltration.HasFiltration`: finite filtrations with prescribed subquotients
  (card `standard-module.md`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Spec.Webster.Cor521

open Categorification.Stendhal
open QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLRAlgebra TwoRep CyclotomicAction
  DoubleDiagram KL3.Diagram ModuleFiltration

open scoped Classical

/-- **Webster, arXiv:1309.3796v2, Corollary 5.21 (condition on projectives).** Let `C` be a
Cartan datum and `k` a field, with the standard Khovanov–Lauda parameters `Q_ij` (`hR`, `hQs`).
For red strands `λ = (λ₁, …, λ_n)`, black content `ν` and a red-ordered loading `s`, the kernel
`U_s` of `T^λ e(s) → S_s` has a finite filtration whose subquotients are standard modules `S_t`
with `t` strictly above `s` in Webster's preorder. -/
theorem standard_filtration_of_kernel {I : Type} {C : CartanDatum I} {k : Type} [Field k]
    (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
    (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
    {n : ℕ} (Λ : Fin n → I →₀ ℕ) (ν : Multiset I) (s : Seq (stendhalWeight n ν))
    (hs : IsRedOrdered s) :
    ∃ m : List {t : Seq (stendhalWeight n ν) // IsRedOrdered t},
      (∀ c ∈ m, StendhalLT s c.1) ∧
      HasFiltration (stdModule (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ν) m
        (ModuleCat.of (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ν)
          ((leftUpper (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ s hs).comap
            (lIdeal (seqIdem (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ s hs)).subtype)) :=
  exists_hasFiltration_leftUpper_std hR hQs Λ ν s hs

end Categorification.Spec.Webster.Cor521
