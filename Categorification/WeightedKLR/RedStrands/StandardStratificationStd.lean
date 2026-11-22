/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StandardProjectiveDimension
import Categorification.WeightedKLR.RedStrands.Prop55DimensionCount

/-!
# Standard filtrations at the standard Khovanov–Lauda scalars

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 5.20 and Corollaries 5.21 and 5.22 (v3: Proposition 5.21 and Corollaries 5.22 and
5.24), at the standard Khovanov–Lauda parameters `Q = CL.qCL KL`. The route hypothesis
`AllFiniteDeltaInjective` of these results is discharged by the dimension count of
Proposition 5.5 (`allFiniteDeltaInjective_std`), at every number of red strands.

## Main results

* `hasStandardFiltrations_std`: Proposition 5.20 (filtration form).
* `exists_hasFiltration_leftUpper_std`: Corollary 5.21 (condition on projectives).
* `exists_hasProjectiveDimensionLT_stdModule_std`: Corollary 5.22 (finite projective dimension).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLRAlgebra TwoRep CyclotomicAction
  DoubleDiagram KL3.Diagram ModuleFiltration

open scoped Classical

variable {I : Type} {C : CartanDatum I} {k : Type} [Field k]
  (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))

include hR

/-- **Projectives have standard filtrations at the standard Khovanov–Lauda parameters**
(Webster, arXiv:1309.3796v2, Proposition 5.20, filtration form). -/
theorem hasStandardFiltrations_std
    (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) {n : ℕ}
    (Λ : Fin n → I →₀ ℕ) :
    HasStandardFiltrations (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ :=
  hasStandardFiltrations _ hQs hR (fun _ _ => allFiniteDeltaInjective_std hR hQs) Λ

/-- **Standard stratification at the standard Khovanov–Lauda parameters** (Webster,
arXiv:1309.3796v2, Corollary 5.21, condition on projectives): the kernel `U_s` of
`T^λ e(s) → S_s` has a finite filtration by standard modules `S_t` with `t` strictly above
`s`. -/
theorem exists_hasFiltration_leftUpper_std
    (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) {n : ℕ}
    (Λ : Fin n → I →₀ ℕ) (ν : Multiset I) (s : Seq (stendhalWeight n ν))
    (hs : IsRedOrdered s) :
    ∃ m : List {t : Seq (stendhalWeight n ν) // IsRedOrdered t},
      (∀ c ∈ m, StendhalLT s c.1) ∧
      HasFiltration (stdModule (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ν) m
        (ModuleCat.of (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ν)
          ((leftUpper (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ s hs).comap
            (lIdeal (seqIdem (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ s hs)).subtype)) :=
  exists_hasFiltration_leftUpper _ hQs hR (fun _ _ => allFiniteDeltaInjective_std hR hQs)
    Λ ν s hs

/-- **Standard modules have finite projective dimension at the standard Khovanov–Lauda
parameters** (Webster, arXiv:1309.3796v2, Corollary 5.22; v3 Corollary 5.24). -/
theorem exists_hasProjectiveDimensionLT_stdModule_std
    (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) {n : ℕ}
    (Λ : Fin n → I →₀ ℕ) (ν : Multiset I) (s : {t : Seq (stendhalWeight n ν) // IsRedOrdered t}) :
    ∃ N : ℕ, CategoryTheory.HasProjectiveDimensionLT
      (stdModule (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ν s) N :=
  exists_hasProjectiveDimensionLT_stdModule _ hQs hR
    (fun _ _ => allFiniteDeltaInjective_std hR hQs) Λ ν s

end Categorification.Stendhal
