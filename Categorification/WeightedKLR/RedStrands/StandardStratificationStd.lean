/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StandardStratification
import Categorification.WeightedKLR.RedStrands.Prop55DimensionCount

/-!
# Standard filtrations at the standard Khovanov–Lauda scalars

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.21 and Corollary 5.22, at the standard Khovanov–Lauda parameters `Q = CL.qCL KL`.
The route hypothesis `AllFiniteDeltaInjective` of these results is discharged by the dimension
count of Proposition 5.5 (`allFiniteDeltaInjective_std`).

## Hypotheses

The dimension count takes, for each cyclotomic datum that occurs, a presentation `P` of the
cyclotomic cover with `CoverRelsNegligible` and well-founded domain (`P.WFDom`): hypotheses on
the choice of presentation used to prove Theorem 4.31, not hypotheses of Webster's statements.
Since Proposition 5.21 and Corollary 5.22 recurse over the number of red strands, the statements
here take such a presentation for every cyclotomic datum (`CoverPresentations`).

## Main results

* `allFiniteDeltaInjective_of_coverPresentations`: the route hypothesis at every number of red
  strands.
* `hasStandardFiltrations_std`: Proposition 5.21 (filtration form).
* `exists_hasFiltration_leftUpper_std`: Corollary 5.22 (condition on projectives).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLRAlgebra TwoRep CyclotomicAction
  DoubleDiagram KL3.Diagram ModuleFiltration

open scoped Classical

variable {I : Type} {C : CartanDatum I} {k : Type} [Field k]
  (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))

/-- For every cyclotomic datum `Λ`, a presentation of the cyclotomic cover with
`CoverRelsNegligible` and well-founded domain: the hypotheses on the choice of presentation of
the dimension count of Proposition 5.5 (`finrank_firstIndF_eq_add`). -/
def CoverPresentations : Prop :=
  ∀ (m : ℕ) (Λ : Fin m → I →₀ ℕ),
    ∃ P : Presentation.{0, 0}
        (signature (coordinateDatum Λ C)
          (redWeight (cyclotomicCoverWeightDatum Λ C))) k,
      CoverRelsNegligible.{0, 0, 0} Λ C hR (coverDotCentral Λ C hR)
        (blockWeight (cyclotomicCoverWeightDatum Λ C)
          (cyclotomicCoverHighest (I := I) (ℓ := m)) 0 : I ⊕ Fin m → ℤ) P ∧ P.WFDom

variable {hR}

/-- The route hypothesis `AllFiniteDeltaInjective` of Proposition 5.21 holds at the standard
Khovanov–Lauda parameters for every number of red strands, given `CoverPresentations`. -/
theorem allFiniteDeltaInjective_of_coverPresentations (hP : CoverPresentations hR)
    (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) (n : ℕ)
    (Λ : Fin (n + 1) → I →₀ ℕ) :
    AllFiniteDeltaInjective (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ hQs := by
  obtain ⟨P, hP₀, hwf₀⟩ := hP (n + 1) Λ
  obtain ⟨P₁, hP₁, hwf₁⟩ := hP n (Λ ∘ Fin.castSucc)
  obtain ⟨P₂, hP₂, hwf₂⟩ := hP 1 (fun _ => Λ (Fin.last n))
  exact allFiniteDeltaInjective_std hP₀ hwf₀ hP₁ hwf₁ hP₂ hwf₂ hQs

/-- **Projectives have standard filtrations at the standard Khovanov–Lauda parameters**
(Webster, arXiv:1309.3796v3, Proposition 5.21, filtration form), given the presentation
hypotheses `CoverPresentations` of the dimension count. -/
theorem hasStandardFiltrations_std (hP : CoverPresentations hR)
    (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) {n : ℕ}
    (Λ : Fin n → I →₀ ℕ) :
    HasStandardFiltrations (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ :=
  hasStandardFiltrations _ hQs hR (allFiniteDeltaInjective_of_coverPresentations hP hQs) Λ

/-- **Standard stratification at the standard Khovanov–Lauda parameters** (Webster,
arXiv:1309.3796v3, Corollary 5.22, condition on projectives): the kernel `U_s` of
`T^λ e(s) → S_s` has a finite filtration by standard modules `S_t` with `t` strictly above `s`,
given the presentation hypotheses `CoverPresentations` of the dimension count. -/
theorem exists_hasFiltration_leftUpper_std (hP : CoverPresentations hR)
    (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) {n : ℕ}
    (Λ : Fin n → I →₀ ℕ) (ν : Multiset I) (s : Seq (stendhalWeight n ν))
    (hs : IsRedOrdered s) :
    ∃ m : List {t : Seq (stendhalWeight n ν) // IsRedOrdered t},
      (∀ c ∈ m, StendhalLT s c.1) ∧
      HasFiltration (stdModule (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ν) m
        (ModuleCat.of (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ν)
          ((leftUpper (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ s hs).comap
            (lIdeal (seqIdem (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ s hs)).subtype)) :=
  exists_hasFiltration_leftUpper _ hQs hR (allFiniteDeltaInjective_of_coverPresentations hP hQs)
    Λ ν s hs

end Categorification.Stendhal
