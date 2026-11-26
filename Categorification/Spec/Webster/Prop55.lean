/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Prop55DimensionCount

/-!
# Specification: the dimension count in Webster, arXiv:1309.3796v2, Proposition 5.5

Source: B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§5.1, Proposition 5.5, and its proof, equation (5.14) (the `F_i` half).

Paraphrase of the source. For a cut of `λ` into two consecutive blocks `λ¹; λ²` and a module
`M` over `T^{λ¹} ⊗ T^{λ²}`, the standardization `S^{λ¹;λ²}(M)` satisfies: `F_i S(M)` has a
two-step filtration whose subquotients are shifts of `S(₁F_i M)` and `S(₂F_i M)` (where `ₖF_i`
acts on the `k`-th factor). The proof reduces this to a dimension count: for every projective
`P`, `dim Hom(P, F_i S(M)) = dim Hom(P, S(₁F_i M)) + dim Hom(P, S(₂F_i M))` (5.14).

The library proves the count in the following form, which is what this file binds:
* the cut is the one before the last red strand (`λ¹ = (λ₁, …, λ_ℓ)`, `λ² = (λ_{ℓ+1})`), which
  is the case the source's reduction to `m = 2` uses at its last step;
* `dim` is the total `k`-dimension (equivalently, (5.14) summed over a complete set of
  idempotents `e`, `P = T e`), for finite-dimensional `M`, ungraded;
* the parameters are the standard Khovanov–Lauda ones, `Q = CL.qCL KL`.
See `docs/Faithfulness/DEVIATIONS.md` for each restriction.

Nothing in the library imports this file. Changes to it need the maintainer's approval.

## Trusted base

* `TensorProductAlgebra`, `stendhalWeight`: the algebra `T^λ` in a black content
  (card `tensor-product-algebra.md`).
* `parabolicFactorAlgebra Q Λ θ β`: the algebra `T^{λ¹}_θ ⊗ T^{λ²}_β` at the cut
  (card `standardization.md`).
* `FirstIndF`: `F_i S(M)`; `FirstIndStandardT`: `S(₁F_i M)`; `LastIndStandardT`: `S(₂F_i M)`
  (card `standardization.md`).
* `CL.qCL CL.CLScalars.kl`: the standard Khovanov–Lauda polynomials `Q_ij`
  (card `klr-parameters.md`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Spec.Webster.Prop55

open Categorification.Stendhal
open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR KLRAlgebra TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite
  ModuleFiltration

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/- Source data (§2.1, §4, §5.1): the Cartan datum `C`, the field `k`, the standard
Khovanov–Lauda parameters with the conditions on `Q_ij` (`hR`, and the symmetry `hQs`), the
sequence `Λ = (λ₁, …, λ_{ℓ+1})` of dominant weights. -/
variable {I : Type} {ℓ : ℕ} {Λ : Fin (ℓ + 1) → I →₀ ℕ} {C : CartanDatum I}
  {k : Type} [Field k] {hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))}

/- The symmetry of the parameters, `Q_ij(u, v) = Q_ji(v, u)` (§2.2). -/
variable (hQs : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))

/- The data of Proposition 5.5: a colour `i`, black contents `θ` (left of the cut) and `β`
(right of the cut), and a module `N` over `T^{λ¹}_θ ⊗ T^{λ²}_β`. -/
variable (i : I) (θ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ
    θ β) N]

variable (hR) in
include hR in
/-- **Webster, arXiv:1309.3796v2, proof of Proposition 5.5, (5.14), summed over idempotents.**
For a finite-dimensional module `N` at the cut before the last red strand,
`dim F_i S(N) = dim S(₁F_i N) + dim S(₂F_i N)`. -/
theorem dimension_count [FiniteDimensional k N] :
    Module.finrank k (FirstIndF (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ i θ β N hQs) =
      Module.finrank k
          (FirstIndStandardT (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ i θ β N hQs) +
        Module.finrank k
          (LastIndStandardT (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ i θ β N hQs) :=
  finrank_firstIndF_eq_add hR hQs i θ β N

end Categorification.Spec.Webster.Prop55
