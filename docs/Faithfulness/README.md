# Faithfulness review: Webster, arXiv:1309.3796v2, §§4–5

This directory records how three results of Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v2, are stated in Lean, and how each object in
those statements corresponds to the source definition.

| Result (v2 numbering) | Spec file | Declarations |
|---|---|---|
| Theorem 4.38 | `Categorification/Spec/Webster/Thm438.lean` | `Spec.Webster.Thm438.existence`, `Spec.Webster.Thm438.uniqueness` |
| Proposition 5.5, `Fᵢ` part, equation (5.14) | `Categorification/Spec/Webster/Prop55.lean` | `Spec.Webster.Prop55.dimension_count` |
| Corollary 5.21, condition on projectives | `Categorification/Spec/Webster/Cor521.lean` | `Spec.Webster.Cor521.standard_filtration_of_kernel` |

Layout:

- `Categorification/Spec/Webster/*.lean`: one spec file per result. Each states the result with
  the hypotheses in source order, with locators, and binds it to the library proof by a
  `theorem`. Spec files are not imported by `Categorification.lean`; they are built by the
  `andSubmodules` glob and imported by `scripts/AxiomAudit.lean`, so their axioms are audited.
- `cards/*.md`: one definition card per object of the trusted base (the definitions a reader
  must trust to read the spec statement). Each card gives the source definition (paraphrased,
  with locator), the Lean definition, a line-by-line correspondence, the conventions, and the
  sanity checks.
- `DEVIATIONS.md`: every difference between a spec statement and the source, classified as
  identical, more general, convention, erratum-corrected, route hypothesis or scope restriction.
- `scripts/Faithfulness/TrustedBase.lean`: prints, for each spec theorem, the project
  definitions reachable from its statement (types and definition bodies, not proofs).
- `scripts/Faithfulness/WebsterSanity.lean`: small checks on the definitions of the cards.

CI runs every file in `scripts/Faithfulness/` with warnings as errors.

Cards:

| Card | Objects |
|---|---|
| [klr-parameters](cards/klr-parameters.md) | `IsRouquierQ`, `CL.qCL`, `CL.CLScalars.kl`, `KLRSymm` |
| [tensor-product-algebra](cards/tensor-product-algebra.md) | `stendhalQ`, `StendhalAlgebraAllOrders`, `StendhalAlgebra`, `IsRedOrdered`, `violatedIdeal`, `TensorProductAlgebra`, `tensorProductGrade` |
| [graded-k0](cards/graded-k0.md) | `GProj`, `K0`, `oppositeGrade`, `K0.homForm`, `GProj.rightTwist` |
| [word-projectives](cards/word-projectives.md) | `TensorWord`, `tensorWordProjective`, `rightTensorWordProjective`, `rightTensorWordProjectiveClass`, `rightTensorProjectiveGroup` |
| [integral-tensor](cards/integral-tensor.md) | `TensorSpace`, `integralTensor`, `tensorWordVector`, `integralWordVector` |
| [ordered-form](cards/ordered-form.md) | `TensorPairing.orderedForm`, `SingleBlack.websterForm`, `tensorCoproductEquiv` |
| [standard-module](cards/standard-module.md) | `blackCount`, `StendhalLE`, `StendhalLT`, `seqIdem`, `leftUpper`, `leftStandard`, `stdModule`, `ModuleFiltration.HasFiltration` |
| [standardization](cards/standardization.md) | `parabolicFactorAlgebra`, `ParabolicShuffle`, `excludedSpace`, `ParabolicStandard`, `FirstIndF`, `FirstIndStandardT`, `LastIndStandardT` |
