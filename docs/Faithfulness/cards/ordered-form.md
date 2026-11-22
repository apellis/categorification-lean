# The form on `V^λ`

## Source

Webster, arXiv:1309.3796v2, §4.7, before Proposition 4.33: `⟨v, w⟩ = ⟨Θ^{(ℓ)} v, w⟩_Ш`, where
`Θ^{(ℓ)}` is the `ℓ`-fold quasi-R-matrix (defined inductively from Lusztig's `Θ`) and `⟨−, −⟩_Ш`
is the factorwise product of the `q`-Shapovalov forms. The form is sesquilinear. Proposition
4.33 characterizes it as the unique system of sesquilinear forms that is nondegenerate,
`τ`-Hermitian, and for which appending `v_{λ_ℓ}` is isometric.

## Lean

- `SingleBlack.websterForm highest hR x y` (`SingleBlackShapovalov.lean`): the bar of Lusztig's
  contravariant form `(x, ȳ)` on `L_q(λ)` (Corollary 3.22 and (3.24) of the source), so that it
  is semilinear in the first argument.
- `TensorPairing.orderedFactorwise hR wt`: the factorwise product of `websterForm`.
- `tensorCoproductEquiv hR wt` (`TensorCoproductWords.lean`): the iterated normalized
  quasi-R-matrix, an isomorphism from the action through the bar coproduct to the action
  through the ordinary coproduct (`tensorCoproductEquiv_act`).
- `TensorPairing.orderedForm hR wt` (`TensorFormOrdered.lean`):
  `B(x, y) = orderedFactorwise(x, tensorCoproductEquiv⁻¹ y)`, semilinear in `x` for the bar
  involution and linear in `y`.

## Correspondence

| Source | Lean |
|---|---|
| factorwise `q`-Shapovalov form `⟨−, −⟩_Ш` | `orderedFactorwise` from `websterForm` |
| `Θ^{(ℓ)}` | `tensorCoproductEquiv` (normalized) |
| `⟨Θ v, w⟩_Ш`: intertwiner on the first argument | `orderedFactorwise(x, Θ'⁻¹ y)`: inverse intertwiner on the second argument |

## Conventions and differences

- The intertwiner acts on the second argument, as its inverse. As printed, the form gives
  `1 + q⁻²` on the first lowering of two fundamental `sl₂` factors, while the corresponding
  graded endomorphism ring has graded dimension `1 + q²`. The library records this as a repair
  of the form (README, erratum row for Proposition 4.33, Lemma 4.36 and Theorem 4.38) and proves
  that the repaired form satisfies Proposition 4.33(2) (`correctedForm_adjoint`). This is under
  separate review; see `DEVIATIONS.md`.
- In the spec of Theorem 4.38 the Euler form `Hom(x, y)` is compared with `B(η y, η x)`: the
  `Hom` target goes to the first argument.
- Values lie in `ℚ(v)` with `v = X`; the comparison with `ℤ((q))` is through Laurent expansion.

## Sanity checks

- Library: `orderedForm_empty`, `orderedFactorwise_append` (appending a factor multiplies by the
  one-factor form), `printedForm_loweredPair`, `terminal_homGdimPoly_ne_printedForm`.
