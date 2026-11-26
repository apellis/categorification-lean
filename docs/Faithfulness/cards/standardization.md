# Standardization at the last red strand and the modules of Proposition 5.5

## Source

Webster, arXiv:1309.3796v2, §5.1:

- Proposition 5.3 and the paragraph after it: the standard modules `S_α` form an
  `(R_{α(0)} ⊗ T^{λ₁}_{α(1)} ⊗ … ⊗ T^{λ_ℓ}_{α(ℓ)}, T̃^λ)`-bimodule `S`.
- Definition 5.4: standardization is `− ⊗ S` from modules over `T^{λ₁} ⊗ … ⊗ T^{λ_ℓ}`;
  partial standardization `S^{λ¹;…;λᵐ}` kills left crossings only for some of the red strands.
- Proposition 5.5, second half: `Fᵢ S^{λ¹;…;λᵐ}(M)` has a filtration `O_m ⊃ … ⊃ O_1` with
  subquotients `S(_kFᵢ M)` up to grading shift. The proof reduces to `m = 2` and to
  equalities of dimensions of `Hom(P, −)` for projectives `P` (displays (5.13) for `Eᵢ`,
  (5.14) for `Fᵢ`).
- Theorem 5.8 identifies standardization with an ordered quotient of induction; the library
  cites it for its model.

## Lean

- `parabolicFactorAlgebra Q Λ θ β` (`ParabolicShuffleAction.lean`): `T^{λ₁…λ_ℓ}_θ ⊗_k
  R^{λ_{ℓ+1}}_β`, the tensor product algebra of the first `ℓ` red strands with black weight
  `θ`, and the cyclotomic KLR algebra of the last red label with black weight `β`.
- `ParabolicShuffle Q Λ θ β N`: KLR induction `Ind` of `N` from the parabolic KLR algebra
  (strands of `θ` with the first `ℓ` reds, then strands of `β` with the last red) to the full
  KLR algebra of `stendhalQ`.
- `excludedSpace ρ F` (`OrderedShuffleRepresentation.lean`): the kernel of the sum of
  idempotents over the red-ordered loadings `F`.
- `ParabolicStandard Q Λ θ β N` (`ParabolicShuffleDescent.lean`): `ParabolicShuffle` modulo
  `excludedSpace`, with the `T^λ` action `parabolicStandardAction`. This is `S(N)` for the
  cut `(λ₁ … λ_ℓ ; λ_{ℓ+1})`.
- `FirstIndF` (`Prop55DimensionCount.lean`): `Fᵢ S(N)`, induction of `S(N)` along adding one
  black `i`-strand on the right.
- `FirstIndStandardT` (`ParabolicStandardLastIndLeft.lean`): `S(₁Fᵢ N)`, where `₁Fᵢ N =
  FirstIndLeft` induces `N` along adding the strand to the first factor.
- `LastIndStandardT` (`ParabolicStandardLastIndMap.lean`): `S(₂Fᵢ N)`, where `₂Fᵢ N =
  LastIndRight` induces along adding the strand to the cyclotomic factor.

## Correspondence

| Source | Lean |
|---|---|
| two-term cut `m = 2` with `λ² = (λ_{ℓ+1})` | `Λ : Fin (ℓ + 1) → …`, cut before the last red strand |
| `V_{λ¹;λ²}`: modules over `T^{λ¹} ⊗ T^{λ²}` | modules over `parabolicFactorAlgebra` (`T^{λ_{ℓ+1}}` with one red strand is the cyclotomic KLR algebra) |
| `S^{λ¹;λ²}(M) = M ⊗ S` | `ParabolicStandard` (ordered quotient of induction) |
| `Fᵢ`, `₁Fᵢ`, `₂Fᵢ` | `FirstIndF`, `FirstIndLeft`, `LastIndRight` |
| `S(₁Fᵢ M)`, `S(₂Fᵢ M)` | `FirstIndStandardT`, `LastIndStandardT` |

## Conventions and review points

- The identification of `ParabolicStandard` with Webster's `− ⊗ S` (Definition 5.4) is a model
  choice justified in the library by its reading of Theorem 5.8 and by
  `twoPieceStandardEquiv` (standardization of `S_t ⊠ R e(u)` is the standard module of the
  concatenated loading). No single comparison theorem with the bimodule `S` is part of the
  trusted base. Reviewers should check that the excluded loadings in `excludedSpace` are
  exactly those that Webster's bimodule kills at the last red strand.
- Left modules (Webster: right modules).
- Only the last-red cut is treated; other cuts and `m > 2` are not stated.

## Sanity checks

- Library: `parabolicStandardUnit_injective` (the identity-shuffle copy of `N` survives),
  `gdimPoly_standardization` (graded character of standardization).
