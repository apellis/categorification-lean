# Deviation register: Webster, arXiv:1309.3796v2

Classes: **identical**, **more general**, **convention**, **erratum-corrected**,
**route hypothesis**, **scope restriction**. Each row compares the spec statement with the
source statement. "README" refers to the erratum and status rows of the repository README.

## Theorem 4.38 (`Spec.Webster.Thm438`)

| # | Item | Source | Spec | Class | Links |
|---|---|---|---|---|---|
| T1 | Side of modules | right projectives `P^κ_i = e(i,κ)T^λ` | right projectives (left word projectives twisted by horizontal reflection) | identical | card word-projectives |
| T2 | Grading shift and `q` | `q` acts on `K₀` and on `V^λ_ℤ` | `η` is semilinear for `q ↦ q⁻¹`, from the shift convention `(M{a})_d = M_{d−a}` | convention | card graded-k0 |
| T3 | Form | `⟨v, w⟩ = ⟨Θ v, w⟩_Ш`, intertwined with the Euler form | Euler form `Hom(x, y)` equals `B(η y, η x)` with `B` the form with the inverse intertwiner on the second argument | erratum-corrected | ERRATA.md entry 10 (form before Prop. 4.33, Lemma 4.36); card ordered-form. The printed form gives `1 + q⁻²` where the graded Hom gives `1 + q²`. The swap of slots is forced: the Euler form is linear in its first argument while the printed form is antilinear there, under either shift convention. Only the remaining `1 + q^{±2}` discrepancy depends on the sign convention for `dim_q` (T2) |
| T4 | Divided powers | Def. 4.34 allows divided powers in `i` | all words with divided-power blocks | identical | card word-projectives |
| T5 | Strands | double Stendhal triples, `DT^λ e₋ = T^λ` | only downward black strands | identical | card word-projectives |
| T6 | `V^λ_ℤ` | tensor product over `ℤ[q,q⁻¹]` of Lusztig integral forms | `ℤ[v,v⁻¹]`-span of pure integral tensors in the rational tensor product | convention | card integral-tensor |
| T7 | Coproduct | Webster's (5.10) | LieLean `comul` (Lusztig's), used by `tensorRepresentation` and the intertwiner | convention | cards integral-tensor, ordered-form |
| T8 | Index set | arbitrary Cartan datum, implicitly finite | `[Finite I]` | scope restriction | — |
| T9 | Root datum | weight lattice of `g` | `R.IsXRegular` root datum, `Dom R` weights, with `hwt` relating `Λ` to `wt` | convention (`hwt`); route hypothesis (`IsXRegular`, needed for the global bases of LieLean) | — |
| T10 | Parameters | `Q_ij` as in §2.2, `rᵢ = 1` | any `Q` with `IsRouquierQ` | identical | card klr-parameters |
| T11 | Uniqueness | "canonical isomorphism" `[P^κ_i] ↦ p^κ_i` | uniqueness among semilinear maps fixing all word classes | identical (word classes span, cf. Lemma 4.37) | — |
| T12 | Ground field | field `k` | `Field k` | identical | — |

## Proposition 5.5 (`Spec.Webster.Prop55`)

| # | Item | Source | Spec | Class | Links |
|---|---|---|---|---|---|
| P1 | Functor | `Eᵢ` and `Fᵢ` filtrations | `Fᵢ` only | scope restriction | README row for Prop. 5.5 |
| P2 | Cut | any `λ¹; …; λᵐ` | `m = 2`, cut before the last red strand | scope restriction | card standardization |
| P3 | Conclusion | filtration with subquotients `S(_kFᵢ M)` (shifted) | `dim Fᵢ S(N) = dim S(₁Fᵢ N) + dim S(₂Fᵢ N)` (total `k`-dimension; the source's (5.14) is for each `Hom(P, −)`) | scope restriction (weaker) | README row for Prop. 5.5 (exactness is stated separately with injectivity as a route hypothesis) |
| P4 | Modules | all graded modules | finite-dimensional `N`, ungraded | scope restriction | — |
| P5 | Parameters | any `Q_ij` | `Q = qCL kl` (Khovanov–Lauda) | scope restriction | ROADMAP item in README row for Prop. 5.5 |
| P6 | Presentation hypotheses | none | none (the library proves the count with the presentation with no relations, `finrank_firstIndF_eq_add`) | identical | — |
| P7 | Standardization | `− ⊗ S` (Def. 5.4) | `ParabolicStandard` (ordered quotient of induction) | convention (model; the comparison is not in the trusted base) | card standardization |
| P8 | Numbering | v2: (5.14) is the `Fᵢ` equation | library docstrings cite v3 "(5.14)–(5.15)" | citation note | — |
| P9 | Side of modules | right modules | left modules | convention | — |

## Corollary 5.21 (`Spec.Webster.Cor521`)

| # | Item | Source | Spec | Class | Links |
|---|---|---|---|---|---|
| C1 | Conclusion | `T^λ` is standardly stratified | the condition on projectives: the kernel of `T^λ e(s) → S_s` has a filtration by `S_t`, `t` strictly above `s` | scope restriction | README row for Cor. 5.22 (v3 numbering) |
| C2 | Indexing | isomorphism classes of indecomposable projectives, dominance order on root functions | red-ordered loadings, `StendhalLT` | convention | card standard-module |
| C3 | Order in Def. 5.1 | printed `≥` | strict `StendhalLT` | erratum-corrected (misprint; the non-strict reading gives `S = 0`) | card standard-module |
| C4 | `U` | defined in `P̃` over `T̃^λ`, then over `T^λ` when `κ(1) = 0` | defined in `T^λ` | identical | card standard-module |
| C5 | Preorder | dominance of root sums left of each red strand | coordinatewise black counts | identical when the simple roots are linearly independent in the weight lattice; otherwise the spec's order is finer | card standard-module |
| C6 | Side of modules | right modules | left modules | convention | — |
| C7 | Parameters | any `Q_ij` | `Q = qCL kl` | scope restriction | README row for Prop. 5.21 / Cor. 5.22 at Khovanov–Lauda scalars |
| C8 | Presentation hypotheses | none | none (`exists_hasFiltration_leftUpper_std` takes only `hR`, `hQs`) | identical | — |
| C9 | Numbering | v2 Cor. 5.21 | library cites v3 Cor. 5.22 | citation note | — |

## Further findings (2026-11-22 review)

Found by restating each result from the source alone and comparing with the spec, then by a
hypothesis-by-hypothesis review of the spec against the source and the trusted base.

| # | Result | Finding | Class | Status |
|---|---|---|---|---|
| T13 | Thm. 4.38 | `TensorFormUnique.lean` cited arXiv v3 locators | citation note | fixed (v2 locators) |
| P10 | Prop. 5.5 | the spec compares `Module.finrank`, which is `0` on an infinite-dimensional module; nothing in the statement says `F_i S(N)`, `S(₁F_i N)`, `S(₂F_i N)` are finite-dimensional. The library proves they are (`firstIndF_restrict_finite` and its siblings) but the spec does not bind it | scope restriction (statement weaker than intended) | open: add the finiteness conjuncts to the spec |
| P11 | Prop. 5.5 | the spec is weaker than the source's own step (5.14), which holds for each `Hom(P, −)` separately; the sum over idempotents loses this | scope restriction (declared in P3; recorded here as weaker than the proof step) | open |
| C10 | Cor. 5.21 | the filtration is proved for `T^λ e(s)`, which is in general decomposable (divided powers, repeated labels). The source's statement is about indecomposable projectives and their standard quotients. Passing from `T^λ e(s)` to each indecomposable summand is an argument the spec neither states nor proves | scope restriction (significant; C2 records only the indexing) | open |
| C11 | Cor. 5.21 | "standardly stratified" also requires that the composition factors of `S_s` are indexed by loadings at or below `s` (asserted in the source's proof of Prop. 5.24). Since `U_s` kills only images from strictly higher loadings, not incomparable ones, this is what makes Def. 5.1's standard modules the standard modules of the general definition. The spec does not bind it | scope restriction (significant; C1 does not name it) | open |
| C12 | Cor. 5.21 | the filtration is ungraded; the grading shifts of Prop. 5.20 are lost | scope restriction | open |
| C13 | Cor. 5.21 | finite-dimensionality of `T^λ_ν`, part of the definition of a standardly stratified algebra, is not a conjunct of the spec | scope restriction | open |
| C14 | Cor. 5.21 | no non-vacuity example applies the spec; `hR`, `hQs` are proved for the Khovanov–Lauda parameters only for the data in the library's existing examples | evidence gap | open |
