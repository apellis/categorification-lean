# The integral tensor product `V^λ_ℤ` and the vectors `p^κ_i`

## Source

Webster, arXiv:1309.3796v2: `V^λ_ℤ` is the tensor product over `ℤ[q, q⁻¹]` of Lusztig's
integral forms of the irreducible modules `V^{λ_m}` (§1). The vectors `p^κ_i` (§4.7, before
Lemma 4.36) are defined recursively along the word: adding a red strand on the right tensors
with the highest weight vector `v_{λ_ℓ}`; adding a black `i`-strand applies `Fᵢ` (or a divided
power `Fᵢ^{(a)}`) through the coproduct.

## Lean

- `Stendhal.TensorSpace wt` (`FirstWeightTensor.lean`): `⨂_{j} L_q(wt j)` over `𝕂 = ℚ(v)`, the
  irreducible highest-weight modules of LieLean at `v = X`.
- `integralTensor wt`: the `ℤ[v, v⁻¹]`-span of pure tensors of vectors in the integral forms
  `hwIntegral (wt j)`.
- `tensorWordVector w wt` (`TensorGenerators.lean`): `empty ↦ ⊗ v_{λ_j}` (no factors when
  `ℓ = 0`); `red w ↦ appendTensor (tensorWordVector w) v_{λ_last}`;
  `black w i a ↦ Fᵢ^{(a)}` acting through `tensorRepresentation`.
- `tensorRepresentation wt` (`TensorAction.lean`): the action of `U_q` on the tensor product by
  the iterated coproduct `comul` of LieLean (Lusztig's coproduct).
- `integralWordVector wt w`: `tensorWordVector w wt` as an element of `integralTensor wt`.

## Correspondence

| Source | Lean |
|---|---|
| `V^λ_ℤ = ⊗_ℤ[q,q⁻¹] V^{λ_m}_ℤ` | `integralTensor`, the span of pure integral tensors inside the rational tensor product |
| append red: `⊗ v_{λ_ℓ}` | `appendTensor … (hwv …)` |
| append black `i`: apply `Fᵢ` (divided powers allowed) | `tensorRepresentation (qDivPow … Fᵢ)` |
| `p^κ_i` | `tensorWordVector w`, `integralWordVector w` |

## Conventions

- `V^λ_ℤ` is modelled as a sublattice of the rational tensor product, not as an abstract tensor
  product over `ℤ[v, v⁻¹]`. The two agree because Lusztig's integral forms are free and their
  rational spans are the rational modules; the identification is a modelling choice to review.
- Coproduct: LieLean's `comul`. Webster's (5.10) displays `Δ(Fᵢ) = Σ 1 ⊗ … ⊗ Fᵢ ⊗ K̃_{−i} ⊗ …`.
  Reviewers should check that `comul` places `K` factors on the same side.
- `Dom R`: dominant weights of an `X`-regular root datum; `hwt` ties the red labels `Λ r i` to
  the pairings `⟨wt r, αᵢ^∨⟩`.

## Sanity checks

- `scripts/NonVacuity.lean` (Thm. 4.38 examples with two fundamental factors).
