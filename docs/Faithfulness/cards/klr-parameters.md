# KLR parameters `Q_ij`

## Source

Webster, arXiv:1309.3796v2, §2.2, opening paragraph (p. 8 of the arXiv PDF). For each pair of
colours `i ≠ j` a polynomial `Q_ij(u, v)` over the ground field is fixed, with `Q_ii = 0` by
convention. Conditions:

1. `Q_ij` is homogeneous of degree `−⟨αᵢ, αⱼ⟩ = −2dᵢcᵢⱼ` when `u` has degree `2dᵢ` and `v` has
   degree `2dⱼ`;
2. its leading order in `u` is `−cᵢⱼ`, with leading coefficient `tᵢⱼ = Qᵢⱼ(1, 0)`;
3. `Qᵢⱼ(u, v) = Qⱼᵢ(v, u)`.

Here `cᵢⱼ` is the Cartan matrix. The Cautis–Lauda parameter `rᵢ` is set to `1` throughout.
The Khovanov–Lauda choice is `Qᵢⱼ = u^{−cᵢⱼ} + v^{−cⱼᵢ}`.

Source note: §2.2 writes `⟨αᵢ, αⱼ⟩ = 2dᵢcᵢⱼ`, while Definition 4.4 assigns degree
`⟨αᵢ, αᵢ⟩ = 2dᵢ` to a dot. The two normalizations differ by a factor of two. The Lean side uses
one normalization throughout (below), which agrees with Definition 4.4 for dots and with the
§2.2 degree of `Qᵢⱼ` measured against dot degree `2dᵢ`.

## Lean

- `Categorification.KLR.IsRouquierQ C Q` (`Categorification/KLR/Rouquier/Polynomial.lean`):
  - `symm`: for `i ≠ j`, swapping the two variables of `Q i j` gives `Q j i`;
  - `homogeneous`: for `i ≠ j`, `Q i j` is weighted homogeneous with weights
    `(C.dot i i, C.dot j j)` of degree `−2 · C.dot i j`;
  - `unit_coeff`: for `i ≠ j`, the coefficient of `u^{dᵢⱼ}` is a unit.
- `Categorification.KL3.Diagram.CL.qCL S` (`Categorification/Diagrams/CL/Scalars.lean`): the
  Cautis–Lauda polynomial `tᵢⱼ u^{dᵢⱼ} + tⱼᵢ v^{dⱼᵢ} + Σ sᵢⱼ^{pq} u^p v^q`, or `tᵢⱼ` when
  `i · j = 0`.
- `CL.CLScalars.kl`: `t = 1`, `s = 0`, `r = 1`; so `qCL kl` is the Khovanov–Lauda choice.
- `KLR.KLRSymm Q`: the symmetry condition alone.

## Correspondence

| Source | Lean |
|---|---|
| `u` of degree `2dᵢ`, `v` of degree `2dⱼ` | weights `C.dot i i`, `C.dot j j` (`C.dot i i = 2dᵢ`) |
| degree `−⟨αᵢ, αⱼ⟩` | `−2 · C.dot i j` against those weights (`C.dot i j = dᵢcᵢⱼ`), i.e. `−2dᵢcᵢⱼ` |
| leading order `−cᵢⱼ` in `u`, `tᵢⱼ` its coefficient | coefficient of `u^{dᵢⱼ}` (`dᵢⱼ = −cᵢⱼ`) is a unit; homogeneity forces it to be the top `u`-power (`IsRouquierQ.support_bound`) |
| `tᵢⱼ` nonzero (implicit; over a field) | `IsUnit` (equivalent over a field) |
| `Qᵢⱼ(u, v) = Qⱼᵢ(v, u)` | `symm` |
| `Qᵢᵢ = 0` | not imposed; the diagonal value is not used by the KLR relations in the library |

## Conventions

- Over a field `k` (Webster's ground field) `IsUnit` is the same as nonzero.
- The results bound in this pilot are, for Prop. 5.5 and Cor. 5.21, only at
  `Q = qCL kl` (see `DEVIATIONS.md`). Thm. 4.38 takes an arbitrary `Q` with `IsRouquierQ`.

## Sanity checks

- `scripts/NonVacuity.lean` instantiates `IsRouquierQ` at concrete data for Thm. 4.38
  (`rightTensorModuleEquiv` examples).
- The spec of Cor. 5.21 carries the hypothesis `hR : IsRouquierQ C (qCL kl)` explicitly.
