# categorification-lean

Lean 4 formalizations of results in categorification.

## Contents

### KLR algebras (Khovanov–Lauda I, arXiv:0803.4121v2; Khovanov–Lauda II, arXiv:0804.2080v1)

The ring `R(ν)` is defined by generators (idempotents `e i`, dots `x a`, crossings `ψ j`) and
relations, for an arbitrary family of polynomials `Q i j ∈ k[u, v]` (the generality of KL II).
The simply-laced rings of KL I, for a simple graph `Γ`, are `KLR.R1 k Γ ν` (`KLR.klQ Γ`) with
`Q_ij = u + v` for adjacent `i, j` and `Q_ij = 1` otherwise. Positions are zero-indexed.

| Source | Result | Declarations |
|---|---|---|
| KL I §2.1, (2.3)–(2.8) | definition of `R(ν)`; the KL I relations | `KLR.KLRAlgebra`, `KLR.Rel`; `KLR.KL1.ψ_sq`, `KLR.KL1.braid_hard`, `KLR.KL1.braid_easy`, … |
| KL I §2.1, (2.9); KL II §3 | grading (`deg x = i·i`, `deg ψ_k e_i = -i_k·i_{k+1}`) | `KLR.GradingDatum.gradedAlgebra`, `KLR.klGradingDatum`, `KLR.GradingDatum.ψw_mul_pol_monomial_mul_e_mem_grade` |
| KL I §2.1 | antiinvolution `ψ` and involution `σ` | `KLR.KLRAlgebra.flipH`, `KLR.KLRAlgebra.hflip_hflip`, `KLR.KLRAlgebra.sigma`, `KLR.KLRAlgebra.sigma_sigma`, `KLR.KLRAlgebra.hflip_sigma` |
| KL I Prop. 2.3 | polynomial representation, for every orientation of `Γ` (and for any factorisation `Q_ij(u,v) = P_ji(u,v) P_ij(v,u)`) | `KLR.polyRepKL1`, `KLR.PolyRep.polyRep` |
| KL I Thm. 2.5 | for any choice of reduced expressions, `_jR(ν)_i` is free with basis `ψ_ŵ x^u e_i` (`w • i = j`) | `KLR.KL1.cornerBasis`, `KLR.KL1.cornerBasis_apply`, `KLR.KL1.basis`; general form `KLR.KLRAlgebra.cornerBasis` |
| KL I Cor. 2.6 | the polynomial representation is faithful | `KLR.KL1.polyRepKL1_injective`; general form `KLR.polyRep_injective` |
| KL I Prop. 2.7 | `R(ν)` is free of rank `m!` over `Pol(ν)`, for both the right and the left action | `KLR.KL1.rightBasis`, `KLR.KL1.leftBasis`, `KLR.KL1.finrank_polMod` |
| KL I Thm. 2.9 | the center of `R(ν)` is `Sym(ν) = Pol(ν)^{S_m}` | `KLR.KL1.center_eq`, `KLR.KL1.symNuEquivCenter`, `KLR.symNu` |
| KL I Cor. 2.10 (1) | `R(ν)` is free of rank `(m!)²` over its center | `KLR.KL1.center_free`, `KLR.KL1.finrank_center`, `KLR.KL1.exists_centerBasis` |
| KL I Cor. 2.11 (1) | `R(ν)` is left and right Noetherian (over a Noetherian domain) | `KLR.KL1.isNoetherianRing`, `KLR.KL1.isNoetherianRing_mulOpposite` |
| KL I Cor. 2.11 (2) | `R(ν)` is indecomposable | `KLR.KL1.eq_zero_or_one_of_mem_center` |

The basis theorem is proved over any integral domain (the paper works over `ℤ`). Spanning holds
over any commutative ring (`KLR.KLRAlgebra.span_eq_top'`). Linear independence is proved by
expanding the action on the polynomial representation over the fraction field in terms of the
automorphisms `w ∈ S_m` (`Categorification.PermExpansion`), rather than by the paper's
induction on sequences.

### Symmetric group combinatorics

Words in adjacent transpositions of `Fin m`: Coxeter length and inversions
(`TypeA.length_eq_invCount`), a normal form (`TypeA.braidEquiv_canWord_or_hasRepeat`), and
Matsumoto's theorem for `S_m` (`TypeA.braidEquiv_of_isReduced`).

### Symmetric polynomials

`Categorification.symmetricBasis`: over any commutative ring, `k[x_0, …, x_{n-1}]` is a free
module of rank `n!` over the symmetric polynomials, with basis the monomials `x^u`,
`u_a ≤ a` (`finrank_symmetric`); more generally, free of rank `|G|` over the invariants of a
label-preserving group `G` (`Categorification.finrank_labelInvariants`).

### Divided differences

`Categorification.ddiff`: divided difference operators on `MvPolynomial` over any commutative
ring, with the nilHecke relations (`ddiff_spec`, `ddiff_ddiff`, `ddiff_mul`, `ddiff_braid`).

## Building

Requires [elan](https://github.com/leanprover/elan). Toolchain
`leanprover/lean4:v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` are
pinned.

```sh
lake exe cache get
lake build
```

## License

Released under the Apache License 2.0; see [`LICENSE`](LICENSE).
