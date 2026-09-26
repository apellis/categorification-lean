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
| KL I §2.2 (1)–(2) | `R(0) ≅ k`, `R(i) ≅ k[x]` | `KLR.KLRAlgebra.zeroEquiv`, `KLR.KLRAlgebra.singleEquiv` |
| KL I §2.2 (3) | `R(m·i)` is the nilHecke ring (divided differences and multiplications on `k[x_1, …, x_m]`), with its defining relations and basis `∂_w x^u` | `KLR.KLRAlgebra.nilHeckeEquiv`, `KLR.NilHecke.basis`, `NilHecke.ddw_eq_of_isReduced` |
| KL I §2.2 (4), (5) | `R(ν)` for pairwise non-interacting distinct labels is a matrix algebra over `k[x_1, …, x_m]` | `KLR.TwoStrand.KL1.nonAdjEquiv`, `KLR.NonInteracting.KL1.equiv` |
| KL I §2.2 (7) | `R(i + j)`, `i · j = -1`: 2×2 matrices over `k[x_1, x_2]` with lower-left entry divisible by `x_1 + x_2` | `KLR.TwoStrand.KL1.adjEquiv` |
| KL I §2.2, Remark | the two orthogonal idempotents in `1_{iji}` | `KLR.KL1.Remark.idemL_add_idemR`, `KLR.KL1.Remark.idemL_mul_idemR` |
| KL I §2.2 (3) | the nilHecke idempotents `e_m = x^δ ∂_{w_0}` and `ψ(e_m)`; divided-power idempotents `1_i` in `R(ν)` (degree 0) | `NilHecke.isIdempotentElem_idemNH`, `KLR.KLRAlgebra.isIdempotentElem_divIdemOf`, `KLR.KLRAlgebra.divIdemOf_mem_grade` |
| KL I §2.1, §2.4 | the basis elements are homogeneous; the crossing degree of `ψ_ŵ e_i` depends only on `w`; graded pieces are finite-dimensional and vanish below `-∑_i ν_i(ν_i - 1)`; `gdim(1_j R(ν) 1_i) = ∑_{w•i=j} q^{deg(ψ_w 1_i)} (1-q^2)^{-m}` | `KLR.GradingDatum.degW_eq_sum_invSet`, `KLR.KL1.grade_eq_bot_of_lt`, `KLR.KL1.gdim_cornerGrade`, `KLR.KL1.hasGdim_of_finite` |
| KL I §2.5 | `(ν)_q = gdim Sym(ν) = ∏_i ∏_{a=1}^{ν_i} (1-q^{2a})^{-1}` | `KLR.KL1.gdim_symGrade`, `KLR.GradingDatum.gdim_center` |
| KL I §2.5 | the form on `K_0`: `([P_j],[P_i]) = gdim(_jR(ν)_i)`, `([P_j],[M]) = ch(M, j)` | `KLR.KL1.homForm_projP`, `KLR.GradingDatum.homForm_projP_left`, `Graded.K0.homForm` |
| KL I Cor. 2.10 (2) | `R(ν)` has a homogeneous basis over its center | `KLR.GradingDatum.exists_homogeneous_centerBasis` |
| KL I Lemma 2.1 | `L_m = k[x]/(Sym⁺)` has dimension `m!`, is a simple `NH_m`-module, its common kernel of the `x_a` is the line through `x^δ`, and all Jordan blocks of `x_m` have size `m`; `L(i^m)` is the unique graded simple `R(m·i)`-module up to shift | `NilHecke.isSimpleModule_coinv`, `NilHecke.coinvSocle_eq_span_xDelta`, `coinvMul_last_pow_eq_zero`, `ker_coinvMul_last`, `KLR.KL1.exists_gradedEquiv_klrRep` |
| KL I Prop. 2.3 | polynomial representation, for every orientation of `Γ` (and for any factorisation `Q_ij(u,v) = P_ji(u,v) P_ij(v,u)`) | `KLR.polyRepKL1`, `KLR.PolyRep.polyRep` |
| KL I Thm. 2.5 | for any choice of reduced expressions, `_jR(ν)_i` is free with basis `ψ_ŵ x^u e_i` (`w • i = j`) | `KLR.KL1.cornerBasis`, `KLR.KL1.cornerBasis_apply`, `KLR.KL1.basis`; general form `KLR.KLRAlgebra.cornerBasis` |
| KL I Cor. 2.6 | the polynomial representation is faithful | `KLR.KL1.polyRepKL1_injective`; general form `KLR.polyRep_injective` |
| KL I Prop. 2.7 | `R(ν)` is free of rank `m!` over `Pol(ν)`, for both the right and the left action | `KLR.KL1.rightBasis`, `KLR.KL1.leftBasis`, `KLR.KL1.finrank_polMod` |
| KL I Thm. 2.9 | the center of `R(ν)` is `Sym(ν) = Pol(ν)^{S_m}` | `KLR.KL1.center_eq`, `KLR.KL1.symNuEquivCenter`, `KLR.symNu` |
| KL I Cor. 2.10 (1) | `R(ν)` is free of rank `(m!)²` over its center | `KLR.KL1.center_free`, `KLR.KL1.finrank_center`, `KLR.KL1.exists_centerBasis` |
| KL I Cor. 2.11 (1) | `R(ν)` is left and right Noetherian (over a Noetherian domain) | `KLR.KL1.isNoetherianRing`, `KLR.KL1.isNoetherianRing_mulOpposite` |
| KL I Cor. 2.11 (2) | `R(ν)` is indecomposable | `KLR.KL1.eq_zero_or_one_of_mem_center` |

| KL I §2.6 | concatenation `ι_{ν,ν'} : R(ν) ⊗ R(ν') → R(ν+ν')` (injective) | `KLR.KLRAlgebra.concat`, `KLR.KLRAlgebra.concat_mul`, `KLR.KLRAlgebra.concat_e_tmul_e`, `KLR.KLRAlgebra.concat_injective` |
| KL I Prop. 2.13, Cor. 2.14 | `1_{…ij…} ~ 1_{…ji…}` for `i·j = 0`; `1_{…iji…}` decomposes into orthogonal idempotents equivalent to `1_{…i^{(2)}j…}` and `1_{…ji^{(2)}…}` for `i·j = -1`, via the paper's matrices `B_0`, `B_1` (degrees `1`, `-1`); the resulting isomorphisms of projective modules and of subspaces `1_i M` | `KLR.KLRAlgebra.prop213_zero`, `KLR.KLRAlgebra.prop213_neg_one`, `KLR.KLRAlgebra.prop213_neg_one_rIdealEquiv`, `KLR.KLRAlgebra.cor214_neg_one` |
| KL I §2.2 (3), §2.5 | `1_î` is a sum of `∏ n_a!` orthogonal idempotents equivalent to `1_i`, with degrees distributed as `q^{-⟨i⟩} i!`; `gdim(1_î M) = q^{-⟨i⟩} i! gdim(1_i M)`; `[P_î] = i! [P_i]` in `K_0` | `KLR.exists_orthogonal_decomposition_e`, `KLR.gdim_e_ofList_expandDiv`, `KLR.K0_projP_expandDiv` |
| KL I Cor. 2.14 (graded), Cor. 2.15 | graded isomorphisms `1_{…iji…}M ≅ 1_{…i^{(2)}j…}M{1} ⊕ 1_{…ji^{(2)}…}M{1}`, `1_{…ij…}M ≅ 1_{…ji…}M`; the three character identities | `KLR.cor214_neg_one_graded`, `KLR.cor215_zero`, `KLR.cor215_neg_one`, `KLR.cor215_divided` |
| KL I §3.1 (relations in `K_0`) | `[P_{…iji…}] = [P_{…i^{(2)}j…}] + [P_{…ji^{(2)}…}]`, `[P_{…ij…}] = [P_{…ji…}]` | `KLR.K0_projDiv_neg_one`, `KLR.K0_projDiv_zero` |
| KL I Prop. 2.12 | a graded simple `R(ν)`-module is finite-dimensional, `Sym⁺(ν)` acts by `0`, `Hom(S, S{a}) = 0` for `a ≠ 0`, and it is simple as an ungraded module; `dim R(ν)/Sym⁺(ν)R(ν) = (m!)²`; at most `(m!)²` simples up to isomorphism and shift | `KLR.KL1.prop_2_12`, `KLR.KL1.finrank_quotient_symPlusIdeal`, `KLR.KL1.card_le_of_isGradedSimple` |
| KL I Prop. 2.16 | `1_{ν,ν'} R(ν+ν')` is a free left `R(ν) ⊗ R(ν')`-module with basis indexed by minimal coset representatives (shuffles) | `KLR.KLRAlgebra.freeBasis`, `KLR.KLRAlgebra.free_oneConcat`, `KLR.KLRAlgebra.inductionBasis` |
| KL I Prop. 2.18 (basis form) | the bimodule `1_{ν,ν'} R(ν+ν') 1_{ν'',ν'''}` is filtered by sub-bimodules indexed by the number of crossing strands, with bases of the steps and subquotients given by minimal double coset representatives (the identification of the subquotients with tensor products over `R'` and the grading shift are not yet formalized) | `KLR.KLRAlgebra.mackeyBimodFilt`, `KLR.KLRAlgebra.mackeyBimodFilt_eq_span_crossings`, `KLR.KL1.mackeySubquotBasis`, `TypeA.mackey_factorisation` |
| KL I Prop. 2.19 (ungraded, left modules) | `Res_{ν,ν'} P_k ≅ ⊕ P_i ⊗ P_j` over the ways of writing `k` as a shuffle of `i` and `j` | `KLR.KLRAlgebra.resProjEquiv` |
| KL I Cor. 2.17 | restriction takes projective modules to projective modules | `KLR.KLRAlgebra.res_projective` |

The basis theorem is proved over any integral domain (the paper works over `ℤ`). Spanning holds
over any commutative ring (`KLR.KLRAlgebra.span_eq_top'`). Linear independence is proved by
expanding the action on the polynomial representation over the fraction field in terms of the
automorphisms `w ∈ S_m` (`Categorification.PermExpansion`), rather than by the paper's
induction on sequences.

### Lusztig's algebra `f` (Lusztig, *Introduction to quantum groups*, Ch. 1; KL I §3.1)

For a symmetric Cartan datum (`QuantumGroup.CartanDatum`, including the simply-laced datum of a
graph, `CartanDatum.ofGraph`) over a commutative ring with a unit `v`:

| Source | Result | Declarations |
|---|---|---|
| Lusztig 1.2.1–1.2.2 | the free algebra `'f`, the twisted algebra `'f ⊗ 'f`, and `r : 'f → 'f ⊗ 'f` | `QuantumGroup.PreF`, `QuantumGroup.PreF.TwSq`, `QuantumGroup.PreF.r`, `QuantumGroup.PreF.tensorEquiv` |
| Lusztig 1.2.3; KL I Prop. 3.3 | existence, uniqueness and symmetry of the bilinear form | `QuantumGroup.PreF.existsUnique_form`, `QuantumGroup.PreF.form_symm` |
| Lusztig 1.2.5 | `f = 'f / radical`, with nondegenerate form | `QuantumGroup.PreF.F`, `QuantumGroup.PreF.formF_nondegenerate` |
| Lusztig 1.4.3 | the quantum Serre relations hold in `f` | `QuantumGroup.CartanDatum.serre`; simply-laced: `QuantumGroup.KL.serre_comm`, `QuantumGroup.KL.serre_cubic` |
| Lusztig 1.4.7 | divided powers and the integral form `_A f` | `QuantumGroup.PreF.dpow`, `QuantumGroup.PreF.Af` |
| Lusztig 1.4.1 | `θ_i^{(a)} θ_i^{(b)} = [a+b choose a]_i θ_i^{(a+b)}` | `QuantumGroup.PreF.dpow_mul_dpow`, `QuantumGroup.CartanDatum.dpowF_mul_dpowF` |
| Lusztig 1.4.3 | divided-power form of the Serre relations; simply-laced: `θ_iθ_jθ_i = θ_i^{(2)}θ_j + θ_jθ_i^{(2)}` | `QuantumGroup.CartanDatum.serre_divided`, `QuantumGroup.KL.serre_divided` |
| Lusztig 1.2.2, 1.4.2 | coassociativity of `r` on `'f`; `r` descends to `f`; `r(θ_i^{(a)})` | `QuantumGroup.PreF.coassoc`, `QuantumGroup.PreF.rbar`, `QuantumGroup.PreF.r_dpow` |
| Lusztig 1.4.4 | `(θ_i^{(a)}, θ_i^{(a)}) = ∏_{s=1}^a (1 − v_i^{−2s})^{−1}` | `QuantumGroup.CartanDatum.form_dpow_dpow`, `QuantumGroup.KL.form_dpow_dpow` |
| Lusztig 1.2.12, 1.4.7 | the bar involution on `f`, preserving `_A f` | `QuantumGroup.CartanDatum.barF`, `QuantumGroup.CartanDatum.barF_mem_Af` |

The converse inclusion (the radical is generated by the Serre relations; Lusztig 33.1.3, used
in KL I §3) is stated as the proposition `QuantumGroup.PreF.GabberKac` but is not proved. In the
list of generators of the ideal in KL I §3.1, `θ_iθ_j − θ_iθ_j` should read `θ_iθ_j − θ_jθ_i`.
In the right-module half of KL I Prop. 2.13, the summands should be the right projectives
`_{…i^{(2)}j…}P ⊕ _{…ji^{(2)}…}P`.

### Graded modules and Grothendieck groups

Generic infrastructure over a `ℤ`-graded algebra (`Categorification.Graded`): graded modules via
Mathlib's `DirectSum.Decomposition` and `SetLike.GradedSMul`, grading shifts `M{a}` (shifted up
by `a`, as in KL I §2.5), graded dimension `gdim` in `ℤ((q))` (additive on short exact
sequences, `gdim (M{a}) = q^a gdim M`), the Grothendieck group `K0` of finitely generated graded
projective modules as a `ℤ[q,q⁻¹]`-module (with `[A e] = q^{-d}[A e']` for idempotents
equivalent via elements of degrees `d`, `-d`, and additivity on orthogonal idempotents), and
`G0` of finite-dimensional graded modules. For `R(ν)`: `P_i = R(ν) 1_i` and characters
`ch(M)` (`KLR.GradingDatum.projP`, `KLR.GradingDatum.ch`). "Graded projective" is taken to mean
projective as a module and graded. The form on `K_0` is defined as `gdim HOM(P, Q)`
(`Graded.K0.homForm`); the paper's `gdim(P^ψ ⊗_{R(ν)} Q)` agrees with it on the classes
`[P_i]`, which is where the paper evaluates it, but the identification on all of `K_0` (which
involves the bar involution) is not formalized.

### Symmetric group combinatorics

Words in adjacent transpositions of `Fin m`: Coxeter length and inversions
(`TypeA.length_eq_invCount`), a normal form (`TypeA.braidEquiv_canWord_or_hasRepeat`), and
Matsumoto's theorem for `S_m` (`TypeA.braidEquiv_of_isReduced`), and factorisation through
minimal coset representatives of `S_n × S_{n'}` with additivity of length
(`TypeA.parabolicEquiv`, `TypeA.length_blockPerm_mul`).

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
