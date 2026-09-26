# categorification-lean

Lean 4 formalizations of results in categorification. Depends on Mathlib and
[string-diagrams-lean](https://github.com/apellis/string-diagrams-lean).

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
| KL I Prop. 3.11 (2), (3) | for a composition `μ` of `n`, the socle of `Res_μ L_n` over the parabolic nilHecke algebra is simple and isomorphic to the Young coinvariant module `L_μ`, and every simple subquotient is isomorphic to `L_μ`; the socle of `Res^n_{n-1} L_n` is simple | `NilHecke.parNH_socle`, `NilHecke.nonempty_linearEquiv_youngRep_subquotient`, `NilHecke.resNH_socle` |
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
| KL I §2.6, §3.1 Prop. 3.1 (`K_0` part) | balanced tensor products over noncommutative algebras and external tensor products (graded); induction `Ind_{ν,ν'}` of graded projectives, `Ind(P_i ⊠ P_j) ≅ P_{ij}`; associativity of `ι`; `[Ind]` makes `K_0(R) = ⊕_ν K_0(R(ν))` an associative unital `ℤ[q,q⁻¹]`-algebra with unit `[R(0)]` | `BalancedTensor`, `KLR.KLRAlgebra.concat_assoc`, `KLR.GradingDatum.indK0`, `KLR.GradingDatum.indK0_projP`, `KLR.GradingDatum.indK0_assoc`, `KLR.GradingDatum.K0R`, `KLR.GradingDatum.K0R_one` |
| KL I Prop. 2.19 (graded), §3.1 Prop. 3.3 (1), (2), (4) | graded restriction on `K_0`; Frobenius reciprocity `HOM(Ind N, X) ≅ HOM(N, Res X)` (graded); `Res P_s ≅ ⊕_u (P_{i_u} ⊠ P_{j_u}){deg(i_u, j_u, s)}`; `(1,1) = 1`, `([P_i],[P_j]) = δ_{ij}(1-q²)⁻¹`, `(x x', y) = (x ⊗ x', Res y)` | `KLR.KLRAlgebra.frobeniusEquiv`, `KLR.GradingDatum.resK0`, `KLR.GradingDatum.resProjGradedEquiv`, `KLR.KL1.K0RForm_one_one`, `KLR.KL1.K0RForm_projP_single`, `KLR.GradingDatum.homForm_indK0` |
| KL I §2.5, §3.1 Props. 3.3 (3), (4) | duality `P̄ = HOM(P, R(ν))^ψ` on graded f.g. projectives (`\overline{P{a}} = P̄{-a}`, `P̄̄ = P`, `\overline{Ae} = Aψ(e)`), the antilinear bar involution on `K_0` with `[P_i]`, `[P_d]` bar-invariant; the bilinear symmetric form `(x, y) = gdim HOM(x̄, y)` with `([P_j],[P_i]) = gdim(1_j R 1_i)`; `(x x', y) = (x ⊗ x', Res y)` and `(x, y y') = (Res x, y ⊗ y')` on the span of the idempotent classes; `[Res][P_s]` | `Graded.K0.bar`, `Graded.K0.pform`, `Graded.K0.pform_comm`, `KLR.KL1.bar_projDiv`, `KLR.GradingDatum.pform_indK0`, `KLR.GradingDatum.pform_indK0_right`, `KLR.GradingDatum.resK0_projP` |
| KL I §3.1 Prop. 3.2 (on the image of `γ`) | Lusztig's `r` on words is the shuffle sum with the KLR crossing degrees; `[Res] ∘ γ = (γ ⊗ γ) ∘ r`, hence `[Res]` is multiplicative for the twisted product on the image of `γ` (which contains the span of the `[P_s]`); the identification `K_0(R(ν) ⊗ R(ν')) ≅ K_0(R(ν)) ⊗ K_0(R(ν'))` is not yet formalized | `QuantumGroup.PreF.r_ofFn`, `KLR.GradingDatum.resK0_projP_eq_realize`, `KLR.KLGamma.resComp_gammaZ`, `KLR.KLGamma.resComp_gammaZ_mul` |
| KL I §3.1 (γ and forms) | `γ` commutes with the bar involutions and is an isometry: `(γx, γy) = (x, y)` for `x, y ∈ 'f` | `KLR.KLGamma.gammaF_barF`, `KLR.KLGamma.pformQ_gammaQ` |
| KL I §3.2, Lemma 2.20, Lemmas 3.5–3.8, Prop. 3.10, Cor. 3.12 (ungraded) | the shuffle lemma (dimensions); `Δ_{i^n}`, `ε_i`, `Hom(Ind N, M) ≅ Hom(N, Δ M)`; simple `R(μ) ⊗ R(ni)`-modules are `N ⊠ L(i^n)`; Lemmas 3.6–3.8; the socle of `Δ_{i^n}M` is simple of the form `L ⊠ L(i^n)` (Prop. 3.10, proved without Kato's theorem); Cor. 3.12 (for finite-dimensional modules with nilpotent dots, which holds for graded simples) | `KLR.KLRAlgebra.shuffle_lemma_finrank`, `KLR.KLRAlgebra.indResEquiv`, `KLR.KLRAlgebra.lemma_3_6`, `KLR.KLRAlgebra.lemma_3_7_head`, `KLR.KLRAlgebra.lemma_3_8`, `KLR.KLRAlgebra.prop_3_10_socle`, `KLR.KLRAlgebra.cor_3_12_socle`, `KLR.KLRAlgebra.crystal_hypotheses_of_isGradedSimple` |
| KL I Cor. 2.17 | restriction takes projective modules to projective modules | `KLR.KLRAlgebra.res_projective` |

The basis theorem is proved over any integral domain (the paper works over `ℤ`). Spanning holds
over any commutative ring (`KLR.KLRAlgebra.span_eq_top'`). Linear independence is proved by
expanding the action on the polynomial representation over the fraction field in terms of the
automorphisms `w ∈ S_m` (`Categorification.PermExpansion`), rather than by the paper's
induction on sequences.

### Diagrammatic presentations (via [string-diagrams-lean](https://github.com/apellis/string-diagrams-lean))

| Source | Result | Declarations |
|---|---|---|
| KL I §2.2 (3) | the diagrammatic nilHecke category (one colour, dot and crossing, all relations at symbolic width); `End(n strands) ≅ NH_n` (over a domain), hence faithfulness of the diagrammatic polynomial representation and a basis; the idempotent `x^δ ψ_{w_0}` | `NilHecke.Diagram.endEquiv`, `NilHecke.Diagram.realize_injective`, `NilHecke.Diagram.basis`, `NilHecke.Diagram.isIdempotentElem_klIdempotent` |
| KL I §2.1 | the diagrammatic presentation of KLR algebras (colours `I`, dots and crossings, the KLR relations for arbitrary `Q`); `R(ν) ≅ ⊕_{i,j} Hom(i, j)` (any commutative ring); the basis theorem on the diagrammatic side; KL I relations (2.3)–(2.8) | `KLR.Diagram.diagREquiv`, `KLR.Diagram.diagBasis`, `KLR.Diagram.kl1Equiv`, `KLR.Diagram.kl1_braid_adj` |
| KL III Def. 3.1 | the 2-category `U` for a root datum: signature with regions the weights, upward/downward dots and crossings, cups and caps (the pivotal extension), and all relations of Def. 3.1 (biadjointness, cyclicity, bubble relations, fake bubbles via the infinite Grassmannian recursion, the `EF`/`FE` decompositions, KLR relations on upward strands); biadjunctions `E_i 1_λ ⊣⊢ F_i 1_{λ+i}`; every 2-morphism is cyclic (pivotal structure); every relation is homogeneous and the Hom spaces are graded; `R(ν) → END_U(E_ν 1_λ)` | `KL3.Diagram.pres`, `KL3.Diagram.U`, `KL3.Diagram.biadjEF`, `KL3.Diagram.isCyclic`, `KL3.Diagram.pivotal`, `KL3.Diagram.pres_isHomogeneous`, `KL3.Diagram.toUEnd` |

The transcription of Def. 3.1 is cross-checked by homogeneity of every relation and by cyclicity
of the generators with respect to the biadjunctions; no faithful 2-representation is formalized yet.

### KLR algebras for arbitrary Cartan data (Khovanov–Lauda II, arXiv:0804.2080v1)

For a symmetric Cartan datum (`QuantumGroup.CartanDatum`), `KLR.R2 k C ν` is `R(ν)` with
`Q_ij = u^{d_ij} + v^{d_ji}` (`i·j ≠ 0`), `d_ij = −2 i·j / i·i`, graded by `deg x = i·i`.

| Source | Result | Declarations |
|---|---|---|
| KL II §3 | the defining relations; polynomial representation; basis theorem and faithfulness | `KLR.KL2.ψ_sq_of_dot_ne_zero`, `KLR.KL2.braid_hard`, `KLR.polyRepKL2`, `KLR.KL2.basis`, `KLR.KL2.cornerBasis`, `KLR.KL2.polyRepKL2_injective` |
| KL II Lemma 5, (10)–(13) | nilHecke computations, on blocks of equally labelled strands | `KLR.KL2.lemma5`, `KLR.KL2.blockElt_mul_x_pow_mul_chainL` |
| KL II Prop. 6, Cor. 7 | `⊕_a {}_{…i^{(2a)} j i^{(d+1−2a)}…}P ≅ ⊕_a {}_{…i^{(2a+1)} j i^{(d−2a)}…}P` (right and left projectives, and `1_{…}M`), via the maps `α′`, `α″`, homogeneous of the degrees matching the shifts | `KLR.KL2.prop6`, `KLR.KL2.prop6_rIdealEquiv`, `KLR.KL2.cor7_lIdealEquiv`, `KLR.KL2.prop6_fixSubEquiv` |
| KL II Thm. 8 (injectivity), §3 | in `K_0`: `[P_î] = i!_{v_i} [P_i]` and the Serre relation `∑_n (-1)^n [P_{…i^{(n)} j i^{(N-n)}…}] = 0`; `γ : 'f → ℚ(v) ⊗ K_0(R)` killing the Serre ideal, its descent to `f` (Gabber–Kac hypothesis), and injectivity on `f` and `_A f`; `K_0(R)` is free | `KLR.KL2Gamma.clsDiv2_serre`, `KLR.KL2Gamma.gammaF2`, `KLR.KL2Gamma.gammaF2_injective`, `KLR.KL2Gamma.gammaInt2'_injective`, `KLR.KL2Gamma.K0R_free2` |

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

### The map `γ` (KL I §1, §3.1)

For the simply-laced datum of a graph (`KLR.KLGamma`): the classes `[P_{i_1^{(a_1)}⋯}]` in
`K_0(R)` with `[P_i][P_j] = [P_{ij}]`, `[P_î] = i![P_i]` and the Serre relations; the algebra map
`'f → K_0(R)`, `θ_i ↦ [P_i]` (over `ℤ[q,q⁻¹]`), which kills the Serre relations; its base change
`γ : f → ℚ(v) ⊗ K_0(R)` (with `q ↦ v⁻¹`) sending divided-power monomials to the corresponding
`[P_{i_1^{(a_1)}⋯}]` (`KLR.KLGamma.gammaF`, `gammaF_dpowMono`), and the integral version on `_A f`
(`gammaInt`). Descending from `'f/(Serre)` to `f` uses the Gabber–Kac theorem, which is taken as an
explicit hypothesis `QuantumGroup.PreF.GabberKac`; the integral map into `K_0(R)` uses that
`K_0(R) → ℚ(v) ⊗ K_0(R)` is injective, which holds because `K_0(R)` is free (see below).

**KL I Prop. 3.4** (injectivity): Lusztig's form on words is
`(θ_{a_1}⋯θ_{a_m}, θ_{b_1}⋯θ_{b_m}) = ∏_x c_{a_x} · ∑_{w : b∘w = a} v^{∑_{(x,y) ∈ inv(w)} a_y·a_x}`
(`QuantumGroup.PreF.form_wordFn`), which matches `gdim(1_j R(ν) 1_i)` under `q ↦ v⁻¹`
(`KLR.KLGamma.lsCast_homForm_projP`); hence the kernel of `'f → ℚ(v) ⊗ K_0(R)` is the radical of the
form, unconditionally (`KLR.KLGamma.ker_gammaQ_le_radical`), and `γ` is injective on `f` and on
`_A f` (`KLR.KLGamma.gammaF_injective`, `gammaA_injective`, `gammaInt_injective`, under the
hypotheses above). That `γ` intertwines `r` with `[Res]` is not yet formalized.

### Modified quantum groups (Khovanov–Lauda III, arXiv:0807.3250v1, §2.1)

For a root datum over a field with `q` not a root of unity: Lusztig's `U̇` as the direct sum of its
blocks `U̇1_λ` (`QuantumGroup.UDot.UD`), its integral form, the involutions `ψ` and `ω`, the
bilinear pairing of KL III Prop. 2.2 (existence and uniqueness, `QuantumGroup.UDot.prop_2_2`,
`QuantumGroup.UDot.KL3.prop_2_2`) and the semilinear form with the properties of Prop. 2.4
(`QuantumGroup.UDot.KL3.prop_2_4`). Nondegeneracy (Prop. 2.5) is not proved.

### Krull–Schmidt, projective covers, and the Grothendieck groups (KL I §2.5)

Over a field, for a `ℤ`-graded algebra with finite-dimensional graded pieces vanishing in
sufficiently negative degrees (`Categorification.Graded`): graded projectivity of projective graded
modules, Fitting's lemma, indecomposable graded projectives have local degree-0 endomorphism rings and
unique tops, every graded simple has a unique projective cover, `K_0` is a free `ℤ[q,q⁻¹]`-module
with basis the indecomposables up to shift (`Graded.K0.indecBasis`), `G_0` is free with basis the
graded simples (`Graded.G0.topBasis`), and the pairing `([P],[M]) = gdim HOM(P, M)` pairs the two
bases diagonally (`Graded.pairing_indecBasis_topBasis`). For `R(ν)`: `KLR.GradingDatum.k0Basis`,
`KLR.GradingDatum.g0Basis`, finitely many indecomposables (at most `(m!)²`), and consequently
`K_0(R) → ℚ(v) ⊗ K_0(R)` is injective (`KLR.KLGamma.toK0Q_injective`), so the integral `γ` needs only
the Gabber–Kac hypothesis (`KLR.KLGamma.gammaInt'`). Uniqueness of decompositions at the level of
modules (as opposed to classes) is not formalized.

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
