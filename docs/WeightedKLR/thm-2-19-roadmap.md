# Webster, Theorem 2.19: roadmap and remaining parts

Source: B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19. Tracking issue: #289. The ground-ring correction and the formalized parts are in
`thm-2-19-ground-ring.md` and in the README row “§2.4, Theorem 2.19”.

Over a field, the graded coproduct `Δ = k0TensorEquiv⁻¹ ∘ resK0` and its Mackey formula
`Δ(x · y) = ∑_i q^{s_i} T_{L i}(Δ x ⊗ Δ y)` are formalized. For loop-free graphs,
`exists_coproductK0_indK0_eq_sum_graded` supplies the comparison hypotheses from
`GradingDatum.tensorK0Hyp`; it takes no additional `hT`. The earlier general statement remains
available as `exists_coproductK0_indK0_eq_sum_graded_of_tensorK0Hyp`, with `TensorK0Hyp`
explicit. The loop-free result keeps the arbitrary grading datum `G` and its `HasGdim`
instances; it does not replace `G` by the grading of the standing hypothesis.

| Item | Content | Status |
|---|---|---|
| A0 | the fields `fdA`, `fdB`, `fdC` of `TensorK0Hyp` for `W_ν` (graded simple tops are finite-dimensional) | formalized under `Γ.Dagger`, `Γ.NoZeroLoops`, `Γ.Standing`; no loop-freeness assumption |
| A | the fields `endA`, `endB` of `TensorK0Hyp` for `W_ν` (graded simple modules are absolutely irreducible) | proved for loop-free graphs over any field by the minimum-support local-chart argument; repeated colours and cycles are allowed |
| B | the quantum Serre relations in graded `K_0` for every `Q` of Rouquier's form | polynomial conditions and leading-coefficient homotopy identities formalized; graded relation remains |
| C | the integral divided-power quantum-group map to `K_0` for loop-free `Γ` | Cartan datum and graded corner-entry maps formalized; needs B and multiplicative assembly |
| D | the antipode / Hopf structure in the braided category of `ℤ[I]`-graded modules | open |

The local-chart proof of A is a replacement argument. The right-restriction
induction initially proposed from KL I has the obstruction recorded below; it is not used
by the replacement proof. Completing A does not settle B, C or D, or the comparison for
graphs with loops.

## A0. Finite-dimensional graded simple tops

`TensorK0Hyp` asks that the graded simple tops of `W_ν` and of `W_{ν'} ⊗ W_{ν''}` be
finite-dimensional. For unweighted KLR algebras this is
`Categorification.GradingDatum.tensorK0Hyp` (KL I Proposition 2.12 and a central polynomial
subalgebra of positive degree). For `W_ν` the same augmentation argument applies:

1. Colour-symmetric polynomials in the dots are central (`CentralPolynomials.lean`).
2. The basis of Webster Theorem 2.8 makes `W_ν` finite over that central subalgebra, and
   its augmentation quotient is finite-dimensional (`CentralFinite.lean`).
3. Positive-degree central elements annihilate graded simple modules. Graded Nakayama then
   presents a graded simple as a quotient of a shift of the augmentation quotient
   (`Simple.lean`). The same argument applies to `W_{ν'} ⊗ W_{ν''}`.

`GradingDatum.finiteDimensional_top` and `GradingDatum.finiteDimensional_top_tensor` provide
`fdA`, `fdB`, `fdC` for the standing grading under `Γ.Dagger`, `Γ.NoZeroLoops` and
`Γ.Standing`, without excluding loops. `SimpleGrading.lean` addresses the arbitrary grading
datum used in the coproduct theorem: `HasGdim` forces positive dot degrees. A negative dot
degree contradicts the lower bound on nonzero graded pieces; a zero degree puts infinitely
many independent polynomial powers in one finite-dimensional graded piece. This allows the
same augmentation and dot-nilpotence arguments for an arbitrary admissible `G`.

## A. Absolute irreducibility by a minimum support star

`AbsoluteSimple.lean` proves
`WeightedKLR.exists_eq_smul_of_isSimpleModule`: a finite-dimensional simple weighted KLR
module with nilpotent dots has scalar endomorphisms when the graph is loop-free and satisfies
`Γ.Dagger` and `Γ.Standing`. Both loop conditions are explicit: distinct head and tail on
each edge, and `Γ.loop i = none`. The coefficient field and standing polynomials are
arbitrary; cycles and repeated colours are allowed.

`GradingDatum.exists_eq_smul_of_isGradedSimple` applies this to graded simples. Finite
dimension comes from A0, and positive dot degrees make the dots nilpotent. The ungraded
finite-dimension and nilpotence assumptions are intermediate assumptions discharged in this
graded application, rather than additional assumptions of the final tensor comparison.
`GradingDatum.exists_eq_smul_of_isGradedSimple_of_hasGdim G` extends this application to
an arbitrary grading datum with `HasGdim`, using the positive-degree result from
`SimpleGrading.lean`.

The replacement argument is as follows.

1. **Choose a minimum support configuration.** A full labelled chamber is supported when some
   diagram factoring through its idempotent acts nontrivially. This support is nonempty and
   invariant under colour-preserving strand permutations (`Local/Support.lean`). Minimize
   `∑_s p_s²` over the closed supported chambers and relabel a minimizing chamber to rank
   order. The proof works over any ordered position field: affine orthogonal projection and
   a finite active-constraint argument give the polyhedral minimum, followed by a finite
   minimum over chambers (`Geometry/AffineProjection.lean`, `PolyhedronMinimum.lean`,
   `SupportMinimum.lean`). No completeness or real-field assumption is added.
2. **Build the local zero-weight graph.** Refine a colour by the position of its strand at
   `p`, and retain the hyperplanes through `p` (`Local/Graph.lean`, `Hyperplanes.lean`).
   The local graph has zero weights and inherits the standing and (†) hypotheses. It is
   loop-free when the original graph is. The faithful polynomial representation checks the
   chart relations (`Local/Chart.lean`, `Operators.lean`). Restricting to rank-ordered
   chambers gives `Local.weightedHom`; its unit image is the sum of the incident
   rank-ordered chamber idempotents (`Local/WeightedChart.lean`).
3. **Show that the local chart supplies the whole star action.** Use the segment basis of
   Theorem 2.8. A basis term whose strand permutation fixes `p` has a local preimage
   (`Local/BasisImage.lean`, `WeightedBasisImage.lean`). For a permutation moving `p`, the
   midpoint between `p` and its relabelling has strictly smaller squared norm, so it lies
   outside every closed supported chamber. Finite perturbation chooses a simple segment
   whose generic midpoint is still outside them. Its crossing word has an unsupported
   prefix chamber, and its gallery therefore annihilates the module
   (`Local/AdaptedSegment.lean`, `SupportSegments.lean`, `BasisSegments.lean`). The basis
   expansion and finite sums assemble these statements into the full star-corner action
   (`Local/CornerAction.lean`, `StarAction.lean`, `StarChartAction.lean`).
4. **Detect scalar endomorphisms locally.** Restrict the module to the fixed subspace of
   the chart unit. A supported incident chamber makes this restriction nonzero, and the
   full corner action makes it simple. The chart preserves labelled dots, so nilpotence
   passes to the restriction. At zero weights, matrix amplification realizes the ordinary KLR algebra as a
   corner acting on the family of chamber components, and KL I arXiv:0803.4121v2, §3.2, Corollary 3.19 supplies
   scalar endomorphisms (`ZeroWeightSimple.lean`). Non-unital restriction then detects
   scalar endomorphisms of the original simple module (`Local/Endomorphisms.lean`).

`TensorSimple.lean` packages A0 and A as
`GradingDatum.tensorK0Hyp G hD hS hne hl ν μ`. It supplies all five fields of
`KLR.TensorK0Hyp (G.klrGrade ν) (G.klrGrade μ)` for arbitrary weights, with `HasGdim` for
the chosen grading. The coproduct theorem uses this construction for every pair of weights,
removing the separate comparison hypothesis in the loop-free case. Graphs with loops retain
`exists_coproductK0_indK0_eq_sum_graded_of_tensorK0Hyp`.

### The multiplicity-free special case

The earlier `GradingDatum.exists_eq_smul_of_isGradedSimple_multiplicityFree` and
`GradingDatum.tensorK0Hyp_multiplicityFree` remain useful specializations under
`∀ i, ν i ≤ 1` (and the corresponding condition on the second weight for the comparison).
Their colour-permutation group is trivial, so each diagonal chamber corner is polynomial.
They allow loops and require no local-chart reduction. The new loop-free result removes the
multiplicity restrictions and includes the interaction of same-colour crossings with ghosts.

### Why the earlier right-restriction induction does not apply

The initial proposed adaptation of KL I Corollary 3.19 was an induction on the weight.
One would restrict a simple module along the juxtaposition idempotent for a single-colour
right block, use the nilHecke algebra on that block, and reconstruct the simple by induction
and adjunction. This requires some nonzero right restriction at every nonzero weight.

That requirement fails for weighted chambers. Take two vertices `a,b`, parallel edges
`a → b` of weights `−1,+1`, no loops, and `Q_e(u,v)=u−v`, with all standing integers equal
to `1`. These satisfy the standing hypothesis and (†). At weight `α_a+α_b`, the two walls
bound a middle chamber `C`. There is a one-dimensional graded simple supported only on `C`:
dots and all steps act by zero. There are no diagonals or nontrivial colour permutations;
the ghost bigon relations evaluate to `Q_e(0,0)=0`. Both juxtaposed chambers with a
single-colour right block lie outside the middle chamber, so every such right restriction
vanishes. Thus every `ε_i(M)` is zero.

This is a mathematical obstruction to that smaller-weight induction, even if its remaining
lemmas hold whenever a right restriction is nonzero. Regular wall factors on the polynomial
representation need not act injectively on dot-nilpotent simple modules. The obstruction is
recorded on [issue #289](https://github.com/apellis/categorification-lean/issues/289#issuecomment-6951906423).
It is not a counterexample to absolute irreducibility. The minimum-support local-chart proof
above avoids the nonzero-right-restriction requirement.

## B. Quantum Serre relations: formalize Rouquier

Goal: for distinct `s, t ∈ I`, in graded `K_0` of the unweighted KLR algebras `R(ν)`,
`∑_{a+b = m+1} (-1)^a [E_s^{(a)} E_t E_s^{(b)}] = 0` with `m = m_{st}`, for every `Q` of
Rouquier's form over every commutative ring. Then transport to `W_ν` (item C).

The earlier Serre relations cover KL's choices of `Q`: KL I `klQ`
(`Categorification/KLR/KL1.lean`) and KL II/III `u^{d_ij} + v^{d_ji}` (`KLR.KL2.serre_rel`,
`K0_serre_window`). Webster's `Γ.klrQ = ∏_e Q_e` is not of either form.

Rouquier's form. R. Rouquier, *2-Kac–Moody algebras*, arXiv:0812.5023v1, works with
`Q_{st}(u, v) = t_{st} u^{m_{st}} + ∑_{r < m_{st}, p < m_{ts}} t_{s,t,r,p} u^r v^p + t_{ts} v^{m_{ts}}`
with `t_{st}`, `t_{ts}` units, over any commutative ring (the universal case is the ring
generated by the coefficients with `t_{st}^{±1}` adjoined). He proves the categorified Serre
relation there: in the section on the Serre relations, a lemma shows that a certain complex of
graded projective `R(ν)`-modules is null-homotopic, and a proposition deduces the isomorphism
`⊕_{a even} E_s^{(m+1-a)} E_t E_s^{(a)} ≅ ⊕_{a odd} E_s^{(m+1-a)} E_t E_s^{(a)}`, compatible with
gradings. The checked locators are Lemma 3.13, §3.2.3, pp. 27–28, and Proposition 4.2, §4.1.1, pp. 32–33. When `m_{st}=0`, the polynomial is a single invertible constant, not a sum of two pure-power terms.

Webster's `Q` is of this form: under the standing hypothesis each `Q_e` is homogeneous for the
grading `deg u = d_{h(e)}`, `deg v = d_{t(e)}` with unit coefficients on `u^c` and `v^{c'}`
(`IsUnitHomogeneous`), so the product `Γ.klrQ s t` is homogeneous with unit coefficients on its
pure powers `u^m`, `v^{m'}`, and every other monomial `u^r v^p` has `r < m` and `p < m'`.

Plan (in `Categorification/KLR/`, generic in `Q`):

1. **Polynomial conditions (done).** `KLR.IsRouquierQ C Q`: for `s ≠ t`, `Q s t` has the shape above, `Q t s (v, u) =
   Q s t (u, v)`, and is homogeneous for the grading. Prove `Γ.IsRouquierQ` for `Γ.klrQ` from
   `Γ.Standing` (above). The declarations are `WeightedGraph.Standing.cartanDatum` and
   `WeightedGraph.Standing.isRouquierQ`; they work over any commutative ring.
2. **Idempotents.** In `R(ν)`, `ν = (m+1)α_s + α_t`, for `a + b = m + 1` let `e_a` be the image of
   `b_a ⊗ 1_t ⊗ b_b` under the parabolic inclusion of `R(aα_s) ⊗ R(α_t) ⊗ R(bα_s)`, where `b_a`
   is the primitive nilHecke idempotent (classical nilHecke library). `P^a = R(ν) e_a` represents
   `E_s^{(a)} E_t E_s^{(b)}` up to a grading shift.
3. **The differential.** Maps `P^a → P^{a+1}` given by right multiplication by
   `e_a τ_{…} e_{a+1}`, the crossings carrying one `s`-strand across the `t`-strand; and maps in the
   opposite direction given by the reversed crossings times `(-1)^{a+m} t_{st}^{-1}`
   in Rouquier's indexing (`n=m+2`, so his sign is `(-1)^{a+n}`).
4. **Null-homotopy.** Prove `d ∘ d = 0` and `h d + d h = id` on each `P^a`. This is a computation
   in `R(ν)` with the KLR relations; `Q` enters both the bigon and the divided-difference braid correction. The nilHecke
   sandwich extracts its leading pure coefficient, which is why the unit `t_{st}` appears. Reduce the computation to the nilHecke algebra acting on symmetric
   polynomials in the `s`-dots, where the lower terms of `Q` are killed by the idempotents
   (degree bound `r < m`).
   The identities `KLR.Rouquier.serre_A`, `serre_B`, `serre_C`, `serre_Dplus` and
   `serre_Dminus` are formalized with arbitrary commutative coefficients.
5. **Graded `K_0`.** A bounded contractible complex of graded finitely generated projective
   modules gives `∑ (-1)^a [P^a] = 0` (`ProjK0.of_eq_add_of_exact` and its graded form). With the
   divided-power normalization this is the quantum Serre relation.
6. **Generalize `K0_serre_window`** from `klQ2` to `IsRouquierQ`, and record the KL II case as a
   specialization.

This holds over every commutative ring. Over a field it gives the Serre relations in `K_0` for
every `Q` that Webster allows on a loop-free graph.

## C. The quantum-group map (needs B)

Webster v4, §2.4, Theorem 2.19, p. 12 asserts a natural map, without a construction
or an explicit loop-free restriction. The target integral Grothendieck group requires the
integral divided-power form over `ℤ[q,q⁻¹]`; a map from the generic quantum group over
`ℚ(v)` instead has target the scalar extension of `K_0`. This distinguishes the conventions
of Rouquier v1, §4.1.2, p. 34 and §4.2.4, p. 46. The evident generator image is
`θ_i ↦ [W_{α_i}]`.

1. **Cartan datum (done).** `WeightedGraph.Standing.cartanDatum` uses the symmetrizer and
   total pure-power exponents. `pairDeg_eq_neg_cartanDatum_dot` identifies the standing
   crossing grading for loop-free graphs. `Standing.isRouquierQ` verifies B's polynomial
   conditions.
2. **Graded loading-family transfer.** Proposition 2.14 (`spacedEquiv`) identifies `R(ν)`
   with a corner of the matrix algebra indexed by sequences of weight `ν`. It is not in
   general a corner of the chamber algebra itself: different sequences can give the same
   chamber. `GradingDatum.spacedHom_entry_mem_grade`, `spacedEntryMap`,
   `spacedEntryMap_mul_of_right_support` and `GradingDatum.spacedEntryMap_mem_klrGrade`
   give homogeneous maps on individual sequence corners and preserve composable products.
   `GradingDatum.indIdemIso` and `GradingDatum.indK0_ofIdempotent` identify products of
   homogeneous principal-projective classes under juxtaposition.
3. **Serre relations and descent.** Transfer B along the loading-family maps, check the
   divided-power normalization and products, and descend to the integral form. The generic
   quantum-group map is obtained after scalar extension.
4. **No surjectivity assertion.** The earlier roadmap incorrectly read Proposition 2.18
   as generation of all weighted projectives. That proposition (v4, p. 11) identifies the
   ordinary KLR subcategory, and Theorem 2.19 does not assert surjectivity. In the parallel-edge
   example described in A, both products of single-colour projectives at weight `α_a+α_b`
   pair to zero with the simple supported in the middle chamber, whereas its chamber
   projective pairs to one. Thus the generator image need not be all of weighted `K_0`.

## D. Antipode

KL I constructs the antipode on `K_0(R)` from the bialgebra structure on `'f`. With C surjective,
the same descent works when the map in C is an isomorphism; Webster states the Hopf structure
without proof and `K_0(W)` may be larger than the image of `U_q^+` when `Γ` has loops. Plan to be
written when A–C are done.
