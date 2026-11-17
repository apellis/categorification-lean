# Cyclotomic quotients and tensor product categorification

Targets 4 and 6 of issue #289 concern cyclotomic and red-strand algebras. The
braided Hopf algebra for the weighted induction algebra is a separate result,
recorded in [the Theorem 2.19 roadmap](thm-2-19-roadmap.md).

## Quotient bases and dimensions

* For the ordinary monomial cyclotomic algebra the dimension of a homogeneous
  corner is the number of affine standard terms with its boundaries and degree,
  minus the rank of the cyclotomic relations with those boundaries and degree.
  The latter rank is computed in the affine algebra. Both index families are
  finite for positive dot degrees. Repeated and interacting colours are allowed.
  See `CycKLR.finrank_cornerGrade_eq_card_sub_rank`. The finite deletion
  procedure selects a basis of projected diagrams with an affine span test
  (`CycKLR.exists_gradePBWBasis`, `exists_cornerGradePBWBasis`,
  `exists_homogeneousPBWBasis`).
* The standard terms in Webster, arXiv:1309.3796v2, Proposition 4.16 give a
  basis before imposing the violating ideal. `Stendhal.tensorProductAlgebra_finite` proves finiteness over the coefficient ring for every Rouquier parameter family. Their projections span the
  quotient, and over a field one can select a homogeneous basis from them.
  `Stendhal.coeff_gdim_tensorProductGrade` counts the selected terms.
  `Stendhal.finrank_tensorProductGrade_eq_card_sub_rank` computes the dimension
  using products through violated cuts, under the hypotheses of the ambient
  standard-basis theorem. In particular, its weighted presentation uses
  loop-free data and zero black edge weights.
* For ordinary cyclotomic corners the closed graded formula of Hu–Shi,
  arXiv:2108.05508v5, Theorem 1.1 is
  `CycKLR.gdimPoly_corner_permutationFormula`. It sums over all
  permutations matching the two boundary words, including repeated and
  interacting colours. Its specialization at 1 gives the ungraded
  dimension by `CycKLR.finrank_corner_permutationFormula`. Both formulas
  hold over any field for homogeneous Rouquier parameters. The additional
  red boundaries of the general Stendhal quotient use the degreewise
  relation-rank formula above.

## Tensor product categorification

The target is Webster, arXiv:1309.3796v2, Theorem 4.38. For a family of
dominant weights the sum of the graded projective Grothendieck groups is
identified with the tensor product of the integral highest-weight lattices.
The identification specifies the images of the diagram projectives and
identifies their graded pairing. The repository uses left projectives;
Definition 4.34 uses right projectives. In the computation by a diagram
corner this reverses the source and target endpoint arguments.

| Source input | Formalization | Remaining identification |
|---|---|---|
| Proposition 3.21, one-factor highest-weight representation | For Rouquier parameters over a field, a finite simple-root index set and an X-regular root datum, `CycKLR.projectiveIntegralEquiv` identifies the total cyclotomic projective group with the integral highest-weight lattice. It sends each divided projective word to its divided lowering word on the highest vector and intertwines induction and normalized restriction with F and E. | Transfer this one-factor identification to multiple red factors via the decompositions and pairing in §4.7. |
| Theorem 4.20, single-red algebra | `SingleRed.cyclotomicEquiv` identifies the one-red block with the monomial cyclotomic algebra for every black multiset over a commutative ring. | `SingleRed.totalCyclotomicK0Equiv` identifies the graded projective groups and `cyclotomicK0Equiv_sequenceProj` identifies each word projective. `Stendhal.blackLower` independently defines right black-strand induction for arbitrary red families. `SingleRed.blackLower_totalCyclotomicK0Equiv` identifies it with the transported one-factor operator on every projective class. |
| Proposition 4.18, adding the last red strand | `appendRedEquiv` identifies the shorter algebra with the terminal-red corner for the homogeneous parameters of §2.2. `appendRed_mem_grade` proves homogeneity. | `lastRedIndK0_sequenceProj` appends red on sequence projectives. `exists_lastRedIndK0_of_retract` gives the induced class of every graded retract of the terminal-red left ideal. |
| Lemmas 4.35 and 4.36, projective decompositions and pairing | `Stendhal.finrank_homGrade_sequenceProj` computes the dimension of the homogeneous Hom between undivided sequence projectives from the quotient basis. | Match the graded projective decompositions with the quantum commutator and identify the Hom pairing with the tensor product pairing, including divided powers. |
| Lemma 4.37 and Theorem 4.38 | `Stendhal.tensorProductVacuumK0Equiv_regular` identifies the vacuum class for every red family. `Stendhal.emptyTensorK0Equiv` accounts for every weight of the empty family. | At one black strand, `FirstWeight.sequenceProjBasis` gives a basis indexed by black positions when every red multiplicity at that colour and all dot degrees are positive. For one factor `SingleBlack.oneBlackLatticeEquiv_regular` identifies the regular class with Fᵢ applied to the highest vector. `lastRed_boundary_mem_span` truncates a constant block after the last red via the boundary with one fewer black strand on its right. In the quotient by smaller suffixes, `sandwich_mem_range_suffixConcat` gives affine juxtaposition spanning and `lastRedLayerTensor_surjective` presents each fixed-weight layer corner as a quotient of the shorter tensor product algebra tensored with the final-weight cyclotomic algebra. `exists_lastRedLayerIdem_mul_boundary` covers every ordered loading and `lastRedLayerTensor_mem_grade` identifies the grading on the presentation. Over any field with Rouquier parameters, `lastRedLayerSourceIndecClassEquiv` indexes the source indecomposable classes by pairs of classes of its factors. `lastRedRankEmbedding` assembles the injections over all black-weight splits, and `lastRedK0_rank_le` bounds the integral Laurent rank by the sum of the products of factor ranks. The general module identification remains open. The printed pairing clause fails on the first lowering of two fundamental factors. |


**Lemma 4.37.** The integral generation statement holds for all red families
and black weights over any field with Rouquier parameters.
`Stendhal.span_dividedSequenceProj` uses the graded surjection
`Stendhal.affineTensorProjection` from an ordinary KLR algebra with one strand
of each red colour. Fitting decomposition in degree zero lifts idempotents to
the affine algebra. Extending the affine nilHecke projectives gives precisely
the shifted divided-word projectives in the violating quotient.

**First lowering component of Theorem 4.38.**
`FirstWeight.sequenceLatticeEquiv_boundary_shift` identifies every boundary
projective with its prefix-lowering vector in the integral tensor product of
the highest-weight modules. The current component proof assumes a finite
X-regular root datum, positive multiplicity at the chosen colour for every
factor and positive dot degrees. For one red factor, `SingleRed.homForm_eq_shapovalov` identifies the Euler and normalized Shapovalov forms on every pair of virtual projectives in every black weight. Removing the positivity restriction and identifying the other weight spaces remain open.

**Compatibility of the pairing conventions.** In Proposition 4.33 the
identity relating the bar-conjugate coproduct to the adjoint in (3.24) fails
for the coproduct of §1.2. On two fundamental sl₂ modules, write h for the
highest vector and f for Fh. For u = F, the two sides applied to h ⊗ f give
h ⊗ h and q² h ⊗ h. The general pairing clause of Theorem 4.38 requires a
choice of compatible conventions. The integral generation in Lemma 4.37
holds independently. See [the calculation on issue #289](https://github.com/apellis/categorification-lean/issues/289#issuecomment-6961908142).


**The tensor form on two fundamental factors.** With the coproduct of §1.2,
the adjoint of (3.24) and the intertwiner of §4.7,
`TensorPairing.printedForm_loweredPair` computes the squared norm of
F(h ⊗ h) as 1 + q⁻². Adjointness would give 1 + q².
`TensorPairing.terminal_homGdimPoly_ne_printedForm` compares the printed form
with the terminal black-strand projective following two fundamental red
strands over ℚ. Its graded endomorphism polynomial is 1 + q² by
`FundamentalCorner.terminal_homGdimPoly`. Thus the
prescribed generators and the printed form in Theorem 4.38 already disagree
on this diagonal entry. The comparison is independent of the passage between
left and right projectives. The construction of a module identification
in the other weights remains open.

**Tensor generators and the last-red filtration.** The prescribed tensor
vectors span the integral tensor lattice by `FirstWeight.span_tensorWordVector`.
The divided coproduct expresses a pure tensor with a lowered last factor
in terms of a divided lowering of a shorter word and smaller powers on the
last factor. On the algebra side, `Stendhal.blocksK0Equiv` identifies the
external product of two independent red blocks over any field with Rouquier
parameters. This follows from finiteness and scalar endomorphisms of their
simple modules. `FirstWeight.span_tensorWordProjectiveClass` gives integral generation on
the diagram side using the same ordered divided words. The map between
the two groups still requires equality of the relations on these words.
`FirstWeight.barTensorWord_sum_eq_zero_iff` compares relations for the
two coproduct conventions on the representation side.


**Support on a layer.** For a nonzero representation of a red block,
`Stendhal.exists_detecting_lastRedCorner` produces a split of the black
content and a last-red quotient through which the representation factors.
The corresponding corner acts nontrivially. Its graded projective group is a quotient of that of the tensor product of the earlier red block and the final cyclotomic block by `Stendhal.lastRedLayerK0_surjective`. For a homogeneous boundary
map whose image exhausts a corner, `Stendhal.boundaryClassEmbedding`
injects the shift classes of the detected projectives into the shift
classes for the source algebra.
