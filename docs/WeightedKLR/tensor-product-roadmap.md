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
The canonical identification `FirstWeight.tensorModuleEquiv` sends the prescribed
divided projectives to their tensor vectors. The additional claim about the
graded pairing fails for two fundamental factors with the printed conventions,
as computed below. The repository uses left projectives;
Definition 4.34 uses right projectives. In the computation by a diagram
corner this reverses the source and target endpoint arguments.

| Source input | Formalization | Remaining identification |
|---|---|---|
| Proposition 3.21, one-factor highest-weight representation | For Rouquier parameters over a field, a finite simple-root index set and an X-regular root datum, `CycKLR.projectiveIntegralEquiv` identifies the total cyclotomic projective group with the integral highest-weight lattice. It sends each divided projective word to its divided lowering word on the highest vector and intertwines induction and normalized restriction with F and E. | The final-factor simple-top tests of this lattice enter the proof of the multi-factor identification. |
| Theorem 4.20, single-red algebra | `SingleRed.cyclotomicEquiv` identifies the one-red block with the monomial cyclotomic algebra for every black multiset over a commutative ring. | `SingleRed.totalCyclotomicK0Equiv` identifies the graded projective groups and `cyclotomicK0Equiv_sequenceProj` identifies each word projective. `Stendhal.blackLower` independently defines right black-strand induction for arbitrary red families. `SingleRed.blackLower_totalCyclotomicK0Equiv` identifies it with the transported one-factor operator on every projective class. |
| Proposition 4.18, adding the last red strand | `appendRedEquiv` identifies the shorter algebra with the terminal-red corner for the homogeneous parameters of §2.2. `appendRed_mem_grade` proves homogeneity. | `lastRedIndK0_sequenceProj` appends red on sequence projectives. `exists_lastRedIndK0_of_retract` gives the induced class of every graded retract of the terminal-red left ideal. |
| Lemmas 4.35 and 4.36, projective decompositions and pairing | `Stendhal.finrank_homGrade_sequenceProj` computes the dimension of the homogeneous Hom between undivided sequence projectives from the quotient basis. | Match the graded projective decompositions with the quantum commutator and identify the Hom pairing with the tensor product pairing, including divided powers. |
| Lemma 4.37 and Theorem 4.38 | `Stendhal.tensorProductVacuumK0Equiv_regular` identifies the vacuum class for every red family. `Stendhal.emptyTensorK0Equiv` accounts for every weight of the empty family. | At one black strand, `FirstWeight.sequenceProjBasis` gives a basis indexed by black positions when every red multiplicity at that colour and all dot degrees are positive. For one factor `SingleBlack.oneBlackLatticeEquiv_regular` identifies the regular class with Fᵢ applied to the highest vector. `lastRed_boundary_mem_span` truncates a constant block after the last red via the boundary with one fewer black strand on its right. In the quotient by smaller suffixes, `sandwich_mem_range_suffixConcat` gives affine juxtaposition spanning and `lastRedLayerTensor_surjective` presents each fixed-weight layer corner as a quotient of the shorter tensor product algebra tensored with the final-weight cyclotomic algebra. `exists_lastRedLayerIdem_mul_boundary` covers every ordered loading and `lastRedLayerTensor_mem_grade` identifies the grading on the presentation. Over any field with Rouquier parameters, `lastRedLayerSourceIndecClassEquiv` indexes the source indecomposable classes by pairs of classes of its factors. `lastRedStandardHeadEquiv` indexes the shift classes of the whole block by the split and its two factor classes. Consequently `lastRedK0_rank_eq` identifies its Laurent rank with the sum over splits of the products of the factor ranks. `FirstWeight.exists_tensorWordEquiv` identifies the whole projective group with the integral tensor lattice and sends every divided word to its prescribed vector. The printed pairing clause fails on the first lowering of two fundamental factors. |


**Lemma 4.37.** The integral generation statement holds for all red families
and black weights over any field with Rouquier parameters.
`Stendhal.span_dividedSequenceProj` uses the graded surjection
`Stendhal.affineTensorProjection` from an ordinary KLR algebra with one strand
of each red colour. Fitting decomposition in degree zero lifts idempotents to
the affine algebra. Extending the affine nilHecke projectives gives precisely
the shifted divided-word projectives in the violating quotient.

**Lemma 5.9 and the rank equality.** `eq_cornerKernel_iff_simpleQuotient`
identifies the unique maximal submodule of a module generated on a simple
corner as the vectors killed by every operator $ea$. Its homogeneous
quotient retains the whole corner. For any factor simple at any black
weight, `nonempty_lastRedInducedCut` identifies the fixed space of the
last-red sector in its standard module with the inducing simple via the
identity shuffle. A cut with greater black content in any prefix colour
has a sector lift acting by zero. The head inherits this support, so its
maximal cut and the simple there recover the two inputs.
`lastRedStandardHeadEmbedding` gives the reverse injection. Together with
`lastRedRankEmbedding` and finiteness, this yields the bijection
`lastRedStandardHeadEquiv` and the Laurent rank equality `lastRedK0_rank_eq`.

**Graded standardization.** Starting from a finite graded module for the
earlier tensor block tensored with the final cyclotomic block,
`standardizationGFin` grades the ordered quotient of its affine parabolic
induction. Projection identifies every ordered fixed space degree by
degree. At each such loading, `gdimPoly_standardization` computes its
Laurent character by the graded affine shuffle formula. On the final
highest-weight factor, `cyclotomicTopTest_point` gives the rational
coordinates dual to its projective shift classes. `cyclotomicTopTest_mask`
evaluates each coordinate on the right-assigned black word as the graded
dimension of the corresponding simple's loading space. A different
black content gives zero by `cyclotomicTopTest_mask_of_ne`. For an external
tensor product, `gdimPoly_standardization_extTensor` gives a sum over
admissible shuffles of products of the earlier and final boundary
characters.

**First lowering component of Theorem 4.38.**
`FirstWeight.sequenceLatticeEquiv_boundary_shift` identifies every boundary
projective with its prefix-lowering vector in the integral tensor product of
the highest-weight modules. The current component proof assumes a finite
X-regular root datum, positive multiplicity at the chosen colour for every
factor and positive dot degrees. For one red factor, `SingleRed.homForm_eq_shapovalov` identifies the Euler and normalized Shapovalov forms on every pair of virtual projectives in every black weight. The all-weight word comparison also covers zero red multiplicities.

**Compatibility of the pairing conventions.** In Proposition 4.33 the
identity relating the bar-conjugate coproduct to the adjoint in (3.24) fails
for the coproduct of §1.2. On two fundamental sl₂ modules, write h for the
highest vector and f for Fh. For u = F, the two sides applied to h ⊗ f give
h ⊗ h and q² h ⊗ h. For two arbitrary dominant factors, `TensorPairing.correctedForm_adjoint`
proves the adjunction of Proposition 4.33(2) with the ordinary coproduct
and (3.24) by applying the printed intertwiner to the second argument of
the factorwise form. The proof uses a finite simple-root index set and
X-regular root datum. The form is bar-semilinear in the first argument
and linear in the second. Its restriction along appending a highest
vector is the one-factor form by `correctedForm_append_highest`.
The all-weight comparison with graded Hom in Theorem 4.38 remains open. The integral generation in Lemma 4.37
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
on this diagonal entry. For the repaired form, `fundamental_prefix_homGdimPoly_eq_correctedForm`
identifies all four entries in this weight. The earlier diagonal is 1
and both off-diagonal entries are q. Nonvanishing of the two crossing
maps follows from their composition, the nonzero terminal dot.
The printed diagonal comparison is independent of the passage between
left and right projectives. The underlying module comparison in all weights uses standard-module characters.

**Ordered form of Proposition 4.33.** For any finite ordered family,
`TensorPairing.orderedForm_adjoint` proves adjunction for the ordinary
coproduct using the inverse normalized intertwiner on the second
argument. The empty family gives the scalar bar pairing.
`orderedForm_append_highest` preserves the prefix form and
`orderedForm_binary` identifies the two-factor specialization with
`correctedForm`.

**Tensor generators and the last-red filtration.** The prescribed tensor
vectors span the integral tensor lattice by `FirstWeight.span_tensorWordVector`.
The divided coproduct expresses a pure tensor with a lowered last factor
in terms of a divided lowering of a shorter word and smaller powers on the
last factor. On the algebra side, `Stendhal.blocksK0Equiv` identifies the
external product of two independent red blocks over any field with Rouquier
parameters. This follows from finiteness and scalar endomorphisms of their
simple modules. `FirstWeight.span_tensorWordProjectiveClass` gives integral generation on
the diagram side using the same ordered divided words. For each pair of factor
simple tops, `FirstWeight.standardizationTestAt_word` identifies the graded
character of the standard module with the product of the two rational word
coordinates. These coordinates separate the rational tensor space. Together with
the rank bound they give equality of the integral word relations in every black
content and hence the Laurent-semilinear isomorphism
`FirstWeight.exists_tensorWordEquiv` by induction on the number of red factors.
`FirstWeight.barTensorWord_sum_eq_zero_iff` compares relations for the
two coproduct conventions on the representation side.


**Support on a layer.** For a nonzero representation of a red block,
`Stendhal.exists_detecting_lastRedCorner` produces a split of the black
content and a last-red quotient through which the representation factors.
The corresponding corner acts nontrivially. Its graded projective group is a quotient of that of the tensor product of the earlier red block and the final cyclotomic block by `Stendhal.lastRedLayerK0_surjective`. For a homogeneous boundary
map whose image exhausts a corner, `Stendhal.boundaryClassEmbedding`
injects the shift classes of the detected projectives into the shift
classes for the source algebra.

**Raising on the vacuum edge of Theorem 4.31.** For any red family over a
field with Rouquier parameters, `tensorProductVacuumK0Equiv_blackResVacuumProj`
identifies the class of raw right-black restriction with the graded Hom
polynomial from induction of the vacuum. For two fundamental sl₂ factors
over ℚ, `fundamental_restriction_eq_E` identifies the normalized
restriction with E on both first-weight boundary projectives. General
black contents still require preservation of projectives and identification
of the normalized action.
