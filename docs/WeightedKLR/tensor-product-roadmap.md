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
  hold over any field for homogeneous Rouquier parameters.
* For an arbitrary ordered family of reds, the coefficient of degree `d` in
  `Stendhal.cornerPolynomial` gives the dimension of the homogeneous corner
  with two prescribed boundary words (`sequenceCornerPoly_eq_wordCornerPoly`,
  `sequenceCornerPoly_coeff`). A red letter carries its weight. For a prefix
  `u`, let `pᵢ(u)` be the sum of its red multiplicities at `i` minus the sum
  of the Cartan entries `aᵢⱼ` of its black letters. When the source ends in
  black `i`, delete that letter and sum over all occurrences of black `i`
  in the target. If `u` is the shortened source and `v` precedes the
  target occurrence, multiply the smaller polynomial by
  `qᵢ^(pᵢ(u)−1) [pᵢ(v)]ᵢ`. Reflection handles a terminal black on the
  target and common final reds can be removed. The empty corner has
  polynomial one. The result includes repeated and interacting colours.
  In particular, `finrank_sequenceCornerGrade_eq_of_parameters` gives equal
  dimensions in every degree over any two fields with homogeneous Rouquier
  parameters for the same Cartan datum.

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
| Lemmas 4.35 and 4.36, projective decompositions and pairing | `Stendhal.finrank_homGrade_sequenceProj` computes the dimension of the homogeneous Hom between undivided sequence projectives from the quotient basis. | The repaired pairing is proved on all virtual projectives, including divided powers. The three corrected isomorphisms hold for induction and restriction words on projectives. Identification with the double Stendhal boundary ideals of Definition 4.34 remains open. |
| Lemma 4.37 and Theorem 4.38 | `Stendhal.tensorProductVacuumK0Equiv_regular` identifies the vacuum class for every red family. `Stendhal.emptyTensorK0Equiv` accounts for every weight of the empty family. | At one black strand, `FirstWeight.sequenceProjBasis` gives a basis indexed by black positions when every red multiplicity at that colour and all dot degrees are positive. For one factor `SingleBlack.oneBlackLatticeEquiv_regular` identifies the regular class with Fᵢ applied to the highest vector. `lastRed_boundary_mem_span` truncates a constant block after the last red via the boundary with one fewer black strand on its right. In the quotient by smaller suffixes, `sandwich_mem_range_suffixConcat` gives affine juxtaposition spanning and `lastRedLayerTensor_surjective` presents each fixed-weight layer corner as a quotient of the shorter tensor product algebra tensored with the final-weight cyclotomic algebra. `exists_lastRedLayerIdem_mul_boundary` covers every ordered loading and `lastRedLayerTensor_mem_grade` identifies the grading on the presentation. Over any field with Rouquier parameters, `lastRedLayerSourceIndecClassEquiv` indexes the source indecomposable classes by pairs of classes of its factors. `lastRedStandardHeadEquiv` indexes the shift classes of the whole block by the split and its two factor classes. Consequently `lastRedK0_rank_eq` identifies its Laurent rank with the sum over splits of the products of the factor ranks. `FirstWeight.exists_tensorWordEquiv` identifies the whole projective group with the integral tensor lattice and sends every divided word to its prescribed vector. The printed pairing clause fails on the first lowering of two fundamental factors. The repaired form gives the Euler pairing on the entire direct sum. |


**Projective decompositions in Lemma 4.35.** Over a field with Rouquier
parameters and the canonical grading, `Stendhal.oneUpward_swap_ne`
commutes distinct black colours across an intervening red word.
For equal colours, write n for the coroot weight immediately before the
lowering, including the intervening reds. The summand for deleting the
two black strands occurs on the EF side for n ≥ 0 and on the FE side for
n ≤ 0. Its |n| copies have shifts dᵢ(2t+1−|n|) for 0 ≤ t < |n|.
Both isomorphisms survive any suffix of reds and downward black strands
(`oneUpward_swap_of_nonneg`, `oneUpward_swap_of_nonpos`).
The proof identifies classes using the tensor representation and lifts the
equalities by graded Krull–Schmidt. It uses a finite set of simple roots.
The auxiliary root datum realizes the given red labels without a separate
weight-realization hypothesis. On the right-module side, `sequenceProj_rightEquiv`
identifies the reflected left sequence ideal with the right sequence ideal,
and `rightTwistWordDecomposition` preserves the shifts of its summands.
The README records the corrections to the
indices and the one-factor counterexample.

To identify these module isomorphisms with the decomposition of the
signed boundary ideals, construct the double Stendhal algebra, identify
its all-down corner with the existing algebra (Lemma 4.28), and prove
that the corner idempotent gives the Morita equivalence (Theorem 4.29).
The upward boundary operation must then agree with normalized restriction.
The diagrammatic crossing, cup and cap maps in the proof of Lemma 4.35
and their 2-action relations are further targets. Extending the
tensor-representation argument beyond finite simple-root index sets
also remains open.

**The all-down corner and fullness in §4.5.** `DoubleBoundary.allDownEquiv`
identifies the all-down boundaries of fixed black content with the existing
ordered KLR sequences. The inclusion preserves and reflects the violating
condition. The region-labelled generator signature uses KL black layers and
both red/black crossing orders. From any signed triple, every horizontal cut
is a unique triple with the same ordered red family and exterior weights
(`DoubleDiagram.existsUnique_triple_at_cut`).

For an ambient presentation, fix the left weight at zero and fix the right
weight. The kernel of projection on Hom is exactly the span of composites
through violating boundaries in this fibre
(`DoubleViolatingQuotient.ker_mapLinearMap`). In particular, a cup followed
by a cap at the left edge gives zero (`DoubleDiagram.map_leftBubble_zero`).
The quotient uses vertical composition. A strand to the left of the first
red can cease to violate after adding a new red strand on the left.
Equation (4.4e) gives the inverse red/up crossings in arbitrary contexts.
Relations (2.3c) and (2.4a) factor the mixed black identity through the
swapped pair and, for equal colours, through the word with both strands
deleted. In `DoubleDiagram.id_mem_allDownFactorSpan` these relations and
(4.4e) move the first upward strand to the left or remove it together
with a downward strand. Every surviving identity is a finite sum of
composites through all-down boundaries. Splitting the resulting retracts gives
`DoubleDiagram.allDownCompletionInclusion_isEquivalence_addRelations`
on ungraded additive idempotent completions over a commutative ring.
Both statements allow further local relations. In the fibre with no reds,
`DoubleDiagram.vacuum_algebraMap_surjective` shows that scalars span the
endomorphisms of the empty word. Every nonempty diagram starting there
first crosses a violated cut.

For the ordinary algebra, `Stendhal.ker_affineTensorProjection` gives the
kernel of the affine presentation used to construct a map into the all-down
corner. In the affine Stendhal algebra, `exists_redsFirst_compression`
proves injectivity of the two shuffles that move reds to the left.
`exists_redsFirst_tensor_ideal_element` detects every nonzero ideal after
tensoring with a free coefficient algebra. The ambient signed comparison of
Lemma 4.26 requires a further independence result. The revised proof uses
a tricolore basis. The proof about the size of the localized morphism spaces
was corrected in the later account. [Webster v3, Lemma 4.29](https://arxiv.org/pdf/1309.3796v3#page=42)
· [Webster, arXiv:1209.0051v5, p. 29](https://arxiv.org/pdf/1209.0051v5#page=29)

The ordinary map of Lemma 4.28 is `DoubleDiagram.ordinaryToDownwardMatrix`.
It sends each idempotent, dot and crossing to its signed downward diagram and
takes values in the same presentation as the all-down generation theorem.
The physical red exponents are the coroot pairings. The current ordinary
algebra encodes a red label by a finitely supported function of its black
colour; `ordinaryToDownwardMatrix_ofWeights` supplies this support when
the set of simple roots is finite. With no red or black boundary strands,
`vacuum_algebraMap_bijective` computes the vacuum corner for these relations
over the free signed base. With other boundaries,
`id_mem_allDownContentFactorSpan` restricts factorizations to exactly the
prescribed ordinary black multiset, even when simple roots are dependent.

For the cyclotomic representation in Theorem 4.25, `cyclotomicRedProjection`
is the quotient for an increase of highest weight, and
`cyclotomicRedPullbackResIso` commutes pullback along it with right-black
restriction on modules. The components act identically on underlying vectors.
This gives the red/up crossing in that representation.

For the empty red family, `ordinaryToDownwardMatrix_bijective_empty_red`
proves bijectivity over a free base with the downward, mixed black and red/up
relations: at nonzero black content both sides vanish, and at content zero
the comparison fixes scalars. For an arbitrary red family the signed Hom
from the finite all-down sum to a boundary of matching content is a finite
projective right module over the all-down endomorphism ring
(`boundaryRightModule_finite_projective`). Identifying this module with the
ordinary graded module in Definition 4.34 requires the general corner theorem.

`exists_downPresentedLift` lifts a diagram all of whose layers are downward
to an ordinary diagram. The signed relations now include the straddled
red/cap equation (`redCap_slide`) and the degree and inversion relations for
real and fake black bubbles (`bubble_eq_of_le`, `bubbleGrassmannian`). The README
records the corrections to (2.2a–b). For the cyclotomic action,
`cyclotomicRedDownQuotient_tmul` computes the quotient crossing on a simple
tensor and `cyclotomicRedDownQuotient_surjective` proves every component is onto.
Across all black contents `cyclotomicRedDotCrossing_tmul` gives the reverse
crossing on arbitrary lifts of the algebra factor. Multiplying the kernel of the
cyclotomic projection by the last-dot power lands in the earlier-strand relations
and the larger cyclotomic ideal (`redDot_cycIdeal_cut`). Balancing the tensor
kills these terms. Both composites equal the prescribed dot powers as natural
transformations. On the singleton block `singletonRedCrossing_trace` identifies
the two crossings as adjoints for the Frobenius pairings. When the last colour
is already present and both coroot weights are positive,
`redProjection_positive_polynomial` compares the cap traces on the polynomial
summand. The opposite mate on the entire induction corner remains open.

For all-down boundaries `boundaryRightModuleDownEquiv` identifies the signed
module with the principal right ideal at the diagonal idempotent. Precomposition
acts by right matrix multiplication. The cup and cap relations, the red/up
inverse relation, the downward bigon and the dot slide imply
`ccwBubble_slide`: a real counterclockwise bubble with m dots immediately
to the left of red equals one with m+d dots to its right, for red multiplicity d.

The printed inverse-bubble bound forces the all-down corner to vanish whenever
an exterior coroot weight is negative. With one fundamental sl₂ red and one
black the ordinary block is ℚ and the far-right weight is −1. Theorem
`printedBubble_no_injection_sl2` rules out even an injective comparison if the
printed constant coefficient is imposed. The rest of this roadmap concerns
the corrected inverse-series relation in the README.

To finish Lemma 4.28 in general, impose the remaining relations in Definition
4.24, straighten signed diagrams with all-down boundary into downward diagrams,
and prove the ordinary map is faithful modulo the violating ideal. The cited
tricolore basis is stated over ℂ[z]. The one-upward-colour proof in the revised
Lemma 4.29 provides a route over arbitrary fields. [Webster, Unfurling, Theorem 5.11](https://arxiv.org/pdf/1603.06311#page=41) The
identification of the corner is the remaining input for the ungraded Morita
comparison with the ordinary algebra in Theorem 4.29.

For a comparison of the full black presentations, Cautis–Lauda §2.2
assigns dual parameters to the downward KLR relations. For disconnected
colours with both leading coefficients 2 over ℚ the downward bigon
polynomial of that presentation is 1/2, whereas Webster (2.5e) gives 2.
Transporting the black presentation by reflection requires also verifying
the crossing normalization against the two pitchfork relations.
[Cautis–Lauda, arXiv:1111.1431v3, p. 6](https://arxiv.org/pdf/1111.1431v3#page=6)
· [Webster, arXiv:1309.3796v2, §2.2](https://arxiv.org/pdf/1309.3796v2#page=11)

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
For the repaired ordered form, `FirstWeight.tensorModuleEquiv_homForm` gives the Euler pairing on the entire direct sum. The integral generation in Lemma 4.37
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
restriction with E on both first-weight boundary projectives. For all black contents, `projective_blackRes` proves preservation
of projectives and `blackRaise` gives normalized restriction on graded K₀.
For the canonical grading, `FirstWeight.tensorModuleEquiv_E` identifies it
with the raising generator of the ordered tensor product on every integral
projective class. In a boundary word, an occurrence of colour i contributes
its deletion with quantum integer given by the i-coroot weight of its prefix.
Agreement of the two deletion sums passes to divided words by cancellation
of their quantum factorials. The hypotheses on the root datum and labels
are the same as for `FirstWeight.tensorModuleEquiv`.

In the enlarged ordinary cyclotomic algebra, each red label has its own
simple root. Setting red dots and unordered-red idempotents to zero gives
the Stendhal algebra by `cyclotomicCoverQuotientEquiv`; the map preserves
the canonical grading by `cyclotomicCoverToTensor_preservesGrading`.
A cyclotomic sequence projective restricts to a summand of a sum of shifted
projectives obtained by deleting one black strand
(`CycKLR.restriction_sequence_summand`). Thus restriction preserves the
unordered-red ideal. The central dot sum for each red colour gives the
corresponding assertion for the red-dot ideal. Together these give the
kernel bound `cyclotomicCoverResMap_ker_le` and projectivity descends.


**The Euler form in Lemma 4.36 and Theorem 4.38.**
For the canonical grading, `FirstWeight.tensorModuleEquiv_homGdimPoly`
identifies the graded Hom polynomial from P to Q with the repaired ordered
form on the images of Q and P. The argument order accounts for left
projectives and the inversion of the grading parameter. Graded Frobenius
reciprocity removes a terminal black strand. Reflection of unshifted
boundary diagrams allows the strand to be removed at either endpoint.
Appending the same final red strand at both endpoints preserves the pairing.
The vacuum normalization starts this induction. The integral spanning
theorem extends it to virtual projectives of fixed black content in
`FirstWeight.tensorHomAgrees_all`. Distinct black contents have orthogonal
weights, giving the total formula `FirstWeight.tensorModuleEquiv_homForm`.
These statements use the finite-index, X-regular root datum and matched
dominant weights of the module identification, over any field with
Rouquier parameters.
