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
as computed below. Webster uses graded right projectives. The proofs below
use graded left projectives, and the headline statements are transported to
right projectives (`FirstWeight.rightTensorModuleEquiv`,
`rightTensorModuleEquiv_homForm`): twisting by horizontal reflection, a
degree-preserving anti-involution, identifies left and right graded
projectives and preserves shifts, direct sums and graded Hom spaces
(`Graded.K0.rightTwistEquiv`, `K0.homForm_rightTwistEquiv`).

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
that the corner idempotent gives the Morita equivalence (Theorem 4.29;
v3 Theorem 4.30). At the standard Khovanov–Lauda black parameters over a
field, the Morita equivalence is `clTensorProduct_moritaEquivalent`.
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

Plan for Theorem 4.25 at the standard KL black parameters. The target is a
pseudofunctor out of the presented 2-category of `clDownwardBlock`, built with
`Diagrams.BicatInterp.presPseudofunctor` as for `cyclotomicPresCL`.
1. Regions. A region weight `x : I ⊕ Fin ℓ → ℤ` lists coroot pairings in
   the coordinate datum. Its red coordinates do not always determine which
   red lines lie to its left: the red block `3·1 - J` of the extended Cartan
   matrix is singular when `ℓ = 3`. So, as in Webster, the region goes to
   the product over highest weights `ν = Σ n_r Λ_r` of the weight-`x`
   categories of the cyclotomic families at `ν`, i.e. modules over
   `CycKLR k Q a_ν β` for the blocks `β` of weight `x`. A red line `r`
   pulls back from the `ν + Λ_r` factor to the `ν` factor.
2. Black strands, dots, crossings, cups and caps take their values from the
   cyclotomic family of Theorem 3.17. Red strands go to
   `cyclotomicRedPullback`. The red/up crossings `a`, `b` go to
   `cyclotomicRedPullbackResIso`. The red/down crossings go to
   `cyclotomicRedDownQuotient` (`a′`) and `cyclotomicRedDotCrossing` (`b′`).
3. Relations. The black relations hold by Theorem 3.17. (4.4a–e) hold because
   `a` and `b` act by identities on vectors. (4.2) is the pair of bigon
   identities `_downQuotient_dotCrossing` and `_dotCrossing_downQuotient`.
   The remaining steps are (4.1a–c), the pitchfork relations, and the
   opposite-cap relations of the signed cap part. Webster proves (4.1a–c) as
   in Lemma 4.12. The cap comparisons above (`redProjection_cyclotomicOppositeCap`,
   `singletonRedCrossing_trace`) are the inputs for the cap relations.

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
summand. On the entire induction corner, `Stendhal.redProjection_cyclotomicOppositeCap`
compares the normalized cap with projection after inserting the red dot power.
In the present-colour case a common positive shift expresses both caps by monic
remainders of dotted affine representatives. In the absent-colour case the last
coordinate of the finite dot basis is the same remainder trace. These arguments
include weight zero. For type A₁, highest weights 3 and 5 with two preceding
black strands give coroot weights −1 and +1. The common projected value on
a crossing difference is a nonzero nilHecke commutator
(`TypeA1Cap.strict_upper_projected_cap`, `strict_lower_cap_ne_zero`).
Functor-level opposite biadjunction in all weights also needs the triangle identities.

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
printed constant coefficient is imposed. A second obstruction survives the inverse-series correction. With disconnected
colours, leading coefficient 2 over ℚ, and one red of weight (1,1), the printed
cup and cap pitchforks in v3 (2.2a) give 8 id = 2 id on the red-first one-black
boundary. The two bigons have coefficient 2 and both closed i-bubbles have
coroot coordinate 1. The ordinary idempotent is nonzero.
`DoubleDiagram.printedPitchfork_no_injection` holds over any additional
signed relations, including the corrected bubble relations. A revised
pitchfork normalization must satisfy c d = 1 on this example; compatibility
with the other relations still needs verification.

For the extended-Cartan cyclotomic cover, `exists_projectedCoverVacuumEntry_ne_zero`
detects every nonzero ordinary element by a projected vacuum matrix entry, with
the reflection `hflip ∘ σ`. The induction and restriction along a signed word
preserve its ordered red subword. An unordered subword or an operator inserting
a dot on a unique red strand gives zero after projection
(`cyclotomicCover_project_unorderedSignedWord`, `cyclotomicCover_project_signedRedDot`).
This supplies the vacuum calculation from the proof of v3 Lemma 4.29 in the cover.
The printed pitchfork obstruction prevents interpreting it as an action of that
signed presentation on the same ordinary algebra.

For the surjectivity part alone, `ordinaryToDownwardMatrix_surjective_of_straightening`
reduces the matrix statement to spanning individual entries. At each horizontal
cut reached from a downward boundary the length is its initial length plus twice
the number of upward strands (`cut_length_from_allDown`). Consequently the
shorter-boundary remainder in cap elimination vanishes. A cap-free representative
already lifts to an ordinary diagram (`exists_downDiagramLift_of_no_caps`).
`redUpWordNaturalIso` moves a red through any upward black diagram, and
`middleRed_triplePoint` moves an intervening red through an upward crossing.
`ccwBubble_afterRedPrefix_zero` removes the positive real counterclockwise
bubbles after any initial red word by moving them to a violated cut.
For the other orientation, `cwBubble_redWord` moves every real bubble to the
left with an increase in dot count. Thus `cwBubble_afterRedPrefix_zero` holds
at every natural dot count, including zero. The suffix can contain signed
black strands. The signed presentation carries the reflected black snake
identities, cyclicity of dots, curl expansions and opposite mixed-crossing
identities in any red context (`blackSnakeLeft_eq`, `blackCup_dot_slide`,
`blackCurlRight`, `mixedBlack_opposite_eq`).

For one dominant red, every surviving diagram is a black diagram on its
right. The reflected KL III downward spanning theorem writes each black term
as a downward diagram times a bubble polynomial. Each positive bubble
generator vanishes at the red prefix. This proves
`singleRed_ordinaryToDownwardMatrix_surjective` over a commutative ring,
for all black contents and the red exponents given by the coroot pairings.
The theorem uses the reflected KL III black relations. At one fundamental red
and one black in type A₁ the remaining dot factors through the violated
loading, giving `fundamentalSingleRed_algebraMap_surjective`.

For a family of red strands, a surviving diagram keeps its leftmost strand
as a spectator at every layer (`left_nonempty_of_diagram_ne_zero`). A black
rectangle between an initial red word and a fixed signed suffix has the same
downward spanning property (`redPrefixBlackEntry_mem_span`). Moving every
positive bubble polynomial of the rectangle past the initial red prefix
gives zero. The suffix is allowed to contain red strands or upward black
strands. This result covers diagrams supported in such rectangles.

At a strict sign change from negative to positive coroot coordinate,
`closeRedBraid_correction_eq_zero` kills the closed divided-difference
correction of the downward black–red–black braid, using reflected KL III
black relations. Each closed braid is zero by a black curl on the appropriate
side of red. This gives a geometric relation beyond the two separate
bubble-series inversions. The latter together with both real slides leave the
first coefficient undetermined at −2 and +2, as shown by
`realRedBubbleSlides_do_not_determine_degree_one`.

Identifying each closed monomial with the product of its two real bubbles
gives the degree-one transport across every strict sign change
(`normalizedBubble_degreeOne`). With N extra dots the closed correction supplies the mixed
coefficient of degree N+1 throughout the interval where neither orientation
has real representatives on both sides. The two single-region Grassmannian
equations and the real slides outside this interval give
`normalizedBubble_slide` for every degree and either orientation. This
uses the reflected KL III black relations, the red/up dot slide, and the
red exponent given by the difference of the two coroot coordinates.

The reflected KL III slides move each bubble algebra element across a black
strand of either orientation, adding only dots on the strand
(`blackCutBubble_mem_leftSpan`). The normalized red slides identify the
images of the bubble algebras at the two cuts adjacent to red
(`redBubbleSlidesLeft_of_ideal_le`). The common cap presentation contains
these signed relations (`signedCapKL_redBubbleSlidesLeft`). Iterating the
moves across a signed prefix and evaluating the far-left cut in the
violating quotient reduces the projected bubble to the span of dot
diagrams. These diagrams preserve forward paths and the crossing count.
The reduction is valid after composing with exterior morphisms and
applying a linear map to the quotient Hom
(`cutProjection_exterior_mem_signedDotSpan`).

The reflected black relations give both half-mate equalities. Thus all six mixed red/black triple points hold for
distinct black colours (`mixedRed_triplePoint_ne`). For equal colours the
middle-downward orders give the negative divided-difference correction in
`mixedRed_triplePoint_correction`.

For caps in arbitrary signed contexts, `capWithRedPassingLeft_down` and its
three orientation variants pass red across both legs. Disjoint blocks commute
and a dotted triangle contracts (`lower_disjoint_blocks`, `dottedSnakeLeft_eq`).
The maximum number of upward strands and then the number of cuts attaining
that maximum give `ordinaryToDownwardMatrix_surjective_of_lowering`.
A general intersecting excursion may introduce a sideways black crossing,
represented by a cup and a cap. Its expansion can return to the original
height. The crossing-count induction
`ordinaryToDownwardMatrix_surjective_of_terminalCaps` treats the sideways
crossing as a single move. The equal-colour mixed corrections contain zero
crossings in place of three, so they are lower terms in every surrounding
diagram by `crossingFreeSpan_in_fewerCrossings`. The signed cap in
`signedCapBlock` sweeps one black leg across an arbitrary word of signed
black and red strands. Its crossing count equals the length of that word.
`pushesTerminalCaps_of_capBlock_steps` reduces the proof to adjoining
one elementary move below this cap. A right-end entry lengthens the cap
word (`capBlock_push_enterRight`), while a crossing in its interior reduces
to a single local braid (`signedCapBlock_crossInside`). All admissible pairs satisfy the required bound in
`signedCapKL_hasCapBraidBound`. The common presentation has exactly the sum
of the relation ideals used in the local calculations. Reflection of the
black KL III relations is explicit in its definition.
`capSuccessor_allCrossings` handles every placement of a crossing preceding
a terminal cap in this presentation. Disjoint crossings interchange, and
the right entrance extends the sweep. The left entrance uses the dotted
cap pitchfork. A crossing at either interior edge produces a bigon, while
crossing the two cap legs produces a dotted curl. The bigon and curl terms
have strictly fewer crossings. The interior case uses the braid bound and
commutes with an arbitrary continuation.

In this presentation, `signedCapKL_downwardDiagramSpan_eq_top` gives
entrywise spanning for any finite ordered family of dominant reds and
any black content. Of the eight placements of a cup, the cup creating
both legs of the cap closes to a bubble. Moving it to the far left in the
violating quotient leaves a sum of dot diagrams. The other placements use
interchange, the triangle identities, and curl and pitchfork reductions.
Together with the dot and crossing cases these exhaust the terminal-cap induction.
`signedCapKL_ordinaryToDownwardMatrix_surjective` gives the resulting matrix
surjection over a commutative ring when the red exponents equal the coroot
coordinates. For finitely many colours
`signedCapKL_ordinaryToDownwardMatrix_ofWeights_surjective` takes the
exponents directly from the weights. Extending the spanning result to
unrestricted Webster black parameters requires comparing the black relations.
The counterexample to faithfulness above applies independently.

For a presentation with compatible pitchfork coefficients, impose the remaining relations in Definition
4.24, straighten signed diagrams with all-down boundary into downward diagrams,
and prove the ordinary map is faithful modulo the violating ideal. The cited
tricolore basis is stated over ℂ[z]. The one-upward-colour proof in the revised
Lemma 4.29 provides a route over arbitrary fields. [Webster, Unfurling, Theorem 5.11](https://arxiv.org/pdf/1603.06311#page=41) The
identification of the corner gives the Morita comparison with the ordinary
algebra (v3 Theorem 4.30, `clTensorProduct_moritaEquivalent`) at the standard
Khovanov–Lauda black parameters; general parameters follow Lemma 4.29 below.

For a comparison of the full black presentations, Cautis–Lauda §2.2
assigns dual parameters to the downward KLR relations. For disconnected
colours with both leading coefficients 2 over ℚ the downward bigon
polynomial of that presentation is 1/2, whereas Webster (2.5e) gives 2.
Transporting the black presentation by reflection requires also verifying
the crossing normalization against the two pitchfork relations.
`rescaledDownward_qCL` computes the resulting downward polynomial and
`rotCrossR_of_cupPitchfork` computes the right rotation by closing the cup
pitchfork. In any linear category over a field with equal nonzero bigon
coefficients and unit bubble closures, `pitchforkCoefficients_mul_eq_one`
shows that a nonzero boundary forces reciprocal cup and cap coefficients.
With unequal bigons, `pitchforkCoefficients_mul_bigon` gives the general
constraint c d p = q, for downward bigon p and sideways bigon q. The printed
pitchforks c = d = 2 of the disconnected example satisfy it for the dual
downward bigon p = 1/2 of Cautis–Lauda, but not for p = 2 from (2.5e).
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
`correctedForm`. `orderedForm_unique` proves Webster's uniqueness by his
induction: `ρ̄` of the subalgebra generated by the `Fᵢ` preserves
`M' = V_{λ₁} ⊗ ⋯ ⊗ V_{λₙ₋₁} ⊗ v_{λₙ}`, and the vectors `g m`, `m ∈ M'`,
span. `orderedForm_nondegenerate` follows from invertibility of the
intertwiner and nondegeneracy of the Shapovalov form.

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
form on the images of Q and P. The argument order comes from the repair
of the form preceding Proposition 4.33 and the inversion of the grading
parameter; it is the same for right projectives, since right twisting
preserves graded Hom spaces (`FirstWeight.rightTensorModuleEquiv_homForm`). Graded Frobenius
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

In the reflected KL III presentation, `capSuccessor_allDots` treats a dot before, on either leg of, inside, or after the terminal cap. The equal-colour passage uses the nilHecke dot correction. Once all downward-boundary entries are spanned, `ordinaryToDownwardMatrix_surjective_of_base_span` transfers that span to the target of the ordinary matrix map.

**Lemma 4.29 for general black parameters.** Bijectivity of the repaired
comparison (`clToDownwardMatrix_kl_bijective`) is proved over a field when
the black parameters agree with the standard Khovanov–Lauda ones off the
diagonal. The vacuum evaluation uses the cyclotomic Cautis–Lauda action, whose
black relations are compared with the presentation only for these scalars:
`t = 1` on black vertices, and `s` vanishes in degrees `p < d_ij`, `q < d_ji`.
To remove this restriction, either extend the black-relation comparison
(`coverLin_blackRel`) to arbitrary Cautis–Lauda scalars or transport
the result along the crossing rescaling `tensorRescale` combined with a
rescaling of the cover action.

## The rest of arXiv:1309.3796v3

Plan for formalizing the paper in full, with numbers checked against v3. Status
key: **done**, **partial**, **open**. The order below is the working order. §3 comes
after §4 because the single-red case of the §4 constructions gives the §3 ones
(Theorem 4.18, `T^λ ≅ R^λ` for one red strand).

### Phase A: the rest of §4

| Result | Content | Status |
|---|---|---|
| Thm 4.28 | `𝒰` acts on the double tensor product algebras `DT^λ` | done: strict pseudofunctor from the 1-cell dual of the KL 2-category to `Cat` (`blackActionPseudofunctor`), built from right whiskering (`violatingWhiskerRight`) and the functorial action of KL 2-morphisms (`blackMap_id`, `blackMap_comp`) |
| Thm 4.30 | `T^λ` and `DT^λ` are Morita equivalent | done (#420) |
| Thm 4.31 | `𝒰` acts on `T^λ`-modules by `βᵤ = e₋ β′ᵤ e₋` | done at the standard KL black parameters over a field: the action of Thm 4.28 on the additive idempotent completions (`StrictPseudofunctor.completion`) for the presentation of Thm 4.30 (`clBlackAction`); its value at `λ - ν` is identified with the completion of the all-down boundaries, with endomorphism ring `T^λ_ν` (`clBlackAction_tensorProduct`). Graded modules and the formula `βᵤ = e₋ β′ᵤ e₋` on algebras are not separately stated |
| Thm 4.25 | representation of the 2-category `𝒯`; red lines act by `I^λ` | in progress: region categories (`regionFamily`) with the black action (`regionPresCL`); red/up iso, red/down quotient and dot crossings with both bigons (`regionRedUpIso`, `regionRedDownQuotient`, `regionRedDownDot`); the opposite counit on interior blocks is the Kang–Kashiwara leftward cap (`globalLoc_capL_app`, `blockLoc_capL`) and slides along red pullback (`redPullback_capL_tmul`). Remaining: the red cup, cap and pitchfork relations and the assembly with `presPseudofunctor`. The action on `T^λ`-modules used in §5 is Thm 4.31, which does not depend on this |
| Prop 4.19 | `T^{λ⁻} ≅ e_ℓ T^λ e_ℓ` | done (v2 Prop 4.18, `appendRedEquiv`) |
| Prop 4.21 | splitting a red strand, `T^{λ′} ≅ e_{λ′} T^λ e_{λ′}` | done (`SplitRed.splitRedEquiv`): with `λ'` splitting `λ_c = λ'_c + λ'_{c+1}`, `T^λ ≅ e T^{λ'} e` for `e` the sum of the idempotents of the loadings with red strands `c`, `c + 1` adjacent, for the crossing parameters of §2.2 (`IsRouquierQ`) |
| Prop 4.32 | `IR^μ I^μ = id` and its commutation with `Eᵢ`, `Fᵢ` | done: `IR^μ Fᵢ I^μ ≅ Fᵢ` on bimodules (`lastRedBlackEquiv`); `IR^μ I^μ = id` is Prop 4.18 (`appendRedEquiv`); `IR^μ Eᵢ I^μ ≅ Eᵢ` over a field by reflection (`lastRedBlackMirrorEquiv`); both raise degrees by `degΨ(λ_ℓ, i)` (`lastRedBlackMap_mem_grade`, `lastRedBlackMirror_mem_grade`) |
| Prop 4.33 | uniqueness of the sesquilinear forms | done (`TensorPairing.orderedForm_unique`, `orderedForm_nondegenerate`): a system of forms that is `τ`-Hermitian and isometric along `V_{λ₁} ⊗ ⋯ ⊗ V_{λₙ₋₁} ⊗ v_{λₙ}` is `orderedForm`, which is nondegenerate in both arguments. Webster's conditions do not fix the form on the empty tensor product; the theorem takes the scalar form `x̄ y` there as a normalization |
| Prop 4.39 | `K₀(T̃^λ) ≅ U⁻_q ⊗ V^λ` | open; taken up after Cor 5.23, whose standard filtrations its proof uses |

### Phase B: §3, cyclotomic quotients

| Result | Content | Status |
|---|---|---|
| Lemmas 3.7, 3.8, Thm 3.9 | 2-functor `G^λ` from `𝒰ᵢ⁻` to bimodules | route steps, not formalized separately (maintainer decision 2026-11-20): the action is obtained by the §4 route (Thms 4.30, 4.31, `clBlackAction_cyclotomic`) |
| Lemma 3.12, Props 3.13, 3.16 | `R^λ ≅ e₋ DᵢR^λ e₋`, Morita equivalence, action of `𝒰ᵢ⁻` | route steps, not formalized separately (maintainer decision 2026-11-20): covered by the §4 route |
| Thm 3.17 | strict 2-functor `𝒰 → Cat`, `μ ↦ R^λ_μ-pmod` | done for every `Q_ij` of Webster's form (`Q_ij(u,v) = Q_ji(v,u)`, unit extremal coefficients `t_ij`, homogeneous) by Kang–Kashiwara and Brundan, as Webster notes after the theorem: `KLR.CyclotomicAction.cyclotomicPresCL` acts on the cyclotomic module categories with `Eᵢ`, `Fᵢ` cyclotomic restriction and induction (both preserve projectives). At the standard KL black parameters over a field it is also the one-red case of Thm 4.31 (`clBlackAction_cyclotomic`), whose value at `λ - ν` is the completion of the all-down boundaries, with endomorphism ring `R^λ_ν` by Thm 4.18 (`SingleRed.cyclotomicEquiv`) |
| Thm 3.18 | `tr^λ : R^λ → k` is a Frobenius trace | done over a field for every `Q_ij` of Webster's form and every cyclotomic quotient (`IsRouquierQ.cyclotomic_frobenius`, from `cyclotomic_trace_nondegenerate` under the hypotheses of Thm 3.17): a `k`-linear trace `R^λ_ν → k` whose pairing `tr (a b)` is nondegenerate on both sides, closing the words `E_t` at the vacuum `R^λ(∅) = k` with the biadjunction of Thm 3.17 (`RouqFamily.wadj`, `RouqFamily.wadjL`, `isNondegTrace_closeTraceIso_of_separating`), where the endomorphisms of the words at the vacuum are `R^λ_ν` (`cycAct_injective`, `cycAct_surjective`); the earlier standard-parameter version is `clCyclotomic_trace_nondegenerate` |
| Cor 3.20 | `p : R^λ → DR^λ` is a Morita equivalence | done at the standard KL black parameters over a field, as the one-red case of Thm 4.30 (`clBlackAction_cyclotomic`): with `DR^λ_ν` realized as `DT^λ_ν` for one red strand, the corner at the all-down boundaries is `R^λ_ν` and their inclusion is an equivalence of additive idempotent completions. Webster's black-only presentation of `DR^λ` (Def 3.1) is not separately compared with `DT^λ` |
| Prop 3.21, Cor 3.22 | `K₀(R^λ) ≅ V^λ_ℤ`, Euler form = Shapovalov form | done |
| Def 3.24, Prop 3.25 (action), Cor 3.26 | universal categorification `Ř^λ` and its `𝒰`-action; `Ř^λ` projective and flat over `Ř^λ_λ`, free over a field `k` | done (`UnivCyc`, `univCyclotomicPresCL`, the action of the presentation over `k` `univCyclotomicPresCLk` by restriction of scalars, its restriction `univCyclotomicPresCLPmod` to `Ř^λ-pmod` (closure under `E_i`, `F_i`: `isFGProj_globalE`, `isFGProj_globalF` via Kang–Kashiwara Cor. 4.6 over every commutative ring), `UnivCyc.projective`, `UnivCyc.flat`, `UnivCyc.free` by a grading and graded Nakayama, via `CycKLR.projective_base`: cyclotomic quotients with monic `a_i` are projective over any commutative base ring) |
| Prop 3.25 (Morita) | comparison with `End_𝒰(⊕ F_i λ)` | done, as the input of Cor 3.27 (maintainer decision 2026-11-21, superseding the earlier route-step decision). Done: the traces `vacTrace` of `y^m mod p_j` generate `Ř^λ_λ` (`adjoin_vacTrace_eq_top`), and at the empty block the clockwise bubbles act by them (`globalLoc_cw_app_of_vacuum`, `coeff_modByMonic_univCycPoly`, via `RouqLoc.cw_hom_app_of_aeval`); `P_∅` is an object `univVacuum` of `Ř^λ-pmod`, killed by every downward strand (`isZero_univPmod_map_vacuum`), so evaluation at `P_∅` kills the ideal `I` spanned by the 2-morphisms factoring through `F_𝐣 E_j 1_λ` (`vacIdeal`, `univVacuum_map₂_eq_zero_of_mem_vacIdeal`, via the generic `TwoRep.factorIdeal`, `TwoRep.map₂_app_eq_zero_of_mem_factorIdeal`). The ideal `I` contains every diagram through a downward strand next to the vacuum (`dg_mem_vacIdeal`), hence the clockwise bubbles at the vacuum (`cwReal_mem_vacIdeal`), the right curl on the strand next to it (`curlR_mem_vacIdeal`) and, by the curl relation, the cyclotomic relation `-∑_f x^{λ^i-f} cw_{f-λ^i-1}` (`curlRHS_mem_vacIdeal`). `I` is a two-sided ideal for composition (`TwoRep.comp_mem_factorIdeal`, `TwoRep.mem_factorIdeal_comp`), and, by the infinite Grassmannian relation at the vacuum region (`vacGrassmannian`, from the general-scalar Grassmannian `CLQ.grassmannian_all`), every element of the bubble algebra at the vacuum is congruent modulo `I` to a polynomial in the fake clockwise bubbles (`mem_vacReduced_of_isBubC`). Upward KLR diagrams at the vacuum region give `vacUpHom` (the KLR relations with the parameters `qCL`, `univScalars_klr`), and through the cyclotomic family `vacUpHom r` acts as `klrAct` of the image of `r` over `Ř^λ_λ` (`upActP_vacUpHom`); its `(t, s)` entry at the vacuum is the class of `hflip (σ (e(s) r e(t)))` in `Ř^λ(ν)` (`vacCoeff`, `vacCoeff_vacUpHom`), and vacuum entries of 2-morphisms in `I` vanish (`vacCoeff_eq_zero_of_mem_vacIdeal`). The counterclockwise bubbles at the vacuum act on `P_∅` by `vacTrace` (`univPres_ccwReal_vacuum`), and bubbles to the right of upward words evaluate by right whiskering through any presentation (`RouqFamily.upEvalP_bubAtC`), so a bubble acting on `P_∅` by `c ∈ Ř^λ_λ`, placed to the right of the upward strands, multiplies every vacuum entry by `c` (`vacCoeff_vacBubMat_mul`; for the counterclockwise bubbles `c = vacTrace`, `vacCoeff_vacBubMat_ccw_mul`). Vacuum entries are multiplicative (`vacCoeff_mul`: the entry of `φ ψ` is the matrix product of the entries of `ψ` and `φ`), so the sum of all entries `vacSum` is a ring homomorphism `vacRingHom` into `Ř^λ(ν)ᵐᵒᵖ`, sending `vacUpHom r` to `hflip (σ r)` (`vacSum_vacUpHom`). The Grassmannian inverse of the vacuum traces is `(-1)^n e_n(p_j)` (`grassInv_vacTrace`), so the fake clockwise bubble of degree index `n ≤ λ^j` acts on `P_∅` by it (`vacEvalLin_cwL`); KLR algebras admit extension of scalars (`KLRAlgebra.extendScalars`), the input for the comparison map `vacTheta` from the KLR algebra over `Ř^λ_λ` to the matrix algebra of upward endomorphisms at the vacuum region (scalars go to fake-bubble diagonals, `vacScalMat`; `vacSum ∘ vacTheta = hflip ∘ σ`, `vacSum_vacTheta`); `I` is stable under right bubbles (`bubAtC_mem_vacIdeal`, through the factorization `vacFactor` at the empty word). Every upward endomorphism at the vacuum region is congruent modulo `I` to an image of `vacTheta` (`exists_vacThetaM_sub_mem`, from `CL.prop310UpC` and `exists_vacScal_eq`), and the universal cyclotomic polynomial in the dot next to the vacuum lies in `I` in context (`vacCurl_mem`, by the right curl relation). The cyclotomic ideal maps into `I` after the flips `hflip`, `σ` (`vacThetaM_sigma_hflip_mem`, via `vacThetaM_cycPoly_mem`), so the kernel of `vacRingHom` is the matrices with entries in `I` (`vacRingHom_eq_zero_iff`); `vacRingHom` is surjective (`vacRingHom_surjective`), and the quotient by `I` is `Ř^λ(ν)ᵐᵒᵖ` (`vacQuotientEquiv`). Between arbitrary words at the region of `P_∅`, evaluation at `P_∅` has kernel exactly `I` (`mem_vacIdeal_of_vacEvW_eq_zero`) and is surjective (`exists_vacEvQ_eq`): sorting both words (`CLQ.decR`), the composites through words with a downward strand next to the vacuum lie in `I` (`vacFactor`, `mem_vacIdeal_of_mem_vacFactor`), and for upward words this is the identification above, with morphisms between upward words of different colour content zero (`CLQ.hom_eq_zero_of_sCnt_ne`, `vacUp_hom_eq_zero`). Used in Cor. 3.27 |
| Def 3.23 | strongly equivariant functors | done: strong transformations of module categories (`TwoRep.StronglyEquivariant`, Webster's condition `StronglyEquivariant.webster_condition`), with the unit and composition axioms of Rouquier's morphisms of 2-representations, which Webster's printed definition leaves out and his "unique up to unique isomorphism" uses; morphisms are modifications |
| Cor 3.27 | universality of `Ř^λ-pmod`; `φ'_C` fully faithful | (1) done: `vacuumFunctor` (existence, for targets with `k`-linear 2-morphism maps, finite biproducts and idempotent completeness, in the universes of `Ř^λ-pmod`), `vacuumFunctorIso`, `vacuumFunctor_modification_ext` (uniqueness), via `Generated.strongTrans` (density `vacuum_isDenseFamily` from `exists_vacuum_retract`, fullness `vacuum_full`, kernel condition `vacuum_kerLe`). (2) done, as the Hom–tensor bijection (maintainer decision): `vacuum_homTensorMap_bijective` (`Hom(M, N) ⊗_{Ř^λ_λ} End(φ_C P_∅) ≅ Hom(φ_C M, φ_C N)` for every strongly equivariant `φ_C`), via the generic `Generated.homTensorMap_bijective`; inputs `univVacuum_smul_id_bijective` (`End(P_∅) = Ř^λ_λ`), `exists_vacuum_up_retract` (retracts of sums of upward images of `P_∅`) and `isZero_vacImg_vacDual` (downward images of `P_∅` vanish) |
| Def 3.28 (v2 only) | the localization `U′`: invert `y` on `F_i`, identify honest bubbles with negative dot counts with fake bubbles | done: `presLoc` (signature `lsig` with inverse downward dots `invDot`, relations `LocRel`), the localization functor `toLoc`, the inverse relations `invDot_comp_downDot`, `downDot_comp_invDot`, and the bubble identifications `cwNegHonest_eq`, `ccwNegHonest_eq`. §3.6 is absent from v3 (arXiv:1309.3796v3, August 2015) |
| Lemma 3.29 (v2 only) | `B′` spans `U′` | done: `span_twoBL_eq_top` (and one-sided `span_oneBL_eq_top`), for `k` a field and every Cartan datum, the hypotheses of KL III Prop 3.11 (`isSpanFamily_twoB`). `B′` = `twoBL`: KL's spanning set with an integer exponent on each strand, placed at the left end of its arc as in `twoB` (negative exponents are inverse dots); `twoBL_of_nonneg` identifies the nonnegative part with the image of `B`. Route: generation of `U′` by `U` and inverse dots (`loc_mem_of_layers`), every 2-morphism is a `U`-morphism up to dots (`mem_coreSet`, cap lemma via KL 3.11 refined by crossing number, `canonSpanLe`), then dots moved to left ends by triangularity |
| Prop 3.30 (v2 only) | weight-shift equivalences of `U′` | done: under Webster's condition `a_i − b_i = α_i^∨(μ − μ′)` (`∀ i, a i - b i = -ip RD i δ`), every relation of `U′` holds under the shift (`shiftRelations`), giving `shiftFunctorOf`; the reverse shift is inverse up to `eqToHom` components (`shiftCompIso`), so `shiftEquivalence` (whole `U′`) and `shiftHomEquivalence` (`U′(μ, μ′) ≌ U′(μ + δ, μ′ + δ)`) |
| Prop 3.31 (v2 only) | `B′` is a basis of `U′` | open; the printed proof does not hold as written: it claims that `Ř^λ` is a `U′`-representation, but for `sl₂`, `λ = 1`, one strand, at region weight `-1`, the honest bubble with `-1` dots acts on `Ř^λ` by `-1/z ≠ 0`, while in `U′` it equals the fake bubble of negative degree, which is `0`. Maintainer decision (2026-11-21): formalize Def 3.28, Lemma 3.29 and Prop 3.30, and record 3.31 as an erratum (README, Webster §3.6 erratum). Roadmap item: prove or refute Prop 3.31; the statement is neither proved nor refuted (a proof needs `U → U′` faithful on Hom spaces) |
| Cor 3.32 (v2 only) | `γ : U̇_ℤ → K₀(𝒰)` is an isomorphism | done (KL III Thm 1.2 for every Cartan datum: `gammaAlgEquiv_unconditional`, `gammaAlg_injective_unconditional`) |

The proved nondegeneracy of the Khovanov–Lauda calculus (`gammaAlg_injective_of_calculusNondeg`,
KL III Thm 1.2) is the input for the basis statements behind Thm 3.17 and Cor 3.26.

### Phase C: §5, standard modules

Done (v3 numbering, `RedStrands/StandardModule.lean`): the preorder of Def 5.1, encoded by the
number of black `i`-strands left of each red strand (`StendhalLE`, `StendhalLT`; the strict
reading of "≥" in Def 5.1 is the one used); `P̃_s`, `U_s` and the standard module `S_s = P̃_s/U_s`
(`seqProj`, `upperSubmodule`, `standardModule`); the cyclotomic step of Prop 5.3: a red strand
followed by a black `i`-strand gives `y^{α_i^∨(λ)} e(s) ∈ U_s` (`dotPow_mem_upperSubmodule`), via
the bigon through the strictly higher sequence (`StendhalAlgebraAllOrders.dotPow_e_eq`).
`RedStrands/StandardAction.lean`: the idempotent `e_α` of a root function (`rootIdem`), `U_α`
and `S_α` (`rootUpper`, `rootStandard`), and the action of the corner `e_α T̃^λ e_α` on `S_α`
by right module endomorphisms (`rootAction`; generic form `cornerQuotientAction`), with the
cyclotomic relations acting by zero (`sandwich_dotPow_mem_rootUpper`,
`rootAction_eq_zero_of_mul_mem`).

Prop 5.3 is done (`RedStrands/StandardBlockAction.lean`): the block maps `R(b_j) → e_α T̃^λ e_α`
act on `S_α` (`rootBlockAction`), the cyclotomic ideal of `λ_r` acts by zero on the block right of
the red strand `λ_r` (`cycBlockAction`), and the commuting actions assemble into the algebra map
`R(b_0) ⊗ R^{λ_0}(b_1) ⊗ ⋯ ⊗ R^{λ_{ℓ-1}}(b_ℓ) → End_{T̃^λ}(S_α)` (`blockAction`; the generic
`PiTensorProduct.liftCommuting`). Def 5.4 is done (`RedStrands/Standardization.lean`): the
standardization `S(M) = M ⊗_B S_α` of a right module over this algebra `B`, a right
`T̃^λ`-module, functorial in `M` (`Standardization`, `standardizationMap`). The functors `Eᵢ`,
`Fᵢ` on right `T^λ`-modules, as restriction and induction along `appendBlack`, with `Fᵢ ⊣ Eᵢ`
and exactness of `Eᵢ` (`RedStrands/BlackModuleFunctors.lean`), are the module-level functors of
Prop 5.5. On the all-down block these module functors are the categorical ones
(`RedStrands/DoubleBlackInduction.lean`): for `M` in the completed block of content `ν`,
inducing `Hom(⊕ O_ν, M)` along the matrix map of `Fᵢ` gives `Hom(⊕ O_{i+ν}, Fᵢ M)`
(`blackHomInd`), and at the standard Khovanov–Lauda parameters over a field the same holds
for induction along `appendBlack` of right `T^λ_ν`-modules, through the repaired Lemma 4.29
(`clBlackHomInd`, `clBlackHomInd_smul`). Dually (`RedStrands/DoubleBlackRestriction.lean`, Webster's
`Eᵢ` after Thm 4.31), restricting `Hom(⊕ O_{i+ν}, M)` along the matrix map gives
`Hom(⊕ O_ν, Eᵢ M)` (`blackHomRes`, `blackHomRes_smul`), and along `appendBlackOp` over `T^λ`
at the standard Khovanov–Lauda parameters (`clBlackHomRes`, `clBlackHomRes_smul`). Prop 5.5's proof also uses the commutation relations of `𝒰` on modules. These are done on the
all-down matrix ring (`RedStrands/BlackModuleSumDecomp.lean`): `Eᵢ Fᵢ M ≅ Fᵢ Eᵢ M ⊕ M^{⊕ n}` for
`n = ⟨i, λ⟩ ≥ 0` and dually (`blackModuleEFEquiv`, `blackModuleFEEquiv`), for every right
module `M`, from the module-functor descriptions `blackResIndModule`, `blackIndResModule` and
the generic `MatEnd.resIndEquivIndResProd`; Thm 5.8's proof uses the injectivity of
Prop 5.26 for `S(L) e_α ≅ L`.

Route for Props 5.5, 5.7 and the stratification results (chosen 2026-11-20). Webster's printed
proofs work over a field with finite-dimensional graded modules and count dimensions. The route
here works for all right modules over every commutative ring, through an induced model of the
standard bimodule `S_α`:

1. Induced model. Let `R(μ)` be the KLR algebra of `stendhalQ`, `P_α ⊂ R(μ)` the parabolic
   subalgebra of the blocks `b_0 | λ_1 b_1 | ⋯ | λ_ℓ b_ℓ` of `α` (each red strand grouped with
   the black strands to its right), `D` the block algebra of Prop 5.3 (a quotient of `P_α`, the
   one-red factors identified with cyclotomic quotients by Thm 4.18,
   `SingleRed.cyclotomicEquiv`) and `e_F` the sum of the red-ordered idempotents. Set
   `Z_α = D ⊗_{P_α} e_α R(μ) e_F`. A minimal coset representative keeps the order of the strands
   inside each block, so no black strand crosses a red strand to its left.
2. Action. The red dots slide to the top and die in `D`, and a path through a sequence with the
   red strands out of order acts by zero (as in `parabolicShuffle_returns` for the last red
   strand), so `T̃^λ` acts on the right of `Z_α`.
3. Comparison. `Z_α ≅ S_α` as `(B, T̃^λ)`-bimodules: `[a] ↦ [1 ⊗ e_α] a` is defined because
   `Z_α e(t) = 0` when the root function of `t` is above `α`, and `d ⊗ a ↦ d [a]` is its inverse.
4. Consequences. `e_α R(μ)` is free as a left `P_α`-module (KL I Prop 2.16, iterated), so `S_α`
   is projective as a left `B`-module and standardization is exact for all modules (Prop 5.7);
   Prop 5.5 from the last-strand Mackey layers of `Z_α`; Prop 5.6 from Prop 5.5.

Status of §5 in the induced model (two pieces: the first `ℓ` red strands, and the last red strand
with the black strands to its right; this is Webster's partial standardization `S^{λ';(λ_ℓ)}`,
from which the full one is obtained by iterating):

* `RedStrands/ParabolicShuffleDescent.lean`: the standardization `ParabolicStandard N` of a left
  module `N` over `T^{λ'} ⊗ R^{λ_ℓ}(β)`, a left `T^λ`-module (`parabolicStandardAction`).
* Prop 5.7 (`RedStrands/ParabolicStandardExact.lean`): standardization is a functor
  (`parabolicStandardMap`, `parabolicStandardMap_action`) which preserves injections,
  surjections and exactness in the middle (`parabolicStandardMap_injective`,
  `parabolicStandardMap_surjective`, `parabolicStandardMap_exact`), for all modules over every
  commutative ring, from the shuffle decomposition of affine induction.
* Lemma 5.9: `existsUnique_isCoatom_of_idempotent` (`Algebra/UniqueSimpleQuotient.lean`) and
  `eq_cornerKernel_iff_simpleQuotient` (`RedStrands/CornerHead.lean`).
* Thm 5.8, two-piece graded form, over a field at Rouquier parameters
  (`RedStrands/LastRedStandardCut.lean`): standardization recovers the factor simple on its
  maximal cut (`nonempty_lastRedInducedCut`), and taking heads of standard modules is a bijection
  from pairs of factor classes, summed over the last-red weight splits, onto the graded
  indecomposable projective classes of `T^λ` (`lastRedStandardHeadEquiv`), with the resulting
  rank formula `lastRedK0_rank_eq`. These files cite v2; in v3 the statements are Thm 5.8 and
  Lemma 5.9.

* Prop 5.5, `Eᵢ`-part, two-piece form (`RedStrands/ParabolicStandardLast*.lean`), for all left
  modules over a field: for `θ = i + θ₀`, `β = i + β₀`, the last-strand Mackey layers give the
  short exact sequence `0 → S(₂Eᵢ N) → Eᵢ S(N) → S(₁Eᵢ N) → 0` (`lastBlackResTwo_injective`,
  `lastBlackRes_exact`, `lastBlackResOne_surjective`), where `Eᵢ` is restriction along
  Webster's idempotent `appendBlack 1` (`castTensorProductAlgebra_appendBlack_one`). When `i`
  occurs in only one block the sequence degenerates to an isomorphism: `Eᵢ S(N) ≅ S(₂Eᵢ N)` for
  `i ∉ θ` (`rightBlackResEquiv`) and `Eᵢ S(N) ≅ S(₁Eᵢ N)` for `i ∉ β` (`leftBlackResEquiv`).
  Gradings (the shift `⟨αᵢ, λ_j − α(j)⟩`) are not modelled.

* Prop 5.5, `Fᵢ`-part, right exactness (`RedStrands/ParabolicStandardLastInd*.lean`,
  `ParabolicStandardLastKernel.lean`): `S(₁Fᵢ N) → Fᵢ S(N) → S(₂Fᵢ N) → 0` is exact
  (`firstIndDeltaT_exact`, `lastIndQuotientMap_surjective`); the image of the first map is the
  submodule `O` generated by the idempotents whose new strand lies left of the last red strand
  (`lastIndKernel_le_range`, `ker_lastIndQuotientMap`). Injectivity of the first map is open.
  The short exact sequence is stated with injectivity as the explicit route hypothesis
  `FirstIndDeltaInjective` (`firstIndDeltaT_shortExact`, `ParabolicStandardLastIndShortExact.lean`;
  decision 2026-11-21: Props 5.6 onward may use it while the count continues). At the standard
  Khovanov–Lauda scalars `Q = CL.qCL KL` (decision 2026-11-21) the hypothesis is discharged for
  finite-dimensional `N`: Webster's count `dim Fᵢ S(N) = dim S(₁Fᵢ N) + dim S(₂Fᵢ N)`
  (`finrank_firstIndF_eq_add`), proved by strong induction on `|θ| + |β|` from the last-strand
  splitting into a red part and colour pieces (`RedStrands/Prop55Dimension*.lean`), gives
  `firstIndDeltaInjective_std` and `allFiniteDeltaInjective_std`, hence the black-word
  filtrations (`hasFiltration_loadingProj_std`; the finite-dimensional form
  `AllFiniteDeltaInjective` suffices, `ParabolicStandardFiniteFiltration.lean`). The
  intermediate lemmas take a base presentation with `CoverRelsNegligible` and well-founded
  domain; the presentation with no relations (`noRelations`) satisfies both vacuously, so the
  headline results carry no presentation hypothesis. **Roadmap item:** extend the count to
  general scalars `Q`.

* Prop 5.5, empty last block (`RedStrands/ParabolicStandardEmptyRed.lean`): for `β = ∅` the
  factor algebra is `T^{λ'}` (`emptyFactorToOld`) and standardization is the induction along
  `appendRed`, `S(N) ≅ T^λ ⊗_{T^{λ'}} N` as `T^λ`-modules (`emptyRedStandardEquiv`), with
  inverse `z ⊗ n ↦ z · (1 ⊗ n)`; the key identity is that the parabolic affine image of a
  concatenation equals `appendRed` after the factor isomorphism (`emptyF_eq_emptyG`).

* Step in the proof of Prop 5.21 (`RedStrands/TwoPieceStandardEquiv.lean`): for a red-ordered loading `t` of the
  first `ℓ` red strands and a black sequence `u`, the standardization of `S_t ⊠ R e(u)` is the
  standard module `S_{t λ_{ℓ+1} u}` of Def 5.1, `S(S_t ⊠ R e(u)) ≅ S_{tλu}` as `T^λ`-modules
  (`twoPieceStandardEquiv`, `twoPieceStandardEquiv_symm_unit`), for `KLRSymm Q`. The map out of
  the standardization is `parabolicDesc`; the inverse is the lift of the unit of `S_{tλu}`,
  using that loadings above `tλu` act by zero (`parabolicStandardAction_upper_eq_zero`).

* Prop 5.21, filtration form (`RedStrands/ProjectiveStandardFiltration.lean`): every `T^λ e(s)`
  has a finite filtration by standard modules (`hasStandardFiltrations`), by induction on the
  number of red strands: loading decomposition `(s₀, λ_{ℓ+1}, w)`
  (`exists_blackWordLoading_appendRed`), the filtration of Prop 5.5's proof, exactness of `⊠`
  over a field (`hasFiltration_tensorLayer`) and `twoPieceStandardEquiv`. Differences from the
  printed statement: existence of a standard filtration rather than the specific `Φ`-indexed
  filtration `P_{≥φ}/P_{>φ} ≅ S^{κφ}_{iφ}`; route hypothesis `AllFiniteDeltaInjective` for every
  sequence of highest weights (removal tracked with Prop 5.5).

* Cor 5.22, condition on projectives (`RedStrands/StandardStratification.lean`): the kernel
  `U_s` of `T^λ e(s) → S_s` has a finite filtration by `S_t` with `t > s` in Webster's dominance
  order on black counts (`exists_hasFiltration_leftUpper`). It comes from the ordered form of the
  filtration of Prop 5.21 (`RedStrands/ProjectiveStandardFiltrationOrder.lean`,
  `hasOrderedStandardFiltrations`: top quotient `S_{s'}` with `s'` equivalent to `s`, other
  labels strictly above `s`). Difference from the printed statement: Webster states that `T^λ`
  is standardly stratified; the formal statement is the condition on projectives of that
  definition. Same route hypothesis as Prop 5.21.

* Prop 5.21 and Cor 5.22 at the standard Khovanov–Lauda scalars
  (`RedStrands/StandardStratificationStd.lean`): `AllFiniteDeltaInjective` is discharged by the
  dimension count (`allFiniteDeltaInjective_std`), with no further hypothesis.

* Lemma 5.29 and Cor 5.24 (`RedStrands/StandardProjectiveDimension.lean`): projective dimension
  `< n` passes from the subquotients of a finite filtration to the module
  (`HasFiltration.hasProjectiveDimensionLT`), and every standard module has finite projective
  dimension (`exists_hasProjectiveDimensionLT_stdModule`; `_std` at the standard scalars, with
  no route hypothesis). Webster's "finite length projective resolution" is stated as vanishing
  of `Ext` in large degrees (Mathlib's `HasProjectiveDimensionLT`). Same route hypothesis as
  Prop 5.21.

Weak `𝔰𝔩₂`-categorification along an `i`-string (input to Prop 5.12): `fgStringWeakSl2`
(Chuang–Rouquier §5.1.1 structure on finitely generated `T^λ`-modules along `ν₀ + m i`, `i ∉ ν₀`),
from the module-tower constructor `ModuleTower.weakSl2` and the class identity
`fgString_compositionFactors_EF_sub_FE`.

* Prop 5.12 (`RedStrands/BlackModuleSimpleHead.lean`): for `U` simple, any two simple quotients
  of `Eᵢ U` (resp. `Fᵢ U`) are isomorphic compatibly with the quotient maps
  (`fgString_head_E`, `fgString_head_F`), by Chuang–Rouquier Prop 5.20 applied to
  `fgStringWeakSl2`. Inputs: `k`-linearity of `Eᵢ`, `Fᵢ` (`fgStringE_linear`,
  `fgStringF_linear`), the nil-Hecke action of the newest black dot with uniform nilpotency
  exponent (`fgStringNilHecke`, `exists_fgStringNilHecke_X_pow_eq_zero`), and `End(S) = k` for
  simples (`fgString_finrank_end_simple`, via the `k`-dual left module). Hypotheses: standard
  Khovanov–Lauda black scalars and Rouquier scalars; the base presentation of the cyclotomic
  cover taken by `fgStringWeakSl2` is instantiated with `noRelations`, so no presentation
  hypothesis remains.

Open: the comparison of the induced model with Def 5.4 (right modules over `T̃^λ` and the block
algebra of all `ℓ + 1` blocks; the induced model uses left modules, which the vertical flip
`tensorFlip` converts), injectivity in the `Fᵢ`-part of Prop 5.5, Prop 5.6, and the results listed below.

Prop 5.17 (stringy loadings classify indecomposable projectives) is proved:
`Stendhal.maxLoadClassification` (`RedStrands/StringyClassification.lean`). Prop 5.18 (summands
of `T^λ e(s)` surject onto `S_s`, a product of standard quotients) is proved for every orthogonal
idempotent decomposition of `e(s)`: `Stendhal.IsSeqDecomp.leftStandardEquiv`,
`Stendhal.IsSeqDecomp.lIdeal_le_sup` (`RedStrands/StandardSplitting.lean`).

Prop 5.28 of v2 (`End(P⁰) ≅ T^{λ̲} ≅ R^{λ̲}` for `P⁰ = e⁰ T^λ`, `e⁰` the red-first loadings) is
proved as a ring isomorphism of the corner `e⁰ T^λ e⁰` with the cyclotomic KLR algebra of the
total weight, for the crossing parameters of §2.2: `Stendhal.redFirstCornerEquiv`
(`RedStrands/RedFirstCorner.lean`), by repeated red-strand splitting (Cor 4.21 of v2,
`splitRedEquiv`) down to one red strand (Prop 4.20). Deferred: the printed `Φ`-indexed form of
Prop 5.21 (the specific filtration `P_{≥φ}/P_{>φ} ≅ S^{κφ}_{iφ}`), which strengthens the
filtration form above.

Cor 5.29 of v2 (v3: Cor 5.32, double centralizer of `P⁰`) is proved under the route hypothesis
`HasCornerCopresentation e⁰`: `Stendhal.existsUnique_eq_mul_left_redFirst`
(`RedStrands/RedFirstDoubleCentralizer.lean`), from the module-theoretic step
`Categorification.exists_eq_mul_left_of_hasCornerCopresentation`
(`Algebra/SelfDualDoubleCentralizer.lean`); uniqueness (faithfulness, Lemma 5.23) is
unconditional. Roadmap item: remove the hypothesis, i.e. show that `T^λ` has dominant dimension
at least two with respect to `P⁰` (`Ext¹(L, T^λ) = 0` for simples `L` killed by `e⁰`). Webster
obtains this from Mazorchuk–Stroppel, J. Reine Angew. Math. 616 (2008), Cor. 2.6, whose proof
uses Ringel duality for standardly stratified algebras.

Prop 5.30 of v2 (v3: Prop 5.33) is proved under the same route hypothesis, which it inherits
from Cor 5.29: `Stendhal.redFirstEndEquiv` (`RedStrands/RedFirstEndomorphism.lean`) identifies
`T^λ` with the endomorphism algebra of the right module `⊕_s y_s B` over `B = e⁰ T^λ e⁰`,
`y_s = θ̇_s θ_s`, with `a ↦ (θ̇_s e_s x ↦ θ̇_s e_s a x)` (`redFirstEndEquiv_apply`). The generic
step is `Categorification.CornerEndomorphism.ringEquiv` (`Algebra/CornerEndomorphism.lean`); the
inputs are the shuffle factorization `e_s T^λ e⁰ = θ_s B` (`exists_eq_redShuffle_mul`) and
injectivity of `θ̇_s` on `e_s T^λ` (`redShuffleDual_mul_injective`, Lemma 5.23).

Prop 5.6 of v2, character form, is proved: the iterated standardization of cyclotomic word
projectives has the word character of the tensor product of the factors
(`Stendhal.FirstWeight.iteratedStandard_word`, `RedStrands/IteratedStandardCharacter.lean`), from
Cor 3.22 for word projectives (`cyclotomicWordModule_word`) and the product test of Thm 4.38
(`standardizationTestAt_word_of_wordCharacters`). On the projective group, the Hom functional of
the standard module is the form with `s` composed with `η` (`iteratedStandardTest_eq`,
`RedStrands/IteratedStandardK0.lean`); this determines its class. Open, only if a later result
needs it: a formal Grothendieck group of finite-dimensional modules with the dual map `η`.

Standardization functors (Prop 5.3, Def 5.4, Props 5.6, 5.7); simples and crystals
(Lemma 5.9, Prop 5.11, Thms 5.14, 5.15); standard stratification (Lemma 5.19, Prop 5.21 in printed `Φ`-indexed form, Lemma 5.25,
Prop 5.26, Cor 5.27: `V^λ` is a tensor product categorification); Thm 5.28 (finite
projective resolutions); self-dual projectives and double centralizer
(Thm 5.30, Prop 5.31, Cor 5.32, Prop 5.33); Thm 5.34 (for `sl_n`, blocks of cyclotomic
`q`-Schur algebras). Open except as listed above.

### Phase D: §6, braiding functors

Defs 6.1–6.3 and Prop 6.4 are proved (`RedStrands/BraidedStendhal.lean`):
`Stendhal.BraidedStendhalAlgebra` holds the `w`-Stendhal diagrams for all `w` at once, with basis
`BraidedStendhalAlgebra.basis`, and `B̃_w` is the corner `cornerSpace` with basis `cornerBasis`.
The grading is deferred (a red/red crossing has degree `-⟨λ_a, λ_b⟩`, not given by the KLR data).
For symmetric `Q`, Prop 4.16 holds over every commutative ring with no further hypothesis
(`RedStrands/StendhalBasisSymm.lean`, `Stendhal.stendhalBasisOfSymm`): the algebra with all red
orders maps to the KLR algebra of `stendhalQ Q Λ`, killing red dots and red/red crossings, and the
Stendhal terms go to KLR basis elements.
For `w = e`, `B̃_e ≃ T̃^λ` (`RedStrands/BraidedIdentity.lean`,
`BraidedStendhalAlgebra.cornerEquivStendhal`), through the map `toAllOrders` that imposes the
vanishing of red crossings: a reduced word between red-ordered sequences crosses no two red
strands (`noRedCross_of_isRedOrdered`), so the bases of Props 6.4 and 4.16 correspond.

Lemma 6.5 is proved for the bimodules `B̃_w` (`RedStrands/BraidedFactorization*.lean`):
multiplication `B̃(κ₂, κ₁) ⊗ B̃(κ₁, κ₀) → B̃(κ₂, κ₀)` over the middle corner is an isomorphism
(`BraidedStendhalAlgebra.tensorMultEquivOfPath`) when `κ₁` is reached from `κ₀` by adjacent red
crossings that `κ₂` still reads crossed (`RedCrossingPath`, the length condition
`ℓ(ww') = ℓ(w) + ℓ(w')`). The one-crossing case (`tensorMult_bijective`) compares frame classes
with the basis of Prop 6.4; the general case follows by induction through the refinement lemma
`CornerTensor.mult_injective_of_factor`. The length condition in inversion-set form (every pair
of labels crossed from `κ₀` to `κ₁` is still crossed in `κ₂`, for `κ₀` without repeated labels)
gives such a path by bubble sort (`redCrossingPath_of_inversions`,
`tensorMult_bijective_of_inversions`). The same holds for the quotient bimodules `B_w` by the
violated idempotents (`violMk_mult_injective`, `violMk_mult_surjective`): a violated diagram is
pushed through red crossings by frames that fix the strands left of the crossing
(`redProj_mul_mul_e_mem`), and injectivity passes to the quotient
(`CornerTensor.mult_injective_of_ker`).

For `w = e` the quotient bimodule is the tensor product algebra: `B_e ≃ T^λ` as rings
(`BraidedStendhalAlgebra.violCornerEquiv`, `RedStrands/BraidedViolatedIdentity.lean`). The
ring `B̃_e ≃ T̃^λ` is `identityCornerEquiv`, and the two ideals correspond
(`val_mem_violIdeal_iff`): a violated idempotent of any red order is pushed to the order
`λ_1, …, λ_ℓ` one crossing at a time (`redProj_mul_e_mem_violSpan`). So each `B_w` is a
`T^{wλ}`–`T^λ` bimodule.

Prop 6.7, part for `E`, at the level of bimodules: appending a black strand at the right is a
non-unital algebra map `φ = βE_i` (`appendBlackAlg`, `RedStrands/BraidedAppendBasis.lean`), and
multiplication `e_{κ'}B(νᵢ)φ(e_{κ'}) ⊗ e_{κ'}B(ν)e_κ → e_{κ'}B(νᵢ)φ(e_κ)` is bijective, for `B̃`
(`mult_injective_append`, `mult_surjective_append`, `RedStrands/BraidedAppendTensor.lean`) and for
the quotients by violated idempotents (`violMk_mult_injective_append`,
`violMk_mult_surjective_append`, `RedStrands/BraidedAppendViolated.lean`). The reduced words go
through the last coset (`lastCosetWord`), as in Webster's proof. The part for `F` is the
part for `E` transported along the top–bottom flip, an anti-automorphism of `B̃` and of the
quotient (`flip`, `violFlip`, `violFlip_appendViol`, `RedStrands/BraidedAppendFlip.lean`): over
the opposite algebras, `violMk_mult_injective_append_op`, `violMk_mult_surjective_append_op`
(transport lemmas `TensorAlong.mult_injective_of_bijective`,
`TensorAlong.mult_surjective_of_surjective'`). Webster deduces it by biadjunction.

Prop 6.7 for `𝔈_i`, derived form (`RedStrands/BraidedAppendDerived.lean`): `appendFunctor κ` is
`- ⊗ᴸ E_κ` with the corner `E_κ` of the induction along `φ`, and
`braidingFunctorCompAppendFunctorIso` gives `𝔈_i ∘ 𝔅(κ', κ) ≅ 𝔅(κ', κ) ∘ 𝔈_i` for symmetric
Rouquier `Q` and `κ'` an ordering of the red labels. Both composite bimodules are the corner
`e_{κ'} V φ(e_κ)` (`firstEquiv`, `secondEquiv`, `compDGEquiv`), and projectivity of `E_κ` on both
sides (`appendCorner_projective_left`, `appendCorner_projective_right`) makes the derived
composites underived (`derivedTensorCompIsoOfProjective`, `dgDerivedTensorCompIso`,
`dgDerivedTensorIsoOfEquiv`). The derived form for `𝔉_i`
(`braidingFunctorCompAppendFunctorOpIso`) works with right modules: the top–bottom flip
identifies the corner of `𝔉_i` with that of `𝔈_i` over the opposite corners, giving left
projectivity (`appendCornerOp_projective_left`), and the bimodule part for `F` identifies both
composites with `φ(e_{κ'}) V e_κ` (`compDGEquivF`).

Def 6.6 is done in ungraded, unbounded form: `braidingFunctor κ' κ`
(`RedStrands/BraidingFunctor.lean`) is the derived tensor product `- ⊗ᴸ B(κ', κ)` on right
modules over the corners of the violated quotient, built on dg-lean's derived categories of dg
modules over rings in degree `0`, computed on K-projective resolutions (`derivedTensor`,
`derivedRightTensor`, `Algebra/DerivedTensor.lean`; the bimodule `e A e'` is
`cornerBimodule`, `Algebra/CornerBimodule.lean`). Webster uses graded modules and `D⁻`; the
graded version and the restriction to `D⁻` are open roadmap items.

The ungraded Figure 5 right-module map for Prop 6.9 (`RedStrands/BraidedStandardTwo.lean`,
`RedStrands/BraidedStandardInjective.lean`, `RedStrands/BraidedStandardIso.lean`). Let the leftmost strand of `t` be `λ_r` and let `g`
carry it to the right edge, `g • t = s` (`EdgeBraid`). The braiding diagram `ψ_g` sends the
generators of the ideal `U_r` (violated idempotents, and idempotents starting with `λ_r` followed
by a black strand) into the violated ideal (`e_mul_mul_e_mem_violIdeal`); every element of
`e(s) A e_{r :: L}` is `ψ_g e(t) x` modulo diagrams with violated bottom
(`exists_e_mul_mul_redProj_sub_mem_of_last`); and if `ψ_g e(t) x e_{r :: L}` is violated then
`e(t) x e_{r :: L}` lies in `U_r` (`mem_edgeIdeal_of_mem_violIdeal`, through the left inverse
`throughMap`). Together they give the isomorphism of Figure 5,
`e(t) (A / U_r) e_{r :: L} ≃ e(s) (A / A e_viol A) e_{r :: L}` (`braidCornerEquiv`).
`violLoadingStandardEquivBraidCorner` identifies the swapped loading standard with the cut
of the braid bimodule as a right module over the swapped-order corner.
`BraidedStandardDerived.lean` evaluates Definition 6.6 on the loading projective `e(s) T`
(`braidingFunctorObjLoadingProjectiveIso`). The projective in degree zero is K-projective and
multiplication identifies its ordinary balanced tensor with `e(s) B`. The Figure 5 comparison
then gives `braidingFunctorObjFigureFiveIso`: the two-red braid applied to the lower loading
projective is `S_t` in cohomological degree zero over the swapped corner.

The endpoint comparisons in `BraidedStandardization.lean` use the standardization of Definition
5.4 on the exterior loading projectives. `loadingProjectiveEquivExteriorStandardization` uses
last-factor vacuum: all strictly higher loadings are violated, so the lower standard is the
loading projective. `loadingStandardEquivExteriorStandardization` identifies the upper loading
standard with the standardization with first-factor vacuum. The comparisons are right-linear
over the respective corners, using red relabelling and horizontal reflection to read the existing
left standardization there. The inverse cyclic rotation relates the two canonical two-piece
loadings, so `braidingFunctorObjFigureFiveStandardizationIso` composes both comparisons with
`braidingFunctorObjFigureFiveIso`. Thus the ungraded two-red braid sends
`S(P_u ⊠ P_∅)` to `S(P_∅ ⊠ P_u)` in cohomological degree zero.

For the internal grading, `ExteriorStandardGrading.lean` grades `stdLayerModule` using the two
projective factors, their exterior tensor, affine balanced induction, and the ordered quotient.
The identity-shuffle tensor of loading idempotents has degree zero. In
`BraidedStandardization.lean`, `loadingProjectiveEquivExteriorStandardization_mem_grade` and
`loadingStandardEquivExteriorStandardization_mk_mem_grade` show that the two endpoint maps
preserve degree on homogeneous diagram representatives. Relabelling and horizontal reflection
preserve diagram degrees, and the standardization map identifies the degree-zero generators.
`BraidedExteriorGrading.lean` identifies the whole pieces under those same maps. A homogeneous
upper exterior element lifts to a homogeneous corner representative: take the corresponding
component of any lift, using uniqueness of the intrinsic direct sum. At the lower endpoint the
same-order cut consists of the diagrams of the loading right ideal, and its intrinsic comap
provides the homogeneous components. The lower identification has no shift
(`figureFiveLowerProjective_mem_grade_iff`). The upper exterior grading includes `ℤ` into `ℂ`,
with zero pieces off the integers. Composing with the shifted loading comparison identifies its
piece at `z + ⟨λ₀ − α, λ₁⟩` with the cut at `z`, for every complex `z`
(`figureFiveExteriorToCut_mem_grade_iff`). Both sides vanish outside the shifted integral coset.

`BraidedExteriorTensor.lean` grades the two-red braid bimodule between the actual ordered
corners: restrict the auxiliary diagram grading to that corner and correct the red/red
degree as in Definition 6.2. Both diagram actions add internal degrees. The balanced tensor
with `S(P_u ⊠ P_∅)` uses the sum of these braid degrees and the intrinsic exterior degrees.
Its defining balancing subgroup is generated by homogeneous relations, so the quotient has
its own internal decomposition before evaluation. `figureFiveExteriorTensorEquivCut` tensors
the lower endpoint isomorphism with the braid and uses `loadingProjectiveTensorEquiv` to
multiply. It identifies each degree of the quotient with the given cut grade. The composite
`figureFiveExteriorTensorEquiv` identifies the ordinary tensor with the shifted upper
exterior standardization, using Webster's `M(a)_z = M_{z+a}`.

The same lower exterior standardization is projective for degree-preserving maps, not just
projective after forgetting degrees. In `figureFiveLowerExterior_graded_retract` the inclusion
reads the standardization as the loading right ideal inside the regular right module. Its
retraction multiplies on the left by the loading idempotent and then applies the lower endpoint
isomorphism. The diagram idempotent has internal degree zero, so both maps preserve every
complex degree, and their composite on the exterior object is the identity.

`BraidedExteriorDerived.lean` uses `DG.WeightCategory` on the source coset `ℤ` and target
coset `c + ℤ`, where `c = 2 − ⟨λ₁, λ₀⟩`. Between source `m` and target `n`, the braid piece
is at internal degree `n − m + c`, independently of the cochain degree. The lower grading
retract gives a corner generator at weight zero, hence `figureFiveLowerWeightModule_isKProjective`.
The tensor descends through homotopy; applying it to a source K-projective representative
and localizing on the target gives the ambient derived tensor, with no condition on the
K-projectivity of the braid's output slices. `figureFiveBraidDerivedTensorObjIso` computes
its value on the lower exterior standardization as the ordinary categorical coend.

The comparison `figureFiveBraidCoendCutIso` sends the lower inclusion through the coend tensor,
then evaluates the source representable at weight zero by `CatTensorProduct.rid`. On a pure
coend tensor it multiplies the included lower diagram on the left of the braid diagram. Its
image is fixed by the lower loading idempotent, hence in the loading cut. Its inverse sends a
cut diagram `y` to `y ⊗ g`, where `g` is the projection of the regular unit to the lower
standardization; balancing gives the first round trip and `e(s)y = y` gives the second.

The right-linear comparison `figureFiveExteriorToCut` identifies that cut with the shifted
upper exterior standardization. At weight coordinate `n` the unshifted upper piece is at
`n + c + ⟨λ₀ − α, λ₁⟩`, all in cochain degree zero. Localizing gives
`figureFiveBraidDerivedExteriorIso`, the ambient derived evaluation for the two-red Figure 5
input. It does not establish the restriction of the functor to all of Webster's `D⁻` or
replace the reduction by Lemma 6.8.

For Lemma 6.11, `braidingBimoduleFlip` implements the horizontal reflection used in
the proof of `f_n → s_n`. It swaps the order corners and intertwines their actions with
the opposite actions through the corner anti-involutions.
`hasReflectedStandardFiltration_braidingBimodule` carries a supplied right-standard
filtration of the inverse braid to a left filtration with the same loading labels on the
braid, using restriction of scalars along the corner flip on each subquotient.
Existence of the right-standard filtration and higher Tor vanishing remain open.

Lemma 6.8, ordinary tensor at a fixed top loading: `adjacentBlockRoot` measures the cuts
of `λ(j)`. A reduced diagram for the adjacent red swap factors through the swapped red
order without decreasing any of these counts (`exists_adjacentBlock_frame`). Hence in the
quotient by violated diagrams, factoring through higher loadings in the bottom or the top
order gives the same subspace of the crossing bimodule (`mem_blockUpperIdeal_iff`). For a
projective at `t`, `ker_blockTensorMult` identifies exactly which classes of the ordinary
tensor are killed by the bottom-order higher relations, and `blockTensorEquiv` identifies the
quotient tensor with the fixed-top corner modulo those relations.

The external algebra acts on the fixed-bottom column by horizontal juxtaposition
(`RedBlock.blockProductAction_projection`). A local violation raises a retained cut;
in the exchanged order `higher_loading_mul_order_mem` moves the resulting higher relation
to the bottom. No relation is imposed at the cut internal to the paired reds. For symmetric
`Q`, `RedBlock.orderedBlockAction` gives the action of the tensor of the ordered block
algebras on the summand selected by their red-order projectors, commuting with bottom
multiplication. At a nonviolated exchanged loading, `RedBlock.blockTensorLoadingEquiv`
identifies the ordinary quotient tensor above with the external loading idempotent's image.

For the other ordinary composite, `RedBlock.crossingProduct` tensors the spectator regular
bimodules with the local corner of red orders `[1,0]` and `[0,1]`. Writing `D₀` for the
external ordered algebra before the crossing and `S₀` for its standardization column,
`RedBlock.crossingStack` maps `crossingProduct ⊗_{D₀} S₀` to the exchanged-top column.
`crossingCut` takes a juxtaposed upper diagram `x` and a global lower representative `y`
to a balanced class. It is onto this tensor, and moving an ordered block diagram between
the halves gives the same class. Stacking the cut gives the exchanged-top projection of
`F(x) F(e₀) y`, where `F` juxtaposes diagrams and `e₀` fixes the seam order. The map is
linear over the exchanged block algebra, commutes with global bottom stacking, and is
natural under maps of right input modules.

`crossingStack_diagramCut` restacks the linear cut of an unmarked diagram to its projection,
so `crossingStack` is surjective. The cut kills violated and higher bottom endpoints.
For interior relations, `exists_zero_crossingSeamClass_of_quotient` gives a *marked*
representative of the same affine column diagram whose class is zero before restacking.
For this lift, push a violation to the bottom red order, cut the upper part using adapted
words, and reattach the lower tail.
Consequently `ker_crossingStack_eq_map_ker_boundaryStack` identifies the ordinary kernel
with the balanced classes of affine relations among marked stacks. Successive parabolic
PBW coordinates (`exists_blockStack_coordinates`) read those stacks linearly over the
juxtaposed upper diagrams. In the lower column the two boundary red orders agree, so
`insert_uncrossed_order` allows the same order to be inserted between a coefficient and
its tail. The ordered coefficient slides by balancing. Hence every affine relation has
zero balanced class: `crossingStack_injective` and `crossingStackEquiv` give the ordinary
comparison for arbitrary spectators and black contents. `crossingDiagramCut_eq_inverse`
identifies the original basis cut on every representative with the inverse on its class.
The binary bottom-projector formula extends to each block of the parabolic
coordinates. Theorem `violated_of_adjacent_shuffleLoading` shows that every compatible
split of a globally violated or strictly higher retained source loading has an
internally violated block. The projected coordinates vanish on diagrams factoring
through one of these loadings, with arbitrary diagrams above and below the cut.
`exists_blockStack_quotient_coordinates` descends the coordinates through red dots
and both loading ideals to the partially standardized quotient. The coordinate
words have coordinate `1` in their own slot and `0` in the other slots.
`exists_blockColumn_coordinate_embedding` shows that the coordinates separate
elements of the source-order block column. The affine coordinate representatives can
be chosen as explicit reduced words indexed by the recursive block shuffles. In a
binary shuffle, a right crossing either extends an external ascent or moves to an
internal crossing in one block, with an error in a lower crossing-filtration step.
The filtered binary coordinate reserves its shuffle length from the crossing
budget, and the two tensor factors share the remainder. Iterating this bound gives
the total-length bound for the recursive coordinates. In
`exists_blockStack_filtered_quotient_coordinates` the bound passes to the image
of that filtration in the quotient. For a right ascent in an arbitrary row,
`quotientCoordinate_external_right_ascent` and
`quotientCoordinate_internal_right_ascent` compute the leading quotient
coordinates. The two alternatives land in disjoint targets. A matched
nonviolated split in the source red order gives an ascent at a black–red joint.
The exact indexed projector agrees with the loading of the selected shuffle.
Consequently the external leading multiplier is the original right projector.
The internal one is the supported crossing in the paired block.
`blockColumn_eq_zero_of_ordered_paired_crossing` uses its ordered local injection
to deduce the whole-column zero-kernel statement over a field.
`exists_place_adjacent` places any nonviolated source loading with the prescribed
red order in an adjacent row, and `mem_blockUpperIdeal_of_blockColumn_right_kernel`
lifts a supported column kernel test to the higher ideal. The marked-column
comparison and higher Tor argument remain open in general.

For (6.21), the loading projective is `e(t)T` in the source order. Its surjection to
the external loading summand has kernel `K = e(t)T ∩ J` for the strictly higher
retained-boundary ideal (`ker_blockStandardCover`). `blockKernelTensorInclusion` tensors
this inclusion over `T` with the full braiding bimodule `B`. By moving a global violation
above the seam, `ker_blockKernelTensorInclusion_eq_map` identifies its kernel with the
classes of sums of marked pairs whose stacks vanish *before* quotienting by violations.
At a bottom loading `s` where the two exchanged reds occupy consecutive positions, all
reduced words admit the same last red crossing after a change of reduced expression.
Its ordered coefficient slides into `K`; PBW division detects the resulting upper
factor. Thus `blockKernelColumnInclusion_injective` proves injectivity after tensoring
with `B e(s)`, for arbitrary spectators and top black contents.

Still open for Lemma 6.8: when a black lies between the bottom reds, prove that changes
between different choices of the last crossing give equal balanced classes **in the
tensor with `K`**. The ordinary parabolic coordinates are linear for juxtaposed block
diagrams, not for arbitrary upper elements of `e(t)T`. Also open: filter `K` by higher
partial standardizations, apply the induction in (6.21), and identify the derived
comparison naturally. Then Prop 6.9
for general `ℓ` by reduction to two
red strands, the graded bounded-above functor of Def 6.6 and its equivariance (Prop 6.7), Cor 6.10, Lemma 6.11, Def 6.12, Cor 6.13,
Lemma 6.14; tilting modules (Thm 6.15); `𝔅_σ` are equivalences (Thm 6.16); the braid group
action (Cor 6.17); Ringel duality (Cor 6.18); semi-orthogonal decompositions (Prop 6.19); the
Serre functor (Prop 6.20).

For the multi-strand interval calculation, `intervalConcat` puts a local KLR diagram
between fixed exterior loading idempotents. The map is injective for symmetric
parameters (`intervalConcat_injective`). Its image is the span of shifted
local PBW words and their shifted bottom dots (`range_intervalConcat_eq_span`).

### Phase E: §7, rigidity

Coevaluation and evaluation for a pair (Def 7.1, Prop 7.2, Def 7.4, Props 7.5, 7.6,
7.8, Cors 7.7, 7.9, 7.10); ribbon structure (Prop 7.11, Def 7.12, Prop 7.13); general
coevaluation and quantum trace (Def 7.15, Lemmas 7.16, 7.17, 7.19, Def 7.18,
Props 7.20, 7.21, 7.22). All open.

### Phase F: §8, knot invariants

Tangle functors and decategorification (Prop 8.1); finiteness for links (Thm 8.2) and
minuscule tangles (Prop 8.3); the unknot for `sl₂` (Prop 8.4); independence of the
projection (Thm 8.6, Lemma 8.7); ribbon elements (Prop 8.8); minuscule duality
(Thm 8.11). All open.

### Phase G: §9, comparisons

Cyclotomic degenerate Hecke algebras and parabolic category `𝒪` (Defs 9.1, 9.2, 9.4,
Lemma 9.3, Prop 9.6); the equivalence `𝒪^p_λ ≃ V^λ` (Props 9.9, 9.11–9.13), Koszulity
and graded lift (Prop 9.14, Cor 9.15); the affine case (Thm 9.16); other knot
homologies (Props 9.18, 9.20, 9.21). All open.

### Inputs from other works (maintainer decisions)

* Prop 9.6 and Thm 9.16 are the Brundan–Kleshchev isomorphism (arXiv:0808.2032),
  which is not in the library. Options: formalize it, or take it as a stated
  hypothesis of the §9 results.
* Thm 5.34 and §9 compare with cyclotomic `q`-Schur algebras and category `𝒪`. On
  2026-11-15 the maintainer excluded the Cherednik and `q`-Schur comparisons for
  the weighted KLR work. This needs confirming for 1309.3796.
* Prop 9.14 (Koszulity) and Props 9.18–9.21 rest on results of other papers (for
  example Enright–Shelton equivalences). These are flagged in the same way when
  they are reached.
