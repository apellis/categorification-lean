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
| Thm 3.17 | strict 2-functor `𝒰 → Cat`, `μ ↦ R^λ_μ-pmod` | done at the standard KL black parameters over a field, as the one-red case of Thm 4.31 (`clBlackAction_cyclotomic`): the value at `λ - ν` is the completion of the all-down boundaries, whose sum has endomorphism ring `R^λ_ν` by Thm 4.18 (`SingleRed.cyclotomicEquiv`) |
| Thm 3.18 | `tr^λ : R^λ → k` is a Frobenius trace | done at the standard KL black parameters over a field (`clCyclotomic_trace_nondegenerate`): an additive trace `R^λ_ν → k` whose pairing `tr (a b)` is nondegenerate on both sides, closing the black strands to the right with the biadjunction of Thm 3.17 (`AmbidextrousTrace`, `MatEnd.trace_nondegenerate`). `k`-linearity of the trace is not part of the statement |
| Cor 3.20 | `p : R^λ → DR^λ` is a Morita equivalence | done at the standard KL black parameters over a field, as the one-red case of Thm 4.30 (`clBlackAction_cyclotomic`): with `DR^λ_ν` realized as `DT^λ_ν` for one red strand, the corner at the all-down boundaries is `R^λ_ν` and their inclusion is an equivalence of additive idempotent completions. Webster's black-only presentation of `DR^λ` (Def 3.1) is not separately compared with `DT^λ` |
| Prop 3.21, Cor 3.22 | `K₀(R^λ) ≅ V^λ_ℤ`, Euler form = Shapovalov form | done |
| Def 3.24, Prop 3.25, Cors 3.26, 3.27 | universal categorification `Ř^λ`, flatness, universality | open |

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
  Webster deduces it by a dimension count; the planned route (finite-dimensional `N`, over a
  field at Rouquier parameters) is strong induction on `|θ| + |β|`, splitting
  `dim Y = Σⱼ dim Eⱼ Y + dim R(Y)` with `R` the part whose last strand is red: the `Eⱼ`-parts
  follow from exactness of `Fᵢ`, the `Eᵢ`-part above and the `EF`/`FE` commutation relations of
  `T^λ` and of the factor algebra (dimension form), and the red part vanishes for `β ≠ ∅` and is
  Prop 4.32 with Prop 4.18 for `β = ∅`.

Open: the comparison of the induced model with Def 5.4 (right modules over `T̃^λ` and the block
algebra of all `ℓ + 1` blocks; the induced model uses left modules, which the vertical flip
`tensorFlip` converts), injectivity in the `Fᵢ`-part of Prop 5.5, Prop 5.6, and the results listed below.

Standardization functors (Prop 5.3, Def 5.4, Props 5.6, 5.7); simples and crystals
(Lemma 5.9, Props 5.11, 5.12, Thms 5.14, 5.15); stringy triples (Props 5.17, 5.18);
standard stratification (Lemma 5.19, Prop 5.21, Cors 5.22, 5.24, Lemma 5.25,
Prop 5.26, Cor 5.27: `V^λ` is a tensor product categorification); Thm 5.28 (finite
projective resolutions, Lemma 5.29); self-dual projectives and double centralizer
(Thm 5.30, Prop 5.31, Cor 5.32, Prop 5.33); Thm 5.34 (for `sl_n`, blocks of cyclotomic
`q`-Schur algebras). Open except as listed above.

### Phase D: §6, braiding functors

`w`-Stendhal diagrams and the bimodules `B_w` (Defs 6.1, 6.3, Prop 6.4, Lemma 6.5);
the functors `𝔅_w` (Def 6.6, Prop 6.7, Cor 6.8, Lemma 6.9, Prop 6.10, Lemma 6.13);
tilting modules (Thm 6.14); `𝔅_w` are equivalences (Thm 6.15); the braid group action
(Def 6.16, Cor 6.18); Ringel duality (Cor 6.19); semi-orthogonal decompositions
(Prop 6.20); the Serre functor (Prop 6.21). All open. These need derived categories of
graded modules; the plan is Mathlib's `DerivedCategory`.

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
