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

**Theorem 4.25 for general black parameters.** Done for every Rouquier
polynomial family `Q` (`Stendhal.regionTensorPseudofunctorQ`). The region
categories carry the action of `U_Sc(g)` with the Kang–Kashiwara scalars
`Sc = cyclotomicScalars` of `Q`. The reflection with inverted orientations maps
the relations of `U_Sc(g)` (`r = 1`) to those of `U_{Sc^θ}(g)`, with
`t^θ_{ij} = t_{ji}^{-1}` and `s^θ = (t_{ij} t_{ji})^{-1} s`
(`CLQ.lin_thetaLin_eq_zero`, via `ψ̃` for all scalars, `CLQ.psiUQ`, and the
rotation of every diagram of `U_Q(g)`, `CL.rotC_dgCL`). So `𝒯` is presented
with the reflected relations of `U_{Sc^θ}(g)`, the mixed black relations (2.3c),
(2.4a) at `t^θ` and the cup pitchforks at `t^θ_{ji}` (`j` the through colour,
`i` the cup colour) (`DoubleDiagram.tensorTwoCatPresentationQ`), and every
Rouquier family with red lines acts on it
(`DoubleDiagram.tensorTwoCatPseudofunctorQ`). With `r = 1`, `Sc ↦ Sc^θ` is an
involution (`CLQ.thetaScalars_thetaScalars`), and at `t = 1` it fixes `Sc`.
Comparison with Webster's §2.1. Webster's `t_ij = Q_ij(1,0)` is the
Kang–Kashiwara `t_ij` of `Q` (`kkScalars`). In `U_W(g)` the downward strands
carry `Q'_ij = (t_ij t_ji)^{-1} Q^W_ij`; for `W = Sc^θ` this is
`(t_ij t_ji) · (t_ij t_ji)^{-1} Q_ij = Q_ij`, so the reflected black part of
`𝒯` puts `Q` on downward strands, as in Webster's (2.6e) and in the downward
KLR relations of `𝒯`. Moreover `Sc^θ = λ · Sc` with `λ_ij = (t_ij t_ji)^{-1}`
(`t`, `s` scaled by the same symmetric factor). Open: whether Webster's printed
scalars in (2.5) and the pitchforks (2.2a) are those of `Sc^θ` or of `Sc`
(they agree at `t = 1`); if the latter, record an erratum with the corrected
scalars `t^θ`.

## The rest of arXiv:1309.3796v2

Plan for formalizing the paper in full. Numbers are those of v2, the target version; where v3
numbers a statement differently, the v3 number is given as "v3: …". Numbers were checked against both versions. Status
key: **done**, **partial**, **open**. The order below is the working order. §3 comes
after §4 because the single-red case of the §4 constructions gives the §3 ones
(Theorem 4.18, `T^λ ≅ R^λ` for one red strand).

### Phase A: the rest of §4

| Result | Content | Status |
|---|---|---|
| v3 Thm 4.28 (no numbered counterpart in v2) | `𝒰` acts on the double tensor product algebras `DT^λ` | done: strict pseudofunctor from the 1-cell dual of the KL 2-category to `Cat` (`blackActionPseudofunctor`), built from right whiskering (`violatingWhiskerRight`) and the functorial action of KL 2-morphisms (`blackMap_id`, `blackMap_comp`) |
| Thm 4.29 (v3: Thm 4.30) | `T^λ` and `DT^λ` are Morita equivalent | done (#420) |
| Thm 4.31 | `𝒰` acts on `T^λ`-modules by `βᵤ = e₋ β′ᵤ e₋` | done at the standard KL black parameters over a field: the action of Thm 4.28 on the additive idempotent completions (`StrictPseudofunctor.completion`) for the presentation of Thm 4.30 (`clBlackAction`); its value at `λ - ν` is identified with the completion of the all-down boundaries, with endomorphism ring `T^λ_ν` (`clBlackAction_tensorProduct`). Graded modules and the formula `βᵤ = e₋ β′ᵤ e₋` on algebras are not separately stated |
| Thm 4.25 | representation of the 2-category `𝒯`; red lines act by `I^λ` | done at the standard KL black parameters (`Stendhal.regionTensorPseudofunctor`; general parameters of Webster's form: roadmap item below): for the Khovanov–Lauda black parameters over a nontrivial commutative ring and the cyclotomic polynomials `X ^ ⟨α_i^∨, λ_r⟩` of dominant weights, the pseudofunctor out of the presented 2-category `𝒯` (`tensorTwoCatPresentation`) on the region categories (`regionFamily`), with red lines acting by pullback along the cyclotomic quotients. The relations are checked in the double model (`tensorTwoCatPseudofunctor`): red/up crossings natural for dots and crossings (`regionUpIsoDotNatural`, `regionUpIsoCrossNatural`, from (4.4d) on cyclotomic blocks), both down bigons (`regionDownBigon`), and the red strand between two downward strands of the same colour (`regionDownMidSame`, through the epimorphic quotient crossing). The presentation `downwardBlockPresentation` used for Lemma 4.29 also imposes KLR relations between two red strands; this representation is for `tensorTwoCatPresentation`, in which red strands do not cross. The action on `T^λ`-modules used in §5 is Thm 4.31, which does not depend on this |
| Prop 4.18 (v3: Prop 4.19) | `T^{λ⁻} ≅ e_ℓ T^λ e_ℓ` | done (`appendRedEquiv`) |
| Prop 4.21 | splitting a red strand, `T^{λ′} ≅ e_{λ′} T^λ e_{λ′}` | done (`SplitRed.splitRedEquiv`): with `λ'` splitting `λ_c = λ'_c + λ'_{c+1}`, `T^λ ≅ e T^{λ'} e` for `e` the sum of the idempotents of the loadings with red strands `c`, `c + 1` adjacent, for the crossing parameters of §2.2 (`IsRouquierQ`) |
| Prop 4.32 | `IR^μ I^μ = id` and its commutation with `Eᵢ`, `Fᵢ` | done: `IR^μ Fᵢ I^μ ≅ Fᵢ` on bimodules (`lastRedBlackEquiv`); `IR^μ I^μ = id` is Prop 4.18 (`appendRedEquiv`); `IR^μ Eᵢ I^μ ≅ Eᵢ` over a field by reflection (`lastRedBlackMirrorEquiv`); both raise degrees by `degΨ(λ_ℓ, i)` (`lastRedBlackMap_mem_grade`, `lastRedBlackMirror_mem_grade`) |
| Prop 4.33 | uniqueness of the sesquilinear forms | done (`TensorPairing.orderedForm_unique`, `orderedForm_nondegenerate`): a system of forms that is `τ`-Hermitian and isometric along `V_{λ₁} ⊗ ⋯ ⊗ V_{λₙ₋₁} ⊗ v_{λₙ}` is `orderedForm`, which is nondegenerate in both arguments. Webster's conditions do not fix the form on the empty tensor product; the theorem takes the scalar form `x̄ y` there as a normalization |
| Prop 4.39 | `K₀(T̃^λ) ≅ U_q^{-,ℤ} ⊗ V^ℤ_λ` | done, with all four compatibilities (4.40): `exists_negIntegralTensorEquiv` gives a `q ↦ q⁻¹`-semilinear isomorphism from `⊕_β K₀(T̃^λ_β)` onto `U_q^{-,ℤ} ⊗ V^ℤ_λ` sending `[P̃_w]` to `p̃_w`, by Webster's route (the functors `𝔯_N`, `prependRedK0_bijective`; the maps `𝔮_N`, `negTensorMap_injective_below`; Theorem 4.38 for `(Nλ₁, λ)`), with the operators `F̃_i` corrected as in ERRATA entry 11. `negTensorLattice_eq_negIntegralTensor` identifies the span of the `p̃_w` with `U_q^{-,ℤ} ⊗ V^ℤ_λ`. Hypothesis from the printed proof: a dominant `λ₁` with `⟨α_i^∨, λ₁⟩ ≥ 1` for all `i`, which holds for Webster's weight lattice but not for every root datum (for example affine `sl₂` with `α₀^∨ + α₁^∨ = 0`). `tildeLower_tildeClass` shows that the induction functor `F̃_i` of `T̃^λ`-modules (`tildeLower`, along the right black strand map `appendBlackStendhal`) sends `[P̃_w]` to `[P̃_{w i}]`, and `exists_negIntegralTensorEquiv_lower` that the isomorphism intertwines it with `F̃_i`. `totalTildeRedInd_tildeClass` and `exists_negIntegralTensorEquiv_red` do the same for the red induction `Ĩ_λ` (along `appendRedStendhalValue`) and `u ⊗ w ↦ u ⊗ w ⊗ v_λ`. For the reflected functor `F̃_i^*` (along `prependBlackStendhal`, which adds the black strand on the left), `tildeLeftLower_tildeClass` gives `F̃_i^* [P̃_w] = [P̃_{i w}]` and `exists_negIntegralTensorEquiv_leftLower` the compatibility with `u ⊗ w ↦ u F_i ⊗ w`: in the left-action convention of ERRATA entry 11 Webster's `F_i · (u ⊗ w)` becomes right multiplication. For `Ĩ_λ^*` (along `prependRedStendhal`, which adds the red strand on the left), `totalTildeLeftRedInd_tildeClass` gives `Ĩ_{λ₀}^* [P̃_w] = [P̃_{λ₀ w}]` and `exists_negIntegralTensorEquiv_leftRed` the compatibility with `negTensorPrepend`, `u ⊗ w ↦ u_{(1)} ⊗ (u_{(2)} v_{λ₀} ⊗ w)`, where `U⁻` is identified with the Verma module `M(0)` and `u_{(1)} ⊗ u_{(2)} v_{λ₀}` is `Δ(u)` applied to `m₀ ⊗ v_{λ₀}` (`negCoprod`) |

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
| Prop 3.31 (v2 only) | `B′` is a basis of `U′` | not in the v3 target; the printed proof does not hold as written: it claims that `Ř^λ` is a `U′`-representation, but for `sl₂`, `λ = 1`, one strand, at region weight `-1`, the honest bubble with `-1` dots acts on `Ř^λ` by `-1/z ≠ 0`, while in `U′` it equals the fake bubble of negative degree, which is `0`. Maintainer decision (2026-11-21): formalize Def 3.28, Lemma 3.29 and Prop 3.30, and record 3.31 as an erratum (README, Webster §3.6 erratum). Closed (2026-11-26): the target is v3, which removes §3.6 and Prop 3.31; the v2 statement is neither proved nor refuted (a proof needs `U → U′` faithful on Hom spaces) and stays recorded in ERRATA §7 |
| Cor 3.32 (v2 only) | `γ : U̇_ℤ → K₀(𝒰)` is an isomorphism | done (KL III Thm 1.2 for every Cartan datum: `gammaAlgEquiv_unconditional`, `gammaAlg_injective_unconditional`) |

The proved nondegeneracy of the Khovanov–Lauda calculus (`gammaAlg_injective_of_calculusNondeg`,
KL III Thm 1.2) is the input for the basis statements behind Thm 3.17 and Cor 3.26.

### Phase C: §5, standard modules

Done (`RedStrands/StandardModule.lean`): the preorder of Def 5.1, encoded by the
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
Prop 5.24 (v3: Prop 5.26) for `S(L) e_α ≅ L`.

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
  `firstIndDeltaInjective_of_rouquier` and `allFiniteDeltaInjective_of_rouquier`, hence the black-word
  filtrations (`hasFiltration_loadingProj_of_rouquier`; the finite-dimensional form
  `AllFiniteDeltaInjective` suffices, `ParabolicStandardFiniteFiltration.lean`). The
  intermediate lemmas take a base presentation with `CoverRelsNegligible` and well-founded
  domain; the presentation with no relations (`noRelations`) satisfies both vacuously, so the
  headline results carry no presentation hypothesis. **Done for general `Q`:** the count holds
  for every Rouquier `Q` with symmetric parameters (`RedStrands/Prop55Dimension*Q.lean`, from
  Thm 4.31 at general `Q`; `finrank_firstIndF_eq_addQ`, `firstIndDeltaInjective_of_rouquier`,
  `allFiniteDeltaInjective_of_rouquier`, `hasFiltration_loadingProj_of_rouquier`).

* Prop 5.5, empty last block (`RedStrands/ParabolicStandardEmptyRed.lean`): for `β = ∅` the
  factor algebra is `T^{λ'}` (`emptyFactorToOld`) and standardization is the induction along
  `appendRed`, `S(N) ≅ T^λ ⊗_{T^{λ'}} N` as `T^λ`-modules (`emptyRedStandardEquiv`), with
  inverse `z ⊗ n ↦ z · (1 ⊗ n)`; the key identity is that the parabolic affine image of a
  concatenation equals `appendRed` after the factor isomorphism (`emptyF_eq_emptyG`).

* Step in the proof of Prop 5.20, v3: Prop 5.21 (`RedStrands/TwoPieceStandardEquiv.lean`): for a red-ordered loading `t` of the
  first `ℓ` red strands and a black sequence `u`, the standardization of `S_t ⊠ R e(u)` is the
  standard module `S_{t λ_{ℓ+1} u}` of Def 5.1, `S(S_t ⊠ R e(u)) ≅ S_{tλu}` as `T^λ`-modules
  (`twoPieceStandardEquiv`, `twoPieceStandardEquiv_symm_unit`), for `KLRSymm Q`. The map out of
  the standardization is `parabolicDesc`; the inverse is the lift of the unit of `S_{tλu}`,
  using that loadings above `tλu` act by zero (`parabolicStandardAction_upper_eq_zero`).

* Prop 5.20 (v3: Prop 5.21), filtration form (`RedStrands/ProjectiveStandardFiltration.lean`): every `T^λ e(s)`
  has a finite filtration by standard modules (`hasStandardFiltrations`), by induction on the
  number of red strands: loading decomposition `(s₀, λ_{ℓ+1}, w)`
  (`exists_blackWordLoading_appendRed`), the filtration of Prop 5.5's proof, exactness of `⊠`
  over a field (`hasFiltration_tensorLayer`) and `twoPieceStandardEquiv`. Differences from the
  printed statement: existence of a standard filtration rather than the specific `Φ`-indexed
  filtration `P_{≥φ}/P_{>φ} ≅ S^{κφ}_{iφ}`; route hypothesis `AllFiniteDeltaInjective` for every
  sequence of highest weights (removal tracked with Prop 5.5).

* Cor 5.21 (v3: Cor 5.22), condition on projectives (`RedStrands/StandardStratification.lean`): the kernel
  `U_s` of `T^λ e(s) → S_s` has a finite filtration by `S_t` with `t > s` in Webster's dominance
  order on black counts (`exists_hasFiltration_leftUpper`). It comes from the ordered form of the
  filtration of Prop 5.20 (`RedStrands/ProjectiveStandardFiltrationOrder.lean`,
  `hasOrderedStandardFiltrations`: top quotient `S_{s'}` with `s'` equivalent to `s`, other
  labels strictly above `s`). Difference from the printed statement: Webster states that `T^λ`
  is standardly stratified; the formal statement is the condition on projectives of that
  definition. Same route hypothesis as Prop 5.20.

* Prop 5.20 and Cor 5.21 at the standard Khovanov–Lauda scalars
  (`RedStrands/StandardStratificationStd.lean`): `AllFiniteDeltaInjective` is discharged by the
  dimension count (`allFiniteDeltaInjective_of_rouquier`), with no further hypothesis.

* Prop 5.20, printed `Φ`-indexed form (v3: Prop 5.21; `RedStrands/PhiDiagrams.lean`,
  `PhiStandardLayers.lean`, `LabelledStandardFiltration.lean`, `PhiLayerStd.lean`): for a
  red-ordered `s`, a choice `ρ` of reduced words and the block assignments `φ` of `s`
  (`PhiIndex s`), put `x_φ = ψ_{ρ φ} e(s)`, `P_{>φ} = Σ_{φ • s < φ' • s} T^λ x_{φ'}` and
  `P_{≥φ} = T^λ x_φ + P_{>φ}`. Then `P_{≥φ}/P_{>φ} ≅ S_{φ • s}`, `[e(φ • s)] ↦ [x_φ]`
  (`phiLayerEquiv`, `phiLayerEquiv_unit`). As in Webster's proof: the `x_φ` span `T^λ e(s)`
  modulo higher terms (`iSup_phiSub_eq_top`), the layer is a quotient of `S_{φ • s}`
  (`phiLayerMap_surjective`), and `dim T^λ e(s) = Σ_φ dim S_{φ • s}`
  (`finrank_lIdeal_eq_sum_phiBottom`, from a standard filtration labelled by the bottoms
  `φ • s`, `hasLabelledStandardFiltrations`) forces bijectivity
  (`Submodule.layerRank_eq_of_sum_eq`). Same route hypothesis as the filtration form; none
  at the standard scalars (`phiLayerEquiv_of_rouquier`).

* Lemma 5.26 and Cor 5.22 (v3: Lemma 5.29, Cor 5.24; `RedStrands/StandardProjectiveDimension.lean`): projective dimension
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

* Prop 5.5, comparison with Def 5.4, bimodule step (`RedStrands/LeftRootStandard.lean`,
  `RootReflectUnit.lean`, `TwoPieceRootStandard*.lean`, `TwoPieceBlockMap*.lean`,
  `TwoPieceLastBlockMap.lean`, `ParabolicStandardUnitExt.lean`): when no sequence of root
  function `α` is violated (for example when `b_0 = 0`), Webster's `S_α` is the horizontal
  reflection of the left root standard module `S^L_α = ⊕_s T^λ e(s) / U_s` (`rootReflectEquiv`),
  which carries the block action of Prop 5.3 to `S^L_α` (`leftBlockAction`). For `ℓ + 1` red
  strands, `S^L_α ≅ S(S^L_{α'} ⊠ R^{λ_{ℓ+1}}(β))` as `T^λ`-modules (`twoPieceRootStandardEquiv`),
  sending the unit vector of `[e(t)] ⊠ e(u)` to that of `S_{t λ_{ℓ+1} u}`
  (`twoPieceRootStandardEquiv_unit`). The isomorphism intertwines the block actions: for the
  blocks `j ≤ ℓ` with the standardization of the actions on `S^L_{α'}`
  (`twoPieceRootStandardEquiv_initBlock`, from `prefixBlockMap_blockEmb`), and for the last block
  with right multiplication by the flipped diagram on `R^{λ_{ℓ+1}}(β)`
  (`twoPieceRootStandardEquiv_lastBlock`, from `suffixBlockMap_lastBlackMap`).

* Prop 5.5, comparison with Def 5.4, iteration step (`RedStrands/LeftStandardization.lean`,
  `TwoPieceBlockAlgebra*.lean`, `TwoPieceStandardization*.lean`,
  `Algebra/CommutingFamilySingle.lean`): when no sequence of root function `α` is violated,
  Def 5.4's `S(M) = M ⊗_B S_α` is `M ⊗_B S^L_α` (`standardizationReflectEquiv`), the right
  action of `a` becoming the left action of `flip(a)`. The block algebra `B` of `ℓ + 1` red
  strands receives commuting maps from the block algebra `B'` of the first `ℓ`
  (`initBlockAlgHom`) and from the last factor (`lastBlockAlgHom`), whose images generate it
  (`blockAlgebra_subalgebra_eq_top`), and `twoPieceRootStandardEquiv` intertwines both actions
  (`twoPieceRootStandardEquiv_initBlockAlg`, `twoPieceRootStandardEquiv_lastBlockAlg`). For a
  right `B`-module `M`, `X_M = M ⊗_{B'} S^L_{α'}` is a module over `T^{λ'} ⊗ R^{λ_{ℓ+1}}(β)`
  (`TwoPieceInput`), and `M ⊗_B S^L_α ≅ S(X_M)` as left `T^λ`-modules
  (`splitStandardEquiv`): this is the reduction of the proof of Prop 5.5 to two tensor
  factors, for Def 5.4's standardization.

* Prop 5.5, `Eᵢ`-part for Def 5.4 (`RedStrands/EiFiltration*.lean`, `EiStep*.lean`, `EiTop*.lean`,
  `EiLastLayer.lean`, `EiRightTerm.lean`, `StandardSplitFiltration.lean`): for `b_0 = 0`,
  `Eᵢ(M ⊗_B S^L_α)` has a filtration by the `ₖEᵢ M ⊗_{B'} S^L_{α'}`, one for each block containing
  `i` (`eiFiltration`), by induction on `ℓ` through `splitStandardEquiv`: when `i` lies in both
  pieces, the two-piece short exact sequence with the induction hypothesis standardized
  (`hasFiltration_splitStandard`) below and the last-strand layer above
  (`eiFiltration_step_both`); when `i` lies in one piece, the isomorphisms `leftBlackResEquiv`,
  `rightBlackResEquiv` made natural and compatible with the commuting action
  (`eiFiltration_step_left`, `eiFiltration_step_right`). The statement carries an algebra `C`
  acting on `M` by `B`-linear maps (the last cyclotomic factor in the induction); `C = k` is
  Webster's statement.

* Prop 5.5, `Fᵢ`-part for Def 5.4 (`RedStrands/FiFiltration*.lean`, `FiSequence.lean`,
  `FiSubTerm.lean`, `FiTopEquiv.lean`, `FiInit*.lean`, `FiLast*.lean`, `FiQuotTerm.lean`): for
  `b_0 = 0`, `Fᵢ(M ⊗_B S^L_α)` has a filtration by the `ₖFᵢ M ⊗_{B'} S^L_{α'}`, one for each red
  strand (`fiFiltration`), by induction on `ℓ`: `Fᵢ(M ⊗_B S^L_α) ≅ Fᵢ S(X_M)` (`fiTopEquiv`), and
  in the last-strand sequence the quotient `S(₂Fᵢ X_M)` is the last layer (`fiQuotEquiv`, through
  `₂Fᵢ X_M ≅ X_{ₗFᵢ M}`, `fiLastInputEquiv`), the sub term `S(₁Fᵢ X_M)` the standardization of the
  induction hypothesis (`fiSubEquiv`, `fiInitLayerStandardEquiv`). Route hypothesis:
  `AllDeltaInjective` for every sequence of highest weights (injectivity of the first map),
  tracked for removal below. For finite-dimensional `M` (Webster's setting) and Rouquier `Q`,
  `fiFiltration_finite` needs only `AllFiniteDeltaInjective`, which is Webster's dimension count
  (`allFiniteDeltaInjective_of_rouquier`), so `fiFiltration_finite_of_rouquier` holds with no
  route hypothesis (at the standard Khovanov–Lauda parameters, `fiFiltration_finite_std`).

Open: substituting `allFiniteDeltaInjective_of_rouquier` for the route hypothesis
`AllFiniteDeltaInjective` in the downstream results at general `Q` (Props 5.20/5.21, Cor 5.22,
Lemma 5.25, §6), the passage from finite-dimensional to arbitrary modules (removes
`AllDeltaInjective` of `fiFiltration`; not needed for Webster's statement), Prop 5.6,
and the results listed below.

Prop 5.17 (stringy loadings classify indecomposable projectives) is proved:
`Stendhal.maxLoadClassification` (`RedStrands/StringyClassification.lean`). Prop 5.18 (summands
of `T^λ e(s)` surject onto `S_s`, a product of standard quotients) is proved for every orthogonal
idempotent decomposition of `e(s)`: `Stendhal.IsSeqDecomp.leftStandardEquiv`,
`Stendhal.IsSeqDecomp.lIdeal_le_sup` (`RedStrands/StandardSplitting.lean`).

Prop 5.28 (v3: Prop 5.31; `End(P⁰) ≅ T^{λ̲} ≅ R^{λ̲}` for `P⁰ = e⁰ T^λ`, `e⁰` the red-first loadings) is
proved as a ring isomorphism of the corner `e⁰ T^λ e⁰` with the cyclotomic KLR algebra of the
total weight, for the crossing parameters of §2.2: `Stendhal.redFirstCornerEquiv`
(`RedStrands/RedFirstCorner.lean`), by repeated red-strand splitting (Cor 4.21 of v2,
`splitRedEquiv`) down to one red strand (Prop 4.20). The printed `Φ`-indexed form of
Prop 5.20 (v3: Prop 5.21; the specific filtration `P_{≥φ}/P_{>φ} ≅ S_{φ • s}`) is proved
(`RedStrands/LabelledStandardFiltration.lean`, `phiLayerEquiv`), under the route hypothesis
`AllFiniteDeltaInjective`, and with no hypothesis at the standard scalars (`phiLayerEquiv_of_rouquier`).

Cor 5.29 (v3: Cor 5.32, double centralizer of `P⁰`) is proved with no extra hypothesis:
`Stendhal.existsUnique_eq_mul_left_redFirst` (`RedStrands/RedFirstDominantDimension.lean`), from
the module-theoretic step `Categorification.exists_eq_mul_left_of_hasCornerCopresentation`
(`Algebra/SelfDualDoubleCentralizer.lean`) and the dominant dimension of `T^λ` with respect to
`P⁰` (`Stendhal.hasCornerCopresentation_redFirstIdem`). Webster obtains the dominant dimension
from Mazorchuk–Stroppel, J. Reine Angew. Math. 616 (2008), Cor. 2.6. Here it is proved directly.
Each red-ordered loading reaches a red-first one by crossings whose cokernels embed into sums of
copies of `P⁰` (`RedStrands/RedFirstCopresentation.lean`, `ExactMulRightTransport.lean`). At the
base crossing the cokernel is `S(₂Fᵢ N)` (`RedFirstBaseCrossingCokernel.lean`), and it has no
nonzero element killed by `e⁰ T^λ` (`LastIndStandardCornerFaithful.lean`). The criteria are in
`Algebra/CornerCopresentationCriteria.lean`.

Prop 5.30 (v3: Prop 5.33) is proved with no extra hypothesis: `Stendhal.redFirstEndEquiv` (`RedStrands/RedFirstEndomorphism.lean`) identifies
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
(Lemma 5.9, Prop 5.11, Thms 5.14, 5.15); standard stratification (Lemma 5.23,
Prop 5.24; v3 adds Lemma 5.19 and Cor 5.27, `V^λ` is a tensor product categorification); Thm 5.25 (finite
projective resolutions); self-dual projectives and double centralizer
(Thm 5.27, Prop 5.28, Cor 5.29, Prop 5.30). Open except as listed above. Thm 5.31 (v3:
Thm 5.34, for `sl_n`, blocks of cyclotomic `q`-Schur algebras) is optional: see Phase G.

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
`cornerBimodule`, `Algebra/CornerBimodule.lean`). Webster uses graded modules and `D⁻`. The
maintainer chose the graded form of Def 6.6 (2026-11-27). The graded braiding functor is
the derived right tensor over the weight categories of the corners with their auxiliary
grading (`diagramCornerWeightDerivedRightTensor`, `Algebra/DiagramWeightCorner.lean`, used so
far for the fundamental braid in §7). For all red orders it is
`auxiliaryGradedBraidingFunctor κ' κ` (`RedStrands/BraidingAuxiliaryDerived.lean`); Webster's
degree on `B(κ', κ)` is the auxiliary degree plus the constant offset `redWordOffset`.
Forgetting the weights is a functor of derived categories (`weightForgetDerived`,
`Algebra/WeightForgetDerived.lean`) that carries the graded functor to the ungraded one
(`auxiliaryGradedBraidingFunctorForgetIso`, `RedStrands/BraidingForgetDerived.lean`, through
`diagramWeightForgetDerivedIso`). Open: carry the §6 results (Lemmas 6.12–6.13, Theorem 6.15)
over to the graded functor.

Lemma 6.8, higher cohomology (`RedStrands/BraidPartialStandardVanishing.lean`): for an
adjacent red pair and a red order `κ`, the braid of the partial standard at every loading of
red word `κ` has no cohomology outside degree zero
(`blockPartialStandardAt_braid_homology_vanish_of_kernel_filtrations`), by Webster's induction
through (6.21), well-founded on `adjacentBlockRoot`. Two inputs of the printed proof are
explicit hypotheses (maintainer decision), each a roadmap item to remove:

- **(6.8-filt)** the kernel of each loading projective onto its partial standard is filtered by
  partial standards at strictly higher loadings. The printed proof uses this without proof.
  **Proved in the red order `λ`** under the route hypothesis `AllFiniteDeltaInjective` of
  Lemma 5.19 (`exists_hasFiltration_blockLoadingKernelAt`, `RedStrands/BlockPartialStandardFiltration.lean`,
  from the left form `exists_hasFiltration_leftPartialKernel`, `RedStrands/CoarsePhiCount.lean`):
  the dimension count of Prop 5.20 (v3: Prop 5.21) for the coarse block assignments
  (`RedStrands/CoarseAssignment.lean`, `RedStrands/CoarsePhiLayers.lean`,
  `Algebra/FinrankCountingFiltration.lean`). This covers Cor 6.10, whose Figure 5 rows are in the
  red order `λ`; the theorem for an arbitrary red order `κ` remains open.
- **(6.8-inj)** injectivity of the balanced tensor of the kernel inclusion with the braiding
  bimodule (`blockKernelTensorInclusion`). The printed cut argument after (6.21) does not handle
  the dotted relations in general; special cases are proved (first black weight, consecutive
  exchanged reds, zero intervening pairings).

Prop 6.9 for general `ℓ`, step 1 (`RedStrands/CommonUpperLoading.lean`,
`RedStrands/StandardPartialKernel.lean`): at a loading of red order `… a b …` whose cut at `b`
is rigid (`IsRigidCut`; it holds when no black strand lies between `b` and the next red strand,
`isRigidCut_of_black_right`, as at the Figure 5 loading), the relations of the standard module
of Def 5.1 are exactly those of the partial standard of Lemma 6.8
(`mem_violStandardUpper_iff_mem_blockUpperIdeal`). One inclusion holds at every loading: every
diagram `e(t) x e(u)` between loadings of one red order factors through loadings above both
(`e_mul_mul_e_mem_commonUpperSpan`).

Step 2 (`RedStrands/BlockPartialStandardTensor.lean`): for a loading `t` of red order
`L ++ b :: a :: M`, the ordinary tensor of the braid bimodule to `L ++ a :: b :: M` with the
partial standard is the cut `e(t) V e_{κ₀}` modulo the diagrams through loadings of the bottom
order with strictly higher retained root (`partialStandardTensorEquiv`, no hypotheses; it uses
the slide `mem_blockUpperIdeal_iff` in place of `blockTensorEquiv`). With Lemma 6.8 this is the
derived braid of the partial standard in degree zero (`blockPartialStandard_braidIso`, under
(6.8-filt) and (6.8-inj)).

Step 3, reduction to two red strands. Generators of the crossing
bimodule of a row (`RedStrands/BlockCutGenerator.lean`): at a top loading, the two-red
Figure 5 diagram tensored with the spectator loading idempotents generates the summand, its
annihilator is carried into the local two-red standard relations, and these relations act by
zero (`crossingProduct_generator`, from `violLoadingStandardEquivBraidCorner`). Stacking
(`RedStrands/BlockCrossingGenerator.lean`, `Algebra/BalancedTensorCyclic.lean`): through
Lemma 6.8's `crossingStackEquiv`, the top summand of the crossed column is the image of the
generator stacked on the uncrossed column, with kernel the submodule generated by the local
relations (`exists_stack_generator`, `mem_spanSmul_of_tmul_eq_zero`,
`tmul_eq_zero_of_mem_spanSmul`). Assembly (`RedStrands/BlockCrossingStandard.lean`,
`RedStrands/BlockCrossingRowStandard.lean`, `RedStrands/BlockCrossingBraidStandard.lean`):
left multiplication by the stacked generator maps `e(s') V e_{κ₀}` onto the cut quotient of
step 2 at `s` with kernel the stacked local relations, so under `StackedStandard` the cut
quotient is the standard module at `s'` (`braidCutQuotientEquivStandard`,
`rowBraidCutEquivStandard`) and the derived braid of the partial standard at a Figure 5 row
loading is that standard module in degree zero (`rowPartialStandard_braidIso`).

`StackedStandard` (Webster's reduction to `ℓ = 2` uses without proof that partial
standardization of the local standard is the global standard) is a theorem at every placed
loading whose pair loading has the identity red order and no black strand left of a red strand
(`RedStrands/BlockStackedStandard.lean`, `stackedStandard_setPairLoading`), in particular at the
Figure 5 rows (`stackedStandard_rowFigureFive`). The inclusion of the stacked relations is the
comparison of roots under juxtaposition (`e_mul_mul_place_mem_stendhalUpperIdeal`); the converse
factors each generator `e(t') x e(u)` of the upper ideal through juxtaposed loadings, which lie
strictly above the uncrossed pair loading when the root does not increase
(`exists_blackCount_lt_of_adjacentBlockRoot_eq`, `RedStrands/BlockStackedCounts.lean`).

Input side (`RedStrands/BlockPartialStandardRigid.lean`): at a rigid cut the partial standard
is the standard module (`partialStandardEquivStandard`, from step 1), giving the ungraded
Prop 6.9 at Figure 5 row loadings (`rowStandard_braidIso`). The cut at `f 0` is rigid
(`RedStrands/BlockCrossingRigid.lean`, `isRigidCut_place_setPairLoading`): in the crossed
Figure 5 loading `f 0` ends the paired block and the next block starts with its red strand,
so `f 0` has as many black strands to its left as the next red strand.

Step 4, the shift (`RedStrands/BlockCrossingGrading.lean`). The cuts `e(s) V e_κ` and their
quotients carry the auxiliary grading of the braided diagrams (`violCornerGrade`,
`braidCutGrade`, `loadingStandardGrade`). The stacked generator acts as the stacked Figure 5
diagram (`rowFigureFive`, `rowBraidCutEquivStandard_mk`), which is homogeneous of auxiliary
degree `⟨α, λ_{f 0}⟩ - 2` (`rowFigureFive_mem_grade`), so `rowBraidCutEquivStandard` is a graded
isomorphism after that shift (`rowAuxiliaryGradedEquiv`). With Webster's degree of the single
red/red crossing in the cut (`rowCutGrade`, as `figureFiveCutGrade` for `ℓ = 2`), the standard
module shifted by `-⟨λ_{f 1} - α, λ_{f 0}⟩` is isomorphic to the cut quotient as a graded module
(`rowGradedBraidCutEquivStandard`), that is, the shift `⟨λ_{f 1} - α, λ_{f 0}⟩` in Webster's
convention `M(a)_n = M_(n+a)`. The derived braid functor of Definition 6.6 is ungraded, so the
derived form `rowStandard_braidIso` carries no shift; the degree is recorded on the module
identification it is built from.

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

### Webster §§6–8 checkpoint, 24 November 2026

- **§6, v2 Lemma 6.11.** The homogeneous ordered loading resolution is
  K-projective and preserves acyclicity under the dg coend. The reflected
  braid has cohomological concentration when every filtration layer satisfies
  the directed loading condition. The general comparison of the two actual
  standard resolutions and its application to every standard pair remain
  open. The underlying dg coend symmetry, cone comparison, and balance
  theorem are available upstream.
  [Ordered resolution](https://github.com/apellis/categorification-lean/pull/917)
  · [Directed vanishing](https://github.com/apellis/categorification-lean/pull/893)
  · [DG balance](https://github.com/apellis/dg-lean/pull/72)
- **§6 geometry.** The explicit bottom-block convention follows the proof of Lemma 6.11 (v3: Lemma 6.12).
  Bottom reconstruction and the eligibility criterion are merged. Drafts
  establish column generation, strict higher-trace reduction, and the
  Bruhat refinement within equal black-count classes. The successive quotient
  surjections are unfinished. Their injectivity via the source dimension
  argument still requires the general braid pairing at (q=1).
  [Reconstruction](https://github.com/apellis/categorification-lean/pull/908)
  · [Generation](https://github.com/apellis/categorification-lean/pull/916)
  · [Successive quotients](https://github.com/apellis/categorification-lean/pull/937)
- **§7.** The graded fundamental braid and the normalized cup–braid–cap
  calculation are merged. The shifted clockwise comparison and double
  positive braid have focused proofs in drafts. The general ribbon twist
  and tangle relations remain open.
  [Cap comparison](https://github.com/apellis/categorification-lean/pull/918)
  · [Shifted trace](https://github.com/apellis/categorification-lean/pull/922)
  · [Double braid](https://github.com/apellis/categorification-lean/pull/934)
- **§8.2.** The middle ordered augmentation and the incoming exterior
  ambient (H^0) and tensor line are merged. Drafts give the graded
  middle recurrence and the characteristic-different-from-two reflected
  simple Tor₃ computation. The companion maps, recurrence base cases,
  and graded dual comparison for the nonsimple terms remain open.
  [Middle augmentation](https://github.com/apellis/categorification-lean/pull/872)
  · [Recurrence](https://github.com/apellis/categorification-lean/pull/932)
  · [Tor₃](https://github.com/apellis/categorification-lean/pull/935)

Engineering item: the §6–§8 files added on 23–24 November raise `maxHeartbeats` in
`BlockPartialStandardOrderedResolution`, `FiveSlotNearbyFlagInjection` and the
`LabelTwo*` modules (exterior complex, degrees, middle map, standard support, incoming
coordinates and degrees, middle exactness, augmentations, quotient coordinates, grading,
specialization and terminal parabolic). Remove these overrides by restructuring the
proofs (named intermediate statements, fewer nested transports), not by larger budgets.

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

The kernel is the trace of higher retained-boundary loading idempotents on the loading
projective (`blockLoadingKernel_eq_idempotentTrace`). To use
`blockLoadingKernel_hasFiltration`, construct a filtration in which the layers killed by
these idempotents precede a tail of higher partial standards generated by them.
For one black strand following the pair and a zero-weight spectator, the unit bigons
identify the source projective with the higher projective before the spectator. All loads
strictly above that higher loading are violated, so its partial standard gives one layer
of the kernel (`ThreeRedOneBlack.kernel_hasHigherFiltration`).
When all three red weights are positive, the first-weight boundary character
proves that this higher partial standard is nonzero. The one-black reduced paths
show that left multiplication by the spectator crossing
(`ThreeRedOneBlack.higherCrossingMap`) maps the higher loading projective onto
the kernel. For positive spectator weight, injectivity of this map remains the
input for the one-layer filtration.

At `b i a` there are distinct exits `i a b` and `a b i`. If `a b i` is strictly
higher, the joint `a i b` is higher too: moving a black left cannot decrease a
retained count. `blockKernelHigherExit_slide` changes the exit idempotent of an
arbitrary upper diagram in `K ⊗_T B`. If only `i a b` is marked, returning to it
costs `Λ_a(i)` dots, not an invertible crossing (`blockKernelBigon_slide`). For any
number of intervening blacks, `blockKernelIntervalBigon_slide` compares the two
extreme exits with the product of the corresponding dot powers at the left exit.
Separately, an excursion at the bottom to the consecutive column and back gives
`ker_blockKernelColumnInclusion_le_ker_dots`. When all intervening pairings with
`a` vanish the dot operator is the identity and the column inclusion is injective.

For symmetric `Q`, at the bottom `b i a` every permutation into the source order
inverts the outside positions. Two successive right descents give a reduced word
ending in `[j+1,j]` or `[j,j+1]`. Putting the dots on top gives two undotted
generators before quotient (`exists_interleavedColumn_exits`); balancing the ordered
coefficients into `K` gives two generators of `K ⊗_T B e(s)` even with spectators
(`exists_interleavedKernelColumn_exits`).

The relations with those exterior strands are determined in the projective row.
Write `L=i a b`, `D=a i b`, `R=a b i` for the three local source loadings. Sort the
three images of the bottom positions and use one exterior PBW word for each right
coset. In these coordinates the stack rows are `(1,X^A)`, `(1,1)`, `(X^B,1)` and
the signed joint columns are `(X^A,−1)`, `(1,−1)`, `(1,−X^B)`, with
`A=Λ_a(i)`, `B=Λ_b(i)`. Here `X` is the local black dot *below* the exterior word.
`ExitPBW.exists_parabolic_read` extends a choice of normal exit by linearity;
subtracting the readback of the stack expresses every relation between sums as a
joint image. `exists_interleavedRelation_affine_lift` lifts a zero stack with its
prescribed quotient coefficients. Thus `interleaved_affine_relation_iff` and
`interleaved_quotient_relation_iff` describe all relations, also those supported
at just one exit. Neither theorem identifies the higher ideal with global violations.

When there is **one black strand in total**, all paths from a non-higher loading to
a strictly higher loading must move that black to the left. PBW division on the
two-sided higher ideal leaves its upper factor in the ideal. The same forced descent
on globally violated loadings proves cancellation of the leftward crossing in the
violated algebra; the dot is cancelled only on the affine PBW basis. This gives
`firstWeight_exit_saturated`. Iterating to the first higher loading (or to a global
violation) gives a generator `g` of the marked row with support `e(u)` such that
`g y = 0` implies `e(u)y = 0`. Thus every marked class is `g ⊗ y` and a zero stack
is already zero by balancing `e(u)`. `firstWeight_blockKernelTensorInclusion_injective`
and `firstWeight_blockKernelColumnInclusion_injective` handle all mixed and same-exit
relations in this weight. `firstWeight_blockKernel_mixedExit` assumes membership of
the two crossed coefficients, not of their joint coefficient. The surjection and
its exact kernel are `firstWeight_interleavedColumn_presentation`: a pair `(x,y)`
of marked coefficients is a relation precisely when `xL + yR = 0` in the globally
violated algebra, with no quotient by higher loadings on the right-hand side.

For example take bottom `c b i a`, top `c a i b`, and pairings `(c,a,b)=(2,1,1)`.
Write `L_d,R_d` for the left and right exit with `d` dots on the reduced upper word.
With one black, each pair of endpoints has one PBW permutation. A black–red return
adds its pairing in dots; a red–red return vanishes. Factoring through a leftmost
black gives the upper dot cutoffs `2,3,3` at the left exit, joint and right exit,
respectively, and cutoff `2` for the stacked column. Through the strictly higher
`c i a b`, the marked exponents start at `0,1,1` at these three loadings. The
unmarked relations are `L₀=R₀`, `L₁=R₁`, `R₂=0`; the marked generators are
`L₀,L₁,R₁,R₂` with relations `L₁=R₁` and `R₂=0`. These two relations are the
images of the one- and two-dot joint coefficients. The remaining `L₀,L₁` stack
to distinct surviving PBW monomials, so there are no further relations. In
particular, checking only the nonzero mixed braid misses a same-exit relation.

For Lemma 6.8 the remaining intersection in these columns is
`im δ_P ∩ (K_L ⊕ K_R) = im δ_K`, with `δ(u)=(uψ_j,−uψ_(j+1))` at the cut
projectors. If `D` is strictly higher, its projector marks the joint witness.
In general `interleaved_joint_dot_mem` puts `u X^min(A,B)` in the higher ideal
by the two return bigons. `interleaved_markedColumn_injective` balances the marked
witness to prove column injectivity when `D` is strictly higher or either return
power is zero, with arbitrary exterior strands. When both powers
are positive and `D` is not higher, one needs a marked witness with the same two
components, i.e. a correction modulo `ker δ_P`, not division by `X`.
`interleaved_markedColumn_injective_of_right_leg` gives a sufficient condition:
the right joint leg is injective on the partially standardized corner. A different black
can furnish either a global violation or a higher retained boundary without the
specified descent. The first-weight division argument therefore does not extend
as stated; this is not a counterexample to injectivity. Ordinary parabolic coordinates
are linear for juxtaposed block diagrams, not for arbitrary upper elements of
`e(t)T`. Also open: filter `K` by higher
partial standardizations, apply the induction in (6.21), and identify the derived
comparison naturally. Then Prop 6.9
for general `ℓ` by reduction to two
red strands, the graded bounded-above functor of Def 6.6 and its equivariance (Prop 6.7), Cor 6.10
(proved for adjacent transpositions as `braidClass_pairSwap`, under `AllFiniteDeltaInjective` and
`RowFigureFiveHypotheses` (the two hypotheses of Lemma 6.8) at every row; finite-dimensionality of `T^λ` is
`tensorProductAlgebra_finite`; removing the other hypotheses is open), Lemma 6.11 (proved for
`w ≠ 1` as `hasCornerStandardFiltration_braidF` under the same hypotheses; the diagram
filtration of the step `p_n → f_n` is proved, `BraidColumnCutFiltration.lean`), Def 6.12, Cor 6.13,
Lemma 6.14; tilting modules (Thm 6.15); `𝔅_σ` are equivalences (Thm 6.16); the braid group
action (Cor 6.17); Ringel duality (Cor 6.18); semi-orthogonal decompositions (Prop 6.19); the
Serre functor (Prop 6.20).

In v3 numbering: Cor 6.8 (`𝔅 P⁰ ≅ P⁰`) is proved for all red orders with no extra hypothesis
(`bijective_redBraid_mul`, `RedFirstBraiding.lean`); Lemma 6.12 (composites,
`braidingFunctorCompIsoOfLengthAdd`) and Lemma 6.13 (compactness, `isCompact_braidingFunctor_obj`)
are proved under the hypotheses of Lemma 6.11. For Thm 6.15 the generic inputs are proved: a
coproduct-preserving triangulated functor which is bijective on the shifted Homs of a compact
generating family and sends it to a compact generating family is an equivalence
(`isEquivalence_of_compactlyGenerates`), and the vanishing form of Ext–Tor duality over a field
(`hom_dualModule_shift_eq_zero`). Remaining, in Webster's order: self-duality of `𝔅_τ P` through
the trace on `P⁰`, `ι`, `π` and Cor 6.8 (Thm 6.14), hence vanishing of the higher Ext between the
`𝔅_τ P`; the dimension count from Cor 6.11 with injectivity from Lemma 5.25; generation.

For the multi-strand interval calculation, `intervalConcat` puts a local KLR diagram
between fixed exterior loading idempotents. The map is injective for symmetric
parameters (`intervalConcat_injective`). Its image is the span of shifted
local PBW words and their shifted bottom dots (`range_intervalConcat_eq_span`).

### Phase E: §7, rigidity

For Definition 7.1, `coevaluationWord` uses the simple coroot pairings along a
reflection path. At nonnegative pairings, `rootSum_coevaluationWord` computes
its total root content from the endpoints. Linear independence then makes
the multiplicities independent of the chosen path with that endpoint.
`nonnegativeReflectionPath_of_reduced` checks the nonnegative pairings for a
reduced Weyl expression and a dominant integral starting weight in a Cartan
realization. Thus `coevaluationWord_multiplicities_eq_of_reduced` compares
reduced expressions of the same Weyl element.

Lemma 7.3 (v3) is proved: the coevaluation wrap projective has the unique simple
head `Stendhal.coevaluationHead`, with kernel the trace of the projectives with
`κ(2) < 2ρ∨(λ)` (`CycKLR.coevaluationTrace_eq_iff_isSimpleModule`). The proof does
not use crystals: it erases the red strands onto the cyclotomic quotient, using the
second red strand's cyclotomic relation at the lowest weight from Kang–Kashiwara.
Coevaluation and evaluation for a pair (Prop 7.2, Def 7.4, Props 7.5, 7.6,
7.8, Cors 7.7, 7.9, 7.10); ribbon structure (Prop 7.11, Def 7.12, Prop 7.13); general
coevaluation and quantum trace (Def 7.15, Lemmas 7.16, 7.17, 7.19, Def 7.18,
Props 7.20, 7.21, 7.22). Defs 7.14, 7.15 and 7.18 are done. Lemma 7.17 is proved for the
cap at the right end (`j = ℓ`, `CupCap.capBasis`) for symmetric `Q`, under the route
hypotheses that the (max1) scalars are units and `PullOffLeft` (the mirror of Lemma 7.16);
at Webster's `L_μ` (`CupCap.capBasis_coevaluationHead`, over a field) the support
hypothesis is proved, leaving these two; removal items: prove Lemma 7.16 and its mirror
for `L_μ`. For a cap after any `λ_j` (`CupCap.midCapBasis`), Lemma 7.17 is proved for
symmetric `Q` under the same route hypotheses plus `PullOff` (Lemma 7.16) and the support
hypothesis: the model is induced along the diagrams at the maximum placed just before the red
strand `λ_{j+1}`, all KLR relations hold on it (`CupCap.midKLRRel`), it is isomorphic to
`K̃^{λ⁺}_λ` as a bimodule (`CupCap.midCapModelEquiv`), and its basis is indexed by Webster's
`B″` (`CupCap.MidTriple`); its elements are Webster's diagrams, with the maximum at its
canonical position at the top and every strand passing under it (`CupCap.midCapBasis_apply`).
Removal item: Lemma 7.16 and its mirror for `L_μ` (needs Thm 4.30).
The projectivity of `coe^{λ⁺}_λ` as a left `T^λ`-module, asserted after Lemma 7.19, is proved
for a cap at the right end (`j = ℓ`, `CupCap.projective_capBimodule`) when the pieces `L e(t)`
are free over `k`, and for a cap after any `λ_j` (`CupCap.projective_midCapBimodule`) when the
pieces `L e(t)` are finitely generated and projective over `k` (true for `L_μ` over a field;
removal item: drop finite generation for general `L`), under the route hypotheses of Lemma 7.17.
Lemma 7.19 and Props 7.20–7.22 are open.

### Phase F: §8, knot invariants

Tangle functors and decategorification (Prop 8.1); finiteness for links (Thm 8.2) and
minuscule tangles (Prop 8.3); the unknot for `sl₂` (Prop 8.4); independence of the
projection (Thm 8.6, Lemma 8.7); ribbon elements (Prop 8.8); minuscule duality
(Thm 8.11). All open.

### Phase G (optional): §9 comparisons and their inputs

Optional item (maintainer, 2026-11-27): skipped for now, to be taken up only on request. It
covers the comparisons with other categories and everything only they need:

* Thm 5.31 (v3: Thm 5.34): for `sl_n`, the algebras `T^λ` and blocks of cyclotomic
  `q`-Schur algebras.
* Cyclotomic degenerate Hecke algebras and parabolic category `𝒪` (Defs 9.1, 9.2, 9.4,
  Lemma 9.3, Prop 9.6); the equivalence `𝒪^p_λ ≃ V^λ` (Props 9.9, 9.11–9.13), Koszulity
  and graded lift (Prop 9.14, Cor 9.15); the affine case (Thm 9.16); other knot
  homologies (Props 9.18, 9.20, 9.21).

All open. The external inputs below are recorded for when the item is taken up.

### Inputs from other works (maintainer decisions)

* Prop 9.6 and Thm 9.16 are the Brundan–Kleshchev isomorphism (arXiv:0808.2032),
  which is not in the library. Options: formalize it, or take it as a stated
  hypothesis of the §9 results (Phase G, optional).
* Thm 5.31 (v3: Thm 5.34) and §9 compare with cyclotomic `q`-Schur algebras and category `𝒪`;
  they are in the optional Phase G (maintainer, 2026-11-27).
* Prop 9.14 (Koszulity) and Props 9.18–9.21 rest on results of other papers (for
  example Enright–Shelton equivalences). These are flagged in the same way when
  they are reached.
