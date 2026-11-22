# Errata

Errors found while formalizing the sources of this library. Each entry gives the printed
statement, the corrected statement, the declarations that refute the printed version and prove
the corrected one, the roadmap item where one is open, and a short paragraph that can be sent to
the authors as is. Locators refer to the cited arXiv version.

Contents:

- [Khovanov–Lauda III, arXiv:0807.3250v1](#khovanovlauda-iii-arxiv08073250v1)
  - [1. Lemma 5.4 (iii), eq. (5.45)](#1-lemma-54-iii-eq-545)
- [Webster, arXiv:1209.2463v4 (weighted KLR algebras)](#webster-arxiv12092463v4-weighted-klr-algebras)
  - [2. Proposition 2.15, sign of the coboundary](#2-proposition-215-sign-of-the-coboundary)
  - [3. §2.1, degree function](#3-21-degree-function)
  - [4. Theorem 2.19](#4-theorem-219)
- [Webster, arXiv:1309.3796v2 (tensor product categorification)](#webster-arxiv13093796v2-tensor-product-categorification)
  - [5. (2.2a–b), bubble degrees](#5-22ab-bubble-degrees)
  - [6. (2.2a) and (2.5e), pitchfork and downward relations](#6-22a-and-25e-pitchfork-and-downward-relations)
  - [7. Proposition 3.31, proof gap](#7-proposition-331-proof-gap)
  - [8. §4.5, κ(0) and the citation of (4.4d)](#8-45-κ0-and-the-citation-of-44d)
  - [9. Lemma 4.35, insertion and deletion conditions](#9-lemma-435-insertion-and-deletion-conditions)
  - [10. The form before Proposition 4.33, and Lemma 4.36](#10-the-form-before-proposition-433-and-lemma-436)

## Khovanov–Lauda III, arXiv:0807.3250v1

### 1. Lemma 5.4 (iii), eq. (5.45)

**Printed.** In `H_{k^{+i}} ⊗_{H_{+_i k}} H_{k^{+i}}`, with `d = k_i - k_{i-1}`,
`∑_{f=0}^{d} (-1)^{d-f} ξ_i^{f+1} ⊗ x(k)_{i+1,d-f} = ∑_{g=0}^{d} (-1)^{d-g} ξ_i^g ⊗ x(k)_{i+1,d-g} ξ_i`.

**Corrected.** The same identity with `x(k)_{i,·}` in place of `x(k)_{i+1,·}`. This is the
version that the proof (from part (i)) establishes and that Corollary 5.5 uses.

**Declarations.** Refuted, under either reading of `x(k)_{i+1,β}` in `H_{k^{+i}}`:
`Categorification.Flag.Erratum545.lemma_5_4_iii_printed_false`,
`Categorification.Flag.Erratum545.lemma_5_4_iii_printed_false'` (`N = 2`, `k = (0, 1, 2)`, any
field of characteristic `≠ 2`; a bilinear trace form takes the values `-1` and `1` on the two
sides). Corrected: `Categorification.Flag.lemma_5_4_iii`.

**Roadmap.** None open: the corrected lemma and Corollary 5.5 are proved.

**For the authors.** In Lemma 5.4 (iii), eq. (5.45), the index `i+1` on `x(k)` should be `i`.
As printed the identity fails already for `N = 2`, `k = (0, 1, 2)`; the proof from part (i) and
the application in Corollary 5.5 both concern `x(k)_{i,·}`.

## Webster, arXiv:1209.2463v4 (weighted KLR algebras)

### 2. Proposition 2.15, sign of the coboundary

**Printed.** The shifted weighting is `(ϑ + dη)_e = ϑ_e + η_{h(e)} - η_{t(e)}`, with the
`i`-strands moved right by `η_i`.

**Corrected.** `ϑ'_e = ϑ_e + η_{t(e)} - η_{h(e)}`. With the paper's walls `x_b - x_a = ϑ_e`
(`a` of colour `h(e)`, `b` of colour `t(e)`), moving the strands by `η` changes `x_b - x_a` by
`η_{t(e)} - η_{h(e)}`. For `ϑ = 0`, `η_{h(e)} = 1`, `η_{t(e)} = 0` and `x_b - x_a = 1`, the
printed weighting gives the moved point the wall value `-1` instead of `1`. The proof in the
paper (the ghost moves right by `η_{t(e)}`) uses the corrected sign.

**Declarations.** `WeightedKLR.weightedKLRShiftEquiv`, with the corrected sign; the printed sign
is the same statement with the strands moved by `-η`.

**Roadmap.** None open.

**For the authors.** In Proposition 2.15 the coboundary should read `ϑ_e + η_{t(e)} - η_{h(e)}`
(or the strands should move left by `η_i`); the proof is unaffected.

### 3. §2.1, degree function

**Printed.** A dot on an `i`-strand has degree `⟨α_i, α_i⟩`, a crossing of strands of colours
`i, j` degree `-δ_{ij}⟨α_i, α_i⟩`, and a crossing of a strand of colour `i` with a ghost of
colour `j` degree `-½⟨α_i, α_j⟩(1 - δ_{ij})`.

**Corrected.** Reading `⟨α_i, α_i⟩ = d_i` and `⟨α_i, α_j⟩ = -d_{h(e)} c_e` for a single edge,
the printed degrees make every relation homogeneous. They fail in three cases:
(a) with several edges between `i` and `j` (of different weights), a ghost crossing of the edge
`e` must have degree `½ d_{h(e)} c_e` for its own edge, since the ghost bigon of `e` multiplies
by `Q_e` alone; (b) for a loop `e` of nonzero weight at `i`, the factor `1 - δ_{ij}` gives an
`i`-strand crossing its own ghost degree `0`, while the bigon multiplies by `Q_e`, of degree
`d_i c_e > 0`; (c) for a loop of weight `0` at `i`, the same-colour bigon relation, which
involves `P_e`, forces a crossing of two `i`-strands to have the degree of `P_e`, not
`-⟨α_i, α_i⟩`. The pairing of §2.4 includes loop terms, which does not repair (b) or (c). The
corrected degree function (in the normalization doubled to avoid half-integers): a dot `2d_i`,
a step across a wall of `e` degree `d_{h(e)} c_e`, a same-colour crossing `-2d_i`, or
`2d_i(c_i - 1)` (twice the degree of `P_e`) at a loop of weight `0`.

**Declarations.** `WeightedKLR.WeightedGraph.Standing.gradingDatum` (the corrected degrees),
`WeightedKLR.GradingDatum.gradedAlgebra` (the graded algebra with this datum).

**Roadmap.** None open.

**For the authors.** In §2.1 the degree of a ghost crossing should be taken edge by edge
(`½ d_{h(e)} c_e` for the ghost of the edge `e`, including loops of nonzero weight), and at a
loop of weight `0` the crossing of two `i`-strands should have the degree of `P_e`.

### 4. Theorem 2.19

The antipode recursion in the proof of Theorem 2.19 and the scope of its quantum-group map are
recorded in the README, next to the Theorem 2.19 row (section on weighted KLR algebras).

## Webster, arXiv:1309.3796v2 (tensor product categorification)

### 5. (2.2a–b), bubble degrees

**Printed.** For region weight `n`, the bubble labels in (2.2a) are `−n−1−j` and `n−1−j`, and
negative-degree vanishing is stated for `j < 0`. In (2.2b) the inverse-bubble sum runs to
`j+n+1`.

**Corrected.** Negative-degree vanishing for `j > 0` (as printed in v3 (2.3a)), and upper bound
`j−n+1` in (2.2b), as given by the bubble-series inversion stated in the text; with `d = j+2` the
two normalized indices are `a` and `d−a`, `0 ≤ a ≤ d`. Version 3 retains the bound `j+n+1` in
(2.3b). With the printed bound, for `n = j = −2` the sum is empty although the right side is the
identity: with one fundamental red and one downward black strand in sl₂ over ℚ, the exterior
weight is `−1`, and at `j = −2` the printed interval `[0, −2]` annihilates the boundary identity
of a block isomorphic to ℚ.

**Declarations.** Refuted: `Categorification.Stendhal.DoubleDiagram.printedBubble_no_injection_sl2`.
Corrected: `DoubleDiagram.bubble_eq_of_le`, `DoubleDiagram.bubbleGrassmannian` (repaired
nonpositive degrees and convolution).

**Roadmap.** None open beyond entry 6.

**For the authors.** In (2.2a) the vanishing of negative-degree bubbles should be stated for
`j > 0`, and in (2.2b) the upper bound of the sum should be `j − n + 1`; with `j + n + 1` the
sum is empty for `n = j = −2`.

### 6. (2.2a) and (2.5e), pitchfork and downward relations

v3 numbering: (2.2a), (2.3a), (2.5b), (2.6e).

**Printed.** Definition 2.4 imposes the cup and cap pitchfork relations (2.2a), both with the
coefficient `t_{ji}` on the downward-crossing side, together with the downward quadratic
relation (2.5e).

**Why it fails.** If `c` and `d` are the cup and cap pitchfork coefficients, `p` the downward
bigon and `q` the sideways (mixed) bigon, composing the two pitchforks forces `c d p = q`. With
both pitchfork coefficients printed as `t_{ji}` and equal bigons this forces `t_{ji}² = 1`.
Example: disconnected colours `i, j` with `Q_{ij} = Q_{ji} = 2` over ℚ, one red of coroot
coordinates `(1, 1)` and one downward `j` to its right. Compose the vertical mirror of the cup
pitchfork with the cap pitchfork. Both bigons have coefficient `2`, and the bare `i`-bubble on
either side of `j` has degree zero since `a_{ij} = 0`. The composite gives `8 id = 2 id`, while
the ordinary one-black algebra is `ℚ[x]/(x) ≅ ℚ`, so the presentation admits no injective
comparison with it, even with the corrected bubble bound of entry 5.

**Corrected.** Keep the printed pitchforks and take the downward black relations with the
reflected dual parameters of Cautis–Lauda, arXiv:1111.1431v3, §2.2; in the example these give
`p = 1/2`, and `c = d = 2` satisfies `c d p = q`. Lemma 4.28 (v3: Lemma 4.29) and the results
that depend on it are formalized in this normalization.

**Declarations.** Refuted: `Categorification.Stendhal.DoubleDiagram.printedPitchfork_no_injection`;
the necessary conditions `DoubleDiagram.pitchforkCoefficients_mul_bigon` (`c d p = q`) and
`DoubleDiagram.pitchforkCoefficients_mul_eq_one` (`c d = 1` for equal nonzero bigons and unit
bubble closures, over any field). Corrected: `DoubleDiagram.rescaledDownward_qCL`.

**Roadmap.** [Tensor product roadmap](docs/WeightedKLR/tensor-product-roadmap.md), pitchfork
compatibility and faithfulness in the Cautis–Lauda normalization (open).

**For the authors.** In the definition of the diagrammatic tensor product category, the cup and
cap pitchfork relations (2.2a) and the downward quadratic relation (2.5e) are not compatible for
general Rouquier parameters. For two disconnected colours with `Q_{ij} = Q_{ji} = 2`, a red of
weight `(1, 1)` followed by one downward black strand has ordinary endomorphism algebra ℚ, but
composing the two pitchforks gives `8·id = 2·id` there. Taking the downward relations with the
dual parameters of Cautis–Lauda (so the downward bigon is `1/2` in this example) restores
compatibility.

### 7. Proposition 3.31, proof gap

**Printed.** The set `B′` (the spanning set of Lemma 3.29, with integer dot exponents) is a basis
of each Hom space of the localization `U′` of Definition 3.28. The proof deduces linear
independence from an action of `U′` on the universal cyclotomic quotient `Ř^λ`.

**The gap.** That action does not exist. Take sl₂, `λ = 1` and one black strand, at region weight
`−1`. The downward dot acts on `Ř^λ` by an invertible element `z`, and the clockwise honest
bubble with `−1` dots on its downward arc acts by `−1/z ≠ 0`. In `U′` this bubble equals the fake
bubble of the same label, which has negative degree and is `0`. So the action of `U` on `Ř^λ`
does not factor through `U → U′`.

**Corrected.** We know neither a proof nor a counterexample for Proposition 3.31; a proof would
in particular show that `U → U′` is faithful on Hom spaces. Section 3.6 is absent from v3.
Corollary 3.32 (`γ` is an isomorphism) does not depend on it here: it is KL III Theorem 1.2,
proved for every Cartan datum.

**Declarations.** Definition 3.28: `KL3.Diagram.presLoc`, `KL3.Diagram.toLoc`. Lemma 3.29:
`KL3.Diagram.span_twoBL_eq_top`. Proposition 3.30: `KL3.Diagram.shiftEquivalence`,
`KL3.Diagram.shiftHomEquivalence`. Corollary 3.32: `gammaAlg_injective_unconditional`,
`gammaAlgEquiv_unconditional`. Proposition 3.31 is not stated as proved.

**Roadmap.** [Tensor product roadmap](docs/WeightedKLR/tensor-product-roadmap.md), Phase B,
Prop 3.31: prove or refute.

**For the authors.** In the proof of Proposition 3.31, `Ř^λ` is not a `U′`-representation: for
sl₂, `λ = 1`, one strand and weight `−1`, the honest bubble with `−1` dots acts by `−1/z ≠ 0`,
while `U′` sets it equal to a fake bubble of negative degree, which is `0`. Linear independence
of `B′` needs another argument, for instance a faithful representation of `U′` itself.

### 8. §4.5, κ(0) and the citation of (4.4d)

**Printed.** The violation condition before Definition 4.27 is `κ(0) > 1`, and the proof of
Theorem 4.29 cites (4.4d) for the two red/up inverse identities.

**Corrected.** `κ(0)` is outside the domain of `κ` in Definition 4.23. The intended condition is
that the first strand is black, of either orientation: with at least one red strand this is
`κ(1) > 0`, and with no red strand it means the word is nonempty. The two red/up inverse
identities are (4.4e); (4.4d) is a three-strand relation. Both are misprints.

**Declarations.** `Categorification.Stendhal.DoubleBoundary.IsViolated`,
`Categorification.Stendhal.DoubleDiagram.redUpCrossingIso`.

**Roadmap.** None open.

**For the authors.** Before Definition 4.27, `κ(0) > 1` should read `κ(1) > 0` (the first strand
is black); in the proof of Theorem 4.29 the reference (4.4d) should be (4.4e).

### 9. Lemma 4.35, insertion and deletion conditions

**Printed.** For insertion of a black strand in gap `j`, increase `κ(m)` when `κ(m) ≤ j`; for
deletion of black strand `j+1`, decrease `κ(m)` when `κ(m) ≤ j+1`.

**Corrected.** For insertion just before the red strands in gap `j`, increase `κ(m)` when
`κ(m) ≥ j`; for deletion of black strand `j+1`, decrease `κ(m)` when `κ(m) > j`. A single
fundamental red followed by one black strand already gives a printed deletion coordinate of `−1`.
The coroot coordinate `n` for the commutator is evaluated immediately before that lowering, at
`µ(j+1) + α_i` for its colour `i`; passing an `i`-strand lowers it by two. In the example the input
has coordinate `+1` and the printed `µ(j+1)` gives `−1`: on the highest vector `h`, `EFh = h ≠ 0`
and `FEh = 0`. For `n < 0` the summand on the `FE` side has graded multiplicity `[−n]_i`.

**Declarations.** `Categorification.Stendhal.ProjectiveCommutator.printed_deletion_out_of_range`,
`ProjectiveCommutator.fundamental_commutator_weights`,
`ProjectiveCommutator.fundamental_commutator_on_highest`,
`Stendhal.FirstWeight.blackBlockPairing_cons_self`.

**Roadmap.** [Tensor product roadmap](docs/WeightedKLR/tensor-product-roadmap.md), Lemmas 4.35
and 4.36 (identification with the boundary ideals of Definition 4.34 is open).

**For the authors.** In Lemma 4.35 the conditions should read `κ(m) ≥ j` for insertion and
`κ(m) > j` for deletion; with the printed conditions a single fundamental red followed by one
black strand gives the deletion coordinate `−1`; the coroot coordinate of the commutator is the one at
`µ(j+1) + α_i`.

### 10. The form before Proposition 4.33, and Lemma 4.36

**Printed.** The sesquilinear form on `V_{λ₁} ⊗ ⋯ ⊗ V_{λₙ}` defined before Proposition 4.33 applies
the intertwiner `Θ` to the first argument of the factorwise form, which is bar-semilinear in the
first argument. Lemma 4.36 and Theorem 4.38 identify this form with the graded Euler (Hom) form
on projectives.

**Why it fails.** With the coproduct of §1.2, the printed form takes the bar conjugates
(`q ↦ q⁻¹`) of the graded Hom dimensions. For two fundamental sl₂ factors, the squared norm of
`F(h ⊗ h)` under the printed form is `1 + q⁻²`, while the graded endomorphism polynomial of the
corresponding terminal-strand projective is `1 + q²`. The identity relating the bar-conjugate
coproduct to the adjoint in (3.24) also fails: on `h ⊗ f` with `u = F`, the two sides give
`h ⊗ h` and `q² h ⊗ h`.

**Corrected.** Apply `Θ` to the second argument: `(x, y) ↦ (x, Θ y)` factorwise. This form
satisfies the adjunction of Proposition 4.33(2) with the ordinary coproduct and (3.24), for
arbitrary dominant factors (finite simple-root index set, X-regular root datum), and equals the
graded Euler pairing `Hom(P, Q)` on the images of `Q` and `P`, for arbitrary finite red families
and all black contents, for right and left projectives alike.

**Declarations.** Refuted: `Categorification.Stendhal.TensorPairing.terminal_homGdimPoly_ne_printedForm`,
`TensorPairing.printedForm_loweredPair`. Corrected: `TensorPairing.correctedForm_adjoint`,
`TensorPairing.correctedForm_append_highest`,
`TensorPairing.fundamental_prefix_homGdimPoly_eq_correctedForm`,
`Stendhal.FirstWeight.tensorModuleEquiv_homForm`, `FirstWeight.tensorModuleEquiv_homGdimPoly`,
`FirstWeight.rightTensorModuleEquiv_homForm`, `Stendhal.FundamentalCorner.terminal_homGdimPoly`.

**Roadmap.** None open for the form; the identification with the boundary ideals of
Definition 4.34 is open (entry 9).

**For the authors.** The form defined before Proposition 4.33 should apply `Θ` to the second
argument. As printed its values are the bar conjugates of the graded Hom dimensions: for two
fundamental sl₂ factors it gives `‖F(h ⊗ h)‖² = 1 + q⁻²`, while the graded endomorphism ring of the
corresponding projective has dimension `1 + q²`. With `Θ` on the second argument, Proposition
4.33(2), Lemma 4.36 and the pairing in Theorem 4.38 hold.
