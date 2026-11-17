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
  basis before imposing the violating ideal. Their projections span the
  quotient, and over a field one can select a homogeneous basis from them.
  `Stendhal.coeff_gdim_tensorProductGrade` counts the selected terms.
  `Stendhal.finrank_tensorProductGrade_eq_card_sub_rank` computes the dimension
  using products through violated cuts, under the hypotheses of the ambient
  standard-basis theorem. In particular, its weighted presentation uses
  loop-free data and zero black edge weights.
* A permutation formula with no relation rank left to compute is a stronger
  dimension statement. Hu–Shi, arXiv:2108.05508v5, Theorem 1.1 gives such a
  formula for ordinary cyclotomic corners. Repeated labels can contribute
  several permutations for a single pair of boundary words. The general
  formula remains open. For a diagonal word with distinct labels,
  `AbsentColour.finrank_diagonalCornerGrade_of_nodup` computes the coefficient
  of the product of the geometric sums for the prefix Cartan pairings.

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
| Proposition 3.21, one-factor highest-weight representation | `CycKLR.projectiveK0Basis` gives a Laurent basis, and `CycKLR.lower` and `CycKLR.raise` give the lowering and raising operators by graded induction and shifted restriction. Its vacuum and first lowering are computed by `indK0_vacuum`, `singleK0Equiv_regular`, and `singleK0_eq_zero`. | Establish the graded quantum-group relations and integral highest-weight representation identification in all weights. |
| Theorem 4.20, single-red algebra | `SingleRed.cyclotomicEquiv` identifies the one-red block with the monomial cyclotomic algebra for every black multiset over a commutative ring. | Transport the graded representation and projective class comparison along this algebra identification. |
| Proposition 4.18, adding the last red strand | The corner is cut out by the ordered loadings ending in the last red strand. | Identify the algebra for the shorter list with this corner of the violating quotient. |
| Lemmas 4.35 and 4.36, projective decompositions and pairing | `Stendhal.finrank_homGrade_sequenceProj` computes the dimension of the homogeneous Hom between undivided sequence projectives from the quotient basis. | Match the graded projective decompositions with the quantum commutator and identify the Hom pairing with the tensor product pairing, including divided powers. |
| Lemma 4.37 and Theorem 4.38 | `Stendhal.tensorProductVacuumK0Equiv_regular` identifies the vacuum class for every red family. `Stendhal.emptyTensorK0Equiv` accounts for every weight of the empty family. | Prove integral spanning by the divided projectives and the tensor product isomorphism for arbitrary families. |
