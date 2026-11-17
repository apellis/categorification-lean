# Webster, Theorem 2.19: the ground ring

Source: B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19 and its proof. The proof refers to Khovanov–Lauda I (arXiv:0803.4121v2),
Proposition 2.18 and §3.2. Declarations below are in the namespace
`Categorification.WeightedKLR` unless prefixed otherwise.

## The printed statement

§2.1 of the source fixes an arbitrary commutative ring `k`. Theorem 2.19 asserts that
`K = ⊕_ν K_0(W_ν)` is a twisted bialgebra over `ℤ[q, q⁻¹]`. Here `K_0` is the Grothendieck
group of finitely generated projective modules, and `K` is graded by `ℤ[I]` and by the
internal degree.

* The product is `[M][N] = [Ind(M ⊠ N)]`.
* The coproduct is `Δ[L] = ∑_{ν' + ν'' = ν} [Res_{ν';ν''} L]`.
* The twist on `K ⊗ K` is `q^{deg b · deg c}`.

The theorem also asserts a natural map `U_q^+(𝔤_Γ) → K`, and that `K` is a Hopf algebra in the
braided category of `ℤ[I]`-graded modules.

The coproduct as printed takes values in `⊕ K_0(W_{ν'} ⊗_k W_{ν''})`. To read it as a map
`K → K ⊗ K`, one composes with the inverse of the comparison map

`c : K_0(W_{ν'}) ⊗_{ℤ[q^±]} K_0(W_{ν''}) → K_0(W_{ν'} ⊗_k W_{ν''})`, `[P] ⊗ [Q] ↦ [P ⊠ Q]`.

## What holds over any commutative ring

These statements do not involve the comparison map.

* **Induction.** `Ind` sends finitely generated projective modules to finitely generated
  projective modules. The product on `K` is well defined, biadditive, associative and unital.
  Formalized, ungraded:
  * `Juxtapose.indK0`, `Juxtapose.indK0_assoc`, `Juxtapose.indK0_one_left`,
    `Juxtapose.indK0_one_right`;
  * `InductionAlong.Ind.projective`, `InductionAlong.Ind.finite`.
* **Restriction.** `Res` sends finitely generated projective modules to finitely generated
  projective `W_{ν'} ⊗ W_{ν''}`-modules, so `Δ` is defined with values in
  `⊕ K_0(W_{ν'} ⊗ W_{ν''})`. Formalized, ungraded, under the standing hypothesis:
  * `Juxtapose.res_projective`, `Juxtapose.res_finite`, `Juxtapose.resProj`,
    `Juxtapose.resK0` (`Δ_{ν';ν''}`, additive), `Juxtapose.resK0_of`;
  * see the last section for the proof; the KLR analogue is `KLR.KLRAlgebra.res_projective`.
* **Coassociativity** of `Δ` in this form. Formalized, ungraded, under the standing hypothesis:
  * `Juxtapose.resK0_coassoc`: `α ∘ (Δ_{ν₁;ν₂} ⊗ id) ∘ Δ_{ν₁+ν₂;ν₃} = (id ⊗ Δ_{ν₂;ν₃}) ∘
    Δ_{ν₁;ν₂+ν₃} ∘ castW`, with `α` the associator of `W_{ν₁} ⊗ W_{ν₂} ⊗ W_{ν₃}`;
  * `Juxtapose.resLeftK0`, `Juxtapose.resRightK0`: `Δ ⊗ id` and `id ⊗ Δ`, restriction along
    `ι ⊗ id` and `id ⊗ ι`;
  * `InductionAlong.Res.tensorLeftEquiv` (`Res (φ ⊗ id) (B ⊗ C) ≅ Res φ B ⊠ C`),
    `InductionAlong.Res.tensorLeft_projective`, `tensorLeft_finite` and their `tensorRight`
    mirrors: restriction along `φ ⊗ id` and `id ⊗ φ` preserves finitely generated projectives
    whenever `Res φ B` is finitely generated projective;
  * the module-level isomorphism `Juxtapose.resCoassocEquiv`, transported to `K_0` with
    `ProjK0.map_of_semilinear`.
* **The Mackey identity.** The Mackey filtration of `Res ∘ Ind` gives an identity between
  `Δ(xy)` and the twisted product of `Δ(x)` and `Δ(y)`, written in `⊕ K_0` of the four-fold
  tensor products.
  * The degree shift is the symmetric pairing `-(μ · μ')`; see the notation note in the README.
  * The filtration and its subquotients are partly formalized (README, rows for §2.4).
  * Step (i) of the proof, the steps are sub-bimodules, is formalized for the whole algebra:
    `GalleryAlgebra.bimoduleFilt` assembles the corner filtrations `mackeyFilt D C S`, and
    `GalleryAlgebra.inductionMap_mul_mul_mem_bimoduleFilt` gives stability under
    `x ↦ ι_{ν₁;ν₂}(u) x ι_{ν';ν''}(w)` for every lower set `S` of shuffle types. The hypotheses
    are those of `mackeyFilt` (chamber segments, `Γ.Dagger`, `Γ.NoZeroLoops`, `Γ.PSymm`, regular
    wall factors and loop factors), as at the corner level.
  * Step (iii), the passage to `K_0`, is formalized generically: tensoring with a projective
    module is exact on bimodules (`BalancedTensor.mapLeftBimodule_exact`), and a finite filtration with
    finitely generated projective subquotients gives a finitely generated projective module whose
    class is the sum of theirs (`ProjK0.exists_of_eq_sum_of_chain`). The two are combined in
    `ProjK0.exists_of_balancedTensor_eq_sum`: for a chain `0 = F 0 ≤ ⋯ ≤ F n = M` of sub-bimodules
    (`SubBimodule`) of a `(B, A)`-bimodule, with surjective bimodule maps `F (i+1) → Y i` of kernel
    `F i`, and a projective left `A`-module `N` with every `Y i ⊗_A N` finitely generated projective
    over `B`, one has `[M ⊗_A N] = ∑_i [Y i ⊗_A N]` in `K_0(B)`.
  * Step (ii) is formalized per shuffle type, for arbitrary weights. `GalleryAlgebra.resIndFilt S`
    cuts the filtration down to `e_{ν₁;ν₂} W_ν e_{ν';ν''}`. Write `ν' = a + b`, `ν'' = c + d`,
    `ν₁ = a + c`, `ν₂ = b + d` and `μ = c`. Let `S` be a lower set whose only type outside a lower set
    `S' ⊇ {μ' < μ}` is `μ`. Then `Juxtapose.exists_middleResInd_equiv` gives a linear isomorphism
    from the balanced tensor product
    `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W_a ⊗ W_b ⊗ W_c ⊗ W_d} e (W_{a+b} ⊗ W_{c+d})` to the subquotient `S / S'`.
    It intertwines the two bimodule actions; the layout form is `Juxtapose.middleResIndEquiv`.
    So the corner maps are balanced and Webster's bimodule claim holds as stated.
  * Applied (`GalleryAlgebra.exists_resInd_balancedTensor_eq_sum`): the corner
    `e_{ν₁;ν₂} W e_{ν';ν''}` is a bimodule (`ResIndBimodule`); the occurring shuffle types are
    enumerated compatibly with dominance, the steps form a chain of sub-bimodules from `0` to the
    corner, and each step maps onto the piece `ResIndPiece L` of its type with kernel the previous
    step. So for projective `N` with each `ResIndPiece L ⊗ N` finitely generated projective,
    `[ResIndBimodule ⊗ N] = ∑ [ResIndPiece L ⊗ N]` in `K_0(W_{ν₁} ⊗ W_{ν₂})`, one term per type.
  * Restriction of induction (`GalleryAlgebra.resIndTensorEquiv`): for every left
    `W_{ν'} ⊗ W_{ν''}`-module `X`, `Res_{ν₁;ν₂} Ind X ≅ ResIndBimodule ⊗ X` as left
    `W_{ν₁} ⊗ W_{ν₂}`-modules, with `W_{ν₁+ν₂}` acting through `castW`.
  * The pieces (`ResIndPiece.balancedTensor_projective`, `ResIndPiece.balancedTensor_finite`):
    under the standing hypothesis, `ResIndPiece L ⊗ N` is finitely generated projective for every
    finitely generated projective `N`, since `e (W_{a+b} ⊗ W_{c+d}) ≅ Res W_{a+b} ⊠ Res W_{c+d}`.
  * The identity in `K_0` (`exists_resK0_indK0_eq_sum_tensorK0`, on classes `[P]`, `[Q]`:
    `exists_resK0_indK0_eq_sum`): under the standing hypothesis, over any commutative ring, for
    `ν₁ + ν₂ = ν' + ν''` and all `x`, `y`,
    `Δ_{ν₁;ν₂}(x · y) = ∑_L [ResIndPiece L ⊗ (x ⊠ y)]`, one layout `L` per shuffle type. The
    ungraded `K_0` needs no shift.
  * The pieces as twisted products of coproducts (`WeightedKLR/Mackey/ResIndTwist.lean`).
    For the layout `ν' = a + b`, `ν'' = c + d`, `ν₁ = a + c`, `ν₂ = b + d`,
    `ResIndPiece.resTwistEquiv` is a `k`-linear isomorphism
    `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)} (Res_{a,b} P ⊠ Res_{c,d} Q) ≅
    ResIndPiece L ⊗_{W_{ν'} ⊗ W_{ν''}} (P ⊠ Q)`, semilinear along `L.leftEquiv`
    (`resTwistEquiv_smul`). Here the middle algebra acts on `(W_{a+c} ⊗ W_{b+d}) e'` through
    `(ι_{a,c} ⊗ ι_{b,d}) ∘ (exchange of W_b and W_c)` (`Juxtapose.middleTop`), and `P`, `Q` are
    restricted along `castW` to `W_{a+b}`, `W_{c+d}`. On `K_0`: `ProjK0.extTensor`
    (`[P], [Q] ↦ [P ⊠ Q]`, biadditive), `Juxtapose.middleIndK0` (induction along the twisted
    map), the biadditive map `ResIndPiece.twistK0`,
    `x, y ↦ (Ind_{a;c} ⊗ Ind_{b;d}) ∘ (exchange) (Δ_{a;b} x ⊠ Δ_{c;d} y)`, and
    `ResIndPiece.tensorK0_eq_twistK0`. Combined: `exists_resK0_indK0_eq_sum_twistK0`, under
    `Γ.Dagger`, `Γ.NoZeroLoops`, `Γ.Standing`, over any commutative ring, for
    `ν₁ + ν₂ = ν' + ν''`: there are layouts `L i`, one per shuffle type (injective in `i`, with
    range the occurring types), such that for all `x ∈ K_0(W_{ν'})`, `y ∈ K_0(W_{ν''})`,
    `Δ_{ν₁;ν₂}(x · y) = ∑_i (Ind_{a;c} ⊗ Ind_{b;d}) ∘ (exchange) (Δ_{a;b} x ⊠ Δ_{c;d} y)`
    in `K_0(W_{ν₁} ⊗ W_{ν₂})`, with `W_{ν'+ν''}` and `W_{ν₁+ν₂}` identified by `castW`.
    The ungraded identity has no shift. The four-block layout agrees with the source's
    (`a = ν₁ - μ`, `c = μ`, `b = μ'`, `d = ν₂ - μ'`); the exchange of the middle factors is
    implicit in the printed formula.
  * The Mackey identity in `K_0 ⊗_ℤ K_0` (`WeightedKLR/Mackey/CoproductK0.lean`).
    * Any commutative ring, no extra hypothesis: `Juxtapose.extIndIndEquiv` is an isomorphism
      of `W_{a+c} ⊗ W_{b+d}`-modules
      `Ind_{a;c}(P_a ⊠ Q_c) ⊠ Ind_{b;d}(P_b ⊠ Q_d) ≅
      (W_{a+c} ⊗ W_{b+d}) e' ⊗_{(W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)} ((P_a ⊠ P_b) ⊠ (Q_c ⊠ Q_d))`,
      hence `Juxtapose.middleIndK0_extTensor`:
      `middleInd((x_a ⊠ x_b) ⊠ (y_c ⊠ y_d)) = (x_a · y_c) ⊠ (x_b · y_d)` in
      `K_0(W_{a+c} ⊗ W_{b+d})`. With the comparison map `ProjK0.extTensorHom`
      (`c` above, ungraded, `[P] ⊗ [Q] ↦ [P ⊠ Q]`) and the twisted product
      `ShuffleLayout.twistedMulK0`, `T_L((x_a ⊗ x_b) ⊗ (y_c ⊗ y_d)) =
      (x_a · y_c) ⊗ (x_b · y_d)` (with `castW`), one has
      `c(T_L(u ⊗ w)) = (Ind_{a;c} ⊗ Ind_{b;d}) ∘ (exchange) (c u ⊠ c w)`
      (`ShuffleLayout.extTensorHom_twistedMulK0`).
    * Under the explicit hypothesis `ProjK0.ExtTensorBijective` (the ungraded comparison
      `K_0(W_μ) ⊗_ℤ K_0(W_{μ'}) → K_0(W_μ ⊗ W_{μ'})` is bijective): `coproductK0 ν₁ ν₂`,
      `Δ_{ν₁,ν₂} = c⁻¹ ∘ resK0 : K_0(W_{ν₁+ν₂}) → K_0(W_{ν₁}) ⊗_ℤ K_0(W_{ν₂})`, and
      `exists_coproductK0_indK0_eq_sum`: under `Γ.Dagger`, `Γ.NoZeroLoops`, `Γ.Standing`,
      over any commutative ring, if the comparison is bijective for all pairs `(μ, μ')`, then
      for `ν₁ + ν₂ = ν' + ν''` there are layouts `L i`, one per shuffle type, with
      `Δ_{ν₁,ν₂}(x · y) = ∑_i T_{L i}(Δ_{a,b} x ⊗ Δ_{c,d} y)` for all `x`, `y` (ungraded).
      Bijectivity on ungraded projective `K_0` is not established in general; the graded
      comparison below does not discharge this ungraded hypothesis.
  * The graded Mackey formula, with the shift `-(μ · μ')` (`middleShift`) of the term of
    shuffle type `μ`, on graded `K_0`, over a field, under `Γ.Dagger`, `Γ.NoZeroLoops` and
    `Γ.Standing`: `exists_resK0_indK0_eq_sum_graded`, and in twisted form
    `exists_resK0_indK0_eq_sum_twistK0Graded` (next section). On `K_0 ⊗_{ℤ[q^±]} K_0`, under
    the route hypothesis `TensorK0Hyp` for every pair `(μ, μ')`:
    `exists_coproductK0_indK0_eq_sum_graded_of_tensorK0Hyp` (next section). For loop-free
    graphs, `GradingDatum.tensorK0Hyp` supplies this hypothesis and
    `exists_coproductK0_indK0_eq_sum_graded` has no separate `hT` assumption.

A0 centrality is available for the gallery algebra as `GalleryAlgebra.poly_mem_center`
(`WeightedKLR/CentralPolynomials.lean`), without additional graph hypotheses. Under
`Γ.Dagger`, `Γ.NoZeroLoops` and `Γ.Standing`, `CentralFinite.lean` proves finiteness over
the central colour-symmetric dots and finite-dimensionality of the augmentation quotient;
`Simple.lean` proves that graded simples of `W_ν` and `W_ν ⊗ W_μ` are finite-dimensional.
The corollaries `GradingDatum.finiteDimensional_top` and `finiteDimensional_top_tensor`
supply `fdA`, `fdB`, `fdC`, with no loop-freeness assumption. For loop-free graphs,
`AbsoluteSimple.lean` supplies scalar endomorphisms by the minimum-support
local-chart argument, and `TensorSimple.lean` assembles the complete `TensorK0Hyp`.
The original induction by single-colour right restrictions remains obstructed; the
replacement proof avoids it (see `thm-2-19-roadmap.md` and issue #289).

## Graded `K_0` (formalized)

Files `WeightedKLR/GradedK0/Grading.lean`, `Induction.lean`, `TensorK0.lean`,
`Restriction.lean`, `ResIndGrading.lean`, `ResIndChainGrading.lean`, `ResIndTwist.lean`,
`CoproductK0.lean`, and
`Algebra/Graded/K0Exact.lean`, `K0Filtration.lean`.

* `GradingDatum.resGProj`, `GradingDatum.resK0`, `resK0_of`: graded restriction from `W_ν`
  to `W_{ν'} ⊗ W_{ν''}` on graded finitely generated projective modules and the induced map
  on graded `K_0`, under `Γ.Dagger`, `Γ.NoZeroLoops` and `Γ.Standing`.
* `GalleryAlgebra.resIndFiltGrading`, `resIndSubquotientGrading` (with `iSup_*` and the
  projections): the steps of the Mackey filtration of `Res ∘ Ind` are spanned by homogeneous
  elements, so the steps and subquotients are graded.
* `Juxtapose.middleResIndGradedEquiv` (and the case `S = {μ ≤ c}`, `S' = {μ < c}`,
  `middleResIndGradedEquivIic`): the Mackey subquotient isomorphism is homogeneous of degree
  `middleShift` (in the normalization of this library, twice Webster's degree; it is
  `-(b · c)` in Webster's normalization).
* `Graded.K0.of_eq_add_of_exact`: over a field, `[P] = [M] + [Q]` in graded `K_0` for a
  short exact sequence of graded projective modules with degree-preserving maps.
* `Graded.K0.exists_of_eq_sum_of_chain`, `Graded.K0.exists_of_balancedTensor_eq_sum`: over a
  field, additivity of graded `K_0` along a chain of homogeneous submodules, and the class of
  `M ⊗_A N` for a graded bimodule `M` with a chain of homogeneous sub-bimodules whose
  successive quotients are graded bimodules `Y i` and a graded projective `N`:
  `[M ⊗_A N] = ∑_i [Y i ⊗_A N]`.
* `ResIndPiece.grading`, `GalleryAlgebra.resIndBimoduleGrading`: the pieces of the Mackey
  chain carry the middle grading shifted by `middleShift`, and `Res ∘ Ind` the grading of
  `W_ν`; all actions are graded and the steps of the chain are homogeneous
  (`resIndSubBimodule_isHomogeneous`). `Juxtapose.exists_middleResInd_gradedEquiv`: the
  bimodule isomorphism of `exists_middleResInd_equiv` is also a graded isomorphism.
* `GalleryAlgebra.exists_resInd_balancedTensor_eq_sum_graded`: over a field, the Mackey chain
  in graded `K_0`: `[Res Ind ⊗ N] = ∑_i [ResIndPiece (L i) ⊗ N]` for every graded projective
  `N` such that all `ResIndPiece (L i) ⊗ N` are finitely generated projective, one term per
  shuffle type. Hypotheses: those of the ungraded `exists_resInd_balancedTensor_eq_sum`
  (Webster, Theorem 2.8, for `ν`), with a field instead of a commutative ring.
* `resK0_map_indK0_eq` (`GradedK0/ResIndTensor.lean`): over a field, under `Γ.Dagger`,
  `Γ.NoZeroLoops` and `Γ.Standing`, `Res_{ν₁;ν₂}` of graded induction, transported along
  `castW`, is the class of the graded balanced tensor product of `Res Ind` with `P ⊠ P'`.
  `Graded.K0.map` (`Algebra/Graded/K0Map.lean`) transports graded `K_0` along a graded
  algebra isomorphism.
* `exists_resK0_indK0_eq_sum_graded` (`GradedK0/ResIndK0.lean`): over a field, under
  `Γ.Dagger`, `Γ.NoZeroLoops` and `Γ.Standing`, for `ν₁ + ν₂ = ν' + ν''`, one layout `L i` per
  shuffle type with
  `Res_{ν₁;ν₂}[Ind(P ⊠ P')] = ∑_i q^{middleShift (L i)} [ResIndPiece (L i) ⊗ (P ⊠ P')]`, the
  piece carrying the unshifted grading of the middle tensor product
  (`ResIndPiece.baseGrading`, `ResIndPiece.tensorGProj`). The shift is pulled out by
  `Graded.K0.of_balancedTensorGProj_shift_left`.
* `GradingDatum.middleIndK0`, `ResIndPiece.of_tensorGProj_eq_twistK0Graded`,
  `exists_resK0_indK0_eq_sum_twistK0Graded` (`GradedK0/ResIndTwist.lean`): same hypotheses.
  The graded piece `ResIndPiece L ⊗ (P ⊠ Q)` (unshifted grading) is, along
  `W_{a+c} ⊗ W_{b+d} ≅ W_{ν₁} ⊗ W_{ν₂}`, the graded induction from the middle parabolic of
  `Res_{a,b} P ⊠ Res_{c,d} Q`, with no further shift because `e = (ι_{a,b} ⊗ ι_{c,d})(1)` has
  degree `0`. Hence
  `Δ_{ν₁;ν₂}(x · y) = ∑_i q^{middleShift (L i)} (Ind_{a;c} ⊗ Ind_{b;d}) ∘ (exchange)
  (Δ_{a;b} x ⊠ Δ_{c;d} y)` for all `x`, `y` in graded `K_0`.
* `Juxtapose.middleIndExtIndEquiv`, `GradingDatum.middleIndGProjExtIndIso`,
  `GradingDatum.middleIndK0_extTensor` (`GradedK0/CoproductK0.lean`): the graded analogue of
  `Juxtapose.extIndIndEquiv`. Over any commutative ring,
  `(W_{a+c} ⊗ W_{b+d}) e' ⊗ ((P_a ⊠ P_b) ⊠ (Q_c ⊠ Q_d)) ≅ Ind(P_a ⊠ Q_c) ⊠ Ind(P_b ⊠ Q_d)`;
  over a field it preserves the gradings (no shift), so
  `middleInd ((x_a ⊠ x_b) ⊠ (y_c ⊠ y_d)) = (x_a · y_c) ⊠ (x_b · y_d)` in graded `K_0`. No
  hypothesis beyond those of graded induction.
* `GradingDatum.coproductK0`, `ShuffleLayout.twistedMulK0Graded`,
  `ShuffleLayout.k0TensorEquiv_twistedMulK0Graded`
  (`GradedK0/CoproductK0.lean`): over a field, `Δ_{ν₁,ν₂} = k0TensorEquiv⁻¹ ∘ resK0 :
  K_0(W_{ν₁+ν₂}) → K_0(W_{ν₁}) ⊗_{ℤ[q^±]} K_0(W_{ν₂})` and the twisted product
  `T_L((x_a ⊗ x_b) ⊗ (y_c ⊗ y_d)) = (x_a · y_c) ⊗ (x_b · y_d)`.
  `exists_coproductK0_indK0_eq_sum_graded_of_tensorK0Hyp` retains the general conditional
  formula under `Γ.Dagger`, `Γ.NoZeroLoops`, `Γ.Standing`, `HasGdim` for every
  `G.klrGrade μ`, and `TensorK0Hyp (G.klrGrade μ) (G.klrGrade μ')` for all pairs:
  `Δ_{ν₁,ν₂}(x · y) = ∑_i q^{middleShift (L i)} T_{L i}(Δ_{a,b} x ⊗ Δ_{c,d} y)`.
  `exists_coproductK0_indK0_eq_sum_graded` discharges the comparison for loop-free graphs
  using `GradingDatum.tensorK0Hyp G hD hS hne hl μ μ'`; it keeps the arbitrary grading
  datum `G` and its `HasGdim` assumptions and takes no extra `hT`. The loop-free conditions
  are distinct head and tail on every edge and `Γ.loop i = none`. Neither result asserts
  the quantum Serre relations, the map from `U_q^+`, or an antipode.

* `GradingDatum.instGradedAlgebraKlrGrade`: for every grading datum `G`, `W_ν` with
  `G.klrGrade ν` is a graded algebra (the corner of `A_ν` at the degree-zero idempotent
  `rankIdem`, `Graded.cornerGradedAlgebra`). Any commutative ring.
* `GalleryAlgebra.hasGdim_klrGrade` (and `hasGdim_grade` for `A_ν`): over a field, under
  `Γ.Dagger`, `Γ.NoZeroLoops` and `Γ.Standing`, the graded pieces of `W_ν` for the grading of
  the standing hypothesis are finite-dimensional and vanish in sufficiently negative degree
  (`Graded.HasGdim`). Proof: the homogeneous basis of Theorem 2.8 (`basisOfSegments`); dots
  have degree `2 d_i > 0` and there are finitely many pairs of chambers.
* `GradingDatum.indProj G P P'`: for graded finitely generated projective `P`, `P'`,
  `Ind (P ⊠ P') = W_{ν'+ν''} e_{ν';ν''} ⊗_{W_{ν'} ⊗ W_{ν''}} (P ⊠ P')` is a graded finitely
  generated projective `W_{ν'+ν''}`-module, with no grading shift. It respects isomorphisms,
  direct sums and shifts in each variable (`indProjCongr`, `indProjProdLeft`,
  `indProjProdRight`, `indProjShiftLeft`, `indProjShiftRight`). Any commutative ring.
* `GradingDatum.indK0`, `GradingDatum.indK0Tensor`: the product
  `K_0(W_{ν'}) ⊗_{ℤ[q^±]} K_0(W_{ν''}) → K_0(W_{ν'+ν''})`, `[P] ⊗ [P'] ↦ [Ind (P ⊠ P')]`, on
  graded `K_0`, `ℤ[q^±]`-bilinear. No hypothesis.
* `GradingDatum.k0TensorEquiv`: over a field, given `HasGdim` for `W_{ν'}` and `W_{ν''}`
  and a value of `TensorK0Hyp (G.klrGrade ν') (G.klrGrade ν'')`, the comparison
  `K_0(W_{ν'}) ⊗_{ℤ[q^±]} K_0(W_{ν''}) ≅ K_0(W_{ν'} ⊗ W_{ν''})`, `x ⊗ y ↦ x ⊠ y`
  (`k0TensorEquiv_tmul`). `TensorK0Hyp` asks for finite-dimensional graded simple tops of
  both factors (`fdA`, `fdB`) and their tensor product (`fdC`), and scalar endomorphisms
  for the tops of both factors (`endA`, `endB`). Webster uses this identification without
  supplying those inputs. `CentralFinite.lean` and `Simple.lean` provide the augmentation
  argument for A0. `AbsoluteSimple.lean` proves the scalar statement for loop-free graphs
  over any field, with arbitrary standing polynomials, cycles and colour multiplicities.
  Its intermediate ungraded theorem assumes finite dimension and nilpotent dots; A0 and
  positive dot degrees discharge these assumptions for graded simples.
* `GradingDatum.wt_pos_of_hasGdim` (`SimpleGrading.lean`) shows that any grading datum `G`
  with locally finite, bounded-below `G.klrGrade ν` has positive dot degrees. Independent
  powers of a dot exclude degree zero; the lower bound excludes negative degree. Thus
  the augmentation and nilpotence arguments also apply to the arbitrary admissible
  grading datum in the coproduct statement.
* `GradingDatum.tensorK0Hyp G hD hS hne hl ν μ` (`TensorSimple.lean`) supplies all five
  fields for any two weights of a loop-free graph, under `HasGdim` for the chosen
  grading. It uses `GradingDatum.exists_eq_smul_of_isGradedSimple_of_hasGdim` for the
  absolute-irreducibility fields. The earlier multiplicity-free comparison remains a
  separate useful result allowing loops; the new result removes restrictions on
  colour multiplicities for loop-free graphs.

## What needs a field, and why

Reading `Δ` as a map `K → K ⊗ K` needs `c` to be an isomorphism. Over a general commutative
ring it is not.

* For `ν' = ν'' = 0` we have `W_0 = k`. Then `c` is the multiplication map
  `K_0(k) ⊗ K_0(k) → K_0(k)`, with `q^±` adjoined.
* Take `k = ℤ × ℤ` and the idempotent `e = (1, 0)`. Then `[ke] ⊗ [k(1 - e)]` is nonzero, but it
  maps to `[ke ⊗_k k(1 - e)] = 0`.
* So the degree-zero part of `K` is `K_0(k)[q^±]`, not `ℤ[q^±]`, and the unit and counit are not
  those of a bialgebra over `ℤ[q^±]`.

This is recorded as an erratum in the README.

The corrected statement takes `k` to be a field, the setting of KL I. The graded
comparison is supplied for loop-free graphs under the standing and (†) hypotheses.
Its two inputs are:

1. **A grading of `W_ν`.** The graded pieces are finite-dimensional and vanish in
   sufficiently negative degree (`Graded.HasGdim`). This is proved for the standing
   grading by `GalleryAlgebra.hasGdim_klrGrade`; the coproduct theorem also accepts an
   arbitrary grading datum `G` with these instances. The graded Krull–Schmidt theorem
   makes graded `K_0` free over `ℤ[q^±]` on indecomposable graded projectives.
2. **Finite-dimensional, absolutely irreducible graded simple tops.** These are the
   fields of `KLR.TensorK0Hyp`. A0 supplies finite dimension. The local-chart replacement
   proof supplies scalar endomorphisms for loop-free weighted KLR graphs over any field;
   algebraic closure, a forest assumption and multiplicity-free weights are unnecessary.

The proof of the second input chooses a minimum squared-norm point in the closed support
of a simple module. The incident chambers define a zero-weight local graph and a chart
whose unit is the incident rank-ordered star idempotent. Stabilizing terms of Webster's
basis lift to this chart. A moving permutation gives a strictly smaller midpoint, so an
adapted basis gallery passes through an unsupported chamber and annihilates the module.
Consequently the local algebra acts as the entire star corner. Its nonzero unit-fixed
restriction is simple with nilpotent dots. The local zero-weight algebra is a full corner
of an ordinary KLR algebra, so KL I arXiv:0803.4121v2, §3.2, Corollary 3.19 detects scalar
endomorphisms. `AbsoluteSimple.lean` and `TensorSimple.lean` assemble these inputs.

Thus `exists_coproductK0_indK0_eq_sum_graded` proves the graded coproduct Mackey formula
for loop-free graphs without a separate tensor-comparison hypothesis. The conditional
statement `exists_coproductK0_indK0_eq_sum_graded_of_tensorK0Hyp` remains available for graphs
with loops or any independently supplied comparison. The obstruction to the earlier
right-restriction induction is preserved in `thm-2-19-roadmap.md`; it does not affect this
local proof. Quantum Serre relations, the map from `U_q^+`, and the antipode remain roadmap
items B, C and D.

## Restriction preserves finitely generated projectives

`Res_{ν';ν''} L = e_{ν';ν''} L`, a module over `W_{ν'} ⊗ W_{ν''}` through
`ι = Juxtapose.inductionRingHom`. The proof follows KL I Prop. 2.16, as Webster's proof of
Theorem 2.19 indicates (`WeightedKLR/Induction/Restriction.lean`).

* `InductionAlong.Res.projective_of_regular`, `InductionAlong.Res.finite_of_regular`: it suffices
  that `Res W_ν = e_{ν';ν''} W_ν` is finitely generated projective, since `Res` commutes with
  finite direct sums and retracts.
* `GalleryAlgebra.rowEquiv`: the right module `W_ν e_{ν';ν''}` is a finite direct sum of
  modules `f (W_{ν'} ⊗ W_{ν''})` with `f` idempotent, `x ↦ Σ c_u ι(x_u)`, assembled from the
  parabolic decomposition `GalleryAlgebra.parabolicCornerEquiv`. Hence `corner_projective` and
  `corner_finite`.
* `InductionAlong.Res.projective_of_corner`: the vertical reflection `reflectW`, an
  anti-involution intertwining `ι` with `ρ ⊗ ρ` (`Juxtapose.reflectW_inductionMap`,
  `Juxtapose.reflectTensorEquiv`), turns the right module `W_ν e` into the left module `e W_ν`.

Hypotheses of `Juxtapose.res_projective`: `Γ.Standing` (§2.1 of the source; it contains the
symmetry of the loop polynomials, the source's reading of the degree-0 loop relation, used by
the reflection), `Γ.Dagger` (the source's condition (†)) and `Γ.NoZeroLoops` (an encoding
convention of the library), the hypotheses under which the gallery basis is formalized.

### The ungraded comparison map

`coproductK0` and `exists_coproductK0_indK0_eq_sum` use the ungraded `K_0` of all finitely
generated projective modules, and assume that `c` is bijective there
(`ProjK0.ExtTensorBijective`). This is not proved, and no result in the library or in Mathlib
gives it, even over an algebraically closed field.

* `W_ν` is infinite-dimensional, so Krull–Schmidt for finite-dimensional algebras does not
  apply, and the graded Krull–Schmidt theorem (available for the grading of the standing
  hypothesis, `GalleryAlgebra.hasGdim_klrGrade`) does not apply to ungraded modules.
* `KLR.TensorK0Hyp.extTensorEquiv` concerns the graded `K_0` of graded projective modules. A
  finitely generated projective `W_ν`-module need not be gradable, and no comparison between
  the ungraded `K_0` and the graded `K_0` (modulo `q = 1`) is formalized or given in the source.
* Already for `W_0 = k[x]`-type factors, ungraded `K_0` is controlled by results such as
  Quillen–Suslin, which are not in Mathlib.

So the ungraded `Δ` with values in `K_0(W_{ν₁}) ⊗ K_0(W_{ν₂})` remains formalized under
`ProjK0.ExtTensorBijective`. The completed graded comparison for loop-free graphs does not
remove that ungraded hypothesis: it concerns graded projectives and cannot identify their
classes with all ungraded projectives. The graded route supplies the coproduct and its Mackey
formula without an extra comparison assumption in the loop-free field case. Extending the
ungraded comparison would require a separate argument and maintainer approval.
