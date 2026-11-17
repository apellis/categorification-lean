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
      The bijectivity hypothesis is not proved for any weighted KLR algebra; see the next
      section.
  * Open: the graded statement, with the shift `-(μ · μ')` of the term of shuffle type `μ`.
    It needs a grading of the pieces compatible with the filtration
    (`Juxtapose.segDeg_chamber_swapChamber` computes the degree of the exchange), a graded
    `K_0` of `W_ν` (no `Graded.HasGdim` instance for `W_ν` exists), and graded versions of
    `ProjK0.extTensor`, `resK0` and `middleIndK0`. None of these is formalized.

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

The corrected statement takes `k` to be a field, the setting of KL I. Over a field, `c` is an
isomorphism given the following inputs.

1. **A grading of `W_ν`.** It must have finite-dimensional graded pieces, vanishing in
   sufficiently negative degree (`Graded.HasGdim`). The weighted grading is
   `WeightedKLR/Grading.lean`, but no `HasGdim` instance for `W_ν` exists yet.
   Given the instance, the graded Krull–Schmidt theorem
   (`Categorification/Algebra/Graded/KrullSchmidt.lean`, `KrullSchmidtUnique.lean`) makes the
   graded `K_0(W_ν)` free over `ℤ[q^±]` on the classes of the indecomposable graded
   projectives. No graded `K_0` of `W_ν` has been set up yet.
2. **Absolute irreducibility.** Every graded simple `W_ν`-module must have endomorphism ring
   `k`. Then the indecomposable graded projectives of `W_{ν'} ⊗ W_{ν''}` are exactly the
   `P ⊠ Q`. This is the content of `KLR.TensorK0Hyp` and `KLR.TensorK0Hyp.extTensorEquiv`.
   These are stated for graded algebras over a field and apply to `W_ν` once (1) is in place.
3. **When (2) is known.** It holds over an algebraically closed field.
   * For KLR algebras over any field, (2) is the corollary on absolute irreducibility in
     KL I §3.2. That corollary uses the independence of characters of simples, proved through
     the surjectivity of `γ`.
   * The source gives no argument for weighted KLR algebras. Over a field that is not
     algebraically closed, (2) is therefore an extra hypothesis of the corrected statement until
     it is proved.

In short: over a field, the missing formal inputs are a `HasGdim` structure on `W_ν`, the graded
`K_0` of `W_ν`, and the Mackey identity in graded
`K_0`. The comparison then follows from `KLR.TensorK0Hyp.extTensorEquiv`, under hypothesis (2).

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

* `W_ν` is infinite-dimensional and its grading is not bounded below in general, so neither
  Krull–Schmidt for finite-dimensional algebras nor the graded Krull–Schmidt theorem applies
  to ungraded modules.
* `KLR.TensorK0Hyp.extTensorEquiv` concerns the graded `K_0` of graded projective modules. A
  finitely generated projective `W_ν`-module need not be gradable, and no comparison between
  the ungraded `K_0` and the graded `K_0` (modulo `q = 1`) is formalized or given in the source.
* Already for `W_0 = k[x]`-type factors, ungraded `K_0` is controlled by results such as
  Quillen–Suslin, which are not in Mathlib.

So `Δ` with values in `K_0(W_{ν₁}) ⊗ K_0(W_{ν₂})` is formalized only under this hypothesis.
The options for the maintainer: (a) the graded route, with a `HasGdim` structure on `W_ν`, a
graded `K_0` of `W_ν`, the graded Mackey identity and absolute irreducibility (items 1–3
above), where `KLR.TensorK0Hyp.extTensorEquiv` gives the comparison; (b) keep
`ProjK0.ExtTensorBijective` as an explicit hypothesis of the ungraded statement (current
state); (c) new theory for the ungraded comparison, which needs the maintainer's approval.
