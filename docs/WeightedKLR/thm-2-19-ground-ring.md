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
