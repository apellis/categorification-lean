/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorSyzygyChain
import Categorification.WeightedKLR.Rigidity.SMoveStandardTor

/-!
# The Tor computation in the proof of the S-move

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22. After the reduction to `λ₁ = λ₂ = ∅`, the S-move reduces to computing
`X ⊗ᴸ Y` for `X = 𝕊^{λ;λ*,λ}(P_∅ ⊠ L)` and `Y = 𝕊^{λ,λ*;λ}(L̇ ⊠ Ṗ_∅)`. Webster resolves both
factors by Proposition 7.8 and uses the spectral sequence of the tensor product, whose `E²` terms
`Tor^k(𝕊(P_∅ ⊠ M_i), 𝕊(Ṁ_j ⊠ Ṗ_∅))` vanish unless `i = 0`, `j = 2ρ^∨` and `k = 0`.

Here the spectral sequence is replaced by dévissage along the two resolutions
(`nonempty_linearEquiv_derivedTensorHomology_of_syzygyChains`), and the vanishing of the `E²`
terms is proved from standard filtrations of the resolution terms: Tor between loading
standards vanishes in every degree when the black counts differ
(`isZero_derivedTensorHomology_of_loadingFiltrations`) and in nonzero degrees always
(`isZero_derivedTensorHomology_of_loadingFiltrations_of_ne_zero`). The resolutions and the
standard filtrations of their terms are inputs, so that Proposition 7.8 (not yet formalized) and
the identification of `𝕊(P_∅ ⊠ S^{κ_j}_𝐢)` with a loading standard can be supplied.

## Main results

* `SMove.isZero_derivedTensorHomology_of_loadingResolutions`: `X ⊗ᴸ Y` is concentrated in
  degree `-(i₀ + j₀)`.
* `SMove.nonempty_addEquiv_tensorProductOver_of_loadingResolutions`: there it is
  `M_{i₀} ⊗ N_{j₀}`.
* `coefficientTensor`, `isZero_derivedTensorHomology_coefficientModule`: the `ℤ`-module
  structure of a bundled coefficient.
-/

noncomputable section

namespace Categorification

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

universe w

/-- The derived tensor product with a bundled coefficient over `ℤ`, for its bundled `ℤ`-module
structure (`derivedTensor` would infer the canonical one, which is equal but not
definitionally). -/
abbrev coefficientTensor {B : Type} [Ring B] [HasDerivedCategory.{w, 0} ℤ]
    [HasDerivedCategory.{w, 0} B] (M : CoefficientModule ℤ B) :
    DerivedCategory.{w, 0} B ⥤ DerivedCategory.{w, 0} ℤ :=
  @derivedTensor.{w, 0} ℤ B _ _ M _ M.isModule _ M.isSMulCommClass _ _

/-- The derived tensor cohomology over `ℤ` of a bundled coefficient does not depend on whether
its `ℤ`-module structure is the bundled one or the canonical one. -/
theorem isZero_derivedTensorHomology_coefficientModule {B : Type} [Ring B]
    [HasDerivedCategory.{w, 0} ℤ] [HasDerivedCategory.{w, 0} B] (M : CoefficientModule ℤ B)
    (Y : DerivedCategory.{w, 0} B) (n : ℤ)
    (h : IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
      ((derivedTensor.{w} ℤ B (ModuleCat.of Bᵐᵒᵖ M)).obj Y))) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj
      ((coefficientTensor.{w} M).obj Y)) := by
  rcases M with @⟨carrier, i₁, i₂, i₃, i₄⟩
  obtain rfl : i₂ = AddCommGroup.toIntModule carrier := Subsingleton.elim _ _
  exact h

namespace Stendhal.BraidedStendhalAlgebra.SMove

open KLR Equiv CornerEndomorphism

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ) (hQ : KLRSymm Q) (σ : Perm (Fin ℓ))

local notation "κ" => List.map σ (List.finRange ℓ)
local notation "C" => ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ
local notation "μ" => stendhalWeight ℓ ν

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable [HasDerivedCategory.{w, 0}
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      (List.map σ (List.finRange ℓ)))]
  [HasDerivedCategory.{w, 0} ℤ]
  (D : ModuleFiltration.OrderedStandardCovers
    (fun s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s} =>
      ModuleCat.of (TensorProductAlgebra k Q (Λ ∘ σ) ν) (leftStandard Q (Λ ∘ σ) s.1 s.2))
    (fun s => seqIdem Q (Λ ∘ σ) s.1 s.2) (fun s t => StendhalLT s.1 t.1))
  (X : CoefficientSyzygyChain ℤ
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      (List.map σ (List.finRange ℓ))))
  (Y : ModuleSyzygyChain
    (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      (List.map σ (List.finRange ℓ)))) {i₀ j₀ : ℕ}
  (hi₀ : i₀ ≤ X.length) (hj₀ : j₀ ≤ Y.length)
  (lab lab' : ℕ → List {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s})
  (hX : ∀ i ≤ X.length, ModuleFiltration.HasFiltration
    (fun t : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s} =>
    ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      (List.map σ (List.finRange ℓ)))ᵐᵒᵖ
      (ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) (Seq.redPerm σ t.1)
        (List.map σ (List.finRange ℓ))))
    (lab i) (ModuleCat.of (ViolOrderCorner (k := k) (Q := Q) (Λ := Λ) (ν := ν)
      (List.map σ (List.finRange ℓ)))ᵐᵒᵖ
      (X.term i)))
  (hY : ∀ j ≤ Y.length, ModuleFiltration.HasFiltration
    (fun s : {s : Seq (stendhalWeight ℓ ν) // IsRedOrdered s} =>
    ReflectedLoadingStandard (k := k) (Q := Q) (Λ := Λ) σ s.1) (lab' j) (Y.term j))
  (hsep : ∀ i ≤ X.length, ∀ j ≤ Y.length, (i ≠ i₀ ∨ j ≠ j₀) →
    ∀ t ∈ lab i, ∀ s ∈ lab' j, ¬ (StendhalLE s.1 t.1 ∧ StendhalLE t.1 s.1))

include hρ hQ D hi₀ hj₀ hX hY hsep in
/-- **The Tor computation of the S-move: concentration** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.22, with dévissage in place of the spectral sequence). Let `X` and `Y`
have finite resolutions by modules `M_i`, `N_j` with filtrations by loading standards and
reflected loading standards, such that for `(i, j) ≠ (i₀, j₀)` no label of `M_i` has the black
counts of a label of `N_j`. Then `X ⊗ᴸ Y` has cohomology only in degree `-(i₀ + j₀)`. -/
theorem isZero_derivedTensorHomology_of_loadingResolutions (n : ℤ)
    (hn : n ≠ -((i₀ + j₀ : ℕ) : ℤ)) :
    IsZero ((homologyFunctor (A := ℤ) ℤ n).obj ((coefficientTensor.{w} (X.syz 0)).obj
      (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor C).obj (Y.syz 0))))) :=
  isZero_derivedTensorHomology_of_syzygyChains X Y hi₀ hj₀
    (fun i hi j hj hij n => isZero_derivedTensorHomology_coefficientModule _ _ n
      (isZero_derivedTensorHomology_of_loadingFiltrations hρ hQ σ D (hX i hi) (hY j hj)
        (hsep i hi j hj hij) n))
    (fun m hm => isZero_derivedTensorHomology_coefficientModule _ _ m
      (isZero_derivedTensorHomology_of_loadingFiltrations_of_ne_zero hρ hQ σ D (hX i₀ hi₀)
        (hY j₀ hj₀) m hm)) n hn

include hρ hQ D hi₀ hj₀ hX hY hsep in
/-- **The Tor computation of the S-move: the surviving term** (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.22): under the hypotheses of
`isZero_derivedTensorHomology_of_loadingResolutions`, the cohomology of `X ⊗ᴸ Y` in degree
`-(i₀ + j₀)` is the ordinary tensor product `M_{i₀} ⊗ N_{j₀}`. In the S-move, `i₀ = 0`,
`j₀ = 2ρ^∨(λ)`, and `M_0 ⊗ N_{2ρ^∨}` is the three-strand corner. -/
theorem nonempty_addEquiv_tensorProductOver_of_loadingResolutions :
    Nonempty ((homologyFunctor (A := ℤ) ℤ (-((i₀ + j₀ : ℕ) : ℤ))).obj
        ((coefficientTensor.{w} (X.syz 0)).obj
          (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor C).obj (Y.syz 0)))) ≃+
      TensorProductOver C (X.term i₀) (Y.term j₀)) := by
  exact nonempty_addEquiv_tensorProductOver_of_syzygyChains X Y hi₀ hj₀
    (fun i hi j hj hij n => isZero_derivedTensorHomology_coefficientModule _ _ n
      (isZero_derivedTensorHomology_of_loadingFiltrations hρ hQ σ D (hX i hi) (hY j hj)
        (hsep i hi j hj hij) n))

end Stendhal.BraidedStendhalAlgebra.SMove

end Categorification
