/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.StarDualTensorCurry
import Categorification.Algebra.DerivedTensorOrdinaryLinear
import Categorification.WeightedKLR.Rigidity.SMoveReflectFlip
import Categorification.WeightedKLR.Rigidity.SMoveStdLayerSeparation
import Categorification.WeightedKLR.Rigidity.RigidityExtLastTerm
import Categorification.WeightedKLR.Rigidity.RigidityExtTorShift

/-!
# The diagonal `Tor₀` of the S-move

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), step R5 (iii). On the diagonal the pairing of the S-move is
`Tor₀(M^r, M) = M^r ⊗_{T} M` for the last term `M = S(T^{λ'} e(t) ⊠ Y₀)` of the resolution of
Proposition 7.8, where `M^r` is the reflection of `M` used in the Tor lemmas (`reflectOne`).

The reflection is restriction along the corner flip, which at the trivial braid is the
horizontal reflection defining the star duals of Proposition 7.8
(`cornerFlipTensorEquiv_one_apply`). So currying (`starDualHomCurryEquiv`) gives
`dim (M^r ⊗_T Y) = dim Hom(Y, M^⋆)` (`finrank_tensorProductOver_reflectOne`), and the second
clause of Proposition 7.8 (`exists_stdResolution_last`, `dim Hom(M, M^⋆) = 1`) gives
`dim Tor₀(M^r, M) = 1`, for the ordinary tensor product and for the degree-zero homology of the
derived tensor product.

## Main results

* `finrank_tensorProductOver_reflectOne`: `dim (M^r ⊗_T Y) = dim Hom(Y, M^⋆)`, and the derived
  form `finrank_derivedTensorHomology_reflectOne`.
* `finrank_tensorProductOver_reflectOne_last`: `dim (M^r ⊗_T M) = 1` for the last term.
* `finrank_derivedTensorHomology_reflectOne_last`: `dim Tor₀(M^r, M) = 1`, `Tor₀` the degree-zero
  homology of the derived tensor product.
-/

noncomputable section

universe w w'

namespace Categorification.Stendhal

open CategoryTheory Abelian KLR KLRAlgebra Equiv MulOpposite BraidedStendhalAlgebra
open DG DG.DerivedCategory
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q) {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "σT" => (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν : T ≃+* Tᵐᵒᵖ)

/-- **`Tor₀` against the reflection is dual to `Hom` into the star dual** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22): `dim (M^r ⊗_T Y) = dim Hom(Y, M^⋆)`. -/
theorem finrank_tensorProductOver_reflectOne (M Y : ModuleCat.{0} T) :
    Module.finrank k (TensorProductOver T ((reflectOne Q Λ hQ hρ).obj M) Y) =
      Module.finrank k (Y ⟶ starDualObj k σT M) :=
  finrank_tensorProductOver_restrictScalars σT
    (cornerFlipTensorEquiv (Λ := Λ) hρ hQ 1).toRingHom
    (fun a => cornerFlipTensorEquiv_one_apply hρ hQ (op a))
    (fun c => tensorFlip_algebraMap' c) M Y

/-- **`Tor₀` against the reflection, derived form** (Webster, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22): the degree-zero homology of `M^r ⊗ᴸ_T Y` has the dimension of
`Hom(Y, M^⋆)`. -/
theorem finrank_derivedTensorHomology_reflectOne [HasDerivedCategory.{w', 0} T]
    [HasDerivedCategory.{w', 0} k] (M Y : ModuleCat.{0} T) :
    Module.finrank k (derivedTensorHomology.{w'} k ((reflectOne Q Λ hQ hρ).obj M) 0 Y) =
      Module.finrank k (Y ⟶ starDualObj k σT M) :=
  (ambientDerivedTensorH0Equiv (k := k) (A := T) (N := ((reflectOne Q Λ hQ hρ).obj M))
    Y).finrank_eq.trans
    (finrank_tensorProductOver_reflectOne Q Λ hQ hρ M Y)

section Last

local notation "old" => Λ ∘ Fin.castSucc
local notation "aΛ" => fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last ℓ) j
local notation "Cyc" => CycKLR k Q (aΛ)

variable {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
  [HasExt.{w} (ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))]

include hR in
/-- **The diagonal `Tor₀` is one-dimensional** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22, gap (c), step R5 (iii)), for the ordinary tensor product: under the
hypotheses of the second clause of Proposition 7.8 (`exists_stdResolution_last`, for Rouquier
`Q`, where the route hypothesis of Proposition 7.6 holds by `allFiniteDeltaInjective_of_rouquier`),
the last term `M = S(T^{λ'} e(t) ⊠ Y₀)` has
`dim (M^r ⊗_T M) = 1`, `M^r` its reflection. -/
theorem finrank_tensorProductOver_reflectOne_last (X : ModuleCat.{0} T) [FiniteDimensional k X]
    (hX : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : X, loadingIdem Q Λ s hs • x = 0)
    (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight ℓ 0)) (ht : IsRedOrdered t)
    (het : TensorProductAlgebra.mk Q (old) 0 (StendhalAlgebra.e t ht) = 1)
    (Y₀ : ModuleCat.{0} (Cyc (wordWt u 0)))
    (hss : ∀ (M : Type) [AddCommGroup M] [Module (Cyc (wordWt u 0)) M]
      [Module.Finite (Cyc (wordWt u 0)) M],
      ∃ n : ℕ, Nonempty (M ≃ₗ[Cyc (wordWt u 0)] (Fin n → Y₀)))
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (ι : J → (Y₀ →ₗ[Cyc (wordWt u 0)] cycWord Q Λ u))
    (π : J → (cycWord Q Λ u →ₗ[Cyc (wordWt u 0)] Y₀))
    (hιπ : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)
    (htot : ∑ j, (ι j).comp (π j) = LinearMap.id)
    (htop : Module.finrank k (Ext.{w} (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) X
      (Multiset.card ν)) = 1) :
    Module.finrank k (TensorProductOver T
      ((reflectOne Q Λ hQ hρ).obj (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀))
      (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀)) = 1 := by
  have hall : AllFiniteDeltaInjective Q Λ hQ := by
    convert allFiniteDeltaInjective_of_rouquier (Λ := Λ) hR hQ
  obtain ⟨-, -, -, -, -, -, -, h⟩ := exists_stdResolution_last.{w} Q Λ hQ hR hall X hX u h₀ t
    ht het Y₀ hss ι π hιπ htot htop
  rw [finrank_tensorProductOver_reflectOne]
  exact h

include hR in
/-- **The diagonal `Tor₀` is one-dimensional, derived form** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.22, gap (c), step R5 (iii)): under the hypotheses of the second clause of
Proposition 7.8 (`exists_stdResolution_last`, for Rouquier `Q`, where the route hypothesis of
Proposition 7.6 holds by `allFiniteDeltaInjective_of_rouquier`), the last term
`M = S(T^{λ'} e(t) ⊠ Y₀)` has `dim Tor₀(M^r, M) = 1`, `Tor₀` the degree-zero homology of
`M^r ⊗ᴸ_T M`. -/
theorem finrank_derivedTensorHomology_reflectOne_last [HasDerivedCategory.{w', 0} T]
    [HasDerivedCategory.{w', 0} k] (X : ModuleCat.{0} T) [FiniteDimensional k X]
    (hX : ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : IsRedOrdered s), ¬HasLastRed s →
      ∀ x : X, loadingIdem Q Λ s hs • x = 0)
    (u : List I) (h₀ : 0 + wordWt u 0 = ν) (t : Seq (stendhalWeight ℓ 0)) (ht : IsRedOrdered t)
    (het : TensorProductAlgebra.mk Q (old) 0 (StendhalAlgebra.e t ht) = 1)
    (Y₀ : ModuleCat.{0} (Cyc (wordWt u 0)))
    (hss : ∀ (M : Type) [AddCommGroup M] [Module (Cyc (wordWt u 0)) M]
      [Module.Finite (Cyc (wordWt u 0)) M],
      ∃ n : ℕ, Nonempty (M ≃ₗ[Cyc (wordWt u 0)] (Fin n → Y₀)))
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (ι : J → (Y₀ →ₗ[Cyc (wordWt u 0)] cycWord Q Λ u))
    (π : J → (cycWord Q Λ u →ₗ[Cyc (wordWt u 0)] Y₀))
    (hιπ : ∀ i j, (π j).comp (ι i) = if i = j then LinearMap.id else 0)
    (htot : ∑ j, (ι j).comp (π j) = LinearMap.id)
    (htop : Module.finrank k (Ext.{w} (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀) X
      (Multiset.card ν)) = 1) :
    Module.finrank k (derivedTensorHomology.{w'} k
      ((reflectOne Q Λ hQ hρ).obj (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀)) 0
      (tensorStd Q Λ hQ h₀ (oldProj Q Λ 0 t ht) Y₀)) = 1 := by
  have hall : AllFiniteDeltaInjective Q Λ hQ := by
    convert allFiniteDeltaInjective_of_rouquier (Λ := Λ) hR hQ
  obtain ⟨-, -, -, -, -, -, -, h⟩ := exists_stdResolution_last.{w} Q Λ hQ hR hall X hX u h₀ t
    ht het Y₀ hss ι π hιπ htot htop
  rw [finrank_derivedTensorHomology_reflectOne]
  exact h

end Last

end Categorification.Stendhal
