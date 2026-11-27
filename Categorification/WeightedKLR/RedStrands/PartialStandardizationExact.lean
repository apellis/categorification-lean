/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationDescent
import Categorification.WeightedKLR.RedStrands.ParabolicStandardExact

/-!
# Exactness of partial standardization at a cut

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5,
Proposition 5.7, for the partial standardization `𝕊^{λ_1…λ_a; λ_{a+1}…λ_{a+r}}` at a cut
(`Stendhal.CutStandard`): a map of modules over the factor algebras induces a map of partial
standardizations, linear over `T^λ(θ + β)`, and partial standardization is exact. Webster states
Proposition 5.7 for the functor of Definition 5.4 (all blocks singletons); the argument, that
induction is exact and the ordered quotient is the image of an idempotent, applies verbatim.

## Main definitions

* `Stendhal.cutStandardMap`: the map of partial standardizations induced by a module map.

## Main results

* `Stendhal.cutStandardMap_action`: it is linear over `T^λ(θ + β)`.
* `Stendhal.cutStandardMap_exact`, `cutStandardMap_injective`, `cutStandardMap_surjective`:
  partial standardization at a cut is exact.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)
local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ
local notation "D" => cutFactorAlgebra Q Λ θ β
local notation "B" => TensorKLR S α δ
local notation "T" => TensorProductAlgebra k Q Λ (θ + β)
local notation "F" => cutOrderedLoadings (a := a) (r := r) θ β

variable {N N' N'' : Type*}
  [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]
  [AddCommGroup N'] [Module k N'] [Module (cutFactorAlgebra Q Λ θ β) N']
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N']
  [AddCommGroup N''] [Module k N''] [Module (cutFactorAlgebra Q Λ θ β) N'']
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N'']

/-- A map of modules over the factor algebras, as a map of their restrictions along the
affine quotient. -/
def cutInputHom (g : N →ₗ[D] N') : CutInput Q Λ θ β N →ₗ[B] CutInput Q Λ θ β N' where
  toFun n := (g n : N')
  map_add' := g.map_add
  map_smul' t n := g.map_smul (cutInputMap Q Λ θ β t) n

/-- The affine induction of a map of modules over the factor algebras. -/
def cutShuffleMap (g : N →ₗ[D] N') :
    CutShuffle Q Λ θ β N →ₗ[KLRAlgebra k S (α + δ)] CutShuffle Q Λ θ β N' :=
  BalancedTensor.mapRight (cutInputHom Q Λ θ β g)

theorem cutShuffleMap_eSum (g : N →ₗ[D] N') (y : CutShuffle Q Λ θ β N) :
    cutShuffleAction Q Λ θ β N' (eSum S F) (cutShuffleMap Q Λ θ β g y) =
      cutShuffleMap Q Λ θ β g (cutShuffleAction Q Λ θ β N (eSum S F) y) :=
  ((cutShuffleMap Q Λ θ β g).map_smul _ y).symm

/-- **The map of partial standardizations** induced by a map of modules over the factor
algebras. -/
def cutStandardMap (g : N →ₗ[D] N') : CutStandard Q Λ θ β N →ₗ[k] CutStandard Q Λ θ β N' :=
  kerQuotientMap ((cutShuffleMap Q Λ θ β g).restrictScalars k) (cutShuffleMap_eSum Q Λ θ β g)

theorem cutStandardMap_mk (g : N →ₗ[D] N') (y : CutShuffle Q Λ θ β N) :
    cutStandardMap Q Λ θ β g (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (cutShuffleMap Q Λ θ β g y) := rfl

variable (hQ : KLRSymm Q)

/-- Every element of the tensor product algebra comes from the affine KLR algebra. -/
theorem cutStandardAffine_surjective (t : T) :
    ∃ z : KLRAlgebra k S (α + δ), TensorProductAlgebra.mk Q Λ (θ + β)
      (orderProjection Q Λ (θ + β) (StendhalAlgebraAllOrders.ofKLR k Q Λ (θ + β)
        (castKLR S (cutInputWeights_add (a := a) (r := r) θ β) z))) = t := by
  obtain ⟨c, rfl⟩ := (show Function.Surjective (TensorProductAlgebra.mk Q Λ (θ + β)) from
    RingCon.mkₐ_surjective _) t
  obtain ⟨b, rfl⟩ := orderProjection_surjective Q Λ (θ + β) c
  obtain ⟨z', rfl⟩ := StendhalAlgebraAllOrders.ofKLR_surjective b
  obtain ⟨z, rfl⟩ := (castKLR S (cutInputWeights_add (a := a) (r := r) θ β)).surjective z'
  exact ⟨z, rfl⟩

include hQ in
/-- The map of partial standardizations is linear over the tensor product algebra. -/
theorem cutStandardMap_action (g : N →ₗ[D] N') (t : T) (z : CutStandard Q Λ θ β N) :
    cutStandardMap Q Λ θ β g (cutStandardAction Q Λ θ β N hQ t z) =
      cutStandardAction Q Λ θ β N' hQ t (cutStandardMap Q Λ θ β g z) := by
  obtain ⟨c, rfl⟩ := cutStandardAffine_surjective Q Λ θ β t
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  rw [cutStandardAction_affine, cutStandardAction_affine]
  exact congrArg Submodule.Quotient.mk ((cutShuffleMap Q Λ θ β g).map_smul c y)

include hQ in
/-- **Partial standardization at a cut is exact** (Webster, arXiv:1309.3796v3,
Proposition 5.7, for the partial standardization): a sequence `N → N' → N''` of modules over
the factor algebras exact at `N'` gives a sequence of partial standardizations exact at the
middle. -/
theorem cutStandardMap_exact (f : N →ₗ[D] N') (g : N' →ₗ[D] N'') (h : Function.Exact f g) :
    Function.Exact (cutStandardMap Q Λ θ β f) (cutStandardMap Q Λ θ β g) :=
  kerQuotientMap_exact ((eSum_idem (Q := S) F).map (cutShuffleAction Q Λ θ β N')) _ _ _ _
    (indMapRight_exact (stendhalQ_symm Q Λ hQ) (cutInputHom Q Λ θ β f)
      (cutInputHom Q Λ θ β g) h)

include hQ in
/-- Partial standardization preserves injections. -/
theorem cutStandardMap_injective (f : N →ₗ[D] N') (hf : Function.Injective f) :
    Function.Injective (cutStandardMap Q Λ θ β f) :=
  kerQuotientMap_injective _ _
    (indMapRight_injective (stendhalQ_symm Q Λ hQ) (cutInputHom Q Λ θ β f) hf)

include hQ in
/-- Partial standardization preserves surjections. -/
theorem cutStandardMap_surjective (f : N →ₗ[D] N') (hf : Function.Surjective f) :
    Function.Surjective (cutStandardMap Q Λ θ β f) :=
  kerQuotientMap_surjective _ _
    (indMapRight_surjective (stendhalQ_symm Q Λ hQ) (cutInputHom Q Λ θ β f) hf)

end Categorification.Stendhal
