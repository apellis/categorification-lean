/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationExact

/-!
# The universal property of partial standardization at a cut

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization `𝕊^{λ_1…λ_a; λ_{a+1}…λ_{a+r}}` at a cut (`Stendhal.CutStandard`).
A map of partial standardizations into a `T^λ(θ + β)`-module `X` is the same as a map from the
input module `N` to `X` which intertwines each pair of juxtaposed affine diagrams of the two
blocks, acting on `N` through the factor algebras and on `X` through `T^λ(θ + β)`
(`cutStandardLift`, `cutStandardLift_unit`, `cutStandardLift_unique`). This is the form in
which partial standardization is left adjoint to restriction, used to compare iterated
partial standardizations.

The representation of `T^λ(θ + β)` on `X` is a map of `k`-algebras
`σ : T^λ(θ + β) → End_k X`, and the affine KLR algebra of all strands maps to `T^λ(θ + β)`
by `cutAffineMap`.

## Main definitions

* `Stendhal.cutAffineMap`: the map from the affine KLR algebra of all strands to `T^λ(θ + β)`.
* `Stendhal.IsCutInputHom`: the intertwining condition on a map `N → X`.
* `Stendhal.cutStandardLift`: the map of partial standardizations it induces.

## Main results

* `Stendhal.cutAffineMap_eSum`: the ordered loadings sum to `1` in `T^λ(θ + β)`.
* `Stendhal.cutStandardLift_action`: the induced map is linear over `T^λ(θ + β)`.
* `Stendhal.cutStandardLift_unit`: it restricts to the given map on the identity shuffle.
* `Stendhal.cutStandardLift_unique`: a `T^λ(θ + β)`-linear map out of the partial
  standardization is determined by its restriction to the identity shuffle.
* `Stendhal.isCutInputHom_comp_unit`: the restriction of a `T^λ(θ + β)`-linear map satisfies
  the intertwining condition.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA TensorProduct MulOpposite
open scoped TensorProduct

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (a + r) → I →₀ ℕ) (θ β : Multiset I)

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ
local notation "T" => TensorProductAlgebra k Q Λ (θ + β)
local notation "A" => KLRAlgebra k S (α + δ)
local notation "B" => TensorKLR S α δ
local notation "F" => cutOrderedLoadings (a := a) (r := r) θ β

/-- **The map from the affine KLR algebra of all strands to `T^λ(θ + β)`.** -/
def cutAffineMap : KLRAlgebra k (stendhalQ Q Λ) (α + δ) →ₐ[k] TensorProductAlgebra k Q Λ (θ + β) :=
  ((TensorProductAlgebra.mk Q Λ (θ + β)).comp (orderProjection Q Λ (θ + β))).comp
    ((StendhalAlgebraAllOrders.ofKLR k Q Λ (θ + β)).comp
      (castKLR (stendhalQ Q Λ) (cutInputWeights_add (a := a) (r := r) θ β)).toAlgHom)

theorem cutAffineMap_apply (z : KLRAlgebra k (stendhalQ Q Λ) (α + δ)) :
    cutAffineMap Q Λ θ β z = TensorProductAlgebra.mk Q Λ (θ + β)
      (orderProjection Q Λ (θ + β) (StendhalAlgebraAllOrders.ofKLR k Q Λ (θ + β)
        (castKLR S (cutInputWeights_add (a := a) (r := r) θ β) z))) := rfl

theorem cutAffineMap_surjective : Function.Surjective (cutAffineMap Q Λ θ β) :=
  cutStandardAffine_surjective Q Λ θ β

omit [DecidableEq I] in
private theorem isRedOrdered_cast' {μ μ' : Multiset (I ⊕ Fin (a + r))} (h : μ = μ') (s : Seq μ) :
    IsRedOrdered (Seq.cast h s) ↔ IsRedOrdered s := by
  subst h; rfl

/-- A loading with the red strands out of order is zero in `T^λ(θ + β)`. -/
theorem cutAffineMap_e_of_not_isRedOrdered (s : Seq (α + δ)) (hs : ¬ IsRedOrdered s) :
    cutAffineMap Q Λ θ β (e s) = 0 := by
  classical
  have hs' : ¬ IsRedOrdered (Seq.cast (cutInputWeights_add (a := a) (r := r) θ β) s) :=
    fun h => hs ((isRedOrdered_cast' _ s).1 h)
  have h0 : orderProjection Q Λ (θ + β) (StendhalAlgebraAllOrders.e
      (Seq.cast (cutInputWeights_add (a := a) (r := r) θ β) s)) = 0 := by
    apply Subtype.ext
    change StendhalAlgebraAllOrders.e _ * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ (θ + β) = 0
    rw [StendhalAlgebraAllOrders.e_mul_redOrderedIdem, ite_eq_right_of_eq_false _ _ (eq_false hs')]
  rw [cutAffineMap_apply, castKLR_e]
  change TensorProductAlgebra.mk Q Λ (θ + β) (orderProjection Q Λ (θ + β)
    (StendhalAlgebraAllOrders.e _)) = 0
  rw [h0, map_zero]

/-- **The ordered loadings sum to `1` in `T^λ(θ + β)`.** -/
theorem cutAffineMap_eSum : cutAffineMap Q Λ θ β (eSum (Q := S) F) = 1 := by
  classical
  have h1 : (1 : T) = cutAffineMap Q Λ θ β (∑ s, e s) := by
    rw [sum_e, map_one]
  rw [h1, map_sum, eSum, map_sum, cutOrderedLoadings, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with hs
  · rfl
  · exact (cutAffineMap_e_of_not_isRedOrdered Q Λ θ β s hs).symm

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  {X : Type*} [AddCommGroup X] [Module k X]
  (σ : TensorProductAlgebra k Q Λ (θ + β) →ₐ[k] Module.End k X)

local notation "N₀" => CutInput Q Λ θ β N
local notation "V" => CutStandard Q Λ θ β N

/-- **The intertwining condition** on a map from the input module to a
`T^λ(θ + β)`-module: a pair of juxtaposed affine diagrams of the two blocks acts on `N`
through the factor algebras and on `X` through `T^λ(θ + β)`. -/
def IsCutInputHom (f : N →ₗ[k] X) : Prop :=
  ∀ (t : TensorKLR (stendhalQ Q Λ) α δ) (n : N),
    f (cutInputMap Q Λ θ β t • n) = σ (cutAffineMap Q Λ θ β (concat S α δ t)) (f n)

variable {N}

/-- A `k`-linear map out of `N`, on the input module. -/
def cutInputLin (f : N →ₗ[k] X) : N₀ →ₗ[k] X where
  toFun n := f n
  map_add' := f.map_add
  map_smul' := f.map_smul


/-- The bilinear map `m ⊗ n ↦ m · f(n)` on the induced module. -/
def cutShuffleBil (f : N →ₗ[k] X) : IndBimod S α δ →ₗ[k] N₀ →ₗ[k] X :=
  LinearMap.mk₂ k (fun m n => σ (cutAffineMap Q Λ θ β (m : A)) (cutInputLin Q Λ θ β f n))
    (fun m m' n => by simp only [Submodule.coe_add, map_add, LinearMap.add_apply])
    (fun c m n => by
      simp only [Submodule.coe_smul_of_tower, map_smul, LinearMap.smul_apply])
    (fun m n n' => by simp only [map_add])
    (fun c m n => by simp only [map_smul])

theorem cutShuffleBil_apply (f : N →ₗ[k] X) (m : IndBimod S α δ) (n : N₀) :
    cutShuffleBil Q Λ θ β σ f m n =
      σ (cutAffineMap Q Λ θ β (m : A)) (cutInputLin Q Λ θ β f n) := rfl

variable {σ}

/-- The map of the induced module into `X` induced by an intertwining map. -/
def cutShuffleLift (f : N →ₗ[k] X) (hf : IsCutInputHom Q Λ θ β N σ f) :
    CutShuffle Q Λ θ β N →ₗ[k] X :=
  BalancedTensor.lift (cutShuffleBil Q Λ θ β σ f) (fun m t n => by
    rw [cutShuffleBil_apply, cutShuffleBil_apply, coe_op_smul, map_mul, map_mul,
      Module.End.mul_apply, unop_op]
    exact congrArg _ (hf t n).symm)

theorem cutShuffleLift_tmul (f : N →ₗ[k] X) (hf : IsCutInputHom Q Λ θ β N σ f)
    (m : IndBimod S α δ) (n : N₀) :
    cutShuffleLift Q Λ θ β f hf (BalancedTensor.tmul m n) =
      σ (cutAffineMap Q Λ θ β (m : A)) (f n) := rfl

/-- The map of the induced module is linear over the affine KLR algebra. -/
theorem cutShuffleLift_smul (f : N →ₗ[k] X) (hf : IsCutInputHom Q Λ θ β N σ f) (z : A)
    (y : CutShuffle Q Λ θ β N) :
    cutShuffleLift Q Λ θ β f hf (z • y) =
      σ (cutAffineMap Q Λ θ β z) (cutShuffleLift Q Λ θ β f hf y) := by
  induction y using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]
  | tmul m n =>
    rw [BalancedTensor.smul_tmul', cutShuffleLift_tmul, cutShuffleLift_tmul, Submodule.coe_smul,
      smul_eq_mul, map_mul, map_mul, Module.End.mul_apply]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add]

/-- The map of the induced module vanishes on the part supported on unordered loadings. -/
theorem cutShuffleLift_excluded (f : N →ₗ[k] X) (hf : IsCutInputHom Q Λ θ β N σ f) :
    excludedSpace (cutShuffleAction Q Λ θ β N) F ≤ LinearMap.ker (cutShuffleLift Q Λ θ β f hf) := by
  intro y hy
  have hy' : (eSum (Q := S) F : A) • y = 0 := hy
  have h1 : cutShuffleLift Q Λ θ β f hf y =
      σ (cutAffineMap Q Λ θ β (eSum (Q := S) F)) (cutShuffleLift Q Λ θ β f hf y) := by
    rw [cutAffineMap_eSum, map_one, Module.End.one_apply]
  rw [LinearMap.mem_ker, h1, ← cutShuffleLift_smul, hy', map_zero]

/-- **The map of partial standardizations** induced by an intertwining map `N → X`. -/
def cutStandardLift (f : N →ₗ[k] X) (hf : IsCutInputHom Q Λ θ β N σ f) : V →ₗ[k] X :=
  (excludedSpace (cutShuffleAction Q Λ θ β N) F).liftQ (cutShuffleLift Q Λ θ β f hf)
    (cutShuffleLift_excluded Q Λ θ β f hf)

theorem cutStandardLift_mk (f : N →ₗ[k] X) (hf : IsCutInputHom Q Λ θ β N σ f)
    (y : CutShuffle Q Λ θ β N) :
    cutStandardLift Q Λ θ β f hf (Submodule.Quotient.mk y) = cutShuffleLift Q Λ θ β f hf y :=
  rfl

variable [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)

include hQ in
/-- **The induced map is linear over `T^λ(θ + β)`.** -/
theorem cutStandardLift_action (f : N →ₗ[k] X) (hf : IsCutInputHom Q Λ θ β N σ f) (t : T)
    (v : V) :
    cutStandardLift Q Λ θ β f hf (cutStandardAction Q Λ θ β N hQ t v) =
      σ t (cutStandardLift Q Λ θ β f hf v) := by
  obtain ⟨z, rfl⟩ := cutAffineMap_surjective Q Λ θ β t
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ v
  rw [cutAffineMap_apply, cutStandardAction_affine]
  exact cutShuffleLift_smul Q Λ θ β f hf z y

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- **The induced map restricts to the given map on the identity shuffle.** -/
theorem cutStandardLift_unit (f : N →ₗ[k] X) (hf : IsCutInputHom Q Λ θ β N σ f) (n : N) :
    cutStandardLift Q Λ θ β f hf (cutStandardUnit Q Λ θ β N n) = f n := by
  change σ (cutAffineMap Q Λ θ β (oneConcat S α δ)) (f n) = f n
  rw [← concat_one, ← hf, map_one, one_smul]

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- An element of the bimodule `A 1_{α,δ}` is its own multiple of the identity shuffle. -/
private theorem tmul_eq_smul_unit (m : IndBimod S α δ) (n : N₀) :
    (BalancedTensor.tmul m n : CutShuffle Q Λ θ β N) =
      (m : A) • indShuffleUnit (Q := S) (ν := α) (ν' := δ) N₀ n := by
  rw [indShuffleUnit, BalancedTensor.smul_tmul']
  congr 1
  exact Subtype.ext (m.2).symm

include hQ in
/-- **A `T^λ(θ + β)`-linear map out of the partial standardization is determined by its
restriction to the identity shuffle.** -/
theorem cutStandardLift_unique {h h' : V →ₗ[k] X}
    (hh : ∀ t v, h (cutStandardAction Q Λ θ β N hQ t v) = σ t (h v))
    (hh' : ∀ t v, h' (cutStandardAction Q Λ θ β N hQ t v) = σ t (h' v))
    (he : ∀ n, h (cutStandardUnit Q Λ θ β N n) = h' (cutStandardUnit Q Λ θ β N n)) :
    h = h' := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ v
  induction y using BalancedTensor.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul m n =>
    have hz : ∀ g : V →ₗ[k] X, (∀ t v, g (cutStandardAction Q Λ θ β N hQ t v) = σ t (g v)) →
        g (Submodule.mkQ _ (BalancedTensor.tmul m n)) =
          σ (cutAffineMap Q Λ θ β (m : A)) (g (cutStandardUnit Q Λ θ β N n)) := by
      intro g hg
      rw [← hg, cutAffineMap_apply, cutStandardAction_affine, tmul_eq_smul_unit]
      rfl
    rw [hz h hh, hz h' hh']
    exact congrArg _ (he n)
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

include hQ in
/-- **The restriction of a `T^λ(θ + β)`-linear map to the identity shuffle is
intertwining.** -/
theorem isCutInputHom_comp_unit {h : V →ₗ[k] X}
    (hh : ∀ t v, h (cutStandardAction Q Λ θ β N hQ t v) = σ t (h v)) :
    IsCutInputHom Q Λ θ β N σ (h.comp (cutStandardUnit Q Λ θ β N)) := by
  intro t n
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hh, cutAffineMap_apply,
    cutStandardAction_concat_unit]

include hQ in
/-- The induced map of the restriction of a `T^λ(θ + β)`-linear map is the map itself. -/
theorem cutStandardLift_comp_unit {h : V →ₗ[k] X}
    (hh : ∀ t v, h (cutStandardAction Q Λ θ β N hQ t v) = σ t (h v)) :
    cutStandardLift Q Λ θ β (h.comp (cutStandardUnit Q Λ θ β N))
      (isCutInputHom_comp_unit Q Λ θ β hQ hh) = h :=
  cutStandardLift_unique Q Λ θ β hQ
    (cutStandardLift_action Q Λ θ β hQ _ _) hh
    (fun n => cutStandardLift_unit Q Λ θ β _ _ n)

end Categorification.Stendhal
