/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedHeadEmbedding
import Categorification.WeightedKLR.RedStrands.LastRedParabolicLift
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleLayer

/-!
# Recovering the factor simple on the maximal cut of a standard module

Webster, arXiv:1309.3796v2, §5, Theorem 5.8 and Lemma 5.9. The identity
shuffle embeds the inducing module into the standard module. Its range
is the fixed space of the separated cut, and the two boundary algebras
act on this space as on the original module. Cuts outside the dominance
bound have a lift of their sector idempotent acting by zero.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra Categorification.Graded GProj
open scoped TensorProduct

private theorem cutActionTower {k C V : Type*} [Field k] [Ring C] [Algebra k C]
    [AddCommGroup V] [Module k V] (ρ : C →ₐ[k] Module.End k V) :
    let := Module.compHom V ρ.toRingHom
    IsScalarTower k C V := by
  let := Module.compHom V ρ.toRingHom
  exact ⟨fun c a x => by
    change ρ (c • a) x = c • (ρ a x)
    rw [map_smul, LinearMap.smul_apply]⟩

private def fixedEquivOfRange {k B C M V : Type*} [Field k] [Ring B] [Ring C] [Algebra k B]
    [Algebra k C] [AddCommGroup M] [Module k M] [Module B M] [IsScalarTower k B M]
    [AddCommGroup V] [Module k V] (ψ : B →ₙₐ[k] C) (ρ : C →ₐ[k] Module.End k V)
    (unit : M →ₗ[k] V) (hinj : Function.Injective unit)
    (hc : ∀ (t : B) (m : M), ρ (ψ t) (unit m) = unit (t • m))
    (hr : ∀ z : V, ρ (ψ 1) z ∈ LinearMap.range unit) :
    let := Module.compHom V ρ.toRingHom
    let := cutActionTower ρ
    M ≃ₗ[B] boundaryFixed ψ V := by
  let := Module.compHom V ρ.toRingHom
  let := cutActionTower ρ
  let f : M →ₗ[B] boundaryFixed ψ V :=
    { toFun := fun m => ⟨unit m, (hc 1 m).trans (congrArg unit (one_smul B m))⟩
      map_add' := fun x y => Subtype.ext (unit.map_add x y)
      map_smul' := fun t x => Subtype.ext (hc t x).symm }
  apply LinearEquiv.ofBijective f
  refine ⟨fun _ _ h => hinj (congrArg Subtype.val h), ?_⟩
  intro z
  obtain ⟨m, hm⟩ := hr z.1
  exact ⟨m, Subtype.ext (hm.trans z.2)⟩

universe w
variable {I : Type} [DecidableEq I] {k : Type w} [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {D : QuantumGroup.CartanDatum I}
    (Λ : Fin (ℓ+1) → I →₀ ℕ) (ν : Multiset I) (G : GradingDatum (stendhalQ Q Λ))

local notation "S" => stendhalQ Q Λ
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "cut" => LastRedWeightSplit ν
local notation "A₁" => fun θ : Multiset I => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "A₂" => fun β : Multiset I => Multiset.map (Sum.map (id : I → I)
  (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)

omit [DecidableEq I] in
private theorem cutParabolicWeight (u : cut) :
    (A₁) u.1.1 + (A₂) u.1.2 = stendhalWeight (ℓ+1) ν :=
  (parabolicInputWeights_add (ℓ := ℓ) u.1.1 u.1.2).trans (congrArg (stendhalWeight (ℓ+1)) u.2)

local notation "H" => cutParabolicWeight (ℓ := ℓ) ν
local notation "p" => fun u : cut => LastRedWeightSplit.position ν u ℓ
local notation "J" => fun u : cut => smallerSuffixIdeal Q Λ ((p) u)
local notation "ψ" => fun u : cut => lastRedLayerAction Q Λ ((p) u)
  (LastRedWeightSplit.content ν u ℓ) (LastRedWeightSplit.length ν u ℓ)
private abbrev cutProjection (u : cut) := ((J) u).ringCon.mkₐ k
local notation "q" => cutProjection (Q := Q) Λ ν
private abbrev cutTensorKLR (u : cut) := TensorKLR S ((A₁) u.1.1) ((A₂) u.1.2)
local notation "A" => cutTensorKLR (Q := Q) Λ ν

private def cutConcat (u : cut) : (A) u →ₗ[k] T :=
  (TensorProductAlgebra.mk Q Λ ν).toLinearMap ∘ₗ (orderProjection Q Λ ν).toLinearMap ∘ₗ
    (StendhalAlgebraAllOrders.ofKLR k Q Λ ν).toLinearMap ∘ₗ (castKLR S ((H) u)).toLinearMap ∘ₗ
      concat S ((A₁) u.1.1) ((A₂) u.1.2)

private theorem standardCut_of_shuffle (u : cut) (b : IndecClass (lastRedFactorGrading Λ ν G u))
    (V : Type w) [AddCommGroup V] [Module k V] (ρ : ((J) u).ringCon.Quotient →ₐ[k] Module.End k V)
    (unit : b.top →ₗ[k] V) (hinj : Function.Injective unit)
    (hunit : ∀ (t : (A) u) (n : b.top), ρ ((q) u (cutConcat Λ ν u t)) (unit n) =
      unit (Algebra.TensorProduct.map (parabolicPrefixProjection Q Λ u.1.1)
        (parabolicLastCyclotomic Q Λ u.1.2) t • n))
    (himage : ∀ (t : (A) u) (z : V), ρ ((q) u (cutConcat Λ ν u t)) z ∈ LinearMap.range unit)
    (hzero : ∀ (v : cut), ¬ v.1.1 ≤ u.1.1 → ∀ (t : (A) v) (z : V),
      ρ ((q) u (cutConcat Λ ν v t)) z = 0) : Nonempty (LastRedInducedCut Λ ν G u b) := by
  let := Module.compHom V ρ.toRingHom
  let := cutActionTower ρ
  refine ⟨{ carrier := V, recover := ⟨fixedEquivOfRange ((ψ) u) ρ unit hinj ?_ ?_⟩, support := ?_ }⟩
  · intro t n
    exact lastRedLayerAction_identityShuffle Q Λ ((p) u) (LastRedWeightSplit.content ν u ℓ)
      (LastRedWeightSplit.length ν u ℓ) ((H) u) ρ (Algebra.lsmul k k _) unit hunit t n
  · obtain ⟨t, _, ht⟩ := lastRedLayerAction_exists_parabolicLift Q Λ ((p) u)
      (LastRedWeightSplit.content ν u ℓ) (LastRedWeightSplit.length ν u ℓ) ((H) u) 1
    intro z
    rw [← ht]
    exact himage t z
  · intro v hv
    obtain ⟨t, _, ht⟩ := lastRedLayerAction_exists_parabolicLift Q Λ ((p) v)
      (LastRedWeightSplit.content ν v ℓ) (LastRedWeightSplit.length ν v ℓ) ((H) v) 1
    exact ⟨cutConcat Λ ν v t, ht, hzero v hv t⟩

/-- Standardization recovers each factor simple on its maximal cut and kills the
sector outside its black-prefix support (Webster, arXiv:1309.3796v2,
§5, Theorem 5.8 and Lemma 5.9). -/
theorem nonempty_lastRedInducedCut (hQ : KLRSymm Q) (u : cut)
    (b : IndecClass (lastRedFactorGrading Λ ν G u)) :
    Nonempty (LastRedInducedCut Λ ν G u b) := by
  rcases u with ⟨⟨θ,β⟩,rfl⟩
  let u : LastRedWeightSplit (θ+β) := ⟨(θ,β),rfl⟩
  let P := LastRedWeightSplit.position (θ+β) u ℓ
  have hp : P.val = ((stendhalWeight ℓ θ).map (addRedColor ℓ)).card := by
    simp [P, u, LastRedWeightSplit.position, stendhalWeight]
  let V := ParabolicStandard Q Λ θ β b.top
  let ρ := parabolicStandardLayerAction Q Λ θ β b.top hQ P hp
  apply standardCut_of_shuffle Λ (θ+β) G u b V ρ (parabolicStandardUnit Q Λ θ β b.top)
    (parabolicStandardUnit_injective Q Λ θ β b.top hQ)
  · exact parabolicStandardAction_concat_unit Q Λ θ β b.top hQ
  · exact parabolicStandardAction_concat_mem_range Q Λ θ β b.top hQ
  · intro v hv t z
    have hz := parabolicStandardAction_other_concat_eq_zero Q Λ θ β b.top hQ
      v.1.1 v.1.2 v.2 hv t
    exact LinearMap.congr_fun hz z

variable (hQ : IsRouquierQ D Q)

/-- Taking standard-module heads embeds the pairs of factor shift classes into the
shift classes for the full tensor block (Webster, arXiv:1309.3796v2, §5, Theorem 5.8). -/
def lastRedStandardHeadEmbedding :
    (Σ u : cut, LastRedFactorClasses Λ ν G u) ↪ IndecClass (tensorProductGrade G ν) :=
  lastRedHeadEmbedding Λ ν G hQ (nonempty_lastRedInducedCut Λ ν G hQ.klrSymm)

/-- Standard-module heads classify projective shift classes by the final split and
the two factor classes (Webster, arXiv:1309.3796v2, §5, Theorem 5.8). -/
def lastRedStandardHeadEquiv :
    (Σ u : cut, LastRedFactorClasses Λ ν G u) ≃ IndecClass (tensorProductGrade G ν) :=
  lastRedHeadEquiv Λ ν G hQ (nonempty_lastRedInducedCut Λ ν G hQ.klrSymm)

include hQ in
/-- The Laurent rank at a given weight is the sum over last-red splits of the
products of the factor ranks (Webster, arXiv:1309.3796v2, §4, Theorem 4.38
and §5, Theorem 5.8). -/
theorem lastRedK0_rank_eq :
    Module.rank (LaurentPolynomial ℤ) (K0 (tensorProductGrade G ν)) =
    Cardinal.sum (fun u : LastRedWeightSplit ν =>
      Module.rank (LaurentPolynomial ℤ) (K0 (tensorProductGrade (restrictRedGrading Q Λ G) u.1.1)) *
      Module.rank (LaurentPolynomial ℤ) (K0 (CycKLR.grade (restrictBlackGrading Q Λ G)
        (Λ (Fin.last ℓ)) u.1.2))) :=
  lastRedK0_rank_eq_of_inducedCut Λ ν G hQ (nonempty_lastRedInducedCut Λ ν G hQ.klrSymm)

end Categorification.Stendhal
