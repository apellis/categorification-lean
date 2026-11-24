/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleDescent

/-!
# Fixed spaces of separated diagrams on a standardization

The identity shuffle identifies the fixed space of a separated diagram on
the inducing module with the fixed space of its concatenation on the
standardization. The action depends only on the separated factor algebra.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA TensorProduct
open scoped TensorProduct
variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) (θ β : Multiset I)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "S" => stendhalQ Q Λ
local notation "νall" => (θ + β)
local notation "T" => TensorProductAlgebra k Q Λ νall
variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]

local notation "V" => ParabolicStandard Q Λ θ β N
variable (hQ : KLRSymm Q)

/-- The action of a separated affine diagram on the actual parabolic standardization. -/
def parabolicStandardConcatAction (t : TensorKLR S α δ) : Module.End k V :=
  parabolicStandardAction Q Λ θ β N hQ (TensorProductAlgebra.mk Q Λ νall
    (orderProjection Q Λ νall (StendhalAlgebraAllOrders.ofKLR k Q Λ νall
      (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β) (concat S α δ t)))))

local notation "act" => parabolicStandardConcatAction Q Λ θ β N hQ
local notation "U" => parabolicStandardUnit Q Λ θ β N

/-- Concatenation acts on the standardization through the separated factor algebra.
In particular projecting to a divided-power component is independent of the
choice of its affine lift. -/
theorem parabolicStandardConcatAction_eq_of_inputMap_eq
    {t t' : TensorKLR S α δ}
    (h : parabolicInputMap Q Λ θ β t = parabolicInputMap Q Λ θ β t') :
    act t = act t' := by
  apply LinearMap.ext
  intro z
  obtain ⟨n, hn⟩ := parabolicStandardAction_concat_mem_range Q Λ θ β N hQ 1 z
  change U n = act 1 z at hn
  have cut (w : TensorKLR S α δ) : act w z = act w (act 1 z) := by
    simp only [parabolicStandardConcatAction, parabolicStandardAction_affine,
      ← Module.End.mul_apply, ← map_mul, concat_one, concat_mul_oneConcat]
  rw [cut t, cut t', ← hn]
  simp only [parabolicStandardConcatAction, parabolicStandardAction_concat_unit, h]

/-- An affine lift of a factor idempotent acts as a projector on standardization. -/
theorem isIdempotentElem_parabolicStandardConcatAction (t : TensorKLR S α δ)
    (ht : IsIdempotentElem (parabolicInputMap Q Λ θ β t)) :
    IsIdempotentElem (act t) := by
  have hmul : act (t * t) = act t * act t := by
    simp only [parabolicStandardConcatAction, parabolicStandardAction_affine, concat_mul, map_mul]
  change act t * act t = act t
  rw [← hmul]
  apply parabolicStandardConcatAction_eq_of_inputMap_eq
  rw [map_mul, ht.eq]

/-- The identity shuffle identifies the fixed subspace of a separated diagram on
the factor module with the fixed subspace of its concatenated diagram on the
actual standardization. This applies in particular to divided-power projectors. -/
def parabolicStandardFixedEquiv (t : TensorKLR S α δ) :
    fixSub k N (parabolicInputMap Q Λ θ β t) ≃ₗ[k] LinearMap.ker (act t - LinearMap.id) := by
  let f : fixSub k N (parabolicInputMap Q Λ θ β t) →ₗ[k] LinearMap.ker (act t - LinearMap.id) :=
    ((U).comp (fixSub k N (parabolicInputMap Q Λ θ β t)).subtype).codRestrict _ fun n => by
      change act t (U n.val) - U n.val = 0
      rw [parabolicStandardConcatAction, parabolicStandardAction_concat_unit Q Λ θ β N hQ,
        show (parabolicInputMap Q Λ θ β t) • n.val = n.val from n.property, sub_self]
  refine LinearEquiv.ofBijective f ⟨fun n n' h => Subtype.ext
    (parabolicStandardUnit_injective Q Λ θ β N hQ (congrArg Subtype.val h)), ?_⟩
  intro z
  have hz : act t z.val = z.val := sub_eq_zero.mp z.property
  obtain ⟨n, hn⟩ := parabolicStandardAction_concat_mem_range Q Λ θ β N hQ t z.val
  change U n = act t z.val at hn
  rw [hz] at hn
  refine ⟨⟨n, ?_⟩, Subtype.ext hn⟩
  apply parabolicStandardUnit_injective Q Λ θ β N hQ
  change U ((parabolicInputMap Q Λ θ β t) • n) = U n
  rw [← parabolicStandardAction_concat_unit Q Λ θ β N hQ]
  change act t (U n) = U n
  rwa [hn]

end Categorification.Stendhal
