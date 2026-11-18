/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackAffineProjection
import Categorification.KLR.CyclotomicAction.Induction
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverQuotient
import Categorification.WeightedKLR.RedStrands.BlackRestriction
import Categorification.KLR.CyclotomicAbsentModule

/-!
# Black restriction cuts of the cyclotomic cover

Webster, arXiv:1309.3796v2, §4.6, Theorem 4.31. Appending a black strand
commutes with projection from the enlarged cyclotomic algebra to the
tensor product algebra. The induced map on the restriction cut is a
surjective semilinear map over the lower projection.
-/
noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section ChangeParameters
variable {J k B : Type*} [DecidableEq J] [CommRing k] [Ring B] [Algebra k B]
    {P S : J → J → MvPolynomial (Fin 2) k} {β δ : Multiset J}
    (i : J) (h : {i} + β = δ) (f : KLRAlgebra k P δ →ₐ[k] B) (g : KLRAlgebra k S δ →ₐ[k] B)
    (hg : ∀ v : FreeAlgebra k (Gen δ), f (KLRAlgebra.mk k P δ v) = g (KLRAlgebra.mk k S δ v))

include hg in
private theorem lastIncl_free (v : FreeAlgebra k (Gen β)) :
    f (lastIncl P i h (KLRAlgebra.mk k P β v)) = g (lastIncl S i h (KLRAlgebra.mk k S β v)) := by
  have he (s : Seq β) : f (lastIncl P i h (e s)) = g (lastIncl S i h (e s)) := by
    simp only [lastIncl_apply, cL_e, castKLR_e]
    exact hg (fe k δ _)
  have h₁ : f (lastIncl P i h 1) = g (lastIncl S i h 1) := by
    rw [← sum_e (k := k) (Q := P) (ν := β), ← sum_e (k := k) (Q := S) (ν := β)]
    simp only [map_sum, he]
  induction v using FreeAlgebra.induction with
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | grade0 c => simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, h₁]
  | grade1 t =>
    cases t with
    | idem s => exact he s
    | dot a =>
      change f (lastIncl P i h (x a)) = g (lastIncl S i h (x a))
      simp only [lastIncl_apply, cL_x, map_mul, castKLR_x]
      exact congrArg₂ (· * ·) (hg (fx k δ _)) h₁
    | cross j =>
      change f (lastIncl P i h (ψ j)) = g (lastIncl S i h (ψ j))
      by_cases hj : j+1 < β.card
      · simp only [lastIncl_apply, cL_ψ i β hj, map_mul, castKLR_ψ]
        exact congrArg₂ (· * ·) (hg (fψ k δ j)) h₁
      · simp only [ψ_eq_zero j (by omega : β.card ≤ j+1), map_zero]

end ChangeParameters

section Tower
variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)
    (C : QuantumGroup.CartanDatum I) (i : I)
local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "ci" => (Sum.inl i : I ⊕ Fin ℓ)
local notation "γ" => ((Singleton.singleton ci : Multiset (I ⊕ Fin ℓ)) + μ)
local notation "S" => cyclotomicCoverQ C Λ Q
local notation "p" => cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)
local notation "hwt" => stendhalWeight_black_cons (ℓ := ℓ) i ν
local notation "π" => cyclotomicCoverToTensor (Q := Q) Λ ν C
local notation "T'" => TensorProductAlgebra k Q Λ νᵢ

/-- The projection on the upper algebra, with its domain indexed by the
literal cyclotomic black extension of the lower content. -/
def cyclotomicCoverUpper : CycKLR k S p γ →ₐ[k] T' :=
  (cyclotomicCoverToTensor (Q := Q) Λ νᵢ C).comp (CyclotomicAction.castCyc S p hwt).toAlgHom

local notation "π'" => cyclotomicCoverUpper (Q := Q) Λ ν C i

theorem cyclotomicCoverUpper_surjective : Function.Surjective π' :=
  (cyclotomicCoverToTensor_surjective (Q := Q) Λ νᵢ C).comp
    (CyclotomicAction.castCyc S p hwt).surjective

theorem cyclotomicCoverUpper_eq_zero_iff (x : CycKLR k S p γ) :
    π' x = 0 ↔ CyclotomicAction.castCyc S p hwt x ∈ cyclotomicCoverIdeal νᵢ S := by
  change cyclotomicCoverToTensor (Q := Q) Λ νᵢ C (CyclotomicAction.castCyc S p hwt x) = 0 ↔ _
  rw [← cyclotomicCoverToTensor_ker (Q := Q) Λ νᵢ C, TwoSidedIdeal.mem_ker]
  rfl

private theorem coverToTensor_affine_mk (v : FreeAlgebra k (Gen μ)) :
    π (CycKLR.mk k S p μ (KLRAlgebra.mk k S μ v)) =
      affineTensorProjection (Q := Q) Λ ν (KLRAlgebra.mk k (affineCoverQ Q Λ) μ v) := by
  rw [cyclotomicCoverToTensor_mk]
  apply congrArg (TensorProductAlgebra.mk Q Λ ν)
  apply congrArg (orderProjection Q Λ ν)
  change StendhalAlgebraAllOrders.ofKLR k Q Λ ν (KLRAlgebra.mk k _ μ v) =
    affineCover Q Λ ν (KLRAlgebra.mk k _ μ v)
  rw [StendhalAlgebraAllOrders.ofKLR_mk]
  symm
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

/-- Projection preserves free diagram representatives of the upper block,
including individual idempotents, dots and crossings. -/
theorem cyclotomicCoverUpper_mk (v : FreeAlgebra k (Gen γ)) :
    π' (CycKLR.mk k S p γ (KLRAlgebra.mk k S γ v)) =
      affineTensorProjection (Q := Q) Λ νᵢ (castKLR (affineCoverQ Q Λ) hwt
        (KLRAlgebra.mk k (affineCoverQ Q Λ) γ v)) := by
  have h {δ : Multiset (I ⊕ Fin ℓ)} (hδ : δ = stendhalWeight ℓ νᵢ) (a : FreeAlgebra k (Gen δ)) :
      cyclotomicCoverToTensor (Q := Q) Λ νᵢ C (CyclotomicAction.castCyc S p hδ
        (CycKLR.mk k S p δ (KLRAlgebra.mk k S δ a))) =
      affineTensorProjection (Q := Q) Λ νᵢ (castKLR (affineCoverQ Q Λ) hδ
        (KLRAlgebra.mk k (affineCoverQ Q Λ) δ a)) := by
    subst δ
    exact coverToTensor_affine_mk Λ νᵢ C a
  exact h hwt v

/-- The ordinary cyclotomic tower and the intrinsic red-strand tower commute
with projection on every element of the lower ring (Webster §4.6). -/
theorem cyclotomicCoverUpper_appendBlack (x : CycKLR k S p μ) :
    π' (AbsentColour.cyclotomicLast S ci p μ x) = appendBlack Q Λ i ν (π x) := by
  obtain ⟨a, rfl⟩ := CycKLR.mk_surjective x
  obtain ⟨v, rfl⟩ := KLRAlgebra.mk_surjective a
  rw [coverToTensor_affine_mk, appendBlack_affineTensorProjection]
  change cyclotomicCoverToTensor Λ νᵢ C (CyclotomicAction.lastEmb S p ci hwt _) = _
  rw [CyclotomicAction.lastEmb_mk]
  exact lastIncl_free ci hwt
    ((cyclotomicCoverToTensor (Q := Q) Λ νᵢ C).comp (CycKLR.mk k S p _))
    (affineTensorProjection (Q := Q) Λ νᵢ)
    (coverToTensor_affine_mk Λ νᵢ C) v

theorem cyclotomicCoverUpper_lastIdem :
    π' (AbsentColour.lastIdem S ci p μ) = appendBlack Q Λ i ν 1 := by
  rw [AbsentColour.lastIdem, cyclotomicCoverUpper_appendBlack, map_one]

end Tower

section Cut
open KLRAlgebra.AbsentColour
variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I)
    (C : QuantumGroup.CartanDatum I) (i : I)
local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "ci" => (Sum.inl i : I ⊕ Fin ℓ)
local notation "γ" => ((Singleton.singleton ci : Multiset (I ⊕ Fin ℓ)) + μ)
local notation "S" => cyclotomicCoverQ C Λ Q
local notation "p" => cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)
local notation "π" => cyclotomicCoverToTensor (Q := Q) Λ ν C
local notation "π'" => cyclotomicCoverUpper (Q := Q) Λ ν C i
local notation "src" => AbsentColour.Res S ci p μ (CycKLR k S p γ)
local notation "dst" => BlackRes (Q := Q) (Λ := Λ) i ν (TensorProductAlgebra k Q Λ νᵢ)

/-- The upper projection on the two regular restriction cuts, semilinear for
the lower projection. -/
def cyclotomicCoverResMap : src →ₛₗ[(π).toRingHom] dst where
  toFun x := ⟨π' x.1, by
    change appendBlack Q Λ i ν 1 * π' x.1 = π' x.1
    rw [← cyclotomicCoverUpper_lastIdem (Q := Q) Λ ν C i, ← map_mul]
    exact congrArg π' x.2⟩
  map_add' x y := Subtype.ext (map_add π' x.1 y.1)
  map_smul' a x := Subtype.ext (by
    change π' (cyclotomicLast S ci p μ a * x.1) = appendBlack Q Λ i ν (π a) * π' x.1
    rw [map_mul, cyclotomicCoverUpper_appendBlack])

theorem cyclotomicCoverResMap_apply (x : src) :
    (cyclotomicCoverResMap (Q := Q) Λ ν C i x).1 = π' x.1 := rfl

theorem cyclotomicCoverResMap_surjective :
    Function.Surjective (cyclotomicCoverResMap (Q := Q) Λ ν C i) := by
  intro y
  obtain ⟨x, hx⟩ := cyclotomicCoverUpper_surjective (Q := Q) Λ ν C i y.1
  refine ⟨⟨lastIdem S ci p μ * x, ?_⟩, ?_⟩
  · change lastIdem S ci p μ * (lastIdem S ci p μ * x) = _
    rw [← mul_assoc, lastIdem_mul]
  · apply Subtype.ext
    rw [cyclotomicCoverResMap_apply]
    change π' (lastIdem S ci p μ * x) = _
    rw [map_mul, hx, cyclotomicCoverUpper_lastIdem]
    exact y.2

end Cut
end Categorification.Stendhal
