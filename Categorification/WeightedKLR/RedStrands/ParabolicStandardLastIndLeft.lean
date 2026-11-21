/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastKernel
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndLayer
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastLeft
import Categorification.KLR.IndFirstSlide

/-!
# The first-factor layer of `F_i(S N)`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. Let `N` be a module over the parabolic factor algebra of `(θ, β)`.
In the induction `F_i(S N)` of the standardization, the diagrams whose last red strand ends after
position `|α| + 1` act by zero (`e_smul_lastIndF_eq_zero`), so the last-red layer quotient of the
split `(i + θ, β)` acts on `F_i(S N)` (`firstIndLayerAction`).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ β : Multiset I)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "T′" => TensorProductAlgebra k Q Λ ((Si i) + (θ + β))
local notation "T₁" => TensorProductAlgebra k Q Λ (((Si i) + θ) + β)
local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "μ₁" => stendhalWeight (ℓ+1) ((Si i) + (θ + β))

omit [DecidableEq I] in
theorem firstInd_blackWeight : (Si i) + (θ + β) = ((Si i) + θ) + β := (add_assoc _ _ _).symm

local notation "cst₁" => castTensorProductAlgebra Q Λ (firstInd_blackWeight i θ β)

/-- The split of `(i + θ) + β` into the prefix `i + θ` and the black suffix `β`. -/
abbrev firstIndSplit : LastRedWeightSplit (((Si i) + θ) + β) := ⟨((Si i) + θ, β), rfl⟩

local notation "p₁" => LastRedWeightSplit.position (((Si i) + θ) + β) (firstIndSplit i θ β) ℓ
local notation "I₁" => smallerSuffixIdeal Q Λ p₁

omit [DecidableEq I] in
theorem firstIndPosition_val : (p₁).val = (Aₚ).card + 1 := by
  simp [LastRedWeightSplit.position, stendhalWeight]
  omega

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)

/-- **`F_i(S N)`** with its `k`-module structure through `T(i + (θ + β))`. -/
abbrev FirstIndF : Type _ :=
  IndK k (ParabolicStandardT Q Λ θ β N hQ) (appendBlackHom Q Λ i θ β)

instance : SMulCommClass T′ k (FirstIndF Q Λ i θ β N hQ) where
  smul_comm t c x := by
    change t • (algebraMap k T′ c • x) = algebraMap k T′ c • (t • x)
    rw [← mul_smul, ← mul_smul, Algebra.commutes]

/-- An idempotent whose last red strand ends after position `|α| + 1` kills `F_i(S N)`. -/
theorem tensorOfKLR_e_smul_firstIndF (s : Seq μ₁) (a : Fin (Multiset.card μ₁))
    (hred : s.lbl a = .inr (Fin.last ℓ)) (hlt : (Aₚ).card + 1 < a.val)
    (x : FirstIndF Q Λ i θ β N hQ) :
    tensorOfKLR Q Λ ((Si i) + (θ + β)) (KLRAlgebra.e s) • x = 0 := by
  have h := e_smul_lastIndF_eq_zero Q Λ i θ β N hQ (Seq.cast (blackCast i θ β).symm s)
    (Fin.cast (congrArg Multiset.card (blackCast i θ β)).symm a)
    hred hlt x
  rw [castKLR_e, Seq.cast_cast_symm] at h
  change TensorProductAlgebra.mk Q Λ _ (orderProjection Q Λ _ (affineCover Q Λ _ _)) • x = 0 at h
  rw [affineCover_e] at h
  exact h

omit [Field k] in
theorem castTensorProductAlgebra_symm' {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
    {Λ : Fin (ℓ + 1) → I →₀ ℕ} {ν ν' : Multiset I} (h : ν = ν') :
    (castTensorProductAlgebra Q Λ h).symm = castTensorProductAlgebra Q Λ h.symm := by
  subst h; rfl

omit [Field k] in
theorem tensorOfKLR_e_of_ordered {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
    {Λ : Fin (ℓ + 1) → I →₀ ℕ} (ν : Multiset I) (s : Seq (stendhalWeight (ℓ+1) ν))
    (hs : IsRedOrdered s) :
    tensorOfKLR Q Λ ν (KLRAlgebra.e s) = TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e s hs) :=
  congrArg _ (Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans
    (ite_eq_left hs)))

/-- `T((i + θ) + β)` acting on `F_i(S N)` through the cast. -/
def firstIndAction : T₁ →ₐ[k] Module.End k (FirstIndF Q Λ i θ β N hQ) :=
  (Algebra.lsmul k k (FirstIndF Q Λ i θ β N hQ)).comp (cst₁).symm.toAlgHom

/-- **The last-red layer quotient of `(i + θ, β)` acts on `F_i(S N)`**: the diagrams whose
last red strand ends after position `|α| + 1` act by zero. -/
def firstIndLayerAction :
    (I₁).ringCon.Quotient →ₐ[k] Module.End k (FirstIndF Q Λ i θ β N hQ) := by
  apply (I₁).ringCon.liftₐ (firstIndAction Q Λ i θ β N hQ)
  apply (TwoSidedIdeal.ringCon_le_iff
    (J := TwoSidedIdeal.ker (firstIndAction Q Λ i θ β N hQ).toRingHom)).mp
  apply TwoSidedIdeal.span_le.mpr
  rintro _ ⟨s, hs, a, ha, hred, rfl⟩
  apply (TwoSidedIdeal.mem_ker _).mpr
  apply LinearMap.ext
  intro x
  change (cst₁).symm (TensorProductAlgebra.mk Q Λ _ (StendhalAlgebra.e s hs)) • x = 0
  rw [← tensorOfKLR_e_of_ordered, castTensorProductAlgebra_symm', castTensorProductAlgebra_mk,
    castKLR_e]
  have hp := firstIndPosition_val i θ β (ℓ := ℓ)
  exact tensorOfKLR_e_smul_firstIndF Q Λ i θ β N hQ _
    (Fin.cast (congrArg Multiset.card (congrArg (stendhalWeight (ℓ+1))
      (firstInd_blackWeight i θ β).symm)) a) hred (by
      change (Aₚ).card + 1 < a.val
      have : (p₁).val < a.val := ha
      omega) x

theorem firstIndLayerAction_mk (a : T₁) :
    firstIndLayerAction Q Λ i θ β N hQ ((I₁).ringCon.mk' a) =
      firstIndAction Q Λ i θ β N hQ a := rfl

end Categorification.Stendhal
