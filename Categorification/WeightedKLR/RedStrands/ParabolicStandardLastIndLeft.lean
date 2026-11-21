/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastKernel
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndLayer
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastLeft
import Categorification.KLR.IndFirstSlide
import Categorification.KLR.MackeyInj

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

local notation "S" => stendhalQ Q Λ
local notation "Aₗ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
  (stendhalWeight 1 β)
local notation "cst" => castTensorProductAlgebra Q Λ (lastInd_blackWeight i θ β)

omit [DecidableEq I] in
theorem firstInd_klrWeight :
    Aₚ + Aₗ + {(Sum.inl i : I ⊕ Fin (ℓ + 1))} = μ₁ :=
  ((lastInd_weight i θ β).trans (parabolicInputWeights_add (ℓ := ℓ) θ ((Si i) + β))).trans
    (congrArg (stendhalWeight (ℓ+1)) (lastInd_blackWeight i θ β).symm)

/-- Diagrams on the parabolic weight of `θ + β` with a black strand `i` on the right, read in
`T(i + (θ + β))`. -/
def firstIndAffine :
    KLRAlgebra k S (Aₚ + Aₗ + {(Sum.inl i : I ⊕ Fin (ℓ + 1))}) →ₐ[k] T′ :=
  (TensorProductAlgebra.mk Q Λ ((Si i) + (θ + β))).comp
    ((orderProjection Q Λ ((Si i) + (θ + β))).comp
      ((StendhalAlgebraAllOrders.ofKLR k Q Λ ((Si i) + (θ + β))).comp
        (castKLR S (firstInd_klrWeight i θ β)).toAlgHom))

local notation "affT" => firstIndAffine Q Λ i θ β

theorem firstIndAffine_apply (a : KLRAlgebra k S (Aₚ + Aₗ + {(Sum.inl i : I ⊕ Fin (ℓ + 1))})) :
    affT a = tensorOfKLR Q Λ ((Si i) + (θ + β)) (castKLR S (firstInd_klrWeight i θ β) a) := rfl

theorem appendBlack_parabolicAffine (a : KLRAlgebra k S (Aₚ + Aₗ)) :
    appendBlack Q Λ i (θ + β) (parabolicAffine Q Λ θ β a) =
      affT (appendR S (Aₚ + Aₗ) (Sum.inl i) a) := by
  apply (cst).injective
  refine (castTensorProductAlgebra_appendBlack_affine Q Λ i θ β a).trans ?_
  rw [firstIndAffine_apply, castTensorProductAlgebra_mk, castKLR_castKLR, castKLR_castKLR]

/-- `[1 ⊗ a m] = ι(a ⊗ 1_i) [1 ⊗ m]` in `F_i(S N)`. -/
theorem firstIndUnit_smul (a : KLRAlgebra k S (Aₚ + Aₗ)) (y : ParabolicShuffle Q Λ θ β N) :
    (Ind.tmul (unitGen (appendBlackHom Q Λ i θ β))
        (show ParabolicStandardT Q Λ θ β N hQ from Submodule.mkQ _ (a • y)) :
          FirstIndF Q Λ i θ β N hQ) =
      affT (appendR S (Aₚ + Aₗ) (Sum.inl i) a) •
        (Ind.tmul (unitGen (appendBlackHom Q Λ i θ β))
          (show ParabolicStandardT Q Λ θ β N hQ from Submodule.mkQ _ y) :
            FirstIndF Q Λ i θ β N hQ) := by
  rw [← appendBlack_parabolicAffine, Ind.smul_tmul, ← op_smul_unitGen_appendBlack,
    Ind.op_smul_tmul]
  congr 1
  change _ = parabolicStandardAction Q Λ θ β N hQ (parabolicAffine Q Λ θ β a)
    (Submodule.mkQ _ y)
  rw [parabolicStandardAction_affine]
  rfl

/-- An idempotent of the parabolic weight whose last red strand lies after position `|α|` kills
`S N`. -/
theorem parabolicAffine_e_smul_standard (s : Seq (Aₚ + Aₗ)) (q : Fin (Multiset.card (Aₚ + Aₗ)))
    (hq : s.lbl q = .inr (Fin.last ℓ)) (hlt : (Aₚ).card < q.val)
    (m : ParabolicStandardT Q Λ θ β N hQ) :
    parabolicAffine Q Λ θ β (KLRAlgebra.e s) • m = 0 := by
  have h := affineTensorProjection_e_smul_standard Q Λ θ β N hQ
    (Seq.cast (parabolicInputWeights_add (ℓ := ℓ) θ β) s)
    (Fin.cast (congrArg Multiset.card (parabolicInputWeights_add (ℓ := ℓ) θ β)) q) hq hlt m
  change TensorProductAlgebra.mk Q Λ _ (orderProjection Q Λ _ (affineCover Q Λ _ _)) • m = 0 at h
  rw [affineCover_e] at h
  change TensorProductAlgebra.mk Q Λ _ (orderProjection Q Λ _
    (StendhalAlgebraAllOrders.ofKLR k Q Λ _ (castKLR S _ (KLRAlgebra.e s)))) • m = 0
  rw [castKLR_e]
  exact h

/-- `ι(1_s a ⊗ 1_i)` kills the unit generators of `F_i(S N)` when the last red strand of `s`
lies after position `|α|`. -/
theorem firstIndAffine_appendR_e_mul_smul (s : Seq (Aₚ + Aₗ))
    (q : Fin (Multiset.card (Aₚ + Aₗ))) (hq : s.lbl q = .inr (Fin.last ℓ))
    (hlt : (Aₚ).card < q.val) (x : KLRAlgebra k S (Aₚ + Aₗ)) (y : ParabolicShuffle Q Λ θ β N) :
    affT (appendR S (Aₚ + Aₗ) (Sum.inl i) (KLRAlgebra.e s * x)) •
      (Ind.tmul (unitGen (appendBlackHom Q Λ i θ β))
        (show ParabolicStandardT Q Λ θ β N hQ from Submodule.mkQ _ y) :
          FirstIndF Q Λ i θ β N hQ) = 0 := by
  rw [← firstIndUnit_smul, mul_smul]
  have h : (show ParabolicStandardT Q Λ θ β N hQ from
      Submodule.mkQ _ ((KLRAlgebra.e s : KLRAlgebra k S (Aₚ + Aₗ)) • (x • y))) =
      parabolicAffine Q Λ θ β (KLRAlgebra.e s) •
        (show ParabolicStandardT Q Λ θ β N hQ from Submodule.mkQ _ (x • y)) := by
    change _ = parabolicStandardAction Q Λ θ β N hQ (parabolicAffine Q Λ θ β _)
      (Submodule.mkQ _ (x • y))
    rw [parabolicStandardAction_affine]
    rfl
  rw [h, parabolicAffine_e_smul_standard Q Λ θ β N hQ s q hq hlt]
  exact Ind.tmul_zero _

omit [DecidableEq I] in
theorem lastRed_mem_lastWeight : (Sum.inr (Fin.last ℓ) : I ⊕ Fin (ℓ + 1)) ∈ Aₗ := by
  simp [stendhalWeight]

/-- **The idempotents of the slide hypothesis kill the unit generators**: if `s` ends with `i`
and lies in the block set of `(α + i, β')`, then `1_s ι(T)` kills `[1 ⊗ m]`. -/
theorem firstIndAffine_e_concat_smul (s : Seq (Aₚ + Aₗ + {(Sum.inl i : I ⊕ Fin (ℓ + 1))}))
    (hs : s ∈ concatSet (Aₚ + Aₗ) {(Sum.inl i : I ⊕ Fin (ℓ + 1))})
    (hs' : s ∈ botSet (firstQuad_h Aₚ Aₗ (Sum.inl i : I ⊕ Fin (ℓ + 1))))
    (T : TensorKLR S (Aₚ + Aₗ) {(Sum.inl i : I ⊕ Fin (ℓ + 1))})
    (y : ParabolicShuffle Q Λ θ β N) :
    affT (KLRAlgebra.e s * concat S (Aₚ + Aₗ) {(Sum.inl i : I ⊕ Fin (ℓ + 1))} T) •
      (Ind.tmul (unitGen (appendBlackHom Q Λ i θ β))
        (show ParabolicStandardT Q Λ θ β N hQ from Submodule.mkQ _ y) :
          FirstIndF Q Λ i θ β N hQ) = 0 := by
  obtain ⟨s'', b, rfl⟩ := mem_concatSet.1 hs
  obtain ⟨s₃, s₄, hs₄⟩ := (mem_botSet_iff _).1 hs'
  obtain ⟨c, -, hc⟩ := Multiset.mem_map.1
    (show (Sum.inr (Fin.last ℓ) : I ⊕ Fin (ℓ + 1)) ∈ Finset.univ.val.map s₄.1 from
      s₄.2.symm ▸ lastRed_mem_lastWeight (ℓ := ℓ) β)
  have hcA : Multiset.card (Aₚ + {(Sum.inl i : I ⊕ Fin (ℓ + 1))}) = (Aₚ).card + 1 := by simp
  have hcT : Multiset.card (Aₚ + Aₗ + {(Sum.inl i : I ⊕ Fin (ℓ + 1))}) =
      (Aₚ).card + (Aₗ).card + 1 := by simp
  have hc4 := c.2
  have hP : (Aₚ).card + 1 + c.val < Multiset.card (Aₚ + Aₗ + {(Sum.inl i : I ⊕ Fin (ℓ + 1))}) :=
    by omega
  have h1 : (seqCast (firstQuad_h Aₚ Aₗ (Sum.inl i : I ⊕ Fin (ℓ + 1)))
      (s₃.append s₄)).1 ⟨(Aₚ).card + 1 + c.val, hP⟩ =
      (s''.append b).1 ⟨(Aₚ).card + 1 + c.val, hP⟩ := by rw [hs₄]
  rw [seqCast_append_apply_ge _ _ _ _ (by simp only [hcA]; omega)] at h1
  have h2 : (s''.append b).1 ⟨(Aₚ).card + 1 + c.val, hP⟩ = .inr (Fin.last ℓ) := by
    rw [← h1]
    exact (Seq.apply_congr s₄ (b := c) (by simp only [hcA]; omega)).trans hc
  clear h1
  have hlt : (Aₚ).card + 1 + c.val < Multiset.card (Aₚ + Aₗ) := by
    by_contra hge
    push Not at hge
    rw [Seq.append_apply_ge _ _ _ hge] at h2
    have hb := b.mem ⟨(Aₚ).card + 1 + c.val - Multiset.card (Aₚ + Aₗ), by
      have := hP; simp only [Multiset.card_add, Multiset.card_singleton] at this ⊢; omega⟩
    rw [h2, Multiset.mem_singleton] at hb
    exact Sum.inr_ne_inl hb
  rw [Seq.append_apply_lt _ _ _ hlt] at h2
  induction T using TensorProduct.inductionOn with
  | add T T' hT hT' => rw [map_add, mul_add, map_add, add_smul, hT, hT', add_zero]
  | tmul x z =>
    rw [← concat_e_tmul_e, ← concat_mul, Algebra.TensorProduct.tmul_mul_tmul,
      show (KLRAlgebra.e s'' * x) ⊗ₜ[k] (KLRAlgebra.e b * z) =
        ((1 : KLRAlgebra k S (Aₚ + Aₗ)) ⊗ₜ[k] (KLRAlgebra.e b * z)) *
          ((KLRAlgebra.e s'' * x) ⊗ₜ[k] (1 : KLRAlgebra k S {(Sum.inl i : I ⊕ Fin (ℓ + 1))})) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one],
      concat_mul, ← appendR_apply, map_mul, mul_smul,
      firstIndAffine_appendR_e_mul_smul Q Λ i θ β N hQ s'' ⟨_, hlt⟩ h2 (by simp only; omega),
      smul_zero]

end Categorification.Stendhal
