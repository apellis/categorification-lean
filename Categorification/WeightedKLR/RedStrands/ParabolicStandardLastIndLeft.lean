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

/-- The unit generators `[1 ⊗ (1 ⊗ n)]` of `F_i(S N)`. -/
abbrev firstIndUnitGen (n : N) : FirstIndF Q Λ i θ β N hQ :=
  Ind.tmul (unitGen (appendBlackHom Q Λ i θ β))
    (show ParabolicStandardT Q Λ θ β N hQ from Submodule.mkQ _
      (BalancedTensor.tmul (oneBimod S Aₚ Aₗ) (show ParabolicInput Q Λ θ β N from n)))

/-- The generators `G [1 ⊗ (1 ⊗ n)]` of the image of `₁F_i N` in `F_i(S N)`. -/
abbrev firstIndGen (n : N) : FirstIndF Q Λ i θ β N hQ :=
  affT (firstG S Aₚ Aₗ (Sum.inl i : I ⊕ Fin (ℓ + 1))) • firstIndUnitGen Q Λ i θ β N hQ n

/-- **The slide on generators**: `G [1 ⊗ (1 ⊗ t n)] = ι(t ⊗_α 1_i) G [1 ⊗ (1 ⊗ n)]`. -/
theorem firstIndGen_slide (t : TensorKLR S Aₚ Aₗ) (n : N) :
    firstIndGen Q Λ i θ β N hQ (parabolicInputMap Q Λ θ β t • n) =
      affT (botConcat S (firstQuad_h Aₚ Aₗ (Sum.inl i : I ⊕ Fin (ℓ + 1)))
        (tensorAppendL S Aₚ Aₗ (Sum.inl i) t)) • firstIndGen Q Λ i θ β N hQ n := by
  have h : affT (firstG S Aₚ Aₗ (Sum.inl i : I ⊕ Fin (ℓ + 1)) *
        appendR S (Aₚ + Aₗ) (Sum.inl i) (concat S Aₚ Aₗ t)) • firstIndUnitGen Q Λ i θ β N hQ n =
      affT (botConcat S (firstQuad_h Aₚ Aₗ (Sum.inl i : I ⊕ Fin (ℓ + 1)))
        (tensorAppendL S Aₚ Aₗ (Sum.inl i) t) * firstG S Aₚ Aₗ (Sum.inl i : I ⊕ Fin (ℓ + 1))) •
        firstIndUnitGen Q Λ i θ β N hQ n := by
    let _ : Module (KLRAlgebra k S (Aₚ + Aₗ + {(Sum.inl i : I ⊕ Fin (ℓ + 1))}))
        (FirstIndF Q Λ i θ β N hQ) := Module.compHom _ (firstIndAffine Q Λ i θ β).toRingHom
    have _ : IsScalarTower k (KLRAlgebra k S (Aₚ + Aₗ + {(Sum.inl i : I ⊕ Fin (ℓ + 1))}))
        (FirstIndF Q Λ i θ β N hQ) := ⟨fun c a x => by
      change affT (c • a) • x = c • (affT a • x)
      rw [map_smul, smul_assoc]⟩
    exact KLRAlgebra.firstG_mul_appendR_concat_smul
      (u := firstIndUnitGen Q Λ i θ β N hQ n)
      (fun s hs hs' T => firstIndAffine_e_concat_smul Q Λ i θ β N hQ s hs hs' T _) t
  rw [map_mul, map_mul, mul_smul, mul_smul] at h
  rw [firstIndGen, firstIndGen, ← h]
  congr 1
  refine Eq.trans ?_ (firstIndUnit_smul Q Λ i θ β N hQ _ _)
  rw [concat_smul_tmul_oneBimod]
  rfl

local notation "hA₁" => prefixWeight_addBlack (ℓ := ℓ) i θ

/-- Juxtaposition of `ι(t ⊗_α 1_i)` modulo smaller suffixes is the class of the bottom
juxtaposition read in `T(i + (θ + β))`. -/
theorem suffixConcat_tensorAppendL (t : TensorKLR S Aₚ Aₗ) :
    suffixConcat Q Λ p₁ (parabolicInputWeights_add (ℓ := ℓ) ((Si i) + θ) β)
        (castTensor S hA₁ rfl (tensorAppendL S Aₚ Aₗ (Sum.inl i) t)) =
      (I₁).ringCon.mk' (cst₁ (affT (botConcat S (firstQuad_h Aₚ Aₗ (Sum.inl i : I ⊕ Fin (ℓ + 1)))
        (tensorAppendL S Aₚ Aₗ (Sum.inl i) t)))) := by
  rw [firstIndAffine_apply, castTensorProductAlgebra_mk]
  refine congrArg (fun x => (I₁).ringCon.mk' (TensorProductAlgebra.mk Q Λ _
    (orderProjection Q Λ _ (StendhalAlgebraAllOrders.ofKLR k Q Λ _ x)))) ?_
  change castKLR S _ (concat S _ _ _) = castKLR S _ (castKLR S _ _)
  rw [botConcat_apply, castAlg_eq_castKLR, ← castKLR_concat, castKLR_castKLR, castKLR_castKLR,
    castKLR_castKLR]

local notation "ψL₁" => lastRedLayerAction Q Λ p₁
  (LastRedWeightSplit.content (((Si i) + θ) + β) (firstIndSplit i θ β) ℓ)
  (LastRedWeightSplit.length (((Si i) + θ) + β) (firstIndSplit i θ β) ℓ)

/-- The layer quotient acts on the generators through `appendBlack ⊗ 1`:
`ψ(ι(d) ⊗ 1) G [1 ⊗ (1 ⊗ n)] = G [1 ⊗ (1 ⊗ d n)]`. -/
theorem firstIndLayerAction_appendLeft (t : TensorKLR S Aₚ Aₗ) (n : N) :
    firstIndLayerAction Q Λ i θ β N hQ
        (ψL₁ (parabolicAppendLeft Q Λ i θ β (parabolicInputMap Q Λ θ β t)))
        (firstIndGen Q Λ i θ β N hQ n) =
      firstIndGen Q Λ i θ β N hQ (parabolicInputMap Q Λ θ β t • n) := by
  rw [← parabolicInputMap_tensorAppendL_left,
    show ψL₁ (parabolicInputMap Q Λ ((Si i) + θ) β (castTensor S hA₁ rfl
        (tensorAppendL S Aₚ Aₗ (Sum.inl i) t))) = _ from
      (suffixConcat_eq_lastRedLayerAction Q Λ p₁ _ _
        (parabolicInputWeights_add (ℓ := ℓ) ((Si i) + θ) β) _).symm,
    suffixConcat_tensorAppendL, firstIndLayerAction_mk, firstIndGen_slide]
  change (cst₁).symm (cst₁ _) • firstIndGen Q Λ i θ β N hQ n = _
  rw [AlgEquiv.symm_apply_apply]

theorem firstIndGen_add (n n' : N) :
    firstIndGen Q Λ i θ β N hQ (n + n') =
      firstIndGen Q Λ i θ β N hQ n + firstIndGen Q Λ i θ β N hQ n' := by
  unfold firstIndGen firstIndUnitGen
  dsimp only
  erw [BalancedTensor.tmul_add, map_add, Ind.tmul_add, smul_add]

/-- **`₁F_i N`**: induction along `appendBlack ⊗ 1`. -/
abbrev FirstIndLeft := IndK k N (leftAppendHom Q Λ i θ β)

local notation "Fl" => FirstIndLeft Q Λ i θ β N
local notation "ρ₁" => firstIndLayerAction Q Λ i θ β N hQ

/-- **The map `₁F_i N → F_i(S N)`**, `z ⊗ n ↦ ψ(z) G [1 ⊗ (1 ⊗ n)]`. -/
def firstIndLeftMap : Ind N (leftAppendHom Q Λ i θ β) →+ FirstIndF Q Λ i θ β N hQ :=
  Ind.liftAdd (φ := leftAppendHom Q Λ i θ β)
    (fun z n => ρ₁ (ψL₁ z.1) (firstIndGen Q Λ i θ β N hQ n))
    (fun z z' n => by
      change ρ₁ (ψL₁ (z.1 + z'.1)) _ = _
      rw [map_add, map_add, LinearMap.add_apply])
    (fun z n n' => by rw [firstIndGen_add, map_add])
    (fun z a n => by
      obtain ⟨t, rfl⟩ := parabolicInputMap_surjective Q Λ θ β a
      change ρ₁ (ψL₁ (z.1 * parabolicAppendLeft Q Λ i θ β (parabolicInputMap Q Λ θ β t))) _ = _
      rw [map_mul, map_mul, Module.End.mul_apply, firstIndLayerAction_appendLeft])

theorem firstIndLeftMap_tmul (z : Corner (leftAppendHom Q Λ i θ β)) (n : N) :
    firstIndLeftMap Q Λ i θ β N hQ (Ind.tmul z n) =
      ρ₁ (ψL₁ z.1) (firstIndGen Q Λ i θ β N hQ n) := rfl

/-- `firstIndLeftMap` intertwines the factor algebra with the layer action. -/
theorem firstIndLeftMap_smul (d : parabolicFactorAlgebra Q Λ ((Si i) + θ) β)
    (y : Ind N (leftAppendHom Q Λ i θ β)) :
    firstIndLeftMap Q Λ i θ β N hQ (d • y) = ρ₁ (ψL₁ d) (firstIndLeftMap Q Λ i θ β N hQ y) := by
  induction y using Ind.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul z n =>
    rw [Ind.smul_tmul, firstIndLeftMap_tmul, firstIndLeftMap_tmul]
    change ρ₁ (ψL₁ (d * z.1)) _ = _
    rw [map_mul, map_mul, Module.End.mul_apply]
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, map_add]

theorem firstIndLeftMap_algebraMap_smul (c : k) (y : Fl) :
    firstIndLeftMap Q Λ i θ β N hQ (show Ind N (leftAppendHom Q Λ i θ β) from c • y) =
      c • firstIndLeftMap Q Λ i θ β N hQ y := by
  have h1 := firstIndLeftMap_smul Q Λ i θ β N hQ 1 y
  erw [one_smul] at h1
  rw [← IndK.algebraMap_smul]
  dsimp only
  erw [firstIndLeftMap_smul Q Λ i θ β N hQ _ y]
  rw [Algebra.algebraMap_eq_smul_one, map_smul,
    map_smul, LinearMap.smul_apply, ← h1]

local notation "Aₚ₁" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ ((Si i) + θ))
local notation "PI₁" => ParabolicInput Q Λ ((Si i) + θ) β Fl
local notation "H₁" => parabolicInputWeights_add (ℓ := ℓ) ((Si i) + θ) β

/-- Diagrams on the parabolic weight of `(i + θ) + β` acting on `F_i(S N)`. -/
def firstIndKLRAction :
    KLRAlgebra k S (Aₚ₁ + Aₗ) →ₐ[k] Module.End k (FirstIndF Q Λ i θ β N hQ) :=
  (firstIndAction Q Λ i θ β N hQ).comp ((TensorProductAlgebra.mk Q Λ (((Si i) + θ) + β)).comp
    ((orderProjection Q Λ (((Si i) + θ) + β)).comp
      ((StendhalAlgebraAllOrders.ofKLR k Q Λ (((Si i) + θ) + β)).comp (castKLR S H₁).toAlgHom)))

local notation "κ₁" => firstIndKLRAction Q Λ i θ β N hQ

theorem firstIndKLRAction_apply (a : KLRAlgebra k S (Aₚ₁ + Aₗ)) :
    κ₁ a = firstIndAction Q Λ i θ β N hQ (parabolicAffine Q Λ ((Si i) + θ) β a) := rfl

/-- Juxtaposition acts on `F_i(S N)` through the layer action of the factor algebra. -/
theorem firstIndKLRAction_concat (t : TensorKLR S Aₚ₁ Aₗ) :
    κ₁ (concat S Aₚ₁ Aₗ t) = ρ₁ (ψL₁ (parabolicInputMap Q Λ ((Si i) + θ) β t)) := by
  rw [show ψL₁ (parabolicInputMap Q Λ ((Si i) + θ) β t) = _ from
    (suffixConcat_eq_lastRedLayerAction Q Λ p₁ _ _ H₁ t).symm]
  rfl

/-- The red-ordered idempotent acts as the identity on `F_i(S N)`. -/
theorem firstIndKLRAction_eSum :
    κ₁ (eSum S (parabolicOrderedLoadings (ℓ := ℓ) ((Si i) + θ) β)) = 1 := by
  rw [firstIndKLRAction_apply, parabolicOrderedLoadings_eq_redOrderedSet, parabolicAffine,
    castKLR_eSum_redOrderedSet, orderProjection_ofKLR_eSum_redOrderedSet, map_one, map_one]

/-- `firstIndLeftMap` as a `k`-linear map on the input module. -/
def firstIndLeftMapK : PI₁ →ₗ[k] FirstIndF Q Λ i θ β N hQ where
  toFun y := firstIndLeftMap Q Λ i θ β N hQ y
  map_add' y y' := map_add (firstIndLeftMap Q Λ i θ β N hQ) y y'
  map_smul' c y := firstIndLeftMap_algebraMap_smul Q Λ i θ β N hQ c y

local notation "Ψ₁" => firstIndLeftMapK Q Λ i θ β N hQ

theorem firstIndLeftMapK_smul (t : TensorKLR S Aₚ₁ Aₗ) (y : PI₁) :
    Ψ₁ (t • y) = κ₁ (concat S Aₚ₁ Aₗ t) (Ψ₁ y) := by
  rw [firstIndKLRAction_concat]
  exact firstIndLeftMap_smul Q Λ i θ β N hQ (parabolicInputMap Q Λ ((Si i) + θ) β t) y

/-- The bilinear map `(r, y) ↦ κ(r) Ψ(y)`. -/
def firstIndBil :
    IndBimod S Aₚ₁ Aₗ →ₗ[k] PI₁ →ₗ[k] FirstIndF Q Λ i θ β N hQ :=
  LinearMap.mk₂ k (fun r y => κ₁ r.1 (Ψ₁ y))
    (fun r r' y => by rw [Submodule.coe_add, map_add, LinearMap.add_apply])
    (fun c r y => by
      change κ₁ (c • r.1) (Ψ₁ y) = _
      rw [map_smul, LinearMap.smul_apply])
    (fun r y y' => by rw [map_add, map_add])
    (fun c r y => by rw [map_smul, map_smul])

/-- The map from the shuffle module of `₁F_i N` to `F_i(S N)`, `r ⊗ y ↦ κ(r) Ψ(y)`. -/
def firstIndShuffle :
    ParabolicShuffle Q Λ ((Si i) + θ) β Fl →ₗ[k] FirstIndF Q Λ i θ β N hQ :=
  BalancedTensor.lift (firstIndBil Q Λ i θ β N hQ) (fun r a y => by
    change κ₁ (r.1 * concat S Aₚ₁ Aₗ a) (Ψ₁ y) = κ₁ r.1 (Ψ₁ (a • y))
    rw [map_mul, Module.End.mul_apply, firstIndLeftMapK_smul])

theorem firstIndShuffle_tmul (r : IndBimod S Aₚ₁ Aₗ) (y : PI₁) :
    firstIndShuffle Q Λ i θ β N hQ (BalancedTensor.tmul r y) = κ₁ r.1 (Ψ₁ y) := rfl

theorem firstIndShuffle_smul (b : KLRAlgebra k S (Aₚ₁ + Aₗ))
    (x : ParabolicShuffle Q Λ ((Si i) + θ) β Fl) :
    firstIndShuffle Q Λ i θ β N hQ (b • x) = κ₁ b (firstIndShuffle Q Λ i θ β N hQ x) := by
  induction x using BalancedTensor.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero]
  | tmul r y =>
    rw [BalancedTensor.smul_tmul', firstIndShuffle_tmul, firstIndShuffle_tmul]
    change κ₁ (b * r.1) _ = _
    rw [map_mul, Module.End.mul_apply]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add]

/-- **`S(₁F_i N)`** as a module over `T(i + (θ + β))`. -/
def FirstIndStandardT (_hQ : KLRSymm Q) : Type _ := ParabolicStandard Q Λ ((Si i) + θ) β Fl

instance : AddCommGroup (FirstIndStandardT Q Λ i θ β N hQ) :=
  inferInstanceAs (AddCommGroup (ParabolicStandard Q Λ ((Si i) + θ) β Fl))
instance : Module k (FirstIndStandardT Q Λ i θ β N hQ) :=
  inferInstanceAs (Module k (ParabolicStandard Q Λ ((Si i) + θ) β Fl))
instance : Module T′ (FirstIndStandardT Q Λ i θ β N hQ) :=
  Module.compHom (ParabolicStandard Q Λ ((Si i) + θ) β Fl)
    ((parabolicStandardAction Q Λ ((Si i) + θ) β Fl hQ).comp (cst₁).toAlgHom).toRingHom

/-- The quotient map onto `S(₁F_i N)`. -/
abbrev firstIndMk :
    ParabolicShuffle Q Λ ((Si i) + θ) β Fl →ₗ[k] FirstIndStandardT Q Λ i θ β N hQ :=
  (excludedSpace (parabolicShuffleAction Q Λ ((Si i) + θ) β Fl)
    (parabolicOrderedLoadings (ℓ := ℓ) ((Si i) + θ) β)).mkQ

/-- **The map `δ₁ : S(₁F_i N) → F_i(S N)`** on underlying `k`-modules. -/
def firstIndDelta : FirstIndStandardT Q Λ i θ β N hQ →ₗ[k] FirstIndF Q Λ i θ β N hQ :=
  (excludedSpace (parabolicShuffleAction Q Λ ((Si i) + θ) β Fl)
    (parabolicOrderedLoadings (ℓ := ℓ) ((Si i) + θ) β)).liftQ
    (firstIndShuffle Q Λ i θ β N hQ) (fun x hx => by
      rw [LinearMap.mem_ker]
      have hx' : eSum S (parabolicOrderedLoadings (ℓ := ℓ) ((Si i) + θ) β) • x = 0 := hx
      rw [← Module.End.one_apply (R := k) (firstIndShuffle Q Λ i θ β N hQ x),
        ← firstIndKLRAction_eSum, ← firstIndShuffle_smul, hx', map_zero])

theorem firstIndDelta_mk (x : ParabolicShuffle Q Λ ((Si i) + θ) β Fl) :
    firstIndDelta Q Λ i θ β N hQ (firstIndMk Q Λ i θ β N hQ x) =
      firstIndShuffle Q Λ i θ β N hQ x := rfl

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
theorem firstIndMk_smul_affine (a : KLRAlgebra k S (Aₚ₁ + Aₗ))
    (x : ParabolicShuffle Q Λ ((Si i) + θ) β Fl) :
    (cst₁).symm (parabolicAffine Q Λ ((Si i) + θ) β a) • firstIndMk Q Λ i θ β N hQ x =
      firstIndMk Q Λ i θ β N hQ (a • x) := by
  change parabolicStandardAction Q Λ ((Si i) + θ) β Fl hQ ((cst₁) ((cst₁).symm _)) _ = _
  rw [AlgEquiv.apply_symm_apply, parabolicStandardAction_affine]
  rfl

/-- `δ₁` is `T(i + (θ + β))`-linear. -/
theorem firstIndDelta_smul (t : T′) (m : FirstIndStandardT Q Λ i θ β N hQ) :
    firstIndDelta Q Λ i θ β N hQ (t • m) = t • firstIndDelta Q Λ i θ β N hQ m := by
  obtain ⟨a, ha⟩ := parabolicAffine_surjective Q Λ ((Si i) + θ) β ((cst₁) t)
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (excludedSpace
    (parabolicShuffleAction Q Λ ((Si i) + θ) β Fl)
    (parabolicOrderedLoadings (ℓ := ℓ) ((Si i) + θ) β)) m
  have ht : t = (cst₁).symm (parabolicAffine Q Λ ((Si i) + θ) β a) := by
    rw [ha, AlgEquiv.symm_apply_apply]
  rw [ht]
  erw [firstIndMk_smul_affine, firstIndDelta_mk, firstIndDelta_mk, firstIndShuffle_smul]
  rfl

/-- **The map `δ₁ : S(₁F_i N) → F_i(S N)`** of `T(i + (θ + β))`-modules
(Webster, arXiv:1309.3796v3, proof of Prop. 5.5). -/
def firstIndDeltaT : FirstIndStandardT Q Λ i θ β N hQ →ₗ[T′] FirstIndF Q Λ i θ β N hQ where
  toFun := firstIndDelta Q Λ i θ β N hQ
  map_add' := map_add _
  map_smul' := firstIndDelta_smul Q Λ i θ β N hQ

end Categorification.Stendhal
