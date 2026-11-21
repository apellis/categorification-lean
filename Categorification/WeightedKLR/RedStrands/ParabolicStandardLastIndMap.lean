/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastInduction

/-!
# The map `F_i(S N) → S(₂F_i N)`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `F`-part. The functor `F_i` on modules over `T(θ + β)` is induction along
Webster's map `appendBlack`, which adds a black strand labelled `i` on the right. The map
`S N → S(₂F_i N)` of `lastIndStandard` intertwines `t` with `appendBlack t`
(`lastIndStandard_smul`), so it induces a map of `T(i + (θ + β))`-modules
`F_i(S N) → S(₂F_i N)`, `z ⊗ m ↦ z · g(m)` (`lastIndQuotientMap`).

## Main definitions

* `ParabolicStandardT`: standardization `S N` as a module over `T(θ + β)`.
* `LastIndStandardT`: `S(₂F_i N)` as a module over `T(i + (θ + β))`.
* `lastIndQuotientMap`: the map `F_i(S N) → S(₂F_i N)`.

## Main results

* `lastIndQuotientMap_surjective`: `F_i(S N) → S(₂F_i N)` is surjective.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open MulOpposite

variable {I k : Type*} [DecidableEq I] [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν ν' ν₂ ν₂' : Multiset I}

theorem castBimod_oneBimod (h : ν = ν₂) (h' : ν' = ν₂') :
    castBimod Q h h' (oneBimod Q ν ν') = oneBimod Q ν₂ ν₂' := by
  subst h h'; rfl

/-- `ι(1_{ν,ν'} ⊗ 1_i) = 1_{ν,ν'+i} · ι(1 ⊗ 1_{ν',i})`. -/
theorem indAppendBimod_oneBimod (i : I) :
    indAppendBimod (i := i) (oneBimod Q ν ν') =
      op (tensorAppendR Q ν ν' i 1) • oneBimod Q ν (ν' + {i}) :=
  Subtype.ext (by
    rw [coe_indAppendBimod, coe_oneBimod, ← concat_one, castKLR_appendR_concat, coe_op_smul,
      unop_op, coe_oneBimod, oneConcat_mul_concat])

/-- `Φ(1_{ν,ν'} ⊗ n) = 1_{ν,ν'+i} ⊗ n`. -/
theorem indAppend_tmul_oneBimod {i : I} {N : Type*} [AddCommGroup N] [Module k N]
    [Module (TensorKLR Q ν (ν' + ({i} : Multiset I))) N]
    [IsScalarTower k (TensorKLR Q ν (ν' + ({i} : Multiset I))) N]
    (n : ResRight Q ν ν' i N) :
    indAppend (BalancedTensor.tmul (oneBimod Q ν ν') n) =
      BalancedTensor.tmul (oneBimod Q ν (ν' + {i})) n.val := by
  rw [indAppend_tmul, indAppendBimod_oneBimod, BalancedTensor.op_smul_tmul]
  exact congrArg _ n.prop

/-- Every element of `R(ν + ν') 1_{ν,ν'}` is `r · 1_{ν,ν'}`. -/
theorem val_smul_oneBimod (r : IndBimod Q ν ν') :
    (r : KLRAlgebra k Q (ν + ν')) • oneBimod Q ν ν' = r :=
  Subtype.ext r.2

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ β : Multiset I)

local notation "Si" j => (Singleton.singleton j : Multiset I)

variable (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)

local notation "Fr" => LastIndRight Q Λ i θ β N
local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "Aₗ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
  (stendhalWeight 1 β)
local notation "Aₗ'" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
  (stendhalWeight 1 ((Si i) + β))

/-- Standardization `S N` viewed as a module over `T(θ + β)`. -/
def ParabolicStandardT (_hQ : KLRSymm Q) : Type _ := ParabolicStandard Q Λ θ β N

instance : AddCommGroup (ParabolicStandardT Q Λ θ β N hQ) :=
  inferInstanceAs (AddCommGroup (ParabolicStandard Q Λ θ β N))
instance : Module k (ParabolicStandardT Q Λ θ β N hQ) :=
  inferInstanceAs (Module k (ParabolicStandard Q Λ θ β N))
instance : Module (TensorProductAlgebra k Q Λ (θ + β)) (ParabolicStandardT Q Λ θ β N hQ) :=
  Module.compHom (ParabolicStandard Q Λ θ β N) (parabolicStandardAction Q Λ θ β N hQ).toRingHom

/-- `S(₂F_i N)` viewed as a module over `T(i + (θ + β))`. -/
def LastIndStandardT (_hQ : KLRSymm Q) : Type _ := ParabolicStandard Q Λ θ ((Si i) + β) Fr

instance : AddCommGroup (LastIndStandardT Q Λ i θ β N hQ) :=
  inferInstanceAs (AddCommGroup (ParabolicStandard Q Λ θ ((Si i) + β) Fr))
instance : Module k (LastIndStandardT Q Λ i θ β N hQ) :=
  inferInstanceAs (Module k (ParabolicStandard Q Λ θ ((Si i) + β) Fr))
instance : Module (TensorProductAlgebra k Q Λ ((Si i) + (θ + β)))
    (LastIndStandardT Q Λ i θ β N hQ) :=
  Module.compHom (ParabolicStandard Q Λ θ ((Si i) + β) Fr)
    ((parabolicStandardAction Q Λ θ ((Si i) + β) Fr hQ).comp
      (castTensorProductAlgebra Q Λ (lastInd_blackWeight i θ β)).toAlgHom).toRingHom

/-- Webster's `appendBlack` as a nonunital ring map. -/
abbrev appendBlackHom :
    TensorProductAlgebra k Q Λ (θ + β) →ₙ+* TensorProductAlgebra k Q Λ ((Si i) + (θ + β)) :=
  NonUnitalRingHomClass.toNonUnitalRingHom (appendBlack Q Λ i (θ + β))

/-- **`F_i(S N)`**: induction of `S N` along `appendBlack`. -/
abbrev LastIndF := Ind (ParabolicStandardT Q Λ θ β N hQ) (appendBlackHom Q Λ i θ β)

/-- The map `S N → S(₂F_i N)` between the module wrappers. -/
def lastIndStandardT :
    ParabolicStandardT Q Λ θ β N hQ → LastIndStandardT Q Λ i θ β N hQ :=
  fun m => lastIndStandard Q Λ i θ β N m

theorem lastIndStandardT_add (m m' : ParabolicStandardT Q Λ θ β N hQ) :
    lastIndStandardT Q Λ i θ β N hQ (m + m') =
      lastIndStandardT Q Λ i θ β N hQ m + lastIndStandardT Q Λ i θ β N hQ m' :=
  map_add (lastIndStandard Q Λ i θ β N) m m'

theorem lastIndStandardT_smul (t : TensorProductAlgebra k Q Λ (θ + β))
    (m : ParabolicStandardT Q Λ θ β N hQ) :
    lastIndStandardT Q Λ i θ β N hQ (t • m) =
      appendBlack Q Λ i (θ + β) t • lastIndStandardT Q Λ i θ β N hQ m :=
  lastIndStandard_smul Q Λ i θ β N hQ t m

/-- **The map `F_i(S N) → S(₂F_i N)`**, `z ⊗ m ↦ z · g(m)`. -/
def lastIndQuotientMap :
    LastIndF Q Λ i θ β N hQ →ₗ[TensorProductAlgebra k Q Λ ((Si i) + (θ + β))]
      LastIndStandardT Q Λ i θ β N hQ :=
  Ind.lift (fun z m => z.1 • lastIndStandardT Q Λ i θ β N hQ m)
    (fun z z' m => add_smul _ _ _)
    (fun z m m' => by rw [lastIndStandardT_add, smul_add])
    (fun z a m => by
      rw [op_smul_val, lastIndStandardT_smul, mul_smul]
      rfl)
    (fun b z m => mul_smul _ _ _)

@[simp] theorem lastIndQuotientMap_tmul (z : Corner (appendBlackHom Q Λ i θ β))
    (m : ParabolicStandardT Q Λ θ β N hQ) :
    lastIndQuotientMap Q Λ i θ β N hQ (Ind.tmul z m) =
      z.1 • lastIndStandardT Q Λ i θ β N hQ m := rfl

/-- The parabolic input map `R(α) ⊗ R(δ) → T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)` is surjective. -/
theorem parabolicInputMap_surjective (θ β : Multiset I) :
    Function.Surjective (parabolicInputMap Q Λ θ β) :=
  Algebra.TensorProduct.map_surjective _ _ (parabolicPrefixProjection_surjective Q Λ θ)
    (parabolicLastCyclotomic_surjective Q Λ β)

/-- `lastIndShuffle (1 ⊗ n) = 1 ⊗ (1 ⊗ n)`. -/
theorem lastIndShuffle_tmul_oneBimod (n : ParabolicInput Q Λ θ β N) :
    lastIndShuffle Q Λ i θ β N (BalancedTensor.tmul (oneBimod (stendhalQ Q Λ) Aₚ Aₗ) n) =
      BalancedTensor.tmul (oneBimod (stendhalQ Q Λ) Aₚ Aₗ')
        ((lastIndInputEquiv Q Λ i θ β N) (lastIndUnit Q Λ i θ β N n).val) := by
  have h2 := congrArg (indCast (Q := stendhalQ Q Λ) rfl (lastWeight_addBlack (ℓ := ℓ) i β)
    (lastIndInputEquiv Q Λ i θ β N) (fun _ _ => rfl))
    (indAppend_tmul_oneBimod (lastIndUnit Q Λ i θ β N n))
  exact h2.trans ((indCast_tmul (Q := stendhalQ Q Λ) rfl (lastWeight_addBlack (ℓ := ℓ) i β)
    (lastIndInputEquiv Q Λ i θ β N) (fun _ _ => rfl) _ _).trans
    (congrArg (BalancedTensor.tmul · _) (castBimod_oneBimod _ _)))

/-- The quotient map onto `S(₂F_i N)`. -/
abbrev lastIndMk : ParabolicShuffle Q Λ θ ((Si i) + β) Fr →ₗ[k] LastIndStandardT Q Λ i θ β N hQ :=
  (excludedSpace (parabolicShuffleAction Q Λ θ ((Si i) + β) Fr)
    (parabolicOrderedLoadings (ℓ := ℓ) θ ((Si i) + β))).mkQ

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- KLR elements act on `S(₂F_i N)` through `T(i + (θ + β))`. -/
theorem exists_lastIndMk_smul (a : KLRAlgebra k (stendhalQ Q Λ)
      (Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ) +
        Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
          (stendhalWeight 1 ((Si i) + β))))
    (x : ParabolicShuffle Q Λ θ ((Si i) + β) Fr) :
    ∃ t : TensorProductAlgebra k Q Λ ((Si i) + (θ + β)),
      lastIndMk Q Λ i θ β N hQ (a • x) = t • lastIndMk Q Λ i θ β N hQ x :=
  ⟨(castTensorProductAlgebra Q Λ (lastInd_blackWeight i θ β)).symm
      (TensorProductAlgebra.mk Q Λ _ (orderProjection Q Λ _
        (StendhalAlgebraAllOrders.ofKLR k Q Λ _
          (castKLR (stendhalQ Q Λ) (parabolicInputWeights_add (ℓ := ℓ) θ ((Si i) + β)) a)))),
    by
      change _ = parabolicStandardAction Q Λ θ ((Si i) + β) Fr hQ
        (castTensorProductAlgebra Q Λ (lastInd_blackWeight i θ β)
          ((castTensorProductAlgebra Q Λ (lastInd_blackWeight i θ β)).symm _)) _
      rw [AlgEquiv.apply_symm_apply, parabolicStandardAction_affine]
      rfl⟩

/-- **`F_i(S N) → S(₂F_i N)` is surjective**: `S(₂F_i N)` is generated over
`T(i + (θ + β))` by the image of `S N`. -/
theorem lastIndQuotientMap_surjective :
    Function.Surjective (lastIndQuotientMap Q Λ i θ β N hQ) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  set R := LinearMap.range (lastIndQuotientMap Q Λ i θ β N hQ)
  have hK : ∀ a x, lastIndMk Q Λ i θ β N hQ x ∈ R →
      lastIndMk Q Λ i θ β N hQ (a • x) ∈ R := fun a x hx => by
    obtain ⟨t, ht⟩ := exists_lastIndMk_smul Q Λ i θ β N hQ a x
    rw [ht]; exact R.smul_mem t hx
  have hg : ∀ m, lastIndStandardT Q Λ i θ β N hQ m ∈ R := fun m =>
    ⟨Ind.tmul (unitGen (appendBlackHom Q Λ i θ β)) m, by
      rw [lastIndQuotientMap_tmul]
      refine (lastIndStandardT_smul Q Λ i θ β N hQ 1 m).symm.trans ?_
      rw [one_smul]⟩
  -- the generators `1 ⊗ (1 ⊗ n)`
  have h0 : ∀ n : ParabolicInput Q Λ θ β N, lastIndMk Q Λ i θ β N hQ
      (BalancedTensor.tmul (oneBimod (stendhalQ Q Λ) Aₚ Aₗ')
        ((lastIndInputEquiv Q Λ i θ β N) (lastIndUnit Q Λ i θ β N n).val)) ∈ R := by
    intro n
    rw [← lastIndShuffle_tmul_oneBimod]
    exact hg (Submodule.mkQ _ (BalancedTensor.tmul (oneBimod (stendhalQ Q Λ) Aₚ Aₗ) n))
  have h1 : ∀ x : ParabolicInput Q Λ θ ((Si i) + β) Fr, lastIndMk Q Λ i θ β N hQ
      (BalancedTensor.tmul (oneBimod (stendhalQ Q Λ) Aₚ Aₗ') x) ∈ R := by
    intro x
    refine Ind.induction_on (motive := fun y : Ind N (parabolicRightHom Q Λ i θ β) =>
      lastIndMk Q Λ i θ β N hQ (BalancedTensor.tmul (oneBimod (stendhalQ Q Λ) Aₚ Aₗ')
        (show ParabolicInput Q Λ θ ((Si i) + β) Fr from y)) ∈ R) x ?_ ?_ ?_
    · change lastIndMk Q Λ i θ β N hQ (BalancedTensor.tmul _
        (0 : ParabolicInput Q Λ θ ((Si i) + β) Fr)) ∈ R
      rw [BalancedTensor.tmul_zero, map_zero]; exact R.zero_mem
    · intro z n
      obtain ⟨t, ht⟩ := parabolicInputMap_surjective Q Λ θ ((Si i) + β) z.1
      have hz : (show ParabolicInput Q Λ θ ((Si i) + β) Fr from Ind.tmul z n) =
          t • (lastIndInputEquiv Q Λ i θ β N) (lastIndUnit Q Λ i θ β N n).val := by
        change _ = parabolicInputMap Q Λ θ ((Si i) + β) t •
          (Ind.tmul (unitGen (parabolicRightHom Q Λ i θ β)) n : Ind N _)
        rw [ht, Ind.smul_tmul]
        exact congrArg (Ind.tmul · n)
          (Subtype.ext z.2.symm : z = z.1 • unitGen (parabolicRightHom Q Λ i θ β))
      rw [hz, ← concat_smul_tmul_oneBimod]
      exact hK _ _ (h0 n)
    · intro s t hs ht
      change lastIndMk Q Λ i θ β N hQ (BalancedTensor.tmul _
        ((show ParabolicInput Q Λ θ ((Si i) + β) Fr from s) +
          (show ParabolicInput Q Λ θ ((Si i) + β) Fr from t))) ∈ R
      rw [BalancedTensor.tmul_add, map_add]; exact R.add_mem hs ht
  have h2 : ∀ y, lastIndMk Q Λ i θ β N hQ y ∈ R := by
    intro y
    induction y using BalancedTensor.induction_on with
    | zero => rw [map_zero]; exact R.zero_mem
    | tmul r x =>
      rw [← val_smul_oneBimod r, ← BalancedTensor.smul_tmul']
      exact hK _ _ (h1 x)
    | add s t hs ht => rw [map_add]; exact R.add_mem hs ht
  intro v _
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ v
  exact h2 y

end Categorification.Stendhal
