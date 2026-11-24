/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastBlack

/-!
# The last-strand sequence of `E_i(S N)` over the tensor product algebra

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `E`-part. Write `θ = i + θ₀` and `β = i + β₀`. The terms of the short exact
sequence

`0 → S(₂E_i N) → E_i(S N) → S(₁E_i N) → 0`

of `ParabolicStandardLastBlack.lean` are modules over `T(θ₀ + β)`: `E_i(S N)` through
`appendBlack`, `S(₁E_i N)` through the standardization action, and `S(₂E_i N)` through the
standardization action transported along `θ₀ + β = θ + β₀`. Both maps of the sequence are
`T(θ₀ + β)`-linear (`lastBlackResTwoT`, `lastBlackResOneT`), so the sequence is a short exact
sequence of `T(θ₀ + β)`-modules (`lastBlackResTwoT_injective`, `lastBlackResT_exact`,
`lastBlackResOneT_surjective`). Gradings are not modelled.

The proof reduces to the images in `T(θ₀ + β)` of KLR diagrams, on which the three actions are
the actions on the parabolic shuffle modules, and uses that `Φ` and `π` intertwine a diagram
`a` with `ι(a ⊗ 1_i)` (`indAppend_smul`, `lastProj_smul`).

## Main definitions

* `LastBlackTwoT`, `LastBlackOneT`: `S(₂E_i N)` and `S(₁E_i N)` as `T(θ₀ + β)`-modules.
* `lastBlackResTwoT`, `lastBlackResOneT`: the maps of the sequence as `T(θ₀ + β)`-linear maps.

## Main results

* `lastBlackResTwoT_injective`, `lastBlackResT_exact`, `lastBlackResOneT_surjective`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra IdempotentQuotient
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Generic

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)

local notation "S" => stendhalQ Q Λ

/-- Every element of `T(ν)` is the image of a KLR diagram on any weight equal to that of `ν`. -/
theorem exists_tensorOfKLR_castKLR_eq (ν : Multiset I) {W : Multiset (I ⊕ Fin (ℓ + 1))}
    (h : W = stendhalWeight (ℓ + 1) ν) (t : TensorProductAlgebra k Q Λ ν) :
    ∃ c : KLRAlgebra k S W, tensorOfKLR Q Λ ν (castKLR S h c) = t := by
  obtain ⟨a, rfl⟩ :=
    ((show Function.Surjective (TensorProductAlgebra.mk Q Λ ν) from RingCon.mkₐ_surjective _).comp
      ((orderProjection_surjective Q Λ ν).comp
        (StendhalAlgebraAllOrders.ofKLR_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν)))) t
  obtain ⟨c, rfl⟩ := (castKLR S h).surjective a
  exact ⟨c, rfl⟩

/-- Transport of the image of a KLR diagram along an equality of black weights. -/
theorem castTensorProductAlgebra_tensorOfKLR_castKLR {ν ν' : Multiset I} (hν : ν = ν')
    {W : Multiset (I ⊕ Fin (ℓ + 1))} (h : W = stendhalWeight (ℓ + 1) ν)
    (h' : W = stendhalWeight (ℓ + 1) ν') (c : KLRAlgebra k S W) :
    castTensorProductAlgebra Q Λ hν (tensorOfKLR Q Λ ν (castKLR S h c)) =
      tensorOfKLR Q Λ ν' (castKLR S h' c) := by
  subst hν; rfl

end Generic

section BlackAppendGeneric

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I)

local notation "S" => stendhalQ Q Λ

private theorem appendBlackStendhal_orderProjection_id' (ν : Multiset I)
    (y : StendhalAlgebraAllOrders k Q Λ ν) :
    appendBlackStendhal Q Λ i ν (orderProjection Q Λ ν y) =
      orderProjection Q Λ ((Singleton.singleton i : Multiset I) + ν)
        (appendBlackAllOrders Q Λ i ν y).val :=
  appendBlackStendhal_orderProjection Q Λ id i ν y

/-- **`appendBlack` on the image of a diagram `c`** is the image of `ι(c ⊗ 1_i)`. -/
theorem appendBlack_tensorOfKLR_castKLR (ν : Multiset I) {W : Multiset (I ⊕ Fin ℓ)}
    (h : W = stendhalWeight ℓ ν)
    (h' : W + {Sum.inl i} = stendhalWeight ℓ ((Singleton.singleton i : Multiset I) + ν))
    (c : KLRAlgebra k S W) :
    appendBlack Q Λ i ν (tensorOfKLR Q Λ ν (castKLR S h c)) =
      tensorOfKLR Q Λ _ (castKLR S h' (appendR S W (Sum.inl i) c)) := by
  subst h
  rw [appendBlack_mk, appendBlackStendhal_orderProjection_id', appendBlackAllOrders_ofKLR_val,
    appendR_apply]
  rfl

end BlackAppendGeneric

section Linear

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "last" => (fun _ : Fin 1 => Fin.last ℓ)
local notation "lastColour" => Sum.map (id : I → I) last
local notation "S" => stendhalQ Q Λ

/-- On standardization, the image of a KLR diagram `c` acts as `c` on the parabolic shuffle
module. -/
theorem parabolicStandardAction_tensorOfKLR (θ' β' : Multiset I) (M : Type*) [AddCommGroup M]
    [Module k M] [Module (parabolicFactorAlgebra Q Λ θ' β') M]
    [IsScalarTower k (parabolicFactorAlgebra Q Λ θ' β') M] (hQ : KLRSymm Q)
    {W : Multiset (I ⊕ Fin (ℓ + 1))} (h : W = stendhalWeight (ℓ + 1) (θ' + β'))
    (h₁ : W = Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ') +
      Multiset.map lastColour (stendhalWeight 1 β'))
    (c : KLRAlgebra k S W) (y : ParabolicShuffle Q Λ θ' β' M) :
    parabolicStandardAction Q Λ θ' β' M hQ (tensorOfKLR Q Λ (θ' + β') (castKLR S h c))
        (Submodule.Quotient.mk y : ParabolicStandard Q Λ θ' β' M) =
      Submodule.Quotient.mk (castKLR S h₁ c • y) := by
  have hc : castKLR S h c =
      castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ' β') (castKLR S h₁ c) := by
    rw [castKLR_castKLR]
  rw [hc]
  exact LinearMap.congr_fun (parabolicStandardAction_affine Q Λ θ' β' M hQ _) _

variable (i : I) (θ₀ β₀ : Multiset I)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ₀)
local notation "Aₗ" => Multiset.map lastColour (stendhalWeight 1 β₀)
local notation "θ" => ((Si i) + θ₀)
local notation "β" => ((Si i) + β₀)
local notation "j" => (Sum.inl i : I ⊕ Fin (ℓ + 1))
local notation "hA" => prefixWeight_addBlack (ℓ := ℓ) i θ₀
local notation "hD" => lastWeight_addBlack (ℓ := ℓ) i β₀

omit [DecidableEq I] in
/-- The weights `θ₀ + β` and `θ + β₀` agree. -/
theorem lastBlackTwo_weight : θ₀ + β = θ + β₀ :=
  (add_left_comm _ _ _).trans (add_assoc _ _ _).symm

/-- The idempotent `ι(1 ⊗ 1_i)` commutes with `ι(c ⊗ 1_i)`. -/
theorem lastIdem_commute_appendR (c : KLRAlgebra k S (Aₚ + {j} + Aₗ)) :
    lastIdem S Aₚ Aₗ j * castKLR S (add_assoc (Aₚ + {j}) Aₗ {j}) (appendR S _ j c) =
      castKLR S (add_assoc (Aₚ + {j}) Aₗ {j}) (appendR S _ j c) * lastIdem S Aₚ Aₗ j := by
  rw [lastIdem, ← map_mul, ← map_mul, ← appendR_one, ← map_mul, ← map_mul, one_mul, mul_one]

-- `{i}` rather than the `Si` notation: notation is not hygienic inside `variable` binders.
variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]
  (hQ : KLRSymm Q)

local notation "N₁" => LastInput Q Λ i θ₀ β₀ N
local notation "Er" => LastResRight Q Λ i θ₀ β₀ N
local notation "El" => LastResLeft Q Λ i θ₀ β₀ N
local notation "Tβ" => TensorProductAlgebra k Q Λ (θ₀ + β)

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N] in
/-- The image of `1_{-,i}` in the parabolic shuffle module commutes with `ι(c ⊗ 1_i)`. -/
theorem lastShuffleIdem_smul_appendR (c : KLRAlgebra k S (Aₚ + {j} + Aₗ))
    (w : ParabolicShuffle Q Λ θ β N) :
    lastShuffleIdem Q Λ i θ₀ β₀ N (castKLR S (lastShuffle_weight i θ₀ β₀)
        (castKLR S (add_assoc (Aₚ + {j}) Aₗ {j}) (appendR S _ j c)) • w) =
      castKLR S (lastShuffle_weight i θ₀ β₀)
        (castKLR S (add_assoc (Aₚ + {j}) Aₗ {j}) (appendR S _ j c)) •
          lastShuffleIdem Q Λ i θ₀ β₀ N w := by
  change castKLR S (lastShuffle_weight i θ₀ β₀) (lastIdem S Aₚ Aₗ j) •
      castKLR S (lastShuffle_weight i θ₀ β₀)
        (castKLR S (add_assoc (Aₚ + {j}) Aₗ {j}) (appendR S _ j c)) • w =
    castKLR S (lastShuffle_weight i θ₀ β₀)
        (castKLR S (add_assoc (Aₚ + {j}) Aₗ {j}) (appendR S _ j c)) •
      castKLR S (lastShuffle_weight i θ₀ β₀) (lastIdem S Aₚ Aₗ j) • w
  rw [smul_smul, smul_smul, ← map_mul, ← map_mul, lastIdem_commute_appendR]

/-- The action of `T(θ₀ + β)` on `S(₂E_i N)`, through `θ₀ + β = θ + β₀`. -/
def lastBlackTwoAction : Tβ →ₐ[k] Module.End k (ParabolicStandard Q Λ θ β₀ Er) :=
  (parabolicStandardAction Q Λ θ β₀ Er hQ).comp
    (castTensorProductAlgebra Q Λ (lastBlackTwo_weight i θ₀ β₀)).toAlgHom

/-- `S(₂E_i N)` viewed as a module over `T(θ₀ + β)`. -/
def LastBlackTwoT (_hQ : KLRSymm Q) : Type _ := ParabolicStandard Q Λ θ β₀ Er

instance : AddCommGroup (LastBlackTwoT Q Λ i θ₀ β₀ N hQ) :=
  inferInstanceAs (AddCommGroup (ParabolicStandard Q Λ θ β₀ Er))
instance : Module k (LastBlackTwoT Q Λ i θ₀ β₀ N hQ) :=
  inferInstanceAs (Module k (ParabolicStandard Q Λ θ β₀ Er))
instance : Module Tβ (LastBlackTwoT Q Λ i θ₀ β₀ N hQ) :=
  Module.compHom (ParabolicStandard Q Λ θ β₀ Er) (lastBlackTwoAction Q Λ i θ₀ β₀ N hQ).toRingHom
instance : IsScalarTower k Tβ (LastBlackTwoT Q Λ i θ₀ β₀ N hQ) :=
  ⟨fun c t m => by
    change lastBlackTwoAction Q Λ i θ₀ β₀ N hQ (c • t) m =
      c • lastBlackTwoAction Q Λ i θ₀ β₀ N hQ t m
    rw [map_smul]
    rfl⟩

/-- `S(₁E_i N)` viewed as a module over `T(θ₀ + β)`. -/
def LastBlackOneT (_hQ : KLRSymm Q) : Type _ := ParabolicStandard Q Λ θ₀ β El

instance : AddCommGroup (LastBlackOneT Q Λ i θ₀ β₀ N hQ) :=
  inferInstanceAs (AddCommGroup (ParabolicStandard Q Λ θ₀ β El))
instance : Module k (LastBlackOneT Q Λ i θ₀ β₀ N hQ) :=
  inferInstanceAs (Module k (ParabolicStandard Q Λ θ₀ β El))
instance : Module Tβ (LastBlackOneT Q Λ i θ₀ β₀ N hQ) :=
  Module.compHom (ParabolicStandard Q Λ θ₀ β El) (parabolicStandardAction Q Λ θ₀ β El hQ).toRingHom
instance : IsScalarTower k Tβ (LastBlackOneT Q Λ i θ₀ β₀ N hQ) :=
  ⟨fun c t m => by
    change parabolicStandardAction Q Λ θ₀ β El hQ (c • t) m =
      c • parabolicStandardAction Q Λ θ₀ β El hQ t m
    rw [map_smul]
    rfl⟩

/-- The inclusion `S(₂E_i N) → E_i(S N)` on classes. -/
theorem lastBlackResTwo_mk (z : ParabolicShuffle Q Λ θ β₀ Er) :
    ((lastBlackResTwo Q Λ i θ₀ β₀ N hQ (Submodule.Quotient.mk z)).1 :
        ParabolicStandard Q Λ θ β N) =
      Submodule.Quotient.mk (lastShuffleIdem Q Λ i θ₀ β₀ N (lastShuffleEquiv Q Λ i θ₀ β₀ N
        (indAppend (Q := S) (ν := Aₚ + {j}) (ν₀' := Aₗ) (i := j) (N := N₁)
          ((lastOuterRightEquiv Q Λ i θ₀ β₀ N).symm z)))) := rfl

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N] in
/-- On `S(₂E_i N)`, the image of a diagram `c` of weight `ν₀ + i + ν₀'` acts as `c`. -/
theorem lastBlackTwo_smul_mk (c : KLRAlgebra k S (Aₚ + {j} + Aₗ))
    (y : Ind S (Aₚ + {j}) Aₗ (ResRight S (Aₚ + {j}) Aₗ j N₁)) :
    (tensorOfKLR Q Λ (θ₀ + β) (castKLR S (lastBlack_klrWeight i θ₀ β₀) c) •
        (show LastBlackTwoT Q Λ i θ₀ β₀ N hQ from
          Submodule.Quotient.mk (lastOuterRightEquiv Q Λ i θ₀ β₀ N y))) =
      (Submodule.Quotient.mk (lastOuterRightEquiv Q Λ i θ₀ β₀ N (c • y)) :
        ParabolicStandard Q Λ θ β₀ Er) := by
  change parabolicStandardAction Q Λ θ β₀ Er hQ (castTensorProductAlgebra Q Λ
    (lastBlackTwo_weight i θ₀ β₀) (tensorOfKLR Q Λ (θ₀ + β)
      (castKLR S (lastBlack_klrWeight i θ₀ β₀) c))) _ = _
  rw [castTensorProductAlgebra_tensorOfKLR_castKLR Q Λ (lastBlackTwo_weight i θ₀ β₀) _
      ((lastBlack_klrWeight i θ₀ β₀).trans
        (congrArg (stendhalWeight (ℓ + 1)) (lastBlackTwo_weight i θ₀ β₀))),
    parabolicStandardAction_tensorOfKLR Q Λ θ β₀ Er hQ _ (add_eq_add_of_eq hA rfl),
    lastOuterRightEquiv, indCast_smul]

/-- On `E_i(S N)`, the image of a diagram `c` of weight `ν₀ + i + ν₀'` acts as `ι(c ⊗ 1_i)`. -/
theorem lastBlackRes_smul_val (c : KLRAlgebra k S (Aₚ + {j} + Aₗ))
    (m : BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ))
    (x : ParabolicShuffle Q Λ θ β N)
    (hx : (m.1 : ParabolicStandard Q Λ θ β N) = Submodule.Quotient.mk x) :
    ((tensorOfKLR Q Λ (θ₀ + β) (castKLR S (lastBlack_klrWeight i θ₀ β₀) c) • m).1 :
        ParabolicStandard Q Λ θ β N) =
      Submodule.Quotient.mk (castKLR S (lastShuffle_weight i θ₀ β₀)
        (castKLR S (add_assoc (Aₚ + {j}) Aₗ {j}) (appendR S _ j c)) • x) := by
  have h' : Aₚ + {j} + Aₗ + {j} = stendhalWeight (ℓ + 1) ((Si i) + (θ₀ + β)) :=
    (congrArg (· + {j}) (lastBlack_klrWeight i θ₀ β₀)).trans
      (stendhalWeight_addBlack i (θ₀ + β))
  change parabolicStandardAction Q Λ θ β N hQ (castTensorProductAlgebra Q Λ
    (lastBlack_weight i θ₀ β₀) (appendBlack Q Λ i (θ₀ + β) (tensorOfKLR Q Λ (θ₀ + β)
      (castKLR S (lastBlack_klrWeight i θ₀ β₀) c)))) m.1 = _
  rw [hx, appendBlack_tensorOfKLR_castKLR Q Λ i (θ₀ + β) _ h',
    castTensorProductAlgebra_tensorOfKLR_castKLR Q Λ (lastBlack_weight i θ₀ β₀) h'
      (h'.trans (congrArg (stendhalWeight (ℓ + 1)) (lastBlack_weight i θ₀ β₀))),
    parabolicStandardAction_tensorOfKLR Q Λ θ β N hQ _
      ((add_assoc _ _ _).trans (lastShuffle_weight i θ₀ β₀)),
    castKLR_castKLR]

/-- The inclusion `S(₂E_i N) → E_i(S N)` is `T(θ₀ + β)`-linear. -/
theorem lastBlackResTwo_smul (t : Tβ) (z : LastBlackTwoT Q Λ i θ₀ β₀ N hQ) :
    lastBlackResTwo Q Λ i θ₀ β₀ N hQ (t • z) = t • lastBlackResTwo Q Λ i θ₀ β₀ N hQ z := by
  obtain ⟨c, rfl⟩ := exists_tensorOfKLR_castKLR_eq Q Λ (θ₀ + β)
    (lastBlack_klrWeight i θ₀ β₀) t
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _
    (show ParabolicStandard Q Λ θ β₀ Er from z)
  obtain ⟨y, rfl⟩ := (lastOuterRightEquiv Q Λ i θ₀ β₀ N).surjective w
  rw [lastBlackTwo_smul_mk]
  apply Subtype.ext
  rw [lastBlackRes_smul_val Q Λ i θ₀ β₀ N hQ c _ _ (lastBlackResTwo_mk Q Λ i θ₀ β₀ N hQ _),
    lastBlackResTwo_mk, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    indAppend_smul, lastShuffleEquiv_smul]
  rw [lastShuffleIdem_smul_appendR]

/-- The projection `E_i(S N) → S(₁E_i N)` on a class `[x]`. -/
theorem lastBlackResOne_eq
    (m : BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ))
    (x : ParabolicShuffle Q Λ θ β N)
    (hx : (m.1 : ParabolicStandard Q Λ θ β N) = Submodule.Quotient.mk x) :
    lastBlackResOne Q Λ i θ₀ β₀ N hQ m =
      Submodule.Quotient.mk (lastOuterLeftEquiv Q Λ i θ₀ β₀ N
        (lastProj (Q := S) (ν₀ := Aₚ) (ν₀' := Aₗ) (i := j) (N := N₁)
          (stendhalQ_swap_symm Q Λ hQ) ((lastShuffleEquiv Q Λ i θ₀ β₀ N).symm x))) := by
  have hfix : (Submodule.Quotient.mk (lastShuffleIdem Q Λ i θ₀ β₀ N x) :
      ParabolicStandard Q Λ θ β N) = Submodule.Quotient.mk x := by
    have h := (appendBlack_one_smul_lastStandardT Q Λ i θ₀ β₀ N hQ m.1).symm.trans m.2
    rw [← lastInducedOp_eq Q Λ i θ₀ β₀ N hQ] at h
    change inducedOp _ _ _ (m.1 : ParabolicStandard Q Λ θ β N) = m.1 at h
    rw [hx] at h
    exact h
  have heq : lastBlackResEquiv Q Λ i θ₀ β₀ N hQ m =
      lastStandardMiddleEquiv Q Λ i θ₀ β₀ N hQ (Submodule.Quotient.mk x) :=
    Subtype.ext (hx.trans hfix.symm)
  change lastStandardOne Q Λ i θ₀ β₀ N hQ ((lastStandardMiddleEquiv Q Λ i θ₀ β₀ N hQ).symm
    (lastBlackResEquiv Q Λ i θ₀ β₀ N hQ m)) = _
  rw [heq, LinearEquiv.symm_apply_apply]
  rfl

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N] in
/-- On `S(₁E_i N)`, the image of a diagram `c` of weight `ν₀ + i + ν₀'` acts as `c`. -/
theorem lastBlackOne_smul_mk (c : KLRAlgebra k S (Aₚ + {j} + Aₗ))
    (w : Ind S Aₚ (Aₗ + {j}) (ResAppendL S Aₚ Aₗ j N₁)) :
    (tensorOfKLR Q Λ (θ₀ + β) (castKLR S (lastBlack_klrWeight i θ₀ β₀) c) •
        (show LastBlackOneT Q Λ i θ₀ β₀ N hQ from
          Submodule.Quotient.mk (lastOuterLeftEquiv Q Λ i θ₀ β₀ N w))) =
      (Submodule.Quotient.mk (lastOuterLeftEquiv Q Λ i θ₀ β₀ N
        (castKLR S (lastQuad_h₁ Aₚ Aₗ j).symm c • w)) : ParabolicStandard Q Λ θ₀ β El) := by
  change parabolicStandardAction Q Λ θ₀ β El hQ
    (tensorOfKLR Q Λ (θ₀ + β) (castKLR S (lastBlack_klrWeight i θ₀ β₀) c)) _ = _
  rw [parabolicStandardAction_tensorOfKLR Q Λ θ₀ β El hQ _
      ((lastQuad_h₁ Aₚ Aₗ j).symm.trans (add_eq_add_of_eq rfl hD)),
    lastOuterLeftEquiv, indCast_smul, castKLR_castKLR]

/-- The projection `E_i(S N) → S(₁E_i N)` is `T(θ₀ + β)`-linear. -/
theorem lastBlackResOne_smul (t : Tβ)
    (m : BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ)) :
    (show LastBlackOneT Q Λ i θ₀ β₀ N hQ from lastBlackResOne Q Λ i θ₀ β₀ N hQ (t • m)) =
      t • (show LastBlackOneT Q Λ i θ₀ β₀ N hQ from lastBlackResOne Q Λ i θ₀ β₀ N hQ m) := by
  obtain ⟨c, rfl⟩ := exists_tensorOfKLR_castKLR_eq Q Λ (θ₀ + β)
    (lastBlack_klrWeight i θ₀ β₀) t
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (m.1 : ParabolicStandard Q Λ θ β N)
  have hsymm : (lastShuffleEquiv Q Λ i θ₀ β₀ N).symm (castKLR S (lastShuffle_weight i θ₀ β₀)
      (castKLR S (add_assoc (Aₚ + {j}) Aₗ {j}) (appendR S _ j c)) • x) =
      lastAppend (castKLR S (lastQuad_h₁ Aₚ Aₗ j).symm c) •
        (lastShuffleEquiv Q Λ i θ₀ β₀ N).symm x := by
    rw [LinearEquiv.symm_apply_eq, lastShuffleEquiv_smul, LinearEquiv.apply_symm_apply,
      lastAppend, castKLR_castAlg_symm]
  rw [lastBlackResOne_eq Q Λ i θ₀ β₀ N hQ _ _
      (lastBlackRes_smul_val Q Λ i θ₀ β₀ N hQ c m x hx.symm),
    lastBlackResOne_eq Q Λ i θ₀ β₀ N hQ m x hx.symm, hsymm, lastProj_smul,
    lastBlackOne_smul_mk]

/-- **The inclusion** `S(₂E_i N) → E_i(S N)` as a map of `T(θ₀ + β)`-modules. -/
def lastBlackResTwoT : LastBlackTwoT Q Λ i θ₀ β₀ N hQ →ₗ[Tβ]
    BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ) where
  toFun := lastBlackResTwo Q Λ i θ₀ β₀ N hQ
  map_add' := map_add (lastBlackResTwo Q Λ i θ₀ β₀ N hQ)
  map_smul' := lastBlackResTwo_smul Q Λ i θ₀ β₀ N hQ

/-- **The projection** `E_i(S N) → S(₁E_i N)` as a map of `T(θ₀ + β)`-modules. -/
def lastBlackResOneT :
    BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ) →ₗ[Tβ]
      LastBlackOneT Q Λ i θ₀ β₀ N hQ where
  toFun := lastBlackResOne Q Λ i θ₀ β₀ N hQ
  map_add' := map_add (lastBlackResOne Q Λ i θ₀ β₀ N hQ)
  map_smul' := lastBlackResOne_smul Q Λ i θ₀ β₀ N hQ

theorem lastBlackResTwoT_apply (z : LastBlackTwoT Q Λ i θ₀ β₀ N hQ) :
    lastBlackResTwoT Q Λ i θ₀ β₀ N hQ z = lastBlackResTwo Q Λ i θ₀ β₀ N hQ z := rfl

theorem lastBlackResOneT_apply
    (m : BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ)) :
    (lastBlackResOneT Q Λ i θ₀ β₀ N hQ m : ParabolicStandard Q Λ θ₀ β El) =
      lastBlackResOne Q Λ i θ₀ β₀ N hQ m := rfl

theorem lastBlackResTwoT_injective :
    Function.Injective (lastBlackResTwoT Q Λ i θ₀ β₀ N hQ) :=
  lastBlackResTwo_injective Q Λ i θ₀ β₀ N hQ

theorem lastBlackResOneT_surjective :
    Function.Surjective (lastBlackResOneT Q Λ i θ₀ β₀ N hQ) :=
  lastBlackResOne_surjective Q Λ i θ₀ β₀ N hQ

/-- **Webster, Prop 5.5, `E`-part, over `T(θ₀ + β)`:** for `θ = i + θ₀`, `β = i + β₀` the
sequence `0 → S(₂E_i N) → E_i(S N) → S(₁E_i N) → 0` is an exact sequence of
`T(θ₀ + β)`-modules. -/
theorem lastBlackResT_exact :
    Function.Exact (lastBlackResTwoT Q Λ i θ₀ β₀ N hQ) (lastBlackResOneT Q Λ i θ₀ β₀ N hQ) :=
  lastBlackRes_exact Q Λ i θ₀ β₀ N hQ

end Linear

end Categorification.Stendhal
