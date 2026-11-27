/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastBlackLinear
import Categorification.KLR.IndLastStrandNatural
import Categorification.WeightedKLR.RedStrands.ParabolicStandardExact

/-!
# Naturality of the last-strand sequence of `E_i(S N)`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `E`-part. For `θ = i + θ₀`, `β = i + β₀` and a map `g : N → N'` of modules over
`T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)`, the maps of the short exact sequence

`0 → S(₂E_i N) → E_i(S N) → S(₁E_i N) → 0`

commute with the maps induced by `g` (`lastBlackResTwo_natural`, `lastBlackResOne_natural`).
This is what carries an extra commuting action on `N` through the sequence in the induction on
the number of red strands.

## Main definitions

* `lastResRightMap`, `lastResLeftMap`: `₂E_i g` and `₁E_i g`.
* `blackResStandardMap`: `E_i(S g)`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra IdempotentQuotient
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ)

local notation "last" => (fun _ : Fin 1 => Fin.last ℓ)
local notation "lastColour" => Sum.map (id : I → I) last
local notation "S" => stendhalQ Q Λ

variable (i : I) (θ₀ β₀ : Multiset I)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ₀)
local notation "Aₗ" => Multiset.map lastColour (stendhalWeight 1 β₀)
local notation "θ" => ((Si i) + θ₀)
local notation "β" => ((Si i) + β₀)
local notation "j" => (Sum.inl i : I ⊕ Fin (ℓ + 1))

variable {N N' : Type w} [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]
  [AddCommGroup N'] [Module k N']
  [Module (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N']
  (hQ : KLRSymm Q)
  (g : N →ₗ[parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)] N')

local notation "N₁" => LastInput Q Λ i θ₀ β₀ N
local notation "N₁'" => LastInput Q Λ i θ₀ β₀ N'
local notation "Tβ" => TensorProductAlgebra k Q Λ (θ₀ + β)

/-- `g` as a map of the inputs over `R(ν₀ + i) ⊗ R(ν₀' + i)`. -/
def lastInputHom : N₁ →ₗ[TensorKLR S (Aₚ + {j}) (Aₗ + {j})] N₁' where
  toFun n := (g (show N from n) : N')
  map_add' n n' := g.map_add (show N from n) (show N from n')
  map_smul' _ n := g.map_smul _ (show N from n)

/-- **`₂E_i g`.** -/
abbrev lastResRightMap :
    LastResRight Q Λ i θ₀ β₀ N →ₗ[parabolicFactorAlgebra Q Λ θ β₀] LastResRight Q Λ i θ₀ β₀ N' :=
  InductionAlong.Res.map (φ := parabolicAppendRightHom Q Λ i θ₀ β₀) g

/-- **`₁E_i g`.** -/
abbrev lastResLeftMap :
    LastResLeft Q Λ i θ₀ β₀ N →ₗ[parabolicFactorAlgebra Q Λ θ₀ β] LastResLeft Q Λ i θ₀ β₀ N' :=
  InductionAlong.Res.map (φ := parabolicAppendLeftHom Q Λ i θ₀ β₀) g

theorem lastShuffleEquiv_natural (y : Ind S (Aₚ + {j}) (Aₗ + {j}) N₁) :
    lastShuffleEquiv Q Λ i θ₀ β₀ N'
        (BalancedTensor.mapRight (lastInputHom Q Λ i θ₀ β₀ g) y) =
      parabolicShuffleMap Q Λ θ β g (lastShuffleEquiv Q Λ i θ₀ β₀ N y) := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]
  [Module k N'] [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N'] in
theorem lastOuterRightEquiv_natural
    (y : Ind S (Aₚ + {j}) Aₗ (ResRight S (Aₚ + {j}) Aₗ j N₁)) :
    parabolicShuffleMap Q Λ θ β₀ (lastResRightMap Q Λ i θ₀ β₀ g)
        (lastOuterRightEquiv Q Λ i θ₀ β₀ N y) =
      lastOuterRightEquiv Q Λ i θ₀ β₀ N' (BalancedTensor.mapRight
        (InductionAlong.Res.map (φ := tensorAppendHom S (Aₚ + {j}) Aₗ j)
          (lastInputHom Q Λ i θ₀ β₀ g)) y) := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N]
  [Module k N'] [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) ({i} + β₀)) N'] in
theorem lastOuterLeftEquiv_natural
    (y : Ind S Aₚ (Aₗ + {j}) (ResAppendL S Aₚ Aₗ j N₁)) :
    parabolicShuffleMap Q Λ θ₀ β (lastResLeftMap Q Λ i θ₀ β₀ g)
        (lastOuterLeftEquiv Q Λ i θ₀ β₀ N y) =
      lastOuterLeftEquiv Q Λ i θ₀ β₀ N' (BalancedTensor.mapRight
        (InductionAlong.Res.map (φ := tensorAppendLHom S Aₚ Aₗ j)
          (lastInputHom Q Λ i θ₀ β₀ g)) y) := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `S(g)` on `S N` viewed over `T(i + (θ₀ + β))`. -/
def lastStandardTMap :
    LastStandardT Q Λ i θ₀ β₀ N hQ →ₗ[TensorProductAlgebra k Q Λ ((Si i) + (θ₀ + β))]
      LastStandardT Q Λ i θ₀ β₀ N' hQ where
  toFun := parabolicStandardMap Q Λ θ β g
  map_add' := map_add _
  map_smul' _ z := parabolicStandardMap_action Q Λ θ β hQ g _ z

/-- **`E_i(S g)`.** -/
def blackResStandardMap :
    BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ) →ₗ[Tβ]
      BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N' hQ) where
  toFun m := ⟨lastStandardTMap Q Λ i θ₀ β₀ hQ g m.1, by
    rw [mem_fixSub, ← map_smul, (mem_fixSub).1 m.2]⟩
  map_add' m m' := Subtype.ext (map_add _ m.1 m'.1)
  map_smul' t m := Subtype.ext (map_smul (lastStandardTMap Q Λ i θ₀ β₀ hQ g) _ m.1)

theorem blackResStandardMap_val
    (m : BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ)) :
    ((blackResStandardMap Q Λ i θ₀ β₀ hQ g m).1 : ParabolicStandard Q Λ θ β N') =
      parabolicStandardMap Q Λ θ β g (m.1 : ParabolicStandard Q Λ θ β N) := rfl

/-- **Naturality of the inclusion** `S(₂E_i N) → E_i(S N)`, on classes. -/
theorem lastBlackResTwo_natural (w : ParabolicShuffle Q Λ θ β₀ (LastResRight Q Λ i θ₀ β₀ N)) :
    parabolicStandardMap Q Λ θ β g
        ((lastBlackResTwo Q Λ i θ₀ β₀ N hQ (Submodule.Quotient.mk w)).1 :
          ParabolicStandard Q Λ θ β N) =
      ((lastBlackResTwo Q Λ i θ₀ β₀ N' hQ
        (Submodule.Quotient.mk
          (parabolicShuffleMap Q Λ θ β₀ (lastResRightMap Q Λ i θ₀ β₀ g) w))).1 :
          ParabolicStandard Q Λ θ β N') := by
  obtain ⟨y, rfl⟩ := (lastOuterRightEquiv Q Λ i θ₀ β₀ N).surjective w
  rw [lastBlackResTwo_mk, parabolicStandardMap_mk, lastBlackResTwo_mk,
    lastOuterRightEquiv_natural, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    ← indAppend_mapRight, lastShuffleEquiv_natural]
  exact congrArg Submodule.Quotient.mk
    ((parabolicShuffleMap Q Λ θ β g).map_smul _ _)

theorem lastOuterLeft_lastProj_natural (u : Ind S (Aₚ + {j}) (Aₗ + {j}) N₁) :
    lastOuterLeftEquiv Q Λ i θ₀ β₀ N' (lastProj (Q := S) (ν₀ := Aₚ) (ν₀' := Aₗ) (i := j)
        (N := N₁') (stendhalQ_swap_symm Q Λ hQ)
        (BalancedTensor.mapRight (lastInputHom Q Λ i θ₀ β₀ g) u)) =
      parabolicShuffleMap Q Λ θ₀ β (lastResLeftMap Q Λ i θ₀ β₀ g)
        (lastOuterLeftEquiv Q Λ i θ₀ β₀ N (lastProj (Q := S) (ν₀ := Aₚ) (ν₀' := Aₗ) (i := j)
          (N := N₁) (stendhalQ_swap_symm Q Λ hQ) u)) := by
  rw [lastProj_mapRight]
  generalize lastProj _ u = y
  rw [lastOuterLeftEquiv_natural]

/-- **Naturality of the projection** `E_i(S N) → S(₁E_i N)`. -/
theorem lastBlackResOne_natural
    (m : BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LastStandardT Q Λ i θ₀ β₀ N hQ)) :
    lastBlackResOne Q Λ i θ₀ β₀ N' hQ (blackResStandardMap Q Λ i θ₀ β₀ hQ g m) =
      parabolicStandardMap Q Λ θ₀ β (lastResLeftMap Q Λ i θ₀ β₀ g)
        (lastBlackResOne Q Λ i θ₀ β₀ N hQ m) := by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (m.1 : ParabolicStandard Q Λ θ β N)
  obtain ⟨u, rfl⟩ := (lastShuffleEquiv Q Λ i θ₀ β₀ N).surjective x
  have hx' : ((blackResStandardMap Q Λ i θ₀ β₀ hQ g m).1 : ParabolicStandard Q Λ θ β N') =
      Submodule.Quotient.mk (parabolicShuffleMap Q Λ θ β g (lastShuffleEquiv Q Λ i θ₀ β₀ N u)) := by
    rw [blackResStandardMap_val, ← hx, parabolicStandardMap_mk]
  rw [lastBlackResOne_eq Q Λ i θ₀ β₀ N' hQ _ _ hx', lastBlackResOne_eq Q Λ i θ₀ β₀ N hQ _ _ hx.symm,
    parabolicStandardMap_mk]
  refine congrArg Submodule.Quotient.mk ?_
  rw [LinearEquiv.symm_apply_apply, ← lastShuffleEquiv_natural Q Λ i θ₀ β₀ g u,
    LinearEquiv.symm_apply_apply]
  exact lastOuterLeft_lastProj_natural Q Λ i θ₀ β₀ hQ g u

end Categorification.Stendhal
