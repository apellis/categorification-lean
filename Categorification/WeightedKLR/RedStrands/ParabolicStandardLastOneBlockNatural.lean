/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastOneBlockLinear
import Categorification.WeightedKLR.RedStrands.ParabolicStandardExact

/-!
# Naturality of `E_i(S N) ≅ S(E_i N)` when `i` occurs in one block

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `E`-part. For a map `g : N → N'` of modules over `T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)`, the
isomorphisms `E_i(S N) ≅ S(₁E_i N)` (`θ = i + θ₀`, `i ∉ β`) and `E_i(S N) ≅ S(₂E_i N)`
(`β = i + β₀`, `i ∉ θ`) commute with the maps induced by `g` (`leftBlackResEquiv_natural`,
`rightBlackResEquiv_natural`). This carries an extra commuting action on `N` through these
isomorphisms in the induction on the number of red strands. The proofs check the inverse maps,
which are explicit on classes.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra IdempotentQuotient
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w

section IndMaps

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν₀ ν ν' ν₀' : Multiset I} {i : I}

theorem indFirst_mapRight {N N' : Type w} [AddCommGroup N] [Module k N]
    [Module (TensorKLR Q (ν₀ + ({i} : Multiset I)) ν') N]
    [IsScalarTower k (TensorKLR Q (ν₀ + ({i} : Multiset I)) ν') N]
    [AddCommGroup N'] [Module k N'] [Module (TensorKLR Q (ν₀ + ({i} : Multiset I)) ν') N']
    [IsScalarTower k (TensorKLR Q (ν₀ + ({i} : Multiset I)) ν') N']
    (f : N →ₗ[TensorKLR Q (ν₀ + ({i} : Multiset I)) ν'] N') (hi : i ∉ ν')
    (y : Ind Q ν₀ ν' (ResFirst Q ν₀ ν' i N)) :
    BalancedTensor.mapRight f (indFirst N hi y) =
      indFirst N' hi (BalancedTensor.mapRight
        (InductionAlong.Res.map (φ := tensorAppendLHom' Q ν₀ ν' i) f) y) := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem indAppend_mapRight' {N N' : Type w} [AddCommGroup N] [Module k N]
    [Module (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N]
    [IsScalarTower k (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N]
    [AddCommGroup N'] [Module k N'] [Module (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N']
    [IsScalarTower k (TensorKLR Q ν (ν₀' + ({i} : Multiset I))) N']
    (f : N →ₗ[TensorKLR Q ν (ν₀' + ({i} : Multiset I))] N')
    (y : Ind Q ν ν₀' (ResRight Q ν ν₀' i N)) :
    BalancedTensor.mapRight f (indAppend y) =
      indAppend (BalancedTensor.mapRight
        (InductionAlong.Res.map (φ := tensorAppendHom Q ν ν₀' i) f) y) := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end IndMaps

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)

local notation "last" => (fun _ : Fin 1 => Fin.last ℓ)
local notation "lastColour" => Sum.map (id : I → I) last
local notation "S" => stendhalQ Q Λ
local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "j" => (Sum.inl i : I ⊕ Fin (ℓ + 1))

section Left

variable (θ₀ β : Multiset I)

local notation "Aₚ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ₀)
local notation "Aβ" => Multiset.map lastColour (stendhalWeight 1 β)
local notation "θ" => ((Si i) + θ₀)

variable {N N' : Type w} [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N]
  [AddCommGroup N'] [Module k N']
  [Module (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N']
  (hQ : KLRSymm Q) (g : N →ₗ[parabolicFactorAlgebra Q Λ ({i} + θ₀) β] N')

local notation "N₁" => LeftInput Q Λ i θ₀ β N
local notation "N₁'" => LeftInput Q Λ i θ₀ β N'
local notation "Jl" => indCast rfl rfl (leftResLeftEquiv Q Λ i θ₀ β N)
  (leftResLeftEquiv_smul Q Λ i θ₀ β N)
local notation "Jl'" => indCast rfl rfl (leftResLeftEquiv Q Λ i θ₀ β N')
  (leftResLeftEquiv_smul Q Λ i θ₀ β N')

/-- `g` as a map of the inputs over `R(ν₀ + i) ⊗ R(ν')`. -/
def leftInputLinearMap : N₁ →ₗ[TensorKLR S (Aₚ + {j}) Aβ] N₁' where
  toFun n := (g (show N from n) : N')
  map_add' n n' := g.map_add (show N from n) (show N from n')
  map_smul' _ n := g.map_smul _ (show N from n)

theorem leftShuffleEquiv_natural (y : Ind S (Aₚ + {j}) Aβ N₁) :
    leftShuffleEquiv Q Λ i θ₀ β N'
        (BalancedTensor.mapRight (leftInputLinearMap Q Λ i θ₀ β g) y) =
      parabolicShuffleMap Q Λ θ β g (leftShuffleEquiv Q Λ i θ₀ β N y) := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N]
  [Module k N'] [IsScalarTower k (parabolicFactorAlgebra Q Λ ({i} + θ₀) β) N'] in
theorem leftResLeftCast_natural (y : Ind S Aₚ Aβ (ResFirst S Aₚ Aβ j N₁)) :
    parabolicShuffleMap Q Λ θ₀ β
        (InductionAlong.Res.map (φ := leftAppendHom Q Λ i θ₀ β) g) (Jl y) =
      Jl' (BalancedTensor.mapRight (InductionAlong.Res.map
        (φ := tensorAppendLHom' S Aₚ Aβ j) (leftInputLinearMap Q Λ i θ₀ β g)) y) := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem leftBlackResEquiv_symm_natural_mk (hi : i ∉ β)
    (y : Ind S Aₚ Aβ (ResFirst S Aₚ Aβ j N₁)) :
    (((leftBlackResEquiv Q Λ i θ₀ β N' hQ hi).symm (parabolicStandardMap Q Λ θ₀ β
        (InductionAlong.Res.map (φ := leftAppendHom Q Λ i θ₀ β) g)
          (Submodule.Quotient.mk (Jl y)))).1 : ParabolicStandard Q Λ θ β N') =
      parabolicStandardMap Q Λ θ β g
        (((leftBlackResEquiv Q Λ i θ₀ β N hQ hi).symm (Submodule.Quotient.mk (Jl y))).1 :
          ParabolicStandard Q Λ θ β N) := by
  have h1 : parabolicStandardMap Q Λ θ₀ β
      (InductionAlong.Res.map (φ := leftAppendHom Q Λ i θ₀ β) g)
      (Submodule.Quotient.mk (Jl y)) = Submodule.Quotient.mk (Jl' (BalancedTensor.mapRight
        (InductionAlong.Res.map (φ := tensorAppendLHom' S Aₚ Aβ j)
          (leftInputLinearMap Q Λ i θ₀ β g)) y)) :=
    congrArg Submodule.Quotient.mk (leftResLeftCast_natural Q Λ i θ₀ β g y)
  have h2 := leftBlackResEquiv_symm_mk Q Λ i θ₀ β N' hQ hi (BalancedTensor.mapRight
    (InductionAlong.Res.map (φ := tensorAppendLHom' S Aₚ Aβ j)
      (leftInputLinearMap Q Λ i θ₀ β g)) y)
  have h3 := leftBlackResEquiv_symm_mk Q Λ i θ₀ β N hQ hi y
  have h4 := indFirst_mapRight (leftInputLinearMap Q Λ i θ₀ β g) (inl_notMem_lastWeight i β hi) y
  have h5 := leftShuffleEquiv_natural Q Λ i θ₀ β g
    (indFirst N₁ (inl_notMem_lastWeight i β hi) y)
  refine ((congrArg (fun z => (((leftBlackResEquiv Q Λ i θ₀ β N' hQ hi).symm z).1 :
    ParabolicStandard Q Λ θ β N')) h1).trans (h2.trans ?_)).trans
    (congrArg (parabolicStandardMap Q Λ θ β g) h3).symm
  rw [parabolicStandardMap_mk, ← h4, h5]
  exact congrArg Submodule.Quotient.mk ((parabolicShuffleMap Q Λ θ β g).map_smul _ _).symm

/-- **Naturality of the inverse of `E_i(S N) ≅ S(₁E_i N)`**, `i ∉ β`. -/
theorem leftBlackResEquiv_symm_natural (hi : i ∉ β)
    (z : ParabolicStandard Q Λ θ₀ β (LeftResLeft Q Λ i θ₀ β N)) :
    (((leftBlackResEquiv Q Λ i θ₀ β N' hQ hi).symm (parabolicStandardMap Q Λ θ₀ β
        (InductionAlong.Res.map (φ := leftAppendHom Q Λ i θ₀ β) g) z)).1 :
        ParabolicStandard Q Λ θ β N') =
      parabolicStandardMap Q Λ θ β g
        (((leftBlackResEquiv Q Λ i θ₀ β N hQ hi).symm z).1 : ParabolicStandard Q Λ θ β N) := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have h := leftBlackResEquiv_symm_natural_mk Q Λ i θ₀ β hQ g hi ((Jl).symm w)
  have e : Jl ((Jl).symm w) = w := LinearEquiv.apply_symm_apply _ w
  rw [← e]
  exact h

/-- **Naturality of `E_i(S N) ≅ S(₁E_i N)`**, `i ∉ β`. -/
theorem leftBlackResEquiv_natural (hi : i ∉ β)
    (m : BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LeftStandardT Q Λ i θ₀ β N hQ))
    (m' : BlackRes (Q := Q) (Λ := Λ) i (θ₀ + β) (LeftStandardT Q Λ i θ₀ β N' hQ))
    (hm : (m'.1 : ParabolicStandard Q Λ θ β N') =
      parabolicStandardMap Q Λ θ β g (m.1 : ParabolicStandard Q Λ θ β N)) :
    leftBlackResEquiv Q Λ i θ₀ β N' hQ hi m' =
      parabolicStandardMap Q Λ θ₀ β
        (InductionAlong.Res.map (φ := leftAppendHom Q Λ i θ₀ β) g)
        (leftBlackResEquiv Q Λ i θ₀ β N hQ hi m) := by
  apply (leftBlackResEquiv Q Λ i θ₀ β N' hQ hi).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  exact hm.trans ((leftBlackResEquiv_symm_natural Q Λ i θ₀ β hQ g hi _).trans (congrArg
    (parabolicStandardMap Q Λ θ β g) (congrArg Subtype.val
      ((leftBlackResEquiv Q Λ i θ₀ β N hQ hi).symm_apply_apply m)))).symm

end Left

section Right

variable (θ β₀ : Multiset I)

local notation "Aθ" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "Aₗ" => Multiset.map lastColour (stendhalWeight 1 β₀)
local notation "β" => ((Si i) + β₀)

variable {N N' : Type w} [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N]
  [AddCommGroup N'] [Module k N']
  [Module (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N']
  (hQ : KLRSymm Q) (g : N →ₗ[parabolicFactorAlgebra Q Λ θ ({i} + β₀)] N')

local notation "N₁" => RightInput Q Λ i θ β₀ N
local notation "N₁'" => RightInput Q Λ i θ β₀ N'
local notation "Jr" => indCast rfl rfl (rightResRightEquiv Q Λ i θ β₀ N)
  (rightResRightEquiv_smul Q Λ i θ β₀ N)
local notation "Jr'" => indCast rfl rfl (rightResRightEquiv Q Λ i θ β₀ N')
  (rightResRightEquiv_smul Q Λ i θ β₀ N')

/-- `g` as a map of the inputs over `R(ν) ⊗ R(ν₀' + i)`. -/
def rightInputLinearMap : N₁ →ₗ[TensorKLR S Aθ (Aₗ + {j})] N₁' where
  toFun n := (g (show N from n) : N')
  map_add' n n' := g.map_add (show N from n) (show N from n')
  map_smul' _ n := g.map_smul _ (show N from n)

theorem rightShuffleEquiv_natural (y : Ind S Aθ (Aₗ + {j}) N₁) :
    rightShuffleEquiv Q Λ i θ β₀ N'
        (BalancedTensor.mapRight (rightInputLinearMap Q Λ i θ β₀ g) y) =
      parabolicShuffleMap Q Λ θ β g (rightShuffleEquiv Q Λ i θ β₀ N y) := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [Module k N] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N]
  [Module k N'] [IsScalarTower k (parabolicFactorAlgebra Q Λ θ ({i} + β₀)) N'] in
theorem rightResRightCast_natural (y : Ind S Aθ Aₗ (ResRight S Aθ Aₗ j N₁)) :
    parabolicShuffleMap Q Λ θ β₀
        (InductionAlong.Res.map (φ := rightAppendHom Q Λ i θ β₀) g) (Jr y) =
      Jr' (BalancedTensor.mapRight (InductionAlong.Res.map
        (φ := tensorAppendHom S Aθ Aₗ j) (rightInputLinearMap Q Λ i θ β₀ g)) y) := by
  induction y using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | tmul r n => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Naturality of the inverse of `E_i(S N) ≅ S(₂E_i N)`**, `i ∉ θ`. -/
theorem rightBlackResEquiv_symm_natural (hi : i ∉ θ)
    (z : ParabolicStandard Q Λ θ β₀ (RightResRight Q Λ i θ β₀ N)) :
    (((rightBlackResEquiv Q Λ i θ β₀ N' hQ hi).symm (parabolicStandardMap Q Λ θ β₀
        (InductionAlong.Res.map (φ := rightAppendHom Q Λ i θ β₀) g) z)).1 :
        ParabolicStandard Q Λ θ β N') =
      parabolicStandardMap Q Λ θ β g
        (((rightBlackResEquiv Q Λ i θ β₀ N hQ hi).symm z).1 : ParabolicStandard Q Λ θ β N) := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨y, rfl⟩ := (Jr).surjective w
  have h1 : parabolicStandardMap Q Λ θ β₀
      (InductionAlong.Res.map (φ := rightAppendHom Q Λ i θ β₀) g)
      (Submodule.Quotient.mk (Jr y)) = Submodule.Quotient.mk (Jr' (BalancedTensor.mapRight
        (InductionAlong.Res.map (φ := tensorAppendHom S Aθ Aₗ j)
          (rightInputLinearMap Q Λ i θ β₀ g)) y)) :=
    congrArg Submodule.Quotient.mk (rightResRightCast_natural Q Λ i θ β₀ g y)
  rw [h1, rightBlackResEquiv_symm_mk Q Λ i θ β₀ N' hQ hi,
    rightBlackResEquiv_symm_mk Q Λ i θ β₀ N hQ hi y, parabolicStandardMap_mk,
    ← indAppend_mapRight' (rightInputLinearMap Q Λ i θ β₀ g) y,
    rightShuffleEquiv_natural Q Λ i θ β₀ g]
  exact congrArg Submodule.Quotient.mk ((parabolicShuffleMap Q Λ θ β g).map_smul _ _).symm

/-- **Naturality of `E_i(S N) ≅ S(₂E_i N)`**, `i ∉ θ`. -/
theorem rightBlackResEquiv_natural (hi : i ∉ θ)
    (m : BlackRes (Q := Q) (Λ := Λ) i (θ + β₀) (RightStandardT Q Λ i θ β₀ N hQ))
    (m' : BlackRes (Q := Q) (Λ := Λ) i (θ + β₀) (RightStandardT Q Λ i θ β₀ N' hQ))
    (hm : (m'.1 : ParabolicStandard Q Λ θ β N') =
      parabolicStandardMap Q Λ θ β g (m.1 : ParabolicStandard Q Λ θ β N)) :
    rightBlackResEquiv Q Λ i θ β₀ N' hQ hi m' =
      parabolicStandardMap Q Λ θ β₀
        (InductionAlong.Res.map (φ := rightAppendHom Q Λ i θ β₀) g)
        (rightBlackResEquiv Q Λ i θ β₀ N hQ hi m) := by
  apply (rightBlackResEquiv Q Λ i θ β₀ N' hQ hi).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  exact hm.trans ((rightBlackResEquiv_symm_natural Q Λ i θ β₀ hQ g hi _).trans (congrArg
    (parabolicStandardMap Q Λ θ β g) (congrArg Subtype.val
      ((rightBlackResEquiv Q Λ i θ β₀ N hQ hi).symm_apply_apply m)))).symm

end Right

end Categorification.Stendhal
