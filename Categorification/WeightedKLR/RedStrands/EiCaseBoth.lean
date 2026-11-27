/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EiTopChain
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastBlackNatural
import Categorification.Algebra.InductionAlongResEnd

/-!
# The last-strand sequence of `Eᵢ S N` with a commuting action

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5, `E`-part. For `θ = i + θ₀`, `β = i + β₀` and a module `N` over
`T^{λ'}(θ) ⊗ R^{λ_ℓ}(β)` with an action `τ` of an algebra `C`, the sequence
`0 → S(₂Eᵢ N) → Eᵢ(S N) → S(₁Eᵢ N) → 0` is a short exact sequence of modules over
`T(θ₀ + β) ⊗ C` (`bothSeqTwo`, `bothSeqOne`, `bothSeqTwo_injective`, `bothSeq_exact`,
`bothSeqOne_surjective`), with `Eᵢ(S N)` in the transported form of `eiTopEquiv`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  (i : I) (θ₀ β₀ : Multiset I) (C : Type) [Ring C] [Algebra k C]
  {N : Type} [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) ({i} + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) ({i} + β₀)) N]
  (τ : C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) ({i} + β₀)) N)

local notation "Tfam" => TensorProductAlgebra k Q Λ
local notation "hW" => Eq.symm (lastBlack_weight i θ₀ β₀)
local notation "hW₂" => Eq.symm (lastBlackTwo_weight i θ₀ β₀)
local notation "Er" => LastResRight Q Λ i θ₀ β₀ N
local notation "El" => LastResLeft Q Λ i θ₀ β₀ N
local notation "SN" => FamilyCast Tfam hW
  (ParabolicStandardT Q Λ ((Singleton.singleton i : Multiset I) + θ₀)
    ((Singleton.singleton i : Multiset I) + β₀) N hQ)
local notation "SEr" => FamilyCast Tfam hW₂
  (ParabolicStandardT Q Λ ((Singleton.singleton i : Multiset I) + θ₀) β₀ Er hQ)

/-- The action of `C` on `S N` over `T(i + (θ₀ + β))`. -/
abbrev bothActionP : C →ₐ[k] Module.End (Tfam (({i} : Multiset I) + (θ₀ + ({i} + β₀)))) SN :=
  (FamilyCast.endHom Tfam hW _).comp (standardActionT Q Λ hQ C τ)

/-- The action of `C` on `₂Eᵢ N`. -/
abbrev bothActionR :
    C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) β₀) Er :=
  (Res.endAlg (parabolicAppendRight Q Λ i β₀ (({i} : Multiset I) + θ₀))).comp τ

/-- The action of `C` on `₁Eᵢ N`. -/
abbrev bothActionL :
    C →ₐ[k] Module.End (parabolicFactorAlgebra Q Λ θ₀ (({i} : Multiset I) + β₀)) El :=
  (Res.endAlg (parabolicAppendLeft Q Λ i θ₀ (({i} : Multiset I) + β₀))).comp τ

/-- The action of `C` on `S(₂Eᵢ N)` over `T(θ₀ + β)`. -/
abbrev bothActionX : C →ₐ[k] Module.End (Tfam (θ₀ + (({i} : Multiset I) + β₀))) SEr :=
  (FamilyCast.endHom Tfam hW₂ _).comp (standardActionT Q Λ hQ C (bothActionR Q Λ i θ₀ β₀ C τ))

/-- `Eᵢ(S N)` over `T(θ₀ + β) ⊗ C`. -/
abbrev BothMid : Type :=
  TensorAct k (Tfam (θ₀ + (({i} : Multiset I) + β₀))) C
    (blackResAction i C (bothActionP Q Λ hQ i θ₀ β₀ C τ))

/-- `S(₂Eᵢ N)` over `T(θ₀ + β) ⊗ C`. -/
abbrev BothLeft : Type :=
  TensorAct k (Tfam (θ₀ + (({i} : Multiset I) + β₀))) C (bothActionX Q Λ hQ i θ₀ β₀ C τ)

/-- `S(₁Eᵢ N)` over `T(θ₀ + β) ⊗ C`. -/
abbrev BothRight : Type :=
  TensorAct k (Tfam (θ₀ + (({i} : Multiset I) + β₀))) C
    (standardActionT Q Λ hQ C (bothActionL Q Λ i θ₀ β₀ C τ))

/-- The inclusion `S(₂Eᵢ N) → Eᵢ(S N)` over `T(θ₀ + β)`. -/
def bothTwoT : SEr →ₗ[Tfam (θ₀ + (({i} : Multiset I) + β₀))]
    BlackRes (Q := Q) (Λ := Λ) i (θ₀ + (({i} : Multiset I) + β₀)) SN :=
  (blackResCongr i (lastStandardTEquiv Q Λ i θ₀ β₀ hQ N)).toLinearMap ∘ₗ
    (lastBlackResTwoT Q Λ i θ₀ β₀ N hQ) ∘ₗ
      (lastBlackTwoTEquiv Q Λ i hQ θ₀ β₀ N).symm.toLinearMap

/-- The projection `Eᵢ(S N) → S(₁Eᵢ N)` over `T(θ₀ + β)`. -/
def bothOneT : BlackRes (Q := Q) (Λ := Λ) i (θ₀ + (({i} : Multiset I) + β₀)) SN →ₗ[
    Tfam (θ₀ + (({i} : Multiset I) + β₀))]
    ParabolicStandardT Q Λ θ₀ (({i} : Multiset I) + β₀) El hQ :=
  (lastBlackOneTEquiv Q Λ i hQ θ₀ β₀ N).toLinearMap ∘ₗ (lastBlackResOneT Q Λ i θ₀ β₀ N hQ) ∘ₗ
    (blackResCongr i (lastStandardTEquiv Q Λ i θ₀ β₀ hQ N)).symm.toLinearMap

theorem bothTwoT_natural (c : C) (x : SEr) :
    bothTwoT Q Λ hQ i θ₀ β₀ (bothActionX Q Λ hQ i θ₀ β₀ C τ c x) =
      blackResAction i C (bothActionP Q Λ hQ i θ₀ β₀ C τ) c (bothTwoT Q Λ hQ i θ₀ β₀ x) := by
  apply Subtype.ext
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _
    (show ParabolicStandard Q Λ (({i} : Multiset I) + θ₀) β₀ Er from x)
  exact (lastBlackResTwo_natural Q Λ i θ₀ β₀ hQ (τ c) w).symm

theorem bothOneT_natural (c : C)
    (m : BlackRes (Q := Q) (Λ := Λ) i (θ₀ + (({i} : Multiset I) + β₀)) SN) :
    bothOneT Q Λ hQ i θ₀ β₀ (blackResAction i C (bothActionP Q Λ hQ i θ₀ β₀ C τ) c m) =
      standardActionT Q Λ hQ C (bothActionL Q Λ i θ₀ β₀ C τ) c (bothOneT Q Λ hQ i θ₀ β₀ m) := by
  have hm : (blackResCongr i (lastStandardTEquiv Q Λ i θ₀ β₀ hQ N)).symm
      (blackResAction i C (bothActionP Q Λ hQ i θ₀ β₀ C τ) c m) =
      blackResStandardMap Q Λ i θ₀ β₀ hQ (τ c)
        ((blackResCongr i (lastStandardTEquiv Q Λ i θ₀ β₀ hQ N)).symm m) := Subtype.ext rfl
  change (lastBlackOneTEquiv Q Λ i hQ θ₀ β₀ N) (lastBlackResOneT Q Λ i θ₀ β₀ N hQ
      ((blackResCongr i (lastStandardTEquiv Q Λ i θ₀ β₀ hQ N)).symm
        (blackResAction i C (bothActionP Q Λ hQ i θ₀ β₀ C τ) c m))) = _
  rw [hm]
  exact lastBlackResOne_natural Q Λ i θ₀ β₀ hQ (τ c)
    ((blackResCongr i (lastStandardTEquiv Q Λ i θ₀ β₀ hQ N)).symm m)

/-- **The inclusion `S(₂Eᵢ N) → Eᵢ(S N)` over `T(θ₀ + β) ⊗ C`.** -/
def bothSeqTwo : BothLeft Q Λ hQ i θ₀ β₀ C τ →ₗ[Tfam (θ₀ + (({i} : Multiset I) + β₀)) ⊗[k] C]
    BothMid Q Λ hQ i θ₀ β₀ C τ :=
  TensorAct.map (bothTwoT Q Λ hQ i θ₀ β₀) (bothTwoT_natural Q Λ hQ i θ₀ β₀ C τ)

/-- **The projection `Eᵢ(S N) → S(₁Eᵢ N)` over `T(θ₀ + β) ⊗ C`.** -/
def bothSeqOne : BothMid Q Λ hQ i θ₀ β₀ C τ →ₗ[Tfam (θ₀ + (({i} : Multiset I) + β₀)) ⊗[k] C]
    BothRight Q Λ hQ i θ₀ β₀ C τ :=
  TensorAct.map (bothOneT Q Λ hQ i θ₀ β₀) (bothOneT_natural Q Λ hQ i θ₀ β₀ C τ)

theorem bothSeqTwo_injective : Function.Injective (bothSeqTwo Q Λ hQ i θ₀ β₀ C τ) :=
  TensorAct.map_injective _ ((blackResCongr i (lastStandardTEquiv Q Λ i θ₀ β₀ hQ N)).injective.comp
    ((lastBlackResTwoT_injective Q Λ i θ₀ β₀ N hQ).comp
      (lastBlackTwoTEquiv Q Λ i hQ θ₀ β₀ N).symm.injective))

theorem bothSeqOne_surjective : Function.Surjective (bothSeqOne Q Λ hQ i θ₀ β₀ C τ) :=
  TensorAct.map_surjective _ ((lastBlackOneTEquiv Q Λ i hQ θ₀ β₀ N).surjective.comp
    ((lastBlackResOneT_surjective Q Λ i θ₀ β₀ N hQ).comp
      (blackResCongr i (lastStandardTEquiv Q Λ i θ₀ β₀ hQ N)).symm.surjective))

theorem bothT_exact :
    Function.Exact (bothTwoT Q Λ hQ i θ₀ β₀ (N := N)) (bothOneT Q Λ hQ i θ₀ β₀ (N := N)) := by
  intro y
  change (lastBlackOneTEquiv Q Λ i hQ θ₀ β₀ N) (lastBlackResOneT Q Λ i θ₀ β₀ N hQ
      ((blackResCongr i (lastStandardTEquiv Q Λ i θ₀ β₀ hQ N)).symm y)) = 0 ↔
    ∃ x, (blackResCongr i (lastStandardTEquiv Q Λ i θ₀ β₀ hQ N)) (lastBlackResTwoT Q Λ i θ₀ β₀ N hQ
      ((lastBlackTwoTEquiv Q Λ i hQ θ₀ β₀ N).symm x)) = y
  rw [LinearEquiv.map_eq_zero_iff, lastBlackResT_exact Q Λ i θ₀ β₀ N hQ]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨lastBlackTwoTEquiv Q Λ i hQ θ₀ β₀ N x, by
      rw [LinearEquiv.symm_apply_apply, hx, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(lastBlackTwoTEquiv Q Λ i hQ θ₀ β₀ N).symm x, by rw [LinearEquiv.symm_apply_apply]⟩

theorem bothSeq_exact :
    Function.Exact (bothSeqTwo Q Λ hQ i θ₀ β₀ C τ) (bothSeqOne Q Λ hQ i θ₀ β₀ C τ) :=
  TensorAct.map_exact _ _ (bothT_exact Q Λ hQ i θ₀ β₀)

end StendhalAlgebra

end Categorification.Stendhal
