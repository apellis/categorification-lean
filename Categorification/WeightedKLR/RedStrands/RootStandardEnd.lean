/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PrependRedBlockCorner
import Categorification.WeightedKLR.RedStrands.Standardization
import Categorification.Algebra.CornerGeneratorTensor

/-!
# Endomorphisms of `S_α` and full faithfulness of standardization

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.26, for every first block `b_0` (that is, also when `α(0) ≠ 0`): the block action
of Proposition 5.3 is an isomorphism
`R(b_0) ⊗ R^{λ_1}(b_1) ⊗ ⋯ ⊗ R^{λ_ℓ}(b_ℓ) ≅ End_{T̃^λ}(S_α)` (`bijective_blockAction`,
`blockActionEquiv`), and the standardization `M ↦ M ⊗_B S_α` of Definition 5.4 is fully
faithful (`standardizationMap_bijective`).

Every endomorphism of `S_α` is left multiplication by an element of the corner
`e_α T̃^λ e_α` (`exists_rootAction_eq`), which acts through the block algebra
(`exists_blockAction_eq_rootAction_of_grading`); the block action on `[e_α]` is injective
(`blockAction_rootStandardUnit_injective`). Hence `[e_α]` generates `S_α`, and
`S_α e_α = B [e_α]` freely (`isCornerGenerator_rootStandardUnit`), which gives full
faithfulness (`BalancedTensor.IsCornerGenerator.mapRight_bijective`).

Both of Webster's inputs for `α(0) ≠ 0`, the comparison with `T^{(λ₀, λ)}` for large `λ₀`, use
a grading of `T̃^λ` in which dots have positive degree: Webster's grading (Definition 4.4) is
one, with red dots of auxiliary degree two.

## Main results

* `StendhalAlgebra.exists_rootAction_eq`: `End_{T̃^λ}(S_α)` is the image of the corner.
* `StendhalAlgebra.bijective_blockAction`, `StendhalAlgebra.blockActionEquiv`.
* `StendhalAlgebra.isCornerGenerator_rootStandardUnit`,
  `StendhalAlgebra.standardizationMap_bijective`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}

section Surjective

variable {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

theorem exists_eq_rootStandardMk {α : Fin ℓ → I → ℕ} (v : rootStandard (ν := ν) Q Λ α) :
    ∃ (z : StendhalAlgebra k Q Λ ν) (hz : rootIdem Q Λ α * z = z), v = rootStandardMk Q Λ α z hz := by
  obtain ⟨q, hq⟩ := v
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hq
  exact ⟨z, (mem_span_singleton_iff_mul (isIdempotentElem_rootIdem α) z).1 hz, rfl⟩

theorem val_op_smul_rootStandardMk {α : Fin ℓ → I → ℕ} (a z : StendhalAlgebra k Q Λ ν)
    (hz : rootIdem Q Λ α * z = z) :
    ((op a • rootStandardMk Q Λ α z hz : rootStandard (ν := ν) Q Λ α) :
      StendhalAlgebra k Q Λ ν ⧸ rootUpper (ν := ν) Q Λ α) = Submodule.Quotient.mk (z * a) :=
  rfl

/-- **Every endomorphism of `S_α` is left multiplication by an element of the corner
`e_α T̃^λ e_α`.** -/
theorem exists_rootAction_eq (α : Fin ℓ → I → ℕ)
    (f : Module.End (StendhalAlgebra k Q Λ ν)ᵐᵒᵖ (rootStandard (ν := ν) Q Λ α)) :
    ∃ c, rootAction Q Λ α c = f := by
  have he := isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := ν) α
  obtain ⟨z, hz, hzv⟩ := exists_eq_rootStandardMk (f (rootStandardUnit Q Λ ν α))
  let c : he.Corner := KLR.Corner.mk (z * rootIdem (ν := ν) Q Λ α) (by
    rw [← mul_assoc, hz, mul_assoc, he.eq])
  refine ⟨c, sub_eq_zero.1 (eq_zero_of_apply_rootStandardUnit _ _ ?_)⟩
  rw [LinearMap.sub_apply, sub_eq_zero]
  have hu : (op (rootIdem (ν := ν) Q Λ α) • rootStandardUnit Q Λ ν α : rootStandard (ν := ν) Q Λ α) =
      rootStandardUnit Q Λ ν α := by
    apply Subtype.ext
    change Submodule.Quotient.mk (rootIdem (ν := ν) Q Λ α * rootIdem (ν := ν) Q Λ α) =
      Submodule.Quotient.mk (rootIdem (ν := ν) Q Λ α)
    rw [he.eq]
  conv_rhs => rw [← hu, map_smul, hzv]
  apply Subtype.ext
  rw [val_op_smul_rootStandardMk]
  unfold rootStandardUnit
  rw [rootAction_mk]
  change Submodule.Quotient.mk (z * rootIdem (ν := ν) Q Λ α * rootIdem (ν := ν) Q Λ α) = _
  rw [mul_assoc, he.eq]

end Surjective

section Bijective

variable {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I} {b : Fin (ℓ + 1) → Multiset I}

/-- **Proposition 5.26 of arXiv:1309.3796v3, `End(S_α)`**, for any first block `b_0`: for
symmetric `Q` and a grading of `T̃^λ` in which dots have positive degree, the block action of
Proposition 5.3 is a bijection from `R(b_0) ⊗ R^{λ_1}(b_1) ⊗ ⋯ ⊗ R^{λ_ℓ}(b_ℓ)` onto
`End_{T̃^λ}(S_α)`. -/
theorem bijective_blockAction (hQ : KLRSymm Q) (G : GradingDatum (stendhalQ Q Λ))
    (hG : ∀ a, 0 < G.degX a) (hb : blockPrefix b (ℓ + 1) = ν) :
    Function.Bijective (blockAction Q Λ hb) := by
  refine ⟨fun β β' h => ?_, fun f => ?_⟩
  · refine blockAction_rootStandardUnit_injective hQ (stendhalBlackGrading G)
      (fun i => hG (.inl i)) Λ b hb ?_
    exact LinearMap.congr_fun h _
  · obtain ⟨c, rfl⟩ := exists_rootAction_eq (blockRoot b) f
    exact exists_blockAction_eq_rootAction_of_grading hQ G hG hb c

/-- **Proposition 5.26 of arXiv:1309.3796v3**: `End_{T̃^λ}(S_α) ≅ R(b_0) ⊗ R^{λ_1}(b_1) ⊗ ⋯ ⊗
R^{λ_ℓ}(b_ℓ)` through the block action, for symmetric `Q` and a grading in which dots have
positive degree. -/
def blockActionEquiv (hQ : KLRSymm Q) (G : GradingDatum (stendhalQ Q Λ))
    (hG : ∀ a, 0 < G.degX a) (hb : blockPrefix b (ℓ + 1) = ν) :
    BlockAlgebra k Q Λ b ≃ₐ[k]
      Module.End (StendhalAlgebra k Q Λ ν)ᵐᵒᵖ (rootStandard (ν := ν) Q Λ (blockRoot b)) :=
  AlgEquiv.ofBijective (blockAction Q Λ hb) (bijective_blockAction hQ G hG hb)

theorem blockActionEquiv_apply (hQ : KLRSymm Q) (G : GradingDatum (stendhalQ Q Λ))
    (hG : ∀ a, 0 < G.degX a) (hb : blockPrefix b (ℓ + 1) = ν) (β : BlockAlgebra k Q Λ b) :
    blockActionEquiv hQ G hG hb β = blockAction Q Λ hb β :=
  rfl

end Bijective

section FullyFaithful

variable {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {b : Fin (ℓ + 1) → Multiset I}

local notation "T" => StendhalAlgebra k Q Λ (blockPrefix b (ℓ + 1))
local notation "S" => rootStandard (ν := blockPrefix b (ℓ + 1)) Q Λ (blockRoot b)
local notation "B" => BlockAlgebra k Q Λ b

/-- A shortcut for the block action as a scalar action; the search through submodule
actions does not terminate here. -/
local instance standardBlockSMul : SMul (BlockAlgebra k Q Λ b)ᵐᵒᵖᵐᵒᵖ S :=
  (standardBlockModule (Q := Q) (Λ := Λ) (b := b)).toDistribMulAction.toMulAction.toSMul

instance standardBlockModule_isScalarTower : IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖᵐᵒᵖ S where
  smul_assoc c a s := by
    induction a using MulOpposite.rec' with | _ a =>
    induction a using MulOpposite.rec' with | _ x =>
    change blockAction Q Λ (b := b) rfl (c • x) s = c • blockAction Q Λ (b := b) rfl x s
    rw [map_smul, LinearMap.smul_apply]

/-- **`[e_α]` is a free corner generator of `S_α`** (arXiv:1309.3796v3, proof of
Proposition 5.26): it generates `S_α` over `T̃^λ`, is fixed by `e_α`, and `S_α e_α` is free of rank
one on it over the block algebra. -/
theorem isCornerGenerator_rootStandardUnit (hQ : KLRSymm Q) (G : GradingDatum (stendhalQ Q Λ))
    (hG : ∀ a, 0 < G.degX a) :
    BalancedTensor.IsCornerGenerator (BlockAlgebra k Q Λ b)ᵐᵒᵖ (op (rootIdem Q Λ (blockRoot b)) : (StendhalAlgebra k Q Λ (blockPrefix b (ℓ + 1)))ᵐᵒᵖ)
      (rootStandardUnit Q Λ (blockPrefix b (ℓ + 1)) (blockRoot b)) where
  fix := by
    apply Subtype.ext
    change Submodule.Quotient.mk (rootIdem Q Λ (blockRoot b) * rootIdem Q Λ (blockRoot b)) =
      Submodule.Quotient.mk (rootIdem Q Λ (blockRoot b))
    rw [(isIdempotentElem_rootIdem (blockRoot b)).eq]
  gen s := by
    obtain ⟨z, hz, rfl⟩ := exists_eq_rootStandardMk s
    refine ⟨op z, Subtype.ext ?_⟩
    change Submodule.Quotient.mk (rootIdem Q Λ (blockRoot b) * z) = Submodule.Quotient.mk z
    rw [hz]
  corner s := by
    obtain ⟨z, hz, rfl⟩ := exists_eq_rootStandardMk s
    have he := isIdempotentElem_rootIdem (Q := Q) (Λ := Λ) (ν := blockPrefix b (ℓ + 1))
      (blockRoot b)
    let c : he.Corner := KLR.Corner.mk (z * rootIdem Q Λ (blockRoot b)) (by
      rw [← mul_assoc, hz, mul_assoc, he.eq])
    obtain ⟨β, hβ⟩ := exists_blockAction_eq_rootAction_of_grading hQ G hG rfl c
    refine ⟨op β, ?_⟩
    change _ = blockAction Q Λ (b := b) rfl β _
    rw [hβ]
    unfold rootStandardUnit
    rw [rootAction_mk]
    apply Subtype.ext
    rw [val_op_smul_rootStandardMk]
    change _ = Submodule.Quotient.mk (z * rootIdem Q Λ (blockRoot b) * rootIdem Q Λ (blockRoot b))
    rw [mul_assoc, he.eq]
  free a ha := by
    induction a using MulOpposite.rec' with | _ β =>
    have h0 := blockAction_rootStandardUnit_injective hQ (stendhalBlackGrading G)
      (fun i => hG (.inl i)) Λ b rfl (a₁ := β) (a₂ := 0) (by
        change blockAction Q Λ (b := b) rfl β _ = blockAction Q Λ (b := b) rfl 0 _
        rw [map_zero, LinearMap.zero_apply]
        exact ha)
    rw [h0, op_zero]

/-- **Proposition 5.26 of arXiv:1309.3796v3, full faithfulness of the standardization of
Definition 5.4**, for any first block `b_0`: for symmetric `Q` and a grading in which dots have
positive degree, `g ↦ g ⊗ 1` is a bijection `Hom_B(M, M') ≅ Hom_{T̃^λ}(M ⊗_B S_α, M' ⊗_B S_α)`
for right modules `M`, `M'` over the block algebra `B`. -/
theorem standardizationMap_bijective (hQ : KLRSymm Q) (G : GradingDatum (stendhalQ Q Λ))
    (hG : ∀ a, 0 < G.degX a) (M M' : Type*) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] [AddCommGroup M'] [Module k M'] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M']
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M'] :
    Function.Bijective (fun g : M →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M' => standardizationMap (Q := Q) (Λ := Λ) g) :=
  (isCornerGenerator_rootStandardUnit hQ G hG).mapRight_bijective

end FullyFaithful

end StendhalAlgebra

end Categorification.Stendhal
