/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EiFiltrationStatement
import Categorification.WeightedKLR.RedStrands.FiSequence
import Categorification.WeightedKLR.RedStrands.BlackInductionExact

/-!
# The statement of the `Fᵢ`-filtration of a standardization

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.5, `F`-part. For blocks `b` and a family `b'` which agrees with `b` except that
`b'_{k+1} = i + b_{k+1}`, the last-strand inclusion on the `k`-th cyclotomic factor gives a
nonunital map of block algebras `B → B'` (`blockBlackRes`), and `ₖFᵢ M = M ⊗_B B' e` is induction
of a right `B`-module along it (`BlockBlackInd`). For a right module `M` over the block algebra
`B` of blocks `b` with total weight `ν`, `Fᵢ(M ⊗_B S^L_α)` has a filtration whose subquotients are
the standardizations `ₖFᵢ M ⊗_{B'} S^L_{α'}`, one for each of the `ℓ` cyclotomic blocks.

As for the `E`-part, the statement carries an action `ρ : C → End_B(M)` of an auxiliary algebra
`C`, and the filtration is one of modules over `T(i + ν) ⊗ C` (`FiFiltration`); `C = k` gives
Proposition 5.5. This file states it.

## Main definitions

* `BlockBlackInd`: the right `B'`-module `ₖFᵢ M`; `blockBlackIndEnd`: `ₖFᵢ` on endomorphisms.
* `fiTop`, `fiLayer`: `Fᵢ(M ⊗_B S^L_α)` and `ₖFᵢ M ⊗_{B'} S^L_{α'}` over `T(i + ν) ⊗ C`.
* `FiFiltration`: the statement for `ℓ` red strands.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong ModuleFiltration
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k]

section BlockBlackInd

variable {ℓ : ℕ} (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (κ : Fin ℓ)
  {b b' : Fin (ℓ + 1) → Multiset I} (h0 : leftBlock b' = leftBlock b)
  (hr : ∀ r, r ≠ κ → rightBlock b' r = rightBlock b r)
  (hκ : {i} + rightBlock b' κ = rightBlock b κ)

theorem blockBlackResOp_smul (c : k) (t : (BlockAlgebra k Q Λ b')ᵐᵒᵖ) :
    blockBlackResOp Q Λ i κ h0 hr hκ (c • t) = c • blockBlackResOp Q Λ i κ h0 hr hκ t :=
  congrArg op (map_smul (blockBlackRes Q Λ i κ h0 hr hκ) c t.unop)

variable (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b')ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b')ᵐᵒᵖ M]

/-- **`ₖFᵢ M = M ⊗_B B' e`** as a right module over the block algebra of `b`. -/
abbrev BlockBlackInd := IndK k M (blockBlackResOp Q Λ i κ h0 hr hκ)

/-- **`ₖFᵢ` on endomorphisms**, as a map of algebras. -/
abbrev blockBlackIndEnd : Module.End (BlockAlgebra k Q Λ b')ᵐᵒᵖ M →ₐ[k]
    Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ (BlockBlackInd Q Λ i κ h0 hr hκ M) :=
  IndK.endAlg (blockBlackResOp Q Λ i κ h0 hr hκ) M (blockBlackResOp_smul Q Λ i κ h0 hr hκ)

end BlockBlackInd

section Statement

variable (Q : I → I → MvPolynomial (Fin 2) k) (i : I)

theorem appendBlackNU_smul {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (c : k)
    (t : TensorProductAlgebra k Q Λ ν) :
    appendBlackNU (Q := Q) (Λ := Λ) i ν (c • t) = c • appendBlackNU (Q := Q) (Λ := Λ) i ν t :=
  map_smul (appendBlack Q Λ i ν) c t

/-- The action of `C` on `Fᵢ(M ⊗_B S^L_α)`. -/
abbrev fiTopAction {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (b : Fin (ℓ + 1) → Multiset I) (ν : Multiset I)
    (hb : blockPrefix b (ℓ + 1) = ν) (hα : RootNonViolated (ν := ν) (blockRoot b)) (C : Type)
    [Ring C] [Algebra k C] (M : Type) [AddCommGroup M] [Module k M]
    [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) :
    C →ₐ[k] Module.End (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν))
      (IndK k (LeftStandardization Q Λ b hb hα M) (appendBlackNU (Q := Q) (Λ := Λ) i ν)) :=
  (IndK.endAlg (appendBlackNU (Q := Q) (Λ := Λ) i ν) (LeftStandardization Q Λ b hb hα M)
    (appendBlackNU_smul Q i Λ ν)).comp (standardAction Q Λ b hb hα C M ρ)

/-- **`Fᵢ(M ⊗_B S^L_α)`** as a module over `T(i + ν) ⊗ C`, `C` acting through `ρ`. -/
abbrev fiTop {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (b : Fin (ℓ + 1) → Multiset I) (ν : Multiset I)
    (hb : blockPrefix b (ℓ + 1) = ν) (hα : RootNonViolated (ν := ν) (blockRoot b)) (C : Type)
    [Ring C] [Algebra k C] (M : Type) [AddCommGroup M] [Module k M]
    [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) :
    ModuleCat.{0} (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν) ⊗[k] C) :=
  ModuleCat.of _ (TensorAct k (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) C
    (fiTopAction Q i Λ b ν hb hα C M ρ))

/-- **`ₖFᵢ M ⊗_{B'} S^L_{α'}`** as a module over `T(i + ν) ⊗ C`. -/
abbrev fiLayer {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) {b b' : Fin (ℓ + 1) → Multiset I} (ν : Multiset I)
    (κ : Fin ℓ) (h0 : leftBlock b = leftBlock b')
    (hr : ∀ r, r ≠ κ → rightBlock b r = rightBlock b' r)
    (hκ : {i} + rightBlock b κ = rightBlock b' κ)
    (hb' : blockPrefix b' (ℓ + 1) = ({i} : Multiset I) + ν)
    (hα' : RootNonViolated (ν := ({i} : Multiset I) + ν) (blockRoot b')) (C : Type) [Ring C]
    [Algebra k C] (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) :
    ModuleCat.{0} (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν) ⊗[k] C) :=
  ModuleCat.of _ (TensorAct k (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) C
    (BalancedTensor.endAction k (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν))
      (BlockLeftStandard Q Λ b' hb' hα') ((blockBlackIndEnd Q Λ i κ h0 hr hκ M).comp ρ)))

/-- **Webster, Proposition 5.5, `F`-part, for `ℓ` red strands**, with a commuting action: for
blocks `b` with `b_0 = 0` and total weight `ν`, and for each `κ` blocks `b'_κ` with
`(b'_κ)_{κ+1} = i + b_{κ+1}` agreeing with `b` elsewhere, `Fᵢ(M ⊗_B S^L_α)` has a filtration over
`T(i + ν) ⊗ C` whose subquotients are the `ₖFᵢ M ⊗ S^L_{α'_κ}`, each `κ` once. -/
def FiFiltration (ℓ : ℕ) : Prop :=
  ∀ (Λ : Fin ℓ → I →₀ ℕ) (b : Fin (ℓ + 1) → Multiset I) (ν : Multiset I), leftBlock b = 0 →
    ∀ (hb : blockPrefix b (ℓ + 1) = ν) (hα : RootNonViolated (ν := ν) (blockRoot b))
      (b' : Fin ℓ → Fin (ℓ + 1) → Multiset I)
      (h0 : ∀ κ, leftBlock b = leftBlock (b' κ))
      (hr : ∀ κ r, r ≠ κ → rightBlock b r = rightBlock (b' κ) r)
      (hκ : ∀ κ, {i} + rightBlock b κ = rightBlock (b' κ) κ)
      (hb' : ∀ κ, blockPrefix (b' κ) (ℓ + 1) = ({i} : Multiset I) + ν)
      (hα' : ∀ κ, RootNonViolated (ν := ({i} : Multiset I) + ν) (blockRoot (b' κ)))
      (C : Type) [Ring C] [Algebra k C]
      (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
      [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
      (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M),
      ∃ m : List (Fin ℓ), m.Nodup ∧ (∀ κ, κ ∈ m) ∧
        HasFiltration (fun κ => fiLayer Q i Λ ν κ (h0 κ) (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ)
          m (fiTop Q i Λ b ν hb hα C M ρ)

/-- **The case without red strands**: `T(i + ν)` is zero, and so is `Fᵢ(M ⊗_B S^L_α)`. -/
theorem fiFiltration_zero : FiFiltration (k := k) Q i 0 := by
  intro Λ b ν _ hb hα b' h0 hr hκ hb' hα' C _ _ M _ _ _ _ ρ
  refine ⟨[], List.nodup_nil, fun κ => κ.elim0, HasFiltration.zero ?_⟩
  have hΛ : Λ = (Fin.elim0 : Fin 0 → I →₀ ℕ) := funext fun j => j.elim0
  subst hΛ
  have : Subsingleton (TensorProductAlgebra k Q (Fin.elim0 : Fin 0 → I →₀ ℕ)
      (({i} : Multiset I) + ν)) :=
    subsingleton_emptyTensorAlgebra Q (by simp)
  have hT : Subsingleton (TensorProductAlgebra k Q (Fin.elim0 : Fin 0 → I →₀ ℕ)
      (({i} : Multiset I) + ν) ⊗[k] C) := by
    apply subsingleton_of_zero_eq_one
    rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : TensorProductAlgebra k Q
      (Fin.elim0 : Fin 0 → I →₀ ℕ) (({i} : Multiset I) + ν)) 0, TensorProduct.zero_tmul]
  exact Module.subsingleton (TensorProductAlgebra k Q (Fin.elim0 : Fin 0 → I →₀ ℕ)
    (({i} : Multiset I) + ν) ⊗[k] C) _

end Statement

end StendhalAlgebra

end Categorification.Stendhal
