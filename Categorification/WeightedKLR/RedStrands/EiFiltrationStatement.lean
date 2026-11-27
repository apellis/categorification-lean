/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StandardSplitFiltration
import Categorification.WeightedKLR.RedStrands.BlackResCast
import Categorification.WeightedKLR.RedStrands.BlockBlackRes

/-!
# The statement of the `Eᵢ`-filtration of a standardization

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.5, `E`-part. For a right module `M` over the block algebra `B` of blocks `b` with
total weight `i + ν₀`, `Eᵢ(M ⊗_B S^L_α)` has a filtration whose subquotients are the
standardizations `ₖEᵢ M ⊗_{B'} S^L_{α'}` of the modules `ₖEᵢ M = M e` (`BlockBlackRes`), one for
each `k` with `i` in the block `b_{k+1}`, each label occurring once.

The proof is an induction on the number `ℓ` of red strands, through the two-piece
standardization. The induction applies the statement for `ℓ` red strands to `M` regarded as a
module over the block algebra of the first `ℓ` of `ℓ + 1` red strands, on which the last
cyclotomic factor acts by commuting endomorphisms. The statement is therefore made for a module
`M` with an action `ρ : C → End_B(M)` of an auxiliary algebra `C`, and the filtration is one of
modules over `T(ν₀) ⊗ C` (`EiFiltration`); `C = k` gives Proposition 5.5. This file states it
and proves the case without red strands (`eiFiltration_zero`), where it is vacuous since the
leftmost block is empty.

## Main definitions

* `blockBlackResEnd`: `ₖEᵢ` on endomorphisms.
* `eiTop`, `eiLayer`: `Eᵢ(M ⊗_B S^L_α)` and `ₖEᵢ M ⊗_{B'} S^L_{α'}` over `T(ν₀) ⊗ C`.
* `EiFiltration`: the statement for `ℓ` red strands.
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

section BlockBlackResEnd

variable {ℓ : ℕ} (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (κ : Fin ℓ)
  {b b' : Fin (ℓ + 1) → Multiset I} (h0 : leftBlock b' = leftBlock b)
  (hr : ∀ r, r ≠ κ → rightBlock b' r = rightBlock b r)
  (hκ : {i} + rightBlock b' κ = rightBlock b κ)
  (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]

/-- **`ₖEᵢ` on endomorphisms**, as a map of algebras. -/
def blockBlackResEnd : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M →ₐ[k]
    Module.End (BlockAlgebra k Q Λ b')ᵐᵒᵖ (BlockBlackRes Q Λ i κ h0 hr hκ M) where
  toFun g := Res.map g
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := LinearMap.ext fun m => Res.ext (by
    change (algebraMap k (Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) c) m.val =
      (blockBlackResOp Q Λ i κ h0 hr hκ (algebraMap k (BlockAlgebra k Q Λ b')ᵐᵒᵖ c)) • m.val
    rw [Module.algebraMap_end_apply]
    change c • m.val = (op (blockBlackRes Q Λ i κ h0 hr hκ (algebraMap k _ c)) :
      (BlockAlgebra k Q Λ b)ᵐᵒᵖ) • m.val
    rw [Algebra.algebraMap_eq_smul_one, map_smul, op_smul, smul_assoc]
    exact congrArg (c • ·) m.prop.symm)

@[simp] theorem blockBlackResEnd_val (g : Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M)
    (m : BlockBlackRes Q Λ i κ h0 hr hκ M) : (blockBlackResEnd Q Λ i κ h0 hr hκ M g m).val =
      g m.val := rfl

end BlockBlackResEnd

section Statement

variable (Q : I → I → MvPolynomial (Fin 2) k) (i : I)

/-- The action of `C` on `M ⊗_B S^L_α`. -/
abbrev standardAction {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (b : Fin (ℓ + 1) → Multiset I) {ν : Multiset I}
    (hb : blockPrefix b (ℓ + 1) = ν) (hα : RootNonViolated (ν := ν) (blockRoot b)) (C : Type)
    [Ring C] [Algebra k C] (M : Type) [AddCommGroup M] [Module k M]
    [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) :
    C →ₐ[k] Module.End (TensorProductAlgebra k Q Λ ν) (LeftStandardization Q Λ b hb hα M) :=
  BalancedTensor.endAction k (TensorProductAlgebra k Q Λ ν) (BlockLeftStandard Q Λ b hb hα) ρ

/-- The action of `C` on `Eᵢ(M ⊗_B S^L_α)`. -/
def eiTopAction {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (b : Fin (ℓ + 1) → Multiset I) (ν₀ : Multiset I)
    (hb : blockPrefix b (ℓ + 1) = ({i} : Multiset I) + ν₀)
    (hα : RootNonViolated (ν := ({i} : Multiset I) + ν₀) (blockRoot b)) (C : Type) [Ring C]
    [Algebra k C] (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) :
    C →ₐ[k] Module.End (TensorProductAlgebra k Q Λ ν₀)
      (BlackRes (Q := Q) (Λ := Λ) i ν₀ (LeftStandardization Q Λ b hb hα M)) where
  toFun c := blackResMap i (standardAction Q Λ b hb hα C M ρ c)
  map_one' := LinearMap.ext fun m => Subtype.ext
    (LinearMap.congr_fun (map_one (standardAction Q Λ b hb hα C M ρ)) m.1)
  map_mul' c c' := LinearMap.ext fun m => Subtype.ext
    (LinearMap.congr_fun (map_mul (standardAction Q Λ b hb hα C M ρ) c c') m.1)
  map_zero' := LinearMap.ext fun m => Subtype.ext
    (LinearMap.congr_fun (map_zero (standardAction Q Λ b hb hα C M ρ)) m.1)
  map_add' c c' := LinearMap.ext fun m => Subtype.ext
    (LinearMap.congr_fun (map_add (standardAction Q Λ b hb hα C M ρ) c c') m.1)
  commutes' c := LinearMap.ext fun m => Subtype.ext ((LinearMap.congr_fun
    ((standardAction Q Λ b hb hα C M ρ).commutes c) m.1).trans (by
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
      rfl))

theorem eiTopAction_val {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (b : Fin (ℓ + 1) → Multiset I)
    (ν₀ : Multiset I) (hb : blockPrefix b (ℓ + 1) = ({i} : Multiset I) + ν₀)
    (hα : RootNonViolated (ν := ({i} : Multiset I) + ν₀) (blockRoot b)) (C : Type) [Ring C]
    [Algebra k C] (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) (c : C)
    (m : BlackRes (Q := Q) (Λ := Λ) i ν₀ (LeftStandardization Q Λ b hb hα M)) :
    (eiTopAction Q i Λ b ν₀ hb hα C M ρ c m).1 = standardAction Q Λ b hb hα C M ρ c m.1 := rfl

/-- **`Eᵢ(M ⊗_B S^L_α)`** as a module over `T(ν₀) ⊗ C`, `C` acting through `ρ`. -/
abbrev eiTop {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (b : Fin (ℓ + 1) → Multiset I) (ν₀ : Multiset I)
    (hb : blockPrefix b (ℓ + 1) = ({i} : Multiset I) + ν₀)
    (hα : RootNonViolated (ν := ({i} : Multiset I) + ν₀) (blockRoot b)) (C : Type) [Ring C]
    [Algebra k C] (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) :
    ModuleCat.{0} (TensorProductAlgebra k Q Λ ν₀ ⊗[k] C) :=
  ModuleCat.of _ (TensorAct k (TensorProductAlgebra k Q Λ ν₀) C
    (eiTopAction Q i Λ b ν₀ hb hα C M ρ))

/-- **`ₖEᵢ M ⊗_{B'} S^L_{α'}`** as a module over `T(ν₀) ⊗ C`. -/
abbrev eiLayer {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) {b b' : Fin (ℓ + 1) → Multiset I} (ν₀ : Multiset I)
    (κ : Fin ℓ) (h0 : leftBlock b' = leftBlock b)
    (hr : ∀ r, r ≠ κ → rightBlock b' r = rightBlock b r)
    (hκ : {i} + rightBlock b' κ = rightBlock b κ) (hb' : blockPrefix b' (ℓ + 1) = ν₀)
    (hα' : RootNonViolated (ν := ν₀) (blockRoot b')) (C : Type) [Ring C] [Algebra k C]
    (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M) :
    ModuleCat.{0} (TensorProductAlgebra k Q Λ ν₀ ⊗[k] C) :=
  ModuleCat.of _ (TensorAct k (TensorProductAlgebra k Q Λ ν₀) C
    (BalancedTensor.endAction k (TensorProductAlgebra k Q Λ ν₀) (BlockLeftStandard Q Λ b' hb' hα')
      ((blockBlackResEnd Q Λ i κ h0 hr hκ M).comp ρ)))

/-- **Webster, Proposition 5.5, `E`-part, for `ℓ` red strands**, with a commuting action: for
blocks `b` with `b_0 = 0` and total weight `i + ν₀`, and for each `κ` with `i ∈ b_{κ+1}` blocks
`b'_κ` with `b_{κ+1} = i + (b'_κ)_{κ+1}` agreeing with `b` elsewhere, `Eᵢ(M ⊗_B S^L_α)` has a
filtration over `T(ν₀) ⊗ C` whose subquotients are the `ₖEᵢ M ⊗ S^L_{α'_κ}`, each `κ` once. -/
def EiFiltration (ℓ : ℕ) : Prop :=
  ∀ (Λ : Fin ℓ → I →₀ ℕ) (b : Fin (ℓ + 1) → Multiset I) (ν₀ : Multiset I), leftBlock b = 0 →
    ∀ (hb : blockPrefix b (ℓ + 1) = ({i} : Multiset I) + ν₀)
      (hα : RootNonViolated (ν := ({i} : Multiset I) + ν₀) (blockRoot b))
      (b' : {κ : Fin ℓ // i ∈ rightBlock b κ} → Fin (ℓ + 1) → Multiset I)
      (h0 : ∀ κ, leftBlock (b' κ) = leftBlock b)
      (hr : ∀ κ r, r ≠ κ.1 → rightBlock (b' κ) r = rightBlock b r)
      (hκ : ∀ κ, {i} + rightBlock (b' κ) κ.1 = rightBlock b κ.1)
      (hb' : ∀ κ, blockPrefix (b' κ) (ℓ + 1) = ν₀)
      (hα' : ∀ κ, RootNonViolated (ν := ν₀) (blockRoot (b' κ)))
      (C : Type) [Ring C] [Algebra k C]
      (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
      [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
      (ρ : C →ₐ[k] Module.End (BlockAlgebra k Q Λ b)ᵐᵒᵖ M),
      ∃ m : List {κ : Fin ℓ // i ∈ rightBlock b κ}, m.Nodup ∧ (∀ κ, κ ∈ m) ∧
        HasFiltration (fun κ => eiLayer Q i Λ ν₀ κ.1 (h0 κ) (hr κ) (hκ κ) (hb' κ) (hα' κ) C M ρ)
          m (eiTop Q i Λ b ν₀ hb hα C M ρ)

/-- **The case without red strands is vacuous**: the only block is the leftmost one, which is
empty, so the weight `i + ν₀` cannot occur. -/
theorem eiFiltration_zero : EiFiltration (k := k) Q i 0 := by
  intro Λ b ν₀ h00 hb
  have h1 : blockPrefix b 1 = leftBlock b := by
    rw [blockPrefix_succ b (Nat.zero_lt_succ 0), blockPrefix_zero, zero_add]
  rw [h1, h00] at hb
  exact absurd hb.symm (Multiset.singleton_add i ν₀ ▸ Multiset.cons_ne_zero)

end Statement

end StendhalAlgebra

end Categorification.Stendhal
