/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.StandardModuleReflection
import Categorification.WeightedKLR.RedStrands.StandardRootDecomposition
import Categorification.WeightedKLR.RedStrands.Standardization

/-!
# The left root standard module and the reflected block action

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1,
Proposition 5.3 and Definition 5.4, in the left-module form of the induced model.

For a root function `α` none of whose sequences is violated (for instance `α(0) = 0`), the
standard module `S_α` of Webster is a direct sum of the `S_s` (`rootStandardEquiv`), and each
`S_s` is the horizontal reflection of the left standard module `T^λ e(s) / U_s`
(`standardModuleReflectEquiv`). The left root standard module `S^L_α = ⊕_s T^λ e(s) / U_s`
is therefore the reflection of `S_α` (`rootReflectEquiv`, with `[y a] ↦ flip(a) [flip(y)]`),
and the block action of Proposition 5.3 on `S_α` transports to an action on `S^L_α` by
`T^λ`-module endomorphisms (`leftBlockAction`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR MulOpposite

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

local notation "A" => StendhalAlgebra k Q Λ ν
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "mk" => TensorProductAlgebra.mk Q Λ ν

namespace StendhalAlgebra

variable (Q Λ) in
/-- **The left root standard module** `S^L_α = ⊕_s T^λ e(s) / U_s`, over the red-ordered
sequences `s` of root function `α`. -/
abbrev LeftRootStandard (α : Fin ℓ → I → ℕ) : Type :=
  (s : RootSeq (ν := ν) α) → leftStandard Q Λ s.1 (RootSeq.isRedOrdered α s)

variable {α : Fin ℓ → I → ℕ}

/-- No sequence of root function `α` is violated. -/
def RootNonViolated (α : Fin ℓ → I → ℕ) : Prop := ∀ s ∈ rootSet ν α, ¬ IsViolated s

theorem op_algebraMap_smul_quotient (U : Submodule Aᵐᵒᵖ A) (c : k) (v : A ⧸ U) :
    op (algebraMap k A c) • v = c • v := by
  induction v using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, op_smul_eq_mul,
      ← Algebra.commutes, ← Algebra.smul_def]

theorem op_algebraMap_smul_submodule {U : Submodule Aᵐᵒᵖ A} (P : Submodule Aᵐᵒᵖ (A ⧸ U)) (c : k)
    (v : P) : op (algebraMap k A c) • v = c • v :=
  Subtype.ext (op_algebraMap_smul_quotient U c v.1)

theorem tensorFlip_mk_algebraMap (c : k) : tensorFlip (mk (algebraMap k A c)) = algebraMap k T c := by
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, tensorFlip_one,
    ← Algebra.algebraMap_eq_smul_one]

variable (Q Λ) in
/-- The reflection `S_α → S^L_α`, `[e_α y] ↦ ([flip(e(s) y)])_s`. -/
def rootReflect : rootStandard (ν := ν) Q Λ α →ₗ[k] LeftRootStandard (ν := ν) Q Λ α where
  toFun v s := standardModuleReflect s.1 (RootSeq.isRedOrdered α s) (rootStandardToPi Q Λ α v s)
  map_add' v w := funext fun s => by simp only [map_add, Pi.add_apply]
  map_smul' c v := funext fun s => by
    rw [← op_algebraMap_smul_submodule, map_smul, Pi.smul_apply, standardModuleReflect_op_smul,
      tensorFlip_mk_algebraMap, algebraMap_smul]
    rfl

theorem rootReflect_apply (v : rootStandard (ν := ν) Q Λ α) (s : RootSeq (ν := ν) α) :
    rootReflect Q Λ v s =
      standardModuleReflect s.1 (RootSeq.isRedOrdered α s) (rootStandardToPi Q Λ α v s) := rfl

/-- The reflection is twisted linear: `[y a] ↦ flip(a) [flip(y)]`. -/
theorem rootReflect_op_smul (a : A) (v : rootStandard (ν := ν) Q Λ α) :
    rootReflect Q Λ (op a • v) = tensorFlip (mk a) • rootReflect Q Λ v := by
  funext s
  rw [rootReflect_apply, map_smul, Pi.smul_apply, standardModuleReflect_op_smul]
  rfl

theorem rootReflect_bijective (hα : RootNonViolated (ν := ν) α) :
    Function.Bijective (rootReflect (ν := ν) (α := α) Q Λ) := by
  have hb : Function.Bijective fun (w : (s : RootSeq (ν := ν) α) →
      standardModule Q Λ s.1 (RootSeq.isRedOrdered α s)) (s : RootSeq (ν := ν) α) =>
      standardModuleReflect s.1 (RootSeq.isRedOrdered α s) (w s) := by
    refine ⟨fun w w' h => funext fun s => ?_, fun z => ?_⟩
    · exact standardModuleReflect_injective s.1 _ (hα s.1 s.2) (congrFun h s)
    · exact ⟨fun s => (standardModuleReflect_surjective s.1 _ (z s)).choose,
        funext fun s => (standardModuleReflect_surjective s.1 _ (z s)).choose_spec⟩
  exact hb.comp (rootStandardEquiv Q Λ α).bijective

variable (Q Λ) in
/-- **`S_α` is the reflection of the left root standard module** `S^L_α`, when no sequence of
root function `α` is violated. -/
def rootReflectEquiv (hα : RootNonViolated (ν := ν) α) :
    rootStandard (ν := ν) Q Λ α ≃ₗ[k] LeftRootStandard (ν := ν) Q Λ α :=
  LinearEquiv.ofBijective (rootReflect Q Λ) (rootReflect_bijective hα)

theorem rootReflectEquiv_apply (hα : RootNonViolated (ν := ν) α)
    (v : rootStandard (ν := ν) Q Λ α) : rootReflectEquiv Q Λ hα v = rootReflect Q Λ v := rfl

theorem tensorFlip_mk_surjective : Function.Surjective fun a : A => tensorFlip (mk a) := by
  intro t
  obtain ⟨a, ha⟩ := tensorProductAlgebra_mk_surjective (k := k) (Q := Q) (Λ := Λ) (ν := ν)
    (tensorFlip t)
  exact ⟨a, by simp only [ha, tensorFlip_tensorFlip]⟩

theorem rootReflectEquiv_symm_smul (hα : RootNonViolated (ν := ν) α) (a : A)
    (w : LeftRootStandard (ν := ν) Q Λ α) :
    (rootReflectEquiv Q Λ hα).symm (tensorFlip (mk a) • w) =
      op a • (rootReflectEquiv Q Λ hα).symm w := by
  rw [LinearEquiv.symm_apply_eq, rootReflectEquiv_apply, rootReflect_op_smul,
    ← rootReflectEquiv_apply hα, LinearEquiv.apply_symm_apply]

variable (Q Λ) in
/-- Conjugation by the reflection: an endomorphism of the right `T̃^λ`-module `S_α` gives an
endomorphism of the left `T^λ`-module `S^L_α`. -/
def rootReflectConj (hα : RootNonViolated (ν := ν) α) :
    Module.End Aᵐᵒᵖ (rootStandard (ν := ν) Q Λ α) →ₐ[k]
      Module.End T (LeftRootStandard (ν := ν) Q Λ α) where
  toFun f :=
    { toFun := fun w => rootReflectEquiv Q Λ hα (f ((rootReflectEquiv Q Λ hα).symm w))
      map_add' := fun w w' => by simp only [map_add]
      map_smul' := fun t w => by
        obtain ⟨a, rfl⟩ := tensorFlip_mk_surjective (Q := Q) (Λ := Λ) (ν := ν) t
        rw [rootReflectEquiv_symm_smul, map_smul, rootReflectEquiv_apply, rootReflect_op_smul]
        rfl }
  map_one' := LinearMap.ext fun w => by
    change rootReflectEquiv Q Λ hα ((rootReflectEquiv Q Λ hα).symm w) = w
    exact LinearEquiv.apply_symm_apply _ _
  map_mul' f g := LinearMap.ext fun w => by
    change rootReflectEquiv Q Λ hα (f (g _)) =
      rootReflectEquiv Q Λ hα (f ((rootReflectEquiv Q Λ hα).symm
        (rootReflectEquiv Q Λ hα (g ((rootReflectEquiv Q Λ hα).symm w)))))
    rw [LinearEquiv.symm_apply_apply]
  map_zero' := LinearMap.ext fun w => by
    change rootReflectEquiv Q Λ hα 0 = 0
    exact map_zero _
  map_add' f g := LinearMap.ext fun w => by
    change rootReflectEquiv Q Λ hα (f _ + g _) = _ + _
    exact map_add _ _ _
  commutes' c := LinearMap.ext fun w => by
    change rootReflectEquiv Q Λ hα (c • (rootReflectEquiv Q Λ hα).symm w) = c • w
    rw [map_smul, LinearEquiv.apply_symm_apply]

theorem rootReflectConj_apply (hα : RootNonViolated (ν := ν) α)
    (f : Module.End Aᵐᵒᵖ (rootStandard (ν := ν) Q Λ α)) (v : rootStandard (ν := ν) Q Λ α) :
    rootReflectConj Q Λ hα f (rootReflectEquiv Q Λ hα v) = rootReflectEquiv Q Λ hα (f v) := by
  change rootReflectEquiv Q Λ hα (f ((rootReflectEquiv Q Λ hα).symm _)) = _
  rw [LinearEquiv.symm_apply_apply]

section Blocks

variable {b : Fin (ℓ + 1) → Multiset I}

theorem rootNonViolated_blockRoot (hℓ : 0 < ℓ) (hb0 : b 0 = 0) :
    RootNonViolated (ν := blockPrefix b (ℓ + 1)) (blockRoot b) :=
  fun _ hs => not_isViolated_of_mem_rootSet_blockRoot hℓ hb0 hs

variable (Q Λ) in
/-- **The reflected block action** (arXiv:1309.3796v3, Proposition 5.3, left form): for
`b_0 = 0`, the algebra `R(b_0) ⊗ R^{λ_0}(b_1) ⊗ ⋯ ⊗ R^{λ_{ℓ-1}}(b_ℓ)` acts on the left root
standard module `S^L_α` by `T^λ`-module endomorphisms, through the reflection
`S_α ≅ S^L_α`. -/
def leftBlockAction (hℓ : 0 < ℓ) (hb0 : b 0 = 0) :
    BlockAlgebra k Q Λ b →ₐ[k]
      Module.End (TensorProductAlgebra k Q Λ (blockPrefix b (ℓ + 1)))
        (LeftRootStandard (ν := blockPrefix b (ℓ + 1)) Q Λ (blockRoot b)) :=
  (rootReflectConj Q Λ (rootNonViolated_blockRoot hℓ hb0)).comp (blockAction Q Λ (b := b) rfl)

theorem leftBlockAction_rootReflect (hℓ : 0 < ℓ) (hb0 : b 0 = 0) (x : BlockAlgebra k Q Λ b)
    (v : rootStandard (ν := blockPrefix b (ℓ + 1)) Q Λ (blockRoot b)) :
    leftBlockAction Q Λ hℓ hb0 x (rootReflect Q Λ v) =
      rootReflect Q Λ (blockAction Q Λ (b := b) rfl x v) :=
  rootReflectConj_apply _ _ v

end Blocks

end StendhalAlgebra

end Categorification.Stendhal
