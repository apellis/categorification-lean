/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardization
import Categorification.WeightedKLR.RedStrands.IteratedStandardCharacter
import Categorification.WeightedKLR.RedStrands.Vacuum
import Categorification.KLR.CyclotomicSplit
import Categorification.Algebra.BalancedTensorScalar

/-!
# The standardization of Definition 5.4 with no red strands

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1. With no
red strands and an empty block `b_0 = 0`, the block algebra `R(0)` and the algebra `T^∅(0)` are
the ground field, the left standard module of the empty loading is a line, and the
standardization `M ⊗_B S^L_α` of a right module `M` over the block algebra is `M` itself
(`leftStandardizationZeroEquiv`), with `T^∅(0)` acting through the augmentation
(`leftStandardizationZeroEquiv_smul`).
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR MulOpposite StendhalAlgebra
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {k : Type} [Field k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- Every element of the KLR algebra with no strands is a scalar. -/
theorem klrZero_scalar (z : KLRAlgebra k Q (0 : Multiset I)) : ∃ c : k, z = algebraMap k _ c := by
  induction z using KLRAlgebra.klr_induction with
  | hadd u v hu hv =>
    obtain ⟨c, rfl⟩ := hu
    obtain ⟨d, rfl⟩ := hv
    exact ⟨c + d, (map_add _ c d).symm⟩
  | hmul u v hu hv =>
    obtain ⟨c, rfl⟩ := hu
    obtain ⟨d, rfl⟩ := hv
    exact ⟨c * d, (map_mul _ c d).symm⟩
  | hr r => exact ⟨r, rfl⟩
  | he s =>
    refine ⟨1, ?_⟩
    rw [map_one, ← KLRAlgebra.sum_e, Finset.sum_eq_single s
      (fun b _ hb => (hb (Subsingleton.elim _ _)).elim) (fun h => (h (Finset.mem_univ _)).elim)]
  | hx a => exact a.elim0
  | hψ j => exact ⟨0, by rw [KLRAlgebra.ψ_eq_zero j (by simp), map_zero]⟩

/-- Every element of the KLR algebra of an empty weight is a scalar. -/
theorem klr_scalar_of_eq_zero {ν : Multiset I} (h : ν = 0) (z : KLRAlgebra k Q ν) :
    ∃ c : k, z = algebraMap k _ c := by
  subst h
  exact klrZero_scalar Q z

/-- **With no red strands and `b_0 = 0`, every element of the block algebra is a scalar.** -/
theorem blockAlgebraZero_scalar (Λ : Fin 0 → I →₀ ℕ) (b : Fin 1 → Multiset I)
    (hb0 : b 0 = 0) (x : BlockAlgebra k Q Λ b) : ∃ c : k, x = algebraMap k _ c := by
  have hP : ∀ y : ⨂[k] r : Fin 0, CycKLR k Q (redCyc Λ r) (rightBlock b r),
      ∃ c : k, y = algebraMap k _ c := by
    intro y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      refine ⟨r, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, PiTensorProduct.one_def]
      exact congrArg (r • PiTensorProduct.tprod k ·) (funext fun i => i.elim0)
    | add y y' hy hy' =>
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨d, rfl⟩ := hy'
      exact ⟨c + d, (map_add _ c d).symm⟩
  induction x using TensorProduct.inductionOn with
  | tmul a y =>
    obtain ⟨c, rfl⟩ := klr_scalar_of_eq_zero Q hb0 a
    obtain ⟨d, rfl⟩ := hP y
    refine ⟨c * d, ?_⟩
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one c,
      Algebra.algebraMap_eq_smul_one d, Algebra.algebraMap_eq_smul_one (c * d),
      TensorProduct.smul_tmul_smul]
    exact TensorProduct.smul_tmul' _ _ _
  | add x x' hx hx' =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hx'
    exact ⟨c + d, (map_add _ c d).symm⟩

section Line

variable (Λ : Fin 0 → I →₀ ℕ)

omit [DecidableEq I] in
private theorem isEmpty_vacuumCard :
    IsEmpty (Fin (Multiset.card (stendhalWeight 0 (0 : Multiset I)))) := by
  rw [show Multiset.card (stendhalWeight 0 (0 : Multiset I)) = 0 by simp [stendhalWeight]]
  infer_instance

/-- The empty loading, as the unique sequence of any root function with no red strands. -/
def vacuumRootSeq (α : Fin 0 → I → ℕ) : RootSeq (ν := (0 : Multiset I)) α :=
  ⟨vacuumSeq, mem_rootSet.2 ⟨vacuumSeq_ordered, funext fun r => r.elim0⟩⟩

instance (α : Fin 0 → I → ℕ) : Unique (RootSeq (ν := (0 : Multiset I)) α) where
  default := vacuumRootSeq α
  uniq s := by
    have := isEmpty_vacuumCard (I := I)
    exact Subtype.ext (Subtype.ext (funext isEmptyElim))

private theorem leftUpper_vacuum' (s : Seq (stendhalWeight 0 (0 : Multiset I)))
    (hs : IsRedOrdered s) : leftUpper Q Λ s hs = ⊥ := by
  have := isEmpty_vacuumCard (I := I)
  refine le_antisymm (Submodule.span_le.2 ?_) bot_le
  rintro _ ⟨t, ht, a, hlt, rfl⟩
  obtain rfl : t = s := Subtype.ext (funext isEmptyElim)
  exact (hlt.2 hlt.1).elim

private theorem lIdeal_vacuum' (s : Seq (stendhalWeight 0 (0 : Multiset I)))
    (hs : IsRedOrdered s) : lIdeal (seqIdem Q Λ s hs) = ⊤ := by
  rw [show seqIdem Q Λ s hs = 1 from FirstWeight.vacuum_mk_e Λ s hs]
  exact eq_top_iff.2 fun y _ => mul_one y

/-- With no red strands, the standard module of the empty loading is the regular module. -/
def vacuumLeftStandardEquiv (s : Seq (stendhalWeight 0 (0 : Multiset I)))
    (hs : IsRedOrdered s) :
    leftStandard Q Λ s hs ≃ₗ[TensorProductAlgebra k Q Λ 0] TensorProductAlgebra k Q Λ 0 :=
  (Submodule.quotEquivOfEqBot _ (by
    rw [leftUpper_vacuum' Q Λ s hs, Submodule.comap_bot, Submodule.ker_subtype])).trans
    ((LinearEquiv.ofEq _ ⊤ (lIdeal_vacuum' Q Λ s hs)).trans Submodule.topEquiv)

variable (b : Fin 1 → Multiset I) (hb : blockPrefix b 1 = 0)
  (hα : RootNonViolated (ν := (0 : Multiset I)) (blockRoot b))

/-- **With no red strands the left standard module `S^L_α` is a line.** -/
def blockLeftStandardZeroEquiv : BlockLeftStandard Q Λ b hb hα ≃ₗ[k] k :=
  (LinearEquiv.piUnique k _).trans
    (((vacuumLeftStandardEquiv Q Λ _ _).restrictScalars k).trans
      (tensorProductAlgebraZeroEquiv Q Λ).toLinearEquiv)

end Line

section Standardization

variable (Λ : Fin 0 → I →₀ ℕ) (b : Fin 1 → Multiset I) (hb0 : b 0 = 0)
  (hb : blockPrefix b 1 = 0) (hα : RootNonViolated (ν := (0 : Multiset I)) (blockRoot b))
  (M : Type*) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]

omit [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] in
theorem op_op_algebraMap_smul_blockLeftStandard (c : k)
    (v : BlockLeftStandard Q Λ b hb hα) :
    (op (op (algebraMap k (BlockAlgebra k Q Λ b) c)) : (BlockAlgebra k Q Λ b)ᵐᵒᵖᵐᵒᵖ) • v =
      c • v := by
  rw [op_op_smul_blockLeftStandard, AlgHom.commutes]
  rfl

/-- **With no red strands and `b_0 = 0`, the standardization is the identity**:
`M ⊗_B S^L_α ≅ M`. -/
def leftStandardizationZeroEquiv : LeftStandardization Q Λ b hb hα M ≃ₗ[k] M :=
  BalancedTensor.scalarEquiv (blockLeftStandardZeroEquiv Q Λ b hb hα) fun a => by
    induction a using MulOpposite.rec' with | _ x =>
    obtain ⟨c, rfl⟩ := blockAlgebraZero_scalar Q Λ b hb0 x
    refine ⟨c, fun l => op_op_algebraMap_smul_blockLeftStandard Q Λ b hb hα c l, fun m => ?_⟩
    rw [show (op (algebraMap k (BlockAlgebra k Q Λ b) c) : (BlockAlgebra k Q Λ b)ᵐᵒᵖ) =
      algebraMap k _ c from rfl, algebraMap_smul]

theorem leftStandardizationZeroEquiv_tmul (l : BlockLeftStandard Q Λ b hb hα) (m : M) :
    leftStandardizationZeroEquiv Q Λ b hb0 hb hα M (BalancedTensor.tmul l m) =
      blockLeftStandardZeroEquiv Q Λ b hb hα l • m := rfl

/-- `T^∅(0)` acts on the standardization with no red strands through the augmentation. -/
theorem leftStandardizationZeroEquiv_smul (t : TensorProductAlgebra k Q Λ 0)
    (y : LeftStandardization Q Λ b hb hα M) :
    leftStandardizationZeroEquiv Q Λ b hb0 hb hα M (t • y) =
      tensorProductAlgebraZeroEquiv Q Λ t • leftStandardizationZeroEquiv Q Λ b hb0 hb hα M y := by
  have ht : t = algebraMap k _ (tensorProductAlgebraZeroEquiv Q Λ t) := by
    apply (tensorProductAlgebraZeroEquiv Q Λ).injective
    rw [AlgEquiv.commutes]
    rfl
  rw [ht, algebraMap_smul, map_smul, ← ht]

/-- The identification with no red strands is natural. -/
theorem leftStandardizationZeroEquiv_mapRight (g : M →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M)
    (y : LeftStandardization Q Λ b hb hα M) :
    leftStandardizationZeroEquiv Q Λ b hb0 hb hα M
        (BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ 0)
          (M := BlockLeftStandard Q Λ b hb hα) g y) =
      g (leftStandardizationZeroEquiv Q Λ b hb0 hb hα M y) := by
  have h := LinearMap.congr_fun (BalancedTensor.ext (f :=
      (leftStandardizationZeroEquiv Q Λ b hb0 hb hα M).toLinearMap.comp
        ((BalancedTensor.mapRight (k := k) (B := TensorProductAlgebra k Q Λ 0)
          (M := BlockLeftStandard Q Λ b hb hα) g).restrictScalars k))
      (g := (g.restrictScalars k).comp (leftStandardizationZeroEquiv Q Λ b hb0 hb hα M).toLinearMap)
      fun l m => (g.map_smul_of_tower _ m).symm) y
  exact h

end Standardization

end Categorification.Stendhal
