/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationSingletons
import Categorification.WeightedKLR.RedStrands.PartialStandardizationCutParabolic
import Categorification.WeightedKLR.RedStrands.TwoPieceBlockAlgebra
import Categorification.WeightedKLR.RedStrands.Vacuum
import Categorification.KLR.CyclotomicFlip

/-!
# The singleton blocks and the block algebra of Proposition 5.3

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1. For
blocks `b_0, b_1, …, b_n` the block algebra of Proposition 5.3 is
`R(b_0) ⊗ R^{λ_1}(b_1) ⊗ ⋯ ⊗ R^{λ_n}(b_n)` (`BlockAlgebra`), and the standardization of
Definition 5.4 is taken of right modules over it. The algebra of the singleton blocks
`T^{λ_1}(b_1) ⊗ ⋯ ⊗ T^{λ_n}(b_n)` (`singAlg`) maps to the opposite of the block algebra
(`singBlockHom`): each factor `T^{λ_r}(b_r)` is identified with the cyclotomic quotient
`R^{λ_r}(b_r)` by Theorem 4.20 for one red strand and then mapped by the anti-involution
`flip`, and the algebra `T^∅(0)` of no strands is the ground ring. So a right module over the
block algebra is a left module over the algebra of the singleton blocks.

## Main definitions

* `Stendhal.singLastBlockHom`: the last singleton block in the opposite block algebra.
* `Stendhal.singBlockHom`: `T^{λ_1}(b_1) ⊗ ⋯ ⊗ T^{λ_n}(b_n) → (R(b_0) ⊗ ⨂_r R^{λ_r}(b_r))ᵐᵒᵖ`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA StendhalAlgebra MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)

omit [DecidableEq I] in
/-- The labels of the last singleton block. -/
theorem natAdd_last_label {n : ℕ} (Λ : Fin (n + 1) → I →₀ ℕ) :
    Λ ∘ Fin.natAdd n = fun _ : Fin 1 => Λ (Fin.last n) :=
  (congrArg (Λ ∘ ·) (lastIndex_eq_natAdd (ℓ := n))).symm

/-- **The last singleton block in the opposite block algebra**: `T^{λ_{n+1}}(b_{n+1})` is the
cyclotomic quotient `R^{λ_{n+1}}(b_{n+1})` (Theorem 4.20), mapped to the last factor by `flip`. -/
def singLastBlockHom (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (b : Fin (n + 2) → Multiset I) :
    singLast Q Λ (b ∘ Fin.succ) →ₐ[k] (BlockAlgebra k Q Λ b)ᵐᵒᵖ :=
  (AlgHom.op (lastBlockAlgHom Q Λ b)).comp
    ((CycKLR.flipEquiv _ (rightBlock b (Fin.last n))).toAlgHom.comp
      ((SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => Λ (Fin.last n))
          (rightBlock b (Fin.last n))).symm.toAlgHom.comp
        (tensorProductAlgebraCast Q (natAdd_last_label Λ) (b (Fin.last n).succ)).toAlgHom))

/-- **The singleton blocks in the opposite block algebra.** -/
def singBlockHom : (n : ℕ) → (Λ : Fin n → I →₀ ℕ) → (b : Fin (n + 1) → Multiset I) →
    singAlg Q n Λ (b ∘ Fin.succ) →ₐ[k] (BlockAlgebra k Q Λ b)ᵐᵒᵖ
  | 0, Λ, _ => (Algebra.ofId k _).comp (tensorProductAlgebraZeroEquiv Q Λ).toAlgHom
  | n + 1, Λ, b => Algebra.TensorProduct.lift
      ((AlgHom.op (initBlockAlgHom Q Λ b)).comp (singBlockHom n (Λ ∘ Fin.castSucc) (initBlocks b)))
      (singLastBlockHom Q n Λ b) fun _ _ =>
        (commute_initBlockAlgHom_lastBlockAlgHom Q Λ b _ _).op

theorem singLastBlockHom_apply (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (b : Fin (n + 2) → Multiset I)
    (c : singLast Q Λ (b ∘ Fin.succ)) :
    singLastBlockHom Q n Λ b c = op (lastBlockAlgHom Q Λ b (CycKLR.flip _ _
      ((SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => Λ (Fin.last n))
        (rightBlock b (Fin.last n))).symm
          (tensorProductAlgebraCast Q (natAdd_last_label Λ) (b (Fin.last n).succ) c)))) :=
  rfl

theorem singBlockHom_zero (Λ : Fin 0 → I →₀ ℕ) (b : Fin 1 → Multiset I)
    (t : singAlg Q 0 Λ (b ∘ Fin.succ)) :
    singBlockHom Q 0 Λ b t =
      algebraMap k _
        (tensorProductAlgebraZeroEquiv Q Λ (show TensorProductAlgebra k Q Λ 0 from t)) :=
  rfl

theorem singBlockHom_succ_tmul (n : ℕ) (Λ : Fin (n + 1) → I →₀ ℕ) (b : Fin (n + 2) → Multiset I)
    (s : singAlg Q n (Λ ∘ Fin.castSucc) (initBlocks b ∘ Fin.succ))
    (c : singLast Q Λ (b ∘ Fin.succ)) :
    singBlockHom Q (n + 1) Λ b (s ⊗ₜ c) =
      AlgHom.op (initBlockAlgHom Q Λ b) (singBlockHom Q n (Λ ∘ Fin.castSucc) (initBlocks b) s) *
        singLastBlockHom Q n Λ b c :=
  Algebra.TensorProduct.lift_tmul _ _ _ s c

end Categorification.Stendhal
