/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalCoefficientCovers
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalTorZeroStandard

/-!
# The `Tor₀` of the coefficient against the diagonal standard is a corner

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), the `Tor₀` of the diagonal pair. For `W = SMove.leftStd N` and a
loading `s` with every black strand left of the last red strand,
`W^r ⊗_T S_s ≅ W^r e(s)` (`SMove.leftStdReflectTensorEquivFixed`, a balanced tensor product
over `k`). The comparison of the two balanced tensor products (`ordinaryBalancedTensorAddEquiv`)
is `k`-linear (`ordinaryBalancedTensorLinearEquiv`), and the reflection at the trivial braid
fixes loading idempotents, so

  `dim_k (W^r ⊗_T S_s) = dim_k e(s) W`

(`SMove.finrank_tensorProductOver_reflectOne_leftStd_leftStandard`). No route hypotheses.

## Main results

* `ordinaryBalancedTensorLinearEquiv`: the comparison `M ⊗_B N ≅ M ⊗_{k, B} N` is `k`-linear.
* `SMove.fixSubReflectOneLeftStdEquiv`: `W^r e(s) ≅ e(s) W`.
* `SMove.finrank_tensorProductOver_reflectOne_leftStd_leftStandard`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification

open MulOpposite DG

section BalancedLinear

variable {k B M N : Type*} [CommRing k] [Ring B] [Algebra k B]
  [AddCommGroup M] [Module k M] [Module Bᵐᵒᵖ M] [SMulCommClass k Bᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module B N] [IsScalarTower k B N]

/-- **The two balanced tensor products agree `k`-linearly**: the additive comparison
`ordinaryBalancedTensorAddEquiv` between `M ⊗_B N` (with `k` acting on `M`) and the balanced
tensor product over `k` is `k`-linear. -/
def ordinaryBalancedTensorLinearEquiv
    (hM : ∀ (c : k) (m : M), op (algebraMap k B c) • m = c • m) :
    TensorProductOver B M N ≃ₗ[k] BalancedTensor k k B M N :=
  { ordinaryBalancedTensorAddEquiv (A := k) (k := k) hM with
    map_smul' := fun c x => by
      induction x using TensorProductOver.induction_on with
      | zero =>
        change (ordinaryBalancedTensorAddEquiv (A := k) (k := k) hM) (c • 0) =
          c • (ordinaryBalancedTensorAddEquiv (A := k) (k := k) hM) 0
        rw [smul_zero, map_zero, smul_zero]
      | tmul m n =>
        change BalancedTensor.tmul (c • m) n = c • BalancedTensor.tmul m n
        exact BalancedTensor.smul_tmul c m n
      | add x y hx hy =>
        simp only [smul_add, AddEquiv.toFun_eq_coe, map_add, RingHom.id_apply] at hx hy ⊢
        rw [hx, hy] }

@[simp]
theorem ordinaryBalancedTensorLinearEquiv_tmul
    (hM : ∀ (c : k) (m : M), op (algebraMap k B c) • m = c • m) (m : M) (n : N) :
    ordinaryBalancedTensorLinearEquiv hM (TensorProductOver.tmul B m n) =
      BalancedTensor.tmul m n := rfl

end BalancedLinear

namespace Stendhal.SMove

open CategoryTheory KLR Equiv BraidedStendhalAlgebra

attribute [local instance] ModuleCat.moduleOfAlgebraModule
  ModuleCat.isScalarTower_of_algebra_moduleCat

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (1 + (1 + 1)) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "Λ₂₃" => (Λ ∘ Fin.natAdd 1 : Fin (1 + 1) → I →₀ ℕ)

attribute [local instance] smulCommClass_leftStdReflect

/-- On the reflection of `SMove.leftStd N` at the trivial braid, the right action of a loading
idempotent is its left action on `SMove.leftStd N` (the flip fixes loading idempotents). -/
theorem op_seqIdem_smul_leftStdReflect (N : ModuleCat.{0} (TensorProductAlgebra k Q Λ₂₃ ν))
    (s : Seq (stendhalWeight (1 + (1 + 1)) ν)) (hs : IsRedOrdered s)
    (w : leftStdReflect Q hQ Λ hρ N) :
    op (seqIdem Q Λ s hs) • w = (seqIdem Q Λ s hs •
      (show (leftStd Q hQ Λ ν).obj N from w) : (leftStd Q hQ Λ ν).obj N) := by
  change (cornerFlipTensorEquiv (Λ := Λ) hρ hQ 1 (op (seqIdem Q Λ s hs))) •
    (show (leftStd Q hQ Λ ν).obj N from w) = _
  rw [cornerFlipTensorEquiv_one_apply, unop_op, seqIdem]
  erw [tensorFlip_mk_e]
  rfl

/-- **The corner of the reflection is the corner of the module**: `W^r e(s) ≅ e(s) W` for
`W = SMove.leftStd N`, as `k`-spaces. -/
def fixSubReflectOneLeftStdEquiv (N : ModuleCat.{0} (TensorProductAlgebra k Q Λ₂₃ ν))
    (s : Seq (stendhalWeight (1 + (1 + 1)) ν)) (hs : IsRedOrdered s) :
    fixSub k (leftStdReflect Q hQ Λ hρ N) (op (seqIdem Q Λ s hs)) ≃ₗ[k]
      fixSub k ((leftStd Q hQ Λ ν).obj N) (seqIdem Q Λ s hs) where
  toFun x := ⟨x.1, (op_seqIdem_smul_leftStdReflect Q hQ Λ hρ N s hs x.1).symm.trans x.2⟩
  invFun x := ⟨x.1, (op_seqIdem_smul_leftStdReflect Q hQ Λ hρ N s hs x.1).trans x.2⟩
  map_add' _ _ := rfl
  map_smul' c x := Subtype.ext (by
    change (algebraMap k Tᵐᵒᵖ c) • (x.1 : leftStdReflect Q hQ Λ hρ N) =
      (algebraMap k T c • (show (leftStd Q hQ Λ ν).obj N from x.1) : (leftStd Q hQ Λ ν).obj N)
    change (cornerFlipTensorEquiv (Λ := Λ) hρ hQ 1 (op (algebraMap k T c))) •
      (show (leftStd Q hQ Λ ν).obj N from x.1) = _
    rw [cornerFlipTensorEquiv_one_apply, unop_op]
    erw [tensorFlip_algebraMap']
    rfl)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`Tor₀` of the coefficient against the diagonal standard** (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.22, `Tor₀` of the diagonal pair): for every input `N` and every
loading `s` with all black strands left of the last red strand,
`dim_k (W^r ⊗_T S_s) = dim_k e(s) W`, `W = SMove.leftStd N`. No route hypotheses. -/
theorem finrank_tensorProductOver_reflectOne_leftStd_leftStandard
    (N : ModuleCat.{0} (TensorProductAlgebra k Q Λ₂₃ ν))
    (s : Seq (stendhalWeight (1 + (1 + 1)) ν)) (hs : IsRedOrdered s)
    (hlast : ∀ i, blackCount s (Fin.last 2) i = ν.count i) :
    Module.finrank k (TensorProductOver T (leftStdReflect Q hQ Λ hρ N)
        (leftStandard Q Λ s hs)) =
      Module.finrank k (fixSub k ((leftStd Q hQ Λ ν).obj N) (seqIdem Q Λ s hs)) :=
  ((ordinaryBalancedTensorLinearEquiv (op_algebraMap_smul_eq Q Λ _)).trans
    ((leftStdReflectTensorEquivFixed Q hQ Λ hρ N s hs hlast).trans
      (fixSubReflectOneLeftStdEquiv Q hQ Λ hρ N s hs))).finrank_eq

end Stendhal.SMove

end Categorification
