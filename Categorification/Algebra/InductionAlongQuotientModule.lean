/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlong

/-!
# Induction of a quotient module

Induction along a nonunital ring map `φ : A → B` is right exact. For a submodule `N'` of an
`A`-module `N`, `Ind_φ (N / N')` is `Ind_φ N` modulo the span of the `z ⊗ n` with `n ∈ N'`
(`InductionAlong.indModQuotEquiv`).

## Main definitions

* `InductionAlong.indImageSub`: the span of the `z ⊗ n` with `n ∈ N'`.
* `InductionAlong.indModQuotEquiv`: `Ind_φ N / indImageSub ≅ Ind_φ (N / N')`.
-/

namespace Categorification

open MulOpposite

noncomputable section

namespace InductionAlong

universe u w

variable {A B : Type u} [Ring A] [Ring B] (φ : A →ₙ+* B)
  {N : Type w} [AddCommGroup N] [Module A N] (N' : Submodule A N)

/-- The span of the `z ⊗ n` with `n ∈ N'`. -/
def indImageSub : Submodule B (Ind N φ) :=
  Submodule.span B {x | ∃ z : Corner φ, ∃ n ∈ N', x = Ind.tmul z n}

variable {φ N'}

theorem tmul_mem_indImageSub (z : Corner φ) {n : N} (hn : n ∈ N') :
    Ind.tmul z n ∈ indImageSub φ N' :=
  Submodule.subset_span ⟨z, n, hn, rfl⟩

theorem indImageSub_le_ker :
    indImageSub φ N' ≤ LinearMap.ker (Ind.map (φ := φ) N'.mkQ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨z, n, hn, rfl⟩
  change Ind.map N'.mkQ (Ind.tmul z n) = 0
  rw [Ind.map_tmul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N').2 hn, Ind.tmul_zero]

variable (φ N')

/-- The map `Ind_φ N / indImageSub → Ind_φ (N / N')`. -/
def indModQuotHom : (Ind N φ ⧸ indImageSub φ N') →ₗ[B] Ind (N ⧸ N') φ :=
  (indImageSub φ N').liftQ (Ind.map N'.mkQ) indImageSub_le_ker

local notation "QI" => Ind N φ ⧸ indImageSub φ N'

/-- The function `(z, n mod N') ↦ z ⊗ n mod indImageSub`. -/
def indModQuotFun (z : Corner φ) (q : N ⧸ N') : QI :=
  Quotient.liftOn' q (fun n => Submodule.Quotient.mk (Ind.tmul z n)) fun n n' h => by
    refine (Submodule.Quotient.eq _).2 ?_
    have h' : n - n' ∈ N' := (Submodule.quotientRel_def _).1 h
    have := tmul_mem_indImageSub (φ := φ) z h'
    have hneg : Ind.tmul z (-n') = -Ind.tmul z n' := by
      rw [eq_neg_iff_add_eq_zero, ← Ind.tmul_add, neg_add_cancel, Ind.tmul_zero]
    rwa [sub_eq_add_neg, Ind.tmul_add, hneg, ← sub_eq_add_neg] at this

theorem indModQuotFun_mk (z : Corner φ) (n : N) :
    indModQuotFun φ N' z (Submodule.Quotient.mk n) = Submodule.Quotient.mk (Ind.tmul z n) := rfl

/-- **The inverse map `Ind_φ (N / N') → Ind_φ N / indImageSub`**, `z ⊗ [n] ↦ [z ⊗ n]`. -/
def indModQuotInv : Ind (N ⧸ N') φ →ₗ[B] QI :=
  Ind.lift (indModQuotFun φ N')
    (fun z z' q => by
      induction q using Submodule.Quotient.induction_on with
      | H n => rw [indModQuotFun_mk, indModQuotFun_mk, indModQuotFun_mk, Ind.add_tmul,
          Submodule.Quotient.mk_add])
    (fun z q q' => by
      induction q using Submodule.Quotient.induction_on with
      | H n =>
        induction q' using Submodule.Quotient.induction_on with
        | H n' => rw [← Submodule.Quotient.mk_add, indModQuotFun_mk, indModQuotFun_mk,
            indModQuotFun_mk, Ind.tmul_add, Submodule.Quotient.mk_add])
    (fun z a q => by
      induction q using Submodule.Quotient.induction_on with
      | H n => rw [← Submodule.Quotient.mk_smul, indModQuotFun_mk, indModQuotFun_mk,
          Ind.op_smul_tmul])
    (fun b z q => by
      induction q using Submodule.Quotient.induction_on with
      | H n => rw [indModQuotFun_mk, indModQuotFun_mk, ← Submodule.Quotient.mk_smul,
          Ind.smul_tmul])

theorem indModQuotInv_tmul (z : Corner φ) (n : N) :
    indModQuotInv φ N' (Ind.tmul z (Submodule.Quotient.mk n)) =
      Submodule.Quotient.mk (Ind.tmul z n) := rfl

/-- **Induction is right exact**: `Ind_φ N / indImageSub ≅ Ind_φ (N / N')`, `[z ⊗ n] ↦ z ⊗ [n]`. -/
def indModQuotEquiv : QI ≃ₗ[B] Ind (N ⧸ N') φ :=
  LinearEquiv.ofLinearMap (indModQuotHom φ N') (indModQuotInv φ N')
    (Ind.ext fun z q => by
      induction q using Submodule.Quotient.induction_on with
      | H n => rfl)
    (Submodule.linearMap_qext _ (Ind.ext fun z n => rfl))

theorem indModQuotEquiv_mk (x : Ind N φ) :
    indModQuotEquiv φ N' (Submodule.Quotient.mk x) = Ind.map N'.mkQ x := rfl

end InductionAlong

end

end Categorification
