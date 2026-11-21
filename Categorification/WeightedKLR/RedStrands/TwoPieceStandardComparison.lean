/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PrefixProjectionDescent
import Categorification.WeightedKLR.RedStrands.LastRedBlackDescent
import Categorification.WeightedKLR.RedStrands.ParabolicStandardUpper
import Categorification.WeightedKLR.RedStrands.ConcatLoadingOrder
import Categorification.WeightedKLR.RedStrands.ParabolicStandardTensorProj
import Categorification.WeightedKLR.RedStrands.LeftStandardModule
import Categorification.WeightedKLR.RedStrands.LastRedTruncation

/-!
# Standardization of a two-piece standard module

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.21. For a red-ordered loading `t` of the first `ℓ` red strands and a black
sequence `u`, the standardization `S(S_t ⊠ R e(u))` is the standard module `S_{t λ_{ℓ+1} u}` of
Definition 5.1, where `t λ_{ℓ+1} u` is the two-piece loading.

This file builds the action of the ambient diagrams on the standard module `S_{t λ_{ℓ+1} u}`
through the two factor algebras.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Kill

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}

/-- Idempotents strictly above `s` kill the standard module `S_s`. -/
theorem leftStandard_seqIdem_mul_smul {s c : Seq (stendhalWeight ℓ ν)} {hs : IsRedOrdered s}
    (hc : IsRedOrdered c) (hlt : StendhalLT s c) (a : TensorProductAlgebra k Q Λ ν)
    (v : leftStandard Q Λ s hs) : (seqIdem Q Λ c hc * a) • v = 0 := by
  obtain ⟨b, rfl⟩ := leftStandard_exists_smul_unit s hs v
  rw [← mul_smul, leftStandardUnit, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact Submodule.subset_span ⟨c, hc, a * b, hlt, by
    change seqIdem Q Λ c hc * a * b * seqIdem Q Λ s hs = _
    rw [mul_assoc (seqIdem Q Λ c hc)]⟩

variable (Q Λ) in
/-- The diagrams of all red orders acting on a standard module. -/
def leftStandardAllOrders (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) :
    StendhalAlgebraAllOrders k Q Λ ν →ₐ[k] Module.End k (leftStandard Q Λ s hs) :=
  (Algebra.lsmul k k (leftStandard Q Λ s hs)).comp
    ((TensorProductAlgebra.mk Q Λ ν).comp (orderProjection Q Λ ν))

/-- An idempotent strictly above `s`, of any red order, kills `S_s`. -/
theorem leftStandardAllOrders_e {s c : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s)
    (hlt : StendhalLT s c) :
    leftStandardAllOrders Q Λ s hs (StendhalAlgebraAllOrders.e c) = 0 := by
  by_cases hc : IsRedOrdered c
  · have he : orderProjection Q Λ ν (StendhalAlgebraAllOrders.e c) = StendhalAlgebra.e c hc :=
      Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem c).trans (ite_eq_left hc))
    refine LinearMap.ext fun v => ?_
    change TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν _) • v = 0
    rw [he, ← mul_one (TensorProductAlgebra.mk Q Λ ν _)]
    exact leftStandard_seqIdem_mul_smul hc hlt 1 v
  · have he : orderProjection Q Λ ν (StendhalAlgebraAllOrders.e c) = 0 :=
      Subtype.ext ((StendhalAlgebraAllOrders.e_mul_redOrderedIdem c).trans (ite_eq_right hc))
    simp [leftStandardAllOrders, he]

end Kill

end Categorification.Stendhal
