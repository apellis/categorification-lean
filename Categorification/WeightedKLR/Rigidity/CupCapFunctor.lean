/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapDiagrams
import Categorification.Algebra.DerivedTensor

/-!
# The coevaluation functor `𝕂^{λ⁺}_λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3,
Definition 7.18 (first part).

The bimodule `K^{λ⁺}_λ` of `CupCapDiagrams` (the quotient of `K̃^{λ⁺}_λ` by violated diagrams)
is a module over `T̃^λ ⊗ (T̃^{λ⁺})ᵐᵒᵖ`. Every violated diagram acts on it by zero, so it is a
`T^λ`–`T^{λ⁺}` bimodule (`capLeftHom`, `capRightHom`). The coevaluation functor is the derived
tensor product with it,
`𝕂^{λ⁺}_λ = - ⊗ᴸ_{T^λ} K^{λ⁺}_λ : D(T^λ) ⥤ D(T^{λ⁺})`
on derived categories of right modules (`coevaluationFunctor`).

## Conventions

Diagrams are multiplied with the first factor on top, so `T^λ` (the top of the cap diagrams)
acts on the left and `T^{λ⁺}` (the bottom, where the legs of the cap end) on the right. The
functor goes from right `T^λ`-modules to right `T^{λ⁺}`-modules, which is Webster's direction
`𝒱^λ → 𝒱^{λ⁺}`; Webster writes the tensor product over the algebra of the other end because he
reads diagrams in the opposite order. As for the braiding functors (Definition 6.6), the functor
is defined on the unbounded derived category of ungraded dg modules; the grading shifts are not
tracked. The quantum trace `𝕋^{λ⁺}_λ = RHom(K^{λ⁺}_λ, -)` of the same definition is not
formalized here.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR MulOpposite CategoryTheory DG DG.DegreeZero
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w

section Actions

variable {I : Type u} [DecidableEq I] (k : Type u) [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (j : ℕ) (hj : j ≤ ℓ) (ν ν₀ : Multiset I)

/-- `a ↦ a ⊗ 1`: the top factor of `T̃^λ ⊗ (T̃^{λ⁺})ᵐᵒᵖ`. -/
def envLeft : StendhalAlgebra k Q Λ ν →+* Env k Q Λ Λc j hj ν ν₀ :=
  (Algebra.TensorProduct.includeLeftRingHom :
    StendhalAlgebra k Q Λ ν →+*
      StendhalAlgebra k Q Λ ν ⊗[k] (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ)

/-- `bᵒᵖ ↦ 1 ⊗ bᵒᵖ`: the bottom factor of `T̃^λ ⊗ (T̃^{λ⁺})ᵐᵒᵖ`. -/
def envRight :
    (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ →+* Env k Q Λ Λc j hj ν ν₀ :=
  (Algebra.TensorProduct.includeRight :
    (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ →ₐ[k]
      StendhalAlgebra k Q Λ ν ⊗[k]
        (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ).toRingHom

theorem envLeft_mul_envRight (a : StendhalAlgebra k Q Λ ν)
    (b : (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ) :
    envLeft k Q Λ Λc j hj ν ν₀ a * envRight k Q Λ Λc j hj ν ν₀ b =
      envRight k Q Λ Λc j hj ν ν₀ b * envLeft k Q Λ Λc j hj ν ν₀ a := by
  have h : ((a ⊗ₜ[k] 1 : StendhalAlgebra k Q Λ ν ⊗[k]
      (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ) * (1 ⊗ₜ[k] b)) =
      (1 ⊗ₜ[k] b) * (a ⊗ₜ[k] 1) := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  exact h

variable (L : Type u) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- The action of `T̃^λ` on `K^{λ⁺}_λ` from the top. -/
def capTopHom : StendhalAlgebra k Q Λ ν →+* AddMonoid.End (Cap k Q Λ Λc j hj ν ν₀ L) :=
  (Module.toAddMonoidEnd (Env k Q Λ Λc j hj ν ν₀) (Cap k Q Λ Λc j hj ν ν₀ L)).comp
    (envLeft k Q Λ Λc j hj ν ν₀)

/-- The action of `(T̃^{λ⁺})ᵐᵒᵖ` on `K^{λ⁺}_λ` from the bottom. -/
def capBotHom :
    (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ →+*
      AddMonoid.End (Cap k Q Λ Λc j hj ν ν₀ L) :=
  (Module.toAddMonoidEnd (Env k Q Λ Λc j hj ν ν₀) (Cap k Q Λ Λc j hj ν ν₀ L)).comp
    (envRight k Q Λ Λc j hj ν ν₀)

/-- Violated diagrams of `T̃^λ` act by zero on `K^{λ⁺}_λ`. -/
theorem capTopHom_violated {a : StendhalAlgebra k Q Λ ν}
    (ha : a ∈ StendhalAlgebra.violatedIdeal k Q Λ ν) :
    capTopHom k Q Λ Λc j hj ν ν₀ L a = 0 := by
  ext z
  induction z using Submodule.Quotient.induction_on with
  | H y =>
    change envLeft k Q Λ Λc j hj ν ν₀ a •
      (Submodule.Quotient.mk y : Cap k Q Λ Λc j hj ν ν₀ L) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span (Or.inl ⟨a, ha, y, rfl⟩)

/-- Violated diagrams of `T̃^{λ⁺}` act by zero on `K^{λ⁺}_λ`. -/
theorem capBotHom_violated {b : StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)}
    (hb : b ∈ StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc j hj) (ν + ν₀)) :
    capBotHom k Q Λ Λc j hj ν ν₀ L (op b) = 0 := by
  ext z
  induction z using Submodule.Quotient.induction_on with
  | H y =>
    change envRight k Q Λ Λc j hj ν ν₀ (op b) •
      (Submodule.Quotient.mk y : Cap k Q Λ Λc j hj ν ν₀ L) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span (Or.inr ⟨b, hb, y, rfl⟩)

/-- **`K^{λ⁺}_λ` is a left `T^λ`-module**: the action of `T̃^λ` from the top factors through
the quotient by violated diagrams. -/
def capLeftHom :
    TensorProductAlgebra k Q Λ ν →+* AddMonoid.End (Cap k Q Λ Λc j hj ν ν₀ L) :=
  (StendhalAlgebra.violatedIdeal k Q Λ ν).ringCon.lift (capTopHom k Q Λ Λc j hj ν ν₀ L)
    fun a b h => by
      rw [RingCon.ker_apply, ← sub_eq_zero, ← map_sub]
      exact capTopHom_violated k Q Λ Λc j hj ν ν₀ L
        (((StendhalAlgebra.violatedIdeal k Q Λ ν).rel_iff a b).1 h)

/-- The action of `T̃^{λ⁺}` from the bottom, as a ring map into the opposite ring. -/
def capBotHomUnop :
    StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀) →+*
      (AddMonoid.End (Cap k Q Λ Λc j hj ν ν₀ L))ᵐᵒᵖ :=
  RingHom.unop ((RingEquiv.opOp _).toRingHom.comp (capBotHom k Q Λ Λc j hj ν ν₀ L))

/-- **`K^{λ⁺}_λ` is a right `T^{λ⁺}`-module**: the action of `T̃^{λ⁺}` from the bottom factors
through the quotient by violated diagrams. -/
def capRightHom :
    (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ →+*
      AddMonoid.End (Cap k Q Λ Λc j hj ν ν₀ L) :=
  (RingEquiv.opOp _).symm.toRingHom.comp (RingHom.op
    ((StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc j hj) (ν + ν₀)).ringCon.lift
      (capBotHomUnop k Q Λ Λc j hj ν ν₀ L) fun a b h => by
        rw [RingCon.ker_apply, ← sub_eq_zero, ← map_sub]
        have := capBotHom_violated k Q Λ Λc j hj ν ν₀ L
          (((StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc j hj) (ν + ν₀)).rel_iff a b).1 h)
        change MulOpposite.op (capBotHom k Q Λ Λc j hj ν ν₀ L (op (a - b))) = 0
        rw [this, MulOpposite.op_zero]))

/-- **Webster's bimodule `K^{λ⁺}_λ` as a `T^λ`–`T^{λ⁺}` bimodule** (arXiv:1309.3796v3, §7.3,
after Lemma 7.17): `Cap` with the actions of the tensor product algebras. -/
def CapBimodule : Type u := Cap k Q Λ Λc j hj ν ν₀ L

noncomputable instance : AddCommGroup (CapBimodule k Q Λ Λc j hj ν ν₀ L) :=
  inferInstanceAs (AddCommGroup (Cap k Q Λ Λc j hj ν ν₀ L))

noncomputable instance : Module (TensorProductAlgebra k Q Λ ν) (CapBimodule k Q Λ Λc j hj ν ν₀ L) :=
  Module.compHom (Cap k Q Λ Λc j hj ν ν₀ L) (capLeftHom k Q Λ Λc j hj ν ν₀ L)

noncomputable instance :
    Module (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ
      (CapBimodule k Q Λ Λc j hj ν ν₀ L) :=
  Module.compHom (Cap k Q Λ Λc j hj ν ν₀ L) (capRightHom k Q Λ Λc j hj ν ν₀ L)

theorem capLeftHom_commute (a : TensorProductAlgebra k Q Λ ν)
    (b : (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ) :
    Commute (capLeftHom k Q Λ Λc j hj ν ν₀ L a) (capRightHom k Q Λ Λc j hj ν ν₀ L b) := by
  induction b using MulOpposite.rec' with
  | h b =>
  induction a using Quotient.inductionOn' with
  | h a =>
  induction b using Quotient.inductionOn' with
  | h b =>
  ext z
  change envLeft k Q Λ Λc j hj ν ν₀ a • envRight k Q Λ Λc j hj ν ν₀ (op b) •
      (z : Cap k Q Λ Λc j hj ν ν₀ L) =
    envRight k Q Λ Λc j hj ν ν₀ (op b) • envLeft k Q Λ Λc j hj ν ν₀ a • z
  rw [← mul_smul, ← mul_smul, envLeft_mul_envRight]

noncomputable instance :
    SMulCommClass (TensorProductAlgebra k Q Λ ν)
      (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ
      (CapBimodule k Q Λ Λc j hj ν ν₀ L) where
  smul_comm a b z := congrArg (fun f : AddMonoid.End (Cap k Q Λ Λc j hj ν ν₀ L) => f z)
    (capLeftHom_commute k Q Λ Λc j hj ν ν₀ L a b).eq

end Actions

section Functor

variable {I : Type u} [DecidableEq I] (k : Type u) [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (j : ℕ) (hj : j ≤ ℓ) (ν ν₀ : Multiset I)
  (L : Type u) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  [HasDerivedCategory.{w} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]
  [HasDerivedCategory.{w} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ]

/-- **The coevaluation functor** `𝕂^{λ⁺}_λ = - ⊗ᴸ_{T^λ} K^{λ⁺}_λ` (arXiv:1309.3796v3,
Definition 7.18), from the derived category of right `T^λ`-modules to that of right
`T^{λ⁺}`-modules, with the coefficient module `L` at the maximum of the cap (Webster: `L_μ`). -/
def coevaluationFunctor :
    DG.DerivedCategory.{w} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ ⥤
      DG.DerivedCategory.{w} (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ :=
  derivedRightTensor.{w} (TensorProductAlgebra k Q Λ ν)
    (TensorProductAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)) (CapBimodule k Q Λ Λc j hj ν ν₀ L)

end Functor

end Categorification.Stendhal.CupCap
