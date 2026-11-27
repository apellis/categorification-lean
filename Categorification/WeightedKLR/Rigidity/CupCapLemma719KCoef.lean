/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KGen
import Categorification.WeightedKLR.Rigidity.CupCapCoevaluation

/-!
# The coefficient module of the cap, from a left `T^{μ μ*}`-module

Webster, arXiv:1309.3796v3, Lemma 7.19 (K). In `(K)`, `K S(Z) ≅ S_+(Z ⊠ L)`, the module `L`
(Webster's `L_μ`) appears twice: as the module of the middle block of `S_+`, a left
`T^{μ μ*}`-module, and as the coefficients at the maximum of the cap in `K^{λ⁺}_λ`, a right
`T̃^{μ μ*}`-module. Here the left module `L'` is primary. The coefficients of the cap are its
horizontal reflection (`ReflectedCoef`), a right `T^{μ μ*}`-module, viewed as a right
`T̃^{μ μ*}`-module through the quotient map (`CapCoef = ViaQuotient (ReflectedCoef L')`).

The support condition on the cap coefficients (loadings at the maximum that do not start with
`μ` and end with `μ*` act by zero) is the route hypothesis `hL` of the model of `K̃^{λ⁺}_λ` and
of `projective_midCapBimodule`; it is not among Webster's hypotheses. `capCoef_support` shows it
is the same condition stated on `L'`.

## Main definitions

* `Stendhal.CupCap.ReflectedCoef`: a left `T^{μ μ*}`-module as a right module by reflection.
* `Stendhal.CupCap.CapCoef`: the coefficient module of the cap.

## Main results

* `Stendhal.CupCap.op_smul_capCoef`: the action of a diagram on the coefficients.
* `Stendhal.CupCap.capCoef_support`: the support hypothesis transfers from `L'`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {Λc : Fin 2 → I →₀ ℕ} {ν₀ : Multiset I}

variable (Q Λc ν₀) in
/-- **A left `T^{μ μ*}`-module as a right module**, through the horizontal reflection. -/
@[nolint unusedArguments]
def ReflectedCoef (_Q : I → I → MvPolynomial (Fin 2) k) (_Λc : Fin 2 → I →₀ ℕ)
    (_ν₀ : Multiset I) (L' : Type) : Type := L'

variable {L' : Type} [AddCommGroup L'] [Module k L'] [Module (TensorProductAlgebra k Q Λc ν₀) L']
  [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

instance : AddCommGroup (ReflectedCoef Q Λc ν₀ L') := inferInstanceAs (AddCommGroup L')
instance : Module k (ReflectedCoef Q Λc ν₀ L') := inferInstanceAs (Module k L')
instance : Module (TensorProductAlgebra k Q Λc ν₀)ᵐᵒᵖ (ReflectedCoef Q Λc ν₀ L') :=
  Module.compHom L' ((tensorFlipRingEquiv (Q := Q) (Λ := Λc) ν₀).symm :
    (TensorProductAlgebra k Q Λc ν₀)ᵐᵒᵖ →+* TensorProductAlgebra k Q Λc ν₀)

variable (Q Λc ν₀) in
/-- **The coefficient module of the cap**: the reflection of `L'` as a right
`T̃^{μ μ*}`-module. -/
abbrev CapCoef (L' : Type) [AddCommGroup L'] [Module k L']
    [Module (TensorProductAlgebra k Q Λc ν₀) L'] : Type :=
  ViaQuotient k Q Λc ν₀ (ReflectedCoef Q Λc ν₀ L')

instance : Module k (CapCoef Q Λc ν₀ L') := inferInstanceAs (Module k L')

/-- An element of `L'` as a coefficient of the cap. -/
def toCapCoef (v : L') : CapCoef Q Λc ν₀ L' := v

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
/-- **The action of a diagram on the coefficients**: its mirror image acting on `L'`. -/
theorem op_smul_capCoef (a : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) (v : L') :
    op (topMap k Q Λc ν₀ a) • toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) v =
      toCapCoef (TensorProductAlgebra.mk Q Λc ν₀ (topMap k Q Λc ν₀ (hflip a)) • v) := by
  change ((tensorFlipRingEquiv (Q := Q) (Λ := Λc) ν₀).symm
    (op (TensorProductAlgebra.mk Q Λc ν₀ (topMap k Q Λc ν₀ a))) • v : L') = _
  rw [tensorFlipRingEquiv_symm_op_mk]
  rfl

/-- The reflection is `k`-linear. -/
theorem tensorFlipRingEquiv_symm_smul (c : k) (x : (TensorProductAlgebra k Q Λc ν₀)ᵐᵒᵖ) :
    (tensorFlipRingEquiv (Q := Q) (Λ := Λc) ν₀).symm (c • x) =
      c • (tensorFlipRingEquiv (Q := Q) (Λ := Λc) ν₀).symm x :=
  (tensorFlip (Q := Q) (Λ := Λc) (ν := ν₀)).map_smul c x.unop

instance : IsScalarTower k (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ (CapCoef Q Λc ν₀ L') where
  smul_assoc c s v := by
    change ((tensorFlipRingEquiv (Q := Q) (Λ := Λc) ν₀).symm
        (op (TensorProductAlgebra.mk Q Λc ν₀ (c • s).unop)) • (show L' from v) : L') =
      c • ((tensorFlipRingEquiv (Q := Q) (Λ := Λc) ν₀).symm
        (op (TensorProductAlgebra.mk Q Λc ν₀ s.unop)) • (show L' from v) : L')
    rw [MulOpposite.unop_smul, map_smul, MulOpposite.op_smul, tensorFlipRingEquiv_symm_smul,
      smul_assoc]

omit [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L'] in
/-- **The support hypothesis transfers from `L'`**: if the loadings at the maximum that are not
of the form `μ ⋯ μ*` act by zero on `L'`, they act by zero on the coefficients of the cap. This
is the route hypothesis `hL` of `projective_midCapBimodule`, stated on `L'`. -/
theorem capCoef_support
    (hL' : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L'), ¬ IsCapGood ν₀ w →
      TensorProductAlgebra.mk Q Λc ν₀ (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (w : Seq (stendhalWeight 2 ν₀)) (v : CapCoef Q Λc ν₀ L') (hw : ¬ IsCapGood ν₀ w) :
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0 := by
  have h := op_smul_capCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) (KLRAlgebra.e w) (show L' from v)
  rw [hflip_e] at h
  exact h.trans (congrArg toCapCoef (hL' w v hw))

end Categorification.Stendhal.CupCap
