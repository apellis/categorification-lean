/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KPsiFlip
import Categorification.WeightedKLR.Rigidity.CupCapModelInverse

/-!
# The inverse on the model of the cap

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof of the inverse `Ψ`: for `y` in the input `Y`
of the cut, the map `f_y` from the model `L ⊗_{T̃^{(μ,μ*)}} e T̃^{λ⁺}` of `K̃^{λ⁺}_λ` (with
`L` the coefficients of the cap made from `L'`) to the right side `S_+(Y ⊠ L')`, sending
`v ⊗ e Z` to `σ(Z) · (1 ⊗ (y ⊠ v))`, with `σ` the horizontal reflection. It is balanced over
`T̃^{(μ,μ*)}` because a diagram at the maximum acts on the unit as it acts on `L'`
(`kSrc_flip_midBot_smul_unit`), and it intertwines the right action of `T̃^{λ⁺}` on the model
with the reflected left action on the right side (`kModelMap_smul`).

## Main definitions

* `Stendhal.CupCap.kModelMap`: the map `f_y` on the model.

## Main results

* `Stendhal.CupCap.kModelMap_tmul`: its value on `v ⊗ e Z`.
* `Stendhal.CupCap.kModelMap_smul`: it intertwines the actions of `T̃^{λ⁺}`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I)
  (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)
  (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "Xs" => KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L'
set_option hygiene false in
local notation "Np" => BlocksOneStepInput Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L'))
set_option hygiene false in
local notation "U" y:max v:max =>
  kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' (show Np from midSpectTmul (k := k) y v)
set_option hygiene false in
local notation "Cm" => Corner (midOp j hj Q Λ Λc (θ + γ) ν₀)
set_option hygiene false in
local notation "Lc" => CapCoef Q Λc ν₀ L'
set_option hygiene false in
local notation "fl" => plusFlip j hj Q Λ Λc (θ + γ) ν₀
set_option hygiene false in
local notation "σm" => midStendhal j hj Q Λ Λc (θ + γ) ν₀

/-- The value of `f_y` on `v ⊗ z`: the reflection of `z` acting on the unit at `y ⊠ v`. -/
def kModelFun (y : Y) (z : Cm) (v : Lc) : Xs := fl z.1.unop • U y (show L' from v)

/-- **`f_y` is balanced over `T̃^{(μ,μ*)}`.** -/
theorem kModelFun_balanced (y : Y) (z : Cm) (a : (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ) (v : Lc) :
    kModelFun j hj Q Λ Λc θ γ ν₀ Y hQ L' y (op a • z) v =
      kModelFun j hj Q Λ Λc θ γ ν₀ Y hQ L' y z (a • v) := by
  obtain ⟨r, hr⟩ := topMap_surjective' (k := k) (Q := Q) (Λ := Λc) (ν := ν₀) a.unop
  obtain rfl : a = op (topMap k Q Λc ν₀ r) := by rw [hr, op_unop]
  have hv : (op (topMap k Q Λc ν₀ r) • v : Lc) =
      toCapCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀)
        ((tensorOfKLR Q Λc ν₀ (hflip r) • (show L' from v) : L')) :=
    op_smul_capCoef (Q := Q) (Λc := Λc) (ν₀ := ν₀) r (show L' from v)
  have hz : (op (op (topMap k Q Λc ν₀ r)) • z).1.unop = σm (topMap k Q Λc ν₀ r) * z.1.unop :=
    rfl
  rw [kModelFun, kModelFun, hv, hz, plusFlip_mul, mul_smul]
  congr 1
  change fl (σm (cupMap k Q Λc ν₀ r)) • U y (show L' from v) = _
  rw [midStendhal_cupMap', plusFlip_mul, mul_smul, kSrc_flip_midStendhal_one_smul_unit,
    kSrc_flip_midBot_smul_unit]
  rfl

theorem kModelFun_add_left (y : Y) (z z' : Cm) (v : Lc) :
    kModelFun j hj Q Λ Λc θ γ ν₀ Y hQ L' y (z + z') v =
      kModelFun j hj Q Λ Λc θ γ ν₀ Y hQ L' y z v + kModelFun j hj Q Λ Λc θ γ ν₀ Y hQ L' y z' v := by
  simp only [kModelFun, Submodule.coe_add, unop_add, plusFlip_add, add_smul]

theorem kModelFun_add_right (y : Y) (z : Cm) (v v' : Lc) :
    kModelFun j hj Q Λ Λc θ γ ν₀ Y hQ L' y z (v + v') =
      kModelFun j hj Q Λ Λc θ γ ν₀ Y hQ L' y z v + kModelFun j hj Q Λ Λc θ γ ν₀ Y hQ L' y z v' := by
  rw [kModelFun, kModelFun, kModelFun, ← smul_add]
  exact congrArg (fl z.1.unop • ·)
    (kSrcU_add j hj Q Λ Λc θ γ ν₀ Y hQ L' y (show L' from v) (show L' from v'))

/-- **The map `f_y` on the model of the cap**: `v ⊗ z ↦ σ(z) · (1 ⊗ (y ⊠ v))`. -/
def kModelMap (y : Y) : MidModel j hj Q Λ Λc (θ + γ) ν₀ Lc →+ Xs :=
  Ind.liftAdd (kModelFun j hj Q Λ Λc θ γ ν₀ Y hQ L' y)
    (kModelFun_add_left j hj Q Λ Λc θ γ ν₀ Y hQ L' y)
    (kModelFun_add_right j hj Q Λ Λc θ γ ν₀ Y hQ L' y)
    (kModelFun_balanced j hj Q Λ Λc θ γ ν₀ Y hQ L' y)

theorem kModelMap_tmul (y : Y) (z : Cm) (v : Lc) :
    kModelMap j hj Q Λ Λc θ γ ν₀ Y hQ L' y (Ind.tmul z v) = fl z.1.unop • U y (show L' from v) :=
  rfl

/-- **`f_y` intertwines the right action of `T̃^{λ⁺}` on the model with its reflected left action
on the right side.** -/
theorem kModelMap_smul (y : Y)
    (b : (StendhalAlgebra k Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀))ᵐᵒᵖ)
    (t : MidModel j hj Q Λ Λc (θ + γ) ν₀ Lc) :
    kModelMap j hj Q Λ Λc θ γ ν₀ Y hQ L' y (b • t) =
      fl b.unop • kModelMap j hj Q Λ Λc θ γ ν₀ Y hQ L' y t := by
  induction t using Ind.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul z v =>
    rw [Ind.smul_tmul, kModelMap_tmul, kModelMap_tmul, ← mul_smul, ← plusFlip_mul]
    rfl
  | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

end Categorification.Stendhal.CupCap
