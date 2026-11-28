/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.ClassFunctionalInvariance
import Categorification.WeightedKLR.Rigidity.QuantumInvariantFunctional

/-!
# Class functionals on `V_μ ⊗ V_{μ*}` killed by the `F_i`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 7.5, invariance step on the categorical side. For two red strands of weights
`(μ, μ*)`, the class functional of a finite-dimensional graded right module `N` over `T^{(μ,μ*)}`
that is killed by the loadings with a black strand right of the second red strand and has
weight `0` is a multiple of the quantum trace `qtr_μ`
(`classFunctional_eq_smul_quantumTrace`), and equals `qtr_μ` once its value on `v_l ⊗ v_h` is
`1` (`classFunctional_eq_quantumTrace`).

**Route hypothesis.** The class functional lives on the library's ordered tensor product
`TensorSpace wt` (`wt = (μ, μ*)`, with the action `tensorRepresentation`), while `qtr_μ` lives on
`TensorModule V_μ V_{μ*}`. The statements take a `U_q(g)`-equivariant linear equivalence
`Φ : TensorSpace wt ≃ V_μ ⊗ V_{μ*}` as an explicit hypothesis (`Φ`, `hΦ`). Its construction
(convention point (a) of the Proposition 7.20 comparison) is not part of this file.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF MulOpposite Module
open Categorification.Stendhal.QuantumDual
open scoped RatFunc TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "𝕂" => RatFunc ℚ
local notation "v" => (RatFunc.X : 𝕂)
local instance classFunctionalQuantumTraceInst : NeZero (RatFunc.X : 𝕂) := ⟨RatFunc.X_ne_zero⟩

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Fintype I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) (Λ : Fin 2 → I →₀ ℕ)
    (wt : Fin 2 → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

set_option hygiene false in
local notation "G" =>
  stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
set_option hygiene false in
local notation "𝒜" ν => oppositeGrade (tensorProductGrade G ν)
set_option hygiene false in
local notation "cf" => classFunctional C hQ hR Λ wt hwt
set_option hygiene false in
local notation "ρ" => tensorRepresentation wt

variable [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]

variable {Kf H : Type*} [Field Kf] [ConditionallyCompleteLinearOrder Kf] [IsStrictOrderedRing Kf]
    [AddCommGroup H] [Module Kf H] (P : Matrix.Realization C.toLusztig.cartanMatrix Kf H)
    [FiniteDimensional Kf H] (μ : Dom R) (weight : P.integralWeights)
    (hdom : P.IsDominantIntegral (weight : Dual Kf H))
    (hm : ∀ j, (weight : Dual Kf H) (P.coroot j) = (μ.1 (R.coroot j) : Kf)) (w : List I)
    (hw : (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
    (hlong : ∀ i, (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsLeftDescent
      ((P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i)

set_option hygiene false in
local notation "μs" => dualWeight P μ weight hdom hm w hw hlong
set_option hygiene false in
local notation "Vμ" => IrreducibleModule R v (Subtype.val μ)
set_option hygiene false in
local notation "Vμs" =>
  IrreducibleModule R v (Subtype.val (dualWeight P μ weight hdom hm w hw hlong))
set_option hygiene false in
local notation "vl" => lowestVector P μ weight w
set_option hygiene false in
local notation "qtr" => quantumTrace P hR μ weight hdom hm w hw hlong
set_option hygiene false in
local notation "vlh" =>
  TensorModule.mk Vμ Vμs (lowestVector P μ weight w ⊗ₜ IrreducibleModule.hwv R v μs.1)

variable (Φ : TensorSpace wt ≃ₗ[𝕂] TensorModule 𝕂 Vμ Vμs)
    (hΦ : ∀ (u : QuantumGroup R v) (x : TensorSpace wt), Φ (ρ u x) = u • Φ x)

include hΦ in
/-- **The class functional is a multiple of `qtr_μ`** (Webster, arXiv:1309.3796v3, proof of
Proposition 7.5, "`[L_λ]` is invariant"): for `N` of weight `0` (`Σ_r λ_r = Σ_{i∈ν} α_i`) killed
by every loading whose last strand is black,
`classFunctional N = classFunctional N (Φ⁻¹ (v_l ⊗ v_h)) • (qtr_μ ∘ Φ)`.
Route hypothesis: the equivariant identification `Φ`, `hΦ` (see the module docstring). -/
theorem classFunctional_eq_smul_quantumTrace (ν : Multiset I) (N : GFin (𝒜 ν))
    (hN : ∀ (t : Seq (stendhalWeight 2 ν)) (ht : IsRedOrdered t), IsLastBlack t →
      ∀ x : N.carrier, op (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht)) • x = 0)
    (hν : ∑ r, (wt r).1 = R.rootSum ν.toFinsupp) :
    cf ν N = cf ν N (Φ.symm vlh) • (qtr ∘ₗ Φ.toLinearMap) := by
  have hK : ∀ (y : Y) (t : TensorModule 𝕂 Vμ Vμs),
      cf ν N (Φ.symm (QuantumGroup.K R v y • t)) = cf ν N (Φ.symm t) := fun y t => by
    rw [Φ.symm_apply_eq.2 (by rw [hΦ, LinearEquiv.apply_symm_apply])]
    exact classFunctional_K C hQ hR Λ wt hwt ν N hν y _
  have hF : ∀ (i : I) (t : TensorModule 𝕂 Vμ Vμs),
      cf ν N (Φ.symm (QuantumGroup.F R v i • t)) = 0 := fun i t => by
    rw [Φ.symm_apply_eq.2 (by rw [hΦ, LinearEquiv.apply_symm_apply])]
    exact LinearMap.congr_fun (classFunctional_comp_F_eq_zero C hQ hR Λ wt hwt ν N hN i) _
  have h := eq_smul_quantumTrace_of_F P hR μ weight hdom hm w hw hlong
    ((cf ν N).comp Φ.symm.toLinearMap) hK hF
  refine LinearMap.ext fun x => ?_
  have hx := LinearMap.congr_fun h (Φ x)
  simpa using hx

include hΦ in
/-- **Webster's normalization**: if moreover the class functional is `1` at `Φ⁻¹ (v_l ⊗ v_h)`,
it is the quantum trace, `classFunctional N = qtr_μ ∘ Φ` (Webster, arXiv:1309.3796v3,
Proposition 7.5, with `qtr_μ (v_l ⊗ v_h) = 1`, `quantumTrace_lowest_hwv`).
Route hypothesis: `Φ`, `hΦ`. -/
theorem classFunctional_eq_quantumTrace (ν : Multiset I) (N : GFin (𝒜 ν))
    (hN : ∀ (t : Seq (stendhalWeight 2 ν)) (ht : IsRedOrdered t), IsLastBlack t →
      ∀ x : N.carrier, op (TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e t ht)) • x = 0)
    (hν : ∑ r, (wt r).1 = R.rootSum ν.toFinsupp) (h1 : cf ν N (Φ.symm vlh) = 1) :
    cf ν N = qtr ∘ₗ Φ.toLinearMap := by
  rw [classFunctional_eq_smul_quantumTrace C hQ hR Λ wt hwt P μ weight hdom hm w hw hlong Φ hΦ
    ν N hN hν, h1, one_smul]

end Categorification.Stendhal.FirstWeight
