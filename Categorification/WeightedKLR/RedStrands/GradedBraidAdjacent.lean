/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidRowClass
import Categorification.WeightedKLR.RedStrands.GradedBraidGenerators
import Categorification.WeightedKLR.RedStrands.GradedBraidCorollary
import Categorification.WeightedKLR.RedStrands.TensorBraiding

set_option backward.isDefEq.respectTransparency false

/-!
# The braid functor of an adjacent transposition categorifies the braiding

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
Corollary 6.10. For `n + 2 + m` red strands and the transposition `π` of the strands
`n + 1, n + 2`, the class map of the graded braid functor `𝔅_π` is `x ↦ B(v² R x, -)`, where
`R : V_λ → V_{λ ∘ π}` is the braiding of the factors `n + 1, n + 2` normalized by
`R (y ⊗ v_h) = v^{-(ν, λ_{n+2})} v_h ⊗ y` for `y` of depth `ν` (`adjacentBraiding`) and `B` is
the form of `V_{λ ∘ π}` (`braidClass_pairSwap`).

Webster states the corollary for his braiding, normalized by
`y ⊗ v_h ↦ v^{⟨wt y, λ_{n+2}⟩} v_h ⊗ y`; the two differ by the scalar `v^{⟨λ_{n+1}, λ_{n+2}⟩}`.
The factor `v²` comes from the degree `-2` of the red/red crossing in the grading used here.

Route hypotheses: `AllFiniteDeltaInjective` (Corollary 5.22) and, at every row of words with
an empty word at `n + 2`, `RowFigureFiveHypotheses` (the injectivity hypothesis of Lemma 6.8;
the kernel filtration of Lemma 6.8 and `StackedStandard` of Proposition 6.9 are proved).
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped RatFunc
open DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra
local notation "𝕂" => RatFunc ℚ
local notation "v" => (RatFunc.X : 𝕂)

universe w

section Depth

variable {I : Type} {Y : Type*} [AddCommGroup Y] {D : LusztigCartanDatum I}
  (R : D.RootDatum Y)

theorem pairDepth_wordWeight (Λ : Y →+ ℤ) (l : List I) :
    pairDepth R Λ (wordWeight l) = (l.map fun i => Λ (ktilde R i)).sum := by
  induction l with
  | nil => simp [pairDepth]
  | cons i l ih =>
    rw [wordWeight_cons, add_comm, pairDepth_add_single, ih, List.map_cons, List.sum_cons,
      add_comm]

end Depth

/-- Values of a dependent function at equal arguments are heterogeneously equal. -/
theorem heq_apply_of_eq {α : Type*} {β : α → Type*} (g : ∀ a, β a) {a b : α} (h : a = b) :
    HEq (g a) (g b) := by
  subst h
  rfl

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {n m : ℕ} (Λ : Fin (n + 2 + m) → I →₀ ℕ)
    (wt : Fin (n + 2 + m) → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    [∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ) (ν : Multiset I),
      Module.Finite k (TensorProductAlgebra k Q Ω ν)]

omit [DecidableEq I] [Finite I] in
include hwt in
theorem pairDepth_wordWeight_reverse (l : List I) :
    pairDepth R (wt (rightPos n m)).1 (wordWeight l.reverse) =
      Multiset.sum (Multiset.map (fun i => QuantumGroup.UDot.di C i *
        (Λ (rightPos n m) i : ℤ)) (l : Multiset I)) := by
  rw [pairDepth_wordWeight, List.map_reverse, List.sum_reverse, Multiset.map_coe,
    Multiset.sum_coe]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [ktilde, map_nsmul, hwt, nsmul_eq_mul, QuantumGroup.UDot.di]
  have := C.toLusztig.two_mul_d i
  change 2 * (C.toLusztig.d i : ℤ) = C.dot i i at this
  congr 1
  omega

/-- **Webster, arXiv:1309.3796v2, §6.1, Corollary 6.10** (graded form): for `n + 2 + m` red
strands and the transposition `π` of the strands `n + 1, n + 2`, the class map of the graded
braid functor `𝔅_π` is `x ↦ B(v² R x, -)`, with `R` the braiding of the factors `n + 1, n + 2`
(`adjacentBraiding`, normalized by `R (y ⊗ v_h) = v^{-(ν, λ_{n+2})} v_h ⊗ y` for `y` of depth
`ν`). Webster's braiding is `v^{⟨λ_{n+1}, λ_{n+2}⟩} R`. Route hypotheses:
`AllFiniteDeltaInjective` (Corollary 5.22) and `RowFigureFiveHypotheses` (injectivity in
Lemma 6.8) at every row of words with an empty word at `n + 2`. -/
theorem braidClass_pairSwap
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ.klrSymm)
    (H : ∀ (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []),
      RowFigureFiveHypotheses C hQ Λ u hu)
    [∀ ν, DG.HasDerivedCategory.{w, 0} (IsIdempotentElem.Corner
      (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj k Q Λ ν
        (List.finRange (n + 2 + m))))ᵐᵒᵖ]
    [∀ ν, DG.HasDerivedCategory.{w, 0} (IsIdempotentElem.Corner
      (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj k Q Λ ν
        ((List.finRange (n + 2 + m)).map (pairSwap n m))))ᵐᵒᵖ] :
    braidClass C hQ hR Λ wt hwt (pairSwap n m) =
      (formDual hR (wt ∘ pairSwap n m)).comp ((v ^ (2 : ℤ) : 𝕂) •
        (adjacentBraiding hR wt (wt ∘ pairSwap n m)
          (fun j => by simp only [Function.comp_apply, pairSwap_castAdd])
          (by simp only [Function.comp_apply]; exact congrArg wt (Equiv.swap_apply_left _ _))
          (by simp only [Function.comp_apply]; exact congrArg wt (Equiv.swap_apply_right _ _))
          (fun j => by simp only [Function.comp_apply, pairSwap_natAdd])).toLinearMap) := by
  refine ext_tensorSpace_wordTensor C hR wt (dualAction (wt ∘ pairSwap n m)) _ _
    (fun i z => braidClass_F_dualAction C hQ hR Λ wt hwt (pairSwap n m) i z)
    (fun i z => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        LinearMap.smul_apply]
      erw [(intertwines_adjacentBraiding hR wt _ _ _ _ _) (F R v i) z]
      rw [map_smul, map_smul, formDual_rho, map_smul]) fun u hu => ?_
  rw [braidClass_wordTensor.{w} C hQ hR Λ wt hwt hall u hu (H u hu), LinearMap.comp_apply,
    LinearMap.smul_apply, LinearEquiv.coe_coe]
  conv_rhs => rw [wordTensor]
  rw [adjacentBraiding_tprod_hwv hR wt (wt ∘ pairSwap n m) _ _ _ _ _
      (fun j => ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂
        (IrreducibleModule R v (wt (pairSwap n m j)).1) (F R v i)) (u (pairSwap n m j))
        (IrreducibleModule.hwv R v (wt (pairSwap n m j)).1))
      (ν := wordWeight (u (leftPos n m)).reverse) ?_ ?_ ?_ ?_ ?_ ?_]
  rotate_left
  · rw [← wordVec_nil, ordinarySuffixOp_wordVec C, List.append_nil]
    exact wordVec_mem_weightSpace _ _
  · simp only [hu]
    rfl
  · exact fun j => heq_apply_of_eq (fun j => ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂
      (IrreducibleModule R v (wt j).1) (F R v i)) (u j) (IrreducibleModule.hwv R v (wt j).1))
      (pairSwap_castAdd j)
  · exact heq_apply_of_eq (fun j => ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂
      (IrreducibleModule R v (wt j).1) (F R v i)) (u j) (IrreducibleModule.hwv R v (wt j).1))
      (Equiv.swap_apply_left _ _)
  · exact heq_apply_of_eq (fun j => ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂
      (IrreducibleModule R v (wt j).1) (F R v i)) (u j) (IrreducibleModule.hwv R v (wt j).1))
      (Equiv.swap_apply_right _ _)
  · exact fun j => heq_apply_of_eq (fun j => ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂
      (IrreducibleModule R v (wt j).1) (F R v i)) (u j) (IrreducibleModule.hwv R v (wt j).1))
      (pairSwap_natAdd j)
  rw [smul_smul, formDual_apply, LinearMap.map_smulₛₗ, integralLaurentEval_T,
    pairDepth_wordWeight_reverse C Λ wt hwt]
  have hc : (v ^ (Multiset.sum (Multiset.map (fun i => QuantumGroup.UDot.di C i *
      (Λ (rightPos n m) i : ℤ)) (u (leftPos n m) : Multiset I)) - 2) : 𝕂) =
      barRingHom (v ^ (2 : ℤ) * v ^ (-Multiset.sum (Multiset.map (fun i =>
        QuantumGroup.UDot.di C i * (Λ (rightPos n m) i : ℤ)) (u (leftPos n m) : Multiset I)))) := by
    change _ = RatFunc.bar _
    rw [map_mul, bar_zpow_X, bar_zpow_X, ← zpow_add₀ RatFunc.X_ne_zero]
    congr 1
    ring
  rw [hc]
  rfl

end Categorification.Stendhal.FirstWeight
