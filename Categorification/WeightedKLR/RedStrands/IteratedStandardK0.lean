/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.IteratedStandardCharacter
import Categorification.WeightedKLR.RedStrands.TensorRestrictionAdjoint

set_option backward.isDefEq.respectTransparency false

/-!
# Standard modules as functionals on the projective group

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5,
Proposition 5.6. The class of a finite-dimensional module `M` in the Grothendieck group of
finite-dimensional modules is determined by the functional `[P] ↦ dim_q Hom(P, M)` on the
projective group. For Webster's standard module `S_κ^i` this functional, transported along
the identification `η` of Theorem 4.38, is the componentwise form against
`s = F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_n} v_{λ_n}`, read in the bar coproduct convention.

## Main results

* `iteratedStandardTest`: the Hom functional of `S_κ^i` on the projective group of a block.
* `iteratedStandardTest_eq`: its value on every virtual projective class, through `η`.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR Categorification.Graded QuantumGroup LieLean LieLean.QuantumGroup
  LieLean.QuantumGroup.GrandLoop LusztigF

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "𝕂" => RatFunc ℚ
local notation "v" => (RatFunc.X : 𝕂)
private local instance standardK0NeZero : NeZero v := ⟨RatFunc.X_ne_zero⟩
local notation "qToV" => KLGamma.qToV

variable {I : Type} [DecidableEq I] [Finite I] {k : Type} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
  {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular)

/-- The functional `[P] ↦ dim_q Hom(P, S_κ^i)` on the projective group of the black block
`ν`, with the grading variable sent to `v⁻¹`. -/
def iteratedStandardTest (n : ℕ) (Λ : Fin n → I →₀ ℕ) (u : Fin n → List I) (ν : Multiset I) :
    tensorProjectiveGroup C hQ Λ ν →ₛₗ[qToV] 𝕂 :=
  let := tensorProductAlgebra_finite Λ ν hQ
  { toFun := fun x => qToV (projectiveCharacter _ (iteratedStandard C hQ n Λ u ν) x)
    map_add' := fun x y => by simp
    map_smul' := fun c x => by simp }

omit [Finite I] in
private theorem iteratedStandardTest_of (n : ℕ) (Λ : Fin n → I →₀ ℕ) (u : Fin n → List I)
    (ν : Multiset I) (p : GProj (tensorProductGrade (iteratedGrading C hQ Λ) ν)) :
    iteratedStandardTest C hQ n Λ u ν (K0.of p) =
      integralLaurentEval (gdimPoly (homGrade (TensorProductAlgebra k Q Λ ν) p.grading
        (iteratedStandard C hQ n Λ u ν).grading)) := by
  let := tensorProductAlgebra_finite Λ ν hQ
  change qToV (LaurentPolynomial.invert (projectiveHomPolynomial _ _ (K0.of p))) = _
  rw [projectiveHomPolynomial_of, ← CycKLR.integralEval_invert]
  exact congrArg integralLaurentEval (LaurentPolynomial.invert.symm_apply_apply _)

/-- **Standard modules on the projective group** (Webster, arXiv:1309.3796v2, Proposition 5.6,
in the form that determines the class of `S_κ^i`). For every virtual projective class `x` of
black content `ν`, the graded Hom from `x` into `S_κ^i` is the componentwise form of
`F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_n} v_{λ_n}` with the image of `x` under Webster's
identification `η` of Theorem 4.38, read in the bar coproduct convention. -/
theorem iteratedStandardTest_eq (n : ℕ) (Λ : Fin n → I →₀ ℕ) (u : Fin n → List I)
    (wt : Fin n → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    (ν : Multiset I) (x : tensorProjectiveGroup C hQ Λ ν) :
    iteratedStandardTest C hQ n Λ u ν x =
      TensorPairing.orderedFactorwise hR wt (wordTensor C wt u)
        ((tensorCoproductEquiv hR wt).symm
          (tensorModuleEquiv C hQ hR Λ wt hwt
            (DirectSum.lof LP _ (tensorProjectiveGroup C hQ Λ) ν x) : TensorSpace wt)) := by
  let T := iteratedStandardTest C hQ n Λ u ν
  let g := TensorPairing.orderedFactorwise hR wt (wordTensor C wt u)
  have hx : x ∈ Submodule.span LP {z | ∃ (w : TensorWord I n) (e : w.content.toMultiset = ν),
      z = e ▸ K0.of (tensorWordProjective Λ C hQ w)} := by
    rw [span_tensorWordProjective Λ C hQ ν]
    trivial
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w, rfl, rfl⟩ := hz
    change T (K0.of (tensorWordProjective Λ C hQ w)) =
      g ((tensorCoproductEquiv hR wt).symm
        (tensorModuleEquiv C hQ hR Λ wt hwt (tensorWordProjectiveClass Λ C hQ w) : TensorSpace wt))
    rw [tensorModuleEquiv_word]
    let c := KL2.divQFact2 C w.blackBlocks
    apply smul_right_injective 𝕂 (KL2Gamma.qToV_divQFact2_ne_zero C w.blackBlocks)
    change qToV c • T (K0.of (tensorWordProjective Λ C hQ w)) =
      qToV c • g ((tensorCoproductEquiv hR wt).symm (tensorWordVector w wt))
    rw [← T.map_smulₛₗ, ← tensorWordProjective_factorial Λ C hQ w, iteratedStandardTest_of,
      ← g.map_smul, ← (tensorCoproductEquiv hR wt).symm.map_smul, ← tensorWordVector_factorial,
      ← tensorCoproductEquiv_ordinary hR w wt, LinearEquiv.symm_apply_apply]
    have hc := ordinary_hom_eq_corner (Q := Q) Λ C hQ _ ⟨w, rfl⟩
      (iteratedStandard C hQ n Λ u w.content.toMultiset)
    have hw := iteratedStandard_word C hQ hR n Λ u wt (fun r i => (hwt r i).symm)
      w.content.toMultiset ⟨w, rfl⟩
    exact (congrArg integralLaurentEval hc).trans hw
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | smul p x _ hx =>
    rw [T.map_smulₛₗ, hx, map_smulₛₗ, map_smulₛₗ, SetLike.val_smul, tensor_laurent_smul,
      map_smul, map_smul]
    change _ = integralLaurentEval (LaurentPolynomial.invert p) • _
    rw [CycKLR.integralEval_invert]

end Categorification.Stendhal.FirstWeight
