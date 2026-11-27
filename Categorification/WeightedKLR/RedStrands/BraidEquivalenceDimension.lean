/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidLengthInduction
import Categorification.WeightedKLR.RedStrands.TensorFormEvalOne
import Categorification.Algebra.Graded.ExtEuler

set_option backward.isDefEq.respectTransparency false

/-!
# The Euler characteristic of `Hom(𝔅_w P_t, 𝔅_w P_{t'})`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.15. Let the class map of `𝔅_w` be `x ↦ B(f x, -)` with `f` congruent at `v = 1` to
the permutation `π_w` of the tensor factors (`HasCongruentBraidClass`). For a projective
resolution `P_•` of `𝔅_w (e(t) T^λ)`, the alternating sum `Σ_j (-1)^j dim Hom(P_j, 𝔅_w e(t') T^λ)`
is `B(f η[P_{t'}], f η[P_t])` at `v = 1`, which is `B(η[P_{t'}], η[P_t])` at `v = 1` since `π_w`
preserves the form at `v = 1` (`orderedForm_tensorPermute_evalOne`), that is
`dim Hom(e(t) T^λ, e(t') T^λ)` (`altSum_finrank_hom_braidF`).

* `orderedForm_evalOne_of_sub_mem` : `B(a, b)` at `v = 1` depends on `b` only modulo `(v - 1)`.
* `altSum_finrank_hom_braidF` : the Euler characteristic of `Hom(𝔅_w P_t, 𝔅_w P_{t'})` along a
  resolution is `dim Hom(P_t, P_{t'})`.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF MulOpposite Equiv
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "𝕂" => RatFunc ℚ
local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "ev" => integralLaurentEval

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}

section SecondArgument

variable {n : ℕ} {wt : Fin n → Dom R}

/-- **The form at `v = 1` depends on the second argument only modulo `v - 1`**: if
`b - b' ∈ (v - 1) · L` and `B(a, b')`, `B(a, y)` are integral on the lattice, then `B(a, b)` and
`B(a, b')` are Laurent polynomials with the same value at `v = 1`. -/
theorem orderedForm_evalOne_of_sub_mem {a b b' : TensorSpace wt}
    (hint : ∀ y ∈ integralTensor wt, ∃ p : LP, TensorPairing.orderedForm hR wt a y = ev p)
    (hb' : b' ∈ integralTensor wt) (hsub : b - b' ∈ vOneTensor wt) :
    ∃ p q : LP, TensorPairing.orderedForm hR wt a b = ev p ∧
      TensorPairing.orderedForm hR wt a b' = ev q ∧ evalOne p = evalOne q := by
  obtain ⟨y, hy, hyeq⟩ := mem_vOneTensor_iff.1 hsub
  obtain ⟨q, hq⟩ := hint b' hb'
  obtain ⟨r, hr⟩ := hint y hy
  refine ⟨q + (LaurentPolynomial.T 1 - 1) * r, q, ?_, hq, ?_⟩
  · rw [show b = b' + (𝕍 - 1) • y by rw [← hyeq, add_sub_cancel], map_add, map_smul, hq, hr,
      smul_eq_mul, map_add, map_mul, map_sub, map_one, integralLaurentEval_T, zpow_one]
  · simp

end SecondArgument

variable [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]

local notation "G" Ω => stendhalGradingDatum Ω hQ.gradingDatum (fun i => C.dot i i / 2)
  (dotDegree C hQ)
local notation "rseq" => rightSequenceProj (G _)

include hR in
/-- **The Euler characteristic of `Hom(𝔅_w P_t, 𝔅_w P_{t'})`** (Webster, arXiv:1309.3796v3, proof
of Theorem 6.15): if the class map of `𝔅_w` is `x ↦ B(f x, -)` with `f` congruent at `v = 1` to
the permutation of the tensor factors, then along any graded projective resolution `P_•` of
`𝔅_w (e(t) T^λ)`, `Σ_j (-1)^j dim Hom(P_j, 𝔅_w (e(t') T^λ)) = dim Hom(e(t) T^λ, e(t') T^λ)`. -/
theorem altSum_finrank_hom_braidF (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) (w : Perm (Fin ℓ))
    (f : TensorSpace wt →ₗ[𝕂] TensorSpace (wt ∘ w))
    (hf : VOneCongr f (tensorPermute wt w).toLinearMap)
    (hcls : braidClass C hQ hR Λ wt hwt w = (formDual hR (wt ∘ w)).comp f)
    {ν : Multiset I} {t t' : Seq (stendhalWeight ℓ ν)} (ht : IsRedOrdered t)
    (ht' : IsRedOrdered t')
    {Ps : List (GProj (oppositeGrade (tensorProductGrade (G (Λ ∘ w)) ν)))}
    (r : GFin.Resolution (braidF C hQ Λ w ν (rightSequenceProj (G Λ) t ht).toGFin)
      (Ps.map GProj.toGFin)) :
    altSum (Ps.map fun P => (Module.finrank k (P.carrier →ₗ[(TensorProductAlgebra k Q (Λ ∘ w) ν)ᵐᵒᵖ]
        (braidF C hQ Λ w ν (rightSequenceProj (G Λ) t' ht').toGFin).carrier) : ℤ)) =
      Module.finrank k ((rightSequenceProj (G Λ) t ht).carrier →ₗ[(TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]
        (rightSequenceProj (G Λ) t' ht').carrier) := by
  have hwt' : ∀ r i, ((Λ ∘ w) r i : ℤ) = ((wt ∘ w) r).1 (R.coroot i) := fun r i => hwt (w r) i
  set N' := braidF C hQ Λ w ν (rightSequenceProj (G Λ) t' ht').toGFin
  set η := rightTensorModuleEquiv C hQ hR Λ wt hwt
  set η' := rightTensorModuleEquiv C hQ hR (Λ ∘ w) (wt ∘ w) hwt'
  set X : rightTensorProjectiveGroup C hQ (Λ ∘ w) ν := altSum (Ps.map fun P => K0.of P)
  set a : TensorSpace wt := (η (DirectSum.lof LP _ (rightTensorProjectiveGroup C hQ Λ) ν
    (K0.of (rightSequenceProj (G Λ) t ht))) : TensorSpace wt)
  set a' : TensorSpace wt := (η (DirectSum.lof LP _ (rightTensorProjectiveGroup C hQ Λ) ν
    (K0.of (rightSequenceProj (G Λ) t' ht'))) : TensorSpace wt)
  have ha : a ∈ integralTensor wt := (η _).2
  have ha' : a' ∈ integralTensor wt := (η _).2
  -- the class functional of a braided projective is `B(f a, -)`
  have hbr : ∀ {s : Seq (stendhalWeight ℓ ν)} (hs : IsRedOrdered s),
      classFunctional C hQ hR (Λ ∘ w) (wt ∘ w) hwt' ν
          (braidF C hQ Λ w ν (rightSequenceProj (G Λ) s hs).toGFin) =
        TensorPairing.orderedForm hR (wt ∘ w) (f (η (DirectSum.lof LP _ (rightTensorProjectiveGroup C hQ Λ) ν
          (K0.of (rightSequenceProj (G Λ) s hs))) : TensorSpace wt)) := by
    intro s hs
    have e := braidClass_of C hQ hR Λ wt hwt w ν (rightSequenceProj (G Λ) s hs)
    rw [hcls, LinearMap.comp_apply, formDual_apply] at e
    exact (ConjDual.of.injective e).symm
  -- the alternating sum of the classes of the resolution is `f a`
  have hX : (η' (DirectSum.lof LP _ (rightTensorProjectiveGroup C hQ (Λ ∘ w)) ν X) :
      TensorSpace (wt ∘ w)) = f a := by
    have e := classFunctional_eq_form_of_resolution C hQ hR (Λ ∘ w) (wt ∘ w) hwt' ν r
    rw [hbr ht] at e
    rw [← sub_eq_zero]
    refine (TensorPairing.orderedForm_nondegenerate hR (wt ∘ w)).1 _ fun y => ?_
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
    have hlof : DirectSum.lof LP _ (rightTensorProjectiveGroup C hQ (Λ ∘ w)) ν X =
        altSum (Ps.map fun P => DirectSum.lof LP _ (rightTensorProjectiveGroup C hQ (Λ ∘ w)) ν
          (K0.of P)) := by
      rw [map_altSum, List.map_map]
      rfl
    rw [hlof]
    exact (LinearMap.congr_fun e y).symm
  -- the left side is `cf' N' (f a)` at `v = 1`
  have hL : altSum (Ps.map fun P => (Module.finrank k (P.carrier →ₗ[(TensorProductAlgebra k Q (Λ ∘ w)
      ν)ᵐᵒᵖ] N'.carrier) : ℤ)) = evalOne (projectiveHomPolynomial _ N' X) := by
    rw [map_altSum, map_altSum, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun P _ => ?_
    rw [Function.comp_apply, Function.comp_apply, projectiveHomPolynomial_of]
    exact finrank_hom_eq_evalOne_gdimPoly P N'
  have hcfX : classFunctional C hQ hR (Λ ∘ w) (wt ∘ w) hwt' ν N' (f a) = ev (projectiveHomPolynomial _ N' X) := by
    rw [← hX, classFunctional_eta, DirectSum.lof_apply]
  rw [hbr ht'] at hcfX
  -- the right side
  have hR' : TensorPairing.orderedForm hR wt a' a = ev (gdimPoly (homGrade (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ
      (rightSequenceProj (G Λ) t ht).grading (rightSequenceProj (G Λ) t' ht').grading)) := by
    have e := classFunctional_of C hQ hR Λ wt hwt ν (rightSequenceProj (G Λ) t' ht').toGFin
      (rightSequenceProj (G Λ) t ht)
    rw [classFunctional_projective] at e
    exact e
  have hRfin := finrank_hom_eq_evalOne_gdimPoly (rightSequenceProj (G Λ) t ht)
    (rightSequenceProj (G Λ) t' ht').toGFin
  -- integrality
  have hint : ∀ x ∈ integralTensor wt, ∀ y ∈ integralTensor wt, ∃ p : LP, TensorPairing.orderedForm hR wt x y = ev p :=
    fun x hx y hy => orderedForm_integralTensor C hQ hR Λ wt hwt hx hy
  have hint' : ∀ x ∈ integralTensor (wt ∘ w), ∀ y ∈ integralTensor (wt ∘ w),
      ∃ p : LP, TensorPairing.orderedForm hR (wt ∘ w) x y = ev p :=
    fun x hx y hy => orderedForm_integralTensor C hQ hR (Λ ∘ w) (wt ∘ w) hwt' hx hy
  obtain ⟨p₁, q₁, hp₁, hq₁, h₁⟩ := orderedForm_evalOne_of_vOneCongr C hQ hR (Λ ∘ w) (wt ∘ w) hwt'
    hf ha' (hf.left a ha)
  obtain ⟨p₂, q₂, hp₂, hq₂, h₂⟩ := orderedForm_evalOne_of_sub_mem C hR
    (fun y hy => hint' _ (hf.right a' ha') y hy) (hf.right a ha) (hf.sub a ha)
  obtain ⟨p₃, q₃, hp₃, hq₃, h₃⟩ := TensorPairing.orderedForm_tensorPermute_evalOne hR wt w
    hint hint' ha' ha
  have e₁ : p₁ = projectiveHomPolynomial _ N' X :=
    integralLaurentEval_injective (hp₁.symm.trans hcfX)
  have e₂ : q₁ = p₂ := integralLaurentEval_injective (hq₁.symm.trans hp₂)
  have e₃ : q₂ = p₃ := integralLaurentEval_injective (hq₂.symm.trans hp₃)
  have e₄ : q₃ = gdimPoly (homGrade (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ
      (rightSequenceProj (G Λ) t ht).grading (rightSequenceProj (G Λ) t' ht').grading) :=
    integralLaurentEval_injective (hq₃.symm.trans hR')
  rw [hL, ← e₁, h₁, e₂, h₂, e₃, h₃, e₄]
  exact_mod_cast hRfin.symm

end Categorification.Stendhal.FirstWeight
