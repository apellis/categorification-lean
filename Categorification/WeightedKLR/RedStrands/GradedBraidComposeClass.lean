/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidCompose
import Categorification.WeightedKLR.RedStrands.GradedBraidResolutionClass
import Categorification.WeightedKLR.RedStrands.TensorFormUnique

set_option backward.isDefEq.respectTransparency false

/-!
# The class map of a composite of braid functors

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11 (step `p_n` on classes). Let `τ * σ` be length-additive over `τ`, so that
`𝔅_σ ∘ 𝔅_τ ≅ 𝔅_{τ σ}` (`braidFunctorCompIso`). Suppose the class maps of `𝔅_τ` and of `𝔅_σ`
(for the labels `λ ∘ τ`) are `x ↦ B(f_τ x, -)` and `y ↦ B(f_σ y, -)`. If every `𝔅_τ P`, `P`
projective, has a finite projective resolution and is braid-concentrated for `σ`, then the class
map of `𝔅_{τ σ}` is `x ↦ B(f_σ (f_τ x), -)` (`braidClass_mul`).

## Main results

* `ext_rightTensorModuleEquiv` : `ℚ(v)`-linear maps on `V_λ` agreeing on the classes `η [P]` of
  projectives are equal.
* `classFunctional_braidF_mul` : the class functional of `𝔅_{τ σ} N` is that of `𝔅_σ (𝔅_τ N)`.
* `braidClass_mul` : the class map of `𝔅_{τ σ}`.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF MulOpposite Equiv
open scoped RatFunc
open DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "𝕂" => RatFunc ℚ

universe w

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2)
  (dotDegree C hQ)
local notation "Kr" => rightTensorProjectiveGroup C hQ Λ
local notation "η'" => rightTensorModuleEquiv C hQ hR Λ wt hwt
local notation "𝒜" ν => oppositeGrade (tensorProductGrade G ν)

/-- `ℚ(v)`-linear maps on `V_λ` that agree on the classes `η [P]` of graded right projectives
are equal. -/
theorem ext_rightTensorModuleEquiv {M : Type*} [AddCommGroup M] [Module 𝕂 M]
    {f g : TensorSpace wt →ₗ[𝕂] M}
    (h : ∀ (ν : Multiset I) (P : GProj (𝒜 ν)),
      f (η' (DirectSum.lof LP _ Kr ν (K0.of P))) = g (η' (DirectSum.lof LP _ Kr ν (K0.of P)))) :
    f = g := by
  suffices hfg : ∀ x, f (η' x) = g (η' x) by
    refine Lattice.ext_of_lattice (isLattice_integralTensor C hR wt) fun z hz => ?_
    obtain ⟨x, hx⟩ := (η').surjective ⟨z, hz⟩
    have hzx : z = (η' x : TensorSpace wt) := by rw [hx]
    rw [hzx]
    exact hfg x
  intro x
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, ZeroMemClass.coe_zero, map_zero, map_zero]
  | of ν y =>
    rw [← DirectSum.lof_eq_of LP]
    induction y using Graded.K0.induction_on with
    | of P => exact h ν P
    | zero => rw [map_zero, map_zero, ZeroMemClass.coe_zero, map_zero, map_zero]
    | add a b ha hb =>
      rw [map_add, map_add, Submodule.coe_add, map_add, map_add, ha, hb]
    | neg a ha => rw [map_neg, map_neg, Submodule.coe_neg, map_neg, map_neg, ha]
  | add x y hx hy => rw [map_add, Submodule.coe_add, map_add, map_add, hx, hy]

variable [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]
  (τ σ : Perm (Fin ℓ))
  (H : ∀ x y, List.Sublist [x, y] ((List.finRange ℓ).map ⇑(τ * σ)) →
    List.Sublist [y, x] ((List.finRange ℓ).map τ) → List.Sublist [y, x] (List.finRange ℓ))

local notation "𝒜τ" ν => oppositeGrade (tensorProductGrade
  (stendhalGradingDatum (Λ ∘ τ) hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)) ν)

include H in
/-- The class functional of `𝔅_{τ σ} N` is the class functional of `𝔅_σ (𝔅_τ N)` when the
lengths add (Webster, arXiv:1309.3796v2, Lemma 6.5). -/
theorem classFunctional_braidF_mul (ν : Multiset I) (N : GFin (𝒜 ν)) :
    classFunctional C hQ hR (Λ ∘ ⇑(τ * σ)) (wt ∘ ⇑(τ * σ)) (fun r i => hwt ((τ * σ) r) i) ν
        (braidF C hQ Λ (τ * σ) ν N) =
      classFunctional C hQ hR ((Λ ∘ τ) ∘ σ) ((wt ∘ τ) ∘ σ) (fun r i => hwt (τ (σ r)) i) ν
        (braidF C hQ (Λ ∘ τ) σ ν (braidF C hQ Λ τ ν N)) :=
  classFunctional_congr C hQ hR (Λ ∘ ⇑(τ * σ)) (wt ∘ ⇑(τ * σ)) (fun r i => hwt ((τ * σ) r) i) ν
    (BraidedStendhalAlgebra.braidFunctorCompIso (isReducedChoice_canChoice ν) hQ.klrSymm τ σ H
      hQ N).symm

include H in
/-- **The class map of a composite of braid functors** (Webster, arXiv:1309.3796v2, proof of
Lemma 6.11, `p_n` on classes): if the class maps of `𝔅_τ` and `𝔅_σ` are `x ↦ B(f_τ x, -)` and
`y ↦ B(f_σ y, -)`, the lengths of `τ` and `σ` add, and every `𝔅_τ P` with `P` projective has a
finite projective resolution and is braid-concentrated for `σ`, then the class map of `𝔅_{τ σ}`
is `x ↦ B(f_σ (f_τ x), -)`. -/
theorem braidClass_mul
    [∀ ν, DG.HasDerivedCategory.{w} (IsIdempotentElem.Corner
      (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj k Q (Λ ∘ τ) ν
        (List.finRange ℓ)))ᵐᵒᵖ]
    [∀ ν, DG.HasDerivedCategory.{w} (IsIdempotentElem.Corner
      (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj k Q (Λ ∘ τ) ν
        (List.map σ (List.finRange ℓ))))ᵐᵒᵖ]
    (fτ : TensorSpace wt →ₗ[𝕂] TensorSpace (wt ∘ τ))
    (fσ : TensorSpace (wt ∘ τ) →ₗ[𝕂] TensorSpace ((wt ∘ τ) ∘ σ))
    (hτ : braidClass C hQ hR Λ wt hwt τ = (formDual hR (wt ∘ τ)).comp fτ)
    (hσ : braidClass C hQ hR (Λ ∘ τ) (wt ∘ τ) (fun r i => hwt (τ r) i) σ =
      (formDual hR ((wt ∘ τ) ∘ σ)).comp fσ)
    (hN : ∀ (ν : Multiset I) (P : GProj (𝒜 ν)),
      BraidedStendhalAlgebra.BraidConcentrated.{w} (Λ ∘ τ) ν (isReducedChoice_canChoice ν)
        hQ.klrSymm σ hQ (braidF C hQ Λ τ ν P.toGFin) ∧
      ∃ Ps : List (GProj (𝒜τ ν)),
        Nonempty (GFin.Resolution (braidF C hQ Λ τ ν P.toGFin) (Ps.map GProj.toGFin))) :
    braidClass C hQ hR Λ wt hwt (τ * σ) = (formDual hR ((wt ∘ τ) ∘ σ)).comp (fσ ∘ₗ fτ) := by
  refine ext_rightTensorModuleEquiv C hQ hR Λ wt hwt fun ν P => ?_
  obtain ⟨hc, Ps, ⟨r⟩⟩ := hN ν P
  have hx := classFunctional_eq_form_of_resolution C hQ hR (Λ ∘ τ) (wt ∘ τ)
    (fun r i => hwt (τ r) i) ν r
  have hτP := braidClass_of C hQ hR Λ wt hwt τ ν P
  rw [hτ, LinearMap.comp_apply, formDual_apply, hx] at hτP
  have hf : fτ (η' (DirectSum.lof LP _ Kr ν (K0.of P))) =
      (rightTensorModuleEquiv C hQ hR (Λ ∘ τ) (wt ∘ τ) (fun r i => hwt (τ r) i)
        (altSum (Ps.map fun P => DirectSum.lof LP _ (rightTensorProjectiveGroup C hQ (Λ ∘ τ)) ν
          (K0.of P))) : TensorSpace (wt ∘ τ)) := by
    have h1 := ConjDual.of.injective hτP
    refine sub_eq_zero.mp ((TensorPairing.orderedForm_nondegenerate hR (wt ∘ τ)).1 _ fun y => ?_)
    rw [map_sub, LinearMap.sub_apply, h1, sub_self]
  rw [braidClass_of]
  change _ = formDual hR ((wt ∘ τ) ∘ σ) (fσ (fτ (η' (DirectSum.lof LP _ Kr ν (K0.of P)))))
  rw [hf, ← LinearMap.comp_apply (formDual hR ((wt ∘ τ) ∘ σ)) fσ, ← hσ,
    braidClass_resolution_of_braidConcentrated C hQ hR (Λ ∘ τ) (wt ∘ τ)
      (fun r i => hwt (τ r) i) σ ν r hc]
  exact congrArg ConjDual.of (classFunctional_braidF_mul C hQ hR Λ wt hwt τ σ H ν P.toGFin)

end Categorification.Stendhal.FirstWeight
