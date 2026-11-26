/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RightTensorHomForm
import Categorification.WeightedKLR.RedStrands.LatticeExtension
import Categorification.WeightedKLR.RedStrands.TensorFactorSeparation
import Categorification.Algebra.Graded.ProjectiveCharacter
import Categorification.KLR.CyclotomicIntegralLattice
import Categorification.KLR.BarGamma

/-!
# Classes of finite-dimensional graded right modules as functionals

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §4.7,
Theorem 4.38, and Corollary 6.10. A finite-dimensional graded right `T^λ`-module `N` need not
be projective. Its class is read through the graded Hom pairing with projectives:
`[P] ↦ gdim HOM(P, N)`. Transported along Webster's identification `η` of Theorem 4.38 (for right
projectives, `rightTensorModuleEquiv`), this is an additive map on the integral lattice of
`V_λ = V_{λ_1} ⊗ ⋯ ⊗ V_{λ_ℓ}`, linear along `q ↦ v`. It extends to a `ℚ(v)`-linear functional
`classFunctional N` on `V_λ` (`Lattice.extend`). For a projective module this functional is the
form against its class, `B(η [P], -)` (`classFunctional_projective`), by Lemma 4.36 in the form
`rightTensorModuleEquiv_homForm_of`.

## Main definitions and results

* `classFunctional N` : the class of `N` as a `ℚ(v)`-linear functional on `V_λ`.
* `classFunctional_eta`, `classFunctional_of` : its values on projective classes.
* `classFunctional_eq_of_shortExact` : additivity in short exact sequences.
* `classFunctional_projective` : `classFunctional P = B(η [P], -)` for `P` projective.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "𝕂" => RatFunc ℚ
local notation "series" => algebraMap 𝕂 (LaurentSeries ℚ)
local notation "ev" => integralLaurentEval
private abbrev invRing : LP ≃+* LP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local notation "inv" => invRing
local instance tensorClassFunctionalInst1 : NeZero (RatFunc.X : 𝕂) := ⟨RatFunc.X_ne_zero⟩
local instance tensorClassFunctionalInst2 : RingHomInvPair invRing.toRingHom invRing.toRingHom :=
  RingHomInvPair.of_ringEquiv invRing

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "Kr" => rightTensorProjectiveGroup C hQ Λ
local notation "Mr" => DirectSum (Multiset I) (rightTensorProjectiveGroup C hQ Λ)
local notation "η'" => rightTensorModuleEquiv C hQ hR Λ wt hwt
local notation "B" => TensorPairing.orderedForm hR wt
local notation "𝒜" ν => oppositeGrade (tensorProductGrade G ν)

/- Finiteness of `T^λ` in each black content (`tensorProductAlgebra_op_finite`) is taken as an
instance argument so that graded Hom polynomials can be stated; it always holds for Rouquier
parameters over a field. -/
variable [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]

include hR in
/-- The integral tensor lattice is a spanning `ℤ[q, q⁻¹]`-lattice of `V_λ`. -/
theorem isLattice_integralTensor : Lattice.IsLattice (integralTensor wt).toAddSubgroup where
  smul_mem a _ hx := (integralTensor wt).smul_mem a hx
  span_eq := rationalSpan_integralTensor hR wt

/-- The graded Hom polynomial of `N` on the integral lattice, through `η⁻¹`. -/
private def latticeCharacter (ν : Multiset I) (N : GFin (𝒜 ν)) :
    (integralTensor wt).toAddSubgroup →+ 𝕂 :=
  (ev : LP →+* 𝕂).toAddMonoidHom.comp <| (projectiveHomPolynomial _ N).comp <|
    (DirectSum.component LP _ Kr ν).toAddMonoidHom.comp (η').symm.toAddEquiv.toAddMonoidHom

private theorem latticeCharacter_apply (ν : Multiset I) (N : GFin (𝒜 ν))
    (z : (integralTensor wt).toAddSubgroup) :
    latticeCharacter C hQ hR Λ wt hwt ν N z =
      ev (projectiveHomPolynomial _ N (((η').symm z) ν)) := rfl

omit [Finite I] in
private theorem projectiveHomPolynomial_smul (ν : Multiset I) (N : GFin (𝒜 ν)) (a : LP)
    (x : Kr ν) :
    projectiveHomPolynomial _ N (invRing a • x) = a * projectiveHomPolynomial _ N x := by
  have h := (projectiveCharacter _ N).map_smul (invRing a) x
  simp only [projectiveCharacter, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul] at h
  have h' := congrArg (LaurentPolynomial.invert (R := ℤ)) h
  have e := fun p : LP => LaurentPolynomial.involutive_invert p
  rw [e, map_mul, e] at h'
  rw [h']
  exact congrArg (· * _) (e a)

private theorem latticeCharacter_smul (ν : Multiset I) (N : GFin (𝒜 ν)) (a : LP) (x : TensorSpace wt)
    (hx : x ∈ (integralTensor wt).toAddSubgroup) :
    latticeCharacter C hQ hR Λ wt hwt ν N ⟨ev a • x, (isLattice_integralTensor C hR wt).smul_mem a hx⟩ =
      ev a • latticeCharacter C hQ hR Λ wt hwt ν N ⟨x, hx⟩ := by
  have hz : (⟨ev a • x, (isLattice_integralTensor C hR wt).smul_mem a hx⟩ :
      (integralTensor wt).toAddSubgroup) = (a • (⟨x, hx⟩ : integralTensor wt) : integralTensor wt) :=
    rfl
  rw [latticeCharacter_apply, latticeCharacter_apply, hz, LinearEquiv.map_smulₛₗ]
  change ev (projectiveHomPolynomial _ N (DirectSum.component LP _ Kr ν (invRing a • _))) = _
  rw [LinearMap.map_smul, projectiveHomPolynomial_smul, map_mul, smul_eq_mul]
  rfl

/-- **The class of a finite-dimensional graded right module as a functional** on `V_λ`
(Webster, arXiv:1309.3796v2, Theorem 4.38 and Corollary 6.10): the `ℚ(v)`-linear functional
whose value at `η x` is `gdim HOM(x, N)` at `q = v`. -/
def classFunctional (ν : Multiset I) (N : GFin (𝒜 ν)) : TensorSpace wt →ₗ[𝕂] 𝕂 :=
  Lattice.extend (isLattice_integralTensor C hR wt) (latticeCharacter C hQ hR Λ wt hwt ν N)
    (latticeCharacter_smul C hQ hR Λ wt hwt ν N)

/-- The class functional at a virtual projective class. -/
theorem classFunctional_eta (ν : Multiset I) (N : GFin (𝒜 ν)) (x : Mr) :
    classFunctional C hQ hR Λ wt hwt ν N (η' x) = ev (projectiveHomPolynomial _ N (x ν)) := by
  rw [classFunctional, Lattice.extend_apply _ _ _ (η' x).2]
  change ev (projectiveHomPolynomial _ N (((η').symm (η' x)) ν)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The class functional at a graded projective: `gdim HOM(P, N)` at `q = v`. -/
theorem classFunctional_of (ν : Multiset I) (N : GFin (𝒜 ν)) (P : GProj (𝒜 ν)) :
    classFunctional C hQ hR Λ wt hwt ν N (η' (DirectSum.lof LP _ Kr ν (K0.of P))) =
      ev (gdimPoly (homGrade (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ P.grading N.grading)) := by
  rw [classFunctional_eta, DirectSum.lof_apply, projectiveHomPolynomial_of]

/-- Class functionals are additive in short exact sequences. -/
theorem classFunctional_eq_of_shortExact (ν : Multiset I) {N N' N'' : GFin (𝒜 ν)}
    (S : GFin.ShortExact N N' N'') :
    classFunctional C hQ hR Λ wt hwt ν N' =
      classFunctional C hQ hR Λ wt hwt ν N + classFunctional C hQ hR Λ wt hwt ν N'' := by
  refine Lattice.ext_of_lattice (isLattice_integralTensor C hR wt) fun z hz ↦ ?_
  obtain ⟨x, hx⟩ := (η').surjective ⟨z, hz⟩
  have hzx : z = (η' x : TensorSpace wt) := by rw [hx]
  rw [hzx, LinearMap.add_apply, classFunctional_eta, classFunctional_eta, classFunctional_eta,
    ← map_add]
  congr 1
  apply toLaurentSeries_injective
  rw [map_add, toLaurentSeries_projectiveHomPolynomial, toLaurentSeries_projectiveHomPolynomial,
    toLaurentSeries_projectiveHomPolynomial, pairingRight_hses S, AddMonoidHom.add_apply]

omit [Finite I] in
/-- The Laurent expansion of `p(v)` is `p` read in `ℚ((q))`. -/
theorem series_eval (p : LP) : series (ev p) = lsCast (toLaurentSeries p) := by
  rw [lsCast_toLaurentSeries, vToLS, RingHom.comp_apply, barQ_qToV, ← CycKLR.integralEval_invert,
    LaurentPolynomial.involutive_invert]

private local instance blockGdimOp (ν : Multiset I) : HasGdim (𝒜 ν) :=
  HasGdim.of_finiteDimensional _

omit [Finite I] in
private theorem rightHomForm_lof_right (ν : Multiset I) (P : GProj (𝒜 ν)) (x : Mr) :
    rightTensorProjectiveHomForm C hQ Λ x (DirectSum.lof LP _ Kr ν (K0.of P)) =
      K0.homForm _ (x ν) (K0.of P) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, AddMonoidHom.add_apply, hx, hy, DirectSum.add_apply, map_add,
      AddMonoidHom.add_apply]
  | of ν' x =>
    unfold rightTensorProjectiveHomForm
    rw [DirectSum.toAddMonoid_of]
    by_cases h : ν' = ν
    · subst h
      simp [DirectSum.lof_eq_of, ← DirectSum.apply_eq_component]
    · simp [DirectSum.lof_eq_of, ← DirectSum.apply_eq_component, DirectSum.of_eq_of_ne, h,
        Ne.symm h]

omit [Finite I] in
private theorem homForm_eq_pairingRight (ν : Multiset I) (P : GProj (𝒜 ν)) (x : Kr ν) :
    K0.homForm _ x (K0.of P) = pairingRight P.toGFin x := by
  induction x using K0.induction_on with
  | of P' => rw [K0.homForm_of, pairingRight_of]; rfl
  | zero => simp
  | add x y hx hy => rw [map_add, AddMonoidHom.add_apply, hx, hy, map_add]
  | neg x hx => rw [map_neg, AddMonoidHom.neg_apply, hx, map_neg]

/-- **The class functional of a projective is the form against its class** (Webster,
arXiv:1309.3796v2, Theorem 4.38 and Lemma 4.36): `classFunctional P = B(η [P], -)`. -/
theorem classFunctional_projective (ν : Multiset I) (P : GProj (𝒜 ν)) :
    classFunctional C hQ hR Λ wt hwt ν P.toGFin = B (η' (DirectSum.lof LP _ Kr ν (K0.of P))) := by
  refine Lattice.ext_of_lattice (isLattice_integralTensor C hR wt) fun z hz ↦ ?_
  obtain ⟨x, hx⟩ := (η').surjective ⟨z, hz⟩
  have hzx : z = (η' x : TensorSpace wt) := by rw [hx]
  rw [hzx, classFunctional_eta]
  apply (algebraMap 𝕂 (LaurentSeries ℚ)).injective
  rw [series_eval, toLaurentSeries_projectiveHomPolynomial, ← rightTensorModuleEquiv_homForm,
    rightHomForm_lof_right, homForm_eq_pairingRight]

end Categorification.Stendhal.FirstWeight
