/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidAppendClass
import Categorification.WeightedKLR.RedStrands.TensorClassLowering
import Categorification.Algebra.Graded.InduceProdShift

/-!
# The braid functor on classes

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
Corollary 6.10. The braid functor `𝔅_σ` (`braidFunctor`) sends a graded right projective
`T^λ`-module `P` to a finite-dimensional graded right `T^{λ ∘ σ}`-module, whose class is a
functional on `V_{λ ∘ σ}` (`classFunctional`). This functional depends only on the class of `P`
in `K₀` (`braidClass`), and is semilinear along the bar involution for the grading shift.

## Main results

* `classFunctional_shift`, `classFunctional_prod` : class functionals of shifts and direct sums.
* `braidClass ν` : `[P] ↦ classFunctional (𝔅_σ P)` on `K₀`.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF MulOpposite Equiv
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "𝕂" => RatFunc ℚ
local notation "ev" => integralLaurentEval
local notation "v" => (RatFunc.X : 𝕂)

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "Kr" => rightTensorProjectiveGroup C hQ Λ
local notation "η'" => rightTensorModuleEquiv C hQ hR Λ wt hwt
local notation "𝒜" ν => oppositeGrade (tensorProductGrade G ν)
local notation "cf" => classFunctional C hQ hR Λ wt hwt
local notation "rseq" => rightSequenceProj G
local notation "Mr" => DirectSum (Multiset I) (rightTensorProjectiveGroup C hQ Λ)

/- Finiteness of `T^λ` in each red order and black content (`tensorProductAlgebra_finite`) is taken
as an instance argument; it always holds for Rouquier parameters over a field. A single instance for
all red orders keeps instance search from comparing `λ` with `λ ∘ σ`. -/
variable [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]

private abbrev invRing : LP ≃+* LP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair invRing.toRingHom invRing.toRingHom :=
  RingHomInvPair.of_ringEquiv invRing
local instance : NeZero (RatFunc.X : 𝕂) := ⟨RatFunc.X_ne_zero⟩

/-! ### Shifts and direct sums -/

/-- The class functional of a shift: `classFunctional (N{a}) = v^a classFunctional N`. -/
theorem classFunctional_shift (ν : Multiset I) (N : GFin (𝒜 ν)) (a : ℤ) :
    cf ν (N.shift a) = ev (LaurentPolynomial.T a) • cf ν N := by
  refine Lattice.ext_of_lattice (isLattice_integralTensor C hR wt) fun z hz ↦ ?_
  obtain ⟨x, hx⟩ := (η').surjective ⟨z, hz⟩
  have hzx : z = (η' x : TensorSpace wt) := by rw [hx]
  rw [hzx, LinearMap.smul_apply, classFunctional_eta, classFunctional_eta,
    projectiveHomPolynomial_shift, map_mul, smul_eq_mul]

/-- The class functional of a direct sum is the sum. -/
theorem classFunctional_prod (ν : Multiset I) (N N' : GFin (𝒜 ν)) :
    cf ν (N.prod N') = cf ν N + cf ν N' :=
  classFunctional_eq_of_shortExact C hQ hR Λ wt hwt ν (GFin.ShortExact.prod N N')

/-! ### Bar-twisted duals -/

/-- `ℚ(v)`-linear functionals on `M`, with `ℚ(v)` acting through the bar involution. -/
def ConjDual (M : Type*) [AddCommGroup M] [Module 𝕂 M] : Type _ := M →ₗ[𝕂] 𝕂

namespace ConjDual

variable {M : Type*} [AddCommGroup M] [Module 𝕂 M]

instance : AddCommGroup (ConjDual M) := inferInstanceAs (AddCommGroup (M →ₗ[𝕂] 𝕂))

instance : Module 𝕂 (ConjDual M) := Module.compHom (M →ₗ[𝕂] 𝕂) barRingHom

/-- A functional, as an element of the bar-twisted dual. -/
def of : (M →ₗ[𝕂] 𝕂) ≃+ ConjDual M := AddEquiv.refl _

theorem smul_of (c : 𝕂) (f : M →ₗ[𝕂] 𝕂) : c • of f = of (barRingHom c • f) := rfl

/-- `ξ ↦ ξ ∘ g` on the bar-twisted dual. -/
def precomp (g : M →ₗ[𝕂] M) : ConjDual M →ₗ[𝕂] ConjDual M where
  toFun ξ := of ((of.symm ξ).comp g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem precomp_of (g : M →ₗ[𝕂] M) (f : M →ₗ[𝕂] 𝕂) : precomp g (of f) = of (f.comp g) := rfl

/-- Evaluation at a vector, a bar-semilinear functional on the bar-twisted dual. -/
def eval (w : M) : ConjDual M →ₛₗ[barRingHom] 𝕂 where
  toFun ξ := of.symm ξ w
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem eval_of (w : M) (f : M →ₗ[𝕂] 𝕂) : eval w (of f) = f w := rfl

theorem ext {ξ ξ' : ConjDual M} (h : ∀ w, eval w ξ = eval w ξ') : ξ = ξ' :=
  LinearMap.ext h

end ConjDual

/-! ### The braid functor on `K₀` -/

section BraidClass

variable (σ : Perm (Fin ℓ))

/-- The canonical reduced word of each permutation of the strands in black content `ν`. -/
def canChoice (ℓ : ℕ) (ν : Multiset I) :
    Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ :=
  TypeA.canWord _

omit [DecidableEq I] [Finite I] [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)] in
theorem isReducedChoice_canChoice (ν : Multiset I) : TypeA.IsReducedChoice (canChoice ℓ ν) :=
  fun w => ⟨TypeA.isReduced_canWord _ w, TypeA.wordProd_canWord _ w⟩

local notation "𝒜σ" ν => oppositeGrade (tensorProductGrade
  (stendhalGradingDatum (Λ ∘ σ) hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)) ν)
local notation "𝒜σr" ν => oppositeGrade (tensorProductGrade
  (BraidedStendhalAlgebra.rouquierGrading Q hQ (Λ ∘ σ)) ν)
local notation "𝒜r" ν => oppositeGrade (tensorProductGrade
  (BraidedStendhalAlgebra.rouquierGrading Q hQ Λ) ν)


/-- The braid functor `𝔅_σ` (Webster, arXiv:1309.3796v2, Definition 6.6), with the canonical
reduced words. -/
def braidF (ν : Multiset I) (N : GFin (𝒜 ν)) : GFin (𝒜σ ν) :=
  BraidedStendhalAlgebra.braidFunctor (Λ := Λ) (ν := ν) (isReducedChoice_canChoice ν)
    hQ.klrSymm σ hQ N

/-- `𝔅_σ (N ⊕ N') ≅ 𝔅_σ N ⊕ 𝔅_σ N'`. -/
def braidFProdIso (ν : Multiset I) (N N' : GFin (𝒜 ν)) :
    (braidF C hQ Λ σ ν (N.prod N')).Iso ((braidF C hQ Λ σ ν N).prod (braidF C hQ Λ σ ν N')) :=
  letI := BraidedStendhalAlgebra.braidBimodDecomposition (Λ := Λ) (ν := ν)
    (isReducedChoice_canChoice ν) hQ.klrSymm σ hQ
  letI := BraidedStendhalAlgebra.braidBimod_gradedSMul_left (Λ := Λ) (ν := ν)
    (isReducedChoice_canChoice ν) hQ.klrSymm σ hQ
  letI := BraidedStendhalAlgebra.braidBimod_gradedSMul_right (Λ := Λ) (ν := ν)
    (isReducedChoice_canChoice ν) hQ.klrSymm σ hQ
  letI := BraidedStendhalAlgebra.finite_braidBimod (Λ := Λ) (ν := ν)
    (isReducedChoice_canChoice ν) hQ.klrSymm σ
  GFin.induceProdIso (𝒜r ν) (𝒜σr ν)
    (BraidedStendhalAlgebra.braidBimodGrading Q Λ ν (isReducedChoice_canChoice ν) hQ.klrSymm σ hQ)
    N N'

/-- `𝔅_σ (N{a}) ≅ (𝔅_σ N){a}`. -/
def braidFShiftIso (ν : Multiset I) (N : GFin (𝒜 ν)) (a : ℤ) :
    (braidF C hQ Λ σ ν (N.shift a)).Iso ((braidF C hQ Λ σ ν N).shift a) :=
  letI := BraidedStendhalAlgebra.braidBimodDecomposition (Λ := Λ) (ν := ν)
    (isReducedChoice_canChoice ν) hQ.klrSymm σ hQ
  letI := BraidedStendhalAlgebra.braidBimod_gradedSMul_left (Λ := Λ) (ν := ν)
    (isReducedChoice_canChoice ν) hQ.klrSymm σ hQ
  letI := BraidedStendhalAlgebra.braidBimod_gradedSMul_right (Λ := Λ) (ν := ν)
    (isReducedChoice_canChoice ν) hQ.klrSymm σ hQ
  letI := BraidedStendhalAlgebra.finite_braidBimod (Λ := Λ) (ν := ν)
    (isReducedChoice_canChoice ν) hQ.klrSymm σ
  GFin.induceShiftIso (𝒜r ν) (𝒜σr ν)
    (BraidedStendhalAlgebra.braidBimodGrading Q Λ ν (isReducedChoice_canChoice ν) hQ.klrSymm σ hQ)
    N a



local notation "cf'" => classFunctional C hQ hR (Λ ∘ σ) (wt ∘ σ) (fun r i => hwt (σ r) i)

/-- **The braid functor on classes of projectives**: `[P] ↦ classFunctional (𝔅_σ P)`, a
functional on `V_{λ ∘ σ}` (Webster, arXiv:1309.3796v2, Corollary 6.10). -/
def braidClassK (ν : Multiset I) : Kr ν →+ ConjDual (TensorSpace (wt ∘ σ)) :=
  K0.lift (fun P => ConjDual.of (cf' ν (braidF C hQ Λ σ ν P.toGFin)))
    (fun _ _ e => congrArg _ (classFunctional_congr C hQ hR (Λ ∘ σ) (wt ∘ σ) (fun r i => hwt (σ r) i) ν
      (BraidedStendhalAlgebra.braidFunctorCongr _ _ σ hQ e)))
    (fun P P' => by
      rw [← map_add, ← classFunctional_prod C hQ hR (Λ ∘ σ) (wt ∘ σ) (fun r i => hwt (σ r) i) ν]
      exact congrArg _ (classFunctional_congr C hQ hR (Λ ∘ σ) (wt ∘ σ) (fun r i => hwt (σ r) i) ν
        (braidFProdIso C hQ Λ σ ν P.toGFin P'.toGFin)))

theorem braidClassK_of (ν : Multiset I) (P : GProj (𝒜 ν)) :
    braidClassK C hQ hR Λ wt hwt σ ν (K0.of P) =
      ConjDual.of (cf' ν (braidF C hQ Λ σ ν P.toGFin)) :=
  K0.lift_of _ _ _ P

theorem braidClassK_T (ν : Multiset I) (a : ℤ) (x : Kr ν) :
    braidClassK C hQ hR Λ wt hwt σ ν ((LaurentPolynomial.T a : LP) • x) =
      ev (LaurentPolynomial.T (-a)) • braidClassK C hQ hR Λ wt hwt σ ν x := by
  induction x using K0.induction_on with
  | of P =>
    rw [K0.T_smul_of, braidClassK_of, braidClassK_of, ConjDual.smul_of]
    congr 1
    have e : (braidF C hQ Λ σ ν (P.shift a).toGFin).Iso ((braidF C hQ Λ σ ν P.toGFin).shift a) :=
      braidFShiftIso C hQ Λ σ ν P.toGFin a
    rw [classFunctional_congr C hQ hR (Λ ∘ σ) (wt ∘ σ) (fun r i => hwt (σ r) i) ν e, classFunctional_shift]
    congr 1
    change _ = RatFunc.bar _
    rw [bar_integralLaurentEval, LaurentPolynomial.invert_T, neg_neg]
  | zero => simp
  | add _ _ hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | neg _ hx => rw [smul_neg, map_neg, map_neg, hx, smul_neg]

/-- `[P] ↦ classFunctional (𝔅_σ P)` is semilinear along the bar involution. -/
theorem braidClassK_smul (ν : Multiset I) (p : LP) (x : Kr ν) :
    braidClassK C hQ hR Λ wt hwt σ ν (p • x) =
      ev (LaurentPolynomial.invert p) • braidClassK C hQ hR Λ wt hwt σ ν x := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => rw [add_smul, map_add, hp, hq, map_add, map_add, add_smul]
  | single a m =>
    have he : (AddMonoidAlgebra.single a m : LP) = m • LaurentPolynomial.T a := by
      rw [LaurentPolynomial.T, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [he, smul_assoc, map_zsmul, braidClassK_T, map_zsmul, map_zsmul,
      LaurentPolynomial.invert_T, smul_assoc]

/-- The braid functor on the integral lattice of `V_λ`, through `η⁻¹`. -/
private def braidClassLattice :
    (integralTensor wt).toAddSubgroup →+ ConjDual (TensorSpace (wt ∘ σ)) :=
  (DirectSum.toAddMonoid fun ν => braidClassK C hQ hR Λ wt hwt σ ν).comp
    (η').symm.toAddEquiv.toAddMonoidHom

private theorem braidClassLattice_smul (a : LP) (x : TensorSpace wt)
    (hx : x ∈ (integralTensor wt).toAddSubgroup) :
    braidClassLattice C hQ hR Λ wt hwt σ ⟨ev a • x, (isLattice_integralTensor C hR wt).smul_mem a hx⟩ =
      ev a • braidClassLattice C hQ hR Λ wt hwt σ ⟨x, hx⟩ := by
  have hz : (⟨ev a • x, (isLattice_integralTensor C hR wt).smul_mem a hx⟩ :
      (integralTensor wt).toAddSubgroup) = (a • (⟨x, hx⟩ : integralTensor wt) : integralTensor wt) :=
    rfl
  change DirectSum.toAddMonoid _ ((η').symm _) = ev a • DirectSum.toAddMonoid _ ((η').symm _)
  rw [hz, LinearEquiv.map_smulₛₗ]
  generalize (η').symm ⟨x, hx⟩ = y
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y y' hy hy' => rw [smul_add, map_add, map_add, hy, hy', smul_add]
  | of ν y =>
    rw [← DirectSum.lof_eq_of LP, ← LinearMap.map_smul, DirectSum.lof_eq_of,
      DirectSum.lof_eq_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    change braidClassK C hQ hR Λ wt hwt σ ν (LaurentPolynomial.invert a • y) = _
    rw [braidClassK_smul, LaurentPolynomial.involutive_invert]

/-- **The braid functor on classes** (Webster, arXiv:1309.3796v2, Corollary 6.10): the
`ℚ(v)`-linear map `V_λ → V_{λ ∘ σ}^*` (bar-twisted dual) with `η [P] ↦ classFunctional (𝔅_σ P)`. -/
def braidClass : TensorSpace wt →ₗ[𝕂] ConjDual (TensorSpace (wt ∘ σ)) :=
  Lattice.extend (isLattice_integralTensor C hR wt) (braidClassLattice C hQ hR Λ wt hwt σ)
    (braidClassLattice_smul C hQ hR Λ wt hwt σ)

/-- `braidClass (η [P]) = classFunctional (𝔅_σ P)`. -/
theorem braidClass_of (ν : Multiset I) (P : GProj (𝒜 ν)) :
    braidClass C hQ hR Λ wt hwt σ (η' (DirectSum.lof LP _ Kr ν (K0.of P))) =
      ConjDual.of (cf' ν (braidF C hQ Λ σ ν P.toGFin)) := by
  rw [braidClass, Lattice.extend_apply _ _ _ (η' _).2]
  change DirectSum.toAddMonoid _ ((η').symm (η' _)) = _
  rw [LinearEquiv.symm_apply_apply, DirectSum.lof_eq_of, DirectSum.toAddMonoid_of,
    braidClassK_of]

/-! ### The class map commutes with `Fᵢ` -/

local notation "G'" => stendhalGradingDatum (Λ ∘ σ) hQ.gradingDatum (fun i => C.dot i i / 2)
  (dotDegree C hQ)
local notation "τF'" i => tensorRepresentation (wt ∘ σ) (barHom R (rho R v (F R v i)))

omit [Finite I] [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)] in
private theorem appendBlackOp_rightSequence (i : I) (γ : Multiset I)
    (s : Seq (stendhalWeight ℓ γ)) (hs : IsRedOrdered s) :
    appendBlackOp Q Λ i γ (op (TensorProductAlgebra.mk Q Λ γ (StendhalAlgebra.e s hs))) =
      op (TensorProductAlgebra.mk Q Λ (({i} : Multiset I) + γ) (StendhalAlgebra.e (appendBlackLoading i γ s)
        (appendBlackLoading_ordered i γ s hs))) :=
  (appendBlackOp_op Q Λ i γ _).trans (congrArg op (appendBlack_mk_e Q Λ i γ s hs))

omit [Finite I] [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)] in
private def ofIdempotentCongrIso {ν : Multiset I}
    {e e' : (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ} (h : e = e')
    (he : IsIdempotentElem e) (he0 : e ∈ (𝒜 ν) 0) (he' : IsIdempotentElem e')
    (he0' : e' ∈ (𝒜 ν) 0) :
    (GProj.ofIdempotent e he he0).toGFin.Iso (GProj.ofIdempotent e' he' he0').toGFin := by
  subst h
  exact GradedEquiv.refl _

/-- `Fᵢ (e(t) T^λ) ≅ e(t i) T^λ` as graded right modules (Webster, Lemma 4.37). -/
private def rightBlackIndRightSequenceIso (i : I) (γ : Multiset I) (t : Seq (stendhalWeight ℓ γ))
    (ht : IsRedOrdered t) :
    (rseq (appendBlackLoading i γ t) (appendBlackLoading_ordered i γ t ht)).toGFin.Iso
      (rightBlackInd G i γ (rseq t ht).toGFin) :=
  ((rightBlackIndPrincipalIso G i γ
    (e := op (TensorProductAlgebra.mk Q Λ γ (StendhalAlgebra.e t ht)))
    (congrArg op (isIdempotentElem_mk_e t ht)) (mk_e_mem_tensorProductGrade G γ t ht)).trans
    (ofIdempotentCongrIso C hQ Λ (appendBlackOp_rightSequence Λ i γ t ht) _ _ _ _)).symm

/-- **Graded Proposition 6.7 for `Fᵢ` on class functionals of projectives** (Webster,
arXiv:1309.3796v2, §6.1): `classFunctional (𝔅_σ Fᵢ (e(t) T^λ)) = classFunctional (Fᵢ 𝔅_σ (e(t) T^λ))`. -/
theorem classFunctional_braidF_rightBlackInd (i : I) (γ : Multiset I)
    (t : Seq (stendhalWeight ℓ γ)) (ht : IsRedOrdered t) :
    cf' (({i} : Multiset I) + γ) (braidF C hQ Λ σ (({i} : Multiset I) + γ) (rightBlackInd G i γ (rseq t ht).toGFin)) =
      cf' (({i} : Multiset I) + γ) (rightBlackInd G' i γ (braidF C hQ Λ σ γ (rseq t ht).toGFin)) := by
  rw [← sub_eq_zero]
  refine ext_rightSequence C hQ hR (Λ ∘ σ) (wt ∘ σ) (fun r i => hwt (σ r) i) _ fun β s hs => ?_
  rw [LinearMap.sub_apply, sub_eq_zero]
  by_cases h : β = {i} + γ
  · subst h
    rw [classFunctional_eta, classFunctional_eta, DirectSum.lof_apply]
    exact congrArg ev (BraidedStendhalAlgebra.projectiveHomPolynomial_rightBlackInd_braidFunctor
      (isReducedChoice_canChoice γ) (isReducedChoice_canChoice _) hQ.klrSymm σ hQ t ht s hs).symm
  · rw [classFunctional_lof_of_ne C hQ hR (Λ ∘ σ) (wt ∘ σ) (fun r i => hwt (σ r) i) _ _ h,
      classFunctional_lof_of_ne C hQ hR (Λ ∘ σ) (wt ∘ σ) (fun r i => hwt (σ r) i) _ _ h]

/-- **The class map of the braid functor commutes with `Fᵢ`** (Webster, arXiv:1309.3796v2,
proof of Corollary 6.10, from Proposition 6.7): `Fᵢ` acts on the bar-twisted dual of
`V_{λ ∘ σ}` through its adjoint `τ(Fᵢ)` for the form of Proposition 4.33. -/
theorem braidClass_F (i : I) (z : TensorSpace wt) :
    braidClass C hQ hR Λ wt hwt σ (tensorRepresentation wt (F R v i) z) =
      ConjDual.precomp (τF' i) (braidClass C hQ hR Λ wt hwt σ z) := by
  refine ConjDual.ext fun w => ?_
  have key : (ConjDual.eval w).comp ((braidClass C hQ hR Λ wt hwt σ).comp
      (tensorRepresentation wt (F R v i))) -
      (ConjDual.eval w).comp ((ConjDual.precomp (τF' i)).comp (braidClass C hQ hR Λ wt hwt σ)) =
      0 := by
    refine ext_rightSequence C hQ hR Λ wt hwt _ fun β t ht => ?_
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, sub_eq_zero]
    rw [F_rightSequence, braidClass_of, braidClass_of, ConjDual.precomp_of, ConjDual.eval_of,
      ConjDual.eval_of,
      ← classFunctional_rightBlackInd C hQ hR (Λ ∘ σ) (wt ∘ σ) (fun r i => hwt (σ r) i) i β,
      ← classFunctional_braidF_rightBlackInd]
    exact LinearMap.congr_fun (classFunctional_congr C hQ hR (Λ ∘ σ) (wt ∘ σ) (fun r i => hwt (σ r) i) _
      (BraidedStendhalAlgebra.braidFunctorCongr _ _ σ hQ
        (rightBlackIndRightSequenceIso C hQ Λ i β t ht))) w
  exact sub_eq_zero.1 (LinearMap.congr_fun key z)

end BraidClass

end Categorification.Stendhal.FirstWeight
