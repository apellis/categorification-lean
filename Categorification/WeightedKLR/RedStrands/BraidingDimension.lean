/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidingComposite

/-!
# Dimensions at `v = 1` from the braiding

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11, step `p_n → f_n`: the dimension of `𝔅_w P` equals the sum of the dimensions of
the standard modules indexing its filtration, because `𝔅_w` categorifies the braiding, which
at `q = 1` is the permutation of the tensor factors.

* `finrank_eq_evalOne_regular`: the dimension of a graded finite-dimensional module is the
  graded Hom dimension from the regular module at `q = 1`.
* `finrank_eq_evalOne_classFunctional`: hence it is read off the class functional, at the class
  of the regular module, at `v = 1`.
* `VOneCongr.zpow_smul`: rescaling by `v^d` keeps the congruence modulo `(v - 1)`.
* `finrank_eq_sum_of_vOneCongr`: if the class functional of `N` is `B(f a, -)` with `f`
  congruent at `v = 1` to `f'`, and `f' a` is a sum of shifted classes `z_c` of modules `S_c`,
  then `dim N = Σ_c dim S_c`.
-/

noncomputable section

open Module

namespace Categorification.Graded

universe u v
variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] [Module.Finite k A]
    (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- **The dimension of a graded module at `q = 1`**: `dim M` is the graded dimension of
`HOM(A, M)` at `q = 1`. -/
theorem finrank_eq_evalOne_regular (M : GFin 𝒜) :
    (finrank k M.carrier : ℤ) =
      evalOne (projectiveHomPolynomial 𝒜 M (K0.of (GProj.regular 𝒜))) := by
  rw [← K0.of_eq_of_iso GProj.ofIdempotentOneIso, projectiveHomPolynomial_ofIdempotent]
  let := idemDecomposition M.grading (SetLike.GradedOne.one_mem (A := 𝒜))
  rw [evalOne_gdimPoly]
  have htop : idemSubspace k M.carrier (1 : A) = ⊤ :=
    eq_top_iff.2 fun m _ => mem_idemSubspace.2 (one_smul A m)
  rw [(LinearEquiv.ofTop _ htop).finrank_eq]

end Categorification.Graded

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "𝕂" => RatFunc ℚ
local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "ev" => integralLaurentEval

/-! ### Rescaling -/

section Rescale

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y}
  {n n' : ℕ} {wt : Fin n → Dom R} {wt' : Fin n' → Dom R}

/-- Rescaling by a power of `v` keeps the congruence modulo `(v - 1)`. -/
theorem VOneCongr.zpow_smul {f f' : TensorSpace wt →ₗ[𝕂] TensorSpace wt'} (hf : VOneCongr f f')
    (d : ℤ) : VOneCongr ((𝕍 ^ d : 𝕂) • f) f' where
  left x hx := by
    have h := (integralTensor wt').smul_mem (LaurentPolynomial.T d : LP) (hf.left x hx)
    rwa [tensor_laurent_smul, integralLaurentEval_T] at h
  right := hf.right
  sub x hx := by
    obtain ⟨p, hp⟩ := exists_zpow_sub_one d
    rw [LinearMap.smul_apply, show (𝕍 ^ d : 𝕂) • f x - f' x =
        (f x - f' x) + (𝕍 - 1) • ((ev p) • f x) by
      rw [smul_smul, ← hp, sub_smul, one_smul]; abel]
    refine add_mem (hf.sub x hx) (sub_one_smul_mem_vOneTensor ?_)
    · have h := (integralTensor wt').smul_mem p (hf.left x hx)
      rwa [tensor_laurent_smul] at h

end Rescale

/-! ### Dimensions -/

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "Kr" => rightTensorProjectiveGroup C hQ Λ
local notation "η'" => rightTensorModuleEquiv C hQ hR Λ wt hwt
local notation "𝒜" ν => oppositeGrade (tensorProductGrade G ν)
local notation "cf" => classFunctional C hQ hR Λ wt hwt
local notation "B" => TensorPairing.orderedForm hR wt

variable [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]

/-- The class of the regular right module of `T^λ` in black content `ν`, in the integral
lattice of `V_λ`. -/
def regularTensor (ν : Multiset I) : TensorSpace wt :=
  η' (DirectSum.lof LP _ Kr ν (K0.of (GProj.regular (𝒜 ν))))

omit [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ] in
theorem regularTensor_mem (ν : Multiset I) :
    regularTensor C hQ hR Λ wt hwt ν ∈ integralTensor wt :=
  (η' _).2

private theorem list_sum_apply {M N : Type*} [AddCommMonoid M] [Module 𝕂 M] [AddCommMonoid N]
    [Module 𝕂 N] (l : List (M →ₗ[𝕂] N)) (x : M) : l.sum x = (l.map fun g => g x).sum := by
  induction l with
  | nil => simp
  | cons g l ih => rw [List.sum_cons, LinearMap.add_apply, ih, List.map_cons, List.sum_cons]

/-- **Dimensions from class functionals at `v = 1`**: the class functional of `N` at the class
of the regular module is `ev p` with `p(1) = dim N`. -/
theorem finrank_eq_evalOne_classFunctional (ν : Multiset I) (N : GFin (𝒜 ν)) :
    cf ν N (regularTensor C hQ hR Λ wt hwt ν) =
        ev (projectiveHomPolynomial _ N (K0.of (GProj.regular (𝒜 ν)))) ∧
      (finrank k N.carrier : ℤ) =
        evalOne (projectiveHomPolynomial _ N (K0.of (GProj.regular (𝒜 ν)))) :=
  ⟨by rw [regularTensor, classFunctional_eta, DirectSum.lof_apply],
    finrank_eq_evalOne_regular _ N⟩

include C hQ Λ hwt in
/-- **The dimension count at `v = 1`** (Webster, arXiv:1309.3796v2, proof of Lemma 6.11, step
`p_n → f_n`): let the class functional of `N` be `B(f a, -)` for a lattice vector `a` of
`V_μ`, with `f ≡ f'` modulo `(v - 1)`, and let `f' a = Σ_c v^{d_c} z_c`, where `z_c` is the
class of `S_c` (`classFunctional S_c = B(z_c, -)`). Then `dim N = Σ_c dim S_c`. -/
theorem finrank_eq_sum_of_vOneCongr {ℓ₀ : ℕ} {μ : Fin ℓ₀ → Dom R}
    {f f' : TensorSpace μ →ₗ[𝕂] TensorSpace wt} (hf : VOneCongr f f') {a : TensorSpace μ}
    (ha : a ∈ integralTensor μ) (ν : Multiset I) (N : GFin (𝒜 ν)) (hN : cf ν N = B (f a))
    {ι : Type*} (m : List ι) (S : ι → GFin (𝒜 ν)) (z : ι → TensorSpace wt) (d : ι → ℤ)
    (hS : ∀ c, cf ν (S c) = B (z c))
    (hfa : f' a = (m.map fun c => (𝕍 ^ d c : 𝕂) • z c).sum) :
    finrank k N.carrier = (m.map fun c => finrank k (S c).carrier).sum := by
  set b := regularTensor C hQ hR Λ wt hwt ν
  obtain ⟨p, q, hp, hq, hpq⟩ := orderedForm_evalOne_of_vOneCongr C hQ hR Λ wt hwt hf ha
    (regularTensor_mem C hQ hR Λ wt hwt ν)
  obtain ⟨hNb, hNd⟩ := finrank_eq_evalOne_classFunctional C hQ hR Λ wt hwt ν N
  have hpN : p = projectiveHomPolynomial _ N (K0.of (GProj.regular (𝒜 ν))) :=
    integralLaurentEval_injective (by rw [← hp, ← hNb, hN])
  have hqS : q = (m.map fun c => LaurentPolynomial.T (-d c) *
      projectiveHomPolynomial _ (S c) (K0.of (GProj.regular (𝒜 ν)))).sum := by
    apply integralLaurentEval_injective
    rw [← hq, hfa, map_list_sum, list_sum_apply, map_list_sum, List.map_map,
      List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply]
    rw [map_smulₛₗ, LinearMap.smul_apply, ← hS, (finrank_eq_evalOne_classFunctional C hQ hR Λ wt
      hwt ν (S c)).1, smul_eq_mul, map_mul, integralLaurentEval_T]
    congr 1
    rw [← integralLaurentEval_T]
    change RatFunc.bar _ = _
    rw [bar_integralLaurentEval, LaurentPolynomial.invert_T,
      integralLaurentEval_T]
  have hZ : (finrank k N.carrier : ℤ) = ((m.map fun c => finrank k (S c).carrier).sum : ℕ) := by
    rw [hNd, ← hpN, hpq, hqS, map_list_sum, List.map_map, Nat.cast_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply]
    rw [map_mul, ← (finrank_eq_evalOne_classFunctional C hQ hR Λ wt hwt ν (S c)).2]
    simp
  exact_mod_cast hZ

end Categorification.Stendhal.FirstWeight
