/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.ExtTensorK0Equiv
import Categorification.KLR.Cor319

/-!
# `K₀(R(ν) ⊗ R(ν')) ≅ K₀(R(ν)) ⊗_{ℤ[q,q⁻¹]} K₀(R(ν'))`

Khovanov–Lauda I (arXiv:0803.4121v2), §3.1 (TeX lines ~1890–1900): "`K₀(R(ν) ⊗ R(ν'))` is
isomorphic to `K₀(R(ν)) ⊗ K₀(R(ν'))`", the isomorphism taking `[Y] ⊗ [Y']` to `[Y ⊗ Y']`. We
verify the hypotheses of the general identification (`Graded.TensorK0Hyp`,
`Categorification.KLR.ExtTensorK0Equiv`) for KLR algebras over a field, in the generality of the
basis theorem (`hPQ`, `hP`) with all dots of positive degree (`hG`):

* the graded simple `R(ν)`-modules are finite-dimensional (KL I, Proposition 2.12) and absolutely
  irreducible, `End(S) = k` (KL I, Corollary 3.19, `KLRAlgebra.exists_eq_smul_of_isSimpleModule`);
* **the graded simple `R(ν) ⊗ R(ν')`-modules are finite-dimensional**
  (`GradingDatum.finiteDimensional_of_isGradedSimple_tensor`): `Sym⁺(ν) ⊗ 1` and `1 ⊗ Sym⁺(ν')`
  are central of positive degree, hence act by zero (graded Nakayama), and
  `R'(ν) ⊗ R'(ν')` is finite-dimensional.

## Main results

* `GradingDatum.tensorK0Hyp` : the hypotheses hold for `R(ν)`, `R(ν')`.
* `GradingDatum.k0TensorEquiv` : **`K₀(R(ν)) ⊗_{ℤ[q,q⁻¹]} K₀(R(ν')) ≅ K₀(R(ν) ⊗ R(ν'))`**,
  `x ⊗ y ↦ x ⊠ y` (`k0TensorEquiv_tmul`).
* `GradingDatum.nonempty_iso_extTensor_rep`, `GradingDatum.isIndec_extTensor_rep` : the
  indecomposable graded projective `R(ν) ⊗ R(ν')`-modules are exactly the `P_b ⊠ P_{b'}`, up to
  isomorphism and grading shift.
-/

noncomputable section

namespace Categorification

open Graded GProj DirectSum MvPolynomial
open scoped TensorProduct

namespace Graded

/-- A graded algebra with a graded dimension vanishes in sufficiently negative degrees. -/
theorem exists_grade_eq_bot_of_hasGdim {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (ℳ : ℤ → Submodule k M) [HasGdim ℳ] : ∃ N : ℤ, ∀ n < N, ℳ n = ⊥ := by
  obtain ⟨N, hN⟩ := HasGdim.bddBelow (ℳ := ℳ)
  exact ⟨N, fun n hn => by
    by_contra h
    exact absurd (hN h) (not_le.2 hn)⟩

end Graded

namespace KLR

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (G : GradingDatum Q) (hG : ∀ a, 0 < G.degX a)

namespace GradingDatum

open KLRAlgebra PolyRep

section Simple

variable {ν ν' : Multiset I} {U : Type*} [AddCommGroup U] [Module k U]
  [Module (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') U]
  [IsScalarTower k (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') U] {𝒰 : ℤ → Submodule k U}
  [Decomposition 𝒰] [SetLike.GradedSMul (tensorGrading (G.grade ν) (G.grade ν')) 𝒰]

omit [IsScalarTower k (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') U] in
include hPQ hP hG in
/-- `Sym⁺(ν) ⊗ 1` acts by zero on a graded simple `R(ν) ⊗ R(ν')`-module. -/
theorem polNu_tmul_one_smul_eq_zero
    (hU : IsGradedSimple (tensorGrading (G.grade ν) (G.grade ν')) 𝒰) {f : symNu k ν}
    (hf : f ∈ symNuPlus k ν) (u : U) :
    ((polNu (f : Pol k ν) : KLRAlgebra k Q ν) ⊗ₜ[k] (1 : KLRAlgebra k Q ν')) • u = 0 := by
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  haveI := G.hasGdim_grade' (ν := ν') hPQ hP hG
  obtain ⟨N, hN⟩ := exists_grade_eq_bot_of_hasGdim (tensorGrading (G.grade ν) (G.grade ν'))
  set z : KLRAlgebra k Q ν := polNu (f : Pol k ν)
  have hz : ∀ a : KLRAlgebra k Q ν, Commute z a := fun a =>
    ((Subalgebra.mem_center_iff.1 (KLRAlgebra.polNu_mem_center hPQ hP f.2)) a).symm
  have hc : ∀ t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν', Commute (z ⊗ₜ[k] 1) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact Commute.zero_right _
    | tmul a b =>
      show (z ⊗ₜ[k] (1 : KLRAlgebra k Q ν')) * (a ⊗ₜ[k] b) = (a ⊗ₜ[k] b) * (z ⊗ₜ[k] 1)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        mul_one, (hz a).eq]
    | add s t hs ht => exact hs.add_right ht
  let L : KLRAlgebra k Q ν →ₗ[k] KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν' :=
    (TensorProduct.mk k _ _).flip 1
  have hL : PreservesGrading (G.grade ν) (tensorGrading (G.grade ν) (G.grade ν')) L :=
    fun d a ha => by
      have := tmul_mem_tensorGrading (k := k) ha (SetLike.GradedOne.one_mem :
        (1 : KLRAlgebra k Q ν') ∈ G.grade ν' 0)
      rwa [add_zero] at this
  have hpos : ∀ d ≤ 0, (decompose (tensorGrading (G.grade ν) (G.grade ν')) (z ⊗ₜ[k] 1) d :
      KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') = 0 := fun d hd => by
    have := decompose_map hL z d
    rw [show L z = z ⊗ₜ[k] 1 from rfl] at this
    rw [this, decompose_polNu_eq_zero G hG ((mem_symNuPlus_iff).1 hf) hd, map_zero]
  exact hU.smul_eq_zero_of_commute hN hc hpos u

omit [IsScalarTower k (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') U] in
include hPQ hP hG in
/-- `1 ⊗ Sym⁺(ν')` acts by zero on a graded simple `R(ν) ⊗ R(ν')`-module. -/
theorem one_tmul_polNu_smul_eq_zero
    (hU : IsGradedSimple (tensorGrading (G.grade ν) (G.grade ν')) 𝒰) {f : symNu k ν'}
    (hf : f ∈ symNuPlus k ν') (u : U) :
    ((1 : KLRAlgebra k Q ν) ⊗ₜ[k] (polNu (f : Pol k ν') : KLRAlgebra k Q ν')) • u = 0 := by
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  haveI := G.hasGdim_grade' (ν := ν') hPQ hP hG
  obtain ⟨N, hN⟩ := exists_grade_eq_bot_of_hasGdim (tensorGrading (G.grade ν) (G.grade ν'))
  set z : KLRAlgebra k Q ν' := polNu (f : Pol k ν')
  have hz : ∀ a : KLRAlgebra k Q ν', Commute z a := fun a =>
    ((Subalgebra.mem_center_iff.1 (KLRAlgebra.polNu_mem_center hPQ hP f.2)) a).symm
  have hc : ∀ t : KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν', Commute (1 ⊗ₜ[k] z) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact Commute.zero_right _
    | tmul a b =>
      show ((1 : KLRAlgebra k Q ν) ⊗ₜ[k] z) * (a ⊗ₜ[k] b) = (a ⊗ₜ[k] b) * (1 ⊗ₜ[k] z)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        mul_one, (hz b).eq]
    | add s t hs ht => exact hs.add_right ht
  let L : KLRAlgebra k Q ν' →ₗ[k] KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν' :=
    TensorProduct.mk k _ _ 1
  have hL : PreservesGrading (G.grade ν') (tensorGrading (G.grade ν) (G.grade ν')) L :=
    fun d b hb => by
      have := tmul_mem_tensorGrading (k := k) (SetLike.GradedOne.one_mem :
        (1 : KLRAlgebra k Q ν) ∈ G.grade ν 0) hb
      rwa [zero_add] at this
  have hpos : ∀ d ≤ 0, (decompose (tensorGrading (G.grade ν) (G.grade ν')) (1 ⊗ₜ[k] z) d :
      KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') = 0 := fun d hd => by
    have := decompose_map hL z d
    rw [show L z = 1 ⊗ₜ[k] z from rfl] at this
    rw [this, decompose_polNu_eq_zero G hG ((mem_symNuPlus_iff).1 hf) hd, map_zero]
  exact hU.smul_eq_zero_of_commute hN hc hpos u

include hPQ hP hG in
/-- **Graded simple `R(ν) ⊗ R(ν')`-modules are finite-dimensional**: they are killed by
`Sym⁺(ν) ⊗ R(ν') + R(ν) ⊗ Sym⁺(ν')`, hence are quotients of `R'(ν) ⊗ R'(ν')`. -/
theorem finiteDimensional_of_isGradedSimple_tensor
    (hU : IsGradedSimple (tensorGrading (G.grade ν) (G.grade ν')) 𝒰) : FiniteDimensional k U := by
  haveI := hU.nontrivial
  obtain ⟨j, v, hv, hv0⟩ := exists_mem_ne_zero 𝒰
  set I₁ := (KLRAlgebra.symPlusIdeal k Q ν).restrictScalars k
  set I₂ := (KLRAlgebra.symPlusIdeal k Q ν').restrictScalars k
  haveI : FiniteDimensional k (KLRAlgebra k Q ν ⧸ I₁) :=
    KLRAlgebra.finiteDimensional_quotient_symPlusIdeal_restrictScalars hPQ hP
  haveI : FiniteDimensional k (KLRAlgebra k Q ν' ⧸ I₂) :=
    KLRAlgebra.finiteDimensional_quotient_symPlusIdeal_restrictScalars hPQ hP
  have hL : ∀ a ∈ KLRAlgebra.symPlusIdeal k Q ν, ∀ b : KLRAlgebra k Q ν',
      (a ⊗ₜ[k] b) • v = 0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      intro b
      rw [show (polNu (f : Pol k ν) : KLRAlgebra k Q ν) ⊗ₜ[k] b =
          ((1 : KLRAlgebra k Q ν) ⊗ₜ[k] b) * (polNu (f : Pol k ν) ⊗ₜ[k] 1) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one], mul_smul,
        polNu_tmul_one_smul_eq_zero hPQ hP G hG hU hf, smul_zero]
    | zero => intro b; rw [TensorProduct.zero_tmul, zero_smul]
    | add y z _ _ hy hz => intro b; rw [TensorProduct.add_tmul, add_smul, hy, hz, add_zero]
    | smul r y _ hy =>
      intro b
      rw [smul_eq_mul, show (r * y) ⊗ₜ[k] b = (r ⊗ₜ[k] (1 : KLRAlgebra k Q ν')) * (y ⊗ₜ[k] b) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], mul_smul, hy, smul_zero]
  have hR : ∀ b ∈ KLRAlgebra.symPlusIdeal k Q ν', ∀ a : KLRAlgebra k Q ν,
      (a ⊗ₜ[k] b) • v = 0 := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, rfl⟩ := hy
      intro a
      rw [show a ⊗ₜ[k] (polNu (f : Pol k ν') : KLRAlgebra k Q ν') =
          (a ⊗ₜ[k] (1 : KLRAlgebra k Q ν')) * (1 ⊗ₜ[k] polNu (f : Pol k ν')) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one], mul_smul,
        one_tmul_polNu_smul_eq_zero hPQ hP G hG hU hf, smul_zero]
    | zero => intro a; rw [TensorProduct.tmul_zero, zero_smul]
    | add y z _ _ hy hz => intro a; rw [TensorProduct.tmul_add, add_smul, hy, hz, add_zero]
    | smul r y _ hy =>
      intro a
      rw [smul_eq_mul, show a ⊗ₜ[k] (r * y) = ((1 : KLRAlgebra k Q ν) ⊗ₜ[k] r) * (a ⊗ₜ[k] y) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], mul_smul, hy, smul_zero]
  -- the map `R'(ν) ⊗ R'(ν') → U`, `ā ⊗ b̄ ↦ (a ⊗ b) v`
  let β : KLRAlgebra k Q ν →ₗ[k] KLRAlgebra k Q ν' →ₗ[k] U :=
    LinearMap.mk₂ k (fun a b => (a ⊗ₜ[k] b) • v)
      (fun a a' b => by beta_reduce; rw [TensorProduct.add_tmul, add_smul])
      (fun c a b => by beta_reduce; rw [← TensorProduct.smul_tmul', smul_assoc])
      (fun a b b' => by beta_reduce; rw [TensorProduct.tmul_add, add_smul])
      (fun c a b => by beta_reduce; rw [TensorProduct.tmul_smul, smul_assoc])
  have hβ : ∀ a, I₂ ≤ LinearMap.ker (β a) := fun a b hb => hR b hb a
  let β' : KLRAlgebra k Q ν →ₗ[k] (KLRAlgebra k Q ν' ⧸ I₂) →ₗ[k] U :=
    { toFun := fun a => I₂.liftQ (β a) (hβ a)
      map_add' := fun a a' => Submodule.linearMap_qext _ (by
        ext b
        simp [map_add])
      map_smul' := fun c a => Submodule.linearMap_qext _ (by
        ext b
        simp [map_smul]) }
  have hβ' : I₁ ≤ LinearMap.ker β' := fun a ha => Submodule.linearMap_qext _ (by
    ext b
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      LinearMap.zero_comp, LinearMap.zero_apply]
    show β a b = 0
    exact hL a ha b)
  let Ψ : (KLRAlgebra k Q ν ⧸ I₁) ⊗[k] (KLRAlgebra k Q ν' ⧸ I₂) →ₗ[k] U :=
    TensorProduct.lift (I₁.liftQ β' hβ')
  have hΨ : ∀ (a : KLRAlgebra k Q ν) (b : KLRAlgebra k Q ν'),
      Ψ (Submodule.Quotient.mk a ⊗ₜ Submodule.Quotient.mk b) = (a ⊗ₜ[k] b) • v := fun _ _ => rfl
  refine Module.Finite.of_surjective Ψ fun u => ?_
  have hu : u ∈ Submodule.span (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') {v} := by
    rw [hU.span_singleton_eq_top hv hv0]; trivial
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hu
  clear hu
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, zero_smul]⟩
  | tmul a b => exact ⟨_, hΨ a b⟩
  | add s t hs ht =>
    obtain ⟨x, hx⟩ := hs
    obtain ⟨y, hy⟩ := ht
    exact ⟨x + y, by rw [map_add, hx, hy, add_smul]⟩

end Simple

variable (ν ν' : Multiset I)

include hPQ hP hG in
/-- **The hypotheses of `K₀(A ⊗ B) ≅ K₀(A) ⊗ K₀(B)` hold for KLR algebras** (KL I,
Proposition 2.12 and Corollary 3.19, and `finiteDimensional_of_isGradedSimple_tensor`). -/
theorem tensorK0Hyp : TensorK0Hyp (G.grade ν) (G.grade ν') where
  fdA b := G.finiteDimensional_top hPQ hP hG ν b
  fdB b := G.finiteDimensional_top hPQ hP hG ν' b
  endA b f := by
    obtain ⟨-, -, hnil⟩ := KLRAlgebra.crystal_hypotheses_of_isGradedSimple G hG b.top.grading
      hPQ hP (IndecClass.isGradedSimple_top b)
    haveI := G.finiteDimensional_top hPQ hP hG ν b
    haveI := KLRAlgebra.isSimpleModule_of_isGradedSimple hPQ hP G hG b.top.grading
      (IndecClass.isGradedSimple_top b)
    obtain ⟨c, hc⟩ := KLRAlgebra.exists_eq_smul_of_isSimpleModule hPQ hP hnil f
    exact ⟨c, LinearMap.ext hc⟩
  endB b f := by
    obtain ⟨-, -, hnil⟩ := KLRAlgebra.crystal_hypotheses_of_isGradedSimple G hG b.top.grading
      hPQ hP (IndecClass.isGradedSimple_top b)
    haveI := G.finiteDimensional_top hPQ hP hG ν' b
    haveI := KLRAlgebra.isSimpleModule_of_isGradedSimple hPQ hP G hG b.top.grading
      (IndecClass.isGradedSimple_top b)
    obtain ⟨c, hc⟩ := KLRAlgebra.exists_eq_smul_of_isSimpleModule hPQ hP hnil f
    exact ⟨c, LinearMap.ext hc⟩
  fdC c := finiteDimensional_of_isGradedSimple_tensor hPQ hP G hG (IndecClass.isGradedSimple_top c)

/-- **KL I, §3.1: `K₀(R(ν)) ⊗_{ℤ[q,q⁻¹]} K₀(R(ν')) ≅ K₀(R(ν) ⊗ R(ν'))`**, `x ⊗ y ↦ x ⊠ y`. -/
def k0TensorEquiv :
    K0 (G.grade ν) ⊗[LaurentPolynomial ℤ] K0 (G.grade ν') ≃ₗ[LaurentPolynomial ℤ]
      K0 (tensorGrading (G.grade ν) (G.grade ν')) :=
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  haveI := G.hasGdim_grade' (ν := ν') hPQ hP hG
  (G.tensorK0Hyp hPQ hP hG ν ν').extTensorEquiv

@[simp] theorem k0TensorEquiv_tmul (x : K0 (G.grade ν)) (y : K0 (G.grade ν')) :
    G.k0TensorEquiv hPQ hP hG ν ν' (x ⊗ₜ y) = K0.extTensor (G.grade ν) (G.grade ν') x y := by
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  haveI := G.hasGdim_grade' (ν := ν') hPQ hP hG
  exact (G.tensorK0Hyp hPQ hP hG ν ν').extTensorEquiv_tmul x y

theorem k0TensorEquiv_symm_extTensor (x : K0 (G.grade ν)) (y : K0 (G.grade ν')) :
    (G.k0TensorEquiv hPQ hP hG ν ν').symm (K0.extTensor (G.grade ν) (G.grade ν') x y) = x ⊗ₜ y := by
  rw [LinearEquiv.symm_apply_eq, k0TensorEquiv_tmul]

include hPQ hP hG in
/-- **The indecomposable graded projective `R(ν) ⊗ R(ν')`-modules are the `P_b ⊠ P_{b'}`**, up to
isomorphism and grading shift. -/
theorem nonempty_iso_extTensor_rep
    (c : IndecClass (tensorGrading (G.grade ν) (G.grade ν'))) :
    ∃ (b : IndecClass (G.grade ν)) (b' : IndecClass (G.grade ν')) (a : ℤ),
      Nonempty (c.rep.Iso ((b.rep.extTensor b'.rep).shift a)) := by
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  haveI := G.hasGdim_grade' (ν := ν') hPQ hP hG
  set H := G.tensorK0Hyp hPQ hP hG ν ν'
  exact ⟨H.fst c, H.snd c, H.shift c, H.nonempty_iso_rep c⟩

include hPQ hP hG in
/-- **`P_b ⊠ P_{b'}` is indecomposable** for indecomposable graded projectives `P_b`, `P_{b'}`
of `R(ν)`, `R(ν')` (absolute indecomposability). -/
theorem isIndec_extTensor_rep (b : IndecClass (G.grade ν)) (b' : IndecClass (G.grade ν')) :
    (b.rep.extTensor b'.rep).IsIndec (KLRAlgebra k Q ν ⊗[k] KLRAlgebra k Q ν') := by
  haveI := G.hasGdim_grade' (ν := ν) hPQ hP hG
  haveI := G.hasGdim_grade' (ν := ν') hPQ hP hG
  exact (G.tensorK0Hyp hPQ hP hG ν ν').isIndec_extTensor_rep b b'

end GradingDatum

end KLR

end Categorification
