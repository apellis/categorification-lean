/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.TensorSimple
import Categorification.Algebra.Graded.KrullSchmidtUnique
import Categorification.KLR.ExtTensorK0

/-!
# `K₀(A ⊗ B) ≅ K₀(A) ⊗_{ℤ[q,q⁻¹]} K₀(B)`

Khovanov–Lauda I (arXiv:0803.4121v2), §3.1 (TeX lines ~1890–1900), identify
`K₀(R(ν) ⊗ R(ν'))` with `K₀(R(ν)) ⊗_{ℤ[q,q⁻¹]} K₀(R(ν'))`, `[Y ⊗ Y'] = [Y] ⊗ [Y']`, in order to
view `[Res]` as a map `K₀(R) → K₀(R) ⊗ K₀(R)`. This file proves the identification for general
`ℤ`-graded algebras over a field. (It sits in `KLR/` only because the map
`[P] ⊗ [P'] ↦ [P ⊠ P']` of `Categorification.KLR.ExtTensorK0` does.)

## Setting and hypotheses

`(A, 𝒜)`, `(B, ℬ)` are `ℤ`-graded algebras over a field `k` with finite-dimensional graded pieces
vanishing in sufficiently negative degrees (`HasGdim`). Write `P_b` for the indecomposable
finitely generated graded projectives (`GProj.IndecClass.rep`) and `S_b` for their graded simple
tops (`GProj.IndecClass.top`). We assume (`TensorK0Hyp`):

* the tops `S_b` of `A` and `B` are finite-dimensional;
* **absolute irreducibility**: every `A`-endomorphism of `S_b` is a scalar, and likewise for `B`
  (for `R(ν)` this is KL I, Corollary 3.19);
* the tops of the indecomposable graded projective `A ⊗ B`-modules are finite-dimensional.

All three hold for `A = R(ν)`, `B = R(ν')` (`Categorification.KLR.TensorKLRK0`).

## Main results

* `GProj.IsIndec.exists_iso_ofIdempotent` : every indecomposable graded projective is
  `A e {j}` for a degree-zero idempotent `e`; hence `K0.span_idemClasses`.
* `Graded.pairingRight_extTensor` (**product formula**):
  `gdim HOM(P ⊠ P', M ⊠ M') = gdim HOM(P, M) · gdim HOM(P', M')` on `K₀`, for finite-dimensional
  `M`, `M'`.
* `TensorK0Hyp.indecClassEquiv` : **the indecomposable graded projective `A ⊗ B`-modules are
  exactly the `P_b ⊠ P_{b'}`** (up to shift): a bijection `c ↦ (b, b')` with
  `P_c ≅ (P_b ⊠ P_{b'}){a_c}` (`TensorK0Hyp.nonempty_iso_rep`); in particular `P_b ⊠ P_{b'}` is
  indecomposable (`TensorK0Hyp.isIndec_extTensor_rep`) with top `S_b ⊠ S_{b'}`, which is graded
  simple (`TensorK0Hyp.isGradedSimple_extTensor_top`): **`P_b ⊠ P_{b'}` is the projective cover of
  `S_b ⊠ S_{b'}`** (`TensorK0Hyp.extTensor_rep_isCover`). The proof counts degree-zero
  homomorphisms into the graded simple `A ⊗ B`-modules, which are the `(S_b ⊠ S_{b'}){a}`
  (`TensorSimple.exists_gradedEquiv_extTensor_top`), using the product formula.
* `TensorK0Hyp.extTensorEquiv` : **the `ℤ[q, q⁻¹]`-linear isomorphism
  `K₀(A) ⊗_{ℤ[q,q⁻¹]} K₀(B) ≅ K₀(A ⊗ B)`**, `x ⊗ y ↦ x ⊠ y` (`extTensorEquiv_tmul`), sending the
  basis `[P_b] ⊗ [P_{b'}]` to the basis `q^{-a} [P_c]`.
-/

noncomputable section

universe u v

namespace Categorification.Graded

open DirectSum Module GProj
open scoped TensorProduct

variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}

/-! ### Indecomposable projectives are `A e {j}` -/

section IdemIndec

variable [GradedAlgebra 𝒜] [HasGdim 𝒜]

/-- **Every indecomposable graded projective is `A e {j}`** for a degree-zero idempotent `e`:
lifting `A{j} → S` (onto the top `S`) through `P → S` and back exhibits `P` as a graded direct
summand of `A{j}`, cut out by right multiplication by an idempotent of `A_0`. -/
theorem GProj.IsIndec.exists_iso_ofIdempotent {P : GProj 𝒜} (hP : P.IsIndec A) :
    ∃ (e : A) (he : IsIdempotentElem e) (he0 : e ∈ 𝒜 0) (j : ℤ),
      Nonempty (P.Iso ((GProj.ofIdempotent e he he0).shift j)) := by
  haveI := hP.nontrivial
  obtain ⟨S, t, hS, ht, ht0, -⟩ := P.exists_isGradedSimple_quotient
  haveI := hS.nontrivial
  obtain ⟨j, v, hv, hv0⟩ := exists_mem_ne_zero S.grading
  let σ : A →ₗ[A] S := LinearMap.toSpanSingleton A S v
  have hσ : PreservesGrading (Graded.shift 𝒜 j) S.grading σ := fun d r hr => by
    have : r • v ∈ S.grading (d - j + j) := SetLike.GradedSMul.smul_mem (mem_shift.1 hr) hv
    rw [sub_add_cancel] at this
    exact this
  have hσ0 : σ ≠ 0 := fun h => hv0 (by simpa [σ] using LinearMap.congr_fun h 1)
  have hσs : Function.Surjective σ := surjective_of_isGradedSimple hS hσ hσ0
  have hts : Function.Surjective t := surjective_of_isGradedSimple hS ht ht0
  obtain ⟨g, hg, hgt⟩ := exists_lift_of_projective 𝒜 (M := A) (ℳ := Graded.shift 𝒜 j) ht hts hσ
  obtain ⟨h, hh, hhσ⟩ := exists_lift_of_projective 𝒜 (ℳ := P.grading) hσ hσs ht
  have hu : PreservesGrading P.grading P.grading (g ∘ₗ h) := hg.comp hh
  have hut : t ∘ₗ (g ∘ₗ h) = t := by rw [← LinearMap.comp_assoc, hgt, hhσ]
  have hbij := hP.bijective_of_comp_eq ht0 hu hut
  let U := GradedEquiv.ofBijective hu hbij
  let h' : P.carrier →ₗ[A] A := h ∘ₗ U.symm.toLinearEquiv.toLinearMap
  have hh' : PreservesGrading P.grading (Graded.shift 𝒜 j) h' :=
    hh.comp U.symm.preservesGrading
  have hgh' : ∀ p, g (h' p) = p := fun p => U.toLinearEquiv.apply_symm_apply p
  set e : A := h' (g 1) with he_def
  have hmul : ∀ x : A, h' (g x) = x * e := fun x => by
    conv_lhs => rw [← mul_one x, ← smul_eq_mul, map_smul, map_smul, smul_eq_mul]
  have he : IsIdempotentElem e := by
    show e * e = e
    rw [← hmul e, he_def, hgh']
  have he0 : e ∈ 𝒜 0 := by
    have h1 : (1 : A) ∈ Graded.shift 𝒜 j j := by
      show (1 : A) ∈ 𝒜 (j - j)
      rw [sub_self]
      exact SetLike.GradedOne.one_mem
    have : h' (g 1) ∈ 𝒜 (j - j) := hh' (hg h1)
    rwa [sub_self] at this
  have hmem : ∀ p, h' p ∈ leftIdeal e := fun p => by
    rw [mem_leftIdeal, ← hmul, hgh']
  let φ : P.carrier →ₗ[A] leftIdeal e := LinearMap.codRestrict _ h' hmem
  have hφbij : Function.Bijective φ := by
    refine ⟨fun p q hpq => ?_, fun y => ⟨g y, Subtype.ext ?_⟩⟩
    · have := congrArg (fun y : leftIdeal e => g (y : A)) hpq
      simpa [φ, hgh'] using this
    · show h' (g y) = y
      rw [hmul]
      exact mem_leftIdeal.1 y.2
  have hφ : PreservesGrading P.grading ((GProj.ofIdempotent e he he0).shift j).grading φ :=
    fun _ _ hp => hh' hp
  exact ⟨e, he, he0, j, ⟨GradedEquiv.ofBijective hφ hφbij⟩⟩

/-- `K₀(A)` is spanned over `ℤ[q, q⁻¹]` by the classes `[A e]` of degree-zero idempotents. -/
theorem K0.span_idemClasses :
    Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses 𝒜) = ⊤ := by
  rw [eq_top_iff, ← K0.span_indec 𝒜, Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  obtain ⟨e, he, he0, j, ⟨φ⟩⟩ := (IndecClass.isIndec_rep b).exists_iso_ofIdempotent
  show K0.of b.rep ∈ _
  rw [ K0.of_eq_of_iso φ, ← K0.T_smul_of]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, he, he0, rfl⟩)

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
/-- `([P{a}], M) = q^{-a} ([P], M)`. -/
theorem pairingRight_shiftHom (M : GFin 𝒜) (a : ℤ) (x : K0 𝒜) :
    pairingRight M (K0.shiftHom a x) = HahnSeries.single (-a) 1 * pairingRight M x := by
  induction x using K0.induction_on with
  | of P =>
    rw [K0.shiftHom_of, pairingRight_of, pairingRight_of, pairingGdim, pairingGdim,
      ← GProj.gdim_comp_add]
    congr 1
    funext d
    exact homGrade_shift_left a d
  | zero => simp
  | add x y hx hy => simp only [map_add, mul_add, hx, hy]
  | neg x hx => simp only [map_neg, mul_neg, hx]

end IdemIndec

/-! ### The product formula `(P ⊠ P', M ⊠ M') = (P, M) (P', M')` -/

section Product

variable {B : Type u} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B}

/-- The external tensor product `M ⊠ M'` of finite-dimensional graded modules. -/
def GFin.extTensor (M : GFin 𝒜) (M' : GFin ℬ) : GFin (tensorGrading 𝒜 ℬ) :=
  { toGMod := GMod.of (ExtTensor k M.carrier M'.carrier) (ExtTensor.grading M.grading M'.grading)
    finiteDimensional := inferInstanceAs (FiniteDimensional k (M.carrier ⊗[k] M'.carrier)) }

theorem GFin.extTensor_grading (M : GFin 𝒜) (M' : GFin ℬ) :
    (M.extTensor M').grading = ExtTensor.grading M.grading M'.grading := rfl

variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [HasGdim 𝒜] [HasGdim ℬ]

omit [HasGdim 𝒜] [HasGdim ℬ] in
theorem pairingRight_extTensor_ofIdempotent (M : GFin 𝒜) (M' : GFin ℬ) {e : A} {e' : B}
    (he : IsIdempotentElem e) (he' : IsIdempotentElem e') (he0 : e ∈ 𝒜 0) (he0' : e' ∈ ℬ 0) :
    pairingRight (M.extTensor M') (K0.extTensor 𝒜 ℬ (K0.of (ofIdempotent e he he0))
        (K0.of (ofIdempotent e' he' he0'))) =
      pairingRight M (K0.of (ofIdempotent e he he0)) *
        pairingRight M' (K0.of (ofIdempotent e' he' he0')) := by
  haveI := HasGdim.of_finiteDimensional M.grading
  haveI := HasGdim.of_finiteDimensional M'.grading
  rw [K0.extTensor_of, pairingRight_of, pairingRight_of, pairingRight_of, pairingGdim,
    pairingGdim, pairingGdim]
  change gdim (homGrade (A ⊗[k] B) (ExtTensor.grading (Graded.submodule 𝒜 (leftIdeal e))
    (Graded.submodule ℬ (leftIdeal e'))) (ExtTensor.grading M.grading M'.grading)) =
    gdim (homGrade A (Graded.submodule 𝒜 (leftIdeal e)) M.grading) *
      gdim (homGrade B (Graded.submodule ℬ (leftIdeal e')) M'.grading)
  rw [gdim_homGrade_ofIdempotent he he0, gdim_homGrade_ofIdempotent he' he0',
    ← gdim_idem_extTensor he he' he0 he0']
  exact gdim_eq_of_finrank_eq fun d =>
    (homGradeExtIdemEquiv (𝒳 := ExtTensor.grading M.grading M'.grading) he he' he0 he0'
      d).finrank_eq

/-- The defect of the product formula, as an additive function of the first argument. -/
def pairingDefectLeft (M : GFin 𝒜) (M' : GFin ℬ) (y : K0 ℬ) : K0 𝒜 →+ LaurentSeries ℤ where
  toFun x := pairingRight (M.extTensor M') (K0.extTensor 𝒜 ℬ x y) -
    pairingRight M x * pairingRight M' y
  map_zero' := by simp
  map_add' x₁ x₂ := by
    simp only [map_add, LinearMap.add_apply, add_mul]
    abel

/-- The defect of the product formula, as an additive function of the second argument. -/
def pairingDefectRight (M : GFin 𝒜) (M' : GFin ℬ) (x : K0 𝒜) : K0 ℬ →+ LaurentSeries ℤ where
  toFun y := pairingRight (M.extTensor M') (K0.extTensor 𝒜 ℬ x y) -
    pairingRight M x * pairingRight M' y
  map_zero' := by simp
  map_add' y₁ y₂ := by
    simp only [map_add, mul_add]
    abel

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [HasGdim 𝒜] [HasGdim ℬ] in
theorem pairingDefectLeft_shift (M : GFin 𝒜) (M' : GFin ℬ) (y : K0 ℬ) (a : ℤ) (x : K0 𝒜) :
    pairingDefectLeft M M' y (K0.shiftHom a x) =
      HahnSeries.single (-a) 1 * pairingDefectLeft M M' y x := by
  simp only [pairingDefectLeft, AddMonoidHom.coe_mk, ZeroHom.coe_mk, K0.extTensor_apply]
  rw [K0.extTensorAdd_shift_left, pairingRight_shiftHom, pairingRight_shiftHom, mul_sub,
    mul_assoc]

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [HasGdim 𝒜] [HasGdim ℬ] in
theorem pairingDefectRight_shift (M : GFin 𝒜) (M' : GFin ℬ) (x : K0 𝒜) (a : ℤ) (y : K0 ℬ) :
    pairingDefectRight M M' x (K0.shiftHom a y) =
      HahnSeries.single (-a) 1 * pairingDefectRight M M' x y := by
  simp only [pairingDefectRight, AddMonoidHom.coe_mk, ZeroHom.coe_mk, K0.extTensor_apply]
  rw [K0.extTensorAdd_shift_right, pairingRight_shiftHom, pairingRight_shiftHom, mul_sub,
    mul_left_comm]

/-- **Product formula**: `(x ⊠ y, [M ⊠ M']) = (x, [M]) · (y, [M'])` for all `x ∈ K₀(A)`,
`y ∈ K₀(B)` and finite-dimensional graded modules `M`, `M'`, where `(-, [M])` is
`[P] ↦ gdim HOM(P, M)` (`Graded.pairingRight`). -/
theorem pairingRight_extTensor (M : GFin 𝒜) (M' : GFin ℬ) (x : K0 𝒜) (y : K0 ℬ) :
    pairingRight (M.extTensor M') (K0.extTensor 𝒜 ℬ x y) =
      pairingRight M x * pairingRight M' y := by
  have key : pairingDefectLeft M M' y x = 0 := by
    refine K0.map_eq_zero_of_mem_span (pairingDefectLeft_shift M M' y) ?_
      (show x ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses 𝒜) by
        rw [K0.span_idemClasses]; trivial)
    rintro _ ⟨e, he, he0, rfl⟩
    have : pairingDefectRight M M' (K0.of (ofIdempotent e he he0)) y = 0 := by
      refine K0.map_eq_zero_of_mem_span (pairingDefectRight_shift M M' _) ?_
        (show y ∈ Submodule.span (LaurentPolynomial ℤ) (K0.idemClasses ℬ) by
          rw [K0.span_idemClasses]; trivial)
      rintro _ ⟨e', he', he0', rfl⟩
      simp only [pairingDefectRight, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [pairingRight_extTensor_ofIdempotent, sub_self]
    exact this
  exact sub_eq_zero.1 key

end Product

/-! ### Isomorphism invariance -/

section Invariance

variable [GradedAlgebra 𝒜]

omit [GradedAlgebra 𝒜] in
/-- Indecomposability is invariant under isomorphism. -/
theorem GProj.IsIndec.of_iso {P Q : GProj 𝒜} (φ : P.Iso Q) (hQ : Q.IsIndec A) : P.IsIndec A := by
  haveI := hQ.nontrivial
  refine ⟨φ.toLinearEquiv.toEquiv.nontrivial, fun e he hidem => ?_⟩
  let f : Module.End A Q.carrier :=
    φ.toLinearEquiv.toLinearMap ∘ₗ e ∘ₗ φ.symm.toLinearEquiv.toLinearMap
  have hf : f ∈ endZero A Q.grading := fun d x hx => φ.map_mem (he (φ.symm.map_mem hx))
  have hfidem : IsIdempotentElem f := by
    refine LinearMap.ext fun x => ?_
    show φ (e (φ.symm (φ (e (φ.symm x))))) = φ (e (φ.symm x))
    rw [show φ.symm (φ (e (φ.symm x))) = e (φ.symm x) from φ.toLinearEquiv.symm_apply_apply _]
    exact congrArg φ (LinearMap.congr_fun hidem (φ.symm x))
  have hback : ∀ x, e x = φ.symm (f (φ x)) := fun x => by
    show e x = φ.symm (φ (e (φ.symm (φ x))))
    rw [show φ.symm (φ x) = x from φ.toLinearEquiv.symm_apply_apply x,
      show φ.symm (φ (e x)) = e x from φ.toLinearEquiv.symm_apply_apply _]
  rcases hQ.eq_zero_or_eq_one f hf hfidem with h | h
  · left
    refine LinearMap.ext fun x => ?_
    rw [hback, h, LinearMap.zero_apply, LinearMap.zero_apply]
    exact φ.symm.toLinearEquiv.map_zero
  · right
    refine LinearMap.ext fun x => ?_
    rw [hback, h, Module.End.one_apply, Module.End.one_apply]
    exact φ.toLinearEquiv.symm_apply_apply x

variable [HasGdim 𝒜]

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
/-- `homRank` depends only on the isomorphism class of the target. -/
theorem K0.homRank_congr {S S' : GMod 𝒜} [HasGdim S.grading] [HasGdim S'.grading]
    (e : S.Iso S') : K0.homRank S = K0.homRank S' :=
  K0.hom_ext fun P => by
    rw [K0.homRank_of, K0.homRank_of, finrank_homGrade_congr_right e 0]

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
/-- `dim END(M)_0 = 1` when every endomorphism of `M` is a scalar. -/
theorem finrank_endZero_eq_one_of_forall {M : GMod 𝒜} [Nontrivial M]
    (h : ∀ f : M →ₗ[A] M, ∃ c : k, f = c • LinearMap.id) :
    finrank k (endZero A M.grading) = 1 := by
  have hbot : endZero A M.grading = ⊥ := eq_bot_iff.2 fun φ _ => by
    obtain ⟨c, hc⟩ := h φ
    rw [Algebra.mem_bot]
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc]; rfl⟩
  rw [hbot, Subalgebra.finrank_bot]

instance GFin.hasGdim_toGMod_shift (M : GFin 𝒜) (s : ℤ) : HasGdim (M.toGMod.shift s).grading :=
  haveI := HasGdim.of_finiteDimensional M.grading
  inferInstanceAs (HasGdim (Graded.shift M.grading s))

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
theorem homRank_shift_eq_coeff (M : GFin 𝒜) (s : ℤ) (P : GProj 𝒜) :
    (K0.homRank (M.toGMod.shift s) (K0.of P) : ℤ) = (pairingRight M (K0.of P)).coeff (-s) := by
  haveI := HasGdim.of_finiteDimensional M.grading
  rw [K0.homRank_of, pairingRight_of, pairingGdim, coeff_gdim]
  change (finrank k (homGrade A P.grading (Graded.shift M.grading s) 0) : ℤ) = _
  rw [homGrade_shift_right, zero_sub]

end Invariance

/-- The unit `q^n` of `ℤ[q, q⁻¹]`. -/
def unitT (n : ℤ) : (LaurentPolynomial ℤ)ˣ :=
  ⟨LaurentPolynomial.T n, LaurentPolynomial.T (-n),
    by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero],
    by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]⟩

@[simp] theorem coe_unitT (n : ℤ) : (unitT n : LaurentPolynomial ℤ) = LaurentPolynomial.T n := rfl

/-! ### The indecomposables of `A ⊗ B` -/

section Counting

variable {B : Type u} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [HasGdim 𝒜] [HasGdim ℬ]

variable (𝒜 ℬ) in
/-- The hypotheses of the identification `K₀(A ⊗ B) ≅ K₀(A) ⊗ K₀(B)`: the graded simple tops of
`A` and `B` are finite-dimensional and **absolutely irreducible** (every endomorphism is a scalar),
and the graded simple tops of `A ⊗ B` are finite-dimensional. -/
structure TensorK0Hyp : Prop where
  fdA : ∀ b : IndecClass 𝒜, FiniteDimensional k b.top
  fdB : ∀ b : IndecClass ℬ, FiniteDimensional k b.top
  endA : ∀ (b : IndecClass 𝒜) (f : b.top →ₗ[A] b.top), ∃ c : k, f = c • LinearMap.id
  endB : ∀ (b : IndecClass ℬ) (f : b.top →ₗ[B] b.top), ∃ c : k, f = c • LinearMap.id
  fdC : ∀ c : IndecClass (tensorGrading 𝒜 ℬ), FiniteDimensional k c.top

namespace TensorK0Hyp

variable (H : TensorK0Hyp 𝒜 ℬ)
include H

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] [GradedAlgebra ℬ] [HasGdim ℬ] in
theorem finrank_endZero_topA (b : IndecClass 𝒜) : finrank k (endZero A b.top.grading) = 1 :=
  haveI := (IndecClass.isGradedSimple_top b).nontrivial
  finrank_endZero_eq_one_of_forall (H.endA b)

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] [GradedAlgebra ℬ] [HasGdim ℬ] in
theorem finrank_endZero_topB (b : IndecClass ℬ) : finrank k (endZero B b.top.grading) = 1 :=
  haveI := (IndecClass.isGradedSimple_top b).nontrivial
  finrank_endZero_eq_one_of_forall (H.endB b)

omit [GradedAlgebra ℬ] [HasGdim ℬ] in
open scoped Classical in
theorem pairingRight_topA (b d : IndecClass 𝒜) :
    pairingRight (IndecClass.topFin H.fdA d) (K0.of b.rep) = if b = d then 1 else 0 := by
  have := pairing_indecBasis_topBasis_of_finrank_eq_one H.fdA H.finrank_endZero_topA b d
  rw [K0.indecBasis_apply, G0.topBasis_apply, pairing_of_of] at this
  rw [pairingRight_of]
  exact this

omit [GradedAlgebra 𝒜] [HasGdim 𝒜] in
open scoped Classical in
theorem pairingRight_topB (b d : IndecClass ℬ) :
    pairingRight (IndecClass.topFin H.fdB d) (K0.of b.rep) = if b = d then 1 else 0 := by
  have := pairing_indecBasis_topBasis_of_finrank_eq_one H.fdB H.finrank_endZero_topB b d
  rw [K0.indecBasis_apply, G0.topBasis_apply, pairing_of_of] at this
  rw [pairingRight_of]
  exact this

omit H in
/-- The finite-dimensional graded simple `A ⊗ B`-module `S_d ⊠ S_{d'}`. -/
def topT (H : TensorK0Hyp 𝒜 ℬ) (d : IndecClass 𝒜) (d' : IndecClass ℬ) :
    GFin (tensorGrading 𝒜 ℬ) :=
  (IndecClass.topFin H.fdA d).extTensor (IndecClass.topFin H.fdB d')

open scoped Classical in
/-- `dim HOM(P_b ⊠ P_{b'}, (S_d ⊠ S_{d'}){s})_0 = δ_{b d} δ_{b' d'} δ_{s 0}`. -/
theorem homRank_topT_shift (b d : IndecClass 𝒜) (b' d' : IndecClass ℬ) (s : ℤ) :
    K0.homRank ((H.topT d d').toGMod.shift s) (K0.of (b.rep.extTensor b'.rep)) =
      if b = d ∧ b' = d' ∧ s = 0 then 1 else 0 := by
  rw [homRank_shift_eq_coeff, ← K0.extTensor_of, topT, pairingRight_extTensor,
    H.pairingRight_topA, H.pairingRight_topB]
  by_cases hb : b = d
  · by_cases hb' : b' = d'
    · simp only [hb, hb', if_true, true_and, mul_one, HahnSeries.coeff_one, neg_eq_zero]
    · simp [hb']
  · simp [hb]

/-- Every graded simple top `S_c` of `A ⊗ B` is some `(S_b ⊠ S_{b'}){a}`. -/
theorem exists_top_iso (c : IndecClass (tensorGrading 𝒜 ℬ)) :
    ∃ (b : IndecClass 𝒜) (b' : IndecClass ℬ) (a : ℤ),
      Nonempty (c.top.grading ≃ᵍ[A ⊗[k] B]
        Graded.shift (ExtTensor.grading b.top.grading b'.top.grading) a) := by
  haveI := H.fdC c
  exact TensorSimple.exists_gradedEquiv_extTensor_top H.endA (IndecClass.isGradedSimple_top c)

omit H in
/-- The first factor `b` of `S_c ≅ (S_b ⊠ S_{b'}){a}`. -/
def fst (H : TensorK0Hyp 𝒜 ℬ) (c : IndecClass (tensorGrading 𝒜 ℬ)) : IndecClass 𝒜 :=
  (H.exists_top_iso c).choose

omit H in
/-- The second factor `b'` of `S_c ≅ (S_b ⊠ S_{b'}){a}`. -/
def snd (H : TensorK0Hyp 𝒜 ℬ) (c : IndecClass (tensorGrading 𝒜 ℬ)) : IndecClass ℬ :=
  (H.exists_top_iso c).choose_spec.choose

omit H in
/-- The shift `a` of `S_c ≅ (S_b ⊠ S_{b'}){a}`. -/
def shift (H : TensorK0Hyp 𝒜 ℬ) (c : IndecClass (tensorGrading 𝒜 ℬ)) : ℤ :=
  (H.exists_top_iso c).choose_spec.choose_spec.choose

theorem top_iso (c : IndecClass (tensorGrading 𝒜 ℬ)) :
    Nonempty (c.top.grading ≃ᵍ[A ⊗[k] B]
      Graded.shift (ExtTensor.grading (H.fst c).top.grading (H.snd c).top.grading) (H.shift c)) :=
  (H.exists_top_iso c).choose_spec.choose_spec.choose_spec

set_option synthInstance.maxHeartbeats 200000 in
open scoped Classical in
theorem mult_mul_finrank (b : IndecClass 𝒜) (b' : IndecClass ℬ)
    (c : IndecClass (tensorGrading 𝒜 ℬ)) (a : ℤ) :
    K0.mult (K0.of (b.rep.extTensor b'.rep)) c a *
        finrank k (endZero (A ⊗[k] B) c.top.grading) =
      if b = H.fst c ∧ b' = H.snd c ∧ H.shift c + a = 0 then 1 else 0 := by
  rw [← K0.homRank_top_shift]
  obtain ⟨e⟩ := H.top_iso c
  have e' : (c.top.shift a).Iso ((H.topT (H.fst c) (H.snd c)).toGMod.shift (H.shift c + a)) :=
    (e.shift a).trans (GradedEquiv.ofEq (shift_shift _ _ _))
  rw [K0.homRank_congr e', H.homRank_topT_shift]

set_option synthInstance.maxHeartbeats 200000 in
theorem finrank_endZero_topC (c : IndecClass (tensorGrading 𝒜 ℬ)) :
    finrank k (endZero (A ⊗[k] B) c.top.grading) = 1 := by
  classical
  have h := H.mult_mul_finrank (H.fst c) (H.snd c) c (-H.shift c)
  rw [if_pos ⟨rfl, rfl, by ring⟩] at h
  have hpos := K0.finrank_endZero_top_pos c
  have hnn := K0.mult_of_nonneg ((H.fst c).rep.extTensor (H.snd c).rep) c (-H.shift c)
  have hpos' : (1 : ℤ) ≤ (finrank k (endZero (A ⊗[k] B) c.top.grading) : ℤ) := by
    exact_mod_cast hpos
  set m := K0.mult (K0.of ((H.fst c).rep.extTensor (H.snd c).rep)) c (-H.shift c)
  have hm1 : 1 ≤ m := by
    rcases (show m = 0 ∨ 1 ≤ m by omega) with h0 | h0
    · rw [h0, zero_mul] at h
      exact absurd h (by norm_num)
    · exact h0
  have : (finrank k (endZero (A ⊗[k] B) c.top.grading) : ℤ) = 1 := by nlinarith
  exact_mod_cast this

set_option synthInstance.maxHeartbeats 200000 in
open scoped Classical in
/-- **Multiplicities of `P_c` in `P_b ⊠ P_{b'}`**: `[P_b ⊠ P_{b'}] = q^{-a_c} [P_c]` for the
unique `c` with top `(S_b ⊠ S_{b'}){a_c}`. -/
theorem mult_extTensor_rep (b : IndecClass 𝒜) (b' : IndecClass ℬ)
    (c : IndecClass (tensorGrading 𝒜 ℬ)) (a : ℤ) :
    K0.mult (K0.of (b.rep.extTensor b'.rep)) c a =
      if b = H.fst c ∧ b' = H.snd c ∧ H.shift c + a = 0 then 1 else 0 := by
  have := H.mult_mul_finrank b b' c a
  rwa [H.finrank_endZero_topC, Nat.cast_one, mul_one] at this

theorem fst_snd_injective :
    Function.Injective fun c : IndecClass (tensorGrading 𝒜 ℬ) => (H.fst c, H.snd c) := by
  intro c₁ c₂ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨e₁⟩ := H.top_iso c₁
  obtain ⟨e₂⟩ := H.top_iso c₂
  rw [h1, h2] at e₁
  set T := ExtTensor.grading (H.fst c₂).top.grading (H.snd c₂).top.grading
  have E : Graded.shift c₁.top.grading (H.shift c₂) ≃ᵍ[A ⊗[k] B]
      Graded.shift c₂.top.grading (H.shift c₁) :=
    (e₁.shift (H.shift c₂)).trans ((GradedEquiv.ofEq (shift_shift T _ _)).trans
      ((GradedEquiv.ofEq (by rw [add_comm])).trans
        ((GradedEquiv.ofEq (shift_shift T _ _)).symm.trans (e₂.shift (H.shift c₁)).symm)))
  exact (IndecClass.eq_of_gradedEquiv_top_shift E).1

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [HasGdim 𝒜] [HasGdim ℬ] in
omit H in
theorem nontrivial_extTensor {P : GProj 𝒜} {P' : GProj ℬ} [Nontrivial P.carrier]
    [Nontrivial P'.carrier] : Nontrivial (P.extTensor P').carrier := by
  obtain ⟨x, hx⟩ := exists_ne (0 : P.carrier)
  obtain ⟨y, hy⟩ := exists_ne (0 : P'.carrier)
  exact ⟨⟨_, 0, TensorSimple.tmul_ne_zero (k := k) hx hy⟩⟩

theorem fst_snd_surjective :
    Function.Surjective fun c : IndecClass (tensorGrading 𝒜 ℬ) => (H.fst c, H.snd c) := by
  classical
  rintro ⟨b, b'⟩
  haveI := (IndecClass.isIndec_rep b).nontrivial
  haveI := (IndecClass.isIndec_rep b').nontrivial
  haveI := nontrivial_extTensor (P := b.rep) (P' := b'.rep)
  have hZ : K0.of (b.rep.extTensor b'.rep) ≠ 0 := by
    intro h
    rw [← K0.of_eq_zero_of_subsingleton (zeroObj (tensorGrading 𝒜 ℬ)), K0.of_eq_of_iff] at h
    obtain ⟨φ⟩ := h
    obtain ⟨x, hx⟩ := exists_ne (0 : (b.rep.extTensor b'.rep).carrier)
    exact hx (φ.toLinearEquiv.injective (Subsingleton.elim _ _))
  obtain ⟨c, hc⟩ : ∃ c, (K0.indecBasis (tensorGrading 𝒜 ℬ)).repr
      (K0.of (b.rep.extTensor b'.rep)) c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hZ ((K0.indecBasis _).repr.injective (by ext c : 1; rw [hcon c, map_zero]; rfl))
  obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hc
  have hm : K0.mult (K0.of (b.rep.extTensor b'.rep)) c a ≠ 0 := ha
  rw [H.mult_extTensor_rep] at hm
  split_ifs at hm with hcond
  · exact ⟨c, Prod.ext hcond.1.symm hcond.2.1.symm⟩
  · exact absurd rfl hm

omit H in
/-- **The indecomposable graded projective `A ⊗ B`-modules are the `P_b ⊠ P_{b'}`**: the
bijection `c ↦ (b, b')`, where `S_c ≅ (S_b ⊠ S_{b'}){a}`. -/
def indecClassEquiv (H : TensorK0Hyp 𝒜 ℬ) :
    IndecClass (tensorGrading 𝒜 ℬ) ≃ IndecClass 𝒜 × IndecClass ℬ :=
  Equiv.ofBijective _ ⟨H.fst_snd_injective, H.fst_snd_surjective⟩

theorem indecClassEquiv_apply (c : IndecClass (tensorGrading 𝒜 ℬ)) :
    H.indecClassEquiv c = (H.fst c, H.snd c) := rfl

/-- `[P_b ⊠ P_{b'}] = q^{-a_c} [P_c]` in `K₀(A ⊗ B)`, `c = indecClassEquiv⁻¹ (b, b')`. -/
theorem of_extTensor_rep (b : IndecClass 𝒜) (b' : IndecClass ℬ) :
    K0.of (b.rep.extTensor b'.rep) =
      (LaurentPolynomial.T (-H.shift (H.indecClassEquiv.symm (b, b'))) : LaurentPolynomial ℤ) •
        K0.of (H.indecClassEquiv.symm (b, b')).rep := by
  classical
  set c := H.indecClassEquiv.symm (b, b') with hc
  have hcb : H.indecClassEquiv c = (b, b') := by rw [hc, Equiv.apply_symm_apply]
  rw [indecClassEquiv_apply, Prod.mk.injEq] at hcb
  refine (K0.indecBasis _).repr.injective (Finsupp.ext fun c' => Finsupp.ext fun a => ?_)
  change K0.mult _ c' a = K0.mult _ c' a
  rw [H.mult_extTensor_rep, K0.mult_T_smul_of_rep]
  by_cases hc' : c' = c
  · subst hc'
    have e1 : (b = H.fst c ∧ b' = H.snd c ∧ H.shift c + a = 0) ↔
        ((c, -H.shift c) = (c, a)) := by
      rw [Prod.mk.injEq]
      constructor
      · rintro ⟨-, -, h⟩
        exact ⟨rfl, by omega⟩
      · rintro ⟨-, h⟩
        exact ⟨hcb.1.symm, hcb.2.symm, by omega⟩
    exact if_congr e1 rfl rfl
  · rw [if_neg, if_neg]
    · rintro h
      exact hc' (Prod.ext_iff.1 h).1.symm
    · rintro ⟨h1, h2, -⟩
      apply hc'
      apply H.indecClassEquiv.injective
      rw [indecClassEquiv_apply, indecClassEquiv_apply, ← h1, ← h2, hcb.1, hcb.2]

/-- **`P_c ≅ (P_b ⊠ P_{b'}){a_c}`**: every indecomposable graded projective `A ⊗ B`-module is
(a shift of) an external tensor product of indecomposable graded projectives. -/
theorem nonempty_iso_rep (c : IndecClass (tensorGrading 𝒜 ℬ)) :
    Nonempty (c.rep.Iso (((H.fst c).rep.extTensor (H.snd c).rep).shift (H.shift c))) := by
  have h := H.of_extTensor_rep (H.fst c) (H.snd c)
  rw [show ((H.fst c, H.snd c) : IndecClass 𝒜 × IndecClass ℬ) = H.indecClassEquiv c from rfl,
    Equiv.symm_apply_apply] at h
  refine K0.of_eq_of_iff.1 ?_
  rw [← K0.T_smul_of, h, smul_smul, ← LaurentPolynomial.T_add, add_neg_cancel,
    LaurentPolynomial.T_zero, one_smul]

/-- **`P_b ⊠ P_{b'}` is indecomposable.** -/
theorem isIndec_extTensor_rep (b : IndecClass 𝒜) (b' : IndecClass ℬ) :
    (b.rep.extTensor b'.rep).IsIndec (A ⊗[k] B) := by
  set c := H.indecClassEquiv.symm (b, b')
  have h := H.of_extTensor_rep b b'
  rw [K0.T_smul_of] at h
  obtain ⟨φ⟩ := K0.of_eq_of_iff.1 h
  exact GProj.IsIndec.of_iso φ ((IndecClass.isIndec_rep c).shift _)

omit [HasGdim 𝒜] [HasGdim ℬ] in
/-- **`S_b ⊠ S_{b'}` is graded simple** (indeed simple): KL I, absolute irreducibility. -/
theorem isGradedSimple_extTensor_top (b : IndecClass 𝒜) (b' : IndecClass ℬ) :
    IsGradedSimple (tensorGrading 𝒜 ℬ) (ExtTensor.grading b.top.grading b'.top.grading) := by
  haveI := H.fdA b
  haveI := H.fdB b'
  haveI : IsSimpleModule A b.top := (IndecClass.isGradedSimple_top b).isSimpleModule
  haveI : IsSimpleModule B b'.top := (IndecClass.isGradedSimple_top b').isSimpleModule
  haveI := TensorSimple.isSimpleModule_extTensor (B := B) (M := b'.top.carrier) (H.endA b)
  exact ⟨IsSimpleModule.nontrivial (A ⊗[k] B) _, fun p _ => IsSimpleOrder.eq_bot_or_eq_top p⟩

omit H [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [HasGdim 𝒜] [HasGdim ℬ] in
theorem extTensor_topMap_preservesGrading (b : IndecClass 𝒜) (b' : IndecClass ℬ) :
    PreservesGrading (b.rep.extTensor b'.rep).grading
      (ExtTensor.grading b.top.grading b'.top.grading)
      (ExtTensor.map (k := k) b.topMap b'.topMap) :=
  ExtTensor.map_preservesGrading (IndecClass.preservesGrading_topMap b)
    (IndecClass.preservesGrading_topMap b')

omit H [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [HasGdim 𝒜] [HasGdim ℬ] in
theorem extTensor_topMap_ne_zero (b : IndecClass 𝒜) (b' : IndecClass ℬ) :
    ExtTensor.map (k := k) b.topMap b'.topMap ≠ 0 := by
  haveI := (IndecClass.isGradedSimple_top b).nontrivial
  haveI := (IndecClass.isGradedSimple_top b').nontrivial
  have hs := ExtTensor.map_surjective (k := k)
    (surjective_of_isGradedSimple (IndecClass.isGradedSimple_top b)
      (IndecClass.preservesGrading_topMap b) (IndecClass.topMap_ne_zero b))
    (surjective_of_isGradedSimple (IndecClass.isGradedSimple_top b')
      (IndecClass.preservesGrading_topMap b') (IndecClass.topMap_ne_zero b'))
  obtain ⟨x, hx⟩ := exists_ne (0 : b.top.carrier)
  obtain ⟨y, hy⟩ := exists_ne (0 : b'.top.carrier)
  intro h
  obtain ⟨z, hz⟩ := hs (ExtTensor.tmul x y)
  rw [h, LinearMap.zero_apply] at hz
  exact TensorSimple.tmul_ne_zero (k := k) hx hy hz.symm

/-- **`P_b ⊠ P_{b'}` is the projective cover of `S_b ⊠ S_{b'}`**: it is indecomposable, and
`π_b ⊠ π_{b'} : P_b ⊠ P_{b'} → S_b ⊠ S_{b'}` is a nonzero (hence surjective) degree-preserving
map onto a graded simple module. -/
theorem extTensor_rep_isCover (b : IndecClass 𝒜) (b' : IndecClass ℬ) :
    (b.rep.extTensor b'.rep).IsIndec (A ⊗[k] B) ∧
      IsGradedSimple (tensorGrading 𝒜 ℬ) (ExtTensor.grading b.top.grading b'.top.grading) ∧
      PreservesGrading (b.rep.extTensor b'.rep).grading
        (ExtTensor.grading b.top.grading b'.top.grading)
        (ExtTensor.map (k := k) b.topMap b'.topMap) ∧
      ExtTensor.map (k := k) b.topMap b'.topMap ≠ 0 :=
  ⟨H.isIndec_extTensor_rep b b', H.isGradedSimple_extTensor_top b b',
    extTensor_topMap_preservesGrading b b', extTensor_topMap_ne_zero b b'⟩

omit H in
/-- **The isomorphism `K₀(A) ⊗_{ℤ[q,q⁻¹]} K₀(B) ≅ K₀(A ⊗ B)`**, `x ⊗ y ↦ x ⊠ y`
(`extTensorEquiv_tmul`): it maps the basis `[P_b] ⊗ [P_{b'}]` to the basis `q^{-a_c} [P_c]`,
`c = indecClassEquiv⁻¹ (b, b')`. -/
def extTensorEquiv (H : TensorK0Hyp 𝒜 ℬ) :
    K0 𝒜 ⊗[LaurentPolynomial ℤ] K0 ℬ ≃ₗ[LaurentPolynomial ℤ] K0 (tensorGrading 𝒜 ℬ) :=
  ((K0.indecBasis 𝒜).tensorProduct (K0.indecBasis ℬ)).equiv
    ((K0.indecBasis (tensorGrading 𝒜 ℬ)).unitsSMul fun c => unitT (-H.shift c))
    H.indecClassEquiv.symm

theorem extTensorEquiv_toLinearMap :
    H.extTensorEquiv.toLinearMap = TensorProduct.lift (K0.extTensor 𝒜 ℬ) := by
  refine ((K0.indecBasis 𝒜).tensorProduct (K0.indecBasis ℬ)).ext fun i => ?_
  obtain ⟨b, b'⟩ := i
  rw [LinearEquiv.coe_coe, extTensorEquiv, Basis.equiv_apply, Basis.unitsSMul_apply,
    Basis.tensorProduct_apply, TensorProduct.lift.tmul, K0.indecBasis_apply, K0.indecBasis_apply,
    K0.indecBasis_apply, K0.extTensor_of, H.of_extTensor_rep, Units.smul_def]
  rfl

/-- `extTensorEquiv (x ⊗ y) = x ⊠ y`. -/
@[simp] theorem extTensorEquiv_tmul (x : K0 𝒜) (y : K0 ℬ) :
    H.extTensorEquiv (x ⊗ₜ y) = K0.extTensor 𝒜 ℬ x y := by
  rw [← LinearEquiv.coe_coe, extTensorEquiv_toLinearMap, TensorProduct.lift.tmul]

/-- The inverse of `extTensorEquiv` on classes: `[P ⊠ P'] ↦ [P] ⊗ [P']`. -/
theorem extTensorEquiv_symm_of (P : GProj 𝒜) (P' : GProj ℬ) :
    H.extTensorEquiv.symm (K0.of (P.extTensor P')) = K0.of P ⊗ₜ K0.of P' := by
  rw [LinearEquiv.symm_apply_eq, extTensorEquiv_tmul, K0.extTensor_of]

end TensorK0Hyp

end Counting

end Categorification.Graded
