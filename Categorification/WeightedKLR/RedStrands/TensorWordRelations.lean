/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorWordSpanning
/-!
# Finite relations for the common divided word generators

Webster, arXiv:1309.3796v2, §4.7, Theorem 4.38. Both sides are spanned
integrally by the same divided words. Identifying their generators is
therefore equivalent to identifying their finite Laurent coefficient
relations. Categorical grading shifts evaluate at the inverse quantum
parameter. The criterion is independent of a choice of bilinear form.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
local notation "LP" => LaurentPolynomial ℤ
private abbrev invLP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv
local instance : RingHomInvPair invLP.toRingHom invLP.toRingHom := RingHomInvPair.of_ringEquiv invLP

private theorem generatorEquiv_iff {J P V : Type*} [AddCommGroup P] [Module LP P] [AddCommGroup V] [Module LP V]
    (p : J → P) (v : J → V) (hp : Submodule.span LP (Set.range p) = ⊤)
    (hv : Submodule.span LP (Set.range v) = ⊤) :
    (∃ e : P ≃ₛₗ[invLP.toRingHom] V, ∀ j, e (p j) = v j) ↔
      ∀ a : J →₀ LP, a.sum (fun j c => c • p j) = 0 ↔ a.sum (fun j c => invLP c • v j) = 0 := by
  let A := Finsupp.linearCombination LP p
  let B := Finsupp.linearCombination LP v
  let σ : (J →₀ LP) ≃ₛₗ[invLP.toRingHom] (J →₀ LP) := Finsupp.mapRange.linearEquiv invLP.toSemilinearEquiv
  let D : (J →₀ LP) →ₛₗ[invLP.toRingHom] V := B.comp σ.toLinearMap
  have hD (a : J →₀ LP) : D a = a.sum (fun j c => invLP c • v j) := by
    change (Finsupp.mapRange invLP (map_zero _) a).sum _ = _
    rw [Finsupp.sum_mapRange_index]
    · rfl
    · intro j; simp
  have genA (j : J) : A (Finsupp.single j 1) = p j := by simp [A]
  have genD (j : J) : D (Finsupp.single j 1) = v j := by rw [hD, Finsupp.sum_single_index]; all_goals simp
  constructor
  · rintro ⟨e,he⟩ a
    have eq : e (A a) = D a := by
      rw [hD, Finsupp.linearCombination_apply]
      unfold Finsupp.sum
      rw [map_sum e]
      apply Finset.sum_congr rfl
      intro j _
      rw [e.map_smulₛₗ, he]
      rfl
    rw [← hD, ← eq]
    exact e.map_eq_zero_iff.symm
  · intro rel
    have hker (a : J →₀ LP) : A a = 0 ↔ D a = 0 := by rw [hD]; exact rel a
    have surA : Function.Surjective A := LinearMap.range_eq_top.mp ((Finsupp.range_linearCombination (v := p) LP).trans hp)
    have surB : Function.Surjective B := LinearMap.range_eq_top.mp ((Finsupp.range_linearCombination (v := v) LP).trans hv)
    have hk : LinearMap.ker A ≤ LinearMap.ker D := fun a ha => (hker a).mp ha
    let f := ((LinearMap.ker A).liftQ D hk).comp
      (A.quotKerEquivOfSurjective surA).symm.toLinearMap
    have hf (a : J →₀ LP) : f (A a) = D a := by
      change (LinearMap.ker A).liftQ D hk ((A.quotKerEquivOfSurjective surA).symm (A a)) = D a
      rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
    have inj : Function.Injective f := by
      rintro x y h
      obtain ⟨a,rfl⟩ := surA x
      obtain ⟨b,rfl⟩ := surA y
      rw [hf,hf] at h
      have hz := (hker (a-b)).mpr (by rw [D.map_sub]; exact sub_eq_zero.mpr h)
      rw [A.map_sub] at hz
      exact sub_eq_zero.mp hz
    have sur : Function.Surjective f := by
      intro y
      obtain ⟨a,ha⟩ := surB y
      refine ⟨A (σ.symm a), (hf _).trans ?_⟩
      change B (σ (σ.symm a)) = y
      rwa [σ.apply_symm_apply]
    refine ⟨LinearEquiv.ofBijective f ⟨inj,sur⟩, fun j => ?_⟩
    change f (p j) = v j
    rw [← genA j, hf, genD]

open KLR QuantumGroup Categorification.Graded LieLean LieLean.QuantumGroup.GrandLoop
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  (hQ : IsRouquierQ C Q) {R : C.toLusztig.RootDatum Y} [Finite I]
  (wt : Fin ℓ → Dom R) (hR : R.IsXRegular) (β : Multiset I)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "P" => K0 (tensorProductGrade G β)
local notation "V" => integralTensorWeight wt hR β.toFinsupp

/-- The common set of divided words in a fixed black content. -/
abbrev TensorWordAt (ℓ : ℕ) (β : Multiset I) := {w : TensorWord I ℓ // w.content.toMultiset = β}

/-- The shifted divided projective at its specified black content. -/
def projectiveWordAt (w : TensorWordAt ℓ β) : P :=
  w.2 ▸ K0.of (tensorWordProjective Λ C hQ w.1)

/-- The divided vector in the corresponding integral weight space. -/
def vectorWordAt (w : TensorWordAt ℓ β) : V :=
  ⟨tensorWordVector w.1 wt, by
    rw [← span_tensorWordVector_content]
    exact Submodule.subset_span ⟨w.1, by simpa using congrArg Multiset.toFinsupp w.2, rfl⟩⟩

omit [Finite I] in
theorem span_projectiveWordAt : Submodule.span LP (Set.range (projectiveWordAt Λ C hQ β)) = ⊤ := by
  rw [← span_tensorWordProjective Λ C hQ β]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨w,hw⟩,rfl⟩
    exact ⟨w,hw,rfl⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨w,hw⟩,rfl⟩

theorem span_vectorWordAt : Submodule.span LP (Set.range (vectorWordAt (C := C) wt hR β)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff _ _).2
  rw [← span_tensorWordVector_content]
  congr 1
  ext x
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨w.1, by simpa using congrArg Multiset.toFinsupp w.2, rfl⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨w, by simp [hw]⟩,rfl⟩

/-- The equality of all finite Laurent coefficient relations at one black
content, with the shift evaluated as the inverse quantum parameter. -/
def SameWordRelations : Prop :=
  ∀ a : TensorWordAt ℓ β →₀ LP,
    a.sum (fun w c => c • projectiveWordAt Λ C hQ β w) = 0 ↔
      a.sum (fun w c => LaurentPolynomial.invert c • vectorWordAt (C := C) wt hR β w) = 0

/-- For the shared divided words in Webster, §4.7, Theorem 4.38, a
grading-compatible isomorphism on one black-content block exists exactly
when the finite coefficient relations agree. -/
theorem exists_wordEquivAt_iff :
    (∃ e : P ≃ₛₗ[invLP.toRingHom] V, ∀ w : TensorWordAt ℓ β,
      e (projectiveWordAt Λ C hQ β w) = vectorWordAt (C := C) wt hR β w) ↔
      SameWordRelations Λ C hQ wt hR β := by
  unfold SameWordRelations
  exact generatorEquiv_iff (projectiveWordAt Λ C hQ β) (vectorWordAt C wt hR β) (span_projectiveWordAt Λ C hQ β) (span_vectorWordAt (C := C) wt hR β)


local notation "Ps" => fun γ : Multiset I => K0 (tensorProductGrade G γ)
local notation "Vs" => fun γ : Multiset I => (integralTensorWeight wt hR (Multiset.toFinsupp γ) : Type _)
private abbrev weightInclusion : V →ₗ[LP] integralTensor wt := Submodule.inclusion (fun _ hx => hx.1)

private def joinWeights : DirectSum (Multiset I) Vs →ₗ[LP] integralTensor wt :=
  DirectSum.toModule LP _ _ (weightInclusion C wt hR)

/-- The divided tensor word as a member of the full integral tensor lattice. -/
def integralWordVector (w : TensorWord I ℓ) : integralTensor wt :=
  ⟨tensorWordVector w wt, span_tensorWordVector wt ▸ Submodule.subset_span (Set.mem_range_self w)⟩

private theorem span_integralWordVector : Submodule.span LP (Set.range (integralWordVector (C := C) wt)) = ⊤ :=
  (Submodule.span_range_subtype_eq_top_iff _ _).2 (span_tensorWordVector wt)

private theorem joinWeights_of (x : V) :
    joinWeights C wt hR (DirectSum.of Vs β x) = weightInclusion C wt hR β x :=
  DirectSum.toModule_lof (M := Vs) (φ := weightInclusion C wt hR) LP β x

private theorem proj_joinWeights (x : DirectSum (Multiset I) Vs) :
    tensorWeightProj wt hR ((∑ j, (wt j).1) - R.rootSum β.toFinsupp)
      ((joinWeights C wt hR x : integralTensor wt) : TensorSpace wt) = (x β : TensorSpace wt) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, Submodule.coe_add, hx, hy]
    rfl
  | of γ y =>
    rw [joinWeights_of]
    by_cases h : β = γ
    · subst γ
      rw [DirectSum.of_eq_same]
      exact y.property.2
    · rw [DirectSum.of_eq_of_ne _ _ _ h]
      have hn : (∑ j, (wt j).1) - R.rootSum β.toFinsupp ≠ (∑ j, (wt j).1) - R.rootSum γ.toFinsupp :=
        fun e => h (Multiset.toFinsupp.injective (R.rootSum_injective hR (sub_right_injective e)))
      have he := tensorWeightProj_orthogonal wt hR hn (y : TensorSpace wt)
      rw [show tensorWeightProj wt hR ((∑ j, (wt j).1) - R.rootSum γ.toFinsupp) (y : TensorSpace wt) = y
        from y.property.2] at he
      exact he

private theorem joinWeights_bijective : Function.Bijective (joinWeights C wt hR) := by
  constructor
  · intro x y h
    ext β
    exact (proj_joinWeights C wt hR β x).symm.trans ((congrArg (fun z : integralTensor wt =>
      tensorWeightProj wt hR ((∑ j, (wt j).1) - R.rootSum β.toFinsupp) (z : TensorSpace wt)) h).trans
      (proj_joinWeights C wt hR β y))
  · apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← span_integralWordVector (C := C) wt]
    apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    exact ⟨DirectSum.of Vs w.content.toMultiset (vectorWordAt C wt hR _ ⟨w,rfl⟩), joinWeights_of C wt hR _ _⟩

/-- The sum over all black contents gives the whole integral tensor lattice
(Webster §4.7, the weight decomposition used in Theorem 4.38). -/
def tensorWeightSumEquiv : DirectSum (Multiset I) Vs ≃ₗ[LP] integralTensor wt :=
  LinearEquiv.ofBijective _ (joinWeights_bijective C wt hR)

@[simp] theorem tensorWeightSumEquiv_of (x : V) :
    ((tensorWeightSumEquiv C wt hR (DirectSum.of Vs β x) : integralTensor wt) : TensorSpace wt) = x :=
  congrArg Subtype.val (joinWeights_of C wt hR β x)

private def sumWordEquiv
    (e : ∀ β : Multiset I, Ps β ≃ₛₗ[invLP.toRingHom] Vs β) :
    DirectSum (Multiset I) Ps ≃ₛₗ[invLP.toRingHom] DirectSum (Multiset I) Vs where
  toAddEquiv := DirectSum.congrAddEquiv (fun β => (e β).toAddEquiv)
  map_smul' r x := by
    ext β
    exact congrArg Subtype.val ((e β).map_smulₛₗ r (x β))

private theorem sumWordEquiv_of (e : ∀ β : Multiset I, Ps β ≃ₛₗ[invLP.toRingHom] Vs β)
    (x : P) : sumWordEquiv Λ C hQ wt hR e (DirectSum.of Ps β x) = DirectSum.of Vs β (e β x) :=
  DirectSum.map_of _ _ _

/-- A Laurent-semilinear isomorphism on the full integral Grothendieck group
sends every divided projective class to its ordered tensor vector exactly when
the finite Laurent relations agree in every black content (Webster, §4.7,
Theorem 4.38). -/
theorem exists_tensorWordEquiv_iff :
    (∃ e : DirectSum (Multiset I) Ps ≃ₛₗ[invLP.toRingHom] integralTensor wt,
      ∀ w, e (tensorWordProjectiveClass Λ C hQ w) = integralWordVector (C := C) wt w) ↔
      ∀ β : Multiset I, SameWordRelations Λ C hQ wt hR β := by
  constructor
  · rintro ⟨e,he⟩ β a
    let p := DirectSum.lof LP _ Ps β
    let v := weightInclusion C wt hR β
    have hw (w : TensorWordAt ℓ β) : e (p (projectiveWordAt Λ C hQ β w)) = v (vectorWordAt C wt hR β w) := by
      rcases w with ⟨w,rfl⟩
      exact he w
    have hs :
        e (p (a.sum (fun w c => c • projectiveWordAt Λ C hQ β w))) =
          v (a.sum (fun w c => LaurentPolynomial.invert c • vectorWordAt C wt hR β w)) := by
      unfold Finsupp.sum
      rw [map_sum p, map_sum e, map_sum v]
      apply Finset.sum_congr rfl
      intro w _
      rw [p.map_smul, e.map_smulₛₗ, v.map_smul, hw]
      rfl
    constructor
    · intro hz
      rw [hz, map_zero, map_zero] at hs
      exact Submodule.inclusion_injective _ (hs.symm.trans v.map_zero.symm)
    · intro hz
      rw [hz, map_zero] at hs
      exact DirectSum.of_injective (β := Ps) β ((e.injective (hs.trans e.map_zero.symm)).trans p.map_zero.symm)
  · intro rel
    choose e he using fun β => (exists_wordEquivAt_iff Λ C hQ wt hR β).mpr (rel β)
    let j := LinearEquiv.ofBijective (joinWeights C wt hR) (joinWeights_bijective C wt hR)
    refine ⟨(sumWordEquiv Λ C hQ wt hR e).trans j, fun w => ?_⟩
    change joinWeights C wt hR (sumWordEquiv Λ C hQ wt hR e (DirectSum.of Ps w.content.toMultiset _)) = _
    rw [sumWordEquiv_of, joinWeights_of]
    exact congrArg (weightInclusion C wt hR _) (he _ ⟨w,rfl⟩)

end Categorification.Stendhal.FirstWeight
