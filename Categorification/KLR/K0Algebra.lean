/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.InductionAlgebra

/-!
# The Grothendieck algebra `K₀(R)` (KL I, Proposition 3.1)

Khovanov–Lauda I (arXiv:0803.4121v2), §3.1, **Proposition 3.1** (`K₀` part): the maps
`[Ind_{ν,ν'}] : K₀(R(ν)) × K₀(R(ν')) → K₀(R(ν + ν'))` make
`K₀(R) = ⨁_{ν ∈ ℕ[I]} K₀(R(ν))` an associative unital `ℤ[q, q⁻¹]`-algebra with unit `[R(0)]`.

## Main definitions and results

* `GradingDatum.K0cast h` : the identification `K₀(R(μ)) ≅ K₀(R(μ'))` for `h : μ = μ'`;
  `K0cast_of_linearEquiv` computes it on classes from an isomorphism of modules which is
  semilinear along `castKLR` and degree-preserving.
* `GradingDatum.indK0_assoc` : `[Ind] ([Ind] (x ⊗ y) ⊗ z) = [Ind] (x ⊗ [Ind] (y ⊗ z))` (after
  `K0cast`), for all `x`, `y`, `z` (not only classes of `P_i`).
* `GradingDatum.indK0_one_left`, `GradingDatum.indK0_one_right` : `[R(0)]` is a two-sided unit.
* `GradingDatum.K0R G` : `⨁_ν K₀(R(ν))`, with its `DirectSum.GRing` and
  `DirectSum.GAlgebra (LaurentPolynomial ℤ)` structures, hence a `Ring` and an
  `Algebra (LaurentPolynomial ℤ)` (Mathlib's `DirectSum.ring`, `DirectSum.instAlgebra`), whose
  multiplication on homogeneous components is `[Ind]` (`K0R_of_mul_of`).
-/

noncomputable section

namespace Categorification.KLR

open scoped TensorProduct
open KLRAlgebra MulOpposite Graded

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}

namespace GradingDatum

variable (G : GradingDatum Q)

/-! ### Transport of `K₀` along equalities of weights -/

section Cast

variable {μ μ' : Multiset I}

/-- The identification `K₀(R(μ)) ≅ K₀(R(μ'))` for `μ = μ'`. -/
def K0cast (h : μ = μ') : K0 (G.grade μ) →+ K0 (G.grade μ') := by
  subst h; exact AddMonoidHom.id _

@[simp] theorem K0cast_rfl (x : K0 (G.grade μ)) : G.K0cast rfl x = x := rfl

theorem K0cast_trans {μ'' : Multiset I} (h : μ = μ') (h' : μ' = μ'') (x : K0 (G.grade μ)) :
    G.K0cast h' (G.K0cast h x) = G.K0cast (h.trans h') x := by
  subst h; subst h'; rfl

/-- The graded monoid element `⟨μ, x⟩` equals `⟨μ', K0cast h x⟩`. -/
theorem gradedMonoid_mk_K0cast (h : μ = μ') (x : K0 (G.grade μ)) :
    (GradedMonoid.mk μ x : GradedMonoid fun ν => K0 (G.grade ν)) =
      GradedMonoid.mk μ' (G.K0cast h x) := by
  subst h; rfl

/-- `K0cast` on classes: an isomorphism `X ≅ Y` of the underlying `k`-modules which is
semilinear along `castKLR : R(μ) ≃ R(μ')` and degree-preserving identifies `[X]` with `[Y]`. -/
theorem K0cast_of_linearEquiv (h : μ = μ') (X : GProj (G.grade μ)) (Y : GProj (G.grade μ'))
    (φ : X.carrier ≃ₗ[k] Y.carrier)
    (hφ : ∀ (b : KLRAlgebra k Q μ) (x : X.carrier), φ (b • x) = castKLR Q h b • φ x)
    (hgr : ∀ ⦃d : ℤ⦄ ⦃x : X.carrier⦄, x ∈ X.grading d → φ x ∈ Y.grading d) :
    G.K0cast h (K0.of X) = K0.of Y := by
  subst h
  rw [K0cast_rfl]
  exact K0.of_eq_of_iso (GradedEquiv.ofPreserves
    (φ.toAddEquiv.toLinearEquiv fun b x => (hφ b x).trans (by rw [castKLR_rfl]; rfl))
    (fun _ _ hx => hgr hx))

end Cast

/-! ### Gradings of the associativity and unit isomorphisms -/

section Gradings

variable {ν ν' ν'' : Multiset I}
  {N₁ : Type*} [AddCommGroup N₁] [Module k N₁] [Module (KLRAlgebra k Q ν) N₁]
    [IsScalarTower k (KLRAlgebra k Q ν) N₁]
  {N₂ : Type*} [AddCommGroup N₂] [Module k N₂] [Module (KLRAlgebra k Q ν') N₂]
    [IsScalarTower k (KLRAlgebra k Q ν') N₂]
  {N₃ : Type*} [AddCommGroup N₃] [Module k N₃] [Module (KLRAlgebra k Q ν'') N₃]
    [IsScalarTower k (KLRAlgebra k Q ν'') N₃]
  (𝒩₁ : ℤ → Submodule k N₁) (𝒩₂ : ℤ → Submodule k N₂) (𝒩₃ : ℤ → Submodule k N₃)

theorem oneBimod_mem (μ μ' : Multiset I) : oneBimod Q μ μ' ∈ G.bimodGrading μ μ' 0 :=
  G.oneConcat_mem_grade

theorem assocBimod_mem_grade {i i' : ℤ} {r : IndBimod Q (ν + ν') ν''} {r' : IndBimod Q ν ν'}
    (hr : r ∈ G.bimodGrading (ν + ν') ν'' i) (hr' : r' ∈ G.bimodGrading ν ν' i') :
    assocBimod Q ν ν' ν'' r r' ∈ G.bimodGrading ν (ν' + ν'') (i + i') := by
  show castKLR Q _ _ ∈ G.grade _ _
  refine G.castKLR_mem_grade _ ?_
  have := SetLike.GradedMul.mul_mem (A := G.grade (ν + ν' + ν'')) hr
    (G.concat_tmul_mem_grade (i := i') (j := 0) hr' (SetLike.GradedOne.one_mem))
  rwa [add_zero] at this

set_option maxHeartbeats 800000 in
/-- The associativity isomorphism is degree-preserving. -/
theorem assocFwd_mem_grading ⦃d : ℤ⦄ ⦃x : AssocL Q ν ν' ν'' N₁ N₂ N₃⦄
    (hx : x ∈ G.indGrading (ν + ν') ν''
      (ExtTensor.grading (G.indGrading ν ν' (ExtTensor.grading 𝒩₁ 𝒩₂)) 𝒩₃) d) :
    assocFwd Q ν ν' ν'' N₁ N₂ N₃ x ∈ G.indGrading ν (ν' + ν'')
      (ExtTensor.grading 𝒩₁ (G.indGrading ν' ν'' (ExtTensor.grading 𝒩₂ 𝒩₃))) d := by
  refine balancedGrading_map_mem (B := KLRAlgebra k Q (ν + ν' + ν''))
    (ℳ := G.bimodGrading (ν + ν') ν'')
    (G.indGrading ν (ν' + ν'') (ExtTensor.grading 𝒩₁ (G.indGrading ν' ν''
      (ExtTensor.grading 𝒩₂ 𝒩₃)))) (assocFwd Q ν ν' ν'' N₁ N₂ N₃) ?_ hx
  intro i j m z hm hz
  rw [assocFwd, BalancedTensor.lift_tmul]
  refine ExtTensor.grading_map_mem (G.indGrading ν ν' (ExtTensor.grading 𝒩₁ 𝒩₂)) 𝒩₃ (fun j => G.indGrading ν (ν' + ν'')
    (ExtTensor.grading 𝒩₁ (G.indGrading ν' ν'' (ExtTensor.grading 𝒩₂ 𝒩₃))) (i + j))
    (assocOuterBil Q ν ν' ν'' N₁ N₂ N₃ m) ?_ hz
  intro j₁ j₂ y n₃ hy hn₃
  rw [assocOuterBil_apply, ExtTensor.lift_tmul, assocOuterInner_apply]
  refine balancedGrading_map_mem (B := KLRAlgebra k Q (ν + ν')) (ℳ := G.bimodGrading ν ν')
    (fun j₁ => G.indGrading ν (ν' + ν'')
      (ExtTensor.grading 𝒩₁ (G.indGrading ν' ν'' (ExtTensor.grading 𝒩₂ 𝒩₃))) (i + (j₁ + j₂)))
    (assocMid Q ν ν' ν'' N₁ N₂ N₃ m n₃) ?_ hy
  intro i' j₁' r' n hr' hn
  rw [assocMid_tmul]
  have h1 := G.assocBimod_mem_grade hm hr'
  have h2 : assocJ Q ν' ν'' N₁ N₂ N₃ (ExtTensor.tmul n n₃) ∈
      ExtTensor.grading 𝒩₁ (G.indGrading ν' ν'' (ExtTensor.grading 𝒩₂ 𝒩₃)) (j₁' + j₂) := by
    refine ExtTensor.grading_map_mem 𝒩₁ 𝒩₂
      (fun j => ExtTensor.grading 𝒩₁ (G.indGrading ν' ν'' (ExtTensor.grading 𝒩₂ 𝒩₃)) (j + j₂))
      ((assocJ Q ν' ν'' N₁ N₂ N₃).comp (ExtTensor.mkRight n₃)) ?_ hn
    intro a b n₁ n₂ h₁ h₂
    have := ExtTensor.tmul_mem_grading h₁ (tmul_mem_balancedGrading
      (B := KLRAlgebra k Q (ν' + ν'')) (A := TensorKLR Q ν' ν'') (G.oneBimod_mem ν' ν'')
      (ExtTensor.tmul_mem_grading h₂ hn₃))
    have e : a + (0 + (b + j₂)) = a + b + j₂ := by abel
    rw [e] at this
    exact this
  have e : i + i' + (j₁' + j₂) = i + (i' + j₁' + j₂) := by abel
  have h3 := tmul_mem_balancedGrading (B := KLRAlgebra k Q (ν + (ν' + ν'')))
    (A := TensorKLR Q ν (ν' + ν'')) h1 h2
  rw [e] at h3
  exact h3

variable {ν : Multiset I} {N : Type*} [AddCommGroup N] [Module k N]
  [Module (KLRAlgebra k Q ν) N] [IsScalarTower k (KLRAlgebra k Q ν) N]
  (𝒩 : ℤ → Submodule k N) [SetLike.GradedSMul (G.grade ν) 𝒩]

/-- The left unit isomorphism is degree-preserving. -/
theorem unitLFwd_mem_grading ⦃d : ℤ⦄ ⦃x : UnitL Q ν N⦄
    (hx : x ∈ G.indGrading 0 ν (ExtTensor.grading (G.grade 0) 𝒩) d) :
    unitLFwd Q ν N x ∈ 𝒩 d := by
  refine balancedGrading_map_mem (B := KLRAlgebra k Q (0 + ν))
    (ℳ := G.bimodGrading 0 ν) _ (unitLFwd Q ν N) ?_ hx
  intro i j m z hm hz
  rw [unitLFwd, BalancedTensor.lift_tmul]
  refine ExtTensor.grading_map_mem _ _ (fun j => 𝒩 (i + j)) (unitLBil Q ν N m) ?_ hz
  intro a b a' n ha hn
  rw [unitLBil_tmul]
  have h1 : castKLR Q (zero_add ν) ((m : KLRAlgebra k Q (0 + ν)) * concat Q 0 ν (a' ⊗ₜ 1)) ∈
      G.grade ν (i + a) := by
    refine G.castKLR_mem_grade _ ?_
    have := SetLike.GradedMul.mul_mem (A := G.grade (0 + ν)) hm
      (G.concat_tmul_mem_grade (i := a) (j := 0) ha (SetLike.GradedOne.one_mem))
    rwa [add_zero] at this
  have := SetLike.GradedSMul.smul_mem (A := G.grade ν) h1 hn
  show _ ∈ 𝒩 (i + (a + b))
  rwa [vadd_eq_add, add_assoc] at this

/-- The right unit isomorphism is degree-preserving. -/
theorem unitRFwd_mem_grading ⦃d : ℤ⦄ ⦃x : UnitR Q ν N⦄
    (hx : x ∈ G.indGrading ν 0 (ExtTensor.grading 𝒩 (G.grade 0)) d) :
    unitRFwd Q ν N x ∈ 𝒩 d := by
  refine balancedGrading_map_mem (B := KLRAlgebra k Q (ν + 0))
    (ℳ := G.bimodGrading ν 0) _ (unitRFwd Q ν N) ?_ hx
  intro i j m z hm hz
  rw [unitRFwd, BalancedTensor.lift_tmul]
  refine ExtTensor.grading_map_mem _ _ (fun j => 𝒩 (i + j)) (unitRBil Q ν N m) ?_ hz
  intro a b n a' hn ha
  rw [unitRBil_tmul]
  have h1 : castKLR Q (add_zero ν) ((m : KLRAlgebra k Q (ν + 0)) * concat Q ν 0 (1 ⊗ₜ a')) ∈
      G.grade ν (i + b) := by
    refine G.castKLR_mem_grade _ ?_
    have := SetLike.GradedMul.mul_mem (A := G.grade (ν + 0)) hm
      (G.concat_tmul_mem_grade (i := 0) (j := b) (SetLike.GradedOne.one_mem) ha)
    rwa [zero_add] at this
  have := SetLike.GradedSMul.smul_mem (A := G.grade ν) h1 hn
  show _ ∈ 𝒩 (i + (a + b))
  rwa [vadd_eq_add, add_right_comm, add_assoc] at this

end Gradings

/-! ### Associativity and unitality in `K₀` -/

section K0

variable {ν ν' ν'' : Multiset I}

theorem K0cast_indProj_assoc (P : GProj (G.grade ν)) (P' : GProj (G.grade ν'))
    (P'' : GProj (G.grade ν'')) :
    G.K0cast (add_assoc ν ν' ν'') (K0.of (G.indProj (G.indProj P P') P'')) =
      K0.of (G.indProj P (G.indProj P' P'')) :=
  G.K0cast_of_linearEquiv _ _ _ (assocEquiv Q ν ν' ν'' P.carrier P'.carrier P''.carrier)
    (fun b x => assocEquiv_smul P.carrier P'.carrier P''.carrier b x)
    (fun _ _ hx => G.assocFwd_mem_grading P.grading P'.grading P''.grading hx)

/-- **Associativity of `[Ind]`** (KL I, Proposition 3.1): for all `x ∈ K₀(R(ν))`,
`y ∈ K₀(R(ν'))`, `z ∈ K₀(R(ν''))`, `(x y) z = x (y z)` (after identifying
`K₀(R((ν + ν') + ν'')) = K₀(R(ν + (ν' + ν'')))`). -/
theorem indK0_assoc (x : K0 (G.grade ν)) (y : K0 (G.grade ν')) (z : K0 (G.grade ν'')) :
    G.K0cast (add_assoc ν ν' ν'') (G.indK0 (ν + ν') ν'' (G.indK0 ν ν' x y) z) =
      G.indK0 ν (ν' + ν'') x (G.indK0 ν' ν'' y z) := by
  induction x using K0.induction_on with
  | of P =>
    induction y using K0.induction_on with
    | of P' =>
      induction z using K0.induction_on with
      | of P'' =>
        rw [indK0_of, indK0_of, indK0_of, indK0_of]
        exact G.K0cast_indProj_assoc P P' P''
      | zero => simp only [map_zero]
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | neg z hz => simp only [map_neg, hz]
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
    | neg y hy => simp only [map_neg, LinearMap.neg_apply, hy]
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, LinearMap.neg_apply, hx]

/-- **Left unitality of `[Ind]`**: `[R(0)] x = x`. -/
theorem indK0_one_left (x : K0 (G.grade ν)) :
    G.K0cast (zero_add ν) (G.indK0 0 ν (K0.of (GProj.regular (G.grade 0))) x) = x := by
  induction x using K0.induction_on with
  | of P =>
    rw [indK0_of]
    exact G.K0cast_of_linearEquiv _ _ _ (unitLEquiv Q ν P.carrier)
      (fun b x => unitLEquiv_smul P.carrier b x)
      (fun _ _ hx => G.unitLFwd_mem_grading P.grading hx)
  | zero => simp only [map_zero]
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | neg x hx => simp only [map_neg, hx]

/-- **Right unitality of `[Ind]`**: `x [R(0)] = x`. -/
theorem indK0_one_right (x : K0 (G.grade ν)) :
    G.K0cast (add_zero ν) (G.indK0 ν 0 x (K0.of (GProj.regular (G.grade 0)))) = x := by
  induction x using K0.induction_on with
  | of P =>
    rw [indK0_of]
    exact G.K0cast_of_linearEquiv _ _ _ (unitREquiv Q ν P.carrier)
      (fun b x => unitREquiv_smul P.carrier b x)
      (fun _ _ hx => G.unitRFwd_mem_grading P.grading hx)
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | neg x hx => simp only [map_neg, LinearMap.neg_apply, hx]

end K0

/-! ### The algebra `K₀(R) = ⨁_ν K₀(R(ν))` -/

section K0R

theorem K0cast_smul {μ μ' : Multiset I} (h : μ = μ') (p : LaurentPolynomial ℤ)
    (x : K0 (G.grade μ)) : G.K0cast h (p • x) = p • G.K0cast h x := by
  subst h; rfl

/-- The family `ν ↦ K₀(R(ν))`. -/
abbrev K0fam : Multiset I → Type _ := fun ν => K0 (G.grade ν)

/-- The unit `[R(0)] ∈ K₀(R(0))`. -/
def K0one : K0 (G.grade (0 : Multiset I)) := K0.of (GProj.regular (G.grade 0))

instance gMulK0 : GradedMonoid.GMul G.K0fam where
  mul {ν ν'} x y := G.indK0 ν ν' x y

instance gOneK0 : GradedMonoid.GOne G.K0fam where
  one := G.K0one

theorem gMul_def {ν ν' : Multiset I} (x : K0 (G.grade ν)) (y : K0 (G.grade ν')) :
    GradedMonoid.GMul.mul (A := G.K0fam) x y = G.indK0 ν ν' x y :=
  rfl

theorem mk_mul_mk {ν ν' : Multiset I} (x : K0 (G.grade ν)) (y : K0 (G.grade ν')) :
    GradedMonoid.mk (A := G.K0fam) ν x * GradedMonoid.mk ν' y =
      GradedMonoid.mk (A := G.K0fam) (ν + ν') (G.indK0 ν ν' x y) := rfl

theorem mk_K0cast {μ μ' : Multiset I} (h : μ = μ') (x : K0 (G.grade μ)) :
    GradedMonoid.mk (A := G.K0fam) μ x = GradedMonoid.mk (A := G.K0fam) μ' (G.K0cast h x) :=
  G.gradedMonoid_mk_K0cast h x

theorem one_mk_mul {ν : Multiset I} (x : K0 (G.grade ν)) :
    (1 : GradedMonoid G.K0fam) * GradedMonoid.mk ν x = GradedMonoid.mk ν x := by
  show GradedMonoid.mk (A := G.K0fam) (0 + ν) (G.indK0 0 ν G.K0one x) = _
  rw [G.mk_K0cast (zero_add ν), K0one, indK0_one_left]

theorem mk_mul_one {ν : Multiset I} (x : K0 (G.grade ν)) :
    GradedMonoid.mk (A := G.K0fam) ν x * (1 : GradedMonoid G.K0fam) = GradedMonoid.mk ν x := by
  show GradedMonoid.mk (A := G.K0fam) (ν + 0) (G.indK0 ν 0 x G.K0one) = _
  rw [G.mk_K0cast (add_zero ν), K0one, indK0_one_right]

instance gMonoidK0 : GradedMonoid.GMonoid G.K0fam where
  one_mul a := by obtain ⟨ν, x⟩ := a; exact G.one_mk_mul x
  mul_one a := by obtain ⟨ν, x⟩ := a; exact G.mk_mul_one x
  mul_assoc a b c := by
    obtain ⟨ν, x⟩ := a
    obtain ⟨ν', y⟩ := b
    obtain ⟨ν'', z⟩ := c
    show GradedMonoid.mk (A := G.K0fam) ν x * GradedMonoid.mk ν' y * GradedMonoid.mk ν'' z =
      GradedMonoid.mk (A := G.K0fam) ν x * (GradedMonoid.mk ν' y * GradedMonoid.mk ν'' z)
    rw [mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_mul_mk, G.mk_K0cast (add_assoc ν ν' ν''),
      indK0_assoc]

instance gRingK0 : DirectSum.GRing G.K0fam where
  mul_zero {ν ν'} x := by rw [gMul_def, map_zero]
  zero_mul {ν ν'} y := by rw [gMul_def, map_zero, LinearMap.zero_apply]
  mul_add {ν ν'} x y y' := by rw [gMul_def, gMul_def, gMul_def, map_add]
  add_mul {ν ν'} x x' y := by rw [gMul_def, gMul_def, gMul_def, map_add, LinearMap.add_apply]
  natCast n := n • G.K0one
  natCast_zero := zero_smul _ _
  natCast_succ n := succ_nsmul _ n
  intCast n := n • G.K0one
  intCast_ofNat n := natCast_zsmul _ n
  intCast_negSucc_ofNat n := negSucc_zsmul _ n

instance gAlgebraK0 : DirectSum.GAlgebra (LaurentPolynomial ℤ) G.K0fam where
  toFun :=
    { toFun := fun p => p • G.K0one
      map_zero' := zero_smul _ _
      map_add' := fun p p' => add_smul _ _ _ }
  map_one := one_smul _ _
  map_mul r s := by
    show GradedMonoid.mk (A := G.K0fam) 0 ((r * s) • G.K0one) = GradedMonoid.mk (0 + 0)
      (G.indK0 0 0 (r • G.K0one) (s • G.K0one))
    rw [G.mk_K0cast (zero_add (0 : Multiset I))]
    simp only [LinearMap.map_smul₂, LinearMap.map_smul, LinearMap.smul_apply, K0cast_smul]
    rw [K0one, indK0_one_left, mul_smul]
  commutes r x := by
    obtain ⟨ν, x⟩ := x
    show GradedMonoid.mk (A := G.K0fam) (0 + ν) (G.indK0 0 ν (r • G.K0one) x) =
      GradedMonoid.mk (ν + 0) (G.indK0 ν 0 x (r • G.K0one))
    rw [G.mk_K0cast (zero_add ν), G.mk_K0cast (add_zero ν)]
    simp only [LinearMap.map_smul₂, LinearMap.map_smul, LinearMap.smul_apply, K0cast_smul]
    rw [K0one, indK0_one_left, indK0_one_right]
  smul_def r x := by
    obtain ⟨ν, x⟩ := x
    show GradedMonoid.mk (A := G.K0fam) ν (r • x) =
      GradedMonoid.mk (0 + ν) (G.indK0 0 ν (r • G.K0one) x)
    rw [G.mk_K0cast (zero_add ν)]
    simp only [LinearMap.map_smul₂, LinearMap.smul_apply, K0cast_smul]
    rw [K0one, indK0_one_left]

/-- **The Grothendieck algebra** `K₀(R) = ⨁_{ν ∈ ℕ[I]} K₀(R(ν))` (KL I, §3.1): an associative
unital `ℤ[q, q⁻¹]`-algebra (`inferInstance : Algebra (LaurentPolynomial ℤ) G.K0R`) whose
product on homogeneous components is `[Ind]` (`K0R_of_mul_of`) and whose unit is `[R(0)]`
(`K0R_one`). -/
abbrev K0R : Type _ := DirectSum (Multiset I) G.K0fam

example : Ring G.K0R := inferInstance

example : Algebra (LaurentPolynomial ℤ) G.K0R := inferInstance

/-- The product on `K₀(R)` of homogeneous elements is `[Ind]`. -/
theorem K0R_of_mul_of {ν ν' : Multiset I} (x : K0 (G.grade ν)) (y : K0 (G.grade ν')) :
    (DirectSum.of G.K0fam ν x * DirectSum.of G.K0fam ν' y : G.K0R) =
      DirectSum.of G.K0fam (ν + ν') (G.indK0 ν ν' x y) :=
  DirectSum.of_mul_of (A := G.K0fam) x y

/-- The unit of `K₀(R)` is `[R(0)]`. -/
theorem K0R_one : (1 : G.K0R) = DirectSum.of G.K0fam 0 (K0.of (GProj.regular (G.grade 0))) :=
  rfl

/-- `[P] [P'] = [Ind (P ⊠ P')]` in `K₀(R)`. -/
theorem K0R_of_of_mul_of_of {ν ν' : Multiset I} (P : GProj (G.grade ν))
    (P' : GProj (G.grade ν')) :
    (DirectSum.of G.K0fam ν (K0.of P) * DirectSum.of G.K0fam ν' (K0.of P') : G.K0R) =
      DirectSum.of G.K0fam (ν + ν') (K0.of (G.indProj P P')) := by
  rw [K0R_of_mul_of, indK0_of]

/-- The `ℤ[q, q⁻¹]`-algebra structure: `p • x = (p • [R(0)]) * x`. -/
theorem K0R_algebraMap (p : LaurentPolynomial ℤ) :
    algebraMap (LaurentPolynomial ℤ) G.K0R p =
      DirectSum.of G.K0fam 0 (p • K0.of (GProj.regular (G.grade 0))) :=
  rfl

end K0R

end GradingDatum

end Categorification.KLR

end
