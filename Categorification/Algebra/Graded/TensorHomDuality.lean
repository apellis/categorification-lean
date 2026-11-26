/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Duality
import Categorification.Algebra.Graded.RightTwist

/-!
# Tensoring with a finitely generated projective module is a Hom functor

Let `A` be an algebra over a field `k`, `P` a finitely generated projective right `A`-module and
`N` a left `A`-module. Write `P^* = Hom_{A^op}(P, A)`, a left `A`-module through left
multiplication in `A`. The map

  `P ⊗_A N → Hom_A(P^*, N)`,   `p ⊗ n ↦ (g ↦ g(p) · n)`

is a bijection: for a dual basis `p = ∑ⱼ xⱼ gⱼ(p)` its inverse is `h ↦ ∑ⱼ xⱼ ⊗ h(gⱼ)`. For
graded `P` and `N` the map preserves degrees, where `P^*` carries the grading by degree of maps.
So the graded dimension of `P ⊗_A N` is that of the graded Hom space from the graded projective
module `P^*` into `N`.

This is used for the induction functors of Webster, arXiv:1309.3796v2, §4.6, on modules that
are not projective: the Hom spaces from a projective into an induced module are Hom spaces from
a fixed projective into the original module.

## Main definitions and results

* `tensorHomMap` : `P ⊗_A N → Hom_A(P^*, N)`, and `tensorHomMap_bijective`.
* `tensorHomMap_mem` : it preserves degrees.
* `tensorHomGradedEquiv` : the graded isomorphism, and `gdimPoly_balancedGrading_eq` :
  `gdim (P ⊗_A N) = gdim HOM(P^*, N)`.
* `dualGProj 𝒜 ℙ` : `P^*` as a finitely generated graded projective left `A`-module.
-/

noncomputable section

namespace Categorification.Graded

open MulOpposite BalancedTensor DirectSum

section Ungraded

variable {k : Type*} [Field k] {A : Type*} [Ring A] [Algebra k A]
  {P : Type*} [AddCommGroup P] [Module k P] [Module Aᵐᵒᵖ P] [IsScalarTower k Aᵐᵒᵖ P]
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- The value `g ↦ g(p) · n` of `p ⊗ n`. -/
def tensorHomValue (p : P) (n : N) : (P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ) →ₗ[A] N where
  toFun g := unop (g p) • n
  map_add' g g' := by rw [LinearMap.add_apply, unop_add, add_smul]
  map_smul' a g := by
    change unop (op (a * unop (g p))) • n = a • unop (g p) • n
    rw [unop_op, mul_smul]

@[simp] theorem tensorHomValue_apply (p : P) (n : N) (g : P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ) :
    tensorHomValue p n g = unop (g p) • n := rfl

variable (k A P N) in
/-- The bilinear map `(p, n) ↦ (g ↦ g(p) · n)`. -/
def tensorHomBil : P →ₗ[k] N →ₗ[k] ((P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ) →ₗ[A] N) where
  toFun p :=
    { toFun := tensorHomValue p
      map_add' n n' := LinearMap.ext fun g => by simp
      map_smul' c n := LinearMap.ext fun g => by
        simp [smul_comm (unop (g p)) c n] }
  map_add' p p' := LinearMap.ext fun n => LinearMap.ext fun g => by simp [add_smul]
  map_smul' c p := LinearMap.ext fun n => LinearMap.ext fun g => by
    simp only [tensorHomValue_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.map_smul_of_tower,
      unop_smul, RingHom.id_apply, LinearMap.smul_apply]
    rw [smul_assoc]

variable (k A P N) in
/-- **The tensor–Hom map** `P ⊗_A N → Hom_A(P^*, N)`, `p ⊗ n ↦ (g ↦ g(p) · n)`. -/
def tensorHomMap : BalancedTensor k k A P N →ₗ[k] ((P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ) →ₗ[A] N) :=
  lift (tensorHomBil k A P N) fun p a n => LinearMap.ext fun g => by
    change unop (g (op a • p)) • n = unop (g p) • a • n
    rw [map_smul, smul_eq_mul, unop_mul, unop_op, mul_smul]

@[simp] theorem tensorHomMap_tmul (p : P) (n : N) (g : P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ) :
    tensorHomMap k A P N (tmul p n) g = unop (g p) • n := rfl

omit [Algebra k A] [IsScalarTower k Aᵐᵒᵖ P] [IsScalarTower k A N] in
private theorem sum_tmul' {ι : Type*} (s : Finset ι) (p : ι → P) (n : N) :
    (tmul (∑ j ∈ s, p j) n : BalancedTensor k k A P N) = ∑ j ∈ s, tmul (p j) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, add_tmul, ih]

/-- A dual basis `p = ∑ⱼ gⱼ(p) • xⱼ` of `P` expands every `g ∈ P^*` as `∑ⱼ g(xⱼ) • gⱼ`. -/
private theorem dual_eq_sum {m : ℕ} {x : Fin m → P} {f : Fin m → (P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ)}
    (hxf : ∀ p, ∑ j, f j p • x j = p) (g : P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ) :
    ∑ j, unop (g (x j)) • f j = g := LinearMap.ext fun p => by
  rw [LinearMap.sum_apply]
  conv_rhs => rw [← hxf p, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- The tensor–Hom map is bijective for finitely generated projective `P`. -/
theorem tensorHomMap_bijective [Module.Finite Aᵐᵒᵖ P] [Module.Projective Aᵐᵒᵖ P] :
    Function.Bijective (tensorHomMap k A P N) := by
  obtain ⟨m, x, f, hxf⟩ := exists_dualBasis (A := Aᵐᵒᵖ) (M := P)
  let inv : ((P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ) →ₗ[A] N) → BalancedTensor k k A P N :=
    fun h => ∑ j, tmul (x j) (h (f j))
  refine Function.bijective_iff_has_inverse.2 ⟨inv, fun t => ?_, fun h => ?_⟩
  · induction t using BalancedTensor.induction_on with
    | zero => simp [inv]
    | tmul p n =>
      change ∑ j, tmul (x j) (unop (f j p) • n) = tmul p n
      simp_rw [← op_smul_tmul, op_unop]
      rw [← sum_tmul', hxf p]
    | add t t' ht ht' =>
      change ∑ j, tmul (x j) (tensorHomMap k A P N (t + t') (f j)) = t + t'
      simp only [map_add, LinearMap.add_apply, tmul_add, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) ht ht'
  · refine LinearMap.ext fun g => ?_
    change tensorHomMap k A P N (∑ j, tmul (x j) (h (f j))) g = h g
    rw [map_sum, LinearMap.sum_apply]
    simp only [tensorHomMap_tmul]
    conv_rhs => rw [← dual_eq_sum hxf g, map_sum]
    simp only [map_smul]

end Ungraded

section Graded

universe u

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A] (𝒜 : ℤ → Submodule k A)
  [GradedAlgebra 𝒜]
  {P : Type u} [AddCommGroup P] [Module k P] [Module Aᵐᵒᵖ P] [IsScalarTower k Aᵐᵒᵖ P]
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  (ℙ : ℤ → Submodule k P) [Decomposition ℙ] [SetLike.GradedSMul (oppositeGrade 𝒜) ℙ]
  (𝒩 : ℤ → Submodule k N) [Decomposition 𝒩] [SetLike.GradedSMul 𝒜 𝒩]

/-- The grading of `P^* = Hom_{A^op}(P, A)` by degree of maps. -/
abbrev dualGrade : ℤ → Submodule k (P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ) := homGrade Aᵐᵒᵖ ℙ (oppositeGrade 𝒜)

instance gradedSMul_dualGrade : SetLike.GradedSMul 𝒜 (dualGrade 𝒜 ℙ) where
  smul_mem i j a g ha hg e y hy := by
    change op (a * unop (g y)) ∈ oppositeGrade 𝒜 (e + (i +ᵥ j))
    change a * unop (g y) ∈ 𝒜 (e + (i +ᵥ j))
    rw [vadd_eq_add, show e + (i + j) = i + (e + j) by abel]
    exact SetLike.GradedMul.mul_mem ha (hg hy)

omit [GradedAlgebra 𝒜] [IsScalarTower k Aᵐᵒᵖ P] [Decomposition ℙ] in
theorem op_smul_mem_of_mem ⦃i l : ℤ⦄ ⦃p : P⦄ ⦃a : A⦄ (hp : p ∈ ℙ i) (ha : a ∈ 𝒜 l) :
    op a • p ∈ ℙ (i + l) := by
  rw [add_comm]
  exact SetLike.GradedSMul.smul_mem (A := oppositeGrade 𝒜)
    (show op a ∈ oppositeGrade 𝒜 l from ha) hp

omit [GradedAlgebra 𝒜] [Decomposition ℙ] [Decomposition 𝒩]
  [SetLike.GradedSMul (oppositeGrade 𝒜) ℙ] in
/-- The tensor–Hom map preserves degrees. -/
theorem tensorHomMap_mem ⦃d : ℤ⦄ ⦃t : BalancedTensor k k A P N⦄
    (ht : t ∈ balancedGrading k A ℙ 𝒩 d) :
    tensorHomMap k A P N t ∈ homGrade A (dualGrade 𝒜 ℙ) 𝒩 d := by
  refine balancedGrading_map_mem (homGrade A (dualGrade 𝒜 ℙ) 𝒩) _ ?_ ht
  intro i j p n hp hn e g hg
  rw [tensorHomMap_tmul, show e + (i + j) = i + e + j by abel]
  exact SetLike.GradedSMul.smul_mem (A := 𝒜) (show unop (g p) ∈ 𝒜 (i + e) from hg hp) hn

variable [Module.Finite Aᵐᵒᵖ P]

instance decomposition_dualGrade : Decomposition (dualGrade 𝒜 ℙ) :=
  (isInternal_homGrade (oppositeGrade 𝒜) ℙ (oppositeGrade 𝒜)).chooseDecomposition

variable [Module.Projective Aᵐᵒᵖ P]

omit [IsScalarTower k Aᵐᵒᵖ P] in
private theorem exists_dual_split :
    ∃ (m : ℕ) (s : (P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ) →ₗ[A] (Fin m → A))
      (t : (Fin m → A) →ₗ[A] (P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ)), t ∘ₗ s = LinearMap.id := by
  obtain ⟨m, x, f, hxf⟩ := exists_dualBasis (A := Aᵐᵒᵖ) (M := P)
  refine ⟨m,
    { toFun := fun g j => unop (g (x j))
      map_add' := fun g g' => funext fun j => by simp
      map_smul' := fun a g => funext fun j => by
        change unop (op (a * unop (g (x j)))) = a * unop (g (x j))
        rw [unop_op] },
    Fintype.linearCombination A f, LinearMap.ext fun g => ?_⟩
  change Fintype.linearCombination A f (fun j => unop (g (x j))) = g
  rw [Fintype.linearCombination_apply]
  exact dual_eq_sum hxf g

instance : Module.Finite A (P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ) := by
  obtain ⟨m, s, t, hts⟩ := exists_dual_split (A := A) (P := P)
  exact Module.Finite.of_surjective t fun g => ⟨s g, LinearMap.congr_fun hts g⟩

instance : Module.Projective A (P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ) := by
  obtain ⟨m, s, t, hts⟩ := exists_dual_split (A := A) (P := P)
  exact Module.Projective.of_split s t hts

/-- **The graded tensor–Hom isomorphism** `P ⊗_A N ≅ HOM_A(P^*, N)`. -/
def tensorHomGradedEquiv :
    letI := balancedDecomposition (B := k) (ℳ := ℙ) (𝒩 := 𝒩) 𝒜 (op_smul_mem_of_mem 𝒜 ℙ)
    letI := (isInternal_homGrade 𝒜 (dualGrade 𝒜 ℙ) 𝒩).chooseDecomposition
    balancedGrading k A ℙ 𝒩 ≃ᵍ[k] homGrade A (dualGrade 𝒜 ℙ) 𝒩 :=
  letI := balancedDecomposition (B := k) (ℳ := ℙ) (𝒩 := 𝒩) 𝒜 (op_smul_mem_of_mem 𝒜 ℙ)
  letI := (isInternal_homGrade 𝒜 (dualGrade 𝒜 ℙ) 𝒩).chooseDecomposition
  GradedEquiv.ofPreserves (LinearEquiv.ofBijective _ tensorHomMap_bijective)
    fun _ _ ht => tensorHomMap_mem 𝒜 ℙ 𝒩 ht

/-- **`gdim (P ⊗_A N) = gdim HOM(P^*, N)`** for a finitely generated graded projective right
module `P`. -/
theorem gdimPoly_balancedGrading_eq :
    gdimPoly (balancedGrading k A ℙ 𝒩) = gdimPoly (homGrade A (dualGrade 𝒜 ℙ) 𝒩) :=
  gdimPoly_congr (tensorHomGradedEquiv 𝒜 ℙ 𝒩)

/-- `P^*` as a finitely generated graded projective left module. -/
def dualGProj : GProj 𝒜 where
  carrier := P →ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ
  grading := dualGrade 𝒜 ℙ

end Graded

end Categorification.Graded
