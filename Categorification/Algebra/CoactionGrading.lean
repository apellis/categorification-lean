/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Gradings from coactions

A grading of a `k`-algebra `A` by an additive monoid `ι` is the same thing as a
coaction of the group-like bialgebra `k[ι]` on `A`, i.e. an algebra homomorphism

`Δ : A →ₐ[k] A[ι]`   (`A[ι] = AddMonoidAlgebra A ι`)

which is counital (`∑_d (Δ a)_d = a`) and coassociative
(`Δ ((Δ a)_d) = single d ((Δ a)_d)` for all `d`). Given such a `Δ`, the degree `d`
component is

`grade Δ d = {a | Δ a = single d a}`.

This is a convenient way to *construct* gradings on algebras given by generators and
relations (such as `RingQuot`s of free algebras): `Δ` is defined on generators, and
checking that it respects the relations amounts to checking that the relations are
homogeneous.

## Main definitions and results

* `CoactionGrading.grade Δ d` : the submodule `{a | Δ a = single d a}`; see `mem_grade`.
* `CoactionGrading.Counit Δ`, `CoactionGrading.Coassoc Δ` : the coaction axioms.
* `CoactionGrading.gradedAlgebra Δ hε hco` : the `GradedAlgebra (grade Δ)` structure.
* `CoactionGrading.decompose_apply` : the degree `d` component of `a` is `(Δ a) d`.
* `CoactionGrading.homogeneousSubalgebra Δ` : the subalgebra `⨆ d, grade Δ d`; if it is
  everything (e.g. because generators are sums of homogeneous elements), then `Δ` is
  automatically counital and coassociative (`counit_of_forall_mem`,
  `coassoc_of_forall_mem`).
-/

namespace Categorification.CoactionGrading

open AddMonoidAlgebra DirectSum

variable {k A ι : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [AddMonoid ι]

variable (Δ : A →ₐ[k] AddMonoidAlgebra A ι)

/-- The degree `d` part `{a | Δ a = single d a}` of the grading defined by a coaction `Δ`. -/
def grade (d : ι) : Submodule k A where
  carrier := {a | Δ a = single d a}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, ha, hb, single_add]
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_smul, ha, smul_single]

theorem mem_grade {d : ι} {a : A} : a ∈ grade Δ d ↔ Δ a = single d a := Iff.rfl

theorem one_mem_grade : (1 : A) ∈ grade Δ 0 := by
  rw [mem_grade, map_one, AddMonoidAlgebra.one_def]

theorem mul_mem_grade {d e : ι} {a b : A} (ha : a ∈ grade Δ d) (hb : b ∈ grade Δ e) :
    a * b ∈ grade Δ (d + e) := by
  rw [mem_grade] at *
  rw [map_mul, ha, hb, single_mul_single]

instance gradedMonoid : SetLike.GradedMonoid (grade Δ) where
  one_mem := one_mem_grade Δ
  mul_mem _ _ _ _ ha hb := mul_mem_grade Δ ha hb

/-- `Δ` is counital: the sum of the coefficients of `Δ a` is `a`. -/
def Counit : Prop := ∀ a : A, (Δ a).sum (fun _ b => b) = a

/-- `Δ` is coassociative: every coefficient `(Δ a) d` is homogeneous of degree `d`. -/
def Coassoc : Prop := ∀ (a : A) (d : ι), Δ (Δ a d) = single d (Δ a d)

variable [DecidableEq ι]

theorem apply_of_mem_grade {d e : ι} {a : A} (ha : a ∈ grade Δ d) :
    Δ a e = if d = e then a else 0 := by
  rw [ha, single_apply]

/-- `Δ` recovers the components of an element of the external direct sum. -/
theorem apply_coe (f : ⨁ d, grade Δ d) (d : ι) :
    Δ (DirectSum.coeAddMonoidHom (grade Δ) f) d = f d := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | of e x =>
    rw [DirectSum.coeAddMonoidHom_of, apply_of_mem_grade Δ x.2, DirectSum.coe_of_apply]
    split_ifs <;> rfl
  | add f g hf hg =>
    rw [map_add, map_add, Finsupp.add_apply, hf, hg, DirectSum.add_apply, Submodule.coe_add]

theorem coe_injective :
    Function.Injective (DirectSum.coeAddMonoidHom (grade Δ)) := by
  intro f g h
  ext d
  rw [← apply_coe Δ f d, ← apply_coe Δ g d, h]

variable {Δ}

/-- The decomposition `a ↦ ∑_d (Δ a)_d` attached to a counital coassociative coaction. -/
noncomputable def decomposition (hε : Counit Δ) (hco : Coassoc Δ) :
    DirectSum.Decomposition (grade Δ) where
  decompose' a := ∑ d ∈ (Δ a).support, DirectSum.of (fun d => grade Δ d) d ⟨Δ a d, hco a d⟩
  left_inv a := by
    simp only [map_sum, DirectSum.coeAddMonoidHom_of]
    exact hε a
  right_inv f := by
    apply coe_injective Δ
    simp only [map_sum, DirectSum.coeAddMonoidHom_of]
    exact hε _

/-- The graded algebra structure defined by a counital coassociative coaction. -/
noncomputable def gradedAlgebra (hε : Counit Δ) (hco : Coassoc Δ) : GradedAlgebra (grade Δ) :=
  { gradedMonoid Δ, decomposition hε hco with }

/-- The degree `d` component of `a` is the coefficient `(Δ a) d`. -/
theorem decompose_apply (hε : Counit Δ) (hco : Coassoc Δ) (a : A) (d : ι) :
    letI := gradedAlgebra hε hco
    (DirectSum.decompose (grade Δ) a d : A) = Δ a d := by
  letI := gradedAlgebra hε hco
  have h := apply_coe Δ (DirectSum.decompose (grade Δ) a) d
  rw [show DirectSum.coeAddMonoidHom (grade Δ) (DirectSum.decompose (grade Δ) a) = a from
    (DirectSum.decompose (grade Δ)).symm_apply_apply a] at h
  exact h.symm

variable (Δ)

/-! ### Elements that are sums of homogeneous elements -/

omit [DecidableEq ι] in
theorem iSup_grade_mul_mem {a b : A} (ha : a ∈ ⨆ d, grade Δ d) (hb : b ∈ ⨆ d, grade Δ d) :
    a * b ∈ ⨆ d, grade Δ d := by
  induction ha using Submodule.iSup_induction' with
  | mem d a ha =>
    induction hb using Submodule.iSup_induction' with
    | mem e b hb => exact Submodule.mem_iSup_of_mem (d + e) (mul_mem_grade Δ ha hb)
    | zero => simp
    | add b c _ _ hb hc => rw [mul_add]; exact Submodule.add_mem _ hb hc
  | zero => simp
  | add a c _ _ ha hc => rw [add_mul]; exact Submodule.add_mem _ ha hc

/-- The subalgebra `⨆ d, grade Δ d` of finite sums of homogeneous elements. -/
def homogeneousSubalgebra : Subalgebra k A where
  carrier := (⨆ d, grade Δ d : Submodule k A)
  mul_mem' ha hb := iSup_grade_mul_mem Δ ha hb
  add_mem' ha hb := Submodule.add_mem _ ha hb
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (Submodule.mem_iSup_of_mem 0 (one_mem_grade Δ))

omit [DecidableEq ι] in
theorem mem_homogeneousSubalgebra {a : A} :
    a ∈ homogeneousSubalgebra Δ ↔ a ∈ ⨆ d, grade Δ d := Iff.rfl

omit [DecidableEq ι] in
theorem mem_homogeneousSubalgebra_of_mem_grade {d : ι} {a : A} (ha : a ∈ grade Δ d) :
    a ∈ homogeneousSubalgebra Δ :=
  Submodule.mem_iSup_of_mem d ha

omit [DecidableEq ι] in
/-- If every element is a sum of homogeneous elements, `Δ` is counital. -/
theorem counit_of_forall_mem (h : ∀ a, a ∈ homogeneousSubalgebra Δ) : Counit Δ := by
  intro a
  have ha : a ∈ ⨆ d, grade Δ d := h a
  induction ha using Submodule.iSup_induction' with
  | mem d a ha => rw [ha, Finsupp.sum_single_index rfl]
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), ha, hb]

/-- If every element is a sum of homogeneous elements, `Δ` is coassociative. -/
theorem coassoc_of_forall_mem (h : ∀ a, a ∈ homogeneousSubalgebra Δ) : Coassoc Δ := by
  intro a
  have ha : a ∈ ⨆ d, grade Δ d := h a
  induction ha using Submodule.iSup_induction' with
  | mem d a ha =>
    intro e
    rw [apply_of_mem_grade Δ ha]
    split_ifs with hde
    · subst hde; exact ha
    · simp
  | zero => simp
  | add a b _ _ ha hb =>
    intro d
    rw [map_add, Finsupp.add_apply, map_add, ha, hb, single_add]

omit [DecidableEq ι] in
/-- A counital coassociative coaction has every element a sum of homogeneous elements. -/
theorem mem_homogeneousSubalgebra_of_counit (hε : Counit Δ) (hco : Coassoc Δ) (a : A) :
    a ∈ homogeneousSubalgebra Δ := by
  rw [← hε a]
  exact Subalgebra.sum_mem _ fun d _ => mem_homogeneousSubalgebra_of_mem_grade Δ (hco a d)

end Categorification.CoactionGrading
