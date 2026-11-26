/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.StandardViolatedDescent

/-!
# The standard module `S_α` as a sum of the `S_s`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1.
The standard module `S_α = e_α T̃^λ / U_α` of a root function `α` is the direct sum of the
standard modules `S_s = e(s) T̃^λ / U_s` (Definition 5.1) over the red-ordered sequences `s` of
root function `α`: `[e_α y] ↦ ([e(s) y])_s`, as right `T̃^λ`-modules (`rootStandardEquiv`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR MulOpposite

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "A" => StendhalAlgebra k Q Λ ν

namespace StendhalAlgebra

variable (α : Fin ℓ → I → ℕ)

/-- The red-ordered sequences of root function `α`. -/
abbrev RootSeq := {s // s ∈ rootSet ν α}

theorem RootSeq.isRedOrdered (s : RootSeq (ν := ν) α) : IsRedOrdered s.1 :=
  (mem_rootSet.1 s.2).1

theorem RootSeq.blackCount_eq (s : RootSeq (ν := ν) α) : blackCount s.1 = α :=
  (mem_rootSet.1 s.2).2

variable {α}

local notation "E" s => (e (Subtype.val s) (RootSeq.isRedOrdered _ s) : A)

theorem rootSeq_e_mul_rootIdem (s : RootSeq (ν := ν) α) :
    (E s) * rootIdem Q Λ α = E s := by
  rw [e_mul_rootIdem, ite_eq_left_of_eq_true _ _ (eq_true (RootSeq.blackCount_eq α s))]

theorem rootIdem_mul_rootSeq_e (s : RootSeq (ν := ν) α) :
    rootIdem Q Λ α * (E s) = E s := by
  rw [rootIdem_mul_e, ite_eq_left_of_eq_true _ _ (eq_true (RootSeq.blackCount_eq α s))]

theorem rootSeq_e_mul_e (s t : RootSeq (ν := ν) α) :
    (E s) * (E t) = if s = t then E s else 0 := by
  rw [e_mul_e]
  by_cases h : s = t
  · subst h; simp
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => h (Subtype.ext h'))),
      ite_eq_right_of_eq_false _ _ (eq_false h)]

theorem e_mul_mem_upperSubmodule_of_mem_rootUpper (s : RootSeq (ν := ν) α) {z : A}
    (hz : z ∈ rootUpper Q Λ α) :
    (E s) * z ∈ upperSubmodule Q Λ s.1 (RootSeq.isRedOrdered α s) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ht, a, hlt, rfl⟩ := hz
    refine Submodule.subset_span ⟨t, ht, a, ?_, ?_⟩
    · rw [stendhalLT_iff, RootSeq.blackCount_eq α s]; exact hlt
    · rw [← mul_assoc, ← mul_assoc, rootSeq_e_mul_rootIdem]
  | zero => rw [mul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [mul_add]; exact add_mem hz hz'
  | smul c z _ hz =>
    rw [← MulOpposite.op_unop c, op_smul_eq_mul, ← mul_assoc, ← op_smul_eq_mul]
    exact Submodule.smul_mem _ _ hz

theorem upperSubmodule_le_rootUpper_of_rootSeq (s : RootSeq (ν := ν) α) :
    upperSubmodule Q Λ s.1 (RootSeq.isRedOrdered α s) ≤ rootUpper Q Λ α := by
  have h := upperSubmodule_le_rootUpper (Q := Q) (Λ := Λ) s.1 (RootSeq.isRedOrdered α s)
  rwa [RootSeq.blackCount_eq α s] at h

variable (Q Λ) in
/-- `[z] ↦ [e(s) z]`, `T̃^λ / U_α → T̃^λ / U_s`. -/
def rootProj (s : RootSeq (ν := ν) α) :
    (A ⧸ rootUpper Q Λ α) →ₗ[Aᵐᵒᵖ] A ⧸ upperSubmodule Q Λ s.1 (RootSeq.isRedOrdered α s) :=
  (rootUpper Q Λ α).mapQ _ (lmulOp (E s)) fun _ hz =>
    e_mul_mem_upperSubmodule_of_mem_rootUpper s hz

variable (Q Λ) in
/-- `[z] ↦ [z]`, `T̃^λ / U_s → T̃^λ / U_α`. -/
def rootIncl (s : RootSeq (ν := ν) α) :
    (A ⧸ upperSubmodule Q Λ s.1 (RootSeq.isRedOrdered α s)) →ₗ[Aᵐᵒᵖ] A ⧸ rootUpper Q Λ α :=
  Submodule.mapQ _ _ LinearMap.id (upperSubmodule_le_rootUpper_of_rootSeq s)

theorem rootProj_mk (s : RootSeq (ν := ν) α) (z : A) :
    rootProj Q Λ s (Submodule.Quotient.mk z) = Submodule.Quotient.mk ((E s) * z) := rfl

theorem rootIncl_mk (s : RootSeq (ν := ν) α) (z : A) :
    rootIncl Q Λ s (Submodule.Quotient.mk z) = Submodule.Quotient.mk z := rfl

theorem mem_seqProj_iff (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) (z : A) :
    z ∈ seqProj Q Λ s hs ↔ e s hs * z = z :=
  mem_span_singleton_iff_mul (e_mul_e_self s hs) z

theorem mem_span_rootIdem_iff (z : A) :
    z ∈ Submodule.span Aᵐᵒᵖ {rootIdem Q Λ α} ↔ rootIdem Q Λ α * z = z :=
  mem_span_singleton_iff_mul (isIdempotentElem_rootIdem α) z

theorem exists_mk_of_mem_rootStandard (v : rootStandard (ν := ν) Q Λ α) :
    ∃ y, rootIdem Q Λ α * y = y ∧
      (v : A ⧸ rootUpper Q Λ α) = Submodule.Quotient.mk y := by
  obtain ⟨_, ⟨y, hy, rfl⟩⟩ := v
  exact ⟨y, (mem_span_rootIdem_iff y).1 hy, rfl⟩

theorem exists_mk_of_mem_standardModule' (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s)
    (v : standardModule Q Λ s hs) :
    ∃ y, e s hs * y = y ∧
      (v : A ⧸ upperSubmodule Q Λ s hs) = Submodule.Quotient.mk y := by
  obtain ⟨_, ⟨y, hy, rfl⟩⟩ := v
  exact ⟨y, (mem_seqProj_iff s hs y).1 hy, rfl⟩

variable (Q Λ α) in
/-- `S_α → ⊕_s S_s`, `[e_α y] ↦ ([e(s) y])_s`. -/
def rootStandardToPi : rootStandard (ν := ν) Q Λ α →ₗ[Aᵐᵒᵖ]
    ((s : RootSeq (ν := ν) α) → standardModule Q Λ s.1 (RootSeq.isRedOrdered α s)) :=
  LinearMap.pi fun s => ((rootProj Q Λ s).comp (rootStandard (ν := ν) Q Λ α).subtype).codRestrict
    _ fun v => by
      obtain ⟨y, -, hv⟩ := exists_mk_of_mem_rootStandard v
      change rootProj Q Λ s (v : A ⧸ rootUpper Q Λ α) ∈ _
      rw [hv, rootProj_mk]
      refine Submodule.mem_map_of_mem ((mem_seqProj_iff _ _ _).2 ?_)
      rw [← mul_assoc, e_mul_e_self]

variable (Q Λ α) in
/-- `⊕_s S_s → S_α`, `([y_s])_s ↦ [∑_s y_s]`. -/
def piToRootStandard :
    ((s : RootSeq (ν := ν) α) → standardModule Q Λ s.1 (RootSeq.isRedOrdered α s)) →ₗ[Aᵐᵒᵖ]
      rootStandard (ν := ν) Q Λ α :=
  (∑ s : RootSeq (ν := ν) α, (rootIncl Q Λ s).comp
      ((standardModule Q Λ s.1 (RootSeq.isRedOrdered α s)).subtype.comp
        (LinearMap.proj s))).codRestrict _ fun w => by
    rw [LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun s _ => ?_
    obtain ⟨y, hy, hw⟩ := exists_mk_of_mem_standardModule' _ _ (w s)
    change rootIncl Q Λ s ((w s : _)) ∈ _
    rw [hw, rootIncl_mk]
    refine Submodule.mem_map_of_mem ((mem_span_rootIdem_iff _).2 ?_)
    rw [← hy, ← mul_assoc, rootIdem_mul_rootSeq_e]

theorem coe_rootStandardToPi_apply (v : rootStandard (ν := ν) Q Λ α) (s : RootSeq (ν := ν) α) :
    ((rootStandardToPi Q Λ α v s : standardModule Q Λ s.1 _) : A ⧸ _) =
      rootProj Q Λ s (v : A ⧸ rootUpper Q Λ α) := rfl

theorem coe_piToRootStandard_apply
    (w : (s : RootSeq (ν := ν) α) → standardModule Q Λ s.1 (RootSeq.isRedOrdered α s)) :
    ((piToRootStandard Q Λ α w : rootStandard (ν := ν) Q Λ α) : A ⧸ rootUpper Q Λ α) =
      ∑ s, rootIncl Q Λ s (w s : A ⧸ _) := by
  change (∑ s : RootSeq (ν := ν) α, (rootIncl Q Λ s).comp
      ((standardModule Q Λ s.1 (RootSeq.isRedOrdered α s)).subtype.comp
        (LinearMap.proj s))) w = _
  rw [LinearMap.sum_apply]
  rfl

theorem sum_rootSeq_e : ∑ s : RootSeq (ν := ν) α, (E s) = rootIdem Q Λ α := by
  exact (rootIdem_eq_sum α).symm

variable (Q Λ α) in
/-- **`S_α = ⊕_s S_s`** (arXiv:1309.3796v3, §5.1): the standard module of a root function
`α` is the direct sum of the standard modules `S_s` of Definition 5.1 over the red-ordered
sequences `s` of root function `α`, as right `T̃^λ`-modules. -/
def rootStandardEquiv : rootStandard (ν := ν) Q Λ α ≃ₗ[Aᵐᵒᵖ]
    ((s : RootSeq (ν := ν) α) → standardModule Q Λ s.1 (RootSeq.isRedOrdered α s)) :=
  LinearEquiv.ofLinearMap (rootStandardToPi Q Λ α) (piToRootStandard Q Λ α)
    (by
      refine LinearMap.ext fun w => funext fun t => Subtype.ext ?_
      obtain ⟨y, hy, hw⟩ := exists_mk_of_mem_standardModule' _ _ (w t)
      change rootProj Q Λ t ((piToRootStandard Q Λ α w : rootStandard (ν := ν) Q Λ α) :
        A ⧸ rootUpper Q Λ α) = (w t : A ⧸ _)
      rw [coe_piToRootStandard_apply, map_sum, hw]
      have : ∀ s, rootProj Q Λ t (rootIncl Q Λ s (w s : A ⧸ _)) =
          if s = t then (Submodule.Quotient.mk y : A ⧸ _) else 0 := by
        intro s
        obtain ⟨y', hy', hw'⟩ := exists_mk_of_mem_standardModule' _ _ (w s)
        rw [hw', rootIncl_mk, rootProj_mk, ← hy', ← mul_assoc, rootSeq_e_mul_e]
        by_cases h : t = s
        · subst h
          rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true rfl), hy', ← hw', hw]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm h)),
            zero_mul]
          rfl
      rw [Finset.sum_congr rfl fun s _ => this s, Finset.sum_ite_eq' Finset.univ t]
      simp)
    (by
      refine LinearMap.ext fun v => Subtype.ext ?_
      obtain ⟨y, hy, hv⟩ := exists_mk_of_mem_rootStandard v
      change ((piToRootStandard Q Λ α (rootStandardToPi Q Λ α v) :
        rootStandard (ν := ν) Q Λ α) : A ⧸ rootUpper Q Λ α) = (v : A ⧸ _)
      rw [coe_piToRootStandard_apply]
      simp_rw [coe_rootStandardToPi_apply, hv, rootProj_mk, rootIncl_mk]
      rw [show ∑ x : RootSeq (ν := ν) α, (Submodule.Quotient.mk ((E x) * y) :
          A ⧸ rootUpper Q Λ α) = Submodule.Quotient.mk (∑ x : RootSeq (ν := ν) α, (E x) * y) from
        (map_sum (rootUpper Q Λ α).mkQ _ _).symm, ← Finset.sum_mul, sum_rootSeq_e, hy])

end StendhalAlgebra

end Categorification.Stendhal
