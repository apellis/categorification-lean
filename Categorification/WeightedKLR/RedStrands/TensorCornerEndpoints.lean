/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BoundaryHomReflection
import Categorification.WeightedKLR.RedStrands.LastRedPairing
import Categorification.WeightedKLR.RedStrands.VacuumRestrictionClass
import Categorification.WeightedKLR.RedStrands.DividedProjectives

/-!
# Graded corners at ordinary tensor product boundaries

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.36. For ordered loadings `s,t`,
evaluation at `e_s` identifies `Hom(T e_s, T e_t)_d` with `(e_s T e_t)_d`.
Reflection, common terminal red removal, and the scalar vacuum give the
corresponding boundary rules for the Laurent polynomial of this corner.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR QuantumGroup Categorification.Graded

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ}
    {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
    (G : GradingDatum (stendhalQ Q Λ))
local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "μ" => stendhalWeight ℓ ν
local notation "e" => fun (j : Seq μ) (hj : IsRedOrdered j) =>
  TensorProductAlgebra.mk Q Λ ν (StendhalAlgebra.e j hj)

/-- The space of degree-`d` elements of the tensor product algebra fixed by
`e_s` on the left and `e_t` on the right. -/
def sequenceCornerGrade (s : Seq μ) (hs : IsRedOrdered s) (t : Seq μ) (ht : IsRedOrdered t)
    (d : ℤ) : Submodule k T where
  carrier := {z | z ∈ tensorProductGrade G ν d ∧ e s hs * z = z ∧ z * e t ht = z}
  zero_mem' := ⟨Submodule.zero_mem _, mul_zero _, zero_mul _⟩
  add_mem' hx hy := ⟨Submodule.add_mem _ hx.1 hy.1, by rw [mul_add, hx.2.1, hy.2.1],
    by rw [add_mul, hx.2.2, hy.2.2]⟩
  smul_mem' r _ hx := ⟨Submodule.smul_mem _ _ hx.1, by rw [mul_smul_comm, hx.2.1],
    by rw [smul_mul_assoc, hx.2.2]⟩

/-- The Laurent polynomial of the homogeneous dimensions of `e_s T e_t`. -/
def sequenceCornerPoly (s : Seq μ) (hs : IsRedOrdered s) (t : Seq μ) (ht : IsRedOrdered t) :
    LaurentPolynomial ℤ := gdimPoly (sequenceCornerGrade G s hs t ht)

/-- Evaluation of a homogeneous left module map at its source idempotent
identifies it with a homogeneous diagram in the two-sided corner. -/
def sequenceHomCornerEquiv (s : Seq μ) (hs : IsRedOrdered s) (t : Seq μ) (ht : IsRedOrdered t)
    (d : ℤ) :
    homGrade T (sequenceProj G s hs).grading (sequenceProj G t ht).grading d ≃ₗ[k]
      sequenceCornerGrade G s hs t ht d :=
  (homGradeIdemEquiv (ℳ := (sequenceProj G t ht).grading)
      (isIdempotentElem_mk_e s hs) (mk_e_mem_tensorProductGrade G ν s hs) d).trans {
    toFun x := ⟨x.val.val.val, x.2, congrArg Subtype.val x.val.2, x.val.val.2⟩
    invFun z := ⟨⟨⟨z.val, z.2.2.2⟩, Subtype.ext z.2.2.1⟩, z.2.1⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

private theorem poly_eq_of_finranks {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (U : ℤ → Submodule k M) (V : ℤ → Submodule k N)
    (h : ∀ d, Module.finrank k (U d) = Module.finrank k (V d)) : gdimPoly U = gdimPoly V := by
  classical
  let polynomial (f : ℤ → ℤ) : LaurentPolynomial ℤ :=
    if hf : (Function.support f).Finite then .ofCoeff (Finsupp.ofSupportFinite f hf) else 0
  change polynomial _ = polynomial _
  exact congrArg polynomial (funext fun d => congrArg (fun n : ℕ => (n : ℤ)) (h d))

/-- The corner dimension polynomial is the unshifted Hom polynomial of the
sequence projectives in the same order, with the source idempotent on the left. -/
theorem sequenceCornerPoly_eq_homGdimPoly (s : Seq μ) (hs : IsRedOrdered s)
    (t : Seq μ) (ht : IsRedOrdered t) :
    sequenceCornerPoly G s hs t ht =
      gdimPoly (homGrade T (sequenceProj G s hs).grading (sequenceProj G t ht).grading) :=
  poly_eq_of_finranks _ _ fun d => (sequenceHomCornerEquiv G s hs t ht d).finrank_eq.symm

variable (C : CartanDatum I) (hQ : IsRouquierQ C Q)

local notation "grade" L => stendhalGradingDatum L hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

/-- Expanding the corner polynomial gives the projective graded Hom series. -/
theorem toLaurentSeries_sequenceCornerPoly (Λ : Fin ℓ → I →₀ ℕ)
    (s : Seq μ) (hs : IsRedOrdered s) (t : Seq μ) (ht : IsRedOrdered t) :
    toLaurentSeries (sequenceCornerPoly (grade Λ) s hs t ht) =
      (sequenceProj (grade Λ) s hs).homGdim (sequenceProj (grade Λ) t ht) := by
  let := tensorProductAlgebra_finite Λ ν hQ
  rw [sequenceCornerPoly_eq_homGdimPoly, GProj.toLaurentSeries_homGdimPoly]

/-- Each coefficient counts the homogeneous diagrams in the corresponding corner. -/
theorem sequenceCornerPoly_coeff (Λ : Fin ℓ → I →₀ ℕ)
    (s : Seq μ) (hs : IsRedOrdered s) (t : Seq μ) (ht : IsRedOrdered t) (d : ℤ) :
    (sequenceCornerPoly (grade Λ) s hs t ht).coeff d =
      Module.finrank k (sequenceCornerGrade (grade Λ) s hs t ht d) := by
  let := tensorProductAlgebra_finite Λ ν hQ
  let := HasGdim.of_finiteDimensional (tensorProductGrade (grade Λ) ν)
  rw [← coeff_toLaurentSeries, toLaurentSeries_sequenceCornerPoly]
  change (gdim _).coeff d = _
  rw [coeff_gdim, (sequenceHomCornerEquiv (grade Λ) s hs t ht d).finrank_eq]

/-- Reflection preserves the homogeneous dimensions when the two ordinary
boundary loadings are exchanged, Webster, Lemma 4.36. -/
theorem sequenceCornerPoly_comm (Λ : Fin ℓ → I →₀ ℕ)
    (s : Seq μ) (hs : IsRedOrdered s) (t : Seq μ) (ht : IsRedOrdered t) :
    sequenceCornerPoly (grade Λ) s hs t ht = sequenceCornerPoly (grade Λ) t ht s hs := by
  rw [sequenceCornerPoly_eq_homGdimPoly, sequenceCornerPoly_eq_homGdimPoly]
  apply homGdimPoly_sequenceProj_symm
  rintro (a|a) (b|b) <;> try rfl
  exact congrArg Neg.neg (C.symm a b)

include hQ in
/-- Removing a common terminal red preserves the corner polynomial for the
restricted grading, Webster, Proposition 4.18 and Lemma 4.36. -/
theorem sequenceCornerPoly_appendRed_restrict {Λ : Fin (ℓ+1) → I →₀ ℕ}
    (D : GradingDatum (stendhalQ Q Λ))
    (s : Seq μ) (hs : IsRedOrdered s) (t : Seq μ) (ht : IsRedOrdered t) :
    sequenceCornerPoly D (appendRedLoading s) ((appendRedLoading_ordered_iff s).2 hs)
      (appendRedLoading t) ((appendRedLoading_ordered_iff t).2 ht) =
      sequenceCornerPoly (restrictRedGrading Q Λ D) s hs t ht := by
  rw [sequenceCornerPoly_eq_homGdimPoly, sequenceCornerPoly_eq_homGdimPoly]
  exact poly_eq_of_finranks _ _ (finrank_homGrade_appendRed hQ D ν s t hs ht)

/-- The terminal-red identity for the Cartan grading on each side. -/
theorem sequenceCornerPoly_appendRed (Λ : Fin (ℓ+1) → I →₀ ℕ)
    (s : Seq μ) (hs : IsRedOrdered s) (t : Seq μ) (ht : IsRedOrdered t) :
    sequenceCornerPoly (grade Λ) (appendRedLoading s) ((appendRedLoading_ordered_iff s).2 hs)
      (appendRedLoading t) ((appendRedLoading_ordered_iff t).2 ht) =
      sequenceCornerPoly (grade (Λ ∘ Fin.castSucc)) s hs t ht := by
  have hr : restrictRedGrading Q Λ (grade Λ) = grade (Λ ∘ Fin.castSucc) := by
    unfold restrictRedGrading stendhalGradingDatum
    congr 1
    · funext a
      cases a <;> rfl
    · funext a b
      cases a <;> cases b <;> rfl
  rw [sequenceCornerPoly_appendRed_restrict (hQ := hQ), hr]

/-- For any number of red strands the vacuum corner has dimension one in
degree zero and zero in every other degree, Webster, Lemma 4.36. -/
theorem sequenceCornerPoly_vacuum :
    sequenceCornerPoly G vacuumSeq vacuumSeq_ordered vacuumSeq vacuumSeq_ordered = 1 := by
  let V := tensorProductGrade G (0 : Multiset I)
  let F := tensorProductAlgebraZeroEquiv Q Λ
  let : Module.Finite k (TensorProductAlgebra k Q Λ (0 : Multiset I)) :=
    Module.Finite.of_injective F.toLinearEquiv.toLinearMap F.injective
  have hEq : sequenceCornerGrade G vacuumSeq vacuumSeq_ordered vacuumSeq vacuumSeq_ordered = V := by
    funext d
    ext z
    change (z ∈ V d ∧ _ ∧ _) ↔ z ∈ V d
    simp only [vacuumSeq_mk_e, one_mul, mul_one, and_self, and_true]
  rw [sequenceCornerPoly, hEq]
  ext d
  rw [gdimPoly_apply]
  change (Module.finrank k (V d) : ℤ) = _
  by_cases hd : d = 0
  · subst d
    have htop : V 0 = ⊤ := eq_top_iff.mpr fun z _ => mem_scalarGrade V F.symm z
    rw [htop, finrank_top, F.toLinearEquiv.finrank_eq]
    simp
  · have hbot : V d = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro z hz
      by_contra hn
      exact hd (DirectSum.degree_eq_of_mem_mem V hz (mem_scalarGrade V F.symm z) hn)
    rw [hbot, ← LaurentPolynomial.T_zero]
    simp only [finrank_bot, Nat.cast_zero, LaurentPolynomial.T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, Ne.symm hd, ↓reduceIte]

end Categorification.Stendhal
