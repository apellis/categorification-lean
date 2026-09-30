/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.Form

/-!
# The `ℕ[I]`-grading of `'f`

Lusztig, *Introduction to quantum groups*, 1.2.1; Khovanov–Lauda, arXiv:0803.4121v2, §3.1:
`'f = ⊕_{ν ∈ ℕ[I]} 'f_ν`, where `'f_ν` is spanned by the words of weight `ν` (the degree of
`θ i` is `i`). Weights are multisets `ν : Multiset I`, as for KLR algebras
(`Categorification.KLR.Basic`).

## Main results

* `PreF.grade ν` — the weight space `'f_ν`;
* `PreF.grade_gradedMonoid` — `'f_ν 'f_μ ⊆ 'f_{ν+μ}`;
* `PreF.grade_isInternal` — `'f` is the internal direct sum of the `'f_ν`, so `'f` is a
  graded algebra (`PreF.gradedAlgebra`);
* `PreF.form_eq_zero_of_grade_ne` — distinct weight spaces are orthogonal for `( , )`;
* `PreF.d_mem_grade` — `d i` maps `'f_{i + ν}` to `'f_ν`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical

namespace PreF

variable {I : Type*} {K : Type*} [CommRing K]

variable (K) in
/-- The weight space `'f_ν`: the span of the words of weight `ν`. -/
def grade (ν : Multiset I) : Submodule K (PreF K I) := supp {w | wt w = ν}

theorem word_mem_grade (w : FreeMonoid I) : (word w : PreF K I) ∈ grade K (wt w) :=
  word_mem_supp rfl

theorem mem_grade_iff {ν : Multiset I} {x : PreF K I} :
    x ∈ grade K ν ↔ ∀ w ∈ x.coeff.support, wt w = ν := by
  rw [grade, supp, MonoidAlgebra.mem_supported]
  exact ⟨fun h w hw => h hw, fun h w hw => h w hw⟩

theorem θ_mem_grade (i : I) : (θ i : PreF K I) ∈ grade K {i} := word_mem_grade _

instance grade_gradedMonoid : SetLike.GradedMonoid (grade K : Multiset I → Submodule K _) where
  one_mem := by
    rw [← word_one]
    exact word_mem_grade 1
  mul_mem := by
    intro ν μ x y hx hy
    rw [mem_grade_iff] at hx hy ⊢
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.1 (MonoidAlgebra.support_coeff_mul_subset x y hw)
    rw [wt_mul, hx a ha, hy b hb]

/-- The weight homomorphism on words, as an additive monoid homomorphism. -/
def wtHom : Additive (FreeMonoid I) →+ Multiset I where
  toFun w := wt (Additive.toMul w)
  map_zero' := rfl
  map_add' u w := wt_mul (Additive.toMul u) (Additive.toMul w)

theorem grade_eq_gradeBy :
    (grade K : Multiset I → Submodule K (PreF K I)) = fun ν =>
      (AddMonoidAlgebra.gradeBy K (wtHom (I := I)) ν).comap
        (MonoidAlgebra.toAdditiveAlgEquiv K K (FreeMonoid I)).toLinearMap := by
  funext ν
  ext x
  rw [mem_grade_iff]
  change _ ↔ ∀ m ∈ (x.coeff.mapDomain Additive.ofMul).support, wtHom m = ν
  rw [Finsupp.mapDomain_support_of_injective Additive.ofMul.injective]
  simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  rfl

/-- `'f` is the internal direct sum of its weight spaces (Lusztig 1.2.1). -/
theorem grade_isInternal :
    DirectSum.IsInternal (grade K : Multiset I → Submodule K (PreF K I)) := by
  have h := AddMonoidAlgebra.gradeBy.isInternal (R := K) (wtHom (I := I))
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
  let o := (Submodule.orderIsoMapComap
    (MonoidAlgebra.toAdditiveAlgEquiv K K (FreeMonoid I)).toLinearEquiv).symm
  have hg : (grade K : Multiset I → Submodule K (PreF K I)) =
      o ∘ AddMonoidAlgebra.gradeBy K (wtHom (I := I)) := grade_eq_gradeBy
  rw [hg, iSupIndep_map_orderIso_iff, Function.comp_def, ← o.map_iSup, h.2, o.map_top]
  exact ⟨h.1, rfl⟩

/-- `'f` as an `ℕ[I]`-graded algebra. -/
@[instance_reducible] def gradedAlgebra : GradedAlgebra (grade K : Multiset I → Submodule K (PreF K I)) :=
  { grade_gradedMonoid, grade_isInternal.chooseDecomposition with }

variable {dot : I → I → ℤ} {v : Kˣ}

/-- Distinct weight spaces are orthogonal for Lusztig's form (Lusztig 1.2.3). -/
theorem form_eq_zero_of_grade_ne (c : I → K) {ν μ : Multiset I} (h : ν ≠ μ) {x y : PreF K I}
    (hx : x ∈ grade K ν) (hy : y ∈ grade K μ) : form dot v c x y = 0 := by
  have := eqOn_supp ((form dot v c).flip y) 0 (S := {w | wt w = ν}) (fun w hw => by
    rw [LinearMap.flip_apply, LinearMap.zero_apply]
    refine form_word_apply_eq_zero w y (supp_mono ?_ hy)
    intro w' hw'
    simp only [Set.mem_ofPred_eq] at hw hw' ⊢
    rw [hw, hw']
    exact Ne.symm h) x hx
  simpa using this

/-- `d i` maps `'f_{i + ν}` to `'f_ν`. -/
theorem d_mem_grade (i : I) {ν : Multiset I} {x : PreF K I} (hx : x ∈ grade K (i ::ₘ ν)) :
    d dot v i x ∈ grade K ν := by
  refine map_supp_le (d dot v i) (fun w hw => supp_mono ?_ (d_word_mem_supp i w)) x hx
  intro w' hw'
  simp only [Set.mem_ofPred_eq] at hw hw' ⊢
  rw [hw] at hw'
  exact (Multiset.cons_inj_right i).1 hw'

end PreF

end Categorification.QuantumGroup

end
