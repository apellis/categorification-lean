/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedRelabel
import Categorification.WeightedKLR.RedStrands.BraidedStandardGrading
import Categorification.Algebra.Graded.Tensor
import Categorification.KLR.CyclotomicSplit

/-!
# Auxiliary grading under permutation of the red labels

For the ordering of the tensor factors in Webster, arXiv:1309.3796v2,
§6.1 and Proposition 7.11, relabelling changes every red endpoint by
the same permutation. The coaction on affine diagrams intertwines the
two labellings and descends to the quotient by violating diagrams.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR Equiv QuantumGroup Categorification.Graded
variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {𝔠 : CartanDatum I} (hR : IsRouquierQ 𝔠 Q) (σ : Perm (Fin ℓ))

private abbrev redRelabelGrading (Ω : Fin ℓ → I →₀ ℕ) : KLR.GradingDatum (stendhalQ Q Ω) :=
  stendhalGradingDatum Ω hR.gradingDatum (UDot.di 𝔠)
    (fun i => (hR.gradingDatum_degX i).trans (UDot.two_mul_di 𝔠 i).symm)

local notation "G" => redRelabelGrading hR Λ
local notation "G'" => redRelabelGrading hR (Λ ∘ σ)
local notation "μ" => stendhalWeight ℓ ν
local notation "F" => SeqRelabel.ofRedPerm (k := k) (Q := Q) (Λ := Λ) (Λ' := Λ ∘ σ)
  (ν := ν) σ (fun _ => rfl)

private theorem redPermAffine_coaction (a : KLRAlgebra k (stendhalQ Q (Λ ∘ σ)) μ) :
    (G).coaction (KLRAlgebra.relabelHom F a) =
      AddMonoidAlgebra.mapAlgHom ℤ (KLRAlgebra.relabelHom F) ((G').coaction a) := by
  classical
  induction a using KLRAlgebra.klr_induction with
  | hr r => simp only [AlgHom.commutes]
  | hadd a b ha hb => simp only [map_add, ha, hb]
  | hmul a b ha hb => simp only [map_mul, ha, hb]
  | he t => simp only [KLRAlgebra.relabelHom_e, GradingDatum.coaction_e,
      AddMonoidAlgebra.mapAlgHom_single]
  | hx j =>
    simp only [KLRAlgebra.relabelHom_x, GradingDatum.coaction_x, map_sum, map_mul,
      AddMonoidAlgebra.mapAlgHom_single, KLRAlgebra.relabelHom_e]
    symm
    apply Fintype.sum_equiv (F).equiv
    intro t
    congr 1
    change (G').degX (t.lbl j) = (G).degX (Sum.map id σ (t.lbl j))
    cases t.lbl j <;> rfl
  | hψ j =>
    simp only [KLRAlgebra.relabelHom_ψ, GradingDatum.coaction_ψ, map_sum, map_mul,
      AddMonoidAlgebra.mapAlgHom_single, KLRAlgebra.relabelHom_e]
    symm
    apply Fintype.sum_equiv (F).equiv
    intro t
    congr 1
    by_cases hj : j + 1 < Multiset.card μ
    · rw [(G').dψ_of_lt hj, (G).dψ_of_lt hj]
      change (G').degΨ (t.lbl _) (t.lbl _) =
        (G).degΨ (Sum.map id σ (t.lbl _)) (Sum.map id σ (t.lbl _))
      cases t.lbl ⟨j, by omega⟩ <;> cases t.lbl ⟨j + 1, hj⟩ <;> rfl
    · simp [GradingDatum.dψ, hj]

/-- Relabelling the affine KLR algebra by a permutation of the red strands
preserves its auxiliary degree. -/
theorem redPermAffine_mem_grade {n : ℤ} {a : KLRAlgebra k (stendhalQ Q (Λ ∘ σ)) μ}
    (ha : a ∈ (G').grade μ n) : KLRAlgebra.relabelEquiv F a ∈ (G).grade μ n := by
  change KLRAlgebra.relabelHom F a ∈ (G).grade μ n
  rw [GradingDatum.mem_grade, redPermAffine_coaction hR σ, (G').mem_grade.mp ha,
    AddMonoidAlgebra.mapAlgHom_single]


local notation "E" => violRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ σ) (Λ := Λ) (ν := ν) σ (fun _ => rfl)

/-- A diagram belongs to the same auxiliary degree before and after
permuting its red labels in the quotient by violating diagrams. -/
theorem violRedPermEquiv_mem_grade_iff {n : ℤ} (x : ViolQuotient k Q (Λ ∘ σ) ν) :
    E x ∈ violAuxiliaryGrade (ν := ν) G n ↔ x ∈ violAuxiliaryGrade (ν := ν) G' n := by
  have homogeneous : PreservesGrading (violAuxiliaryGrade (ν := ν) G') (violAuxiliaryGrade (ν := ν) G)
      (E).toLinearMap := by
    intro j y hy
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hb
    change E (violMk k Q (Λ ∘ σ) ν (ofKLR k Q (Λ ∘ σ) ν a)) ∈ _
    rw [violRedPermEquiv_violMk,redPermAlgEquiv,relabelAlgEquiv_ofKLR]
    exact Graded.mem_map_of_mem _ (violMk k Q Λ ν).toLinearMap
      (Graded.mem_map_of_mem _ (ofKLR k Q Λ ν).toLinearMap (redPermAffine_mem_grade hR σ ha))
  refine ⟨fun hx => ?_, fun hx => homogeneous hx⟩
  have h := (GradedEquiv.ofPreserves (E).toLinearEquiv homogeneous).symm_map_mem' hx
  exact (E).symm_apply_apply x ▸ h

/-- Restricting the red permutation to one ordered corner also preserves
and reflects the auxiliary degree of each element. -/
theorem violCornerRedPermEquiv_mem_grade_iff {n : ℤ} (κ : List (Fin ℓ))
    (x : ViolOrderCorner (k := k) (Q := Q) (Λ := Λ ∘ σ) (ν := ν) κ) :
    (violCornerRedPermEquiv (k := k) (Q := Q) (Λ' := Λ ∘ σ) (Λ := Λ) (ν := ν) σ (fun _ => rfl) κ x).val ∈
      violAuxiliaryGrade (ν := ν) G n ↔ x.val ∈ violAuxiliaryGrade (ν := ν) G' n :=
  violRedPermEquiv_mem_grade_iff hR σ x.val

end Categorification.Stendhal.BraidedStendhalAlgebra
