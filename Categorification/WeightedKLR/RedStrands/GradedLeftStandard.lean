/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StendhalGrading
import Categorification.WeightedKLR.RedStrands.LeftStandardModule
import Categorification.Algebra.Graded.Idempotent

/-!
# The diagram grading on the left loading standard

Webster's Definitions 4.4 and 5.1 give the grading of the diagram algebra
and the quotient of the loading projective by its higher trace. The trace
is homogeneous, so the literal standard quotient inherits this grading.
-/

noncomputable section

namespace Categorification.Stendhal
open KLR DirectSum
variable {I k : Type} [DecidableEq I] [Field k] {ℓ : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  (G : KLR.GradingDatum (stendhalQ Q Λ))
local notation "R" => TensorProductAlgebra k Q Λ ν
local notation "Γ" => tensorProductGrade G ν

/-- The higher trace defining the ordinary left loading standard is homogeneous
for Webster's diagram grading. -/
theorem leftUpper_isHomogeneous (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s) :
    (leftUpper Q Λ s hs).IsHomogeneous Γ := by
  classical
  intro n x hx
  unfold leftUpper at hx
  induction hx using Submodule.span_induction generalizing n with
  | mem z hz =>
    obtain ⟨t, ht, a, hst, rfl⟩ := hz
    have e₀ := mk_e_mem_tensorProductGrade G ν s hs
    have t₀ := mk_e_mem_tensorProductGrade G ν t ht
    have hr := coe_decompose_mul_add_of_right_mem Γ
      (a := seqIdem Q Λ t ht * a) (i := n) e₀
    rw [add_zero] at hr
    have hl := coe_decompose_mul_add_of_left_mem Γ (b := a) (j := n) t₀
    rw [zero_add] at hl
    rw [hr, hl]
    exact Submodule.subset_span ⟨t, ht, _, hst, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [decompose_add, DirectSum.add_apply, Submodule.coe_add]
    exact Submodule.add_mem _ (ihx n) (ihy n)
  | smul r x hx ih =>
    change (decompose Γ (r * x) n : R) ∈ _
    rw [decompose_mul, coe_mul_apply]
    exact Submodule.sum_mem _ fun ij _ => Submodule.smul_mem _ _ (ih ij.2)

variable (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s)
local notation "P" => lIdeal (seqIdem Q Λ s hs)
set_option quotPrecheck false in
local notation "U" => (leftUpper Q Λ s hs).comap (P).subtype
local notation "𝒫" => Graded.submodule Γ P

private theorem orderedLoadingIdeal_homogeneous : (P : Submodule R R).IsHomogeneous Γ :=
  Graded.leftIdeal_isHomogeneous (𝒜 := Γ) (mk_e_mem_tensorProductGrade G ν s hs)

local instance orderedLoadingIdealDecomposition : Decomposition 𝒫 :=
  Graded.submoduleDecomposition Γ (orderedLoadingIdeal_homogeneous G s hs)

/-- The standard quotient receives the image grading of the ordered loading ideal. -/
def gradedLeftStandard : ℤ → Submodule k (leftStandard Q Λ s hs) :=
  Graded.map 𝒫 ((U).mkQ.restrictScalars k)

@[instance_reducible]
def gradedLeftStandardDecomposition : Decomposition (gradedLeftStandard G s hs) := by
  apply Graded.mapDecomposition (𝒳 := 𝒫) (Submodule.mkQ_surjective U)
  intro x hx n
  change Submodule.Quotient.mk (decompose 𝒫 x n : P) = (0 : leftStandard Q Λ s hs)
  rw [Submodule.Quotient.mk_eq_zero]
  change ((decompose 𝒫 x n : P) : R) ∈ leftUpper Q Λ s hs
  have hcomm := Graded.decompose_map (ℳ := 𝒫) (𝒩 := Γ)
    (f := (P).subtype.restrictScalars k) (fun _ _ h => h) x n
  change (decompose Γ (x : R) n : R) = ((decompose 𝒫 x n : P) : R) at hcomm
  rw [← hcomm]
  have hxq : (Submodule.Quotient.mk x : leftStandard Q Λ s hs) = 0 := hx
  exact leftUpper_isHomogeneous G s hs n ((Submodule.Quotient.mk_eq_zero (p := U)).mp hxq)

theorem gradedLeftStandard_mkQ_mem {n : ℤ} (x : P) (hx : (x : R) ∈ Γ n) :
    (U).mkQ x ∈ gradedLeftStandard G s hs n :=
  ⟨x, hx, rfl⟩

/-- The left standard action has the same internal degree as its scalar. -/
theorem gradedLeftStandard_smul_mem {i j : ℤ} {a : R} {x : leftStandard Q Λ s hs}
    (ha : a ∈ Γ i) (hx : x ∈ gradedLeftStandard G s hs j) :
    a • x ∈ gradedLeftStandard G s hs (i+j) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨a • y, SetLike.GradedSMul.smul_mem (A := Γ) (B := 𝒫) ha hy,
    ((U).mkQ.map_smul a y).symm⟩

end Categorification.Stendhal
