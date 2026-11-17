/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAdjunction
import Categorification.KLR.CyclotomicGradedRestriction
import Categorification.Algebra.Graded.HomForm

/-!
# Graded Frobenius reciprocity for cyclotomic projectives

Induction adds a final black strand. A homogeneous map out of the induced
projective is determined by its values on the last-strand idempotent tensored
with generators of the source projective. The resulting adjoint on the graded
Hom form is raw restriction. This gives a corner dimension recursion in the
setting of Hu–Shi, arXiv:2108.05508v5, Theorem 1.1, and Kang–Kashiwara,
arXiv:1102.4677v4, §§4 and 6.
-/

noncomputable section
namespace Categorification.KLR.CycKLR
open KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (i : I) (β : Multiset I)
    (hsym : KLRSymm Q)
    (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)

local notation "aΛ" => (fun j => (Polynomial.X : Polynomial k) ^ Λ j)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rl" => CycKLR k Q aΛ β
local notation "Su" => CycKLR k Q aΛ (Si + β)
local notation "src" => grade G Λ β
local notation "dst" => grade G Λ (Si + β)
local notation "cor" => Graded.submodule dst (lIdeal (lastIdem Q i aΛ β))

/-- Frobenius reciprocity in degree `d` with unshifted restriction. -/
def homGrade_ind_res (P : GProj src) (V : GProj dst) (d : ℤ) :
    homGrade Su (gradedIndProj G Λ i β P).grading V.grading d ≃ₗ[k]
      homGrade Rl P.grading (gradedResProj G Λ i β hsym hQ V).grading d where
  toFun f := ⟨homToRes Q i aΛ β f.1, by
    intro j n hn
    have he : indGenerator Q i aΛ β ∈ cor 0 :=
      cyclotomicLast_mem_grade G Λ i β SetLike.GradedOne.one_mem
    have ht := tmul_mem_balancedGrading (B := Su) (A := Rl) (ℳ := cor) (𝒩 := P.grading) he hn
    rw [zero_add] at ht
    change f.1 (BalancedTensor.tmul (indGenerator Q i aΛ β) n) ∈ V.grading (j + d)
    exact f.2 (e := j) ht⟩
  invFun g := ⟨homFromRes Q i aΛ β g.1, by
    intro e y hy
    apply balancedGrading_map_mem (B := Su) (A := Rl) (ℳ := cor) (𝒩 := P.grading)
      (fun j => V.grading (j+d)) ((homFromRes Q i aΛ β g.1).restrictScalars k) _ hy
    intro j l r n hr hn
    have h₁ : (g.1 n).1 ∈ V.grading (l+d) := g.2 hn
    have h₂ := SetLike.GradedSMul.smul_mem (A := dst) (B := V.grading)
      (show r.1 ∈ dst j from hr) h₁
    change r.1 • (g.1 n).1 ∈ V.grading ((j+l)+d)
    simpa only [vadd_eq_add,add_assoc] using h₂⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := Subtype.ext (homFromRes_homToRes Q i aΛ β f.1)
  right_inv g := Subtype.ext (homToRes_homFromRes Q i aΛ β g.1)

/-- On the projective Grothendieck group raw restriction is the right adjoint
of one-strand induction for the graded Hom form. -/
theorem homForm_ind_res [HasGdim src] [HasGdim dst] (x : K0 src) (y : K0 dst) :
    K0.homForm dst (indK0 G Λ i β x) y =
      K0.homForm src x (resK0 G Λ i β hsym hQ y) := by
  induction y using K0.induction_on with
  | of V =>
    induction x using K0.induction_on with
    | of P =>
      rw [indK0_of,resK0_of,K0.homForm_of,K0.homForm_of]
      exact gdim_eq_of_finrank_eq fun d => (homGrade_ind_res G Λ i β hsym hQ P V d).finrank_eq
    | zero => simp only [map_zero,AddMonoidHom.zero_apply]
    | add x x' hx hx' => simp only [map_add,AddMonoidHom.add_apply,hx,hx']
    | neg x hx => simp only [map_neg,AddMonoidHom.neg_apply,hx]
  | zero => simp only [map_zero]
  | add y y' hy hy' => simp only [map_add,hy,hy']
  | neg y hy => simp only [map_neg,hy]

end Categorification.KLR.CycKLR
