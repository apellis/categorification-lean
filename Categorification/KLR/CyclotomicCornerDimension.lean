/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicHuShiPermutation
import Categorification.KLR.Crystal.Thm317Graded

/-!
# Ordinary cyclotomic corner dimensions

At q = 1 the graded dimension formula of Hu–Shi, arXiv:2108.05508v5,
Theorem 1.1, gives equation (1.2). The sum of products of ordinary integers
computes the dimension over every coefficient field.
-/

noncomputable section
namespace Categorification.KLR.CycKLR
open KLRAlgebra Categorification.Graded QuantumGroup LieLean.QuantumGroup Equiv

private theorem eval_quantumInteger (d n : ℤ) : evalOne (qIntU (qUnitLP ^ d) n) = n := by
  have h (r : ℕ) : evalOne (qNatU (qUnitLP ^ d) r) = (r : ℤ) := by
    rw [qNatU_eq_qint,qint_eq_sum,map_sum]
    simp only [← zpow_mul,val_qUnitLP_zpow,evalOne_T,Finset.sum_const,Finset.card_range,nsmul_one]
  cases n with
  | ofNat r => exact h r
  | negSucc r => rw [qIntU,map_neg,h]; omega

variable {I k : Type*} [DecidableEq I] [Field k] {C : CartanDatum I}
    {Q : I → I → MvPolynomial (Fin 2) k} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {β : Multiset I} (s t : Seq β)

local notation "aΛ" => (fun j => (Polynomial.X : Polynomial k)^Λ j)
local notation "B" => CycKLR k Q aΛ β
local notation "g" => grade hP.gradingDatum Λ β
local notation "cor" => corner k Q aΛ s t

private theorem corner_homogeneous : (cor).IsHomogeneous g := by
  apply isHomogeneous_range (ℳ := g)
  intro d x hx
  have hzero (v : Seq β) : mk k Q aΛ β (e v) ∈ g 0 :=
    Graded.mem_map_of_mem _ _ (hP.gradingDatum.e_mem_grade v)
  change mk k Q aΛ β (e s) * (x * mk k Q aΛ β (e t)) ∈ g d
  simpa only [zero_add,add_zero] using
    SetLike.GradedMul.mul_mem (hzero s) (SetLike.GradedMul.mul_mem hx (hzero t))

include hP in
/-- Hu–Shi, arXiv:2108.05508v5, equation (1.2). The ungraded dimension of a
cyclotomic sequence corner is the sum, over matching permutations, of the
products of the prefix integers from Definition 3.2. -/
theorem finrank_corner_permutationFormula :
    (Module.finrank k (cor) : ℤ) =
      ∑ w : Perm (Fin β.card) with ∀ j, s.1 j = t.1 (w j), ∏ j, huShiN C Λ s.1 w j := by
  let : Module.Finite k B := module_finite
    (fun i j hij => by obtain ⟨c,hc,he⟩ := hP.polyInY_leading i j hij; rw [he]; exact hc.map Polynomial.C)
    (fun _ => Polynomial.monic_X_pow _)
  let := submoduleDecomposition g (corner_homogeneous hP Λ s t)
  have hdim (d : ℤ) : Module.finrank k (Graded.submodule g (cor) d) =
      Module.finrank k ↥(g d ⊓ cor) := by
    have h := finrank_comap g (f := (cor).subtype) Subtype.val_injective d
    refine h.trans ?_
    exact congrArg (fun V : Submodule k B => Module.finrank k ↥(g d ⊓ V)) (cor).range_subtype
  have h : gdimPoly (Graded.submodule g (cor)) =
      huShiPolynomial C Λ (List.ofFn s.1) (List.ofFn t.1) := by
    ext d
    rw [gdimPoly_apply,hdim,finrank_cornerGrade_huShi]
  rw [←evalOne_gdimPoly (Graded.submodule g (cor)),h,huShiPolynomial_eq_sum_permutations,map_sum]
  simp only [map_prod,map_mul,evalOne_T,one_mul,eval_quantumInteger]

end Categorification.KLR.CycKLR
