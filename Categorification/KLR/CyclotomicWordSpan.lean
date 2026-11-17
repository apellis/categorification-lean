/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicSerreK0
import Categorification.KLR.KL2.Gamma2

/-!
# Generation of the rational cyclotomic projective module by induction

Webster, arXiv:1309.3796v2, §3.4, proof of Proposition 3.21. The divided
projectives span integrally. Over the rational function field their quantum
factorials are invertible, so ordinary induction words on the vacuum span.
-/

noncomputable section
namespace Categorification.KLR.CycKLR

open Categorification.Graded KLRAlgebra QuantumGroup KL2 KLGamma
open scoped TensorProduct
attribute [local instance] KLGamma.qToVAlgebra

variable {I k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    {C : CartanDatum I} (hQ : IsRouquierQ C Q) (Λ : I → ℕ)

local notation "G" => hQ.gradingDatum
local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "P" => projectiveK0 G Λ
local notation "M" => L ⊗[LP] P
local notation "B" => Module.End.baseChangeHom LP L P
local notation "ι" => DirectSum.lof LP _ (fun ν => K0 (grade G Λ ν))

/-- The class of the expanded black word in the rational cyclotomic projective module. -/
def lowerWordQ (w : List I) : M :=
  (1 : L) ⊗ₜ[LP] totalQuotientK0 G Λ ((G).clsW w)

theorem lowerWordQ_nil : lowerWordQ hQ Λ [] =
    (1 : L) ⊗ₜ[LP] totalQuotientK0 G Λ 1 := by rw [lowerWordQ, (G).clsW_nil]

/-- Appending a letter is the scalar extension of ordinary cyclotomic induction. -/
theorem lowerWordQ_append (w : List I) (i : I) :
    lowerWordQ hQ Λ (w ++ [i]) = B (lower G Λ i) (lowerWordQ hQ Λ w) := by
  change (1 : L) ⊗ₜ[LP] totalQuotientK0 G Λ ((G).clsW (w ++ [i])) =
    (1 : L) ⊗ₜ[LP] lower G Λ i (totalQuotientK0 G Λ ((G).clsW w))
  rw [(G).clsW_append, lower_totalQuotientK0 G Λ i (fun a b hab => (hQ.symm a b hab).symm) C.dot_self_pos]

/-- Expanding an induction word multiplies its divided projective class by the
product of its quantum factorials (Webster, proof of Proposition 3.21). -/
theorem word_eq_factorial (β : Multiset I) (d : List (I × ℕ))
    (h : (expandDiv d : Multiset I) = β) :
    totalQuotientK0 G Λ ((G).clsW (expandDiv d)) = divQFact2 C d •
      ι β (K0.of (dividedProjective G (fun i j => congrArg Neg.neg (C.symm i j)) C Λ β d h)) := by
  rw [(G).clsW_eq _ h]
  change totalQuotientK0 G Λ (DirectSum.lof LP _ (G).K0fam β _) = _
  rw [totalQuotientK0_lof]
  have hs (i j) : (G).degΨ i j = (G).degΨ j i := congrArg Neg.neg (C.symm i j)
  rw [show K0.of ((G).projP (Seq.ofList (expandDiv d) h)) = _ from
    (G).of_expanded_eq_factorial hs C (fun _ => rfl) d h, map_smul,
    quotientK0_dividedProjective, map_smul]

/-- Ordinary induction words on the empty projective span after rational scalar
extension (Webster, §3.4, Proposition 3.21). -/
theorem span_lowerWordQ : Submodule.span L (Set.range (lowerWordQ hQ Λ)) = ⊤ := by
  let V := Submodule.span L (Set.range (lowerWordQ hQ Λ))
  let f := TensorProduct.mk LP L P 1
  have ht : ⊤ ≤ (V.restrictScalars LP).comap f := by
    rw [← span_total_dividedProjective C Λ hQ]
    apply Submodule.span_le.mpr
    rintro _ ⟨β, d, h, rfl⟩
    let z := ι β (K0.of (dividedProjective G (fun i j => congrArg Neg.neg (C.symm i j)) C Λ β d h))
    change (1 : L) ⊗ₜ[LP] z ∈ V
    have hw : lowerWordQ hQ Λ (expandDiv d) = qToV (divQFact2 C d) • ((1 : L) ⊗ₜ[LP] z) := by
      rw [lowerWordQ, word_eq_factorial hQ Λ β d h]
      change (1 : L) ⊗ₜ[LP] (divQFact2 C d • z) = _
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one, smul_eq_mul, mul_one]
      rfl
    have hm : qToV (divQFact2 C d) • ((1 : L) ⊗ₜ[LP] z) ∈ V :=
      hw ▸ Submodule.subset_span (Set.mem_range_self (expandDiv d))
    simpa only [smul_smul, inv_mul_cancel₀ (KL2Gamma.qToV_divQFact2_ne_zero C d), one_smul] using
      V.smul_mem (qToV (divQFact2 C d))⁻¹ hm
  apply Submodule.eq_top_iff'.mpr
  intro x
  change x ∈ V
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => exact V.add_mem hx hy
  | tmul a z =>
    have hz : (1 : L) ⊗ₜ[LP] z ∈ V := ht (Submodule.mem_top (x := z))
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using V.smul_mem a hz

/-- A rational submodule containing the vacuum and closed under each cyclotomic
induction is the whole module (Webster, §3.4, proof of Proposition 3.21). -/
theorem eq_top_of_lower_stable (V : Submodule L M)
    (h₀ : (1 : L) ⊗ₜ[LP] totalQuotientK0 G Λ 1 ∈ V)
    (hF : ∀ i x, x ∈ V → B (lower G Λ i) x ∈ V) : V = ⊤ := by
  apply top_unique
  rw [← span_lowerWordQ hQ Λ]
  apply Submodule.span_le.mpr
  rintro _ ⟨w, rfl⟩
  induction w using List.reverseRecOn with
  | nil => rwa [lowerWordQ_nil]
  | append_singleton w i ih => rw [lowerWordQ_append]; exact hF i _ ih

end Categorification.KLR.CycKLR
