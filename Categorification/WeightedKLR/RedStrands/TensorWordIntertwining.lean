/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorWordRelations
import Categorification.WeightedKLR.RedStrands.TensorWordInduction

/-!
# Induction under the divided-word comparison

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.37 and Theorem 4.38.
The downward-strand recursion preceding Lemma 4.36 identifies right black
induction with the coproduct action of the lowering generators on every
projective class. Appending the last red strand tensors with its highest
vector. Both conclusions use the integral span of the word projectives.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra Categorification.Graded QuantumGroup KL2 LieLean LieLean.QuantumGroup
open LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "LP" => LaurentPolynomial ℤ
local notation "v" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

variable {I k Y : Type*} {ℓ : ℕ} [DecidableEq I] [Field k] [AddCommGroup Y]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {R : C.toLusztig.RootDatum Y}
private abbrev wordGrading (L : Fin ℓ → I →₀ ℕ) :=
  stendhalGradingDatum L hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)

/-- The graded projective group in black content β for the standard Stendhal grading. -/
abbrev tensorProjectiveGroup (L : Fin ℓ → I →₀ ℕ) (β : Multiset I) :=
  K0 (tensorProductGrade (wordGrading C hQ L) β)

section Black
variable (Λ : Fin ℓ → I →₀ ℕ)

/-- Webster, §4.6 and Theorem 4.38. Ordinary right induction appends one
black strand to any divided-word projective. -/
theorem blackLower_tensorWordProjectiveClass (w : TensorWord I ℓ) (i : I) :
    blackLower (wordGrading C hQ Λ) i (tensorWordProjectiveClass Λ C hQ w) =
      tensorWordProjectiveClass Λ C hQ (w.black i 1) := by
  have h := blackLower_pow_eq_qfact_smul Λ C hQ i 1
  simp only [pow_one, qfact_one, one_smul] at h
  rw [h, blackDividedLower_tensorWordProjectiveClass]

variable [Finite I] (wt : Fin ℓ → Dom R) {σ : LP →+* LP}
  (f : DirectSum (Multiset I) (tensorProjectiveGroup C hQ Λ) →ₛₗ[σ] integralTensor wt)
  (hw : ∀ w, f (tensorWordProjectiveClass Λ C hQ w) = integralWordVector (C := C) wt w)

include hw

/-- Webster, Theorem 4.38, lowering operators. A comparison preserving
divided words intertwines intrinsic divided induction with the iterated
coproduct on the entire integral projective group. -/
theorem map_blackDividedLower (i : I) (n : ℕ) (x : DirectSum (Multiset I) (tensorProjectiveGroup C hQ Λ)) :
    (f (blackDividedLower Λ C hQ i n x) : TensorSpace wt) =
      tensorRepresentation wt (qDivPow (v ^ C.toLusztig.d i) n (F R v i)) (f x : TensorSpace wt) := by
  have hx : x ∈ Submodule.span LP (Set.range (tensorWordProjectiveClass Λ C hQ)) := by
    rw [span_tensorWordProjectiveClass]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w,rfl⟩ := hz
    rw [blackDividedLower_tensorWordProjectiveClass, hw, hw]
    rfl
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | smul a x _ hx =>
    rw [map_smul, f.map_smulₛₗ, f.map_smulₛₗ, Submodule.coe_smul, Submodule.coe_smul,
      tensor_laurent_smul, tensor_laurent_smul, map_smul, hx]

/-- Webster, Theorem 4.38. The comparison of prescribed words intertwines
the actual one-strand induction functor with the lowering generator. -/
theorem map_blackLower (i : I) (x : DirectSum (Multiset I) (tensorProjectiveGroup C hQ Λ)) :
    (f (blackLower (wordGrading C hQ Λ) i x) : TensorSpace wt) =
      tensorRepresentation wt (F R v i) (f x : TensorSpace wt) := by
  have h := blackLower_pow_eq_qfact_smul Λ C hQ i 1
  simp only [pow_one, qfact_one, one_smul] at h
  rw [h]
  simpa [qDivPow, qFactorial, qInt] using map_blackDividedLower C hQ Λ wt f hw i 1 x

end Black

section Red
variable (Λ : Fin (ℓ + 1) → I →₀ ℕ)
local notation "Λ₀" => (Λ ∘ Fin.castSucc)
local notation "G" => wordGrading C hQ Λ

omit [DecidableEq I] in
private theorem restrictGrade_eq : restrictRedGrading Q Λ G = wordGrading C hQ Λ₀ := by
  unfold restrictRedGrading wordGrading stendhalGradingDatum
  congr 1
  · funext a
    cases a <;> rfl
  · funext a b
    cases a <;> cases b <;> rfl

private def lastRedIndAt (D : GradingDatum (stendhalQ Q Λ₀)) (h : restrictRedGrading Q Λ G = D)
    (β : Multiset I) : K0 (tensorProductGrade D β) →ₗ[LP] tensorProjectiveGroup C hQ Λ β :=
  h ▸ lastRedIndK0 G β

private theorem lastRedIndAt_word (D : GradingDatum (stendhalQ Q Λ₀)) (h : restrictRedGrading Q Λ G = D)
    (w : TensorWord I ℓ) :
    lastRedIndAt C hQ Λ D h w.content.toMultiset (K0.of (sequenceProj D w.loading w.blocks_redOrdered)) =
      K0.of (sequenceProj G w.red.loading w.red.blocks_redOrdered) := by
  subst D
  exact tensorWordSequenceProj_red G w

/-- The sum of Webster's last-red induction functors over all black contents
(arXiv:1309.3796v2, proof of Lemma 4.37). -/
def totalLastRedIndK0 : DirectSum (Multiset I) (tensorProjectiveGroup C hQ Λ₀) →ₗ[LP] DirectSum (Multiset I) (tensorProjectiveGroup C hQ Λ) :=
  DirectSum.toModule _ _ _ fun β => DirectSum.lof LP _ (tensorProjectiveGroup C hQ Λ) β ∘ₗ
    lastRedIndAt C hQ Λ _ (restrictGrade_eq C hQ Λ) β

private theorem expandedClass_factorial {n : ℕ} (L : Fin n → I →₀ ℕ) (w : TensorWord I n) :
    DirectSum.lof LP _ (tensorProjectiveGroup C hQ L) w.content.toMultiset
      (K0.of (sequenceProj (wordGrading C hQ L) w.loading w.blocks_redOrdered)) =
      divQFact2 C w.blackBlocks • tensorWordProjectiveClass L C hQ w := by
  rw [tensorWordProjectiveClass, ← LinearMap.map_smul]
  exact congrArg _ (tensorWordProjective_factorial L C hQ w)

/-- Terminal-red induction appends the last red to a divided word with its
projective grading shift (Webster, §4.7, Lemma 4.37). -/
theorem totalLastRedIndK0_tensorWordProjectiveClass (w : TensorWord I ℓ) :
    totalLastRedIndK0 C hQ Λ (tensorWordProjectiveClass Λ₀ C hQ w) =
      tensorWordProjectiveClass Λ C hQ w.red := by
  have hn : divQFact2 C w.blackBlocks ≠ 0 := fun h =>
    KL2Gamma.qToV_divQFact2_ne_zero C _ (by rw [h, map_zero])
  apply totalK0_smul_injective Λ C hQ hn
  dsimp only
  rw [← map_smul, ← expandedClass_factorial, ← show w.red.blackBlocks = w.blackBlocks from rfl,
    ← expandedClass_factorial, totalLastRedIndK0, DirectSum.toModule_lof, LinearMap.comp_apply,
    lastRedIndAt_word]
  rfl

variable [Finite I] (wt : Fin (ℓ + 1) → Dom R) {σ : LP →+* LP}
local notation "wt₀" => fun j : Fin ℓ => wt (Fin.castSucc j)
local notation "high" => IrreducibleModule.hwv R v (Subtype.val (wt (Fin.last ℓ)))

/-- Webster, arXiv:1309.3796v2, Lemma 4.37. A word-preserving comparison
tensors every earlier projective class with the highest vector when the
last red strand is appended. -/
theorem map_totalLastRedIndK0
    (f₀ : DirectSum (Multiset I) (tensorProjectiveGroup C hQ Λ₀) →ₛₗ[σ] integralTensor wt₀)
    (f : DirectSum (Multiset I) (tensorProjectiveGroup C hQ Λ) →ₛₗ[σ] integralTensor wt)
    (hw₀ : ∀ w, f₀ (tensorWordProjectiveClass Λ₀ C hQ w) = integralWordVector (C := C) wt₀ w)
    (hw : ∀ w, f (tensorWordProjectiveClass Λ C hQ w) = integralWordVector (C := C) wt w)
    (x : DirectSum (Multiset I) (tensorProjectiveGroup C hQ Λ₀)) :
    (f (totalLastRedIndK0 C hQ Λ x) : TensorSpace wt) = appendTensor wt (f₀ x : TensorSpace wt₀) high := by
  have hx : x ∈ Submodule.span LP (Set.range (tensorWordProjectiveClass Λ₀ C hQ)) := by
    rw [span_tensorWordProjectiveClass]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w,rfl⟩ := hz
    rw [totalLastRedIndK0_tensorWordProjectiveClass, hw, hw₀]
    rfl
  | zero => simp [appendTensor]
  | add x y _ _ hx hy =>
    simp only [map_add, Submodule.coe_add, hx, hy, appendTensor, TensorProduct.add_tmul]
  | smul a x _ hx =>
    rw [map_smul, f.map_smulₛₗ, f₀.map_smulₛₗ, Submodule.coe_smul, Submodule.coe_smul,
      tensor_laurent_smul, tensor_laurent_smul, hx, appendTensor, appendTensor,
      ← TensorProduct.smul_tmul', map_smul]

end Red
end Categorification.Stendhal.FirstWeight
