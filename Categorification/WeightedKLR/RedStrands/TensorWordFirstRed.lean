/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.NegativeTensor
import Categorification.WeightedKLR.RedStrands.TensorWordWeights

/-!
# Tensor words with black strands before the first red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 4.39. A black divided block placed before every red strand acts on the empty
tensor product through the counit, so it kills the tensor vector unless its multiplicity is
zero. Hence every tensor vector of `V_{λ₀} ⊗ V^λ` is zero or the tensor vector of a word that
begins with the red strand `λ₀` (`tensorWordVector_eq_zero_or`).

## Main definitions

* `TensorWord.eraseFirstRed` : delete the first red strand and everything before it.

## Main results

* `tensorWordVector_eq_zero_or` : `p_w = 0` or `p_w = p_{r(e(w))}`.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance instNeZeroXTensorWordFirstRed : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y}

local notation "divF" => fun (i : I) (n : ℕ) => qDivPow (𝕍 ^ D.d i) n (F R 𝕍 i)

/-- Delete the first red strand of a word, and every black block before it. -/
def TensorWord.eraseFirstRed : {n : ℕ} → TensorWord I (n + 1) → TensorWord I n
  | 0, .red _ => .empty
  | _ + 1, .red w => .red w.eraseFirstRed
  | _, .black w i a => .black w.eraseFirstRed i a

omit [DecidableEq I] in
theorem TensorWord.eraseFirstRed_red_zero (w : TensorWord I 0) :
    (TensorWord.red w).eraseFirstRed = .empty := by
  rw [TensorWord.eraseFirstRed]

omit [DecidableEq I] in
theorem TensorWord.eraseFirstRed_red_succ {n : ℕ} (w : TensorWord I (n + 1)) :
    (TensorWord.red w).eraseFirstRed = .red w.eraseFirstRed := by
  rw [TensorWord.eraseFirstRed]

omit [DecidableEq I] in
theorem TensorWord.eraseFirstRed_black {n : ℕ} (w : TensorWord I (n + 1)) (i : I) (a : ℕ) :
    (TensorWord.black w i a).eraseFirstRed = .black w.eraseFirstRed i a := by
  rw [TensorWord.eraseFirstRed]

/-- The counit of a divided power of `F_i`. -/
theorem counit_divF (i : I) (a : ℕ) :
    counit R 𝕍 (divF i a) = if a = 0 then 1 else 0 := by
  rw [map_qDivPow', counit_F, qDivPow]
  rcases a with _ | a
  · simp [qFactorial]
  · simp

/-- A tensor vector of words without red strands is `0` or the empty tensor. -/
theorem tensorWordVector_zero_red : ∀ (w : TensorWord I 0) (wt : Fin 0 → Dom R),
    tensorWordVector w wt = 0 ∨
      (tensorWordVector w wt = PiTensorProduct.tprod 𝕂 (fun j => IrreducibleModule.hwv R 𝕍 (wt j).1)
        ∧ w.content = 0)
  | .empty, _ => Or.inr ⟨rfl, rfl⟩
  | .black w i a, wt => by
    change tensorRepresentation wt (divF i a) (tensorWordVector w wt) = 0 ∨
      (tensorRepresentation wt (divF i a) (tensorWordVector w wt) = _ ∧
        w.content + Finsupp.single i a = 0)
    rw [tensorRepresentation_zero, counit_divF]
    rcases tensorWordVector_zero_red w wt with h | ⟨h, hc⟩
    · left; rw [h, smul_zero]
    · split_ifs with ha
      · right
        refine ⟨by rw [one_smul, h], ?_⟩
        rw [hc, ha, Finsupp.single_zero, add_zero]
      · left; rw [zero_smul]

/-- **Every tensor vector is `0` or comes from a word beginning with the first red strand**
(Webster, arXiv:1309.3796v3, proof of Proposition 4.39). -/
theorem tensorWordVector_eq_zero_or : ∀ {n : ℕ} (w : TensorWord I (n + 1))
    (wt : Fin (n + 1) → Dom R),
    tensorWordVector w wt = 0 ∨ (tensorWordVector w wt =
      tensorWordVector w.eraseFirstRed.prependRed wt ∧ w.eraseFirstRed.content = w.content)
  | 0, .red w, wt => by
    rw [TensorWord.eraseFirstRed_red_zero]
    change appendTensor wt (tensorWordVector w _) _ = 0 ∨
      (appendTensor wt (tensorWordVector w _) _ = appendTensor wt (tensorWordVector .empty _) _ ∧
        (0 : I →₀ ℕ) = w.content)
    rcases tensorWordVector_zero_red w (fun j => wt (Fin.castSucc j)) with h | ⟨h, hc⟩
    · left
      rw [h, appendTensor, TensorProduct.zero_tmul, map_zero]
    · right; exact ⟨by rw [h]; rfl, hc.symm⟩
  | _ + 1, .red w, wt => by
    rw [TensorWord.eraseFirstRed_red_succ]
    change appendTensor wt (tensorWordVector w _) _ = 0 ∨
      (appendTensor wt (tensorWordVector w _) _ =
        appendTensor wt (tensorWordVector w.eraseFirstRed.prependRed _) _ ∧
          w.eraseFirstRed.content = w.content)
    rcases tensorWordVector_eq_zero_or w (fun j => wt (Fin.castSucc j)) with h | ⟨h, hc⟩
    · left
      rw [h, appendTensor, TensorProduct.zero_tmul, map_zero]
    · right; exact ⟨by rw [h], hc⟩
  | _, .black w i a, wt => by
    rw [TensorWord.eraseFirstRed_black]
    change tensorRepresentation wt (divF i a) (tensorWordVector w wt) = 0 ∨
      (tensorRepresentation wt (divF i a) (tensorWordVector w wt) =
        tensorRepresentation wt (divF i a) (tensorWordVector w.eraseFirstRed.prependRed wt) ∧
          w.eraseFirstRed.content + Finsupp.single i a = w.content + Finsupp.single i a)
    rcases tensorWordVector_eq_zero_or w wt with h | ⟨h, hc⟩
    · left; rw [h, map_zero]
    · right; exact ⟨by rw [h], by rw [hc]⟩

omit [DecidableEq I] in
/-- Erasing the first red strand keeps the black content when nothing precedes it. -/
theorem TensorWord.eraseFirstRed_prependRed : ∀ {n : ℕ} (w : TensorWord I n),
    w.prependRed.eraseFirstRed = w
  | _, .empty => by rw [TensorWord.prependRed, TensorWord.eraseFirstRed]
  | _, .red w => by
    rw [TensorWord.prependRed, TensorWord.eraseFirstRed, TensorWord.eraseFirstRed_prependRed w]
  | _, .black w i a => by
    rw [TensorWord.prependRed, TensorWord.eraseFirstRed, TensorWord.eraseFirstRed_prependRed w]

omit [DecidableEq I] in
/-- Adding a red strand keeps the black content. -/
theorem TensorWord.content_prependRed : ∀ {n : ℕ} (w : TensorWord I n),
    w.prependRed.content = w.content
  | _, .empty => rfl
  | _, .red w => TensorWord.content_prependRed w
  | _, .black w i a => by
    change w.prependRed.content + Finsupp.single i a = w.content + Finsupp.single i a
    rw [TensorWord.content_prependRed w]

end Categorification.Stendhal.FirstWeight
