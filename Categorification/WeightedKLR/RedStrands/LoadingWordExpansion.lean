/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.IteratedStandardCharacter
import Categorification.WeightedKLR.RedStrands.CyclotomicWordCharacter
import Categorification.WeightedKLR.RedStrands.TensorWordRaising

/-!
# Word tensors under the lowering operators

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 5.20 and of Lemma 6.11. By the coproduct `Δ(F_i) = F_i ⊗ K_i^{-1} + 1 ⊗ F_i`, the
lowering operator `F_i` sends the word tensor `F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_ℓ} v_{λ_ℓ}` to a sum of
word tensors with monomial coefficients, one for each factor that receives the new letter
(`F_wordTensor`). Each such sum is recorded as a list of pairs `(d, u)` standing for `v^d` times
the word tensor of `u` (`monoSum`).
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

variable {I : Type} [DecidableEq I] {C : QuantumGroup.CartanDatum I}
  {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y}

local notation "𝕂" => RatFunc ℚ
local notation "v" => (RatFunc.X : 𝕂)
private local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

/-- The weight `λ - Σ_{i ∈ u} α_i` of `F_u v_λ`. -/
def wordWeight (w : Dom R) (u : List I) : Y →+ ℤ :=
  w.1 - R.rootSum (u : Multiset I).toFinsupp

theorem ordinarySuffixOp_hwv_mem_weightSpace (w : Dom R) (u : List I) :
    ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂 (IrreducibleModule R v w.1) (F R v i)) u
        (IrreducibleModule.hwv R v w.1) ∈
      weightSpace R v (IrreducibleModule R v w.1) (wordWeight w u) :=
  ordinarySuffixOp_mem_weightSpace C (R := R) w u IrreducibleModule.hwv_mem_weightSpace

omit [DecidableEq I] in
theorem ordinarySuffixOp_append_singleton {V : Type*} [AddCommGroup V] [Module 𝕂 V]
    (act : I → Module.End 𝕂 V) (u : List I) (i : I) :
    ordinarySuffixOp act (u ++ [i]) = act i * ordinarySuffixOp act u := by
  induction u with
  | nil => simp [ordinarySuffixOp]
  | cons a u ih => rw [List.cons_append, ordinarySuffixOp, ih, ordinarySuffixOp, mul_assoc]

/-- The monomials of `F_i` applied to a word tensor: the letter `i` is appended to the word of
one factor, with the power of `v` from `K_i^{-1}` on the factors after it. -/
def wordF (i : I) : {n : ℕ} → (Fin n → Dom R) → (Fin n → List I) → List (ℤ × (Fin n → List I))
  | 0, _, _ => []
  | n + 1, wt, u =>
    ((wordF i (fun j => wt (Fin.castSucc j)) (fun j => u (Fin.castSucc j))).map fun p =>
      (p.1 - wordWeight (wt (Fin.last n)) (u (Fin.last n)) (ktilde R i),
        Fin.lastCases (u (Fin.last n)) p.2)) ++
      [(0, Fin.lastCases (u (Fin.last n) ++ [i]) fun j => u (Fin.castSucc j))]

variable {n : ℕ}

/-- The vector `Σ_{(d, u)} v^d F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_n} v_{λ_n}` of a list of monomials. -/
def monoSum (wt : Fin n → Dom R) (l : List (ℤ × (Fin n → List I))) : TensorSpace wt :=
  (l.map fun p => (v ^ p.1 : 𝕂) • wordTensor C wt p.2).sum

theorem monoSum_append (wt : Fin n → Dom R) (l l' : List (ℤ × (Fin n → List I))) :
    monoSum wt (l ++ l') = monoSum wt l + monoSum wt l' := by
  simp [monoSum]

theorem wordTensor_lastCases (wt : Fin (n + 1) → Dom R) (u : Fin n → List I) (a : List I) :
    wordTensor C wt (Fin.lastCases a u) = appendTensor wt (wordTensor C (fun j => wt (Fin.castSucc j)) u)
      (ordinarySuffixOp (fun i => Algebra.lsmul 𝕂 𝕂 _ (F R v i)) a
        (IrreducibleModule.hwv R v (wt (Fin.last n)).1)) := by
  rw [wordTensor_succ]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last]

/-- **`F_i` on a word tensor** (Webster, arXiv:1309.3796v2, proof of Proposition 5.20): a sum
of word tensors with monomial coefficients. -/
theorem F_wordTensor (i : I) : ∀ {n : ℕ} (wt : Fin n → Dom R) (u : Fin n → List I),
    tensorRepresentation wt (F R v i) (wordTensor C wt u) = monoSum wt (wordF i wt u)
  | 0, wt, u => by
    change counit R v (F R v i) • wordTensor C wt u = _
    rw [counit_F, zero_smul]
    rfl
  | n + 1, wt, u => by
    have hu : u = Fin.lastCases (u (Fin.last n)) fun j => u (Fin.castSucc j) := by
      funext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
    conv_lhs => rw [hu, wordTensor_lastCases, tensorRepresentation_F_append,
      F_wordTensor i (fun j => wt (Fin.castSucc j)) (fun j => u (Fin.castSucc j))]
    rw [wordF, monoSum_append]
    congr 1
    · rw [ordinarySuffixOp_hwv_mem_weightSpace (wt (Fin.last n)) (u (Fin.last n)) (-ktilde R i),
        monoSum, monoSum, List.map_map]
      rw [map_neg]
      generalize (wordF i (fun j => wt (Fin.castSucc j)) fun j => u (Fin.castSucc j)) = l
      induction l with
      | nil => simp [appendTensor]
      | cons p l ih =>
        rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ← ih]
        simp only [Function.comp_apply, appendTensor, TensorProduct.add_tmul, map_add]
        congr 1
        rw [wordTensor_lastCases, appendTensor, TensorProduct.smul_tmul_smul, map_smul,
          sub_eq_add_neg, zpow_add₀ (RatFunc.X_ne_zero : (RatFunc.X : 𝕂) ≠ 0)]
    · rw [monoSum, List.map_singleton, List.sum_singleton, zpow_zero, one_smul,
        wordTensor_lastCases, ordinarySuffixOp_append_singleton, Module.End.mul_apply]
      rfl

/-- `F_i` on a sum of word tensors with monomial coefficients. -/
def monoF (i : I) (wt : Fin n → Dom R) (l : List (ℤ × (Fin n → List I))) :
    List (ℤ × (Fin n → List I)) :=
  l.flatMap fun p => (wordF i wt p.2).map fun q => (p.1 + q.1, q.2)

theorem F_monoSum (i : I) (wt : Fin n → Dom R) (l : List (ℤ × (Fin n → List I))) :
    tensorRepresentation wt (F R v i) (monoSum (C := C) wt l) = monoSum (C := C) wt (monoF i wt l) := by
  induction l with
  | nil => simp [monoSum, monoF]
  | cons p l ih =>
    rw [monoF, List.flatMap_cons, ← monoF, monoSum_append, ← ih]
    simp only [monoSum, List.map_cons, List.sum_cons, map_add, map_smul]
    congr 1
    rw [F_wordTensor, monoSum, List.smul_sum, List.map_map, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun q _ => ?_)
    simp only [Function.comp_apply, smul_smul, zpow_add₀ (RatFunc.X_ne_zero : (RatFunc.X : 𝕂) ≠ 0)]

/-- Appending a red strand, `x ↦ x ⊗ v_λ`, on monomials: the new factor has the empty word. -/
def monoRed (l : List (ℤ × (Fin n → List I))) : List (ℤ × (Fin (n + 1) → List I)) :=
  l.map fun p => (p.1, Fin.lastCases [] p.2)

theorem appendTensor_monoSum (wt : Fin (n + 1) → Dom R) (l : List (ℤ × (Fin n → List I))) :
    appendTensor wt (monoSum (C := C) (fun j => wt (Fin.castSucc j)) l)
        (IrreducibleModule.hwv R v (wt (Fin.last n)).1) = monoSum (C := C) wt (monoRed l) := by
  induction l with
  | nil => simp [monoSum, monoRed, appendTensor]
  | cons p l ih =>
    rw [monoRed, List.map_cons, ← monoRed, monoSum, List.map_cons, List.sum_cons, monoSum,
      List.map_cons, List.sum_cons, ← monoSum, ← monoSum, ← ih, wordTensor_lastCases]
    simp only [appendTensor, TensorProduct.add_tmul, map_add, ordinarySuffixOp,
      Module.End.one_apply]
    rw [← TensorProduct.smul_tmul', map_smul]

variable {J : Type*}

/-- The monomials of a loading read from its last letter. -/
def monoReverse : (s : List (I ⊕ J)) → {n : ℕ} → (wt : Fin n → Dom R) →
    List (ℤ × (Fin n → List I))
  | [], 0, _ => [(0, Fin.elim0)]
  | [], _ + 1, _ => []
  | .inl i :: s, _, wt => monoF i wt (monoReverse s wt)
  | .inr _ :: _, 0, _ => []
  | .inr _ :: s, _ + 1, wt => monoRed (monoReverse s fun j => wt (Fin.castSucc j))

/-- **The parameter set of a loading** (Webster, arXiv:1309.3796v2, Proposition 5.20): the
monomials of the vector read from the loading `s`. -/
def loadingMono (wt : Fin n → Dom R) (s : List (I ⊕ J)) : List (ℤ × (Fin n → List I)) :=
  monoReverse s.reverse wt

/-- **The vector of a loading is a sum of word tensors** with monomial coefficients, indexed by
`loadingMono`. -/
theorem loadingVector_eq_monoSum (s : List (I ⊕ J)) : ∀ {n : ℕ} (wt : Fin n → Dom R),
    loadingVector wt s = monoSum (C := C) wt (loadingMono wt s) := by
  induction s using List.reverseRecOn with
  | nil =>
    intro n wt
    cases n with
    | zero =>
      rw [loadingVector_nil_zero, loadingMono, List.reverse_nil, monoReverse, monoSum,
        List.map_singleton, List.sum_singleton, zpow_zero, one_smul]
      exact congrArg (PiTensorProduct.tprod 𝕂) (funext fun j => j.elim0)
    | succ n => rw [loadingVector_nil_succ]; rfl
  | append_singleton s z ih =>
    intro n wt
    cases z with
    | inl i =>
      rw [loadingVector_append_inl, ih, F_monoSum]
      simp only [loadingMono, List.reverse_append]
      rfl
    | inr r =>
      cases n with
      | zero =>
        rw [loadingVector_append_inr_zero]
        simp only [loadingMono, List.reverse_append]
        rfl
      | succ n =>
        rw [loadingVector_append_inr, ih, appendTensor_monoSum]
        simp only [loadingMono, List.reverse_append]
        rfl

end Categorification.Stendhal.FirstWeight
