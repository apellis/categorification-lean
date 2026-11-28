/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalStandard

/-!
# The diagonal corner in loading coordinates

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, the `Tor_0` term on the diagonal. `SMove.finrank_fixSub_diagonalStandard`
computes the fixed vectors of a loading idempotent written in cut coordinates (the prefix
loading `(red₁ 𝐣)` of the outer cut, appended with `(red₃)`). This file identifies that
idempotent with the idempotent `e(s)` of the loading `s = (red₁ red₂ 𝐮' red₃)`, so that the
dimension statement is literally about `e(s') S_s`.

## Main results

* `Stendhal.tensorLoad_eq_seqIdem`: for a red-ordered loading the two encodings of the loading
  idempotent of `T^λ` agree.
* `Stendhal.SMove.cutLoad_eq_seqIdem_diagonalLoading`: the cut-coordinate idempotent is
  `e(red₁ red₂ 𝐮' red₃)`.
* `Stendhal.SMove.finrank_fixSub_seqIdem_diagonalStandard`: the dimension of
  `{v ∈ S_s : e(s') v = v}` for `s = (red₁ red₂ 𝐮 red₃)`, `s' = (red₁ red₂ 𝐮' red₃)`.
* `Stendhal.SMove.finrank_fixSub_seqIdem_diagonalStandard_self`: the case `𝐮' = 𝐮`.

No route hypotheses beyond a Rouquier choice of `Q` (needed for the Hu–Shi formula).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra
open scoped TensorProduct

/-! ### Words of sequences -/

namespace SMove

section Words

variable {J : Type*}

/-- Two sequences of the same weight with the same word are equal. -/
theorem seq_eq_of_seqWord_eq {μ : Multiset J} {s t : Seq μ} (h : List.ofFn s.1 = List.ofFn t.1) :
    s = t :=
  Subtype.ext (List.ofFn_injective h)

/-- `Seq.cast` does not change the word. -/
theorem seqWord_cast {μ μ' : Multiset J} (h : μ = μ') (s : Seq μ) :
    List.ofFn (Seq.cast h s).1 = List.ofFn s.1 := by
  subst h; rfl

/-- The word of `Seq.map f s` is the image of the word of `s`. -/
theorem seqWord_map {J' : Type*} (f : J → J') {μ : Multiset J} (s : Seq μ) :
    List.ofFn (Seq.map f s).1 = (List.ofFn s.1).map f := by
  apply List.ext_getElem
  · simp
  · intro n h₁ h₂
    simp only [List.getElem_ofFn, List.getElem_map]
    rfl

/-- The word of a concatenation is the concatenation of the words. -/
theorem seqWord_append {μ μ' : Multiset J} (s : Seq μ) (t : Seq μ') :
    List.ofFn (s.append t).1 = List.ofFn s.1 ++ List.ofFn t.1 := by
  apply List.ext_getElem
  · simp [Multiset.card_add]
  · intro n h₁ h₂
    simp only [List.length_ofFn] at h₁
    rw [List.getElem_append]
    split_ifs with hn
    · simp only [List.getElem_ofFn]
      simp only [List.length_ofFn] at hn
      exact Seq.append_posL s t ⟨n, hn⟩
    · simp only [List.getElem_ofFn]
      simp only [List.length_ofFn, not_lt] at hn
      have hlt : n - Multiset.card μ < Multiset.card μ' := by
        rw [Multiset.card_add] at h₁; omega
      have := Seq.append_posR s t ⟨n - Multiset.card μ, hlt⟩
      convert this using 2
      all_goals (apply Fin.ext; simp only [Seq.posR_val, List.length_ofFn]; try omega)

/-- A sequence of a singleton weight has a one-letter word. -/
theorem seqWord_singleton {μ : Multiset J} {x : J} (hμ : μ = {x}) (s : Seq μ) :
    List.ofFn s.1 = [x] := by
  subst hμ
  apply List.ext_getElem
  · simp
  · intro n h₁ h₂
    simp only [List.getElem_ofFn, List.getElem_singleton]
    exact Multiset.mem_singleton.1 (s.mem _)

/-- A sequence of the zero weight has the empty word. -/
theorem seqWord_zero {μ : Multiset J} (hμ : μ = 0) (s : Seq μ) : List.ofFn s.1 = [] := by
  subst hμ
  simp

end Words

end SMove

/-! ### The two encodings of a loading idempotent -/

section Load

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)

/-- For a red-ordered loading `c`, the loading idempotent `tensorLoad c` (projection of the
idempotent of all orders) is the idempotent `e(c)` of the ordered algebra. -/
theorem tensorLoad_eq_seqIdem {n : ℕ} (Λ : Fin n → I →₀ ℕ) (ν : Multiset I)
    (c : Seq (stendhalWeight n ν)) (hc : IsRedOrdered c) :
    tensorLoad Q Λ ν c = seqIdem Q Λ c hc := by
  unfold tensorLoad seqIdem
  apply congrArg (TensorProductAlgebra.mk Q Λ ν)
  apply Subtype.ext
  change StendhalAlgebraAllOrders.e c * StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν =
    StendhalAlgebraAllOrders.e c
  rw [StendhalAlgebraAllOrders.e_mul_redOrderedIdem]
  simp only [hc, ↓reduceIte]

end Load

/-! ### The S-move loading -/

namespace SMove

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (2 + 1) → I →₀ ℕ) (β : Multiset I)

omit [DecidableEq I] in
/-- The word of the one-red loading `(red₂ 𝐮)`. -/
theorem seqWord_insertWord (u : Seq β) :
    List.ofFn (SingleRed.insertWord β u).1 =
      (Sum.inr 0 : I ⊕ Fin 1) :: (List.ofFn u.1).map Sum.inl := by
  unfold SingleRed.insertWord
  rw [seqWord_cast, seqWord_append, seqWord_map, seqWord_singleton rfl]
  rfl

omit [DecidableEq I] in
theorem seqWord_oneZero (t : Seq (stendhalWeight 1 (0 : Multiset I))) :
    List.ofFn t.1 = [(Sum.inr 0 : I ⊕ Fin 1)] :=
  seqWord_singleton (by simp [stendhalWeight]) t

omit [DecidableEq I] in
/-- The cut-coordinate loading of `SMove.finrank_fixSub_diagonalStandard`, transported to
`T^λ(β)`, is the loading `(red₁ red₂ 𝐮' red₃)` of `SMove.diagonalLoading`. -/
theorem seqCast_cutLoading_eq_diagonalLoading (t : Seq (stendhalWeight 1 (0 : Multiset I)))
    (ht : IsRedOrdered t) (u' : Seq β) (u₀ : Seq (0 : Multiset I))
    (i : Seq (Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1))
      (stendhalWeight 1 (0 : Multiset I))))
    (j₃ : Seq (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2))
      (stendhalWeight 1 (0 : Multiset I)))) :
    Seq.cast (congrArg (stendhalWeight (2 + 1)) (add_zero β))
        (Seq.cast (cutInputWeights_add (a := 2) (r := 1) β 0)
          ((innerLoading Q Λ β i (middleLoading Q Λ β u')).append j₃)) =
      (diagonalLoading β t ht u' u₀).1 := by
  apply seq_eq_of_seqWord_eq
  unfold diagonalLoading twoPieceLabel twoPieceLoading concatLoading innerLoading
    middleLoading
  simp only [redSubfamilyRelabel, SeqRelabel.ofInjective, Seq.mapEquiv_apply]
  simp only [seqWord_cast, seqWord_append, seqWord_map, seqWord_insertWord, seqWord_oneZero t,
    seqWord_zero rfl u₀,
    seqWord_singleton (x := (Sum.inr (Fin.castAdd 1 0) : I ⊕ Fin (1 + 1)))
      (by simp [stendhalWeight]) i,
    seqWord_singleton (x := (Sum.inr (Fin.natAdd 2 0) : I ⊕ Fin (2 + 1)))
      (by simp [stendhalWeight]) j₃]
  simp only [List.map_cons, List.map_nil, List.map_map, List.cons_append, List.nil_append,
    Sum.map_inr]
  rfl

/-- **The cut-coordinate idempotent is `e(red₁ red₂ 𝐮' red₃)`** (Webster, arXiv:1309.3796v3,
§7.3, proof of Proposition 7.22). -/
theorem cutLoad_eq_seqIdem_diagonalLoading (t : Seq (stendhalWeight 1 (0 : Multiset I)))
    (ht : IsRedOrdered t) (u' : Seq β) (u₀ : Seq (0 : Multiset I))
    (i : Seq (Multiset.map (Sum.map (id : I → I) (Fin.castAdd 1))
      (stendhalWeight 1 (0 : Multiset I))))
    (j₃ : Seq (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2))
      (stendhalWeight 1 (0 : Multiset I)))) :
    cutLoad Q Λ (add_zero β) ((innerLoading Q Λ β i (middleLoading Q Λ β u')).append j₃) =
      seqIdem Q Λ (diagonalLoading β t ht u' u₀).1 (diagonalLoading β t ht u' u₀).2 := by
  rw [cutLoad, ← seq_cast_symm_cast (cutInputWeights_add (a := 2) (r := 1) β 0)
      ((innerLoading Q Λ β i (middleLoading Q Λ β u')).append j₃),
    ← tensorLoad_eq_affineToTensor (a := 2) (r := 1), cast_tensorLoad,
    seqCast_cutLoading_eq_diagonalLoading Q Λ β t ht u' u₀ i j₃, tensorLoad_eq_seqIdem]

include hQ in
/-- **The dimension of `e(s') S_s` on the diagonal** (Webster, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, `Tor_0` on the diagonal): for a Rouquier choice of `Q`,
`s = (red₁ red₂ 𝐮 red₃)` and `s' = (red₁ red₂ 𝐮' red₃)`, the vectors of the standard module
`S_s` fixed by `e(s')` have the dimension of the cyclotomic corner `e(𝐮') R^{λ_2}(β) e(𝐮)`,
given by the Hu–Shi permutation formula. -/
theorem finrank_fixSub_seqIdem_diagonalStandard {C : QuantumGroup.CartanDatum I}
    (hP : IsRouquierQ C Q) (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t)
    (u u' : Seq β) (u₀ : Seq (0 : Multiset I)) :
    (Module.finrank k (fixSub k
        (leftStandard Q Λ (diagonalLoading β t ht u u₀).1 (diagonalLoading β t ht u u₀).2)
        (seqIdem Q Λ (diagonalLoading β t ht u' u₀).1 (diagonalLoading β t ht u' u₀).2))
      : ℤ) =
      ∑ w : Equiv.Perm (Fin β.card) with ∀ j, u'.1 j = u.1 (w j),
        ∏ j, CycKLR.huShiN C ((Λ ∘ Fin.castAdd 1 : Fin (1 + 1) → I →₀ ℕ) (Fin.last 1))
          u'.1 w j := by
  rw [← cutLoad_eq_seqIdem_diagonalLoading Q Λ β t ht u' u₀
    (Seq.map (Sum.map (id : I → I) (Fin.castAdd 1)) t)
    (Seq.map (Sum.map (id : I → I) (Fin.natAdd 2)) t)]
  exact finrank_fixSub_diagonalStandard Q hQ Λ β hP t ht u u' u₀ _ _

include hQ in
/-- **The diagonal corner `e(s) S_s`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22): the case `𝐮' = 𝐮` of `finrank_fixSub_seqIdem_diagonalStandard`. -/
theorem finrank_fixSub_seqIdem_diagonalStandard_self {C : QuantumGroup.CartanDatum I}
    (hP : IsRouquierQ C Q) (t : Seq (stendhalWeight 1 (0 : Multiset I))) (ht : IsRedOrdered t)
    (u : Seq β) (u₀ : Seq (0 : Multiset I)) :
    (Module.finrank k (fixSub k
        (leftStandard Q Λ (diagonalLoading β t ht u u₀).1 (diagonalLoading β t ht u u₀).2)
        (seqIdem Q Λ (diagonalLoading β t ht u u₀).1 (diagonalLoading β t ht u u₀).2))
      : ℤ) =
      ∑ w : Equiv.Perm (Fin β.card) with ∀ j, u.1 j = u.1 (w j),
        ∏ j, CycKLR.huShiN C ((Λ ∘ Fin.castAdd 1 : Fin (1 + 1) → I →₀ ℕ) (Fin.last 1))
          u.1 w j :=
  finrank_fixSub_seqIdem_diagonalStandard Q hQ Λ β hP t ht u u u₀

end SMove

end Categorification.Stendhal
