/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedShuffleDegree
import Categorification.WeightedKLR.RedStrands.OrdinaryShuffleSum

/-!
# Parabolic shuffle exponents and the ordinary tensor coproduct

In Webster, arXiv:1309.3796v2, §§4.6–4.7 and (5.10), the earlier letters of
a shuffle belong to the prefix factor, and the final red strand belongs to
the last factor. The sum of the remaining right-before-left crossing degrees
then equals the ordinary tensor-word exponent on the tagged black suffix.
-/

namespace Categorification.Stendhal.FirstWeight

open QuantumGroup LieLean.QuantumGroup

private theorem falsePrefix {J : Type*} (f : J → J → ℤ) (pre : List J) (tail : List (J × Bool)) :
    shuffleCrossingSum f (pre.map (fun z => (z,false)) ++ tail) = shuffleCrossingSum f tail := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simpa [shuffleCrossingSum] using ih

private theorem rightBlackSum {I : Type*} (C : CartanDatum I) (highest : I →₀ ℕ) (ℓ : ℕ)
    (tags : List (I × Bool)) (i : I) :
    List.sum (List.map (fun z => lastRedCrossing C highest z.1 (.inl i))
      ((tags.map (fun z => ((Sum.inl z.1 : I ⊕ Fin (ℓ+1)),z.2))).filter Prod.snd)) =
    -((maskSubword true tags).map (C.dot i)).sum := by
  induction tags with
  | nil => simp [maskSubword]
  | cons z tags ih =>
    obtain ⟨j,b⟩ := z
    cases b <;> simp_all [maskSubword,lastRedCrossing,add_comm]

/-- The crossing exponent for a normalized last-red shuffle in Webster,
arXiv:1309.3796v2, §§4.6–4.7, agrees with the ordinary bar-coproduct
exponent in (5.10), for every assignment of its black suffix. -/
theorem lastRedCrossingSum_eq_suffixMaskExponent {I Y : Type*} [AddCommGroup Y]
    (C : CartanDatum I) {R : C.toLusztig.RootDatum Y} (highest : I →₀ ℕ) (μ : Y →+ ℤ)
    (hhighest : ∀ i, μ (R.coroot i) = (highest i : ℤ)) {ℓ : ℕ}
    (pre : List (I ⊕ Fin (ℓ+1))) (tags : List (I × Bool)) :
    shuffleCrossingSum (lastRedCrossing C highest)
      ((pre.map (fun z => (z,false))) ++ [(Sum.inr (Fin.last ℓ),true)] ++
        tags.map (fun z => ((Sum.inl z.1 : I ⊕ Fin (ℓ+1)),z.2))) =
      suffixMaskExponent R μ tags := by
  rw [List.append_assoc,falsePrefix]
  induction tags using List.reverseRecOn with
  | nil => rfl
  | append_singleton tags z ih =>
    obtain ⟨i,b⟩ := z
    simp only [List.map_append,List.map_cons,List.map_nil]
    rw [← List.append_assoc,shuffleCrossingSum_snoc,suffixMaskExponent_snoc,ih]
    congr 1
    cases b with
    | true => rfl
    | false =>
      change C.dot i i / 2 * (highest i : ℤ) +
        List.sum (List.map (fun z => lastRedCrossing C highest z.1 (.inl i))
          ((tags.map (fun z => ((Sum.inl z.1 : I ⊕ Fin (ℓ+1)),z.2))).filter Prod.snd)) = _
      simp only [Bool.false_eq_true,↓reduceIte]
      rw [rightBlackSum,shuffleExponent_eq_crossings,hhighest]
      have h := C.toLusztig.two_mul_d i
      change 2 * (C.toLusztig.d i : ℤ) = C.dot i i at h
      rw [show (C.toLusztig.d i : ℤ) = C.dot i i / 2 by omega]
      rfl

end Categorification.Stendhal.FirstWeight
