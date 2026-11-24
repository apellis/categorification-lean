/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.IndFirstSlide
import Categorification.WeightedKLR.RedStrands.RedBlackCrossingInjective
import Categorification.WeightedKLR.RedStrands.AddRed
import Categorification.WeightedKLR.RedStrands.BlackInduction

/-!
# The one-strand frame for a red–black crossing

Webster, arXiv:1309.3796v2, proof of Lemma 5.23. The first-factor Mackey diagram,
cut by a loading with the black strand just left of the red at the top, is the
single crossing with the black strand just right of the red at the bottom.
-/

namespace Categorification.KLR.KLRAlgebra

open TypeA

variable {I k : Type*} [DecidableEq I] [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k)

/-- On the indicated top and bottom loadings, the first-factor Mackey frame of a
singleton second block is precisely the single crossing with its bottom idempotent. -/
theorem e_mul_firstG_eq_ψ_mul_e_of_singleton (a b : Multiset I) (i : I)
    (hb : b.card = 1) (s t : Seq (a + b + {i}))
    (hs : s ∈ botSet (firstQuad_h a b i))
    (ht : t ∈ concatSet (a + b) {i})
    (hst : sadj (a + b + {i}).card a.card • s = t) :
    (e s * firstG Q a b i : KLRAlgebra k Q (a + b + {i})) = ψ a.card * e t := by
  rw [firstG, ← mul_assoc, ← mul_assoc, botOne, e_mul_eSum, ite_eq_left hs,
    firstψ_eq_ψ Q a b i hb, hflip_ψ, e_mul_ψ, hst, mul_assoc, oneConcat, e_mul_eSum,
    ite_eq_left ht]

end Categorification.KLR.KLRAlgebra

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

variable {I k : Type} [DecidableEq I] [Field k]

local notation "Si" i:max => (Singleton.singleton i : Multiset I)

/-- The top loading ending in black, red belongs to the bottom Mackey block. -/
theorem cast_blackRedLoading_mem_botSet
    {a b : Multiset (I ⊕ Fin 2)} (i : I) (θ : Multiset I)
    (u : Seq (stendhalWeight 1 (θ + 0)))
    (w : a + b + {Sum.inl i} = stendhalWeight 2 (Si i + (θ + 0)))
    (hb₁ : b.card = 1) (hb : ∀ r ∈ b, r = Sum.inr (Fin.last 1)) :
    Seq.cast w.symm (appendRedLoading (appendBlackLoading i (θ + 0) u)) ∈
      botSet (firstQuad_h a b (Sum.inl i)) := by
  let s := appendRedLoading (appendBlackLoading i (θ + 0) u)
  let j : I ⊕ Fin 2 := .inl i
  let h := firstQuad_h a b j
  let z := seqCast h.symm (Seq.cast w.symm s)
  have hlen := congrArg Multiset.card (h.trans w)
  have hz : z ∈ concatSet (a + {j}) b := by
    rw [mem_concatSet_iff_hasTail hb]
    refine ⟨by simp [hb₁], ?_⟩
    intro p hp
    have hlast : s.lbl (lastRedPosition 1 (Si i + (θ + 0))) = Sum.inr (Fin.last 1) :=
      hasLastRed_appendRedLoading (appendBlackLoading i (θ + 0) u)
    change (seqCast h.symm (Seq.cast w.symm s)).1 p = _
    rw [seqCast_apply, Seq.cast_apply]
    convert hlast using 1
    change s.lbl _ = s.lbl _
    apply congrArg s.lbl
    apply Fin.ext
    have hp' := hlen.ge.trans hp
    have hpl := p.isLt.trans_le hlen.le
    rw [hb₁] at hp'
    simp [stendhalWeight] at hp' hpl
    simp only [Fin.val_cast, lastRedPosition, Multiset.card_add, Multiset.card_singleton, add_zero]
    omega
  refine Finset.mem_image.2 ⟨z, hz, ?_⟩
  simp only [z, seqCast_eq_cast, Seq.cast_cast_symm, s]

/-- The bottom loading ending in red, black belongs to the singleton-black block. -/
theorem cast_redBlackLoading_mem_concatSet
    {a b : Multiset (I ⊕ Fin 2)} (i : I) (θ : Multiset I)
    (u : Seq (stendhalWeight 1 (θ + 0)))
    (w : a + b + {Sum.inl i} = stendhalWeight 2 (Si i + (θ + 0))) :
    Seq.cast w.symm (appendBlackLoading i (θ + 0) (appendRedLoading u)) ∈
      concatSet (a + b) {Sum.inl i} := by
  rw [mem_concatSet_singleton_iff, Seq.cast_apply]
  apply appendBlackLoading_lbl_of_eq
  change (a + b).card = (stendhalWeight 2 (θ + 0)).card
  have hlen := congrArg Multiset.card w
  simp [stendhalWeight] at hlen ⊢
  omega

section Suffix

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 2 → I →₀ ℕ)

/-- A straight black strand appended on the right preserves the index of a crossing
and appends the black label to its bottom idempotent. -/
theorem cast_appendR_ψ_mul_e (j : I) (ν : Multiset I)
    (a : ℕ) (ha : a + 1 < (stendhalWeight 2 ν).card) (t : Seq (stendhalWeight 2 ν)) :
    castKLR (stendhalQ Q Λ) (stendhalWeight_addBlack j ν)
      (appendR (stendhalQ Q Λ) _ (Sum.inl j) (ψ a * e t)) =
      ψ a * e (appendBlackLoading j ν t) := by
  let S := stendhalQ Q Λ
  let A := stendhalWeight 2 ν
  let J : I ⊕ Fin 2 := .inl j
  let d : Seq ({J} : Multiset (I ⊕ Fin 2)) := default
  have hψ : appendR S A J (ψ a : KLRAlgebra k S A) = ψ a * oneConcat S A {J} := by
    have hw : ValidWord A.card [a] := validWord_cons.2 ⟨ha, validWord_nil _⟩
    simpa only [ψw_cons, ψw_nil, mul_one] using (appendR_ψw (Q := S) (i := J) hw)
  have hd : (e d : KLRAlgebra k S {J}) = 1 := by
    rw [← sum_e (Q := S) (ν := ({J} : Multiset (I ⊕ Fin 2))), Fintype.sum_unique]
  have he : appendR S A J (e t) = e (t.append d) := by
    rw [appendR_apply, ← hd, concat_e_tmul_e]
  have hh : (oneConcat S A {J} * e (t.append d) : KLRAlgebra k S (A + {J})) =
      e (t.append d) := by
    rw [oneConcat, eSum_mul_e, ite_eq_left (append_mem_concatSet t d)]
  have hr : appendR S A J (ψ a * e t) = ψ a * e (t.append d) := by
    rw [map_mul, hψ, he, mul_assoc, hh]
  have hs : castKLR S (stendhalWeight_addBlack j ν) (ψ a * e (t.append d)) =
      ψ a * e (appendBlackLoading j ν t) := by
    rw [map_mul, castKLR_ψ, castKLR_e]
    rfl
  rw [hr]
  exact hs

end Suffix

end Categorification.Stendhal
