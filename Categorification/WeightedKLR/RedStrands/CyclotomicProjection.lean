/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleRed
import Categorification.KLR.Reindex
import Categorification.KLR.ConcatAssoc
import Categorification.KLR.CyclotomicSplit

/-!
# Inserting a single red strand on the left

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Theorem 4.20, p. 37. Inserting a red strand and imposing the violating ideal gives
a surjection from the cyclotomic quotient in every black weight.
-/

noncomputable section

namespace Categorification.Stendhal.SingleRed

open KLR KLRAlgebra TypeA StendhalAlgebraAllOrders
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] KLRAlgebra.instAlgebraConcatCorner

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 1 → I →₀ ℕ) (ν : Multiset I)

private abbrev red (I : Type*) : I ⊕ Fin 1 := .inr 0
local notation "R" => ({red I} : Multiset (I ⊕ Fin 1))
local notation "B" => ν.map (Sum.inl : I → I ⊕ Fin 1)
local notation "μ" => stendhalWeight 1 ν
local notation "S" => stendhalQ Q Λ
local notation "T" => TensorProductAlgebra k Q Λ ν

omit [DecidableEq I] in
private theorem splitWeight : R + B = μ := by simp [stendhalWeight, red, add_comm]

private def redSeq : Seq R := default

omit [DecidableEq I] in
private theorem redSeq_lbl (a : Fin (Multiset.card R)) : (redSeq (I := I)).1 a = red I :=
  Multiset.mem_singleton.mp (Seq.mem _ a)

private def raw : KLRAlgebra k S (R + B) →ₐ[k] T :=
  ((mk Q Λ ν).comp (ofKLR k Q Λ ν)).comp (castKLR S (splitWeight ν)).toAlgHom

private theorem raw_e (s : Seq (R + B)) :
    raw Q Λ ν (KLRAlgebra.e s) =
      mk Q Λ ν (StendhalAlgebraAllOrders.e (Seq.cast (splitWeight ν) s)) := by
  simp only [raw, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, castKLR_e, StendhalAlgebraAllOrders.e]

private theorem raw_x (a : Fin (Multiset.card (R + B))) :
    raw Q Λ ν (KLRAlgebra.x a) =
      mk Q Λ ν (StendhalAlgebraAllOrders.x (Fin.cast (congrArg Multiset.card (splitWeight ν)) a)) := by
  simp only [raw, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, castKLR_x, StendhalAlgebraAllOrders.x]

private theorem raw_ψ (j : ℕ) : raw Q Λ ν (KLRAlgebra.ψ j) =
    mk Q Λ ν (StendhalAlgebraAllOrders.ψ j) := by
  simp only [raw, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, castKLR_ψ, StendhalAlgebraAllOrders.ψ]

omit [DecidableEq I] in
private theorem red_head_split (s : Seq (R + B)) (hs : s.1 ⟨0, by simp⟩ = red I) :
    ∃ b : Seq B, (redSeq (I := I)).append b = s := by
  have hl (a : Fin (Multiset.card R)) : s.1 (Seq.posL B a) = red I := by
    convert hs using 2
    exact Fin.ext (by simpa using (show a.val = 0 by have := a.isLt; simp at this; omega))
  have hf : Finset.univ.val.map (s.1 ∘ Seq.posL B) = R := by
    rw [show s.1 ∘ Seq.posL B = fun _ => red I from funext hl, Multiset.map_const']
    simp
  have split (f : Fin (Multiset.card (R + B)) → I ⊕ Fin 1) : Finset.univ.val.map f =
      Finset.univ.val.map (f ∘ Seq.posL B) + Finset.univ.val.map (f ∘ Seq.posR R) := by
    conv_lhs => rw [← Multiset.map_univ_val_equiv (blockEquiv (Seq.card_add' R B))]
    rw [Multiset.map_map, ← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.disjSum,
      Multiset.map_add, Multiset.map_map, Multiset.map_map]
    rfl
  have hw := split s.1
  rw [s.2, hf] at hw
  refine ⟨⟨_, (add_left_cancel hw).symm⟩, Subtype.ext (funext fun a => ?_)⟩
  obtain ⟨a, rfl⟩ := (blockEquiv (Seq.card_add' R B)).surjective a
  cases a with
  | inl a => exact (Seq.append_posL _ _ a).trans ((redSeq_lbl a).trans (hl a).symm)
  | inr a => exact Seq.append_posR _ _ a

private theorem raw_e_zero (s : Seq (R + B)) (hs : s ∉ concatSet R B) :
    raw Q Λ ν (KLRAlgebra.e s) = 0 := by
  rw [raw_e]
  apply mk_e_of_violated
  have hμ : 0 < Multiset.card μ := by simp [stendhalWeight]
  refine ⟨hμ, ?_⟩
  change (s.1 ⟨0, _⟩).isLeft
  cases h : s.1 ⟨0, by simp⟩ with
  | inl c => rfl
  | inr r =>
    have hr : r = 0 := Subsingleton.elim _ _
    obtain ⟨b, hb⟩ := red_head_split ν s (by simpa [hr, red] using h)
    exact (hs (hb ▸ append_mem_concatSet _ b)).elim

private theorem raw_oneConcat : raw Q Λ ν (oneConcat S R B) = 1 := by
  classical
  rw [← map_one (raw Q Λ ν), ← KLRAlgebra.sum_e, oneConcat, eSum, map_sum, map_sum]
  apply Finset.sum_subset (Finset.subset_univ _)
  exact fun s _ hs => raw_e_zero Q Λ ν s hs

private def projectCorner : ConcatCorner S R B →ₐ[k] T where
  toFun z := raw Q Λ ν z.1
  map_mul' _ _ := map_mul _ _ _
  map_add' _ _ := map_add _ _ _
  map_one' := raw_oneConcat Q Λ ν
  map_zero' := map_zero _
  commutes' c := by
    change raw Q Λ ν (algebraMap k _ c * oneConcat S R B) = _
    rw [map_mul, AlgHom.commutes, raw_oneConcat, mul_one]

/-- Webster's map obtained by inserting a single red strand on the left and
then projecting to the violating quotient (Theorem 4.20). -/
def insertRed : KLRAlgebra k Q ν →ₐ[k] T :=
  (projectCorner Q Λ ν).comp (((blockR R B).hom S).comp
    (reindexEquiv Sum.inl_injective S ν).toAlgHom)


/-- The red-first word associated to a black word. -/
def insertWord (s : Seq ν) : Seq μ :=
  Seq.cast (splitWeight ν) (redSeq.append (Seq.map Sum.inl s))

/-- The position of a black strand after inserting the red strand. -/
def blackPos (a : Fin (Multiset.card ν)) : Fin (Multiset.card μ) :=
  ⟨a.val + 1, by simp [stendhalWeight]⟩

private theorem insertRed_apply (z : KLRAlgebra k Q ν) :
    insertRed Q Λ ν z = raw Q Λ ν (concat S R B
      (1 ⊗ₜ[k] (reindexEquiv Sum.inl_injective S ν z))) := by
  rw [concat_tmul, map_one, Corner.val_one, Corner.E_mul_val]
  rfl

theorem insertRed_e (s : Seq ν) : insertRed Q Λ ν (KLRAlgebra.e s) =
    mk Q Λ ν (StendhalAlgebraAllOrders.e (insertWord ν s)) := by
  have he : (reindexEquiv Sum.inl_injective S ν) (KLRAlgebra.e (Q := Q) s) =
      KLRAlgebra.e (Seq.map Sum.inl s) := reindexEquiv_e _ s
  rw [insertRed_apply, he,
    ← e_single (Q := S) (red I) redSeq, concat_e_tmul_e, raw_e]
  rfl

theorem insertRed_x (a : Fin (Multiset.card ν)) : insertRed Q Λ ν (KLRAlgebra.x a) =
    mk Q Λ ν (StendhalAlgebraAllOrders.x (blackPos ν a)) := by
  have hx : (reindexEquiv Sum.inl_injective S ν) (KLRAlgebra.x (Q := Q) a) =
      KLRAlgebra.x (Fin.cast (Multiset.card_map _ _).symm a) := reindexEquiv_x _ a
  rw [insertRed_apply, hx, concat_one_tmul_x, map_mul, raw_oneConcat, mul_one, raw_x]
  congr 2
  apply Fin.ext
  change Multiset.card R + a.val = a.val + 1
  simp [add_comm]

theorem insertRed_ψ (j : ℕ) (hj : j + 1 < Multiset.card ν) :
    insertRed Q Λ ν (KLRAlgebra.ψ j) = mk Q Λ ν (StendhalAlgebraAllOrders.ψ (j + 1)) := by
  have hp : (reindexEquiv Sum.inl_injective S ν) (KLRAlgebra.ψ (Q := Q) j) =
      KLRAlgebra.ψ j := reindexEquiv_ψ _ j
  rw [insertRed_apply, hp, concat_one_tmul_ψ (by simpa using hj), map_mul,
    raw_oneConcat, mul_one, raw_ψ]
  simp [add_comm]

omit [DecidableEq I] in
theorem insertWord_head (s : Seq ν) :
    (insertWord ν s).lbl ⟨0, by simp [stendhalWeight]⟩ = .inr 0 := by
  simp only [insertWord, Seq.lbl, Seq.cast_apply]
  rw [Seq.append_apply_lt _ _ _ (by change 0 < Multiset.card R; simp)]
  exact redSeq_lbl _

omit [DecidableEq I] in
theorem insertWord_black (s : Seq ν) (a : Fin (Multiset.card ν)) :
    (insertWord ν s).lbl (blackPos ν a) = .inl (s.lbl a) := by
  change (redSeq.append (Seq.map Sum.inl s)).1
    (Fin.cast _ (blackPos ν a)) = _
  rw [Seq.append_apply_ge _ _ _ (by change Multiset.card R ≤ a.val + 1; simp)]
  change Sum.inl (s.1 _) = Sum.inl (s.1 a)
  congr 2

/-- The red-left insertion descends to the undeformed cyclotomic quotient
(Webster, arXiv:1309.3796v2, Theorem 4.20, first kernel inclusion). -/
def cyclotomicProjection :
    CycKLR k Q (fun i => Polynomial.X ^ Λ 0 i) ν →ₐ[k] T :=
  CycKLR.lift (insertRed Q Λ ν) fun s => by
    by_cases h : 0 < Multiset.card ν
    · rw [cycElt_of_pos _ _ s h, map_mul, map_pow, Polynomial.aeval_X, map_pow,
        insertRed_x, insertRed_e]
      exact first_black_dot_pow Q Λ _ _ _ (insertWord_head ν s) (insertWord_black ν s ⟨0, h⟩)
    · simp [cycElt, h]


private theorem raw_surjective : Function.Surjective (raw Q Λ ν) :=
  (mk_surjective Q Λ ν).comp (ofKLR_surjective.comp (castKLR S (splitWeight ν)).surjective)

theorem insertRed_surjective : Function.Surjective (insertRed Q Λ ν) := by
  classical
  intro y
  obtain ⟨z, rfl⟩ := raw_surjective Q Λ ν y
  change raw Q Λ ν z ∈ (insertRed Q Λ ν).range
  induction z using klr_induction with
  | hadd u v hu hv => rw [map_add]; exact add_mem hu hv
  | hmul u v hu hv => rw [map_mul]; exact mul_mem hu hv
  | hr c => rw [AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ c
  | he s =>
    by_cases hs : s ∈ concatSet R B
    · obtain ⟨r, b, rfl⟩ := mem_concatSet.mp hs
      obtain rfl : r = redSeq := Subsingleton.elim _ _
      obtain ⟨s, rfl⟩ := (Seq.map_bijective Sum.inl_injective ν).surjective b
      exact ⟨KLRAlgebra.e s, (insertRed_e Q Λ ν s).trans (raw_e Q Λ ν _).symm⟩
    · rw [raw_e_zero Q Λ ν s hs]
      exact zero_mem _
  | hx a =>
    rw [raw_x]
    rcases ha : a.val with _ | n
    · rw [show Fin.cast (congrArg Multiset.card (splitWeight ν)) a = ⟨0, by simp [stendhalWeight]⟩
          from Fin.ext ha, mk_first_dot]
      exact zero_mem _
    · have hn : n < Multiset.card ν := by
        have hb := a.isLt
        simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_map] at hb
        omega
      exact ⟨KLRAlgebra.x ⟨n, hn⟩, (insertRed_x Q Λ ν _).trans
        (congrArg (fun b => mk Q Λ ν (StendhalAlgebraAllOrders.x b)) (Fin.ext ha.symm))⟩
  | hψ j =>
    cases j with
    | zero => rw [raw_ψ, mk_first_cross]; exact zero_mem _
    | succ n =>
      by_cases hn : n + 1 < Multiset.card ν
      · rw [raw_ψ]
        exact ⟨KLRAlgebra.ψ n, insertRed_ψ Q Λ ν n hn⟩
      · rw [KLRAlgebra.ψ_eq_zero _ (by simp; omega), map_zero]
        exact zero_mem _

/-- The cyclotomic algebra surjects onto the single-red algebra in every weight
(Webster, Theorem 4.20, surjectivity and the first kernel inclusion). -/
theorem cyclotomicProjection_surjective : Function.Surjective (cyclotomicProjection Q Λ ν) := by
  intro y
  obtain ⟨z, rfl⟩ := insertRed_surjective Q Λ ν y
  exact ⟨CycKLR.mk k Q _ ν z, CycKLR.lift_mk _ _ _⟩

end Categorification.Stendhal.SingleRed
