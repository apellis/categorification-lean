/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicWordRestriction
import Categorification.Algebra.Graded.KrullSchmidtUnique
import Categorification.WeightedKLR.RedStrands.Stendhal
import Categorification.WeightedKLR.RedStrands.CyclotomicRestrictionIdeal

/-! # Projective summands of cyclotomic word restrictions

The signed deletion formula of Hu–Shi, arXiv:2108.05508v5, §3, Proposition
3.3, and graded Krull–Schmidt give a direct summand description preserving
the order of every strand other than the one removed.
-/

noncomputable section
namespace Categorification.KLR.CycKLR
open Categorification.Graded KLRAlgebra QuantumGroup QuantumGroup.UDot LieLean.QuantumGroup
local notation "LP" => LaurentPolynomial ℤ

section Sums

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
    [GradedAlgebra 𝒜] {ι : Type*} (P : ι → GProj 𝒜)

/-- A finite sum of grading shifts of specified projectives. -/
def shiftedWordSum : List (ι × ℤ) → GProj 𝒜
  | [] => GProj.zeroObj 𝒜
  | (i,n)::l => ((P i).shift n).prod (shiftedWordSum l)

private theorem class_append (l m : List (ι × ℤ)) :
    K0.of (shiftedWordSum P (l ++ m)) = K0.of (shiftedWordSum P l) + K0.of (shiftedWordSum P m) := by
  induction l with
  | nil => simp [shiftedWordSum,K0.of_eq_zero_of_subsingleton]
  | cons h t ih => rcases h with ⟨i,n⟩; simp [shiftedWordSum,K0.of_prod,ih,add_assoc]

private theorem class_shift (l : List (ι × ℤ)) (d : ℤ) :
    (LaurentPolynomial.T d : LP) • K0.of (shiftedWordSum P l) =
      K0.of (shiftedWordSum P (l.map fun t => (t.1,d+t.2))) := by
  induction l with
  | nil => simp [shiftedWordSum,K0.of_eq_zero_of_subsingleton]
  | cons h t ih =>
    rcases h with ⟨i,n⟩
    simp only [List.map_cons,shiftedWordSum,K0.of_prod,smul_add,ih,← K0.T_smul_of,
      ← mul_smul,← LaurentPolynomial.T_add]

private def wordDifferences : AddSubgroup (K0 𝒜) where
  carrier := {x | ∃ l m : List (ι × ℤ), x = K0.of (shiftedWordSum P l) - K0.of (shiftedWordSum P m)}
  zero_mem' := ⟨[],[],by simp⟩
  add_mem' := by
    rintro _ _ ⟨l,m,rfl⟩ ⟨l',m',rfl⟩
    exact ⟨l++l',m++m',by rw [class_append,class_append]; abel⟩
  neg_mem' := by rintro _ ⟨l,m,rfl⟩; exact ⟨m,l,by abel⟩

private def wordSpan : Submodule LP (K0 𝒜) where
  __ := (wordDifferences P).toAddSubmonoid
  smul_mem' := by
    intro c x hx
    change c • x ∈ wordDifferences P
    induction c using LaurentPolynomial.induction_on' with
    | add p q hp hq => rw [add_smul]; exact (wordDifferences P).add_mem hp hq
    | C_mul_T a n =>
      rw [mul_smul,LaurentPolynomial.C_eq_algebraMap,algebraMap_smul]
      apply (wordDifferences P).zsmul_mem
      obtain ⟨l,m,rfl⟩ := hx
      exact ⟨_,_,by rw [smul_sub,class_shift,class_shift]⟩

private theorem mem_wordSpan (i : ι) : K0.of (P i) ∈ wordSpan P := by
  refine ⟨[(i,0)],[],?_⟩
  simp only [shiftedWordSum,K0.of_prod,← K0.T_smul_of,LaurentPolynomial.T_zero,one_smul,
    add_sub_cancel_right]

end Sums

variable {I k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    {C : CartanDatum I} (hP : IsRouquierQ C Q) (Λ : I → ℕ)

local notation "G" => hP.gradingDatum
local notation "π" => mk k Q (fun j => (Polynomial.X : Polynomial k)^Λ j)
local notation "ι" => DirectSum.lof LP _ (fun ν => K0 (grade G Λ ν))

/-- The principal projective of a cyclotomic word. -/
abbrev sequenceProjective {β : Multiset I} (s : Seq β) : GProj (grade G Λ β) :=
  GProj.ofIdempotent _ ((show IsIdempotentElem (e (Q := Q) s) from e_mul_self s).map (π β))
    (Graded.mem_map_of_mem _ (π β).toLinearMap ((G).e_mem_grade s))

private theorem sequence_lof {β : Multiset I} (w : List I) (hw : (w : Multiset I) = β) :
    sequenceClass hP Λ w = ι β (K0.of (sequenceProjective hP Λ (Seq.ofList w hw))) := by
  subst β
  rw [sequenceClass]
  exact (totalQuotientK0_lof ..).trans (congrArg _ (quotientK0_ofIdempotent G Λ _ _ _))

/-- A factorization of the word at a specific removable occurrence of a colour. -/
abbrev WordDeletion (i : I) (w : List I) := {t : List I × List I // w = t.1 ++ i :: t.2}

omit [DecidableEq I] in
private theorem marked_eq {w : List I} {t : List I × I × List I} (ht : t ∈ markedWords w) :
    w = t.1 ++ t.2.1 :: t.2.2 := by
  induction w generalizing t with
  | nil => simp [markedWords] at ht
  | cons a w ih =>
    simp only [markedWords,List.mem_cons,List.mem_map] at ht
    rcases ht with rfl | ⟨s,hs,rfl⟩
    · rfl
    · simp [ih hs]

omit [DecidableEq I] in
private theorem deletion_content {β : Multiset I} {i : I} {w : List I}
    (hw : (w : Multiset I) = {i} + β) (t : WordDeletion i w) :
    ((t.1.1 ++ t.1.2 : List I) : Multiset I) = β := by
  rcases t with ⟨⟨u,v⟩,rfl⟩
  apply add_left_cancel (a := ({i} : Multiset I))
  rw [← hw]
  simp only [← Multiset.coe_add,← Multiset.cons_coe,← Multiset.singleton_add]
  ac_rfl

/-- The sequence projective of the remaining word after deletion. -/
abbrev deletionProjective {β : Multiset I} {i : I} {w : List I}
    (hw : (w : Multiset I) = {i} + β) (t : WordDeletion i w) :=
  sequenceProjective hP Λ (Seq.ofList (t.1.1 ++ t.1.2) (deletion_content hw t))

local notation "raising" => fun i => raise G Λ i hP.klrSymm hP.polyInY_leading C

/-- In the ordinary cyclotomic KLR category, restricting a sequence projective
in colour `i` gives a direct summand of a finite sum of shifted deletion
projectives. This follows from the signed integral word formula in Hu–Shi,
arXiv:2108.05508v5, §3, Proposition 3.3, via graded Krull–Schmidt. -/
theorem restriction_sequence_summand {β : Multiset I} (i : I) (w : List I)
    (hw : (w : Multiset I) = {i} + β) :
    ∃ l m : List (WordDeletion i w × ℤ), Nonempty
      (((gradedResProj G Λ i β hP.klrSymm hP.polyInY_leading
        (sequenceProjective hP Λ (Seq.ofList w hw))).prod
          (shiftedWordSum (deletionProjective hP Λ hw) m)).Iso
        (shiftedWordSum (deletionProjective hP Λ hw) l)) := by
  classical
  let D := deletionProjective hP Λ hw
  let V := wordSpan D
  let component := DirectSum.component LP _ (fun ν => K0 (grade G Λ ν)) β
  let RD : WeightDatum C (I → ℤ) ((I → ℤ) →+ ℤ) :=
    { pair := AddMonoidHom.id _
      iX := fun j i => A C i j
      iY := fun i => { toFun := fun x => x i, map_zero' := rfl, map_add' := fun _ _ => rfl }
      pair_iY_iX := fun _ _ => rfl }
  have hr : component (raising i (sequenceClass hP Λ w)) ∈ V := by
    rw [raise_sequenceClass hP Λ RD (fun j => (Λ j : ℤ)) (fun _ => rfl),map_list_sum]
    apply V.list_sum_mem
    intro x hx
    obtain ⟨_,hy,rfl⟩ := List.mem_map.mp hx
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hy
    split_ifs with he
    · let del : WordDeletion i w := ⟨(t.1,t.2.2),he ▸ marked_eq ht⟩
      rw [map_smul]
      apply V.smul_mem
      rw [sequence_lof hP Λ _ (deletion_content hw del)]
      change DirectSum.component LP _ _ β (ι β _) ∈ V
      rw [DirectSum.component.lof_self]
      exact mem_wordSpan D del
    · rw [map_zero]; exact V.zero_mem
  let s := raiseShift Λ i β C
  let E := gradedResProj G Λ i β hP.klrSymm hP.polyInY_leading (sequenceProjective hP Λ (Seq.ofList w hw))
  rw [sequence_lof hP Λ w hw,raise_lof] at hr
  change DirectSum.component LP _ _ β (ι β _) ∈ V at hr
  rw [DirectSum.component.lof_self,raiseK0,LinearMap.smul_apply,resK0_of] at hr
  change (LaurentPolynomial.T s : LP) • K0.of E ∈ V at hr
  have h := V.smul_mem (LaurentPolynomial.T (-s) : LP) hr
  rw [← mul_smul,← LaurentPolynomial.T_add,neg_add_cancel,LaurentPolynomial.T_zero,one_smul] at h
  obtain ⟨l,m,hm⟩ := h
  refine ⟨l,m,?_⟩
  let := module_finite (Q := Q) (ν := β)
    (fun a b hab => by obtain ⟨c,hc,he⟩ := hP.polyInY_leading a b hab; rw [he]; exact hc.map Polynomial.C)
    (fun a => Polynomial.monic_X_pow (R := k) (Λ a))
  let := HasGdim.of_finiteDimensional (grade G Λ β)
  apply K0.of_eq_of_iff.mp
  exact (K0.of_prod E _).trans (eq_sub_iff_add_eq.mp hm)

end Categorification.KLR.CycKLR

namespace Categorification.Stendhal

open KLR KLRAlgebra CycKLR Categorification.Graded QuantumGroup QuantumGroup.UDot

private def redBefore {I : Type*} {ℓ : ℕ} (x y : I ⊕ Fin ℓ) : Prop :=
  ∀ r s : Fin ℓ, x = .inr r → y = .inr s → r < s

private theorem ordered_iff_pairwise {I : Type*} [DecidableEq I] {ℓ : ℕ}
    {μ : Multiset (I ⊕ Fin ℓ)} (w : List (I ⊕ Fin ℓ)) (hw : (w : Multiset _) = μ) :
    IsRedOrdered (Seq.ofList w hw) ↔ w.Pairwise redBefore := by
  rw [List.pairwise_iff_getElem]
  have hn : w.length = μ.card := by rw [←hw]; rfl
  constructor
  · intro h a b ha hb hab r s hr hs
    exact h ⟨a,hn ▸ ha⟩ ⟨b,hn ▸ hb⟩ r s hab hr hs
  · intro h a b r s hab hr hs
    exact h a.val b.val (by rw [hn]; exact a.isLt) (by rw [hn]; exact b.isLt) hab r s hr hs

/-- Removing a black letter leaves precisely the same order on red labels
(Webster, arXiv:1309.3796v2, Definition 4.5). -/
theorem isRedOrdered_delete_black {I : Type*} [DecidableEq I] {ℓ : ℕ} {μ ν : Multiset (I ⊕ Fin ℓ)}
    {w : List (I ⊕ Fin ℓ)} {i : I} (t : WordDeletion (.inl i) w)
    (hw : (w : Multiset _) = μ) (ht : ((t.1.1 ++ t.1.2 : List _) : Multiset _) = ν) :
    IsRedOrdered (Seq.ofList (t.1.1 ++ t.1.2) ht) ↔ IsRedOrdered (Seq.ofList w hw) := by
  rw [ordered_iff_pairwise,ordered_iff_pairwise]
  rcases t with ⟨⟨u,v⟩,rfl⟩
  simp [List.pairwise_append,List.pairwise_cons,redBefore]

section IdealAction
variable {R : Type*} [Ring R] (J : TwoSidedIdeal R)

private theorem leftIdeal_mem_span {e : R} (he : IsIdempotentElem e) (hj : e ∈ J)
    (x : leftIdeal e) : x ∈ idealActionSpan (P := leftIdeal e) J := by
  have hx : (x : R) * e = x := x.2
  have hxj : (x : R) ∈ J := hx ▸ J.mul_mem_left _ _ hj
  exact Submodule.subset_span ⟨x.val,hxj,⟨e,he.eq⟩,Subtype.ext hx.symm⟩

private theorem shiftedSum_mem_span {k : Type*} [Field k] [Algebra k R] {𝒜 : ℤ → Submodule k R}
    [GradedAlgebra 𝒜] {ι : Type*} (D : ι → GProj 𝒜)
    (hD : ∀ t (x : (D t).carrier), x ∈ idealActionSpan (P := (D t).carrier) J)
    (l : List (ι × ℤ)) (x : (shiftedWordSum D l).carrier) :
    x ∈ idealActionSpan (P := (shiftedWordSum D l).carrier) J := by
  induction l with
  | nil =>
    have hx : x = 0 := (inferInstance : Subsingleton (GProj.zeroObj 𝒜).carrier).elim _ _
    rw [hx]; exact Submodule.zero_mem _
  | cons t l ih =>
    rcases t with ⟨t,d⟩
    obtain ⟨x,y⟩ := x
    let L := (D t).carrier
    let M := (shiftedWordSum D l).carrier
    have h₁ := mapsTo_idealActionSpan J (LinearMap.inl R L M) (hD t x)
    have h₂ := mapsTo_idealActionSpan J (LinearMap.inr R L M) (ih y)
    exact (show (x,y) = (x,0) + (0,y) by simp).symm ▸ (idealActionSpan (P := L × M) J).add_mem h₁ h₂

end IdealAction

variable {I k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
    {Q : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k} {C : CartanDatum (I ⊕ Fin ℓ)}
    (hP : IsRouquierQ C Q) (Λ : I ⊕ Fin ℓ → ℕ)
local notation "G" => hP.gradingDatum
local notation "p" => fun j => (Polynomial.X : Polynomial k)^Λ j

/-- A restricted word is generated by the ideal of its black deletions. -/
theorem restricted_word_mem_span_of_deletions {β : Multiset (I ⊕ Fin ℓ)} (i : I) (w : List (I ⊕ Fin ℓ))
    (hw : (w : Multiset _) = {Sum.inl i} + β)
    (J : TwoSidedIdeal (CycKLR k Q p β)) (hJ : ∀ t : WordDeletion (.inl i) w,
      CycKLR.mk k Q p β (e (Seq.ofList (t.1.1 ++ t.1.2) (deletion_content hw t))) ∈ J)
    (x : (gradedResProj G Λ (.inl i) β hP.klrSymm hP.polyInY_leading
      (sequenceProjective hP Λ (Seq.ofList w hw))).carrier) :
    x ∈ idealActionSpan J := by
  obtain ⟨l,m,⟨iso⟩⟩ := restriction_sequence_summand hP Λ (.inl i) w hw
  let D := deletionProjective hP Λ hw
  have hD (t : WordDeletion (.inl i) w) (y : (D t).carrier) : y ∈ idealActionSpan (P := (D t).carrier) J := by
    apply leftIdeal_mem_span J
    · exact (show IsIdempotentElem (e (Q := Q) _) from e_mul_self _).map _
    · exact hJ t
  have h := shiftedSum_mem_span J D hD l (iso (x,0))
  let f := (LinearMap.fst (CycKLR k Q p β) _ _).comp iso.symm.toLinearEquiv.toLinearMap
  exact (show f (iso (x,0)) = x from congrArg Prod.fst (iso.toLinearEquiv.symm_apply_apply (x,0))) ▸ mapsTo_idealActionSpan J f h

/-- Restricting an unordered sequence at a black colour lies in the action
of any lower ideal containing the unordered sequence idempotents (Webster,
arXiv:1309.3796v2, Definitions 4.5–4.7 and Lemma 4.35). -/
theorem restricted_unordered_mem_span {β : Multiset (I ⊕ Fin ℓ)} (i : I)
    (s : Seq ({Sum.inl i} + β)) (hu : ¬ IsRedOrdered s)
    (J : TwoSidedIdeal (CycKLR k Q p β)) (hJ : ∀ t : Seq β, ¬ IsRedOrdered t → CycKLR.mk k Q p β (e t) ∈ J)
    (x : (gradedResProj G Λ (.inl i) β hP.klrSymm hP.polyInY_leading (sequenceProjective hP Λ s)).carrier) :
    x ∈ idealActionSpan J := by
  let w := List.ofFn s.1
  have h := restricted_word_mem_span_of_deletions hP Λ i w (Seq.coe_ofFn s) J
  have hs : Seq.ofList w (Seq.coe_ofFn s) = s := Seq.ofList_ofFn s _
  have hdel (t : WordDeletion (.inl i) w) :
      CycKLR.mk k Q p β (e (Seq.ofList (t.1.1 ++ t.1.2) (deletion_content (Seq.coe_ofFn s) t))) ∈ J :=
    hJ _ fun ho => hu (hs ▸ (isRedOrdered_delete_black t (Seq.coe_ofFn s) _).mp ho)
  have hx := h hdel
  rw [hs] at hx
  exact hx x

include hP in
/-- Every left multiple of an unordered upper idempotent, cut at a terminal
black strand, belongs to the span of the lower unordered ideal
(Webster, arXiv:1309.3796v2, Definitions 4.5–4.7 and Lemma 4.35). -/
theorem cut_mul_unordered_mem_span (a : I ⊕ Fin ℓ → Polynomial k) (ha : a = p)
    {β : Multiset (I ⊕ Fin ℓ)} (i : I)
    (s : Seq ({Sum.inl i} + β)) (hu : ¬ IsRedOrdered s)
    (J : TwoSidedIdeal (CycKLR k Q a β)) (hJ : ∀ t : Seq β, ¬ IsRedOrdered t → CycKLR.mk k Q a β (e t) ∈ J)
    (b : CycKLR k Q a ({Sum.inl i} + β))
    (z : AbsentColour.Res Q (.inl i) a β (CycKLR k Q a ({Sum.inl i} + β)))
    (hz : z.val = AbsentColour.lastIdem Q (.inl i) a β * (b * CycKLR.mk k Q a _ (e s))) :
    z ∈ idealActionSpan J := by
  subst a
  let eₛ := CycKLR.mk k Q p _ (e s)
  have he : IsIdempotentElem eₛ := (show IsIdempotentElem (e (Q := Q) s) from e_mul_self s).map _
  have hR : z.val * eₛ = z.val := by rw [hz,mul_assoc,mul_assoc,he.eq]
  let z' : (gradedResProj G Λ (.inl i) β hP.klrSymm hP.polyInY_leading (sequenceProjective hP Λ s)).carrier :=
    ⟨⟨z.val,hR⟩,Subtype.ext z.2⟩
  let f := AbsentColour.resMap Q (.inl i) p β (leftIdeal eₛ) (leftIdeal eₛ).subtype
  exact mapsTo_idealActionSpan J f (restricted_unordered_mem_span hP Λ i s hu J hJ z')

end Categorification.Stendhal
