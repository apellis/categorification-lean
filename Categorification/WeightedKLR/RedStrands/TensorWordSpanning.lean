/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorWordBlackLower
import Categorification.WeightedKLR.RedStrands.TensorFinite

/-!
# Common divided-word generators of the two integral modules

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.37. A red-ordered
loading is determined by its unlabelled red positions and the ordered list
of its red labels. The projected affine generators thus admit exactly the
same divided-word indices as the tensor vectors.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR KLRAlgebra
variable {I J : Type*} {ℓ : ℕ}

private def blank (a : I ⊕ J) : I ⊕ Unit := Sum.map id (fun _ => ()) a
private def blackBlock (a : (I ⊕ J) × ℕ) : Option (I × ℕ) :=
  a.1.getLeft?.map (fun i => (i,a.2))

private theorem lists_eq {s t : List (I ⊕ J)} (hb : s.map blank = t.map blank)
    (hr : s.filterMap Sum.getRight? = t.filterMap Sum.getRight?) : s = t := by
  induction s generalizing t with
  | nil => simpa using hb.symm
  | cons a s ih =>
    cases t with
    | nil => simp at hb
    | cons b t =>
      obtain ⟨hhead,htail⟩ := List.cons.inj hb
      cases a with
      | inl i =>
        cases b with
        | inr => cases hhead
        | inl j =>
          have hij : i = j := Sum.inl.inj hhead
          exact congrArg₂ List.cons (congrArg Sum.inl hij) (ih htail (by simpa [List.filterMap, Sum.getRight?] using hr))
      | inr r =>
        cases b with
        | inl => cases hhead
        | inr t' =>
          change r :: _ = t' :: _ at hr
          exact congrArg₂ List.cons (congrArg Sum.inr (List.cons.inj hr).1) (ih htail (List.cons.inj hr).2)

private theorem reds_multiset {ν : Multiset I} {s : List (I ⊕ Fin ℓ)}
    (hw : (s : Multiset _) = stendhalWeight ℓ ν) :
    (s.filterMap Sum.getRight? : Multiset (Fin ℓ)) = Finset.univ.val := by
  rw [← Multiset.filterMap_coe, hw, stendhalWeight, Multiset.filterMap_add, Multiset.filterMap_map,
    Multiset.filterMap_map]
  simp [Function.comp_def]
  clear hw
  induction ν using Multiset.induction_on with
  | empty => rfl
  | cons i s ih => exact (Multiset.filterMap_cons_none i s rfl).trans ih

private theorem reds_length {ν : Multiset I} {s : List (I ⊕ Fin ℓ)}
    (hw : (s : Multiset _) = stendhalWeight ℓ ν) :
    (s.filterMap Sum.getRight?).length = ℓ := by
  simpa using congrArg Multiset.card (reds_multiset hw)

private theorem reds_order {ν : Multiset I} {s : List (I ⊕ Fin ℓ)}
    (hw : (s : Multiset _) = stendhalWeight ℓ ν) (ho : IsRedOrdered (Seq.ofList _ hw)) :
    (s.filterMap Sum.getRight?).Pairwise (· < ·) := by
  rw [List.pairwise_filterMap, List.pairwise_iff_getElem]
  intro a b ha hb hab r ha' t hb'
  have hn := congrArg Multiset.card hw
  simp only [Multiset.coe_card] at hn
  apply ho ⟨a,hn ▸ ha⟩ ⟨b,hn ▸ hb⟩ r t hab
  · rw [Seq.ofList_lbl]
    cases he : s[a] <;> simp_all
  · rw [Seq.ofList_lbl]
    cases he : s[b] <;> simp_all

private theorem length_filter_blank (s : List (I ⊕ J)) :
    ((s.map blank).filterMap Sum.getRight?).length = (s.filterMap Sum.getRight?).length := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    cases a with
    | inl => exact ih
    | inr => exact congrArg (· + 1) ih

private theorem red_one {ν : Multiset I} (d : List ((I ⊕ Fin ℓ) × ℕ))
    (hw : (expandDiv d : Multiset _) = stendhalWeight ℓ ν) :
    ∀ r a, (Sum.inr r,a) ∈ d → a ≤ 1 := by
  classical
  intro r a ha
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem ha
  have hc := congrArg (Multiset.count (Sum.inr r)) hw
  simp only [expandDiv_append, show expandDiv ((Sum.inr r,a) :: post) =
    List.replicate a (.inr r) ++ expandDiv post from rfl, ← Multiset.coe_add, Multiset.coe_replicate,
    Multiset.count_add, Multiset.count_replicate_self, stendhalWeight] at hc
  have hr : Multiset.count (.inr r) (ν.map (Sum.inl : I → I ⊕ Fin ℓ)) = 0 := by simp
  have hs : Multiset.count (Sum.inr r : I ⊕ Fin ℓ) (Finset.univ.val.map Sum.inr) = 1 := by
    rw [Multiset.count_map_eq_count' _ _ Sum.inr_injective]
    exact Multiset.count_univ _
  rw [hr, hs] at hc
  omega

private theorem exists_blank (d : List ((I ⊕ J) × ℕ))
    (hred : ∀ r a, (Sum.inr r,a) ∈ d → a ≤ 1) :
    ∃ (n : ℕ) (w : TensorWord I n), (expandDiv w.blocks).map blank = (expandDiv d).map blank ∧
      w.blackBlocks = d.filterMap blackBlock := by
  induction d using List.reverseRecOn with
  | nil => exact ⟨_, .empty, rfl, rfl⟩
  | append_singleton d q ih =>
    have hp : ∀ r a, (Sum.inr r,a) ∈ d → a ≤ 1 := fun r a ha => hred _ _ (List.mem_append_left _ ha)
    obtain ⟨n,w,he,hb⟩ := ih hp
    rcases q with ⟨i|r,a⟩
    · refine ⟨n,w.black i a, ?_, ?_⟩
      · simp [TensorWord.blocks, expandDiv, List.map_append, he, blank] at he ⊢
      · simp [TensorWord.blackBlocks, hb, blackBlock]
    · have ha := hred r a (by simp)
      interval_cases a
      · refine ⟨n,w, ?_, ?_⟩
        · simpa [expandDiv_append, expandDiv] using he
        · simp [hb, blackBlock]
      · refine ⟨n+1,w.red, ?_, ?_⟩
        · have hmap : ∀ (ds : List ((I ⊕ Fin n) × ℕ)),
              (expandDiv (ds.map (Prod.map (addRedColor n) id))).map blank = (expandDiv ds).map blank := by
            intro ds
            induction ds with
            | nil => rfl
            | cons q ds ih =>
              obtain ⟨c,a⟩ := q
              cases c <;> simp [expandDiv, List.map_append, blank] at ih ⊢ <;> exact ih
          rw [TensorWord.blocks, expandDiv_append, expandDiv_append, List.map_append, List.map_append, hmap]
          exact congrArg (fun l : List (I ⊕ Unit) => l ++ [.inr ()]) he
        · simp [TensorWord.blackBlocks, hb, blackBlock]

/-- A red-ordered divided loading has a tensor word with precisely the same
expanded sequence and black blocks. Zero-sized red blocks disappear. -/
theorem exists_tensorWord_of_ordered {ν : Multiset I} (d : List ((I ⊕ Fin ℓ) × ℕ))
    (hw : (expandDiv d : Multiset _) = stendhalWeight ℓ ν) (ho : IsRedOrdered (Seq.ofList _ hw)) :
    ∃ w : TensorWord I ℓ, expandDiv w.blocks = expandDiv d ∧
      w.blackBlocks = d.filterMap (fun q => q.1.getLeft?.map (fun i => (i,q.2))) := by
  obtain ⟨n,w,he,hb⟩ := exists_blank d (red_one d hw)
  have hn : n = ℓ := by
    rw [← reds_length w.blocks_weight, ← reds_length hw, ← length_filter_blank (expandDiv w.blocks),
      he, length_filter_blank]
  subst n
  refine ⟨w, lists_eq he ?_, hb⟩
  exact List.Perm.eq_of_pairwise' (reds_order w.blocks_weight w.blocks_redOrdered)
    (reds_order hw ho) (Multiset.coe_eq_coe.mp ((reds_multiset w.blocks_weight).trans (reds_multiset hw).symm))


open QuantumGroup Categorification.Graded KL2 StendhalAlgebraAllOrders
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I) (hQ : IsRouquierQ C Q) (ν : Multiset I)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "𝓣" => tensorProductGrade G ν

omit [DecidableEq I] in
private theorem factorial_black (d : List ((I ⊕ Fin ℓ) × ℕ))
    (hred : ∀ r a, (Sum.inr r,a) ∈ d → a ≤ 1) :
    divQFact2 (affineCoverCartan C ℓ) d = divQFact2 C (d.filterMap blackBlock) := by
  induction d with
  | nil => rfl
  | cons q d ih =>
    have ht := ih (fun r a ha => hred r a (List.mem_cons_of_mem _ ha))
    rcases q with ⟨i|r,a⟩
    · change _ * divQFact2 (affineCoverCartan C ℓ) d = _ * divQFact2 C (d.filterMap blackBlock)
      rw [ht]
      rfl
    · have ha := hred r a List.mem_cons_self
      interval_cases a <;> simpa [divQFact2, blackBlock, List.filterMap] using ht

private theorem unordered_vanishes (d : List ((I ⊕ Fin ℓ) × ℕ))
    (hw : (expandDiv d : Multiset _) = stendhalWeight ℓ ν) (ho : ¬ IsRedOrdered (Seq.ofList _ hw)) :
    K0.of (dividedSequenceProj Λ C hQ ν d hw) = 0 := by
  let t := Seq.ofList _ hw
  let π := affineTensorProjection (Q := Q) Λ ν
  have he : π (KLRAlgebra.e t) = 0 := by
    change TensorProductAlgebra.mk Q Λ ν (orderProjection Q Λ ν (affineCover Q Λ ν (KLRAlgebra.e t))) = 0
    rw [affineCover_e, ← map_zero (TensorProductAlgebra.mk Q Λ ν)]
    apply congrArg
    apply Subtype.ext
    change StendhalAlgebraAllOrders.e t * redOrderedIdem k Q Λ ν = 0
    simp [e_mul_redOrderedIdem, t, ho]
  have hp : π (hflip (divIdem t (blocksDiv d 0))) = 0 := by
    rw [divIdem, hflip_mul, hflip_e, map_mul, he, zero_mul]
  unfold dividedSequenceProj
  rw [← K0.T_smul_of]
  have hc := K0.of_ofIdempotent_zero (𝒜 := 𝓣) IsIdempotentElem.zero (Submodule.zero_mem _)
  refine Eq.trans (congrArg (_ • ·) ((K0.of_ofIdempotent_congr (𝒜 := 𝓣) hp _ _ _ _).trans hc)) (smul_zero _)

omit [DecidableEq I] in
private theorem weight_inj {α β : Multiset I} (h : stendhalWeight ℓ α = stendhalWeight ℓ β) : α = β :=
  Multiset.map_injective Sum.inl_injective (add_right_cancel h)

private theorem sequence_class_congr (s t : KLR.Seq (stendhalWeight ℓ ν))
    (hs : IsRedOrdered s) (ht : IsRedOrdered t) (he : s = t) :
    K0.of (sequenceProj G s hs) = K0.of (sequenceProj G t ht) := by cases he; rfl

set_option maxHeartbeats 500000 in
/-- Webster, §4.7, Lemma 4.37. At each black content the integral
Stendhal projective group is generated by the shifted projectives with
exactly the same ordered divided-word indices as the tensor generators. -/
theorem span_tensorWordProjective :
    Submodule.span (LaurentPolynomial ℤ) {z : K0 𝓣 | ∃ (w : TensorWord I ℓ)
      (h : w.content.toMultiset = ν), z = h ▸ K0.of (tensorWordProjective Λ C hQ w)} = ⊤ := by
  classical
  apply top_unique
  rw [← span_dividedSequenceProj Λ C hQ ν]
  apply Submodule.span_le.mpr
  rintro _ ⟨d,hw,rfl⟩
  by_cases ho : IsRedOrdered (Seq.ofList _ hw)
  · obtain ⟨w,he,hb⟩ := exists_tensorWord_of_ordered d hw ho
    have hx : stendhalWeight ℓ w.content.toMultiset = stendhalWeight ℓ ν := by
      rw [← w.blocks_weight, he, hw]
    have hν := weight_inj hx
    subst ν
    apply Submodule.subset_span
    refine ⟨w,rfl,?_⟩
    let := tensorProductAlgebra_finite Λ w.content.toMultiset hQ
    let := HasGdim.of_finiteDimensional (tensorProductGrade G w.content.toMultiset)
    have hn : divQFact2 (affineCoverCartan C ℓ) d ≠ 0 := fun h =>
      KL2Gamma.qToV_divQFact2_ne_zero _ _ (by rw [h,map_zero])
    apply (isRegular_iff_ne_zero.mpr hn).smul_right_injective (K0 (tensorProductGrade G w.content.toMultiset))
    change divQFact2 (affineCoverCartan C ℓ) d • K0.of (dividedSequenceProj Λ C hQ _ d hw) =
      divQFact2 (affineCoverCartan C ℓ) d • K0.of (tensorWordProjective Λ C hQ w)
    refine (sequenceProj_eq_factorial Λ C hQ _ d hw ho).symm.trans ?_
    have hfac : divQFact2 (affineCoverCartan C ℓ) d = divQFact2 C w.blackBlocks :=
      (factorial_black C d (red_one _ hw)).trans (congrArg (divQFact2 C) hb.symm)
    rw [hfac, ← tensorWordProjective_factorial Λ C hQ w]
    have hs := Seq.ofList_congr he w.blocks_weight hw
    exact sequence_class_congr Λ C hQ _ _ _ ho w.blocks_redOrdered hs.symm
  · rw [unordered_vanishes Λ C hQ ν d hw ho]
    exact zero_mem _

/-- The same divided words generate the direct sum of all black-content
Grothendieck groups over the integral Laurent polynomial ring. -/
theorem span_tensorWordProjectiveClass :
    Submodule.span (LaurentPolynomial ℤ) (Set.range (tensorWordProjectiveClass Λ C hQ)) = ⊤ := by
  set V := Submodule.span (LaurentPolynomial ℤ) (Set.range (tensorWordProjectiveClass Λ C hQ))
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using DirectSum.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | of β y =>
    let l := DirectSum.lof (LaurentPolynomial ℤ) _ (fun γ => K0 (tensorProductGrade G γ)) β
    have H : ⊤ ≤ V.comap l := by
      rw [← span_tensorWordProjective Λ C hQ β]
      apply Submodule.span_le.mpr
      rintro _ ⟨w,rfl,rfl⟩
      exact Submodule.subset_span (Set.mem_range_self w)
    exact H (Submodule.mem_top (x := y))

end Categorification.Stendhal.FirstWeight
