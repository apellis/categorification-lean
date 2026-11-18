/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.GradedIndShuffle

/-!
# Valid shuffle masks after the last red

For an ordered diagram in Webster, arXiv:1309.3796v2, §4.6–4.7, the final input
loading must begin with the final red colour. The preceding output letters therefore
come from the first input. The remaining mask is supported on the black suffix.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR KLRAlgebra TypeA QuantumGroup.PreF

variable {I J : Type*}

/-- Extract the subword of one factor from a sequence tagged by its shuffle mask. -/
def maskSubword (r : Bool) (t : List (I × Bool)) : List I :=
  t.filterMap fun p => if p.2 = r then some p.1 else none

/-- Tag each occurrence of a suffix, including repeated equal letters, by its own bit. -/
def tagMask (s : List I) (b : Fin s.length → Bool) : List (I × Bool) :=
  List.ofFn fun j => (s.get j, b j)

theorem tagMask_cons (i : I) (s : List I) (b : Bool) (bs : Fin s.length → Bool) :
    tagMask (i::s) (Fin.cons b bs) = (i,b) :: tagMask s bs := by
  rw [tagMask, List.ofFn_succ]
  rfl

private theorem tagMask_fst (s : List J) (b : Fin s.length → Bool) :
    (tagMask s b).map Prod.fst = s := by simp [tagMask, List.map_ofFn, Function.comp_def]

private theorem tagMask_injective (s : List J) :
    Function.Injective (tagMask s) := by
  intro b b' h
  have := congrArg (List.map Prod.snd) h
  simpa [tagMask, List.map_ofFn, Function.comp_def] using this

private theorem exists_tagMask (s : List J) (t : List (J × Bool)) (h : t.map Prod.fst = s) :
    ∃ b, tagMask s b = t := by
  induction s generalizing t with
  | nil =>
    cases t with
    | nil => exact ⟨fun _ => false, by simp [tagMask]⟩
    | cons z t => simp at h
  | cons j s ih =>
    cases t with
    | nil => simp at h
    | cons z t =>
      have ⟨hj,ht⟩ := List.cons.inj h
      obtain ⟨b,rfl⟩ := ih t ht
      exact ⟨Fin.cons z.2 b, by rw [tagMask_cons, ← hj]⟩

/-- Extend a suffix assignment to the complete loading, assigning every preceding letter
to the earlier factor and the last red to the final factor. -/
def lastRedMask (p : List J) (r : J) (s : List J) (b : Fin s.length → Bool) : List (J × Bool) :=
  p.map (fun j => (j,false)) ++ (r,true) :: tagMask s b

private theorem mem_maskSubword {j : J} {b : Bool} {t : List (J × Bool)} (h : j ∈ maskSubword b t) :
    j ∈ t.map Prod.fst := by
  obtain ⟨z,hz,he⟩ := List.mem_filterMap.1 h
  split_ifs at he with he'
  · exact List.mem_map.2 ⟨z,hz,Option.some.inj he⟩

private theorem head_lastRedMask (p : List J) (r : J) (s : List J) (b : Fin s.length → Bool) :
    (maskSubword true (lastRedMask p r s b)).head? = some r := by
  induction p with
  | nil => simp [lastRedMask, maskSubword]
  | cons j p ih => exact ih

private theorem fst_lastRedMask (p : List J) (r : J) (s : List J) (b : Fin s.length → Bool) :
    (lastRedMask p r s b).map Prod.fst = p ++ r :: s := by
  simp [lastRedMask, List.map_map, Function.comp_def, tagMask_fst]

/-- A tagged loading whose final-factor subword begins with the unique final red colour
comes from exactly one suffix mask. -/
theorem existsUnique_lastRedMask {p s : List J} {r : J} (hp : r ∉ p) (hs : r ∉ s)
    {t : List (J × Bool)} (ht : t.map Prod.fst = p ++ r :: s)
    (hr : (maskSubword true t).head? = some r) :
    ∃! b, lastRedMask p r s b = t := by
  suffices hh : ∃ b, lastRedMask p r s b = t by
    obtain ⟨b,rfl⟩ := hh
    refine ⟨b,rfl,fun c hc => tagMask_injective s ?_⟩
    simpa [lastRedMask] using hc
  induction p generalizing t with
  | nil =>
    cases t with
    | nil => simp at ht
    | cons z t =>
      obtain ⟨hj,ht'⟩ := List.cons.inj ht
      obtain ⟨b,rfl⟩ := exists_tagMask s t ht'
      rcases z with ⟨j,v⟩
      change j = r at hj
      subst j
      cases v with
      | true => exact ⟨b,rfl⟩
      | false =>
        have hh : r ∈ maskSubword true (tagMask s b) := List.mem_of_mem_head? hr
        exact (hs (tagMask_fst s b ▸ mem_maskSubword hh)).elim
  | cons j p ih =>
    cases t with
    | nil => simp at ht
    | cons z t =>
      obtain ⟨hj,ht'⟩ := List.cons.inj ht
      rcases z with ⟨j',v⟩
      change j' = j at hj
      subst j'
      have hp' : r ∉ p := fun h => hp (List.mem_cons_of_mem _ h)
      cases v with
      | true =>
        have h : j = r := Option.some.inj hr
        exact (hp (by simp [h])).elim
      | false =>
        obtain ⟨b,hb⟩ := ih hp' ht' hr
        exact ⟨b,congrArg ((j,false) :: ·) hb⟩

private theorem maskSubword_ofFn {n : ℕ} (w : Fin n → J) (b : Fin n → Bool) (c : Bool) :
    maskSubword c (List.ofFn fun j => (w j,b j)) = FreeMonoid.toList (maskWord w b c) := by
  rw [toList_maskWord, List.ofFn_eq_map]
  generalize List.finRange n = l
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : b a = c
    · simpa [maskSubword, h] using congrArg (w a :: ·) ih
    · simpa [maskSubword, h] using ih

private theorem exists_mask_of_fst {n : ℕ} (w : Fin n → J) (t : List (J × Bool))
    (h : t.map Prod.fst = List.ofFn w) : ∃ b : Fin n → Bool, (List.ofFn fun j => (w j,b j)) = t := by
  induction n generalizing t with
  | zero => obtain rfl := List.eq_nil_of_map_eq_nil h; exact ⟨fun _ => false, rfl⟩
  | succ n ih =>
    rw [List.ofFn_succ] at h
    cases t with
    | nil => simp at h
    | cons z t =>
      obtain ⟨h0,ht⟩ := List.cons.inj h
      obtain ⟨b, hb⟩ := ih _ t ht
      exact ⟨Fin.cons z.2 b, by rw [List.ofFn_succ]; exact congrArg₂ List.cons (by rw [← h0]; rfl) hb⟩

variable [DecidableEq J] {α β : Multiset J} (w : Seq (α + β))

/-- The colours and source-factor bits of a shuffle of the output loading. -/
def shuffleTags (u : ShuffleOf α β w) := List.ofFn fun j => (w.lbl j, u.mask j)

/-- The labelled subword from either factor of the permutation. -/
theorem maskSubword_shuffleTags (u : ShuffleOf α β w) (c : Bool) :
    maskSubword c (shuffleTags w u) = FreeMonoid.toList (maskWord w.1 u.mask c) :=
  maskSubword_ofFn _ _ _

private theorem shuffleTags_fst (u : ShuffleOf α β w) : (shuffleTags w u).map Prod.fst =
    List.ofFn w.1 := by simp [shuffleTags, List.map_ofFn, Function.comp_def, Seq.lbl]

private theorem shuffleTags_injective : Function.Injective (shuffleTags w) := by
  intro u u' h
  apply ShuffleOf.mask_injective w
  have he := congrArg (List.map Prod.snd) h
  simp only [shuffleTags, List.map_ofFn] at he
  exact List.ofFn_injective he

variable (p : List J) (r : J) (s : List J)

private theorem exists_suffixMask (hw : List.ofFn w.1 = p ++ r :: s) (hp : r ∉ p) (hs : r ∉ s)
    (u : {u : ShuffleOf α β w // (List.ofFn u.split.2.1).head? = some r}) :
      ∃! b, lastRedMask p r s b = shuffleTags w u.1 := by
    apply existsUnique_lastRedMask hp hs ((shuffleTags_fst w u.1).trans hw)
    rw [maskSubword_shuffleTags, ← u.1.ofFn_split_snd]
    exact u.2

/-- Surviving shuffles of fixed parabolic content, indexed by the bits on the post-red
suffix alone. The inverse reconstructs the minimal parabolic permutation. -/
def lastRedShuffleMaskEquiv (hw : List.ofFn w.1 = p ++ r :: s) (hp : r ∉ p) (hs : r ∉ s) :
    {u : ShuffleOf α β w // (List.ofFn u.split.2.1).head? = some r} ≃
      {b : Fin s.length → Bool //
        (maskSubword false (lastRedMask p r s b) : Multiset J) = α ∧
        (maskSubword true (lastRedMask p r s b) : Multiset J) = β} := by
  classical
  let ex := exists_suffixMask w p r s hw hp hs
  let f (u : {u : ShuffleOf α β w // (List.ofFn u.split.2.1).head? = some r}) :
      {b : Fin s.length → Bool //
        (maskSubword false (lastRedMask p r s b) : Multiset J) = α ∧
        (maskSubword true (lastRedMask p r s b) : Multiset J) = β} :=
    ⟨(ex u).choose, by
      rw [(ex u).choose_spec.1,maskSubword_shuffleTags,maskSubword_shuffleTags]
      exact ⟨u.1.wt_mask_false,u.1.wt_mask_true⟩⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro u u' he
    apply Subtype.ext
    apply shuffleTags_injective
    rw [← (ex u).choose_spec.1, ← (ex u').choose_spec.1]
    exact congrArg (lastRedMask p r s) (congrArg Subtype.val he)
  · intro b
    let tags := lastRedMask p r s b.1
    obtain ⟨v,hv⟩ := exists_mask_of_fst w.1 tags ((fst_lastRedMask p r s b.1).trans hw.symm)
    have hv' (c : Bool) : FreeMonoid.toList (maskWord w.1 v c) = maskSubword c tags :=
      (maskSubword_ofFn w.1 v c).symm.trans (congrArg (maskSubword c) hv)
    obtain ⟨u,hu⟩ := ShuffleOf.exists_mask_eq (s := w) v
      (by rw [QuantumGroup.wt,hv']; exact b.2.1) (by rw [QuantumGroup.wt,hv']; exact b.2.2)
    have ht : shuffleTags w u = tags := by simpa only [shuffleTags,hu,Seq.lbl] using hv
    have hr : (List.ofFn u.split.2.1).head? = some r := by
      rw [u.ofFn_split_snd, ← maskSubword_shuffleTags, ht]
      exact head_lastRedMask p r s b.1
    exact ⟨⟨u,hr⟩,Subtype.ext ((ex ⟨u,hr⟩).choose_spec.2 _ ht.symm).symm⟩

/-- The reindexing preserves the complete coloured tagged diagram. -/
theorem lastRedShuffleMaskEquiv_tags (hw : List.ofFn w.1 = p ++ r :: s) (hp : r ∉ p) (hs : r ∉ s)
    (u : {u : ShuffleOf α β w // (List.ofFn u.split.2.1).head? = some r}) :
    lastRedMask p r s (lastRedShuffleMaskEquiv w p r s hw hp hs u).1 = shuffleTags w u.1 :=
  (exists_suffixMask w p r s hw hp hs u).choose_spec.1

/-- Sum over the surviving KLR shuffles by summing over masks on the black suffix
with the required two factor contents. This applies to arbitrary tagged-word coefficients. -/
theorem sum_lastRedShuffleMasks {M : Type*} [AddCommMonoid M]
    (hw : List.ofFn w.1 = p ++ r :: s) (hp : r ∉ p) (hs : r ∉ s) (F : List (J × Bool) → M) :
    ∑ u : {u : ShuffleOf α β w // (List.ofFn u.split.2.1).head? = some r}, F (shuffleTags w u.1) =
      ∑ b : {b : Fin s.length → Bool //
        (maskSubword false (lastRedMask p r s b) : Multiset J) = α ∧
        (maskSubword true (lastRedMask p r s b) : Multiset J) = β}, F (lastRedMask p r s b.1) := by
  classical
  let E := lastRedShuffleMaskEquiv w p r s hw hp hs
  convert E.sum_comp (fun b => F (lastRedMask p r s b.1)) using 1
  exact Finset.sum_congr rfl fun u _ => congrArg F (lastRedShuffleMaskEquiv_tags w p r s hw hp hs u).symm

end Categorification.Stendhal.FirstWeight
