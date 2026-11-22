/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceLoading
import Categorification.KLR.Prop320
import Categorification.KLR.DividedPowerIdempotents

/-!
# Every red-ordered loading is a two-piece loading

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 5.17. A red-ordered loading of `ℓ + 1` red strands reads `t λ_{ℓ+1} w`: a loading
`t` of the first `ℓ` red strands with black weight `θ`, then the last red strand, then a black
word `w` of weight `β`, where `θ` is the black content left of the last red strand
(`twoPieceLoading`). This is the decomposition used in the induction on the number of red
strands.

## Main results

* `ofFn_twoPieceLoading`: the word of `t λ_{ℓ+1} w`.
* `exists_twoPieceLoading_eq`: every red-ordered loading is a two-piece loading.
-/

namespace Categorification.Stendhal

open KLR

variable {I : Type*} {ℓ : ℕ}

private theorem ofFn_seq_cast {J : Type*} {a b : Multiset J} (h : a = b) (s : Seq a) :
    List.ofFn (KLR.Seq.cast h s).lbl = List.ofFn s.lbl := by
  subst b
  rfl

private theorem ofFn_seq_map {J K : Type*} (f : J → K) {a : Multiset J} (s : Seq a) :
    List.ofFn (KLR.Seq.map f s).lbl = (List.ofFn s.lbl).map f := by
  rw [List.map_ofFn]
  exact (List.ofFn_congr (Multiset.card_map f a).symm (f ∘ s.lbl)).symm

private theorem ofFn_seq_singleton {J : Type*} {a : J} (s : Seq ({a} : Multiset J)) :
    List.ofFn s.lbl = [a] := by
  have hl : s.lbl = fun _ => a := funext fun j => Multiset.mem_singleton.mp (s.mem j)
  rw [hl]
  simp

private theorem ofFn_seq_ofList {J : Type*} {a : Multiset J} (l : List J)
    (h : (l : Multiset J) = a) : List.ofFn (KLRAlgebra.Seq.ofList l h).lbl = l := by
  apply List.ext_getElem
  · rw [List.length_ofFn, ← Multiset.coe_card, h]
  · intro n h1 h2
    rw [List.getElem_ofFn]
    rfl

/-- A multiset over `I ⊕ R` is its left part plus its right part. -/
private theorem multiset_eq_inl_add_inr {R : Type*} (l : List (I ⊕ R)) :
    (l : Multiset (I ⊕ R)) = ((l.filterMap Sum.getLeft? : List I) : Multiset I).map Sum.inl +
      ((l.filterMap Sum.getRight? : List R) : Multiset R).map Sum.inr := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rcases x with i | r
    · simp only [List.filterMap_cons, Sum.getLeft?_inl, Sum.getRight?_inl, ← Multiset.cons_coe,
        Multiset.map_cons, ih, Multiset.cons_add]
    · simp only [List.filterMap_cons, Sum.getLeft?_inr, Sum.getRight?_inr, ← Multiset.cons_coe,
        Multiset.map_cons, ih, Multiset.add_cons]

private theorem filterMap_const_none {J K : Type*} (s : Multiset J) :
    s.filterMap (fun _ => (none : Option K)) = 0 := by
  induction s using Multiset.induction_on <;> simp_all

private theorem filterMap_getLeft_add {R : Type*} (A : Multiset I) (B : Multiset R) :
    (A.map Sum.inl + B.map Sum.inr).filterMap Sum.getLeft? = A := by
  simp [Multiset.filterMap_add, Multiset.filterMap_map, Function.comp_def, filterMap_const_none]

private theorem filterMap_getRight_add {R : Type*} (A : Multiset I) (B : Multiset R) :
    (A.map Sum.inl + B.map Sum.inr).filterMap Sum.getRight? = B := by
  simp [Multiset.filterMap_add, Multiset.filterMap_map, Function.comp_def, filterMap_const_none]

local notation "lastColour" => Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)

/-- The word of the two-piece loading `t λ_{ℓ+1} w`. -/
theorem ofFn_twoPieceLoading {θ β : Multiset I} (t : Seq (stendhalWeight ℓ θ)) (w : Seq β) :
    List.ofFn (twoPieceLoading θ β t w).lbl =
      (List.ofFn t.lbl).map (addRedColor ℓ) ++ .inr (Fin.last ℓ) :: (List.ofFn w.lbl).map .inl := by
  rw [twoPieceLoading, concatLoading, ofFn_seq_cast, KLR.ofFn_append, ofFn_seq_map,
    ofFn_seq_map, SingleRed.insertWord, ofFn_seq_cast, KLR.ofFn_append, ofFn_seq_singleton,
    ofFn_seq_map]
  simp [Function.comp_def]

/-- The labels of the first `ℓ` red strands and the black strands, read back from
`I ⊕ Fin (ℓ + 1)`; the last red strand is dropped. -/
private def lowerColour : I ⊕ Fin (ℓ + 1) → Option (I ⊕ Fin ℓ)
  | .inl i => some (.inl i)
  | .inr r => if h : r = Fin.last ℓ then none else some (.inr (r.castPred h))

private theorem map_filterMap_lowerColour (l : List (I ⊕ Fin (ℓ + 1)))
    (hl : Sum.inr (Fin.last ℓ) ∉ l) : (l.filterMap lowerColour).map (addRedColor ℓ) = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.mem_cons, not_or] at hl
    rcases x with i | r
    · rw [List.filterMap_cons, lowerColour.eq_1]
      simp [ih hl.2]
    · have hr : r ≠ Fin.last ℓ := fun h => hl.1 (by rw [h])
      rw [List.filterMap_cons, lowerColour.eq_2]
      simp [hr, ih hl.2]

private theorem map_filterMap_getLeft {R : Type*} (l : List (I ⊕ R))
    (hl : ∀ x ∈ l, x.isLeft) : (l.filterMap Sum.getLeft?).map Sum.inl = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rcases x with i | r
    · simp only [List.filterMap_cons, Sum.getLeft?_inl, List.map_cons]
      rw [ih fun y hy => hl y (List.mem_cons_of_mem _ hy)]
    · exact absurd (hl _ List.mem_cons_self) (by simp)

/-- **Webster, arXiv:1309.3796v2, step in the proof of Proposition 5.17.** Every red-ordered
loading of `ℓ + 1` red strands is a two-piece loading `t λ_{ℓ+1} w`, with `t` red-ordered. -/
theorem exists_twoPieceLoading_eq [DecidableEq I] {ν : Multiset I}
    {p : Seq (stendhalWeight (ℓ + 1) ν)} (hp : IsRedOrdered p) :
    ∃ (θ β : Multiset I) (h : θ + β = ν) (t : Seq (stendhalWeight ℓ θ)) (w : Seq β),
      IsRedOrdered t ∧
        Seq.cast (congrArg (stendhalWeight (ℓ + 1)) h) (twoPieceLoading θ β t w) = p := by
  set L := List.ofFn p.lbl with hL
  have hLm : (L : Multiset _) = stendhalWeight (ℓ + 1) ν := by
    rw [hL, ← Fin.univ_val_map]
    exact p.2
  obtain ⟨a, ha⟩ := exists_lbl_eq_inr p (Fin.last ℓ)
  have hmem : Sum.inr (Fin.last ℓ) ∈ L := by
    rw [hL, List.mem_ofFn]
    exact ⟨a, ha⟩
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem hmem
  -- The last red strand occurs once.
  have hcount : (L : Multiset (I ⊕ Fin (ℓ + 1))).count (Sum.inr (Fin.last ℓ)) = 1 := by
    rw [hLm, ← stendhalWeight_addRed, Multiset.count_add, Multiset.count_singleton_self,
      Multiset.count_eq_zero.2]
    intro h
    obtain ⟨x, -, hx⟩ := Multiset.mem_map.1 h
    rcases x with i | r
    · simp [addRedColor] at hx
    · simp only [addRedColor, Sum.map_inr, Sum.inr.injEq] at hx
      exact Fin.castSucc_ne_last r hx
  have hL₁ : Sum.inr (Fin.last ℓ) ∉ L₁ := by
    intro h
    have := Multiset.count_pos.2 (Multiset.mem_coe.2 h)
    rw [hsplit, ← Multiset.coe_add, ← Multiset.cons_coe, Multiset.count_add,
      Multiset.count_cons_self] at hcount
    omega
  -- Every strand right of the last red strand is black.
  have hL₂ : ∀ x ∈ L₂, x.isLeft := by
    intro x hx
    rcases x with i | r
    · rfl
    · exfalso
      obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
      have hlen : L₁.length + 1 + j < L.length := by
        rw [hsplit]
        simp
        omega
      have hlen' : L₁.length < L.length := by omega
      have hcard : L.length = Multiset.card (stendhalWeight (ℓ + 1) ν) := by
        rw [hL, List.length_ofFn]
      have h1 : p.lbl ⟨L₁.length, by omega⟩ = .inr (Fin.last ℓ) := by
        have := List.getElem_ofFn (f := p.lbl) (i := L₁.length) (by rw [← hL]; exact hlen')
        rw [← this]
        simp_rw [← hL, hsplit]
        simp
      have h2 : p.lbl ⟨L₁.length + 1 + j, by omega⟩ = .inr r := by
        have := List.getElem_ofFn (f := p.lbl) (i := L₁.length + 1 + j)
          (by rw [← hL]; exact hlen)
        rw [← this]
        simp_rw [← hL, hsplit]
        rw [List.getElem_append_right (by omega)]
        simp only [show L₁.length + 1 + j - L₁.length = j + 1 by omega,
          List.getElem_cons_succ, hjx]
      have := hp _ _ _ _ (show (⟨L₁.length, _⟩ : Fin _) < ⟨L₁.length + 1 + j, _⟩ by
        exact Fin.mk_lt_mk.2 (by omega)) h1 h2
      exact absurd (Fin.le_last r) (not_le.2 this)
  set L₁' := L₁.filterMap lowerColour
  set L₂' := L₂.filterMap Sum.getLeft?
  have hL₁eq : L₁'.map (addRedColor ℓ) = L₁ := map_filterMap_lowerColour L₁ hL₁
  have hL₂eq : L₂'.map Sum.inl = L₂ := map_filterMap_getLeft L₂ hL₂
  set θ : Multiset I := ((L₁'.filterMap Sum.getLeft? : List I) : Multiset I)
  set β : Multiset I := ((L₂' : List I) : Multiset I)
  -- Comparing contents.
  have hsum : (L₁' : Multiset (I ⊕ Fin ℓ)) + β.map Sum.inl = stendhalWeight ℓ ν := by
    apply Multiset.map_injective (addRedColor_injective (I := I) ℓ)
    apply add_right_cancel (b := ({Sum.inr (Fin.last ℓ)} : Multiset (I ⊕ Fin (ℓ + 1))))
    have hβ : (β.map Sum.inl).map (addRedColor ℓ) =
        ((L₂'.map (Sum.inl : I → I ⊕ Fin (ℓ + 1)) : List _) : Multiset _) := by
      rw [Multiset.map_map, Multiset.map_coe]
      rfl
    rw [stendhalWeight_addRed, ← hLm, hsplit, ← hL₁eq, ← hL₂eq, Multiset.map_add, hβ,
      Multiset.map_coe, Multiset.coe_add, ← Multiset.coe_singleton, Multiset.coe_add,
      Multiset.coe_eq_coe]
    rw [List.append_assoc]
    exact List.perm_append_comm.append_left _
  rw [multiset_eq_inl_add_inr L₁', add_assoc, add_comm _ (β.map Sum.inl), ← add_assoc,
    ← Multiset.map_add, stendhalWeight] at hsum
  have hν : θ + β = ν := by
    have := congrArg (Multiset.filterMap Sum.getLeft?) hsum
    rwa [filterMap_getLeft_add, filterMap_getLeft_add] at this
  have hR : ((L₁'.filterMap Sum.getRight? : List (Fin ℓ)) : Multiset (Fin ℓ)) =
      Finset.univ.val := by
    have := congrArg (Multiset.filterMap Sum.getRight?) hsum
    rwa [filterMap_getRight_add, filterMap_getRight_add] at this
  have hθ : (L₁' : Multiset (I ⊕ Fin ℓ)) = stendhalWeight ℓ θ := by
    rw [multiset_eq_inl_add_inr L₁', hR]
    rfl
  let t : Seq (stendhalWeight ℓ θ) := KLRAlgebra.Seq.ofList L₁' hθ
  let w : Seq β := KLRAlgebra.Seq.ofList L₂' rfl
  have hword : List.ofFn (twoPieceLoading θ β t w).lbl = L := by
    rw [ofFn_twoPieceLoading, ofFn_seq_ofList, ofFn_seq_ofList, hL₁eq, hL₂eq, hsplit]
  refine ⟨θ, β, hν, t, w, ?_, ?_⟩
  · intro a b r r' hab ha hb
    have hlen : L₁'.length = Multiset.card (stendhalWeight ℓ θ) := by
      rw [← Multiset.coe_card, hθ]
    have hcard : L.length = Multiset.card (stendhalWeight (ℓ + 1) ν) := by
      rw [hL, List.length_ofFn]
    have hL1len : L₁.length = L₁'.length := by rw [← hL₁eq, List.length_map]
    have hLlen : L.length = L₁.length + 1 + L₂.length := by
      rw [hsplit]; simp; omega
    have hpos : ∀ (c : Fin (Multiset.card (stendhalWeight ℓ θ))) (s : Fin ℓ),
        t.lbl c = .inr s → p.lbl ⟨c, by have := c.2; omega⟩ = .inr s.castSucc := by
      intro c s hc
      have hc' : L₁'[(c : ℕ)]'(by rw [hlen]; exact c.2) = .inr s := hc
      have := List.getElem_ofFn (f := p.lbl) (i := c) (by
        rw [← hL]; have := c.2; omega)
      rw [← this]
      simp_rw [← hL, hsplit, ← hL₁eq]
      rw [List.getElem_append_left (by simp [hlen]), List.getElem_map, hc']
      rfl
    exact Fin.castSucc_lt_castSucc_iff.mp (hp _ _ _ _ (Fin.mk_lt_mk.2 hab)
      (hpos a r ha) (hpos b r' hb))
  · apply Subtype.ext
    apply List.ofFn_injective
    change List.ofFn (Seq.cast _ (twoPieceLoading θ β t w)).lbl = List.ofFn p.lbl
    rw [ofFn_seq_cast, hword]

end Categorification.Stendhal
