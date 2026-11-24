/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AdjacentBlockRow

/-!
# Cutting a loading at the retained red boundaries

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
§6.1, proof of Lemma 6.8. Cut before each exterior red strand and before the first red
in the exchanging pair. The black strands after each retained cut belong to that block.
The two successive red pieces of the pair give one local loading.
-/

namespace Categorification.Stendhal.RedBlock

open KLR

variable {I : Type*} {ℓ : ℕ}

private def StartsRed (w : List (I ⊕ Fin ℓ)) : Prop :=
  ∀ i, w.head? ≠ some (.inl i)

private theorem blackPrefix (w : List (I ⊕ Fin ℓ)) :
    ∃ (u : List I) (v : List (I ⊕ Fin ℓ)), w = u.map Sum.inl ++ v ∧ StartsRed v := by
  induction w with
  | nil => exact ⟨[], [], rfl, by simp [StartsRed]⟩
  | cons x w ih =>
    cases x with
    | inl i =>
      obtain ⟨u, v, h, hv⟩ := ih
      exact ⟨i :: u, v, by simpa using congrArg (List.cons (.inl i)) h, hv⟩
    | inr r => exact ⟨[], .inr r :: w, rfl, by simp [StartsRed]⟩

private theorem peelRed {w : List (I ⊕ Fin ℓ)} {r : Fin ℓ} {rs : List (Fin ℓ)}
    (h : w.filterMap Sum.getRight? = r :: rs) (hs : StartsRed w) :
    ∃ (u : List I) (v : List (I ⊕ Fin ℓ)), w = (.inr r :: u.map Sum.inl) ++ v ∧
      v.filterMap Sum.getRight? = rs ∧ StartsRed v := by
  cases w with
  | nil => simp at h
  | cons x w =>
    cases x with
    | inl i => exact (hs i rfl).elim
    | inr r' =>
      have h' : r' :: w.filterMap Sum.getRight? = r :: rs := h
      obtain ⟨rfl, hr⟩ := List.cons.inj h'
      obtain ⟨u, v, hv, hv'⟩ := blackPrefix w
      refine ⟨u, v, by simpa using congrArg (List.cons (.inr r')) hv, ?_, hv'⟩
      simpa [hv, List.filterMap_map, Function.comp_def] using hr

private def spectatorWords (L : List (Fin ℓ × List I)) : List (I ⊕ Fin ℓ) :=
  L.flatMap fun x => .inr x.1 :: x.2.map Sum.inl

private theorem takeSpectators (Lr : List (Fin ℓ)) {Mr : List (Fin ℓ)}
    {w : List (I ⊕ Fin ℓ)} (h : w.filterMap Sum.getRight? = Lr ++ Mr) (hs : StartsRed w) :
    ∃ (L : List (Fin ℓ × List I)) (v : List (I ⊕ Fin ℓ)),
      L.map Prod.fst = Lr ∧ w = spectatorWords L ++ v ∧
      v.filterMap Sum.getRight? = Mr ∧ StartsRed v := by
  induction Lr generalizing w with
  | nil => exact ⟨[], w, rfl, rfl, h, hs⟩
  | cons r Lr ih =>
    obtain ⟨u, v, he, hv, hv'⟩ := peelRed h hs
    obtain ⟨L, w', hL, hW, hw', hw''⟩ := ih hv hv'
    refine ⟨(r,u) :: L, w', by simp [hL], ?_, hw', hw''⟩
    simp [he, hW, spectatorWords, List.append_assoc]

private theorem headOfFn {α : Type*} {n : ℕ} (f : Fin n → α) (hn : 0 < n) :
    (List.ofFn f).head? = some (f ⟨0,hn⟩) := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simpa), List.getElem_ofFn]

private theorem startsRed_of_unviolated {μ : Multiset (I ⊕ Fin ℓ)}
    (t : Seq μ) (ht : ¬ IsViolated t) :
    StartsRed (List.ofFn t.lbl) := by
  intro i hi
  obtain ⟨v, ev⟩ := List.head?_eq_some_iff.1 hi
  have hp : 0 < μ.card := by rw [← List.length_ofFn (f := t.lbl), ev]; simp
  obtain he := Option.some.inj ((headOfFn t.lbl hp).symm.trans hi)
  exact ht ⟨hp, by simp [he]⟩

private theorem unviolated_of_head {μ : Multiset (I ⊕ Fin ℓ)} (t : Seq μ) {r : Fin ℓ}
    (h : (List.ofFn t.lbl).head? = some (.inr r)) : ¬ IsViolated t := by
  rintro ⟨hp, hv⟩
  have he := Option.some.inj ((headOfFn t.lbl hp).symm.trans h)
  simp [he] at hv

private theorem wordMap {A D : Type*} (f : A → D) {μ : Multiset A} (t : Seq μ) :
    List.ofFn (Seq.map f t).lbl = (List.ofFn t.lbl).map f := by
  rw [List.map_ofFn]
  exact (List.ofFn_congr (Multiset.card_map f μ).symm (f ∘ t.lbl)).symm

private theorem wordCast {A : Type*} {μ μ' : Multiset A} (h : μ = μ') (t : Seq μ) :
    List.ofFn (Seq.cast h t).lbl = List.ofFn t.lbl := by
  subst μ'
  rfl

private theorem coeWord {A : Type*} {μ : Multiset A} (t : Seq μ) :
    (List.ofFn t.lbl : Multiset A) = μ := by
  rw [← Fin.univ_val_map]
  exact t.2

private theorem wordOfList {A : Type*} {μ : Multiset A}
    (l : List A) (h : (l : Multiset A) = μ) :
    List.ofFn (KLRAlgebra.Seq.ofList l h).lbl = l := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    rw [← Multiset.coe_card, h]
  · intro a h₁ h₂
    rw [List.getElem_ofFn]
    exact KLRAlgebra.Seq.ofList_lbl l h _

private theorem wordAppend {A : Type*} {μ ν : Multiset A} (s : Seq μ) (t : Seq ν) :
    List.ofFn (s.append t).lbl = List.ofFn s.lbl ++ List.ofFn t.lbl := by
  change List.ofFn (s.append t).1 = List.ofFn s.1 ++ List.ofFn t.1
  apply List.ext_getElem
  · simp
  · intro n h₁ h₂
    rw [List.getElem_ofFn]
    by_cases hn : n < μ.card
    · rw [Seq.append_apply_lt _ _ _ hn, List.getElem_append_left (by simpa using hn),
        List.getElem_ofFn]
    · rw [Seq.append_apply_ge _ _ _ (by simp; omega),
        List.getElem_append_right (by simp; omega), List.getElem_ofFn]
      simp

private def contents (L : List (Fin ℓ × List I)) : List (Fin ℓ × Multiset I) :=
  L.map fun x => (x.1, (x.2 : Multiset I))

private def spectLoading (r : Fin ℓ) (u : List I) :
    Seq (spectator (r, (u : Multiset I))).localWeight :=
  KLRAlgebra.Seq.ofList (.inr 0 :: u.map Sum.inl) (by
    have h0 : (Finset.univ.val : Multiset (Fin 1)) = {0} := by decide
    change ((.inr 0 :: u.map Sum.inl : List (I ⊕ Fin 1)) : Multiset _) =
      stendhalWeight 1 (u : Multiset I)
    simp only [stendhalWeight, h0, Multiset.map_coe, Multiset.map_singleton]
    rw [← Multiset.cons_coe, ← Multiset.singleton_add]
    exact add_comm _ _)

private theorem spectWord (r : Fin ℓ) (u : List I) :
    List.ofFn (Seq.map (spectator (r, (u : Multiset I))).colour (spectLoading r u)).lbl =
      .inr r :: u.map Sum.inl := by
  rw [wordMap, spectLoading, wordOfList]
  simp [colour, List.map_map, Function.comp_def]
  rfl

private def pairLoading (u v : List I) :
    Seq (stendhalWeight 2 ((u : Multiset I) + (v : Multiset I))) :=
  KLRAlgebra.Seq.ofList (.inr 0 :: (u.map Sum.inl ++ .inr 1 :: v.map Sum.inl)) (by
    have hr : (Finset.univ.val : Multiset (Fin 2)) = ([0,1] : List (Fin 2)) := by decide
    rw [stendhalWeight, hr, Multiset.map_add, Multiset.map_coe, Multiset.map_coe,
      Multiset.map_coe, ← Multiset.cons_coe, ← Multiset.singleton_add, ← Multiset.coe_add]
    simp only [List.map_cons, List.map_nil, ← Multiset.cons_coe, ← Multiset.singleton_add,
      Multiset.coe_nil, add_zero]
    ac_rfl)

private theorem pairWord (g : Fin 2 ↪ Fin ℓ) (u v : List I) :
    List.ofFn (Seq.map (Sum.map id g) (pairLoading u v)).lbl =
      .inr (g 0) :: (u.map Sum.inl ++ .inr (g 1) :: v.map Sum.inl) := by
  rw [wordMap, pairLoading, wordOfList]
  simp [List.map_map, Function.comp_def]

private def attachSpectators {row : List (RedBlock I ℓ)} (s : Loadings row) :
    (L : List (Fin ℓ × List I)) → Loadings ((contents L).map spectator ++ row)
  | [] => s
  | (r,u) :: xs => (spectLoading r u, attachSpectators s xs)

private theorem attachSpectators_word {row : List (RedBlock I ℓ)} (s : Loadings row)
    (L : List (Fin ℓ × List I)) :
    List.ofFn (place _ (attachSpectators s L)).lbl =
      spectatorWords L ++ List.ofFn (place row s).lbl := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨r,u⟩
    change List.ofFn
      ((Seq.map _ (spectLoading r u)).append (place _ (attachSpectators s xs))).lbl = _
    rw [wordAppend, spectWord, ih]
    simp [spectatorWords, List.append_assoc]

private theorem attachSpectators_unviolated {row : List (RedBlock I ℓ)} (s : Loadings row)
    (hs : ¬ Violated row s) (L : List (Fin ℓ × List I)) :
    ¬ Violated _ (attachSpectators s L) := by
  induction L with
  | nil => exact hs
  | cons x xs ih =>
    rcases x with ⟨r,u⟩
    refine not_or.mpr ⟨unviolated_of_head _ (r := 0) ?_, ih⟩
    change (List.ofFn (spectLoading r u).lbl).head? = _
    rw [spectLoading, wordOfList]
    rfl

private def spectatorLoadings (M : List (Fin ℓ × List I)) :
    Loadings ((contents M).map spectator) :=
  List.append_nil ((contents M).map spectator) ▸ attachSpectators (row := []) PUnit.unit M

private theorem wordPlaceTransport {r s : List (RedBlock I ℓ)} (h : r = s) (u : Loadings r) :
    List.ofFn (place s (h ▸ u)).lbl = List.ofFn (place r u).lbl := by
  subst s
  rfl

private theorem violatedTransport {r s : List (RedBlock I ℓ)} (h : r = s) (u : Loadings r) :
    Violated s (h ▸ u) ↔ Violated r u := by
  subst s
  rfl

private theorem spectatorLoadings_word (M : List (Fin ℓ × List I)) :
    List.ofFn (place _ (spectatorLoadings M)).lbl = spectatorWords M := by
  unfold spectatorLoadings
  have hnil : List.ofFn (place ([] : List (RedBlock I ℓ)) PUnit.unit).lbl = [] :=
    List.ofFn_zero
  rw [wordPlaceTransport, attachSpectators_word, hnil, List.append_nil]

private theorem spectatorLoadings_unviolated (M : List (Fin ℓ × List I)) :
    ¬ Violated _ (spectatorLoadings M) := by
  unfold spectatorLoadings
  rw [violatedTransport]
  exact attachSpectators_unviolated (row := []) PUnit.unit not_false M

/-- Cutting a nonviolated loading at the exterior red strands recovers local loadings. -/
theorem exists_place_adjacent {ν : Multiset I} (t : Seq (stendhalWeight ℓ ν))
    (ht : ¬ IsViolated t) (Lr Mr : List (Fin ℓ)) (g : Fin 2 ↪ Fin ℓ)
    (horder : redWord t = Lr ++ g 0 :: g 1 :: Mr) :
    ∃ (L M : List (Fin ℓ × Multiset I)) (β : Multiset I)
      (h : weightSum (adjacentRow L M g β) = stendhalWeight ℓ ν)
      (s : Loadings (adjacentRow L M g β)),
      L.map Prod.fst = Lr ∧ M.map Prod.fst = Mr ∧
        Seq.cast h (place _ s) = t ∧ ¬ Violated _ s := by
  let w := List.ofFn t.lbl
  have hr : w.filterMap Sum.getRight? = Lr ++ g 0 :: g 1 :: Mr := by
    change (List.ofFn t.lbl).filterMap Sum.getRight? = _
    rw [← horder, List.ofFn_eq_map, List.filterMap_map]
    rfl
  obtain ⟨L, w', hL, hW, hw', hs'⟩ := takeSpectators Lr hr (startsRed_of_unviolated t ht)
  obtain ⟨u, w₁, hw₁, hr₁, hs₁⟩ := peelRed hw' hs'
  obtain ⟨v, w₂, hw₂, hr₂, hs₂⟩ := peelRed hr₁ hs₁
  obtain ⟨M, w₃, hM, hw₃, hr₃, hs₃⟩ :=
    takeSpectators Mr (Mr := []) (by simpa using hr₂) hs₂
  have h₃ : w₃ = [] := by
    cases w₃ with
    | nil => rfl
    | cons x xs =>
      cases x with
      | inl i => exact (hs₃ i rfl).elim
      | inr r => simp at hr₃
  let β : Multiset I := (u : Multiset I) + (v : Multiset I)
  let s₀ := spectatorLoadings M
  let s : Loadings (adjacentRow (contents L) (contents M) g β) :=
    attachSpectators (row := ⟨2,g,β⟩ :: (contents M).map spectator) (pairLoading u v, s₀) L
  have hsw : List.ofFn (place _ s).lbl = w := by
    change List.ofFn (place _ (attachSpectators _ L)).lbl = w
    rw [hW, hw₁, hw₂, hw₃, h₃, List.append_nil, attachSpectators_word]
    congr 1
    change List.ofFn ((Seq.map _ (pairLoading u v)).append (place _ s₀)).lbl = _
    rw [wordAppend, pairWord]
    change _ ++ List.ofFn (place _ (spectatorLoadings M)).lbl = _
    rw [spectatorLoadings_word]
    simp [List.append_assoc]
  have hwt : weightSum (adjacentRow (contents L) (contents M) g β) = stendhalWeight ℓ ν :=
    (coeWord (place _ s)).symm.trans
      ((congrArg (fun xs : List (I ⊕ Fin ℓ) => (xs : Multiset (I ⊕ Fin ℓ))) hsw).trans
        (coeWord t))
  refine ⟨contents L, contents M, β, hwt, s, ?_, ?_, ?_, ?_⟩
  · simpa [contents, List.map_map, Function.comp_def] using hL
  · simpa [contents, List.map_map, Function.comp_def] using hM
  · apply Subtype.ext
    apply List.ofFn_injective
    change List.ofFn (Seq.cast hwt (place _ s)).lbl = w
    rw [wordCast, hsw]
  · apply attachSpectators_unviolated _ _ L
    change ¬ (IsViolated (pairLoading u v) ∨ Violated _ (spectatorLoadings M))
    refine not_or.mpr ⟨unviolated_of_head _ (r := 0) ?_, spectatorLoadings_unviolated M⟩
    rw [pairLoading, wordOfList]
    rfl

end Categorification.Stendhal.RedBlock
