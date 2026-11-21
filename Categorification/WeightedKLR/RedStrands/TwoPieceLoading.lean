/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackCountTransport
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleDescent

/-!
# The loading of a two-piece standard module

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.21. The layers of the filtration of `T^λ e` are the standardizations
`S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))` of a loading `t` of the first `ℓ` red strands and a black word
`u`. The corresponding loading of all `ℓ + 1` red strands is `t` followed by the last red strand
and then `u` (`twoPieceLoading`). Its black counts are those of `t` for the first `ℓ` red
strands, and the whole of `θ` for the last red strand.

## Main definitions

* `twoPieceLoading t u`: the loading `t λ_{ℓ+1} u`.

## Main results

* `blackCount_twoPieceLoading_castSucc`, `blackCount_twoPieceLoading_last`: its black counts.
* `isRedOrdered_twoPieceLoading`: it is red-ordered when `t` is.
-/

namespace Categorification.Stendhal

open KLR

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} (θ β : Multiset I)

local notation "lastColour" => Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)

omit [DecidableEq I] in
theorem isRedOrdered_cast {μ μ' : Multiset (I ⊕ Fin ℓ)} (h : μ = μ') {s : Seq μ}
    (hs : IsRedOrdered s) : IsRedOrdered (Seq.cast h s) := by
  subst h
  exact hs

/-- The number of positions of `s` with label `x` is the multiplicity of `x`. -/
theorem card_filter_lbl_eq {J : Type*} [DecidableEq J] {μ : Multiset J} (s : Seq μ) (x : J) :
    (Finset.univ.filter fun a => s.lbl a = x).card = μ.count x := by
  have h := congrArg (Multiset.count x) s.2
  rw [← h, count_map_univ, Finset.card_filter]

/-- A red strand at the first position has no black strand to its left. -/
theorem blackCount_eq_zero_of_first {μ : Multiset (I ⊕ Fin ℓ)} (s : Seq μ)
    (h : 0 < Multiset.card μ) {r : Fin ℓ} (hr : s.lbl ⟨0, h⟩ = .inr r) (i : I) :
    blackCount s r i = 0 := by
  rw [blackCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ ha
  have := ha.2 _ hr
  rw [Fin.lt_def] at this
  exact Nat.not_lt_zero _ this

/-- The loading `c d` of all `ℓ + 1` red strands made of a loading `c` of the first `ℓ` red
strands and a loading `d` of the last one. -/
def concatLoading (c : Seq (stendhalWeight ℓ θ)) (d : Seq ((stendhalWeight 1 β).map lastColour)) :
    Seq (stendhalWeight (ℓ + 1) (θ + β)) :=
  Seq.cast (parabolicInputWeights_add θ β) ((Seq.map (addRedColor ℓ) c).append d)

/-- The loading `t λ_{ℓ+1} u` of all `ℓ + 1` red strands: the loading `t` of the first `ℓ`,
followed by the last red strand and then the black word `u`. -/
def twoPieceLoading (t : Seq (stendhalWeight ℓ θ)) (u : Seq β) :
    Seq (stendhalWeight (ℓ + 1) (θ + β)) :=
  concatLoading θ β t (Seq.map lastColour (SingleRed.insertWord β u))

variable {θ β}

theorem blackCount_concatLoading_castSucc (c : Seq (stendhalWeight ℓ θ))
    (d : Seq ((stendhalWeight 1 β).map lastColour)) (r : Fin ℓ) (i : I) :
    blackCount (concatLoading θ β c d) r.castSucc i = blackCount c r i := by
  rw [concatLoading, blackCount_cast, blackCount_append_left]
  · exact blackCount_map (Fin.castSucc_injective ℓ) c r i
  · obtain ⟨a, ha⟩ := exists_lbl_eq_inr c r
    refine ⟨Fin.cast (Multiset.card_map _ _).symm a, ?_⟩
    rw [Seq.map_lbl]
    simp [ha]
  · intro y hy
    exact (Fin.castSucc_lt_last r).ne (parabolicLast_red_eq_last β _ y hy)

omit [DecidableEq I] in
/-- A loading of the last red strand which is not violated starts with that red strand. -/
theorem lbl_zero_of_not_isViolated (d : Seq ((stendhalWeight 1 β).map lastColour))
    (hd : ¬ IsViolated d) (h0 : 0 < Multiset.card ((stendhalWeight 1 β).map lastColour)) :
    d.lbl ⟨0, h0⟩ = .inr (Fin.last ℓ) := by
  rcases hx : d.lbl ⟨0, h0⟩ with j | r
  · exact (hd ⟨h0, by simp [hx]⟩).elim
  · rw [parabolicLast_red_eq_last β d _ hx]

theorem blackCount_concatLoading_last (c : Seq (stendhalWeight ℓ θ))
    (d : Seq ((stendhalWeight 1 β).map lastColour)) (hd : ¬ IsViolated d) (i : I) :
    blackCount (concatLoading θ β c d) (Fin.last ℓ) i = θ.count i := by
  have h0 : 0 < Multiset.card ((stendhalWeight 1 β).map lastColour) := by
    simp [stendhalWeight]
  have hd0 := lbl_zero_of_not_isViolated d hd h0
  rw [concatLoading, blackCount_cast, blackCount_append_right _ _ _ ⟨_, hd0⟩,
    blackCount_eq_zero_of_first _ h0 hd0, add_zero, card_filter_lbl_eq,
    show (Sum.inl i : I ⊕ Fin (ℓ + 1)) = addRedColor ℓ (Sum.inl i) from rfl,
    Multiset.count_map_eq_count' _ _ (addRedColor_injective ℓ) (Sum.inl i)]
  · simp [stendhalWeight, Multiset.count_map_eq_count' _ _ Sum.inl_injective]
  · intro x hx
    exact (parabolicPrefix_red_lt_last θ _ x hx).ne rfl

omit [DecidableEq I] in
theorem isNotViolated_insertWord (u : Seq β) :
    ¬ IsViolated (Seq.map lastColour (SingleRed.insertWord β u)) := by
  rintro ⟨h0, hv⟩
  rw [Seq.map_lbl, show Fin.cast (Multiset.card_map _ _) (⟨0, h0⟩ : Fin _) =
    ⟨0, by simp [stendhalWeight]⟩ from Fin.ext rfl, SingleRed.insertWord_head] at hv
  simp at hv

theorem blackCount_twoPieceLoading_castSucc (t : Seq (stendhalWeight ℓ θ)) (u : Seq β)
    (r : Fin ℓ) (i : I) :
    blackCount (twoPieceLoading θ β t u) r.castSucc i = blackCount t r i :=
  blackCount_concatLoading_castSucc t _ r i

theorem blackCount_twoPieceLoading_last (t : Seq (stendhalWeight ℓ θ)) (u : Seq β) (i : I) :
    blackCount (twoPieceLoading θ β t u) (Fin.last ℓ) i = θ.count i :=
  blackCount_concatLoading_last t _ (isNotViolated_insertWord u) i

omit [DecidableEq I] in
theorem isRedOrdered_concatLoading {c : Seq (stendhalWeight ℓ θ)} (hc : IsRedOrdered c)
    (d : Seq ((stendhalWeight 1 β).map lastColour)) : IsRedOrdered (concatLoading θ β c d) :=
  isRedOrdered_cast _ (parabolic_isRedOrdered_append θ β
    (isRedOrdered_map_of_strictMono Fin.castSucc θ Fin.strictMono_castSucc c hc)
    (parabolicLast_ordered β _))

omit [DecidableEq I] in
theorem isRedOrdered_twoPieceLoading {t : Seq (stendhalWeight ℓ θ)} (ht : IsRedOrdered t)
    (u : Seq β) : IsRedOrdered (twoPieceLoading θ β t u) :=
  isRedOrdered_concatLoading ht _

omit [DecidableEq I] in
/-- A loading of the first `ℓ` red strands is red-ordered when its recolouring is. -/
theorem isRedOrdered_of_map_castSucc {c : Seq (stendhalWeight ℓ θ)}
    (hc : IsRedOrdered (Seq.map (addRedColor ℓ) c)) : IsRedOrdered c := by
  intro a b r r' hab ha hb
  have hcard := Multiset.card_map (addRedColor ℓ) (stendhalWeight ℓ θ)
  have h := hc (Fin.cast hcard.symm a) (Fin.cast hcard.symm b) r.castSucc r'.castSucc
    (by rwa [Fin.lt_def] at hab ⊢) (by simp [ha]) (by simp [hb])
  exact Fin.castSucc_lt_castSucc_iff.mp h

/-- **Comparison of black counts.** A red-ordered loading strictly above `t λ_{ℓ+1} u` of the
form `c d`, with `d` not violated, has `c` strictly above `t`. -/
theorem stendhalLT_of_concatLoading {t : Seq (stendhalWeight ℓ θ)} {u : Seq β}
    {c : Seq (stendhalWeight ℓ θ)} {d : Seq ((stendhalWeight 1 β).map lastColour)}
    (hd : ¬ IsViolated d) (h : StendhalLT (twoPieceLoading θ β t u) (concatLoading θ β c d)) :
    StendhalLT t c := by
  refine ⟨fun r i => ?_, fun hle => h.2 fun R i => ?_⟩
  · have := h.1 r.castSucc i
    rwa [blackCount_twoPieceLoading_castSucc, blackCount_concatLoading_castSucc] at this
  · rcases Fin.eq_castSucc_or_eq_last R with ⟨r, rfl⟩ | rfl
    · rw [blackCount_twoPieceLoading_castSucc, blackCount_concatLoading_castSucc]
      exact hle r i
    · rw [blackCount_twoPieceLoading_last, blackCount_concatLoading_last c d hd]

end Categorification.Stendhal
