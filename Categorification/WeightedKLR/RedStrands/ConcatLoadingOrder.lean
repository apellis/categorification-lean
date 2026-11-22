/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TwoPieceLoading

/-!
# Concatenated loadings above a two-piece loading

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 5.20. The comparison of the standardization `S(S_t ⊠ R e(u))` with the standard
module `S_{t λ_{ℓ+1} u}` of Definition 5.1 needs to know which concatenations `c d` lie strictly
above the two-piece loading `t λ_{ℓ+1} u` in Webster's preorder: those with `c` strictly above
`t`, and those with `d` violated (a black strand left of the last red strand).

## Main results

* `blackCount_concatLoading_last_eq`: the black counts of `c d` at the last red strand.
* `stendhalLT_twoPiece_concatLoading`: `c` strictly above `t` puts `c d` strictly above
  `t λ_{ℓ+1} u`.
* `stendhalLT_twoPiece_concatLoading_violated`: so does a violated `d`, with `c = t`.
* `stendhalLT_of_le_of_lt`: the preorder is transitive on the strict side.
-/

namespace Categorification.Stendhal

open KLR

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} {θ β : Multiset I}

local notation "lastColour" => Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)

theorem stendhalLE_trans {μ : Multiset (I ⊕ Fin ℓ)} {a b c : Seq μ} (hab : StendhalLE a b)
    (hbc : StendhalLE b c) : StendhalLE a c :=
  fun r i => (hab r i).trans (hbc r i)

theorem stendhalLT_of_le_of_lt {μ : Multiset (I ⊕ Fin ℓ)} {a b c : Seq μ}
    (hab : StendhalLE a b) (hbc : StendhalLT b c) : StendhalLT a c :=
  ⟨stendhalLE_trans hab hbc.1, fun hca => hbc.2 (stendhalLE_trans hca hab)⟩

omit [DecidableEq I] in
/-- A loading of the last red strand contains that red strand. -/
theorem exists_lbl_last (d : Seq ((stendhalWeight 1 β).map lastColour)) :
    ∃ y, d.lbl y = .inr (Fin.last ℓ) := by
  have : (Sum.inr (Fin.last ℓ) : I ⊕ Fin (ℓ + 1)) ∈ Finset.univ.val.map d.1 := by
    rw [d.2]
    simp [stendhalWeight]
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 this
  exact ⟨a, ha⟩

/-- The black counts of `c d` at the last red strand: all of `θ`, and the black strands of `d`
left of it. -/
theorem blackCount_concatLoading_last_eq (c : Seq (stendhalWeight ℓ θ))
    (d : Seq ((stendhalWeight 1 β).map lastColour)) (i : I) :
    blackCount (concatLoading θ β c d) (Fin.last ℓ) i =
      θ.count i + blackCount d (Fin.last ℓ) i := by
  rw [concatLoading, blackCount_cast, blackCount_append_right _ _ _ (exists_lbl_last d),
    card_filter_lbl_eq,
    show (Sum.inl i : I ⊕ Fin (ℓ + 1)) = addRedColor ℓ (Sum.inl i) from rfl,
    Multiset.count_map_eq_count' _ _ (addRedColor_injective ℓ) (Sum.inl i)]
  · simp [stendhalWeight, Multiset.count_map_eq_count' _ _ Sum.inl_injective]
  · intro x hx
    exact (parabolicPrefix_red_lt_last θ _ x hx).ne rfl

theorem stendhalLE_twoPiece_concatLoading {t c : Seq (stendhalWeight ℓ θ)} (u : Seq β)
    (hc : StendhalLE t c) (d : Seq ((stendhalWeight 1 β).map lastColour)) :
    StendhalLE (twoPieceLoading θ β t u) (concatLoading θ β c d) := fun R i => by
  rcases Fin.eq_castSucc_or_eq_last R with ⟨r, rfl⟩ | rfl
  · rw [blackCount_twoPieceLoading_castSucc, blackCount_concatLoading_castSucc]
    exact hc r i
  · rw [blackCount_twoPieceLoading_last, blackCount_concatLoading_last_eq]
    omega

/-- A concatenation `c d` with `c` strictly above `t` lies strictly above `t λ_{ℓ+1} u`. -/
theorem stendhalLT_twoPiece_concatLoading {t c : Seq (stendhalWeight ℓ θ)} (u : Seq β)
    (hc : StendhalLT t c) (d : Seq ((stendhalWeight 1 β).map lastColour)) :
    StendhalLT (twoPieceLoading θ β t u) (concatLoading θ β c d) := by
  refine ⟨stendhalLE_twoPiece_concatLoading u hc.1 d, fun hle => hc.2 fun r i => ?_⟩
  have := hle r.castSucc i
  rwa [blackCount_twoPieceLoading_castSucc, blackCount_concatLoading_castSucc] at this

theorem blackCount_pos_of_violated
    {d : Seq ((stendhalWeight 1 β).map lastColour)} (hd : IsViolated d) :
    ∃ j, 0 < blackCount d (Fin.last ℓ) j := by
  obtain ⟨h0, hv⟩ := hd
  rcases hx : d.lbl ⟨0, h0⟩ with j | r
  · refine ⟨j, Finset.card_pos.2 ⟨⟨0, h0⟩, ?_⟩⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hx, fun b hb => ?_⟩
    rw [Fin.lt_def]
    refine Nat.pos_of_ne_zero fun hb0 => ?_
    rw [show b = ⟨0, h0⟩ from Fin.ext hb0, hx] at hb
    cases hb
  · simp [Seq.lbl, hx] at hv

/-- A concatenation `t d` with `d` violated lies strictly above `t λ_{ℓ+1} u`. -/
theorem stendhalLT_twoPiece_concatLoading_violated (t : Seq (stendhalWeight ℓ θ)) (u : Seq β)
    {d : Seq ((stendhalWeight 1 β).map lastColour)} (hd : IsViolated d) :
    StendhalLT (twoPieceLoading θ β t u) (concatLoading θ β t d) := by
  refine ⟨stendhalLE_twoPiece_concatLoading u (fun _ _ => le_rfl) d, fun hle => ?_⟩
  obtain ⟨j, hj⟩ := blackCount_pos_of_violated hd
  have := hle (Fin.last ℓ) j
  rw [blackCount_twoPieceLoading_last, blackCount_concatLoading_last_eq] at this
  omega

end Categorification.Stendhal
