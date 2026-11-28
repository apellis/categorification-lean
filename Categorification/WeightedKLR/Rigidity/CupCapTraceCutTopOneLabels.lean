/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutLeadingDatum
import Categorification.WeightedKLR.Rigidity.CupCapTraceCutTopOneCorner

/-!
# The second top blocks of the leading Mackey data of `S_+` and `S_cut`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half, step L5 (the top factor).

The identity-shuffle part of the leading Mackey layer is induced from the bottom corner along
`R(γ) ⊗ R(δ) → R(γ + δ)` (`topOneCornerEquiv`). At the outer cut of `S_+` (datum `q`, weight
of the window) and at the cut of `S_cut` (datum `q'`, weight `0`) the weights `γ`, `δ` are the
same strands read in two sets of labels. The colours of the cut labels `λ_1 … λ_ℓ` (blocks
`j | ℓ - j`) go to the old colours of `λ⁺` (blocks `j | 2 | ℓ - j`) by `cutToPlusColour`, which
is injective and carries the Stendhal parameters of `λ⁺` to those of `λ`
(`stendhalQ_cutToPlusColour`). Then:

* the last bottom block of `S_+` is the window plus the last bottom block of `S_cut`, relabelled
  (`plusTailWeight_eq`);
* `q.δ = q'.δ.map cutToPlusColour` and `q.γ = q'.γ.map cutToPlusColour`
  (`leadingQuad_δ_eq_map`, `leadingQuad_γ_eq_map`).

So `KLR.SeqRelabel.ofInjectiveOf` along `cutToPlusColour` relabels `R(q'.γ)`, `R(q'.δ)` and
`R(q'.γ + q'.δ)` (cut labels) as the corresponding algebras of `q` (labels `λ⁺`).

Webster's proof does not spell this out. No new hypothesis.

## Main results

* `Stendhal.CupCap.cutToPlusColour`, `Stendhal.CupCap.cutToPlusColour_injective`,
  `Stendhal.CupCap.stendhalQ_cutToPlusColour`.
* `Stendhal.CupCap.suffixWt_windowLoading_eq_map_cut`, `Stendhal.CupCap.plusTailWeight_eq`,
  `Stendhal.CupCap.leadingQuad_δ_eq_map`, `Stendhal.CupCap.leadingQuad_γ_eq_map`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra

variable {I : Type} {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)

/-- **The colours of the cut labels as old colours of `λ⁺`**: the red strand `r` of the blocks
`j | ℓ - j` of `λ` is the old red strand `r` of the blocks `j | 2 | ℓ - j` of `λ⁺`. -/
abbrev cutToPlusColour : I ⊕ Fin (j + (ℓ - j)) → I ⊕ Fin (j + (2 + (ℓ - j))) :=
  Sum.map id (Fin.cast (plusBlock_card j hj).symm ∘ oldRed j hj ∘
    Fin.cast (Nat.add_sub_of_le hj))

theorem cutToPlusColour_injective : Function.Injective (cutToPlusColour (I := I) j hj) :=
  Sum.map_injective.2 ⟨Function.injective_id,
    (Fin.cast_injective _).comp ((oldRed_injective j hj).comp (Fin.cast_injective _))⟩

theorem stendhalQ_cutToPlusColour {k : Type*} [CommRing k] (Q : I → I → MvPolynomial (Fin 2) k)
    (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ) (a b : I ⊕ Fin (j + (ℓ - j))) :
    stendhalQ Q (plusBlockLabels Λ Λc j hj) (cutToPlusColour j hj a) (cutToPlusColour j hj b) =
      stendhalQ Q (cutLabels j hj Λ) a b := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp [stendhalQ, plusBlockLabels, cutLabels, Function.comp_apply]

/-- `cutToPlusColour` after the cut reindexing is the old colour map of `λ⁺`. -/
theorem cutToPlusColour_comp_cast :
    cutToPlusColour (I := I) j hj ∘ Sum.map (id : I → I) (Fin.cast (Nat.add_sub_of_le hj).symm) =
      Sum.map (id : I → I) (Fin.cast (plusBlock_card j hj).symm) ∘ oldColour j hj := by
  funext a
  rcases a with a | a
  · rfl
  · simp only [Function.comp_apply, Sum.map_inr, Fin.cast_cast, Fin.cast_eq_self]

/-- The red strand `j + r` of `λ` is the red strand `j + 2 + r` of `λ⁺`. -/
theorem cutToPlusColour_comp_natAdd :
    cutToPlusColour (I := I) j hj ∘ Sum.map (id : I → I) (Fin.natAdd j) =
      Sum.map (id : I → I) (Fin.natAdd j) ∘
        Sum.map (id : I → I) (Fin.natAdd 2 : Fin (ℓ - j) → Fin (2 + (ℓ - j))) := by
  funext a
  rcases a with a | r
  · rfl
  · simp only [Function.comp_apply, Sum.map_inr, Sum.inr.injEq]
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_natAdd, oldRed, insertPos, Equiv.coe_fn_mk]
    split_ifs
    all_goals (try simp only)
    all_goals omega

variable {θ γ ν₀ : Multiset I}

/-- **The second top block of `S_+` is that of `S_cut`, relabelled.** -/
theorem suffixWt_windowLoading_eq_map_cut (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀)) :
    Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s) =
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s)).map
        (cutToPlusColour j hj) := by
  rw [suffixWt_windowLoading, suffixWt_cutLoading, Multiset.map_map,
    cutToPlusColour_comp_cast]

/-- The red strands of the blocks `2 | ℓ - j`. -/
theorem stendhalWeight_two_add (ν₀ γ : Multiset I) :
    stendhalWeight (2 + (ℓ - j)) (ν₀ + γ) =
      (stendhalWeight 2 ν₀).map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) +
        (stendhalWeight (ℓ - j) γ).map
          (Sum.map (id : I → I) (Fin.natAdd 2 : Fin (ℓ - j) → Fin (2 + (ℓ - j)))) := by
  simp only [stendhalWeight, Multiset.map_add, Multiset.map_map, univ_val_fin_add]
  simp only [Function.comp_def, Sum.map_inl, Sum.map_inr, id_eq]
  abel

/-- **The last bottom block of `S_+` is the window plus the last bottom block of `S_cut`**,
relabelled along `cutToPlusColour`. -/
theorem plusTailWeight_eq (ν₀ γ : Multiset I) :
    Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ)) =
      (stendhalWeight 2 ν₀).map (windowColour j hj) +
        (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (stendhalWeight (ℓ - j) γ)).map (cutToPlusColour j hj) := by
  rw [windowWeight_eq_map, Multiset.map_map (cutToPlusColour j hj), cutToPlusColour_comp_natAdd,
    ← Multiset.map_map (Sum.map (id : I → I) (Fin.natAdd j)), ← Multiset.map_add,
    stendhalWeight_two_add]

/-- **The right parts agree**: `q.δ = q'.δ.map cutToPlusColour` for the leading data `q`
(weight of the window) of `S_+` and `q'` (weight `0`) of `S_cut`. -/
theorem leadingQuad_δ_eq_map (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀))
    (q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))))
    (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
    (hq' : q'.β = 0) :
    q.δ = q'.δ.map (cutToPlusColour j hj) := by
  have h4 := q.h₄.trans (plusTailWeight_eq j hj ν₀ γ)
  rw [hq] at h4
  have h4' := q'.h₄
  rw [hq', zero_add] at h4'
  rw [h4']
  exact add_left_cancel h4

/-- **The left parts agree**: `q.γ = q'.γ.map cutToPlusColour`. -/
theorem leadingQuad_γ_eq_map (s : Seq (stendhalWeight ℓ (θ + γ)))
    (w : Seq (stendhalWeight 2 ν₀))
    (q : MackeyQuad (Seq.prefixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Seq.suffixWt (windowLoading j hj θ γ ν₀ s w)
        (midPos j s + Multiset.card (stendhalWeight 2 ν₀)) (midPos_add_le_card (hj := hj) s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
        (stendhalWeight (2 + (ℓ - j)) (ν₀ + γ))))
    (hq : q.β = (stendhalWeight 2 ν₀).map (windowColour j hj))
    (q' : MackeyQuad (Seq.prefixWt (cutLoading j hj θ γ s) (midPos j s + 0)
        (midPos_le_card_cut s))
      (Seq.suffixWt (cutLoading j hj θ γ s) (midPos j s + 0) (midPos_le_card_cut s))
      (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight j θ))
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j)) (stendhalWeight (ℓ - j) γ)))
    (hq' : q'.β = 0) :
    q.γ = q'.γ.map (cutToPlusColour j hj) := by
  have h2 := (q.h₂.trans (suffixWt_windowLoading_eq_map_cut j hj s w)).trans
    (congrArg (Multiset.map (cutToPlusColour j hj)) q'.h₂.symm)
  rw [Multiset.map_add, ← leadingQuad_δ_eq_map j hj s w q hq q' hq'] at h2
  exact add_right_cancel h2

end Categorification.Stendhal.CupCap
