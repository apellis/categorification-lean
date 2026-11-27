/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KTransport
import Categorification.WeightedKLR.Rigidity.CupCapDiagrams
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAction
import Categorification.WeightedKLR.RedStrands.StandardBlocks

/-!
# Loadings of the three blocks of `λ⁺` and the cap

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof: on idempotents, the comparison map sends the
loading `i ⊔ w ⊔ l` of the three blocks `λ_1…λ_j; μ μ*; λ_{j+1}…λ_ℓ` of `λ⁺` to the cap generator
whose bottom loading is the loading `i ⊔ l` of `λ` at the cut with `w` inserted at the cut
(`insertSeq_cutSeq_lbl`).

## Main definitions

* `Stendhal.CupCap.cutSeq`: the loading `i ⊔ l` of `λ`.
* `Stendhal.CupCap.plusSeq`: the loading `i ⊔ w ⊔ l` of the three blocks of `λ⁺`.

## Main results

* `Stendhal.CupCap.insertSeq_cutSeq_lbl`: the loading of `λ⁺` is `i ⊔ l` with `w` inserted.
* `Stendhal.CupCap.insertSeq_left_injective`: an inserted loading determines the loading of `λ`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

variable {I : Type*} {ℓ j : ℕ} (hj : j ≤ ℓ) {θ γ ν₀ : Multiset I}

/-- **The loading `i ⊔ l` of `λ`** at the cut. -/
def cutSeq (i : Seq (stendhalWeight j θ)) (l : Seq (stendhalWeight (ℓ - j) γ)) :
    Seq (stendhalWeight ℓ (θ + γ)) :=
  castLabelsSeq (Nat.add_sub_of_le hj) (cutInputWeights_add θ γ)
    ((Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) i).append
      (Seq.map (Sum.map (id : I → I) (Fin.natAdd j)) l))

/-- **The loading `i ⊔ w ⊔ l` of the three blocks of `λ⁺`.** -/
def plusSeq (i : Seq (stendhalWeight j θ)) (w : Seq (stendhalWeight 2 ν₀))
    (l : Seq (stendhalWeight (ℓ - j) γ)) :
    Seq (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) (stendhalWeight j θ) +
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)) +
        Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ)))) :=
  (Seq.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) i).append
    ((Seq.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) w)).append
      (Seq.map (Sum.map (id : I → I) (Fin.natAdd j))
        (Seq.map (Sum.map (id : I → I) (Fin.natAdd 2)) l)))

theorem cutSeq_apply_lt (i : Seq (stendhalWeight j θ)) (l : Seq (stendhalWeight (ℓ - j) γ))
    (a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ)))) (v : ℕ) (hv : a.val = v)
    (hvA : v < Multiset.card (stendhalWeight j θ)) :
    (cutSeq hj i l).1 a = Sum.map id (Fin.cast (Nat.add_sub_of_le hj))
      (Sum.map id (Fin.castAdd (ℓ - j)) (i.1 ⟨v, hvA⟩)) := by
  have h := castLabelsSeq_lbl (Nat.add_sub_of_le hj) (cutInputWeights_add θ γ)
    ((Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) i).append
      (Seq.map (Sum.map (id : I → I) (Fin.natAdd j)) l)) a
  refine h.trans (congrArg _ ?_)
  rw [Seq.lbl, Seq.append_apply_lt _ _ _ (by simp; omega)]
  exact congrArg _ (Seq.apply_congr i (by simp; omega))

theorem cutSeq_apply_ge (i : Seq (stendhalWeight j θ)) (l : Seq (stendhalWeight (ℓ - j) γ))
    (a : Fin (Multiset.card (stendhalWeight ℓ (θ + γ)))) (v : ℕ) (hv : a.val = v + Multiset.card
      (stendhalWeight j θ)) :
    (cutSeq hj i l).1 a = Sum.map id (Fin.cast (Nat.add_sub_of_le hj))
      (Sum.map id (Fin.natAdd j) (l.1 ⟨v, by
        have := a.2
        simp only [card_stendhalWeight, Multiset.card_add] at this hv ⊢
        omega⟩)) := by
  have h := castLabelsSeq_lbl (Nat.add_sub_of_le hj) (cutInputWeights_add θ γ)
    ((Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) i).append
      (Seq.map (Sum.map (id : I → I) (Fin.natAdd j)) l)) a
  refine h.trans (congrArg _ ?_)
  rw [Seq.lbl, Seq.append_apply_ge _ _ _ (by simp; omega)]
  exact congrArg _ (Seq.apply_congr l (by simp; omega))

theorem plusSeq_apply_lt (i : Seq (stendhalWeight j θ)) (w : Seq (stendhalWeight 2 ν₀))
    (l : Seq (stendhalWeight (ℓ - j) γ)) (q : Fin _) (v : ℕ) (hv : q.val = v)
    (hvA : v < Multiset.card (stendhalWeight j θ)) :
    (plusSeq i w l).1 q = Sum.map id (Fin.castAdd (2 + (ℓ - j))) (i.1 ⟨v, hvA⟩) := by
  rw [plusSeq, Seq.append_apply_lt _ _ _ (by simp; omega)]
  exact congrArg _ (Seq.apply_congr i (by simp; omega))

theorem plusSeq_apply_mid (i : Seq (stendhalWeight j θ)) (w : Seq (stendhalWeight 2 ν₀))
    (l : Seq (stendhalWeight (ℓ - j) γ)) (q : Fin _) (v : ℕ)
    (hv : q.val = v + Multiset.card (stendhalWeight j θ))
    (hvN : v < Multiset.card (stendhalWeight 2 ν₀)) :
    (plusSeq i w l).1 q = Sum.map id (Fin.natAdd j)
      (Sum.map id (Fin.castAdd (ℓ - j)) (w.1 ⟨v, hvN⟩)) := by
  rw [plusSeq, Seq.append_apply_ge _ _ _ (by simp; omega), Seq.append_apply_lt _ _ _
    (by simp; omega)]
  exact congrArg _ (congrArg _ (Seq.apply_congr w (by simp; omega)))

theorem plusSeq_apply_ge (i : Seq (stendhalWeight j θ)) (w : Seq (stendhalWeight 2 ν₀))
    (l : Seq (stendhalWeight (ℓ - j) γ)) (q : Fin _) (v : ℕ)
    (hv : q.val = v + Multiset.card (stendhalWeight 2 ν₀) + Multiset.card (stendhalWeight j θ))
    (hvl : v < Multiset.card (stendhalWeight (ℓ - j) γ)) :
    (plusSeq i w l).1 q = Sum.map id (Fin.natAdd j)
      (Sum.map id (Fin.natAdd 2) (l.1 ⟨v, hvl⟩)) := by
  rw [plusSeq, Seq.append_apply_ge _ _ _ (by simp; omega), Seq.append_apply_ge _ _ _
    (by simp; omega)]
  exact congrArg _ (congrArg _ (Seq.apply_congr l (by simp; omega)))

theorem plusSeq_head_label (z : I ⊕ Fin j) :
    oldColour j hj
        (Sum.map id (Fin.cast (Nat.add_sub_of_le hj)) (Sum.map id (Fin.castAdd (ℓ - j)) z)) =
      Sum.map id (Fin.cast (plusBlock_card j hj)) (Sum.map id (Fin.castAdd (2 + (ℓ - j))) z) := by
  rcases z with b | r
  · rfl
  · simp [oldRed, Fin.ext_iff, r.2]

theorem plusSeq_mid_label (z : I ⊕ Fin 2) :
    cupColour j hj z =
      Sum.map id (Fin.cast (plusBlock_card j hj))
        (Sum.map id (Fin.natAdd j) (Sum.map id (Fin.castAdd (ℓ - j)) z)) := by
  rcases z with b | r
  · rfl
  · simp [cupRed, Fin.ext_iff]

theorem plusSeq_tail_label (z : I ⊕ Fin (ℓ - j)) :
    oldColour j hj (Sum.map id (Fin.cast (Nat.add_sub_of_le hj)) (Sum.map id (Fin.natAdd j) z)) =
      Sum.map id (Fin.cast (plusBlock_card j hj))
        (Sum.map id (Fin.natAdd j) (Sum.map id (Fin.natAdd 2) z)) := by
  rcases z with b | r
  · rfl
  · simp [oldRed, Fin.ext_iff]
    omega

theorem insertSeq_cutSeq_lbl (i : Seq (stendhalWeight j θ)) (w : Seq (stendhalWeight 2 ν₀))
    (l : Seq (stendhalWeight (ℓ - j) γ)) (hn) (p : Fin (Multiset.card
      (stendhalWeight (ℓ + 2) ((θ + γ) + ν₀))))
    (q : Fin (Multiset.card (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j))))
      (stendhalWeight j θ) +
      (Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) (stendhalWeight 2 ν₀)) +
        Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
          (Multiset.map (Sum.map (id : I → I) (Fin.natAdd 2)) (stendhalWeight (ℓ - j) γ))))))
    (hpq : p.val = q.val) :
    (insertSeq (j := j) (hj := hj) (ν₀ := ν₀) (cutSeq hj i l) (Multiset.card (stendhalWeight j θ))
        hn (Seq.map (cupColour j hj) w)).lbl p =
      Sum.map id (Fin.cast (plusBlock_card j hj)) ((plusSeq i w l).lbl q) := by
  simp only [insertSeq, Seq.lbl, insertPos, Equiv.coe_fn_symm_mk, Function.comp_apply]
  have hA := card_stendhalWeight (ℓ := j) (ν := θ)
  have hN := card_stendhalWeight (ℓ := 2) (ν := ν₀)
  have hL := card_stendhalWeight (ℓ := ℓ - j) (ν := γ)
  have hT := card_stendhalWeight (ℓ := ℓ) (ν := θ + γ)
  have hq := q.2
  simp only [Multiset.card_add, Multiset.card_map] at hq hT
  split_ifs with h h'
  · simp only [Sum.elim_inl, Function.comp_apply]
    simp only [Fin.val_cast] at h
    rw [cutSeq_apply_lt hj i l _ q.val (by simp [hpq]) (by omega),
      plusSeq_apply_lt i w l q q.val rfl (by omega)]
    exact plusSeq_head_label hj _
  · simp only [Sum.elim_inr]
    simp only [Fin.val_cast, Multiset.card_map] at h h'
    rw [plusSeq_apply_mid i w l q (q.val - Multiset.card (stendhalWeight j θ)) (by omega)
      (by omega)]
    rw [← plusSeq_mid_label hj]
    exact congrArg _ (Seq.apply_congr w (by simp; omega))
  · simp only [Sum.elim_inl, Function.comp_apply]
    simp only [Fin.val_cast, Multiset.card_map] at h h'
    rw [cutSeq_apply_ge hj i l _ (q.val - Multiset.card (stendhalWeight 2 ν₀) -
        Multiset.card (stendhalWeight j θ)) (by simp; omega),
      plusSeq_apply_ge i w l q (q.val - Multiset.card (stendhalWeight 2 ν₀) -
        Multiset.card (stendhalWeight j θ)) (by omega) (by omega)]
    exact plusSeq_tail_label hj _

/-- An inserted loading determines the loading of `λ` it was inserted into. -/
theorem insertSeq_left_injective {ν : Multiset I} {s s' : Seq (stendhalWeight ℓ ν)} {n : ℕ}
    {hn : n ≤ Multiset.card (stendhalWeight ℓ ν)}
    {t t' : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))}
    (h : insertSeq (j := j) (hj := hj) s n hn t = insertSeq (j := j) (hj := hj) s' n hn t') :
    s = s' := by
  have key : ∀ a, s.lbl a = s'.lbl a := fun a => by
    apply oldColour_injective j hj
    have := congrArg (fun S => Seq.lbl S
      (Fin.cast (card_plus j hj ν ν₀).symm (insertPos _ _ n hn (.inl a)))) h
    rwa [insertSeq_lbl_old, insertSeq_lbl_old] at this
  exact Subtype.ext (funext key)

end Categorification.Stendhal.CupCap
