/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutSeq
import Categorification.WeightedKLR.Rigidity.CupCapMidDescent

/-!
# The maximum at the cut for loadings with a good tail

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof of the inverse `Ψ`: the cap generators of the
model `L ⊗ e T̃^{λ⁺}` sit at `midPos`, just before the red strand `λ_{j+1}`. For a loading `i ⊔ l`
at the cut whose tail `l` is neither violated nor out of red order (the tails whose idempotent
survives in `T^{λ_{j+1}…λ_ℓ}`), `λ_{j+1}` is the first strand of `l`, so `midPos` is the cut
`|h|` (`midPos_cutSeq`). Hence an inserted loading at `midPos` equals the loading of `λ⁺` with
block loadings `i`, `w`, `l` exactly when it is inserted into `i ⊔ l` with the window `w`
(`insertSeq_midPos_eq_iff`).

## Main results

* `Stendhal.CupCap.midPos_cutSeq`: the maximum of `i ⊔ l` is at the cut.
* `Stendhal.CupCap.insertSeq_midPos_eq_iff`: inserted loadings at the maximum against the
  loadings with three block loadings.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

variable {I : Type*} [DecidableEq I] {ℓ j : ℕ} (hj : j ≤ ℓ) {θ γ ν₀ : Multiset I}

/-- **The maximum of a loading at the cut with a good tail is the cut.** -/
theorem midPos_cutSeq (i : Seq (stendhalWeight j θ)) {l : Seq (stendhalWeight (ℓ - j) γ)}
    (hl : IsRedOrdered l) (hv : ¬ IsViolated l) :
    midPos j (cutSeq hj i l) = Multiset.card (stendhalWeight j θ) := by
  have hA := card_stendhalWeight (ℓ := j) (ν := θ)
  have hL := card_stendhalWeight (ℓ := ℓ - j) (ν := γ)
  have hT := card_stendhalWeight (ℓ := ℓ) (ν := θ + γ)
  simp only [Multiset.card_add] at hT
  by_cases h : j < ℓ
  · have hpos : 0 < Multiset.card (stendhalWeight (ℓ - j) γ) := by omega
    obtain ⟨r, hr⟩ : ∃ r, l.lbl ⟨0, hpos⟩ = .inr r := by
      rcases hc : l.lbl ⟨0, hpos⟩ with b | r
      · exact absurd ⟨hpos, by rw [hc]; rfl⟩ hv
      · exact ⟨r, rfl⟩
    obtain ⟨b, hb⟩ := exists_lbl_eq_inr l ⟨0, by omega⟩
    have hb0 : b = ⟨0, hpos⟩ := by
      by_contra hne
      have hlt : (⟨0, hpos⟩ : Fin _) < b := by
        rw [Fin.lt_def]
        exact Nat.pos_of_ne_zero fun h0 => hne (Fin.ext h0)
      exact absurd (Fin.lt_def.1 (hl _ _ r _ hlt hr hb)) (Nat.not_lt_zero _)
    subst hb0
    have hr0 : r = ⟨0, by omega⟩ := Sum.inr_injective (hr.symm.trans hb)
    subst hr0
    have hcut : (cutSeq hj i l).lbl ⟨Multiset.card (stendhalWeight j θ), by omega⟩ =
        .inr ⟨j, h⟩ := by
      rw [Seq.lbl, cutSeq_apply_ge hj i l _ 0 (by simp)]
      change Sum.map id (Fin.cast (Nat.add_sub_of_le hj))
        (Sum.map id (Fin.natAdd j) (l.lbl ⟨0, hpos⟩)) = _
      rw [hr]
      simp
    unfold midPos
    rw [dite_eq_left_of_eq_true (eq_true h)]
    exact congrArg Fin.val (lbl_eq_inr_unique (exists_lbl_eq_inr _ ⟨j, h⟩).choose_spec hcut)
  · have hjl : j = ℓ := by omega
    have hγ : Multiset.card γ = 0 := by
      by_contra hne
      have hpos : 0 < Multiset.card (stendhalWeight (ℓ - j) γ) := by omega
      refine hv ⟨hpos, ?_⟩
      rcases hc : l.lbl ⟨0, hpos⟩ with b | r
      · rfl
      · exact absurd r.2 (by omega)
    rw [midPos_of_not_lt j _ h]
    omega

variable {ν₀ : Multiset I}

/-- **An inserted loading at the maximum is the loading with block loadings `i`, `w`, `l`
exactly when it is the window `w` inserted into `i ⊔ l`**, for a good tail `l`. -/
theorem insertSeq_midPos_eq_iff (s : Seq (stendhalWeight ℓ (θ + γ)))
    (t : Seq (stendhalWeight 2 ν₀)) (i : Seq (stendhalWeight j θ))
    (w : Seq (stendhalWeight 2 ν₀)) {l : Seq (stendhalWeight (ℓ - j) γ)}
    (hl : IsRedOrdered l) (hv : ¬ IsViolated l) (hn) :
    insertSeq (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s)
        (Seq.map (cupColour j hj) t) =
      insertSeq (j := j) (hj := hj) (ν₀ := ν₀) (cutSeq hj i l)
        (Multiset.card (stendhalWeight j θ)) hn (Seq.map (cupColour j hj) w) ↔
      s = cutSeq hj i l ∧ t = w := by
  have hm := midPos_cutSeq hj i hl hv
  have hrw : insertSeq (j := j) (hj := hj) (ν₀ := ν₀) (cutSeq hj i l)
      (Multiset.card (stendhalWeight j θ)) hn (Seq.map (cupColour j hj) w) =
      insertSeq (j := j) (hj := hj) (ν₀ := ν₀) (cutSeq hj i l) (midPos j (cutSeq hj i l))
        (midPos_le j _) (Seq.map (cupColour j hj) w) := by
    congr 1
    exact hm.symm
  rw [hrw]
  constructor
  · intro h
    have hs : s = cutSeq hj i l := by
      by_contra hne
      refine Finset.disjoint_left.1 (disjoint_insertSet_midPos (j := j) (hj := hj)
        (ν₀ := ν₀) hne) (Finset.mem_image_of_mem _ (Finset.mem_univ (Seq.map (cupColour j hj) t)))
        ?_
      rw [h]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    subst hs
    exact ⟨rfl, (Seq.mapEquiv (cupColour_injective j hj) _).injective
      (insertSeq_injective _ _ h)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end Categorification.Stendhal.CupCap
