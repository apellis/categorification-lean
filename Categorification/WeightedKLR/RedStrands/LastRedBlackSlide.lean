/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AddRedInjective
import Categorification.WeightedKLR.RedStrands.BlackInduction

/-!
# Sliding a black strand past the last red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6,
Proposition 4.32. Appending the last red strand `λ_ℓ` and then a black strand `i` on the far
right gives the loadings `(s, i, λ_ℓ)`, while appending them in the other order gives
`(s, λ_ℓ, i)`. The two loadings differ by the crossing `ψ` of the last two strands. This file
records the loading combinatorics and the slide of a diagram through that crossing.

## Main results

* `swap_blackRedLoading`: the crossing of the last two strands exchanges the loadings.
* `slide_crossing`: a diagram on the old strands slides through the crossing of the last
  black strand with the last red strand.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv

variable {I : Type} {ℓ : ℕ}

section Loadings

variable (i : I) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "μ'" => stendhalWeight (ℓ + 1) νᵢ
local notation "N₀" => Multiset.card (stendhalWeight ℓ ν)

theorem card_stendhalWeight_append :
    Multiset.card μ' = N₀ + 2 := by
  simp [stendhalWeight]
  omega

/-- The loading `(s, i, λ_ℓ)`: append the black strand, then the last red strand. -/
def blackRedLoading (s : Seq μ) : Seq μ' :=
  appendRedLoading (appendBlackLoading i ν s)

/-- The loading `(s, λ_ℓ, i)`: append the last red strand, then the black strand. -/
def redBlackLoading (s : Seq μ) : Seq μ' :=
  appendBlackLoading (ℓ := ℓ + 1) i ν (appendRedLoading s)

variable {i ν}

theorem blackRedLoading_lbl_of_lt (s : Seq μ) (a : Fin (Multiset.card μ'))
    (ha : a.val < N₀) : (blackRedLoading i ν s).lbl a = addRedColor ℓ (s.lbl ⟨a.val, ha⟩) := by
  have hb : a.val < Multiset.card (stendhalWeight ℓ νᵢ) := by
    simp [stendhalWeight] at ha ⊢; omega
  have h := appendRedLoading_lbl (appendBlackLoading i ν s) ⟨a.val, hb⟩
  rw [appendBlackLoading_lbl_of_lt i ν s _ ha] at h
  exact h

theorem blackRedLoading_lbl_of_eq (s : Seq μ) (a : Fin (Multiset.card μ'))
    (ha : a.val = N₀) : (blackRedLoading i ν s).lbl a = .inl i := by
  have hb : a.val < Multiset.card (stendhalWeight ℓ νᵢ) := by
    simp [stendhalWeight] at ha ⊢; omega
  have h := appendRedLoading_lbl (appendBlackLoading i ν s) ⟨a.val, hb⟩
  rw [appendBlackLoading_lbl_of_eq i ν s _ ha] at h
  exact h

theorem blackRedLoading_lbl_of_last (s : Seq μ) (a : Fin (Multiset.card μ'))
    (ha : a.val = N₀ + 1) : (blackRedLoading i ν s).lbl a = .inr (Fin.last ℓ) := by
  have h := hasLastRed_appendRedLoading (appendBlackLoading i ν s)
  rw [HasLastRed, show lastRedPosition ℓ νᵢ = a from Fin.ext (by
    simp [lastRedPosition, ha, stendhalWeight]; omega)] at h
  exact h

theorem redBlackLoading_lbl_of_lt (s : Seq μ) (a : Fin (Multiset.card μ'))
    (ha : a.val < N₀) : (redBlackLoading i ν s).lbl a = addRedColor ℓ (s.lbl ⟨a.val, ha⟩) := by
  have hb : a.val < Multiset.card (stendhalWeight (ℓ + 1) ν) := by
    simp [stendhalWeight] at ha ⊢; omega
  rw [redBlackLoading, appendBlackLoading_lbl_of_lt (ℓ := ℓ + 1) i ν _ _ hb,
    show (⟨a.val, hb⟩ : Fin _) = appendRedPosition ⟨a.val, ha⟩ from Fin.ext rfl,
    appendRedLoading_lbl]

theorem redBlackLoading_lbl_of_eq (s : Seq μ) (a : Fin (Multiset.card μ'))
    (ha : a.val = N₀) : (redBlackLoading i ν s).lbl a = .inr (Fin.last ℓ) := by
  have hb : a.val < Multiset.card (stendhalWeight (ℓ + 1) ν) := by
    simp [stendhalWeight] at ha ⊢; omega
  rw [redBlackLoading, appendBlackLoading_lbl_of_lt (ℓ := ℓ + 1) i ν _ _ hb]
  have h := hasLastRed_appendRedLoading s
  rwa [HasLastRed, show lastRedPosition ℓ ν = ⟨a.val, hb⟩ from Fin.ext (by
    simp [lastRedPosition, ha, stendhalWeight])] at h

theorem redBlackLoading_lbl_of_last (s : Seq μ) (a : Fin (Multiset.card μ'))
    (ha : a.val = N₀ + 1) : (redBlackLoading i ν s).lbl a = .inl i := by
  rw [redBlackLoading]
  exact appendBlackLoading_lbl_of_eq (ℓ := ℓ + 1) i ν _ _ (by
    simp [stendhalWeight] at ha ⊢; omega)

/-- The crossing of the last two strands exchanges `(s, i, λ_ℓ)` and `(s, λ_ℓ, i)`. -/
theorem swap_blackRedLoading (s : Seq μ) :
    sadj (Multiset.card μ') N₀ • blackRedLoading i ν s = redBlackLoading i ν s := by
  have hN : N₀ + 1 < Multiset.card μ' := by rw [card_stendhalWeight_append]; omega
  apply Subtype.ext
  funext a
  change (blackRedLoading i ν s).lbl ((sadj (Multiset.card μ') N₀).symm a) =
    (redBlackLoading i ν s).lbl a
  rw [show (sadj (Multiset.card μ') N₀).symm = sadj (Multiset.card μ') N₀ from
    TypeA.sadj_inv _ _]
  rcases lt_trichotomy a.val N₀ with h | h | h
  · rw [sadj_apply_of_ne a (by omega) (by omega), blackRedLoading_lbl_of_lt s a h,
      redBlackLoading_lbl_of_lt s a h]
  · rw [show a = ⟨N₀, by omega⟩ from Fin.ext h, sadj_apply_left hN,
      blackRedLoading_lbl_of_last s _ rfl, redBlackLoading_lbl_of_eq s _ rfl]
  · have h' : a.val = N₀ + 1 := by
      have := a.isLt
      have hc := card_stendhalWeight_append (ℓ := ℓ) i ν
      omega
    rw [show a = ⟨N₀ + 1, hN⟩ from Fin.ext h', sadj_apply_right hN,
      blackRedLoading_lbl_of_eq s _ rfl, redBlackLoading_lbl_of_last s _ rfl]

/-- The crossing of the last two strands exchanges `(s, λ_ℓ, i)` and `(s, i, λ_ℓ)`. -/
theorem swap_redBlackLoading (s : Seq μ) :
    sadj (Multiset.card μ') N₀ • redBlackLoading i ν s = blackRedLoading i ν s := by
  rw [← swap_blackRedLoading, smul_smul, TypeA.sadj_mul_self, one_smul]

theorem blackRedLoading_injective : Function.Injective (blackRedLoading (ℓ := ℓ) i ν) := by
  intro s t h
  apply Subtype.ext
  funext a
  have ha : a.val < Multiset.card (stendhalWeight (ℓ + 1) νᵢ) := by
    rw [card_stendhalWeight_append]; omega
  have := congrArg (fun u => u.lbl ⟨a.val, ha⟩) h
  have hs := blackRedLoading_lbl_of_lt (i := i) s ⟨a.val, ha⟩ a.isLt
  have ht := blackRedLoading_lbl_of_lt (i := i) t ⟨a.val, ha⟩ a.isLt
  exact addRedColor_injective ℓ (hs.symm.trans (this.trans ht))

theorem redBlackLoading_injective : Function.Injective (redBlackLoading (ℓ := ℓ) i ν) := by
  intro s t h
  apply blackRedLoading_injective
  rw [← swap_redBlackLoading, h, swap_redBlackLoading]

end Loadings

end Categorification.Stendhal
