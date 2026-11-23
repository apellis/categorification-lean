/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.LastStrand
import Categorification.WeightedKLR.RedStrands.BraidedAppendBasis

set_option backward.isDefEq.respectTransparency false

/-!
# Reduced words through the last coset

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1,
proof of Proposition 6.7. Every `w ∈ S_{m₀+1}` factors uniquely as `w = c (τ × 1)` with
`τ ∈ S_{m₀}` and `c` increasing on the first `m₀` positions (`c⁻¹` a shuffle for the blocks
`(m₀, 1)`), and `ℓ(w) = ℓ(c) + ℓ(τ)`. Concatenating a reduced word for `c` with a chosen reduced
word for `τ` gives a choice of reduced words for `S_{m₀+1}`.

## Main definitions and results

* `TypeA.lastCosetSplit` : `w ↦ (c, τ)`.
* `TypeA.lastCosetSplit_mul`, `TypeA.length_lastCosetSplit`, `TypeA.strictMono_lastCosetSplit`,
  `TypeA.lastCosetSplit_eq`.
* `TypeA.lastCosetWord`, `TypeA.isReducedChoice_lastCosetWord`.
-/

namespace Categorification.TypeA

open Equiv

variable {m m₀ : ℕ} (hm : m₀ + 1 = m)

/-- The factorisation `w = c (τ × 1)` with `c⁻¹` a shuffle for the blocks `(m₀, 1)`. -/
noncomputable def lastCosetSplit (w : Perm (Fin m)) : Perm (Fin m) × Perm (Fin m₀) :=
  (((parabolicEquiv hm).symm w⁻¹).2.2.1⁻¹, ((parabolicEquiv hm).symm w⁻¹).1⁻¹)

theorem lastCosetSplit_mul (w : Perm (Fin m)) :
    (lastCosetSplit hm w).1 * extPerm hm (lastCosetSplit hm w).2 = w := by
  set p := (parabolicEquiv hm).symm w⁻¹ with hpd
  have hp : blockPerm hm p.1 1 * p.2.2.1 = w⁻¹ := by
    have := (parabolicEquiv hm).apply_symm_apply w⁻¹
    rw [← hpd, parabolicEquiv_apply, show p.2.1 = 1 from Subsingleton.elim _ _] at this
    exact this
  show p.2.2.1⁻¹ * blockPerm hm p.1⁻¹ 1 = w
  rw [← inv_inj, mul_inv_rev, inv_inv, blockPerm_inv, inv_inv, inv_one, hp]

/-- `c` is increasing on the first block. -/
theorem strictMono_lastCosetSplit (w : Perm (Fin m)) :
    StrictMono fun x : Fin m₀ => (lastCosetSplit hm w).1 (blockEquiv hm (Sum.inl x)) :=
  ((parabolicEquiv hm).symm w⁻¹).2.2.2.1

theorem length_lastCosetSplit (w : Perm (Fin m)) :
    length m w = length m (lastCosetSplit hm w).1 + length m₀ (lastCosetSplit hm w).2 := by
  have hp := (parabolicEquiv hm).apply_symm_apply w⁻¹
  rw [parabolicEquiv_apply] at hp
  have hl := length_blockPerm_mul hm ((parabolicEquiv hm).symm w⁻¹).1
    ((parabolicEquiv hm).symm w⁻¹).2.1 ((parabolicEquiv hm).symm w⁻¹).2.2.2
  rw [hp, length_inv] at hl
  have hb : ((parabolicEquiv hm).symm w⁻¹).2.1 = 1 := Subsingleton.elim _ _
  rw [hb, length_one] at hl
  simp only [lastCosetSplit, length_inv]
  omega

/-- Uniqueness of the factorisation `w = c (τ × 1)`. -/
theorem lastCosetSplit_eq {c : Perm (Fin m)} {τ : Perm (Fin m₀)}
    (hc : StrictMono fun x : Fin m₀ => c (blockEquiv hm (Sum.inl x))) :
    lastCosetSplit hm (c * extPerm hm τ) = (c, τ) := by
  have hu : IsShuffle hm c⁻¹ :=
    ⟨by simpa using hc, fun y y' hy => absurd hy (by simp [Subsingleton.elim y y'])⟩
  have he : (c * extPerm hm τ)⁻¹ = parabolicEquiv hm (τ⁻¹, 1, ⟨c⁻¹, hu⟩) := by
    rw [parabolicEquiv_apply, mul_inv_rev, extPerm, blockPerm_inv, inv_one]
  rw [lastCosetSplit, he, Equiv.symm_apply_apply]
  simp

variable {hm}

/-- Reduced words through the last coset: a reduced word for `c` followed by `ρ τ`. -/
noncomputable def lastCosetWord (hm : m₀ + 1 = m) (ρ : Perm (Fin m₀) → List ℕ)
    (w : Perm (Fin m)) : List ℕ :=
  canWord m (lastCosetSplit hm w).1 ++ ρ (lastCosetSplit hm w).2

theorem wordProd_lastCosetWord {ρ : Perm (Fin m₀) → List ℕ}
    (hρ : ∀ τ, ValidWord m₀ (ρ τ) ∧ wordProd m₀ (ρ τ) = τ) (w : Perm (Fin m)) :
    wordProd m (lastCosetWord hm ρ w) = w := by
  rw [lastCosetWord, wordProd_append, wordProd_canWord, wordProd_eq_blockPerm_left hm (hρ _).1,
    (hρ _).2]
  exact lastCosetSplit_mul hm w

theorem isReducedChoice_lastCosetWord {ρ : Perm (Fin m₀) → List ℕ} (hρ : IsReducedChoice ρ) :
    IsReducedChoice (lastCosetWord hm ρ) := by
  have hρ' : ∀ τ, ValidWord m₀ (ρ τ) ∧ wordProd m₀ (ρ τ) = τ := fun τ => ⟨(hρ τ).1.1, (hρ τ).2⟩
  intro w
  refine ⟨⟨validWord_append.2 ⟨validWord_canWord m _, (hρ _).1.1.of_le (by omega)⟩, ?_⟩,
    wordProd_lastCosetWord hρ' w⟩
  rw [wordProd_lastCosetWord hρ' w, lastCosetWord, List.length_append, length_canWord,
    (hρ _).1.2, (hρ _).2, length_lastCosetSplit hm w]

/-- A permutation increasing on the first block compares positions of the first block as they
are compared. -/
theorem lt_iff_of_strictMono {c : Perm (Fin m)}
    (hc : StrictMono fun x : Fin m₀ => c (blockEquiv hm (Sum.inl x))) {p q : Fin m}
    (hp : p.val < m₀) (hq : q.val < m₀) : c p < c q ↔ p < q := by
  have ep : p = blockEquiv hm (Sum.inl ⟨p.val, hp⟩) := Fin.ext rfl
  have eq : q = blockEquiv hm (Sum.inl ⟨q.val, hq⟩) := Fin.ext rfl
  rw [ep, eq, hc.lt_iff_lt, blockEquiv_inl_lt_inl]

end Categorification.TypeA

namespace Categorification.Stendhal

open KLR TypeA Equiv

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} (i : I) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)

namespace BraidedStendhalAlgebra

omit [DecidableEq I] in
theorem appendCard : Multiset.card μ + 1 = Multiset.card (stendhalWeight ℓ νᵢ) :=
  (card_stendhalWeight_addBlack i ν).symm

omit [DecidableEq I] in
/-- `(τ × 1) • (s i) = (τ • s) i`. -/
theorem extPerm_smul_appendBlackLoading (τ : Perm (Fin (Multiset.card μ))) (s : Seq μ) :
    extPerm (appendCard i ν) τ • appendBlackLoading i ν s =
      appendBlackLoading i ν (τ • s) := by
  apply Subtype.ext
  funext a
  change (appendBlackLoading i ν s).lbl ((extPerm _ τ).symm a) =
    (appendBlackLoading i ν (τ • s)).lbl a
  have hv := extPerm_val (appendCard i ν) τ⁻¹ a
  rw [← Perm.inv_def, extPerm_inv]
  by_cases ha : a.val < Multiset.card μ
  · simp only [ha, ↓reduceDIte] at hv
    rw [appendBlackLoading_lbl_of_lt i ν _ _ (hv ▸ (τ⁻¹ _).isLt),
      appendBlackLoading_lbl_of_lt i ν _ _ ha]
    change s.1 _ = s.1 (τ.symm _)
    exact congrArg s.1 (Fin.ext hv)
  · simp only [ha, ↓reduceDIte] at hv
    have h' : a.val = Multiset.card μ := by
      have := a.isLt; have := card_stendhalWeight_addBlack i ν (ℓ := ℓ); omega
    rw [appendBlackLoading_lbl_of_eq i ν _ _ (hv.trans h'),
      appendBlackLoading_lbl_of_eq i ν _ _ h']

omit [DecidableEq I] in
/-- A permutation increasing on the old strands does not change the red order of `s i`. -/
theorem redWord_smul_appendBlackLoading {c : Perm (Fin (Multiset.card (stendhalWeight ℓ νᵢ)))}
    (hc : StrictMono fun x : Fin (Multiset.card μ) => c (blockEquiv (appendCard i ν) (Sum.inl x)))
    (s : Seq μ) : redWord (c • appendBlackLoading i ν s) = redWord s := by
  rw [← redWord_appendBlackLoading i ν s]
  conv_rhs => rw [← one_smul (Perm (Fin (Multiset.card (stendhalWeight ℓ νᵢ))))
    (appendBlackLoading i ν s)]
  refine (redWord_smul_eq_iff _ c 1).2 fun p q r r' hp hq => ?_
  have hlt : ∀ a : Fin (Multiset.card (stendhalWeight ℓ νᵢ)), ∀ r : Fin ℓ,
      (appendBlackLoading i ν s).lbl a = .inr r → a.val < Multiset.card μ := by
    intro a r ha
    by_contra hn
    have := a.isLt
    have := card_stendhalWeight_addBlack i ν (ℓ := ℓ)
    rw [appendBlackLoading_lbl_of_eq i ν _ _ (by omega)] at ha
    exact Sum.inl_ne_inr ha
  rw [Perm.one_apply, Perm.one_apply]
  exact lt_iff_of_strictMono hc (hlt p r hp) (hlt q r' hq)

end BraidedStendhalAlgebra

end Categorification.Stendhal
