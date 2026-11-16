/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.CrawleyBoeveyIn
import Categorification.WeightedKLR.RedStrands.Stendhal
import Categorification.WeightedKLR.KLR.SpacedCrossing

/-!
# Stendhal loadings

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 3.5: the loadings of the Crawley-Boevey graph `Γ_λ` (new edges directed into the new
vertex, of weights `ϖ_1 < ⋯ < ϖ_ℓ`, old edges of weight `0`) attached to Stendhal sequences.

Webster turns the ghosts of the `0`-labelled strand into the red strands of a Stendhal diagram.
Conversely, a sequence `i` of black and red termini of a Stendhal diagram, with red strands in
the order `λ_1, …, λ_ℓ`, gives a loading: the `0`-strand at `0`, so that its ghost for the new
edges of `λ_j` is at `ϖ_j`, and the black strands at increasing points, each lying between the
ghosts `ϖ_j` with the same red strands on its left as in `i`.

We place the black strand at position `p` (among `M` positions, `g` of the red positions being
smaller than `p`) at `stPt ϖ M ρ p`, a point strictly between the `g`-th and `(g + 1)`-st entry of
the sequence `ϖ_1 - 1 < ϖ_1 < ⋯ < ϖ_ℓ < ⋯` (`lowB`). These points increase with `p`, and lie
right of the ghost `ϖ_j` exactly when the `j`-th red position is smaller than `p`
(`ghost_lt_stPt_iff`).

## Main definitions

* `Stendhal.stPt`: the points of the black strands.
* `Stendhal.toTilde`: the strands of a Stendhal sequence as strands of `ν̃ = ν + α_0`, the red
  strands becoming the `0`-strand.
* `Stendhal.stCfg`: the loading of a position function on the strands of a Stendhal sequence.

## Main results

* `Stendhal.stPt_lt_stPt`, `Stendhal.ghost_lt_stPt_iff`.
* `Stendhal.oldWall_pos_iff`, `Stendhal.newWall_pos_iff`, `Stendhal.diag_pos_iff`: the side of
  each hyperplane on which `stCfg` lies.
* `Stendhal.isGeneric_stCfg`.
* `Stendhal.separates_stCfg_swap_black`, `Stendhal.separates_stCfg_swap_red`: the hyperplanes
  crossed by exchanging two neighbouring black strands, or a black and a red strand.
-/

namespace Categorification.Stendhal

open Categorification.WeightedKLR Equiv

section Points

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {ℓ : ℕ}
  (ϖ : Fin ℓ → 𝕜)

/-- The weights `ϖ_j`, continued past `ℓ` by an increasing sequence. -/
def extW (n : ℕ) : 𝕜 :=
  if h : n < ℓ then ϖ ⟨n, h⟩ else (1 + ∑ r, |ϖ r|) + n

variable {ϖ}

omit [IsStrictOrderedRing 𝕜] in
theorem extW_of_lt {n : ℕ} (h : n < ℓ) : extW ϖ n = ϖ ⟨n, h⟩ := by simp [extW, h]

omit [IsStrictOrderedRing 𝕜] in
theorem extW_of_not_lt {n : ℕ} (h : ¬ n < ℓ) : extW ϖ n = (1 + ∑ r, |ϖ r|) + n := by
  simp [extW, h]

omit [IsStrictOrderedRing 𝕜] in
theorem extW_fin (r : Fin ℓ) : extW ϖ r = ϖ r := extW_of_lt r.2

theorem extW_strictMono (hϖ : StrictMono ϖ) : StrictMono (extW ϖ) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  by_cases h1 : n + 1 < ℓ
  · rw [extW_of_lt h1, extW_of_lt (by omega)]
    exact hϖ (Fin.mk_lt_mk.2 (Nat.lt_succ_self n))
  · rw [extW_of_not_lt h1]
    by_cases h0 : n < ℓ
    · rw [extW_of_lt h0]
      have h2 := Finset.single_le_sum (fun r (_ : r ∈ Finset.univ) => abs_nonneg (ϖ r))
        (Finset.mem_univ ⟨n, h0⟩)
      have h3 := le_abs_self (ϖ ⟨n, h0⟩)
      have h4 : (0 : 𝕜) ≤ ((n + 1 : ℕ) : 𝕜) := Nat.cast_nonneg _
      linarith
    · rw [extW_of_not_lt h0]
      push_cast
      linarith

variable (ϖ) in
/-- The bounds of the intervals of black strands: `ϖ_1 - 1, ϖ_1, ϖ_2, …`. -/
def lowB : ℕ → 𝕜
  | 0 => extW ϖ 0 - 1
  | n + 1 => extW ϖ n

theorem lowB_strictMono (hϖ : StrictMono ϖ) : StrictMono (lowB ϖ) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  cases n with
  | zero => show extW ϖ 0 - 1 < extW ϖ 0; linarith
  | succ n => exact extW_strictMono hϖ (Nat.lt_succ_self n)

/-- The number of red positions smaller than `p`. -/
def gap (ρ : Fin ℓ → ℕ) (p : ℕ) : ℕ := (Finset.univ.filter fun r => ρ r < p).card

theorem gap_mono (ρ : Fin ℓ → ℕ) {p p' : ℕ} (h : p ≤ p') : gap ρ p ≤ gap ρ p' :=
  Finset.card_le_card fun r hr => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    omega

theorem succ_le_gap {ρ : Fin ℓ → ℕ} (hρ : StrictMono ρ) {p : ℕ} {r : Fin ℓ} (h : ρ r < p) :
    r.val + 1 ≤ gap ρ p := by
  rw [← Fin.card_Iic]
  refine Finset.card_le_card fun r' hr' => ?_
  simp only [Finset.mem_Iic] at hr'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact lt_of_le_of_lt (hρ.monotone hr') h

theorem gap_le {ρ : Fin ℓ → ℕ} (hρ : StrictMono ρ) {p : ℕ} {r : Fin ℓ} (h : p < ρ r) :
    gap ρ p ≤ r.val := by
  conv_rhs => rw [← Fin.card_Iio r]
  refine Finset.card_le_card fun r' hr' => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr'
  simp only [Finset.mem_Iio]
  exact hρ.lt_iff_lt.1 (by omega)

variable (ϖ) in
/-- The point of the black strand at position `p < M`, when the red strands are at the
positions `ρ`: a point strictly between `lowB (gap ρ p)` and `lowB (gap ρ p + 1)`, increasing
with `p`. -/
def stPt (M : ℕ) (ρ : Fin ℓ → ℕ) (p : ℕ) : 𝕜 :=
  lowB ϖ (gap ρ p) + (lowB ϖ (gap ρ p + 1) - lowB ϖ (gap ρ p)) * ((p + 1) / (M + 1))

theorem frac_pos_lt_one {M p : ℕ} (h : p < M) :
    (0 : 𝕜) < ((p : 𝕜) + 1) / ((M : 𝕜) + 1) ∧ ((p : 𝕜) + 1) / ((M : 𝕜) + 1) < 1 := by
  have hM : (0 : 𝕜) < (M : 𝕜) + 1 := by positivity
  have hp : (p : 𝕜) + 1 < (M : 𝕜) + 1 := by exact_mod_cast Nat.succ_lt_succ h
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hM]
  exact hp

theorem lowB_lt_stPt (hϖ : StrictMono ϖ) {M : ℕ} (ρ : Fin ℓ → ℕ) {p : ℕ} (h : p < M) :
    lowB ϖ (gap ρ p) < stPt ϖ M ρ p := by
  have hd := sub_pos.2 (lowB_strictMono hϖ (Nat.lt_succ_self (gap ρ p)))
  have ht := (frac_pos_lt_one (𝕜 := 𝕜) h).1
  unfold stPt
  nlinarith

theorem stPt_lt_lowB (hϖ : StrictMono ϖ) {M : ℕ} (ρ : Fin ℓ → ℕ) {p : ℕ} (h : p < M) :
    stPt ϖ M ρ p < lowB ϖ (gap ρ p + 1) := by
  have hd := sub_pos.2 (lowB_strictMono hϖ (Nat.lt_succ_self (gap ρ p)))
  have ht := (frac_pos_lt_one (𝕜 := 𝕜) h).2
  unfold stPt
  nlinarith

/-- The points of the black strands increase with their positions. -/
theorem stPt_lt_stPt (hϖ : StrictMono ϖ) {M : ℕ} (ρ : Fin ℓ → ℕ) {p p' : ℕ} (hp : p < p')
    (hp' : p' < M) : stPt ϖ M ρ p < stPt ϖ M ρ p' := by
  have hg := gap_mono ρ hp.le
  rcases hg.lt_or_eq with hg | hg
  · calc stPt ϖ M ρ p < lowB ϖ (gap ρ p + 1) := stPt_lt_lowB hϖ ρ (hp.trans hp')
      _ ≤ lowB ϖ (gap ρ p') := (lowB_strictMono hϖ).monotone hg
      _ < stPt ϖ M ρ p' := lowB_lt_stPt hϖ ρ hp'
  · have hd := sub_pos.2 (lowB_strictMono hϖ (Nat.lt_succ_self (gap ρ p)))
    have hM : (0 : 𝕜) < (M : 𝕜) + 1 := by positivity
    have hpp : ((p : 𝕜) + 1) / ((M : 𝕜) + 1) < ((p' : 𝕜) + 1) / ((M : 𝕜) + 1) := by
      rw [div_lt_div_iff_of_pos_right hM]
      exact_mod_cast Nat.succ_lt_succ hp
    unfold stPt
    rw [← hg]
    nlinarith

theorem stPt_injOn (hϖ : StrictMono ϖ) {M : ℕ} (ρ : Fin ℓ → ℕ) {p p' : ℕ} (hp : p < M)
    (hp' : p' < M) (h : stPt ϖ M ρ p = stPt ϖ M ρ p') : p = p' := by
  rcases lt_trichotomy p p' with hl | rfl | hl
  · exact absurd h (stPt_lt_stPt hϖ ρ hl hp').ne
  · rfl
  · exact absurd h (stPt_lt_stPt hϖ ρ hl hp).ne'

/-- **The ghosts of the `0`-strand are the red strands**: the black strand at position `p`, not
a red position, lies right of `ϖ_j` exactly when the `j`-th red strand is left of it. -/
theorem ghost_lt_stPt_iff (hϖ : StrictMono ϖ) {M : ℕ} {ρ : Fin ℓ → ℕ} (hρ : StrictMono ρ)
    {p : ℕ} (hp : p < M) (hpr : ∀ r, ρ r ≠ p) (r : Fin ℓ) :
    ϖ r < stPt ϖ M ρ p ↔ ρ r < p := by
  constructor
  · intro h
    by_contra h'
    have hlt : p < ρ r := lt_of_le_of_ne (not_lt.1 h') (hpr r).symm
    have hg := gap_le hρ hlt
    have : stPt ϖ M ρ p < ϖ r := by
      calc stPt ϖ M ρ p < lowB ϖ (gap ρ p + 1) := stPt_lt_lowB hϖ ρ hp
        _ ≤ lowB ϖ (r.val + 1) := (lowB_strictMono hϖ).monotone (by omega)
        _ = ϖ r := extW_fin r
    exact absurd h (not_lt.2 this.le)
  · intro h
    calc ϖ r = lowB ϖ (r.val + 1) := (extW_fin r).symm
      _ ≤ lowB ϖ (gap ρ p) := (lowB_strictMono hϖ).monotone (succ_le_gap hρ h)
      _ < stPt ϖ M ρ p := lowB_lt_stPt hϖ ρ hp

end Points

end Categorification.Stendhal
