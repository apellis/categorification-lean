/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedRelabel
import Categorification.WeightedKLR.RedStrands.BraidedAppendViolated

set_option backward.isDefEq.respectTransparency false

/-!
# Relabelling the red strands commutes with appending a black strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1. The
functors `𝔈_i` on the corner of red order `κ` are induction along the map adding a black strand
at the right. Relabelling the red strands along a permutation `σ` (`redPermAlgEquiv`) only
changes the labels of red strands, so it commutes with adding a black strand. Together with
`violCornerRedPermTensorEquiv`, this identifies `𝔈_i` at every red order with `𝔈_i` on the
tensor product algebra of the reordered sequence.

## Main results

* `Seq.redPerm_appendBlackLoading`: relabelling commutes with appending a black label.
* `BraidedStendhalAlgebra.redPermAlgEquiv_appendIdem`: relabelling preserves the idempotent of
  diagrams ending in a black strand.
* `BraidedStendhalAlgebra.redPermAlgEquiv_appendBlackAlg`: relabelling commutes with appending
  a black strand, and `violRedPermEquiv_appendViol` the same on the violated quotients.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra Equiv

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ Λ' : Fin ℓ → I →₀ ℕ} (i : I) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)

omit [DecidableEq I] in
theorem Seq.redPerm_appendBlackLoading (σ : Perm (Fin ℓ)) (s : Seq μ) :
    Seq.redPerm σ (appendBlackLoading i ν s) = appendBlackLoading i ν (Seq.redPerm σ s) := by
  apply Subtype.ext
  funext a
  change Sum.map id σ ((appendBlackLoading i ν s).lbl a) =
    (appendBlackLoading i ν (Seq.redPerm σ s)).lbl a
  by_cases ha : a.val < Multiset.card μ
  · rw [appendBlackLoading_lbl_of_lt i ν _ _ ha, appendBlackLoading_lbl_of_lt i ν _ _ ha]
    rfl
  · have hlt : a.val < Multiset.card μ + 1 :=
      (BraidedStendhalAlgebra.card_stendhalWeight_addBlack i ν) ▸ a.isLt
    have hae : a.val = Multiset.card μ := by omega
    rw [appendBlackLoading_lbl_of_eq i ν _ _ hae, appendBlackLoading_lbl_of_eq i ν _ _ hae]
    rfl

namespace BraidedStendhalAlgebra

variable (σ : Perm (Fin ℓ)) (h : ∀ r, Λ' r = Λ (σ r))

theorem redPermAlgEquiv_x (a : Fin (Multiset.card μ)) :
    redPermAlgEquiv σ h (ofKLR k Q Λ' ν (KLRAlgebra.x a)) = ofKLR k Q Λ ν (KLRAlgebra.x a) := by
  rw [redPermAlgEquiv, relabelAlgEquiv_ofKLR, KLRAlgebra.relabelHom_x]
  rfl

theorem redPermAlgEquiv_ψ (j : ℕ) :
    redPermAlgEquiv σ h (ofKLR k Q Λ' ν (KLRAlgebra.ψ j)) = ofKLR k Q Λ ν (KLRAlgebra.ψ j) := by
  rw [redPermAlgEquiv, relabelAlgEquiv_ofKLR, KLRAlgebra.relabelHom_ψ]

/-- Relabelling the red strands preserves the idempotent of diagrams ending in a black strand
coloured `i`. -/
theorem redPermAlgEquiv_appendIdem :
    redPermAlgEquiv (ν := νᵢ) σ h (appendIdem Q Λ' i ν) = appendIdem Q Λ i ν := by
  rw [appendIdem_eq_sum, appendIdem_eq_sum, map_sum]
  refine Fintype.sum_equiv (Seq.redPermEquiv σ) _ _ fun s => ?_
  rw [redPermAlgEquiv_e, Seq.redPerm_appendBlackLoading]
  rfl

/-- **Relabelling the red strands commutes with appending a black strand**
(arXiv:1309.3796v2, §6.1). -/
theorem redPermAlgEquiv_appendBlackAlg (z : BraidedStendhalAlgebra k Q Λ' ν) :
    redPermAlgEquiv (ν := νᵢ) σ h (appendBlackAlg Q Λ' i ν z) =
      appendBlackAlg Q Λ i ν (redPermAlgEquiv σ h z) := by
  obtain ⟨u, rfl⟩ := ofKLR_surjective (k := k) (Q := Q) (Λ := Λ') (ν := ν) z
  obtain ⟨u, rfl⟩ := KLRAlgebra.mk_surjective u
  induction u using FreeAlgebra.induction with
  | grade0 c =>
    have hc : (KLRAlgebra.mk k (stendhalQ Q Λ') μ) (algebraMap k _ c) =
        ∑ s, c • KLRAlgebra.e s := by
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, ← KLRAlgebra.sum_e, Finset.smul_sum]
    rw [hc, map_sum, map_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [map_smul, appendBlackAlg_apply, appendBlackValue_e, redPermAlgEquiv_e,
      Seq.redPerm_appendBlackLoading]
  | grade1 g =>
    rcases g with s | a | j
    · change redPermAlgEquiv σ h (appendBlackValue Q Λ' i ν (ofKLR k Q Λ' ν (e s))) =
        appendBlackValue Q Λ i ν (redPermAlgEquiv σ h (ofKLR k Q Λ' ν (e s)))
      rw [appendBlackValue_e, redPermAlgEquiv_e, redPermAlgEquiv_e, appendBlackValue_e,
        Seq.redPerm_appendBlackLoading]
    · change redPermAlgEquiv σ h (appendBlackValue Q Λ' i ν (ofKLR k Q Λ' ν (x a))) =
        appendBlackValue Q Λ i ν (redPermAlgEquiv σ h (ofKLR k Q Λ' ν (x a)))
      rw [appendBlackValue_apply, appendBlack_ofKLR_x, redPermAlgEquiv_x, appendBlackValue_apply,
        appendBlack_ofKLR_x, map_mul, redPermAlgEquiv_x, redPermAlgEquiv_appendIdem]
    · change redPermAlgEquiv σ h (appendBlackValue Q Λ' i ν (ofKLR k Q Λ' ν (ψ j))) =
        appendBlackValue Q Λ i ν (redPermAlgEquiv σ h (ofKLR k Q Λ' ν (ψ j)))
      rw [redPermAlgEquiv_ψ]
      by_cases hj : j + 1 < Multiset.card μ
      · rw [appendBlackValue_apply, appendBlack_ofKLR_ψ Q Λ' i ν hj, appendBlackValue_apply,
          appendBlack_ofKLR_ψ Q Λ i ν hj, map_mul, redPermAlgEquiv_ψ, redPermAlgEquiv_appendIdem]
      · rw [KLRAlgebra.ψ_eq_zero j (by omega), map_zero, map_zero, map_zero,
          KLRAlgebra.ψ_eq_zero j (by omega), map_zero, map_zero]
  | add a b ha hb =>
    simp only [map_add] at ha hb ⊢
    rw [ha, hb]
  | mul a b ha hb =>
    simp only [map_mul] at ha hb ⊢
    rw [ha, hb]

end BraidedStendhalAlgebra

namespace BraidedStendhalAlgebra

variable {I₀ : Type} [DecidableEq I₀] {Q₀ : I₀ → I₀ → MvPolynomial (Fin 2) k}
  {Λ₀ Λ₀' : Fin ℓ → I₀ →₀ ℕ} (i₀ : I₀) (ν₀ : Multiset I₀) (σ : Perm (Fin ℓ))
  (h₀ : ∀ r, Λ₀' r = Λ₀ (σ r))

/-- Relabelling the red strands commutes with appending a black strand on the quotients by
violated idempotents. -/
theorem violRedPermEquiv_appendViol (z : ViolQuotient k Q₀ Λ₀' ν₀) :
    violRedPermEquiv (ν := {i₀} + ν₀) σ h₀ (appendViol Q₀ Λ₀' i₀ ν₀ z) =
      appendViol Q₀ Λ₀ i₀ ν₀ (violRedPermEquiv σ h₀ z) := by
  obtain ⟨z, rfl⟩ := violMk_surjective z
  rw [appendViol_violMk, violRedPermEquiv_violMk, violRedPermEquiv_violMk, appendViol_violMk,
    redPermAlgEquiv_appendBlackAlg]

end BraidedStendhalAlgebra

end Categorification.Stendhal
