/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OneBlackRetainedOrder
import Categorification.WeightedKLR.RedStrands.HigherKernelCrossingAt
import Categorification.WeightedKLR.RedStrands.TerminalSpectatorCuts

/-!
# Higher crossings for one black

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
A strict retained step across one red gives a surjection onto the loading kernel.
-/


namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR Equiv

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} {i : I}
local notation "μ" => stendhalWeight ℓ (Singleton.singleton i : Multiset I)
local notation "n" => Multiset.card μ

/-- When a red is immediately left of the unique black, any strictly higher
retained loading has the black before that red. Thus the permutation to the
original loading has the prescribed left descent. -/
theorem oneBlack_leftDescent_of_higher
    {a b r : Fin ℓ} {s w : Seq μ} {L M : List (Fin ℓ)}
    (hs : redWord s = L ++ a :: b :: M) (ho : redWord w = redWord s)
    (j : ℕ) (hj : j + 1 < n)
    (hr : s.lbl ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩ = .inr r)
    (hb : s.lbl ⟨j + 1, hj⟩ = .inl i)
    (hlt : adjacentBlockRoot a b s < adjacentBlockRoot a b w)
    (v : Perm (Fin n)) (hv : v • w = s) :
    v⁻¹ ⟨j + 1, hj⟩ < v⁻¹ ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩ := by
  let redPosition : Fin n := ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩
  let blackPosition : Fin n := ⟨j + 1, hj⟩
  have hlabel (q : Fin n) : w.lbl (v⁻¹ q) = s.lbl q :=
    congrArg (fun t : Seq μ => t.lbl q) hv
  have hbw : w.lbl (v⁻¹ blackPosition) = .inl i := (hlabel _).trans hb
  obtain ⟨_, r', ps, pt, _, hps, hpt, hsep, hp⟩ :=
    (adjacentBlockRoot_oneBlack_lt_iff hs (ho.trans hs) blackPosition
      (v⁻¹ blackPosition) hb hbw).1 hlt
  have hps_lt : ps < blackPosition := by
    refine lt_of_le_of_ne hsep ?_
    rintro rfl
    have h := hps.symm.trans hb
    cases h
  have hps_le : ps ≤ redPosition := by
    change ps.val ≤ j
    exact Nat.lt_succ_iff.mp hps_lt
  have hpt_eq : pt = v⁻¹ ps :=
    lbl_inj_of_inr w r' hpt ((hlabel ps).trans hps)
  rw [hpt_eq] at hp
  rcases eq_or_lt_of_le hps_le with hsame | hstrict
  · simpa only [hsame] using hp
  · have hinv : v⁻¹ • s = w := by rw [← hv, inv_smul_smul]
    have hw : redWord (v⁻¹ • s) = redWord ((1 : Perm (Fin n)) • s) := by
      rw [hinv, one_smul, ho]
    have horder := (redWord_smul_eq_iff s v⁻¹ 1).1 hw _ _ _ _ hps hr
    exact hp.trans (horder.2 hstrict)

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {i : I}
local notation "μ" => stendhalWeight ℓ (Singleton.singleton i : Multiset I)
local notation "n" => Multiset.card μ

/-- The crossing of the unique black to the left across an adjacent red
surjects onto the retained kernel when the new loading is strictly higher. -/
theorem crossingIntoKernelMap_oneBlack_surjective
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    {a b r : Fin ℓ} {s t : Seq μ} {L M : List (Fin ℓ)}
    (hs : redWord s = L ++ a :: b :: M) (ho : redWord t = redWord s)
    (hstrict : adjacentBlockRoot a b s < adjacentBlockRoot a b t)
    (j : ℕ) (hj : j + 1 < n) (hstep : TypeA.sadj n j • s = t)
    (hr : s.lbl ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩ = .inr r)
    (hb : s.lbl ⟨j + 1, hj⟩ = .inl i) :
    Function.Surjective (crossingIntoKernelMap Q Λ a b ho hstrict j) := by
  have hswap : TypeA.sadj n j • t = s := by rw [← hstep, sadj_smul_smul]
  apply crossingIntoKernelMap_surjective_of_factors Q Λ a b ho hstrict j hswap
  intro w hw hlt _ z
  have h := cut_factors_of_leftDescent j hj s w z
    (oneBlack_leftDescent_of_higher hs hw j hj hr hb hlt)
  rw [hstep] at h
  exact h

end Categorification.Stendhal.BraidedStendhalAlgebra
