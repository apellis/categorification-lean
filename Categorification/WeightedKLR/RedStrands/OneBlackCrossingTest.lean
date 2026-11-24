/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AppendRedCrossingSuffix
import Categorification.WeightedKLR.RedStrands.BraidedFactorization
import Categorification.WeightedKLR.RedStrands.BraidedIdentity
import Categorification.WeightedKLR.RedStrands.LastRedBlackSlide
import Categorification.WeightedKLR.RedStrands.TensorHomInduction

/-!
# The ordinary crossing test at one black

Webster, arXiv:1309.3796v2, Lemma 5.23 and the proof of Lemma 6.8 at (6.21).
Peeling off an uncrossed final red reduces the crossing test to the rightmost
red-black crossing in the shorter loading.
-/
namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA

variable {I : Type} {ℓ : ℕ} {ν : Multiset I}
local notation "n" => Multiset.card (stendhalWeight ℓ ν)
local notation "m" => Multiset.card (stendhalWeight (ℓ + 1) ν)

/-- An adjacent swap of two old strands commutes with appending a terminal red. -/
theorem sadj_appendRedLoading {j : ℕ} (hj : j + 1 < n) (s : Seq (stendhalWeight ℓ ν)) :
    sadj m j • appendRedLoading s = appendRedLoading (sadj n j • s) := by
  have hm : j + 1 < m := hj.trans_le (by simp [stendhalWeight])
  have happ (a : Fin n) :
      sadj m j (appendRedPosition a) = appendRedPosition (sadj n j a) := by
    by_cases h : a.val = j
    · rw [show a = ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩ from Fin.ext h]
      rw [sadj_apply_left hj]
      rw [show appendRedPosition (⟨j, lt_trans (Nat.lt_succ_self _) hj⟩ : Fin n) =
        ⟨j, lt_trans (Nat.lt_succ_self _) hm⟩ from rfl, sadj_apply_left hm]
      rfl
    · by_cases h' : a.val = j + 1
      · rw [show a = ⟨j + 1, hj⟩ from Fin.ext h', sadj_apply_right hj]
        rw [show appendRedPosition (⟨j + 1, hj⟩ : Fin n) = ⟨j + 1, hm⟩ from rfl,
          sadj_apply_right hm]
        rfl
      · exact (sadj_apply_of_ne (appendRedPosition a) h h').trans
          (congrArg appendRedPosition (sadj_apply_of_ne a h h')).symm
  apply Subtype.ext
  funext a
  change (sadj m j • appendRedLoading s).1 a = (appendRedLoading (sadj n j • s)).lbl a
  rw [sadj_smul_apply]
  change (appendRedLoading s).lbl (sadj m j a) = (appendRedLoading (sadj n j • s)).lbl a
  rcases eq_lastRedPosition_or a with rfl | ⟨p, rfl⟩
  · rw [sadj_apply_of_ne _ (by
        simp [lastRedPosition, stendhalWeight] at hj ⊢; omega)
      (by simp [lastRedPosition, stendhalWeight] at hj ⊢; omega)]
    exact (hasLastRed_appendRedLoading s).trans (hasLastRed_appendRedLoading _).symm
  · rw [happ, appendRedLoading_lbl, appendRedLoading_lbl]
    exact congrArg (addRedColor ℓ) (KLRAlgebra.sadj_smul_apply j s p).symm

end Categorification.Stendhal

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA

variable {I : Type} {ℓ : ℕ} {i : I}
local notation "v" => (Singleton.singleton i : Multiset I)
local notation "n" => Multiset.card (stendhalWeight ℓ v)
local notation "m" => Multiset.card (stendhalWeight (ℓ + 1) v)

/-- A terminal red in a red-ordered loading has maximal red label. -/
private theorem hasLastRed_of_inr (s : Seq (stendhalWeight (ℓ + 1) v)) (hs : IsRedOrdered s)
    {r : Fin (ℓ + 1)} (hr : s.lbl (lastRedPosition ℓ v) = .inr r) : HasLastRed s := by
  obtain ⟨p, hp⟩ := exists_lbl_eq_inr s (Fin.last ℓ)
  have heq : p = lastRedPosition ℓ v := by
    by_contra hne
    have hlt : p < lastRedPosition ℓ v := by
      have hval := p.isLt
      have hneq : p.val ≠ (lastRedPosition ℓ v).val := fun hv => hne (Fin.ext hv)
      change p.val < Multiset.card v + ℓ
      change p.val ≠ Multiset.card v + ℓ at hneq
      have hcard : Multiset.card (stendhalWeight (ℓ + 1) v) = ℓ + 1 + 1 := by
        simp [stendhalWeight]
      have hval' := Nat.lt_of_lt_of_eq hval hcard
      simp only [Multiset.card_singleton] at hneq ⊢
      omega
    exact (not_lt_of_ge (Fin.le_last r)) (hs p _ _ _ hlt hp hr)
  change s.lbl (lastRedPosition ℓ v) = _
  rwa [← heq]

/-- If the black has a strand to its right, the last red can be peeled from
both loadings around a crossing at the black's left. -/
theorem oneBlack_crossing_peelLastRed {j : ℕ} (hj : j + 1 < n)
    (s : Seq (stendhalWeight (ℓ + 1) v)) (hs : IsRedOrdered s)
    (hb : s.lbl ⟨j + 1, hj.trans_le (by simp [stendhalWeight])⟩ = .inl i) :
    ∃ u : Seq (stendhalWeight ℓ v), IsRedOrdered u ∧
      appendRedLoading u = s ∧ appendRedLoading (sadj n j • u) = sadj m j • s := by
  have hlast : HasLastRed s := by
    cases h : s.lbl (lastRedPosition ℓ v) with
    | inr r => exact hasLastRed_of_inr s hs h
    | inl c =>
      exfalso
      have hc : c = i := by
        have hmem := Seq.mem s (lastRedPosition ℓ v)
        change s.lbl (lastRedPosition ℓ v) ∈ _ at hmem
        rw [h] at hmem
        simpa [stendhalWeight] using hmem
      subst c
      have hinj : Function.Injective s.lbl := by
        have hn : (Finset.univ.val.map s.lbl).Nodup := by
          rw [show Finset.univ.val.map s.lbl = _ from s.2]
          simp [stendhalWeight, List.nodup_ofFn]
          exact Sum.inr_injective.comp (Fin.succ_injective _)
        exact fun j l e => Multiset.inj_on_of_nodup_map hn j (by simp) l (by simp) e
      have he := congrArg Fin.val (hinj (h.trans hb.symm))
      change Multiset.card v + ℓ = j + 1 at he
      have hcard : n = ℓ + 1 := by simp [stendhalWeight]
      rw [hcard] at hj
      simp only [Multiset.card_singleton] at he
      omega
  obtain ⟨u, hu⟩ := (appendRedOrderedEquiv (ℓ := ℓ) (ν := (Singleton.singleton i : Multiset I))).surjective ⟨s, hs, hlast⟩
  have he : appendRedLoading u.1 = s := congrArg Subtype.val hu
  exact ⟨u.1, u.2, he, (sadj_appendRedLoading hj u.1).symm.trans (congrArg (sadj m j • ·) he)⟩

end Categorification.Stendhal

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open FirstWeight

variable {I : Type} {ℓ : ℕ} {i : I}
local notation "ν₁" => (Singleton.singleton i : Multiset I)
local notation "m" => Multiset.card (stendhalWeight (ℓ + 1) ν₁)

/-- When the black is terminal, the exact crossing pair comes from a red-only prefix. -/
theorem oneBlack_terminalCrossing_is_rightmost {j : ℕ}
    (hj : j + 1 < m) (hterm : j + 2 = m)
    (s : Seq (stendhalWeight (ℓ + 1) ν₁)) (hs : IsRedOrdered s)
    (hb : s.lbl ⟨j + 1, hj⟩ = .inl i) :
    ∃ u : Seq (stendhalWeight ℓ (0 : Multiset I)), IsRedOrdered u ∧
      j = (stendhalWeight ℓ (0 : Multiset I)).card ∧
      s = redBlackLoading i 0 u ∧ sadj m j • s = blackRedLoading i 0 u := by
  have hm : j = ℓ := by simp [stendhalWeight] at hterm; omega
  have hx : s.lbl (terminalPos (ℓ := ℓ + 1) (ν := ({i} + (0 : Multiset I)))
      (by simp)) = .inl i := by
    have hpos : terminalPos (ℓ := ℓ + 1) (ν := ({i} + (0 : Multiset I))) (by simp) =
        ⟨j + 1, hj⟩ := Fin.ext (by
          change m - 1 = j + 1
          omega)
    rwa [hpos]
  obtain ⟨v, hv, hvs⟩ := exists_appendBlack_terminal (β := (0 : Multiset I)) s hx hs
  have hlast : HasLastRed v := by
    cases hvlast : v.lbl (lastRedPosition ℓ (0 : Multiset I)) with
    | inr r => exact terminal_red_last v hv r hvlast
    | inl c =>
      have hmem := Seq.mem v (lastRedPosition ℓ (0 : Multiset I))
      change v.lbl _ ∈ _ at hmem
      rw [hvlast] at hmem
      simp [stendhalWeight] at hmem
  obtain ⟨u, hu⟩ :=
    (appendRedOrderedEquiv (ℓ := ℓ) (ν := (0 : Multiset I))).surjective ⟨v, hv, hlast⟩
  have he : appendRedLoading u.1 = v := congrArg Subtype.val hu
  have hj' : j = (stendhalWeight ℓ (0 : Multiset I)).card := by simpa [stendhalWeight] using hm
  have hsource : s = redBlackLoading i 0 u.1 := hvs.symm.trans (congrArg (appendBlackLoading i 0) he.symm)
  refine ⟨u.1, u.2, hj', hsource, ?_⟩
  rw [hsource, hj']
  exact swap_redBlackLoading u.1

end Categorification.Stendhal

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA

variable {I k : Type} [DecidableEq I] [Field k] {i : I}
local notation "ν" => (Singleton.singleton i : Multiset I)
local notation "W" => fun ℓ => stendhalWeight ℓ ν

/-- Right multiplication by the reverse crossing is injective for a unique black
whenever the right-edge crossing test and red-suffix transport hold. -/
private theorem oneBlack_crossing_injective_of_base (Q : I → I → MvPolynomial (Fin 2) k)
    (hQ : KLRSymm Q)
    (base : ∀ {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)
      (u : Seq (stendhalWeight ℓ (0 : Multiset I))), IsRedOrdered u →
        ∀ x : TensorProductAlgebra k Q Λ ν,
          x * tensorOfKLR Q Λ ν (e (blackRedLoading i 0 u)) = x →
          x * tensorOfKLR Q Λ ν (ψ (stendhalWeight ℓ (0 : Multiset I)).card *
            e (redBlackLoading i 0 u)) = 0 → x = 0)
    {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (s : Seq (W ℓ)) (hs : IsRedOrdered s) (j : ℕ) (hj : j + 1 < (W ℓ).card)
    (hb : s.lbl ⟨j + 1, hj⟩ = .inl i)
    (x : TensorProductAlgebra k Q Λ ν)
    (hx : x * tensorOfKLR Q Λ ν (e (sadj (W ℓ).card j • s)) = x)
    (hc : x * tensorOfKLR Q Λ ν (ψ j * e s) = 0) : x = 0 := by
  induction ℓ with
  | zero =>
    have hcard : (W 0).card = 1 := by simp [stendhalWeight]
    omega
  | succ ℓ ih =>
    by_cases h : j + 1 < (W ℓ).card
    · obtain ⟨u, hu, he, ht⟩ := oneBlack_crossing_peelLastRed h s hs hb
      have hbu : u.lbl ⟨j + 1, h⟩ = .inl i := by
        have heq := appendRedLoading_lbl u ⟨j + 1, h⟩
        rw [he] at heq
        exact addRedColor_injective ℓ (heq.symm.trans hb)
      have hu' : IsRedOrdered (sadj (W ℓ).card j • u) := by
        apply (appendRedLoading_ordered_iff _).mp
        rw [ht]
        have hred : ¬ ((s.lbl ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩).isRight
            ∧ (s.lbl ⟨j + 1, hj⟩).isRight) := by rw [hb]; simp
        exact (redWord_eq_finRange_iff _).1
          ((redWord_sadj_smul s hj hred).trans
            ((redWord_eq_finRange_iff _).2 hs))
      let c : OrderedCrossingTest ℓ ν := ⟨sadj (W ℓ).card j • u, u, hu', hu, j, h⟩
      have hc' : c.InjectiveAt Q (Λ ∘ Fin.castSucc) := ih (Λ ∘ Fin.castSucc) u hu h hbu
      apply c.injectiveAt_appendReds Q hQ 1 Λ hc' x
      · change x * tensorOfKLR Q Λ ν (e (appendRedLoading (sadj (W ℓ).card j • u))) = x
        rwa [ht]
      · change x * tensorOfKLR Q Λ ν (ψ j * e (appendRedLoading u)) = 0
        rwa [he]
    · have hterm : j + 2 = (W (ℓ + 1)).card := by
        have hm : (W (ℓ + 1)).card = ℓ + 1 + 1 := by simp [stendhalWeight]
        have hn : (W ℓ).card = ℓ + 1 := by simp [stendhalWeight]
        rw [hm] at hj ⊢
        rw [hn] at h
        omega
      obtain ⟨u, hu, he, hs', ht'⟩ := oneBlack_terminalCrossing_is_rightmost hj hterm s hs hb
      exact base Λ u hu x (ht' ▸ hx) (he ▸ hs' ▸ hc)

end Categorification.Stendhal

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA QuantumGroup KL3.Diagram

variable {I k : Type} [DecidableEq I] [Field k] {D : CartanDatum I} {ℓ : ℕ}
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars D k)

/-- The ordinary crossing test at one black and any number of red strands,
at the standard Khovanov–Lauda parameters. -/
theorem oneBlack_crossing_injective_standard
    (hR : IsRouquierQ D QL) (hQ : KLRSymm QL) (i : I) (Λ : Fin ℓ → I →₀ ℕ)
    (s : Seq (stendhalWeight ℓ ({i} : Multiset I))) (hs : IsRedOrdered s)
    (j : ℕ) (hj : j + 1 < (stendhalWeight ℓ ({i} : Multiset I)).card)
    (hb : s.lbl ⟨j + 1, hj⟩ = .inl i)
    (x : TensorProductAlgebra k QL Λ {i})
    (hx : x * tensorOfKLR QL Λ {i} (e (sadj (stendhalWeight ℓ ({i} : Multiset I)).card j • s)) = x)
    (hc : x * tensorOfKLR QL Λ {i} (ψ j * e s) = 0) : x = 0 :=
  oneBlack_crossing_injective_of_base QL hQ
    (fun weights u hu => eq_zero_of_mul_rightmostRedCrossing (k := k) (C := D)
      hR hQ weights i 0 u hu)
    Λ s hs j hj hb x hx hc

end Categorification.Stendhal
