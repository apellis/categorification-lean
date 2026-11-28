/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCrossTop
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendMixedTopSlide
import Categorification.WeightedKLR.RedStrands.BlackMixedCrossing

/-!
# Two passages of strands of different colours under the window

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔈_a 𝔈_b ≅ 𝔈_a 𝔈_b ∘ K` with the crossing for a cap
at the right end (`j = ℓ`). Appending `b`, then `a`, passes the two new strands under the window
one after the other (`CupCap.topPass_mul_appendPlus_topPass_mixed`). The crossing of the last two
strands of `λ` on the result equals, up to diagrams in which a strand leaves the window at the top,
the passages of `a`, then `b`, transported to the content `{a} + ({b} + ν)`, followed by the
crossing of the two appended strands of `λ⁺` (`CupCap.midCross_mul_topPass_mixed_sub_mem`).
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (a b : I)

local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))
local notation "νba" =>
  ((Singleton.singleton b : Multiset I) + ((Singleton.singleton a : Multiset I) + ν))
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "Rpab" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (νab + ν₀))
local notation "Eab" u:max n:max hn:max =>
  (KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) u n hn) : Rpab)
local notation "sab" s:max => appendBlackLoading a νb (appendBlackLoading b ν s)

omit [DecidableEq I] in
theorem card_appendBlackWeight_mixed : Multiset.card (stendhalWeight ℓ νab) = m + 2 := by
  rw [card_appendBlackWeight, card_appendBlackWeight]

omit [DecidableEq I] in
theorem le_card_appendBlackWeight_mixed : m ≤ Multiset.card (stendhalWeight ℓ νab) := by
  have := card_appendBlackWeight_mixed (ℓ := ℓ) ν a b; omega

omit [DecidableEq I] in
theorem succ_le_card_appendBlackWeight_mixed : m + 1 ≤ Multiset.card (stendhalWeight ℓ νab) := by
  have := card_appendBlackWeight_mixed (ℓ := ℓ) ν a b; omega

/-- The window idempotents of the second passage fix the doubly appended loadings with the
window at `m + 1`. -/
theorem topPassIdem_mul_eSum_mixed (s : Seq (stendhalWeight ℓ ν)) :
    topPassIdem (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) νb a *
        Eab (sab s) (m + 1) (succ_le_card_appendBlackWeight_mixed ν a b) =
      Eab (sab s) (m + 1) (succ_le_card_appendBlackWeight_mixed ν a b) := by
  have hE : Eab (sab s) (m + 1) (succ_le_card_appendBlackWeight_mixed ν a b) =
      Eab (sab s) (Multiset.card (stendhalWeight ℓ νb)) (le_card_appendBlackWeight νb a) :=
    congrArg _ (insertSet_congr' _ _ _ (card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := b)).symm)
  rw [hE]
  exact topPassIdem_mul_eSum νb a (appendBlackLoading b ν s)

/-- **The two passages of strands of different colours**: appending `b`, then `a`, passes the
two new strands under the window, `ψ_{m+1} ⋯ ψ_{m+N} · ψ_m ⋯ ψ_{m+N-1}` on the doubly appended
loadings with the window at `m`. -/
theorem topPass_mul_appendPlus_topPass_mixed :
    topPass (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) νb a *
        appendPlus Q Λ Λc j hj νb ν₀ a
          (topPass (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) ν b) =
      ∑ s : Seq (stendhalWeight ℓ ν),
        underRight N (m + 1) * underRight N m *
          Eab (sab s) m (le_card_appendBlackWeight_mixed ν a b) := by
  have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := b)
  have hU : (underRight N (Multiset.card (stendhalWeight ℓ νb)) : Rpab) = underRight N (m + 1) :=
    congrArg (fun q => (underRight N q : Rpab)) hm
  rw [topPass, topPass, hU, show (underRight N m : KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj))
      (stendhalWeight (ℓ + 2) (νb + ν₀))) = KLRAlgebra.ψw (List.range' m N) from rfl,
    appendPlus_ψw_mul νb a _ (fun q hq => by
      have := card_plus' (I := I) (ℓ := ℓ) (ν := νb) (ν₀ := ν₀)
      rw [List.mem_range'_1] at hq; omega),
    topPassIdem.eq_1 (ν := ν), map_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [appendPlus_eSum_insertSet νb a (appendBlackLoading b ν s) (le_card_appendBlackWeight ν b)
    (le_card_appendBlackWeight_mixed ν a b)]
  have hc := underRight_mul_eSum Q Λ Λc (j := j) (hj := hj) (ν₀ := ν₀) (sab s) (q := m)
    (succ_le_card_appendBlackWeight_mixed ν a b)
  change _ * (underRight N m * _) = _
  rw [hc, mul_assoc, ← mul_assoc (topPassIdem νb a), topPassIdem_mul_eSum_mixed, ← hc,
    ← mul_assoc]

local notation "sba" s:max => appendBlackLoading b νa (appendBlackLoading a ν s)

omit [DecidableEq I] in
theorem le_card_appendBlackWeight_mixed' : m ≤ Multiset.card (stendhalWeight ℓ νba) := by
  rw [card_appendBlackWeight, card_appendBlackWeight]; omega

omit [DecidableEq I] in
/-- The transport of the contents `{b} + ({a} + ν) = {a} + ({b} + ν)` of `λ⁺`. -/
theorem stendhalWeight_mixedSwap :
    stendhalWeight (ℓ + 2) (νba + ν₀) = stendhalWeight (ℓ + 2) (νab + ν₀) :=
  congrArg (fun μ => stendhalWeight (ℓ + 2) (μ + ν₀)) (mixedSwap ν a b)

omit [DecidableEq I] in
/-- **Swapping the two appended strands** of a loading of `λ⁺` with `a`, then `b`, appended gives
the loading with `b`, then `a`, appended. -/
theorem sadj_smul_cast_insertSeq_mixed (s : Seq (stendhalWeight ℓ ν))
    (w : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) :
    sadj (Multiset.card (stendhalWeight (ℓ + 2) (νab + ν₀))) (m + N) •
        Seq.cast (stendhalWeight_mixedSwap (ℓ := ℓ) (ν₀ := ν₀) ν a b)
          (insertSeq (sba s) m (le_card_appendBlackWeight_mixed' ν a b) w) =
      insertSeq (sab s) m (le_card_appendBlackWeight_mixed ν a b) w := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := νab) (ν₀ := ν₀)
  have hM' := card_plus' (I := I) (ℓ := ℓ) (ν := νba) (ν₀ := ν₀)
  have h2 := card_appendBlackWeight_mixed (ℓ := ℓ) ν a b
  have h2' := card_appendBlackWeight_mixed (ℓ := ℓ) ν b a
  have ha1 := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := a)
  have hb1 := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := b)
  have hN := Multiset.card_map (cupColour (I := I) (ℓ := ℓ) j hj) (stendhalWeight 2 ν₀)
  apply Subtype.ext
  funext c
  change (insertSeq (sba s) m _ w).lbl (Fin.cast _ ((sadj _ (m + N))⁻¹ c)) =
    (insertSeq (sab s) m _ w).lbl c
  rw [sadj_inv]
  obtain ⟨cv, hcv⟩ := c
  by_cases hc1 : cv < m + N
  · rw [sadj_apply_of_ne _ (by dsimp only; omega) (by dsimp only; omega)]
    by_cases hc2 : cv < m
    · rw [insertSeq_lbl_lt _ _ w ⟨cv, by omega⟩ hc2 rfl,
        insertSeq_lbl_lt _ _ w ⟨cv, by omega⟩ hc2 rfl,
        appendBlackLoading_lbl_of_lt b νa _ _ (by dsimp only; omega),
        appendBlackLoading_lbl_of_lt a ν _ _ (by dsimp only; omega),
        appendBlackLoading_lbl_of_lt a νb _ _ (by dsimp only; omega),
        appendBlackLoading_lbl_of_lt b ν _ _ (by dsimp only; omega)]
    · rw [insertSeq_lbl_win _ _ w ⟨cv - m, by omega⟩ (by simp only [Fin.val_cast]; omega),
        insertSeq_lbl_win _ _ w ⟨cv - m, by omega⟩ (by dsimp only; omega)]
  · by_cases hc3 : cv = m + N
    · subst hc3
      rw [sadj_apply_left (by omega),
        insertSeq_lbl_ge _ _ w ⟨m + 1, by omega⟩ (by dsimp only; omega)
          (by simp only [Fin.val_cast]; omega),
        insertSeq_lbl_ge _ _ w ⟨m, by omega⟩ le_rfl rfl,
        appendBlackLoading_lbl_of_eq b νa _ _ (by dsimp only; omega),
        appendBlackLoading_lbl_of_lt a νb _ _ (by dsimp only; omega),
        appendBlackLoading_lbl_of_eq b ν _ _ rfl]
    · have hc4 : cv = m + N + 1 := by omega
      subst hc4
      rw [sadj_apply_right (by omega),
        insertSeq_lbl_ge _ _ w ⟨m, by omega⟩ le_rfl rfl,
        insertSeq_lbl_ge _ _ w ⟨m + 1, by omega⟩ (by dsimp only; omega) (by dsimp only; omega),
        appendBlackLoading_lbl_of_lt b νa _ _ (by dsimp only; omega),
        appendBlackLoading_lbl_of_eq a ν _ _ rfl,
        appendBlackLoading_lbl_of_eq a νb _ _ (by dsimp only; omega)]

/-- **The passages of `a`, then `b`, transported, followed by the crossing of the appended
strands**: the passages of `b`, then `a`, with the crossing of the two appended strands of `λ⁺`
at their bottom. -/
theorem castKLR_topPass_mixed_mul_ψ :
    castKLR (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight_mixedSwap (ℓ := ℓ) ν a b)
        (topPass (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) νa b *
          appendPlus Q Λ Λc j hj νa ν₀ b
            (topPass (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) ν a)) *
        KLRAlgebra.ψ (m + N) =
      ∑ s : Seq (stendhalWeight ℓ ν),
        underRight N (m + 1) * underRight N m * KLRAlgebra.ψ (m + N) *
          Eab (sab s) m (le_card_appendBlackWeight_mixed ν a b) := by
  rw [topPass_mul_appendPlus_topPass_mixed ν b a, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, map_mul]
  simp only [underRight, KLRAlgebra.castKLR_ψw]
  rw [eSum_insertSet, eSum_insertSet, map_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [castKLR_e, ← sadj_smul_cast_insertSeq_mixed ν a b s, mul_assoc _ (ψ _), KLRAlgebra.ψ_mul_e,
    ← mul_smul, TypeA.sadj_mul_self, one_smul, ← mul_assoc]

/-- **The crossing of the last two strands of `λ` on the image of the two passages**, for
`j = ℓ` and colours `a`, `b`: below the window idempotents of `λ⁺`, it equals the transported
passages of `a`, then `b`, followed by the crossing of the two appended strands of `λ⁺`, up to
diagrams in which a strand leaves the window at the top. -/
theorem midCross_mul_topPass_mixed_sub_mem (h : ¬ j < ℓ) :
    (∑ u, midIdem j hj Q Λ Λc νab ν₀ u) *
        (midCross j hj Q Λ Λc νab ν₀ m *
            (topPass (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) νb a *
              appendPlus Q Λ Λc j hj νb ν₀ a
                (topPass (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) ν b)) -
          castKLR (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight_mixedSwap (ℓ := ℓ) ν a b)
            (topPass (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) νa b *
              appendPlus Q Λ Λc j hj νa ν₀ b
                (topPass (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) ν a)) *
            KLRAlgebra.ψ (m + N)) ∈ midExit j hj Q Λ Λc νab ν₀ := by
  have h2 := card_appendBlackWeight_mixed (ℓ := ℓ) ν a b
  have hq : m + 2 ≤ Multiset.card (stendhalWeight ℓ νab) := by omega
  rw [castKLR_topPass_mixed_mul_ψ, midCross_eq_of_not_lt h (by omega), mul_assoc,
    ← mul_assoc (∑ u, midIdem j hj Q Λ Λc νab ν₀ u), sum_midIdem_mul_topPass νb a h,
    topPass_mul_appendPlus_topPass_mixed, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  refine Submodule.sum_mem _ fun u _ => ?_
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [eSum_insertSet, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Submodule.sum_mem _ fun w _ => ?_
  have hE : midIdem j hj Q Λ Λc νab ν₀ u = Eab u (m + 2) hq := by
    rw [midIdem_eq_of_not_lt νab h u]
    exact congrArg _ (insertSet_congr' _ _ _ h2)
  have hX : ∀ (n : ℕ) (hn : n ≤ Multiset.card (stendhalWeight ℓ νab)), n = m + 2 →
      exitSpan (ν₀ := ν₀) Q Λ Λc j hj u (m + 2) hq ≤ exitSpan (ν₀ := ν₀) Q Λ Λc j hj u n hn := by
    rintro n hn rfl; exact le_rfl
  refine mem_midExit u (hX _ _ (by rw [midPos_of_not_lt j u h, h2]) ?_)
  rw [hE, underRight, underRight, ← mul_assoc, ← mul_assoc]
  refine eSum_mul_crossSlide_mem (Λ := Λ) u hq _ fun r => ?_
  rw [insertSeq_lbl_ge _ _ _ ⟨m + 1, by omega⟩ (by dsimp only; omega) (by dsimp only; omega)]
  exact oldColour_ne_cupColour_inr _ r

end Categorification.Stendhal.CupCap

