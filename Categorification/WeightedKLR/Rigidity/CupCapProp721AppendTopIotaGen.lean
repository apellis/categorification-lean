/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendIotaGen
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendTopIotaSurj

/-!
# Appending a black strand to a block generator, at the right end

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`, for `j = ℓ`. A block generator `g = (s, t, u)` at `ν` gives
a block generator `g i = (s i, t, c (u × 1))` at `{i} + ν`, where `c = s_m ⋯ s_{m+N-1}` passes the
appended strand `i` under the window at the right end (`CupCap.MidGen.appendExtTop`). As for
`j < ℓ`, its bottom is the bottom of `g` followed by `i`, so `γ_{g i}` is fixed by `e'⁺`, and
`ι(v γ_g) = v γ_{g i}` for the reduced words through the last coset
(`CupCap.appendTopIota_tmul_midGenCorner`).

## Main definitions

* `CupCap.MidGen.appendExtTop`.

## Main results

* `CupCap.MidGen.appendExtTop_bot`, `CupCap.MidGen.appendExtTop_perm`.
* `CupCap.appendTopIota_tmul_midGenCorner`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA Equiv MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "M'" => Multiset.card (stendhalWeight (ℓ + 2) (((Singleton.singleton i :
  Multiset I) + ν) + ν₀))
local notation "σᵢ" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin (ℓ + 2)))
local notation "ρ" => stendhalWeight (ℓ + 2) (ν + ν₀)
local notation "c" => wordProd (Multiset.card (stendhalWeight (ℓ + 2) (((Singleton.singleton i :
  Multiset I) + ν) + ν₀))) (List.range' (Multiset.card (stendhalWeight ℓ ν))
    (Multiset.card (stendhalWeight 2 ν₀)))

section Ext

omit [DecidableEq I] in
/-- `(u × 1)⁻¹` on a loading with the strand `i` appended. -/
theorem extPerm_inv_smul_cast_append (X : Seq ρ) (u : Perm (Fin M)) :
    (extPerm (card_plus_appendBlack (ℓ := ℓ) (ν₀ := ν₀) ν i) u)⁻¹ •
        Seq.cast (plusAddBlack ν ν₀ i) (X.append (default : Seq σᵢ)) =
      Seq.cast (plusAddBlack ν ν₀ i) ((u⁻¹ • X).append (default : Seq σᵢ)) := by
  have hm := card_plus_appendBlack (ℓ := ℓ) (ν₀ := ν₀) ν i
  apply Subtype.ext
  funext p
  rw [Seq.smul_apply, Perm.inv_def, Equiv.symm_symm, Seq.cast_apply, Seq.cast_apply]
  by_cases hp : p.val < M
  · have hp' : (extPerm hm u p).val = (u ⟨p.val, hp⟩).val := by
      rw [extPerm_val]; split_ifs; rfl
    rw [Seq.append_apply_lt _ _ _ (by
        change (extPerm hm u p).val < _; rw [hp']; exact (u ⟨p.val, hp⟩).2),
      Seq.append_apply_lt _ _ _ (by exact hp), Seq.smul_apply, Perm.inv_def,
      Equiv.symm_symm]
    exact Seq.apply_congr _ (by simp only [Fin.val_cast]; exact hp')
  · have hp' : (extPerm hm u p).val = p.val := by
      rw [extPerm_val]; split_ifs; rfl
    rw [Seq.append_apply_ge _ _ _ (by simp only [Fin.val_cast, hp']; omega),
      Seq.append_apply_ge _ _ _ (by simp only [Fin.val_cast]; omega)]
    exact Seq.apply_congr _ (by simp only [Fin.val_cast, hp'])

variable (h : ¬ j < ℓ)

include h in
omit [DecidableEq I] in
/-- For `j = ℓ`, the loading at the window of an appended loading is `c` applied to the loading
at the window followed by `i`. -/
theorem midSeq_appendBlackLoading_eq_smul (s : Seq (stendhalWeight ℓ ν))
    (t : Seq (stendhalWeight 2 ν₀)) :
    midSeq j hj (appendBlackLoading i ν s) t =
      c • Seq.cast (plusAddBlack ν ν₀ i) ((midSeq j hj s t).append (default : Seq σᵢ)) := by
  rw [midSeq_appendBlackLoading_eq_insertSeq ν i h, midSeq_append_eq_insertSeq ν i h,
    range'_smul_insertSeq _ _ (succ_le_card_appendBlackWeight ν i)]

omit [DecidableEq I] in
/-- The values of `c = s_m ⋯ s_{m+N-1}`. -/
theorem val_topPerm_apply (r : Fin M') :
    (c r).val = if r.val = m + N then m else if m ≤ r.val ∧ r.val < m + N then r.val + 1
      else r.val := by
  have hK := card_plus_appendBlack_eq (ℓ := ℓ) (ν₀ := ν₀) ν i
  exact val_wordProd_range'_apply (by omega) r

omit [DecidableEq I] in
theorem val_topPerm_inv_apply (r : Fin M') :
    (c⁻¹ r).val = if r.val = m then m + N else if m < r.val ∧ r.val ≤ m + N then r.val - 1
      else r.val := by
  have hK := card_plus_appendBlack_eq (ℓ := ℓ) (ν₀ := ν₀) ν i
  have key := val_topPerm_apply ν i (ν₀ := ν₀) (c⁻¹ r)
  rw [Perm.inv_def, Equiv.apply_symm_apply] at key
  rw [Perm.inv_def]
  have h2 := (Equiv.symm c r).2
  generalize (Equiv.symm c r).val = y at key h2 ⊢
  split_ifs at key ⊢ <;> omega

/-- **The appended generator at the right end** `g i = (s i, t, c (u × 1))` at `{i} + ν` of a
generator `g` at `ν`, without dots, for `j = ℓ`. -/
def MidGen.appendExtTop (g : MidGen j hj ν ν₀) : MidGen j hj νᵢ ν₀ where
  s := appendBlackLoading i ν g.s
  t := g.t
  d := 0
  u := c * extPerm (card_plus_appendBlack (ℓ := ℓ) (ν₀ := ν₀) ν i) g.u
  hs := appendBlackLoading_ordered i ν g.s g.hs
  ht := g.ht
  hd := fun a ha => absurd ha (Finset.notMem_empty a)
  hu := by
    have hm := card_plus_appendBlack (ℓ := ℓ) (ν₀ := ν₀) ν i
    have hK := card_plus_appendBlack_eq (ℓ := ℓ) (ν₀ := ν₀) ν i
    have hmid : midPos j (appendBlackLoading i ν g.s) = m + 1 := by
      rw [midPos_appendBlackLoading_of_not_lt i h, midPos_of_not_lt j _ h]
    have hmid0 : midPos j g.s = m := midPos_of_not_lt j _ h
    have key : ∀ x : Fin N,
        ((c * extPerm hm g.u)⁻¹
          (winPos (midPos_add_N_le j ν₀ (appendBlackLoading i ν g.s)) x)).val =
          (g.u⁻¹ (winPos (midPos_add_N_le j ν₀ g.s) x)).val := by
      intro x
      have hx := x.2
      rw [mul_inv_rev, Perm.mul_apply]
      have hc : (c⁻¹ (winPos (midPos_add_N_le j ν₀ (appendBlackLoading i ν g.s)) x)).val =
          m + x.val := by
        rw [val_topPerm_inv_apply, winPos_val, hmid]
        split_ifs <;> omega
      have hlt : (c⁻¹ (winPos (midPos_add_N_le j ν₀ (appendBlackLoading i ν g.s)) x)).val <
          M := by
        rw [hc]; have := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀); omega
      rw [extPerm_inv, extPerm_val]
      simp only [hlt, ↓reduceDIte]
      congr 2
      apply Fin.ext
      rw [hc, winPos_val, hmid0]
    intro x x' hxx'
    have := g.hu hxx'
    rw [Fin.lt_def] at this ⊢
    rw [key, key]
    exact this
  hbot := by
    rw [midSeq_appendBlackLoading_eq_smul ν i h, mul_inv_rev, mul_smul, inv_smul_smul,
      extPerm_inv_smul_cast_append]
    exact isRedOrdered_cast_append ν i _ g.hbot

variable (g : MidGen j hj ν ν₀)

omit [DecidableEq I] in
theorem MidGen.appendExtTop_bot :
    (g.appendExtTop ν i h).bot =
      Seq.cast (plusAddBlack ν ν₀ i) (g.bot.append (default : Seq σᵢ)) := by
  change (c * extPerm _ g.u)⁻¹ • midSeq j hj (appendBlackLoading i ν g.s) g.t = _
  rw [midSeq_appendBlackLoading_eq_smul ν i h, mul_inv_rev, mul_smul, inv_smul_smul,
    extPerm_inv_smul_cast_append]
  rfl

omit [DecidableEq I] in
/-- **The appended generator of a block shuffle is a block shuffle**, for `j = ℓ`. -/
theorem MidGen.appendExtTop_perm (hg : g.perm = 1) : (g.appendExtTop ν i h).perm = 1 := by
  have hm := card_plus_appendBlack (ℓ := ℓ) (ν₀ := ν₀) ν i
  have hK := card_plus_appendBlack_eq (ℓ := ℓ) (ν₀ := ν₀) ν i
  have hmb := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have hmid : midPos j (appendBlackLoading i ν g.s) = m + 1 := by
    rw [midPos_appendBlackLoading_of_not_lt i h, midPos_of_not_lt j _ h]
  have hmid0 : midPos j g.s = m := midPos_of_not_lt j _ h
  have hmo := g.strictMono_of_perm_eq_one hg
  have hcard := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  apply MidGen.perm_eq_one_of_strictMono
  have ho : ∀ a : Fin (Multiset.card (stendhalWeight ℓ νᵢ)),
      (outPos j ν₀ (appendBlackLoading i ν g.s) a).val = a.val := by
    intro a
    have := a.2
    rw [outPos_val, hmid]
    split_ifs <;> omega
  have k1 : ∀ (a : Fin (Multiset.card (stendhalWeight ℓ νᵢ))) (ha : a.val < m),
      ((g.appendExtTop ν i h).botEquiv (.inl a)).val =
        (g.botEquiv (.inl ⟨a.val, ha⟩)).val := by
    intro a ha
    rw [MidGen.botEquiv_inl, MidGen.botEquiv_inl]
    change ((c * extPerm hm g.u)⁻¹ (outPos j ν₀ (appendBlackLoading i ν g.s) a)).val =
      (g.u⁻¹ (outPos j ν₀ g.s ⟨a.val, ha⟩)).val
    have ho0 : (outPos j ν₀ g.s ⟨a.val, ha⟩).val = a.val := by
      rw [outPos_val, hmid0]
      simp only [ha, ↓reduceIte]
    have hc : (c⁻¹ (outPos j ν₀ (appendBlackLoading i ν g.s) a)).val = a.val := by
      rw [val_topPerm_inv_apply, ho]
      split_ifs <;> omega
    have hlt : (c⁻¹ (outPos j ν₀ (appendBlackLoading i ν g.s) a)).val < M := by
      rw [hc]; omega
    rw [mul_inv_rev, Perm.mul_apply, extPerm_inv, extPerm_val]
    simp only [hlt, ↓reduceDIte]
    congr 2
    exact Fin.ext (by rw [hc, ho0])
  have k2 : ∀ a : Fin (Multiset.card (stendhalWeight ℓ νᵢ)), ¬ a.val < m →
      ((g.appendExtTop ν i h).botEquiv (.inl a)).val = M := by
    intro a ha
    rw [MidGen.botEquiv_inl]
    change ((c * extPerm hm g.u)⁻¹ (outPos j ν₀ (appendBlackLoading i ν g.s) a)).val = M
    have ha2 := a.2
    have hc : (c⁻¹ (outPos j ν₀ (appendBlackLoading i ν g.s) a)).val = M := by
      rw [val_topPerm_inv_apply, ho]
      split_ifs <;> omega
    rw [mul_inv_rev, Perm.mul_apply, extPerm_inv, extPerm_val]
    simp only [hc, lt_irrefl, ↓reduceDIte]
  intro a a' haa'
  rw [Fin.lt_def] at haa' ⊢
  have ha2 := a'.2
  by_cases h1 : a.val < m
  · rw [k1 a h1]
    by_cases h2 : a'.val < m
    · rw [k1 a' h2]
      exact hmo (show (⟨a.val, h1⟩ : Fin m) < ⟨a'.val, h2⟩ from Fin.lt_def.2 haa')
    · rw [k2 a' h2]
      exact (g.botEquiv (.inl ⟨a.val, h1⟩)).2
  · omega

end Ext

/-! ### `ι` on the generators -/

section Elt

variable (h : ¬ j < ℓ)

local notation "aBP" => appendBlackPlus Q Λ Λc j hj ν ν₀ i

/-- **`γ_{g i}` is fixed by `e'⁺`**, for `j = ℓ`. -/
theorem midGenElt_appendExtTop_mul_appendBlackPlus_one {ρ' : Perm (Fin M') → List ℕ}
    (g : MidGen j hj ν ν₀) :
    midGenElt Q Λ Λc ρ' (g.appendExtTop ν i h) * aBP 1 =
      midGenElt Q Λ Λc ρ' (g.appendExtTop ν i h) := by
  rw [appendBlackPlus_one, midGenElt, ← map_mul, midGenKLR, mul_assoc,
    MidGen.appendExtTop_bot ν i h, e_cast_append_mul_appendPlus_one]

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

/-- **`ι` on a generator without dots**, for `j = ℓ`: `ι(v γ_g) = v γ_{g i}`, for the canonical
reduced words at `ν` and the reduced words through the last coset at `{i} + ν`. -/
theorem appendTopIota_tmul_midGenCorner (g : MidGen j hj ν ν₀) (hd : g.d = 0) (v : L) :
    appendTopIota ν i hP hPL hL hκ h (Ind.tmul (midGenCorner Q Λ Λc (canWord M) g) v) =
      (Ind.tmul (midGenCorner Q Λ Λc (appendWords ν i) (g.appendExtTop ν i h)) v :
        MidModel j hj Q Λ Λc νᵢ ν₀ L) := by
  have hm := card_plus_appendBlack (ℓ := ℓ) (ν₀ := ν₀) ν i
  have hK := card_plus_appendBlack_eq (ℓ := ℓ) (ν₀ := ν₀) ν i
  have hg := appendBlackPlusOp_one_smul_tmul_midGenCorner_top (Q := Q) (Λ := Λ) (Λc := Λc) ν i
    hP hPL hL hκ h (ρ' := appendWords ν i) (g.appendExtTop ν i h) rfl (s := g.s) rfl
    (validWord_canWord M g.u) (lastCosetWord_range'_mul_extPerm hm hK _ g.u)
    (by rw [wordProd_append, wordProd_canWord_ext hm]; rfl) v
  have he : midGenElt Q Λ Λc (canWord M) g =
      botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.e (midSeq j hj g.s g.t) * ψw (canWord M g.u)) := by
    rw [midGenElt, midGenKLR_of_d_eq_zero g hd (wordProd_canWord M g.u)]
  rw [← midGen_midGenElt, he]
  refine Eq.trans hg.symm ?_
  rw [Ind.smul_tmul]
  congr 1
  apply Subtype.ext
  apply MulOpposite.unop_injective
  exact midGenElt_appendExtTop_mul_appendBlackPlus_one ν i h g

end Elt

end Categorification.Stendhal.CupCap
