/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendIotaSurjCap

/-!
# Appending a black strand to a block generator

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the part for `𝔈_i`, for `j < ℓ`. A block generator `g = (s, t, u)` at `ν` gives
a block generator `g i = (s i, t, u × 1)` at `{i} + ν`, appending the black strand `i` at the far
right (`CupCap.MidGen.appendExt`). Its bottom is the bottom of `g` followed by `i`, so `γ_{g i}`
is fixed by `e'⁺`, and `ι(v γ_g) = v γ_{g i}` for the reduced words through the last coset
(`CupCap.appendIota_tmul_midGenCorner`). These are the generators whose bottom ends in `i`.

## Main definitions

* `CupCap.MidGen.appendExt`.

## Main results

* `CupCap.MidGen.perm_eq_one_of_strictMono`, `CupCap.MidGen.appendExt_perm`.
* `CupCap.midGenElt_appendExt_mul_appendBlackPlus_one`.
* `CupCap.appendIota_tmul_midGenCorner`.
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
local notation "Ap" => appendPlus Q Λ Λc j hj ν ν₀ i
local notation "aBP" => appendBlackPlus Q Λ Λc j hj ν ν₀ i

/-! ### Block shuffles -/

section Perm

variable {μ : Multiset I}

omit [DecidableEq I] in
/-- **A generator whose strands of `λ` keep their order is a block shuffle**: if the bottom
positions of the strands of `λ` increase, the permutation of the strands of `λ` is trivial. -/
theorem MidGen.perm_eq_one_of_strictMono (g : MidGen j hj μ ν₀)
    (hg : StrictMono fun a => g.botEquiv (.inl a)) : g.perm = 1 := by
  have hf : (fun a => g.botEquiv (.inl a)) = g.botOrd :=
    Finset.orderEmbOfFin_unique g.card_botSet
      (fun a => Finset.mem_map_of_mem _ (Finset.mem_univ a)) hg
  refine Equiv.ext fun b => ?_
  have h1 := g.botEquiv_perm b
  rw [← hf] at h1
  exact Sum.inl_injective (g.botEquiv.injective h1)

omit [DecidableEq I] in
theorem MidGen.botEquiv_inl (g : MidGen j hj μ ν₀) (a : Fin (Multiset.card (stendhalWeight ℓ μ))) :
    g.botEquiv (.inl a) = g.u⁻¹ (outPos j ν₀ g.s a) := by
  simp [MidGen.botEquiv, outPos, Perm.inv_def]

omit [DecidableEq I] in
theorem MidGen.strictMono_of_perm_eq_one (g : MidGen j hj μ ν₀) (hg : g.perm = 1) :
    StrictMono fun a => g.botEquiv (.inl a) := by
  have h : (fun a => g.botEquiv (.inl a)) = g.botOrd := funext fun b => by
    have := g.botEquiv_perm b
    rwa [hg, Perm.one_apply] at this
  rw [h]
  exact g.botOrd.strictMono

end Perm

/-! ### The appended generator -/

section Ext

omit [DecidableEq I] in
/-- The red-ordered loadings of `λ⁺` stay red-ordered when a black strand is appended. -/
theorem isRedOrdered_cast_append (X : Seq ρ) (hX : IsRedOrdered X) :
    IsRedOrdered (Seq.cast (plusAddBlack ν ν₀ i) (X.append (default : Seq σᵢ))) := by
  have hm := card_plus_appendBlack (ℓ := ℓ) (ν₀ := ν₀) ν i
  intro x y r r' hxy hx hy
  by_cases hyl : y.val < M
  · have hxl : x.val < M := lt_trans hxy hyl
    have ex : (Seq.cast (plusAddBlack ν ν₀ i) (X.append (default : Seq σᵢ))).lbl x =
        X.lbl ⟨x.val, hxl⟩ := by
      change (X.append (default : Seq σᵢ)).1 _ = _
      rw [Seq.append_apply_lt _ _ _ (by exact hxl)]
      rfl
    have ey : (Seq.cast (plusAddBlack ν ν₀ i) (X.append (default : Seq σᵢ))).lbl y =
        X.lbl ⟨y.val, hyl⟩ := by
      change (X.append (default : Seq σᵢ)).1 _ = _
      rw [Seq.append_apply_lt _ _ _ (by exact hyl)]
      rfl
    rw [ex] at hx
    rw [ey] at hy
    exact hX _ _ r r' (by rw [Fin.lt_def] at hxy ⊢; exact hxy) hx hy
  · have hy2 := y.2
    rw [lbl_last_cast_append ν i X y (by omega)] at hy
    exact absurd hy (by simp)

variable (h : j < ℓ)

include h in
/-- The bottom of the appended generator, before it is defined: the window shuffle `u × 1` on the
appended loading at the window. -/
theorem extPerm_inv_smul_midSeq_appendBlackLoading (s : Seq (stendhalWeight ℓ ν))
    (t : Seq (stendhalWeight 2 ν₀)) (u : Perm (Fin M)) :
    (extPerm (card_plus_appendBlack (ℓ := ℓ) (ν₀ := ν₀) ν i) u)⁻¹ •
        midSeq j hj (appendBlackLoading i ν s) t =
      Seq.cast (plusAddBlack ν ν₀ i) ((u⁻¹ • midSeq j hj s t).append (default : Seq σᵢ)) := by
  have hm := card_plus_appendBlack (ℓ := ℓ) (ν₀ := ν₀) ν i
  rw [midSeq_appendBlackLoading ν i h]
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

/-- **The appended generator** `g i = (s i, t, u × 1)` at `{i} + ν` of a generator `g` at `ν`,
without dots, for `j < ℓ`. -/
def MidGen.appendExt (g : MidGen j hj ν ν₀) : MidGen j hj νᵢ ν₀ where
  s := appendBlackLoading i ν g.s
  t := g.t
  d := 0
  u := extPerm (card_plus_appendBlack (ℓ := ℓ) (ν₀ := ν₀) ν i) g.u
  hs := appendBlackLoading_ordered i ν g.s g.hs
  ht := g.ht
  hd := fun a ha => absurd ha (Finset.notMem_empty a)
  hu := by
    have hm := card_plus_appendBlack (ℓ := ℓ) (ν₀ := ν₀) ν i
    have hmid := midPos_appendBlackLoading j ν i h g.s
    have hle := midPos_add_N_le j ν₀ g.s
    have key : ∀ x : Fin N,
        ((extPerm hm g.u)⁻¹ (winPos (midPos_add_N_le j ν₀ (appendBlackLoading i ν g.s)) x)).val =
          (g.u⁻¹ (winPos (midPos_add_N_le j ν₀ g.s) x)).val := by
      intro x
      have hx := x.2
      have hx' : (winPos (midPos_add_N_le j ν₀ (appendBlackLoading i ν g.s)) x).val < M := by
        rw [winPos_val, hmid]; omega
      rw [extPerm_inv, extPerm_val]
      simp only [hx', ↓reduceDIte]
      congr 2
      apply Fin.ext
      simp only [winPos_val, hmid]
    intro x x' hxx'
    have := g.hu hxx'
    rw [Fin.lt_def] at this ⊢
    rw [key, key]
    exact this
  hbot := by
    rw [extPerm_inv_smul_midSeq_appendBlackLoading ν i h]
    exact isRedOrdered_cast_append ν i _ g.hbot

variable (g : MidGen j hj ν ν₀)

theorem MidGen.appendExt_bot :
    (g.appendExt ν i h).bot = Seq.cast (plusAddBlack ν ν₀ i) (g.bot.append (default : Seq σᵢ)) :=
  extPerm_inv_smul_midSeq_appendBlackLoading ν i h g.s g.t g.u

/-- **The appended generator of a block shuffle is a block shuffle.** -/
theorem MidGen.appendExt_perm (hg : g.perm = 1) : (g.appendExt ν i h).perm = 1 := by
  have hm := card_plus_appendBlack (ℓ := ℓ) (ν₀ := ν₀) ν i
  have hmb := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
  have hmid := midPos_appendBlackLoading j ν i h g.s
  have hmo := g.strictMono_of_perm_eq_one hg
  have hle := midPos_le j g.s
  have hcard := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  apply MidGen.perm_eq_one_of_strictMono
  have k1 : ∀ (a : Fin (Multiset.card (stendhalWeight ℓ νᵢ))) (ha : a.val < m),
      ((g.appendExt ν i h).botEquiv (.inl a)).val = (g.botEquiv (.inl ⟨a.val, ha⟩)).val := by
    intro a ha
    rw [MidGen.botEquiv_inl, MidGen.botEquiv_inl]
    change ((extPerm hm g.u)⁻¹ (outPos j ν₀ (appendBlackLoading i ν g.s) a)).val =
      (g.u⁻¹ (outPos j ν₀ g.s ⟨a.val, ha⟩)).val
    have ho : (outPos j ν₀ (appendBlackLoading i ν g.s) a).val =
        (outPos j ν₀ g.s ⟨a.val, ha⟩).val := by
      rw [outPos_val, outPos_val, hmid]
    have hlt : (outPos j ν₀ (appendBlackLoading i ν g.s) a).val < M := by
      rw [ho]; exact (outPos j ν₀ g.s ⟨a.val, ha⟩).2
    rw [extPerm_inv, extPerm_val]
    simp only [hlt, ↓reduceDIte]
    congr 2
    exact Fin.ext ho
  have k2 : ∀ a : Fin (Multiset.card (stendhalWeight ℓ νᵢ)), ¬ a.val < m →
      ((g.appendExt ν i h).botEquiv (.inl a)).val = M := by
    intro a ha
    rw [MidGen.botEquiv_inl]
    change ((extPerm hm g.u)⁻¹ (outPos j ν₀ (appendBlackLoading i ν g.s) a)).val = M
    have ha2 := a.2
    have ho : (outPos j ν₀ (appendBlackLoading i ν g.s) a).val = M := by
      rw [outPos_val, hmid]
      split_ifs <;> omega
    rw [extPerm_inv, extPerm_val]
    simp only [ho, lt_irrefl, ↓reduceDIte]
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

/-! ### The appended generator is fixed by `e'⁺` -/

section Elt

variable (h : j < ℓ)

/-- Appending the strand to an idempotent is fixed by the appended unit. -/
theorem e_cast_append_mul_appendPlus_one (X : Seq ρ) :
    KLRAlgebra.e (Seq.cast (plusAddBlack ν ν₀ i) (X.append (default : Seq σᵢ))) * Ap 1 =
      (KLRAlgebra.e (Seq.cast (plusAddBlack ν ν₀ i) (X.append (default : Seq σᵢ))) :
        KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (νᵢ + ν₀))) := by
  rw [← appendPlus_e, ← map_mul, mul_one]

/-- **`γ_{g i}` is fixed by `e'⁺`**, for `j < ℓ`. -/
theorem midGenElt_appendExt_mul_appendBlackPlus_one {ρ' : Perm (Fin M') → List ℕ}
    (g : MidGen j hj ν ν₀) :
    midGenElt Q Λ Λc ρ' (g.appendExt ν i h) * aBP 1 = midGenElt Q Λ Λc ρ' (g.appendExt ν i h) := by
  rw [appendBlackPlus_one, midGenElt, ← map_mul, midGenKLR, mul_assoc,
    MidGen.appendExt_bot ν i h, e_cast_append_mul_appendPlus_one]

/-- The corner element of a generator, through `midGen`. -/
theorem midGen_midGenElt {μ : Multiset I}
    {ρ₃ : Perm (Fin (Multiset.card (stendhalWeight (ℓ + 2) (μ + ν₀)))) → List ℕ}
    (g : MidGen j hj μ ν₀) :
    midGen j hj Q Λ Λc μ ν₀ (midGenElt Q Λ Λc ρ₃ g) = midGenCorner Q Λ Λc ρ₃ g :=
  Subtype.ext (congrArg op (midStendhal_one_mul_midGenElt g))

variable {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **`ι` on a generator without dots**, for `j < ℓ`: `ι(v γ_g) = v γ_{g i}`, for the canonical
reduced words at `ν` and the reduced words through the last coset at `{i} + ν`. -/
theorem appendIota_tmul_midGenCorner (g : MidGen j hj ν ν₀) (hd : g.d = 0) (v : L) :
    appendIota ν i L h (Ind.tmul (midGenCorner Q Λ Λc (canWord M) g) v) =
      (Ind.tmul (midGenCorner Q Λ Λc (appendWords ν i) (g.appendExt ν i h)) v :
        MidModel j hj Q Λ Λc νᵢ ν₀ L) := by
  have hm := card_plus_appendBlack (ℓ := ℓ) (ν₀ := ν₀) ν i
  have hg := appendBlackPlusOp_one_smul_tmul_midGenCorner (Q := Q) (Λ := Λ) (Λc := Λc) ν i h
    (ρ' := appendWords ν i) (g.appendExt ν i h) rfl (s := g.s) rfl (validWord_canWord M g.u)
    (lastCosetWord_extPerm hm _ g.u) (wordProd_canWord_ext hm g.u) v
  have he : midGenElt Q Λ Λc (canWord M) g =
      botMap k Q Λ Λc j hj ν ν₀ (KLRAlgebra.e (midSeq j hj g.s g.t) * ψw (canWord M g.u)) := by
    rw [midGenElt, midGenKLR_of_d_eq_zero g hd (wordProd_canWord M g.u)]
  rw [← midGen_midGenElt, he]
  refine Eq.trans hg.symm ?_
  rw [Ind.smul_tmul]
  congr 1
  apply Subtype.ext
  apply MulOpposite.unop_injective
  exact midGenElt_appendExt_mul_appendBlackPlus_one ν i h g

end Elt

end Categorification.Stendhal.CupCap
