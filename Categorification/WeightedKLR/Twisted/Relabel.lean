/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Twisted.Arrangement
import Categorification.WeightedKLR.GalleryRep

/-!
# Relabelling and adjacency in the twisted arrangement

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.5 (the
category `P` before Proposition 2.20).

The colour-preserving permutations of the strands act on the chambers of the big arrangement
of positions and weights (`Twisted/Arrangement.lean`) by relabelling the strands, compatibly
with the action on the chambers of each fibre (`FullChamber.toTw_smul`). Two chambers adjacent
across a hyperplane are chambers of one fibre, adjacent there (`TwChamber.Adjacent.exists_toTw`):
one moves a strand of the hyperplane near a point of its facet, keeping the weights. In
particular crossing the diagonal `d` relabels by the transposition of its two strands
(`TwChamber.Adjacent.refl_smul`), as in a fixed fibre.

## Main results

* `TwChamber.Adjacent.exists_toTw`: adjacent chambers come from adjacent chambers of a fibre.
* `TwChamber.Adjacent.refl_smul`: crossing the diagonal `d` from `C` gives `d.refl • C`.
-/

namespace Categorification.WeightedKLR

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace Hyp

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem comap_withWeight (ϑ : Γ.E → 𝕜) (g : ColPerm ν) (x : Hyp Γ ν) :
    Hyp.comap (Γ := Γ.withWeight ϑ) g x = x.comap g := by
  rcases x with w | d <;> rfl

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem reverses_withWeight (ϑ : Γ.E → 𝕜) (g : ColPerm ν) (x : Hyp Γ ν) :
    Hyp.reverses (Γ := Γ.withWeight ϑ) g x = x.reverses g := by
  rcases x with w | d <;> rfl

end Hyp

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Relabelling acts on the sign vectors of a fibre as on those of the big arrangement. -/
theorem signMap_withWeight (ϑ : Γ.E → 𝕜) (g : ColPerm ν) (σ : Hyp Γ ν → Bool) :
    signMap (Γ := Γ.withWeight ϑ) g σ = signMap g σ := by
  funext x
  simp only [signMap, Hyp.comap_withWeight, Hyp.reverses_withWeight]

namespace TwChamber

instance : SMul (ColPerm ν) (TwChamber Γ ν) where
  smul g C := ⟨signMap g C.1, by
    obtain ⟨ϑ, C₀, rfl⟩ := C.exists_eq_toTw
    exact (g • C₀).toTw.2.imp fun z hz => ⟨hz.1, hz.2.trans (signMap_withWeight ϑ g C₀.1)⟩⟩

omit [DecidableEq I] in
theorem smul_apply (g : ColPerm ν) (C : TwChamber Γ ν) (x : Hyp Γ ν) :
    (g • C).1 x = if x.reverses g then !C.1 (x.comap g) else C.1 (x.comap g) := rfl

end TwChamber

namespace FullChamber

omit [DecidableEq I] in
/-- Relabelling commutes with viewing a chamber of a fibre in the big arrangement. -/
theorem toTw_smul {ϑ : Γ.E → 𝕜} (g : ColPerm ν) (C : FullChamber (Γ.withWeight ϑ) ν) :
    (g • C).toTw = g • C.toTw :=
  Subtype.ext (signMap_withWeight ϑ g C.1)

end FullChamber

namespace TwChamber

instance : MulAction (ColPerm ν) (TwChamber Γ ν) where
  one_smul C := by
    obtain ⟨ϑ, C₀, rfl⟩ := C.exists_eq_toTw
    rw [← FullChamber.toTw_smul, one_smul]
  mul_smul g h C := by
    obtain ⟨ϑ, C₀, rfl⟩ := C.exists_eq_toTw
    rw [← FullChamber.toTw_smul, ← FullChamber.toTw_smul, ← FullChamber.toTw_smul, mul_smul]

omit [DecidableEq I] in
theorem Adjacent.smul {C C' : TwChamber Γ ν} {h : Hyp Γ ν} (hh : C.Adjacent C' h)
    (g : ColPerm ν) : (g • C).Adjacent (g • C') (h.comap g⁻¹) := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [smul_apply, smul_apply, Hyp.comap_inv_comap]
    have := hh.1
    split_ifs <;> simpa using this
  · have hx' : x.comap g ≠ h := fun e => hx (by rw [← e, Hyp.comap_comap_inv])
    rw [smul_apply, smul_apply, hh.2 _ hx']

omit [DecidableEq I] in
theorem Adjacent.of_smul {C C' : TwChamber Γ ν} {h : Hyp Γ ν} (g : ColPerm ν)
    (hh : (g • C).Adjacent (g • C') h) : C.Adjacent C' (h.comap g) := by
  have := hh.smul g⁻¹
  rwa [inv_smul_smul, inv_smul_smul, inv_inv] at this

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Adjacent.apply_eq_not {C C' : TwChamber Γ ν} {h : Hyp Γ ν}
    (hh : C.Adjacent C' h) : C'.1 h = !C.1 h := by
  have := hh.1
  revert this
  cases C.1 h <;> cases C'.1 h <;> simp

end TwChamber

/-! ### Adjacent chambers lie in one fibre -/

namespace Hyp

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem twVal_lineMap (h : Hyp Γ ν) (z z' : Strand ν ⊕ Γ.E → 𝕜) (t : 𝕜) :
    h.twVal ((1 - t) • z + t • z') = (1 - t) * h.twVal z + t * h.twVal z' := by
  simp only [twVal, map_add, map_smul, smul_eq_mul]

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem twVal_add_smul (h : Hyp Γ ν) (z v : Strand ν ⊕ Γ.E → 𝕜) (t : 𝕜) :
    h.twVal (z + t • v) = h.twVal z + t * h.twVal v := by
  simp only [twVal, map_add, map_smul, smul_eq_mul]

/-- A strand of the hyperplane `h` whose coordinate appears in `h` with coefficient `1`. -/
def moving : Hyp Γ ν → Strand ν
  | .inl w => w.tgt
  | .inr d => d.snd

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem twVal_single_moving (h : Hyp Γ ν) :
    h.twVal (Pi.single (.inl h.moving) (1 : 𝕜)) = 1 := by
  rcases h with w | d
  · have hst : w.tgt ≠ w.src := fun e => w.2.2.2 e.symm
    simp [moving, hst]
  · have hst : d.snd ≠ d.fst := d.fst_ne_snd.symm
    simp [moving, hst]

end Hyp

namespace TwChamber

omit [DecidableEq I] in
/-- Two chambers adjacent across `h₀` share a point of `h₀` lying on no other hyperplane, on the
side of `C` of each of them. -/
theorem Adjacent.exists_facet {C C' : TwChamber Γ ν} {h₀ : Hyp Γ ν} (hC : Adjacent C C' h₀) :
    ∃ q : Strand ν ⊕ Γ.E → 𝕜, h₀.twVal q = 0 ∧
      ∀ h, h ≠ h₀ → h.twVal q ≠ 0 ∧ (0 < h.twVal q ↔ C.1 h = true) := by
  obtain ⟨z, hz, hs⟩ := C.2
  obtain ⟨z', hz', hs'⟩ := C'.2
  have key : ∀ h, C.1 h = C'.1 h ↔ (0 < h.twVal z ↔ 0 < h.twVal z') := by
    intro h
    rw [← hs, ← hs']
    simp [twSigns]
  obtain ⟨t, ht0, ht1, hq⟩ :=
    exists_zero_on_segment (hz h₀) (hz' h₀) fun hiff => hC.1 ((key h₀).2 hiff)
  refine ⟨(1 - t) • z + t • z', by rw [Hyp.twVal_lineMap]; exact hq, fun h hh => ?_⟩
  rw [Hyp.twVal_lineMap]
  have := convex_sign (hz h) ((key h).1 (hC.2 h hh)) ht0 ht1
  refine ⟨this.1, this.2.trans ?_⟩
  rw [← hs]
  simp [twSigns]

omit [DecidableEq I] in
/-- Two chambers adjacent across `h` are the chambers of two adjacent chambers of one fibre:
moving one strand of `h` near a point of its facet changes the side of `h` only, at fixed
weights. -/
theorem Adjacent.exists_toTw {C C' : TwChamber Γ ν} {h₀ : Hyp Γ ν} (hC : Adjacent C C' h₀) :
    ∃ (ϑ : Γ.E → 𝕜) (C₀ C₀' : FullChamber (Γ.withWeight ϑ) ν),
      C₀.toTw = C ∧ C₀'.toTw = C' ∧ C₀.Adjacent C₀' h₀ := by
  classical
  obtain ⟨q, hq0, hq⟩ := hC.exists_facet
  set v : Strand ν ⊕ Γ.E → 𝕜 := Pi.single (.inl h₀.moving) 1
  obtain ⟨t, ht0, -, ht⟩ := exists_pos_small (fun h : Hyp Γ ν => h.twVal q)
    (fun h => h.twVal v) (fun h => -h.twVal v)
  set ϑ : Γ.E → 𝕜 := q ∘ Sum.inr
  have e : ∀ s : 𝕜, Sum.elim ((q + s • v) ∘ Sum.inl) ϑ = q + s • v := by
    intro s
    funext c
    rcases c with c | c
    · rfl
    · simp [v, ϑ]
  -- the point `q + s • v`, for `s = ± t`, is generic with the signs of `C` off `h₀`
  have hval : ∀ s : 𝕜, |s| = t → ∀ h, h ≠ h₀ → h.twVal (q + s • v) ≠ 0 ∧
      (0 < h.twVal (q + s • v) ↔ C.1 h = true) := by
    intro s hst h hh
    rw [Hyp.twVal_add_smul]
    have hsmall : |s * h.twVal v| < |h.twVal q| := by
      rcases abs_choice s with e' | e'
      · rw [abs_mul, hst, ← abs_of_pos ht0, ← abs_mul]
        exact (ht h (hq h hh).1).1
      · have : s = -t := by linarith
        rw [this, neg_mul, ← mul_neg]
        exact (ht h (hq h hh).1).2
    have h1 := pos_add_iff_of_abs_lt (hq h hh).1 hsmall
    exact ⟨h1.2, h1.1.trans (hq h hh).2⟩
  have h0 : ∀ s : 𝕜, h₀.twVal (q + s • v) = s := by
    intro s
    rw [Hyp.twVal_add_smul, hq0, Hyp.twVal_single_moving, mul_one, zero_add]
  have hgen : ∀ s : 𝕜, s ≠ 0 → |s| = t →
      IsGeneric (Γ.withWeight ϑ) ((q + s • v) ∘ Sum.inl) := by
    intro s hs0 hst
    rw [← twGeneric_elim_iff, e]
    intro h
    by_cases hh : h = h₀
    · subst hh; rw [h0]; exact hs0
    · exact (hval s hst h hh).1
  have hsign : ∀ (s : 𝕜) (hs0 : s ≠ 0) (hst : |s| = t) (h : Hyp Γ ν),
      (FullChamber.ofPoint _ (hgen s hs0 hst)).1 h =
        if h = h₀ then decide (0 < s) else C.1 h := by
    intro s hs0 hst h
    change fullSigns (Γ := Γ.withWeight ϑ) ((q + s • v) ∘ Sum.inl) h = _
    rw [← twSigns_elim, e]
    change decide (0 < h.twVal (q + s • v)) = _
    split_ifs with hh
    · subst hh; rw [h0]
    · rw [Bool.eq_iff_iff, decide_eq_true_iff]; exact (hval s hst h hh).2
  obtain ⟨Cp, hp⟩ : ∃ Cp : FullChamber (Γ.withWeight ϑ) ν,
      ∀ h : Hyp Γ ν, Cp.1 h = if h = h₀ then true else C.1 h :=
    ⟨_, fun h => by rw [hsign t ht0.ne' (abs_of_pos ht0) h]; simp [ht0]⟩
  obtain ⟨Cm, hm⟩ : ∃ Cm : FullChamber (Γ.withWeight ϑ) ν,
      ∀ h : Hyp Γ ν, Cm.1 h = if h = h₀ then false else C.1 h :=
    have hm0 : -t ≠ 0 := neg_ne_zero.2 ht0.ne'
    have hmt : |-t| = t := by rw [abs_neg, abs_of_pos ht0]
    ⟨FullChamber.ofPoint _ (hgen (-t) hm0 hmt), fun h => by
      rw [hsign (-t) hm0 hmt h]
      simp [show ¬(0 < -t) by linarith]⟩
  have hadj : Cp.Adjacent Cm h₀ :=
    ⟨fun e => by have := (hp h₀).symm.trans (e.trans (hm h₀)); simp at this,
      fun (h : Hyp Γ ν) (hh : h ≠ h₀) => by
        have a := hp h
        have b := hm h
        simp only [hh, ↓reduceIte] at a b
        exact a.trans b.symm⟩
  have eq₁ : ∀ (Z : FullChamber (Γ.withWeight ϑ) ν) (D : TwChamber Γ ν),
      (∀ h, h ≠ h₀ → Z.1 h = D.1 h) → Z.1 h₀ = D.1 h₀ → Z.toTw = D := by
    intro Z D hZ hZ0
    apply Subtype.ext
    funext h
    by_cases hh : h = h₀
    · subst hh; exact hZ0
    · exact hZ h hh
  have hC' : ∀ h, h ≠ h₀ → C.1 h = C'.1 h := hC.2
  refine ⟨ϑ, ?_⟩
  cases hc : C.1 h₀
  · have hc' : C'.1 h₀ = true := by rw [hC.apply_eq_not, hc]; rfl
    refine ⟨Cm, Cp, eq₁ _ _ (fun h hh => by rw [hm]; simp [hh]) (by rw [hm, hc]; simp),
      eq₁ _ _ (fun h hh => by rw [hp, ← hC' h hh]; simp [hh]) (by rw [hp, hc']; simp),
      hadj.symm⟩
  · have hc' : C'.1 h₀ = false := by rw [hC.apply_eq_not, hc]; rfl
    refine ⟨Cp, Cm, eq₁ _ _ (fun h hh => by rw [hp]; simp [hh]) (by rw [hp, hc]; simp),
      eq₁ _ _ (fun h hh => by rw [hm, ← hC' h hh]; simp [hh]) (by rw [hm, hc']; simp), hadj⟩

/-- Crossing the diagonal `d` from the chamber `C` leads to `d.refl • C`. -/
theorem Adjacent.refl_smul {C C' : TwChamber Γ ν} {d : Diag ν} (hC : Adjacent C C' (.inr d)) :
    d.refl • C = C' := by
  obtain ⟨ϑ, C₀, C₀', rfl, rfl, h⟩ := hC.exists_toTw
  rw [← FullChamber.toTw_smul, h.refl_smul]

end TwChamber

end Categorification.WeightedKLR
