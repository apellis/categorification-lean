/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedShuffle
import Categorification.KLR.GradedBasis
import Categorification.WeightedKLR.RedStrands.ParabolicAffineQuotients

/-!
# Black content to the left of a shuffled last red

The first strand in the second input of a partial standardization is its
last red. Every position to the left of it in a shuffle therefore comes
from the earlier red block.
-/
namespace Categorification.Stendhal
open KLR TypeA Equiv

theorem shuffle_before_right_zero {n r m : ℕ} (h : n+r=m) (u : Shuffle h) (hr : 0 < r)
    {p q : Fin m} (hp : u.1 p = blockEquiv h (.inr ⟨0,hr⟩)) (hq : q < p) :
    ∃ x : Fin n, u.1 q = blockEquiv h (.inl x) := by
  obtain ⟨z,hz⟩ := (blockEquiv h).surjective (u.1 q)
  cases z with
  | inl x => exact ⟨x,hz.symm⟩
  | inr y =>
    have hh := u.2.2.monotone (show (⟨0,hr⟩ : Fin r) ≤ y from Nat.zero_le _)
    have hinv (t : Fin m) : u.1⁻¹ (u.1 t) = t := u.1.symm_apply_apply t
    rw [← hp, hz, hinv, hinv] at hh
    exact (not_le_of_gt hq hh).elim

/-- Any family of black positions supported to the left of the first
strand of the second input has content bounded by that of the first input. -/
theorem shuffle_black_content_le {I : Type*} [DecidableEq I] {ℓ : ℕ} {θ θ' : Multiset I}
    {δ : Multiset (Fin ℓ)} {β : Multiset (I ⊕ Fin ℓ)}
    (a : KLR.Seq (θ.map Sum.inl + δ.map Sum.inr)) (b : KLR.Seq β)
    {s : KLR.Seq (θ.map Sum.inl + δ.map Sum.inr + β)}
    (u : Shuffle (Seq.card_add' (θ.map Sum.inl + δ.map Sum.inr) β)) (hu : u.1 • s = a.append b)
    (hr : 0 < β.card) {p : Fin (θ.map Sum.inl + δ.map Sum.inr + β).card}
    (hp : u.1 p = Seq.posR _ ⟨0,hr⟩) (z : KLR.Seq θ')
    (g : Fin θ'.card ↪ Fin (θ.map Sum.inl + δ.map Sum.inr + β).card)
    (hbefore : ∀ q, g q < p) (hcol : ∀ q, s.lbl (g q) = .inl (z.lbl q)) :
    θ' ≤ θ := by
  classical
  choose pos hpos using fun q => shuffle_before_right_zero _ u hr hp (hbefore q)
  have hinj : Function.Injective pos := by
    intro x y hh
    apply g.injective
    apply u.1.injective
    rw [hpos, hpos, hh]
  have hlabel (q) : a.lbl (pos q) = .inl (z.lbl q) := by
    have he := congrArg (fun t => Seq.lbl t (u.1 (g q))) hu
    change s.lbl (u.1.symm (u.1 (g q))) = (a.append b).1 (u.1 (g q)) at he
    rw [Equiv.symm_apply_apply, hpos] at he
    have hx := Seq.append_posL a b (pos q)
    exact hx.symm.trans (he.symm.trans (hcol q))
  apply Multiset.le_iff_count.mpr
  intro i
  have hcount : Multiset.count (Sum.inl i : I ⊕ Fin ℓ) (θ.map Sum.inl + δ.map Sum.inr) = θ.count i := by
    simp [Multiset.count_map_eq_count' Sum.inl _ Sum.inl_injective]
  rw [← hcount, KL1.count_eq_card z i, KL1.count_eq_card a (.inl i)]
  apply Finset.card_le_card_of_injOn pos
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hlabel x).trans (congrArg Sum.inl (Finset.mem_filter.mp hx).2)⟩
  · exact hinj.injOn

/-- At an ordered cut, the black labels of its prefix form a submultiset
of the earlier input. The map `g` includes all prefix positions into the
output loading, including the red positions. -/
theorem shuffle_cut_content_le {I : Type*} [DecidableEq I] {ℓ : ℕ} {θ θ' : Multiset I}
    {δ δ' : Multiset (Fin ℓ)} {β : Multiset (I ⊕ Fin ℓ)}
    (a : KLR.Seq (θ.map Sum.inl + δ.map Sum.inr)) (b : KLR.Seq β)
    {s : KLR.Seq (θ.map Sum.inl + δ.map Sum.inr + β)}
    (u : Shuffle (Seq.card_add' (θ.map Sum.inl + δ.map Sum.inr) β)) (hu : u.1 • s = a.append b)
    (hr : 0 < β.card) {p : Fin (θ.map Sum.inl + δ.map Sum.inr + β).card}
    (hp : u.1 p = Seq.posR _ ⟨0,hr⟩) (w : KLR.Seq (θ'.map Sum.inl + δ'.map Sum.inr))
    (g : Fin (θ'.map Sum.inl + δ'.map Sum.inr).card ↪ Fin (θ.map Sum.inl + δ.map Sum.inr + β).card)
    (hbefore : ∀ j i, w.lbl j = .inl i → g j < p) (hcol : ∀ j, s.lbl (g j) = w.lbl j) :
    θ' ≤ θ := by
  classical
  apply Multiset.le_iff_count.mpr
  intro i
  have hc {η : Multiset I} (Δ : Multiset (Fin ℓ)) :
      Multiset.count (Sum.inl i : I ⊕ Fin ℓ) (η.map Sum.inl + Δ.map Sum.inr) = η.count i := by
    simp [Multiset.count_map_eq_count' Sum.inl _ Sum.inl_injective]
  rw [← hc δ', ← hc δ, KL1.count_eq_card w, KL1.count_eq_card a]
  let U := Finset.univ.filter (fun j => w.lbl j = Sum.inl i)
  let V := Finset.univ.filter (fun j => a.lbl j = Sum.inl i)
  have hi (j : U) : w.lbl j.val = Sum.inl i := (Finset.mem_filter.mp j.2).2
  choose pos hpos using fun j : U => shuffle_before_right_zero _ u hr hp (hbefore j.val i (hi j))
  have hmem (j : U) : pos j ∈ V := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h1 := congrArg (fun t => Seq.lbl t (u.1 (g j.val))) hu
    change s.lbl (u.1.symm (u.1 (g j.val))) = (a.append b).1 (u.1 (g j.val)) at h1
    rw [Equiv.symm_apply_apply, hpos] at h1
    exact (Seq.append_posL a b _).symm.trans (h1.symm.trans ((hcol _).trans (hi j)))
  have hinj : Function.Injective (fun j : U => (⟨pos j,hmem j⟩ : V)) := by
    intro x y hxy
    apply Subtype.ext
    apply g.injective
    apply u.1.injective
    rw [hpos, hpos, show pos x = pos y from congrArg Subtype.val hxy]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ hinj

/-- A prefix of a shuffled loading preceding the first position of the
second input has weight bounded by that of the first input. -/
theorem shuffle_prefix_weight_le {J : Type*} [DecidableEq J] {α δ α' δ' : Multiset J}
    (H : α'+δ'=α+δ) (a : Seq α) (b : Seq δ) (a' : Seq α') (b' : Seq δ')
    (u : Shuffle (Seq.card_add' α δ)) (hu : u.1 • Seq.cast H (a'.append b') = a.append b)
    (hr : 0 < δ.card) {p : Fin (α+δ).card} (hp : u.1 p = Seq.posR α ⟨0,hr⟩)
    (hcut : α'.card ≤ p.val) : α' ≤ α := by
  classical
  let s := Seq.cast H (a'.append b')
  let g (j : Fin α'.card) := Fin.cast (congrArg Multiset.card H) (Seq.posL δ' j)
  have hg (j : Fin α'.card) : g j < p := (show j.val < p.val from lt_of_lt_of_le j.isLt hcut)
  choose f hf using fun j => shuffle_before_right_zero _ u hr hp (hg j)
  have hlabel (j : Fin α'.card) : a.lbl (f j) = a'.lbl j := by
    have he := congrArg (fun t => Seq.lbl t (u.1 (g j))) hu
    change s.lbl (u.1.symm (u.1 (g j))) = (a.append b).1 (u.1 (g j)) at he
    rw [Equiv.symm_apply_apply, hf j] at he
    exact (Seq.append_posL a b _).symm.trans (he.symm.trans (Seq.append_posL a' b' j))
  have hinj : Function.Injective f := by
    intro i j hij
    have hh := u.1.injective ((hf i).trans ((congrArg (fun z => blockEquiv _ (.inl z)) hij).trans (hf j).symm))
    exact Fin.ext (congrArg (fun z : Fin (α+δ).card => z.val) hh)
  apply Multiset.le_iff_count.mpr
  intro i
  rw [KL1.count_eq_card a' i, KL1.count_eq_card a i]
  exact Finset.card_le_card_of_injOn f (fun j hj => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (hlabel j).trans (Finset.mem_filter.mp hj).2⟩) hinj.injOn

private abbrev pref {I : Type*} (n : ℕ) (v : Multiset I) := (stendhalWeight n v).map (addRedColor n)
private abbrev lastWt {I : Type*} (n : ℕ) (v : Multiset I) :=
  (stendhalWeight 1 v).map (Sum.map id (fun _ : Fin 1 => Fin.last n))

/-- If a second cut of a standardization has a compatible shuffle, its
earlier black content is bounded by the original earlier black content. -/
theorem parabolicShuffle_cut_le {I : Type*} [DecidableEq I] {ℓ : ℕ} {θ β θ' β' : Multiset I}
    (H : pref ℓ θ' + lastWt ℓ β' = pref ℓ θ + lastWt ℓ β)
    (a : Seq (pref ℓ θ)) (b : Seq (lastWt ℓ β)) (a' : Seq (pref ℓ θ')) (b' : Seq (lastWt ℓ β'))
    (u : Shuffle (Seq.card_add' (pref ℓ θ) (lastWt ℓ β)))
    (hu : u.1 • Seq.cast H (a'.append b') = a.append b)
    (p : Fin (pref ℓ θ + lastWt ℓ β).card)
    (hp : (Seq.cast H (a'.append b')).lbl p = .inr (Fin.last ℓ))
    (hu0 : u.1 p = Seq.posR (pref ℓ θ) ⟨0, by simp [lastWt, stendhalWeight]⟩) : θ' ≤ θ := by
  have hc : (pref ℓ θ').card ≤ p.val := by
    by_contra! hl
    let z := Fin.cast (congrArg Multiset.card H).symm p
    have hy := Seq.append_apply_lt a' b' z hl
    exact (lt_irrefl _ (parabolicPrefix_red_lt_last θ' a' _ (hy.symm.trans hp)))
  have hh := shuffle_prefix_weight_le H a b a' b' u hu _ hu0 hc
  have cnt (v : Multiset I) (i : I) : (pref ℓ v).count (.inl i) = v.count i := by
    change Multiset.count (addRedColor ℓ (.inl i)) _ = _
    rw [Multiset.count_map_eq_count' _ _ (Sum.map_injective.mpr ⟨Function.injective_id, Fin.castSucc_injective _⟩)]
    simp [stendhalWeight, Multiset.count_map_eq_count' Sum.inl _ Sum.inl_injective]
  exact Multiset.le_iff_count.mpr fun i => (cnt θ' i) ▸ (cnt θ i) ▸ Multiset.le_iff_count.mp hh (.inl i)

end Categorification.Stendhal
