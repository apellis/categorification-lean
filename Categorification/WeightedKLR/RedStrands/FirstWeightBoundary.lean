/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Stendhal
import Mathlib.Order.Preorder.Finite

/-!
# Boundaries in the first lowering weight

Webster, arXiv:1309.3796v2, Definitions 4.1 and 4.3. With one black strand,
a nonviolated ordered boundary is specified by the red strand immediately to
its left. This is the prefix on which the first lowering operator acts in
the recursion for `pᵢ^κ` before Lemma 4.36.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR

variable {I : Type*} (i : I) (ℓ : ℕ)

local notation "μ" => stendhalWeight ℓ (Singleton.singleton i : Multiset I)

/-- The surviving ordered boundary words in black weight `αᵢ`. -/
abbrev Boundary := {s : Seq μ // IsRedOrdered s ∧ ¬ IsViolated s}

private theorem card_weight : Multiset.card μ = ℓ + 1 := by
  simp [stendhalWeight]

private abbrev standardPosition : Fin (Multiset.card μ) ≃ Fin (ℓ + 1) :=
  finCongr (card_weight i ℓ)

private def labels (p : Fin (ℓ + 1)) : Fin (ℓ + 1) → I ⊕ Fin ℓ :=
  Fin.insertNth p (Sum.inl i) Sum.inr

private theorem labels_weight (p : Fin (ℓ + 1)) :
    (Finset.univ.val.map (labels i ℓ p)) = μ := by
  rw [Fin.univ_succAbove ℓ p]
  change (p ::ₘ (Finset.univ.map (Fin.succAboveEmb p)).val).map (labels i ℓ p) = μ
  rw [Multiset.map_cons]
  simp only [Finset.map_val, Multiset.map_map, Function.comp_def, Fin.coe_succAboveEmb,
    labels, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rfl

private def wordAt (p : Fin (ℓ + 1)) : Seq μ :=
  ⟨labels i ℓ p ∘ standardPosition i ℓ, by
    rw [← Multiset.map_map]
    have h := congrArg Finset.val (Finset.map_univ_equiv (standardPosition i ℓ))
    rw [show Finset.univ.val.map (standardPosition i ℓ) = _ from h, labels_weight]⟩

private theorem wordAt_black (p : Fin (ℓ + 1)) :
    (wordAt i ℓ p).lbl ((standardPosition i ℓ).symm p) = .inl i := by
  change labels i ℓ p (standardPosition i ℓ ((standardPosition i ℓ).symm p)) = _
  rw [Equiv.apply_symm_apply, labels, Fin.insertNth_apply_same]

private theorem wordAt_red (p : Fin (ℓ + 1)) (r : Fin ℓ) :
    (wordAt i ℓ p).lbl ((standardPosition i ℓ).symm (p.succAbove r)) = .inr r := by
  change labels i ℓ p (standardPosition i ℓ ((standardPosition i ℓ).symm _)) = _
  rw [Equiv.apply_symm_apply, labels, Fin.insertNth_apply_succAbove]

private theorem wordAt_ordered (p : Fin (ℓ + 1)) : IsRedOrdered (wordAt i ℓ p) := by
  intro a b r r' hab ha hb
  have hex (a : Fin (Multiset.card μ)) (r : Fin ℓ) (ha : (wordAt i ℓ p).lbl a = .inr r) :
      standardPosition i ℓ a = p.succAbove r := by
    have hne : standardPosition i ℓ a ≠ p := by
      intro h
      rw [show a = (standardPosition i ℓ).symm p from (Equiv.eq_symm_apply _).mpr h,
        wordAt_black] at ha
      contradiction
    obtain ⟨r₀, hr₀⟩ := Fin.exists_succAbove_eq hne
    have hpos := (Equiv.eq_symm_apply (standardPosition i ℓ)).2 hr₀.symm
    rw [hpos, wordAt_red] at ha
    rw [Sum.inr.inj ha] at hr₀
    exact hr₀.symm
  have hpos : standardPosition i ℓ a < standardPosition i ℓ b := hab
  rw [hex a r ha, hex b r' hb] at hpos
  exact (Fin.strictMono_succAbove _).lt_iff_lt.mp hpos

private theorem wordAt_notViolated (r : Fin ℓ) : ¬ IsViolated (wordAt i ℓ r.succ) := by
  rintro ⟨h, hb⟩
  have hp : (⟨0, h⟩ : Fin (Multiset.card μ)) ≠ (standardPosition i ℓ).symm r.succ := by
    intro he
    have hz := congrArg Fin.val he
    change 0 = r.val + 1 at hz
    omega
  have hs : standardPosition i ℓ ⟨0, h⟩ ≠ r.succ := fun he =>
    hp ((Equiv.eq_symm_apply _).mpr he)
  obtain ⟨s, hs⟩ := Fin.exists_succAbove_eq hs
  have hz := (Equiv.eq_symm_apply (standardPosition i ℓ)).2 hs.symm
  rw [hz, wordAt_red] at hb
  exact Bool.noConfusion hb

/-- Place the first black strand immediately after red strand `r`. -/
def boundaryAt (r : Fin ℓ) : Boundary i ℓ :=
  ⟨wordAt i ℓ r.succ, wordAt_ordered i ℓ r.succ, wordAt_notViolated i ℓ r⟩

@[simp] theorem boundaryAt_lbl_black (r : Fin ℓ) :
    (boundaryAt i ℓ r).1.lbl ⟨r.val + 1, by rw [card_weight]; exact r.succ.isLt⟩ = .inl i :=
  wordAt_black i ℓ r.succ

private theorem lbl_injective (s : Seq μ) : Function.Injective s.lbl := by
  classical
  have hnodup : (Finset.univ.val.map s.lbl).Nodup := by
    rw [show Finset.univ.val.map s.lbl = μ from s.2]
    simp [stendhalWeight, List.nodup_ofFn, Sum.inr_injective]
  exact fun a b h => Multiset.inj_on_of_nodup_map hnodup a (by simp) b (by simp) h

private theorem word_eq (s : Seq μ) (hs : IsRedOrdered s) (p : Fin (ℓ + 1))
    (hb : s.lbl ((standardPosition i ℓ).symm p) = .inl i) : s = wordAt i ℓ p := by
  have hred (r : Fin ℓ) : ∃ t, s.lbl ((standardPosition i ℓ).symm (p.succAbove r)) = .inr t := by
    cases h : s.lbl ((standardPosition i ℓ).symm (p.succAbove r)) with
    | inr t => exact ⟨t, rfl⟩
    | inl j =>
      have hj : j = i := by
        have hm := s.mem ((standardPosition i ℓ).symm (p.succAbove r))
        rw [show s.1 _ = .inl j from h] at hm
        simpa [stendhalWeight] using hm
      subst j
      exact ((Fin.succAbove_ne _ _) ((standardPosition i ℓ).symm.injective
        (lbl_injective i ℓ s (h.trans hb.symm)))).elim
  choose f hf using hred
  have hfm : StrictMono f := fun _ _ h => hs _ _ _ _
    (by exact Fin.strictMono_succAbove p h) (hf _) (hf _)
  have hfid : f = id := hfm.eq_id
  apply Subtype.ext
  funext a
  change s.lbl a = (wordAt i ℓ p).lbl a
  by_cases h : standardPosition i ℓ a = p
  · rw [(Equiv.eq_symm_apply _).mpr h, hb, wordAt_black]
  · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq h
    have hz := (Equiv.eq_symm_apply (standardPosition i ℓ)).2 hr.symm
    rw [hz, hf r, wordAt_red, hfid, id_eq]

/-- The final red strand in the prefix ending at the black strand, as used
in Webster's recursion for the vectors `pᵢ^κ`. -/
def boundaryEquiv : Fin ℓ ≃ Boundary i ℓ :=
  Equiv.ofBijective (boundaryAt i ℓ) ⟨by
    intro r t h
    apply Fin.succ_injective _
    apply (standardPosition i ℓ).symm.injective
    apply lbl_injective i ℓ (boundaryAt i ℓ r).1
    have he : wordAt i ℓ r.succ = wordAt i ℓ t.succ := congrArg Subtype.val h
    change (wordAt i ℓ r.succ).lbl _ = (wordAt i ℓ r.succ).lbl _
    rw [wordAt_black, he, wordAt_black], by
    intro s
    have hb : Sum.inl i ∈ Finset.univ.val.map s.1.lbl := by
      rw [show Finset.univ.val.map s.1.lbl = μ from s.1.2]
      simp [stendhalWeight]
    obtain ⟨a, _, ha⟩ := Multiset.mem_map.1 hb
    have hano : a.val ≠ 0 := fun h => s.2.2 ⟨by rw [card_weight]; omega, by
      rw [show (⟨0, by rw [card_weight]; omega⟩ : Fin (Multiset.card μ)) = a from Fin.ext h.symm, ha]
      rfl⟩
    let p := standardPosition i ℓ a
    let r := p.pred (by intro h; exact hano (congrArg Fin.val h))
    have hr : r.succ = p := Fin.succ_pred _ _
    refine ⟨r, Subtype.ext ?_⟩
    change wordAt i ℓ r.succ = s.1
    rw [hr]
    exact (word_eq i ℓ s.1 s.2.1 p (by simpa [p] using ha)).symm⟩

@[simp] theorem boundaryEquiv_apply (r : Fin ℓ) :
    boundaryEquiv i ℓ r = boundaryAt i ℓ r := rfl

end Categorification.Stendhal.FirstWeight
