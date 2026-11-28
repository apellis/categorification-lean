/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721Induced
import Categorification.WeightedKLR.Rigidity.CupCapMidModule

/-!
# The appended loadings among the windows at the maximum

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for a cap not at the right end (`j < ℓ`). The unit `σ(1)` of the diagrams at
the maximum is the sum of the window idempotents of the loadings of `λ`
(`CupCap.midStendhal_one_eq_botMap`). Appending a black strand `i` to it gives the idempotent
`e'` of the appended loadings (`CupCap.appendBlackPlus_midStendhal_one`). Conversely, cutting
`σ(1)` at the black weight `{i} + ν` by the idempotent `e⁺ = appendBlack 1` of `T̃^{λ⁺}` keeps
exactly the loadings ending with a black strand `i`, i.e. the appended loadings
(`CupCap.midStendhal_one_mul_appendBlackPlus_one`): since `j < ℓ` the window lies left of the last
strand, which is therefore the last strand of the loading of `λ`.

## Main results

* `CupCap.appendPlus_midIdem`, `CupCap.appendBlackPlus_midStendhal_one`.
* `CupCap.midStendhal_one_mul_appendBlackPlus_one`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I} (ν : Multiset I) (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "σᵢ" => (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin (ℓ + 2)))
local notation "ρ" => stendhalWeight (ℓ + 2) (ν + ν₀)
local notation "ρᵢ" => stendhalWeight (ℓ + 2) (νᵢ + ν₀)

/-- The unit of the diagrams at the maximum is the sum of the window idempotents. -/
theorem midStendhal_one_eq_botMap (μ : Multiset I) :
    midStendhal j hj Q Λ Λc μ ν₀ 1 =
      botMap k Q Λ Λc j hj μ ν₀ (∑ s : Seq (stendhalWeight ℓ μ), midIdem j hj Q Λ Λc μ ν₀ s) := by
  rw [midStendhal_one_eq_midBot, midBot_apply, midMapKLR, map_sum, map_sum]
  exact Finset.sum_congr rfl fun s _ => botMap_insertMap_redOrderedKLR Q Λ Λc s _

/-- Appending the strand to a window idempotent, for `j < ℓ`. -/
theorem appendPlus_midIdem (h : j < ℓ) (t : Seq (stendhalWeight ℓ ν)) :
    appendPlus Q Λ Λc j hj ν ν₀ i (midIdem j hj Q Λ Λc ν ν₀ t) =
      midIdem j hj Q Λ Λc νᵢ ν₀ (appendBlackLoading i ν t) := by
  rw [midIdem, midIdem, ← insertMap_one Q Λ Λc t (midPos_le j t),
    appendPlus_insertMap t _ _ (midPos_le_appendBlackLoading j ν i t), insertMap_one]
  congr 2
  exact (midPos_appendBlackLoading j ν i h t).symm

/-- **Appending the strand to the unit of the diagrams at the maximum** gives `e'`, for
`j < ℓ`. -/
theorem appendBlackPlus_midStendhal_one (h : j < ℓ) :
    appendBlackPlus Q Λ Λc j hj ν ν₀ i (midStendhal j hj Q Λ Λc ν ν₀ 1) =
      appendIdemPlus Q Λ Λc j hj ν ν₀ i := by
  rw [midStendhal_one_eq_botMap, appendBlackPlus_botMap, map_sum, appendIdemPlus]
  congr 1
  exact Finset.sum_congr rfl fun t _ => appendPlus_midIdem ν i h t

theorem appendIdemPlus_mul_self (h : j < ℓ) :
    appendIdemPlus Q Λ Λc j hj ν ν₀ i * appendIdemPlus Q Λ Λc j hj ν ν₀ i =
      appendIdemPlus Q Λ Λc j hj ν ν₀ i := by
  rw [← appendBlackPlus_midStendhal_one ν i h, ← map_mul, ← map_mul, one_mul]

theorem appendIdemPlus_mul_midStendhal_one (h : j < ℓ) :
    appendIdemPlus Q Λ Λc j hj ν ν₀ i * midStendhal j hj Q Λ Λc νᵢ ν₀ 1 =
      appendIdemPlus Q Λ Λc j hj ν ν₀ i := by
  rw [← appendBlackPlus_midStendhal ν i h, appendBlackPlus_midStendhal_one ν i h]

theorem midStendhal_one_mul_appendIdemPlus (h : j < ℓ) :
    midStendhal j hj Q Λ Λc νᵢ ν₀ 1 * appendIdemPlus Q Λ Λc j hj ν ν₀ i =
      appendIdemPlus Q Λ Λc j hj ν ν₀ i := by
  rw [← (commute_appendIdemPlus ν i 1).eq, appendIdemPlus_mul_midStendhal_one ν i h]

section Last

omit [DecidableEq I] in
/-- The last strand of an appended loading of `λ⁺` is black of colour `i`. -/
theorem lbl_last_cast_append (w : Seq ρ) (c : Fin (Multiset.card ρᵢ))
    (hc : c.val + 1 = Multiset.card ρᵢ) :
    (Seq.cast (plusAddBlack ν ν₀ i) (w.append (default : Seq σᵢ))).lbl c = .inl i := by
  have hρ : Multiset.card ρᵢ = Multiset.card ρ + 1 := by
    rw [← congrArg Multiset.card (plusAddBlack ν ν₀ i), Multiset.card_add,
      Multiset.card_singleton]
  change (w.append (default : Seq σᵢ)).1 (Fin.cast _ c) = _
  rw [Seq.append_apply_ge _ _ _ (by simp only [Fin.val_cast]; omega)]
  exact Multiset.mem_singleton.mp ((default : Seq σᵢ).mem _)


omit [DecidableEq I] in
/-- A loading of `λ` at the black weight `{i} + ν` whose last strand is black of colour `i` is an
appended loading. -/
theorem exists_appendBlackLoading_eq (t : Seq (stendhalWeight ℓ νᵢ))
    (c : Fin (Multiset.card (stendhalWeight ℓ νᵢ)))
    (hc : c.val + 1 = Multiset.card (stendhalWeight ℓ νᵢ)) (ht : t.lbl c = .inl i) :
    ∃ s : Seq (stendhalWeight ℓ ν), appendBlackLoading i ν s = t := by
  classical
  have hw := stendhalWeight_addBlack (ℓ := ℓ) i ν
  have hσ : ∀ a ∈ (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin ℓ)), a = Sum.inl i :=
    fun a ha => Multiset.mem_singleton.mp ha
  have hcard := congrArg Multiset.card hw
  rw [Multiset.card_add, Multiset.card_singleton] at hcard
  have htail : Seq.HasTail (Sum.inl i) (Seq.cast hw.symm t)
      (Multiset.card (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin ℓ))) := by
    refine ⟨by simp, fun a ha => ?_⟩
    simp only [Multiset.card_add, Multiset.card_singleton] at ha
    rw [Seq.cast_apply]
    have : Fin.cast (congrArg Multiset.card hw.symm).symm a = c := Fin.ext (by
      have := a.2
      simp only [Multiset.card_add, Multiset.card_singleton] at this
      simp only [Fin.val_cast]
      omega)
    rw [this]
    exact ht
  obtain ⟨u, hu⟩ := Seq.exists_eq_append_const_of_hasTail hσ htail
  refine ⟨u, ?_⟩
  have hd : (default : Seq (Singleton.singleton (Sum.inl i) : Multiset (I ⊕ Fin ℓ))) =
      Seq.constSeq hσ := (Seq.uniqueOfForall hσ).uniq _
  rw [appendBlackLoading, hd, hu]
  apply Subtype.ext
  funext a
  rw [Seq.cast_apply, Seq.cast_apply, Fin.cast_cast, Fin.cast_eq_self]

/-- For `j < ℓ`, a window idempotent of a loading whose last strand is not black of colour `i`
vanishes against the appended idempotent `appendPlus 1`. -/
theorem midIdem_mul_appendPlus_one_of_lbl (h : j < ℓ) (t : Seq (stendhalWeight ℓ νᵢ))
    (c : Fin (Multiset.card (stendhalWeight ℓ νᵢ)))
    (hc : c.val + 1 = Multiset.card (stendhalWeight ℓ νᵢ)) (ht : t.lbl c ≠ .inl i) :
    midIdem j hj Q Λ Λc νᵢ ν₀ t * appendPlus Q Λ Λc j hj ν ν₀ i 1 = 0 := by
  obtain ⟨a, ha, -⟩ := midPos_of_lt j t h
  rw [midIdem, eSum_insertSet, ← KLRAlgebra.sum_e, map_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [appendPlus_e, KLRAlgebra.e_mul_e]
  split_ifs with heq
  swap
  · rfl
  exfalso
  have ha' := a.2
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := νᵢ) (ν₀ := ν₀)
  have h1 := insertSeq_lbl_old (j := j) (hj := hj) (ν₀ := ν₀) t (midPos j t) (midPos_le j t)
    (Seq.map (cupColour j hj) w) c
  rw [heq, lbl_last_cast_append ν i u _ (by
    simp only [Fin.val_cast, insertPos_inl_val, Multiset.card_map]; split_ifs <;> omega)] at h1
  cases hl : t.lbl c with
  | inl b =>
    rw [hl] at h1 ht
    simp only [oldColour, Sum.map_inl, id, Sum.inl.injEq] at h1
    exact ht (congrArg Sum.inl h1.symm)
  | inr r =>
    rw [hl] at h1
    simp [oldColour] at h1


/-- `e⁺ = appendBlack 1` in `T̃^{λ⁺}` is the image of `appendPlus 1`. -/
theorem appendBlackPlus_one :
    appendBlackPlus Q Λ Λc j hj ν ν₀ i 1 =
      botMap k Q Λ Λc j hj νᵢ ν₀ (appendPlus Q Λ Λc j hj ν ν₀ i 1) := by
  rw [← map_one (botMap k Q Λ Λc j hj ν ν₀), appendBlackPlus_botMap]

/-- **The appended loadings among the windows at the maximum** (arXiv:1309.3796v3, §7.3, proof
of Proposition 7.21), for `j < ℓ`: cutting the unit `σ(1)` of the diagrams at the maximum at the
black weight `{i} + ν` by `e⁺ = appendBlack 1` gives the idempotent `e'` of the appended
loadings. -/
theorem midStendhal_one_mul_appendBlackPlus_one (h : j < ℓ) :
    midStendhal j hj Q Λ Λc νᵢ ν₀ 1 * appendBlackPlus Q Λ Λc j hj ν ν₀ i 1 =
      appendIdemPlus Q Λ Λc j hj ν ν₀ i := by
  classical
  have hinj : Function.Injective (appendBlackLoading (ℓ := ℓ) i ν) := fun s t hst =>
    Subtype.ext (funext fun a => by
      have hm := card_appendBlackWeight (ℓ := ℓ) (ν := ν) (i := i)
      have h1 := appendBlackLoading_lbl_of_lt i ν s ⟨a.val, by omega⟩ a.2
      have h2 := appendBlackLoading_lbl_of_lt i ν t ⟨a.val, by omega⟩ a.2
      rw [hst, h2] at h1
      exact h1.symm)
  rw [midStendhal_one_eq_botMap, appendBlackPlus_one, ← map_mul, Finset.sum_mul, map_sum,
    appendIdemPlus, map_sum, ← Finset.sum_image (f := fun t =>
      botMap k Q Λ Λc j hj νᵢ ν₀ (midIdem j hj Q Λ Λc νᵢ ν₀ t)) fun a _ b _ hab => hinj hab]
  refine (Finset.sum_subset (Finset.subset_univ (Finset.univ.image (appendBlackLoading i ν)))
    fun t _ ht => ?_).symm.trans ?_
  · by_cases hord : IsRedOrdered t
    · have hm : 0 < Multiset.card (stendhalWeight ℓ νᵢ) := by
        rw [card_appendBlackWeight]; omega
      let c : Fin (Multiset.card (stendhalWeight ℓ νᵢ)) :=
        ⟨Multiset.card (stendhalWeight ℓ νᵢ) - 1, by omega⟩
      by_cases hl : t.lbl c = .inl i
      · obtain ⟨s, hs⟩ := exists_appendBlackLoading_eq ν i t c (Nat.sub_add_cancel hm) hl
        exact (ht (Finset.mem_image.2 ⟨s, Finset.mem_univ _, hs⟩)).elim
      · rw [midIdem_mul_appendPlus_one_of_lbl ν i h t c (Nat.sub_add_cancel hm) hl, map_zero]
    · rw [map_mul, midIdem, eSum_insertSet, map_sum, Finset.sum_eq_zero fun w _ =>
        botMap_e_of_not Q Λ Λc (fun h' => hord (isRedOrdered_of_insertSeq' _ h')), zero_mul]
  · refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 ht
    rw [← appendPlus_midIdem ν i h, ← map_mul, mul_one]

end Last

end Categorification.Stendhal.CupCap
