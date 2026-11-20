/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.MatEndMap
import Categorification.WeightedKLR.RedStrands.DoubleDownBlackAppend
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackAction
import Categorification.WeightedKLR.RedStrands.BlackAffineProjection

/-!
# The matrix map of `Fᵢ` on the all-down block

Webster, arXiv:1309.3796v3, §4.6, the module functors `Fᵢ` after Theorem 4.31. The action of
the Khovanov–Lauda word `Fᵢ` sends the all-down boundary of a loading `s` to the all-down
boundary of `s` followed by `i`. Applied entrywise, it gives a homomorphism of non-unital
algebras from the all-down matrix algebra at black content `ν` to the one at `{i} + ν`
(`blackMatrix`). It sends the boundary idempotent of `s` to that of the appended loading, and
the dot and crossing matrices to the same matrices of the larger content, cut down by the image
of `1`.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLR.Diagram KL3.Diagram
  TypeA
open scoped Classical

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

instance blackAct_linear {μ ν : X} (s : List (Letter I)) (hs : wt RD μ s = ν) :
    (blackAct P s hs).Linear k := by
  unfold blackAct violatingWhiskerRight
  infer_instance

section Loading

variable (i : I) (ν : Multiset I)

theorem card_stendhalWeight_cons :
    Multiset.card (stendhalWeight ℓ ({i} + ν)) = Multiset.card (stendhalWeight ℓ ν) + 1 := by
  simp [stendhalWeight]

/-- A position of the old loading, as a position of the appended loading. -/
def appendPos (a : Fin (Multiset.card (stendhalWeight ℓ ν))) :
    Fin (Multiset.card (stendhalWeight ℓ ({i} + ν))) :=
  ⟨a.val, by rw [card_stendhalWeight_cons]; omega⟩

theorem appendBlackLoading_lbl_appendPos (s : Seq (stendhalWeight ℓ ν))
    (a : Fin (Multiset.card (stendhalWeight ℓ ν))) :
    (appendBlackLoading i ν s).lbl (appendPos i ν a) = s.lbl a :=
  appendBlackLoading_lbl_of_lt i ν s _ a.isLt

theorem appendBlackLoading_injective :
    Function.Injective (appendBlackLoading (ℓ := ℓ) i ν) := by
  intro s t h
  apply Subtype.ext
  funext a
  have := congrArg (fun s => s.lbl (appendPos i ν a)) h
  simpa only [appendBlackLoading_lbl_appendPos] using this

theorem word_appendBlackLoading (s : Seq (stendhalWeight ℓ ν)) :
    word (appendBlackLoading i ν s) = word s ++ [.inl i] :=
  ofFn_appendBlackLoading i ν s

/-- Appending a black strand on the right commutes with adjacent swaps of the old positions. -/
theorem appendBlackLoading_sadj (s : Seq (stendhalWeight ℓ ν)) {j : ℕ}
    (hj : j + 1 < Multiset.card (stendhalWeight ℓ ν)) :
    appendBlackLoading i ν (sadj (Multiset.card (stendhalWeight ℓ ν)) j • s) =
      sadj (Multiset.card (stendhalWeight ℓ ({i} + ν))) j • appendBlackLoading i ν s := by
  have hj' : j + 1 < Multiset.card (stendhalWeight ℓ ({i} + ν)) := by
    rw [card_stendhalWeight_cons]; omega
  apply Subtype.ext
  funext a
  change (appendBlackLoading i ν (sadj _ j • s)).lbl a =
    (appendBlackLoading i ν s).lbl ((sadj _ j)⁻¹ a)
  rw [sadj_inv]
  by_cases ha : a.val < Multiset.card (stendhalWeight ℓ ν)
  · have hsa : (sadj _ j a).val < Multiset.card (stendhalWeight ℓ ν) := by
      rw [sadj_val_of_lt hj']; unfold swapNat; split_ifs <;> omega
    rw [appendBlackLoading_lbl_of_lt i ν _ a ha, appendBlackLoading_lbl_of_lt i ν _ _ hsa]
    change s.lbl ((sadj _ j)⁻¹ _) = _
    rw [sadj_inv]
    congr 1
    ext
    rw [sadj_val_of_lt hj, sadj_val_of_lt hj']
  · have ha' : a.val = Multiset.card (stendhalWeight ℓ ν) := by
      have := a.isLt; have := card_stendhalWeight_cons (ℓ := ℓ) i ν; omega
    rw [sadj_apply_of_ne a (by omega) (by omega), appendBlackLoading_lbl_of_eq i ν _ a ha',
      appendBlackLoading_lbl_of_eq i ν _ a ha']

end Loading

section Matrix

variable (i : I) {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "Ord" => {s : Seq μ // IsRedOrdered s}
local notation "F" => blackAct P [(false, i)] (wt_downRightWeight i ν)

theorem appendDown_injective : Function.Injective (appendDown (ℓ := ℓ) i (ν := ν)) := by
  intro s t h
  exact Subtype.ext (appendBlackLoading_injective i ν (congrArg Subtype.val h))

/-- The action of `Fᵢ` on the all-down matrix algebra, as a homomorphism of non-unital
algebras (Webster, arXiv:1309.3796v3, §4.6, after Theorem 4.31). -/
def blackMatrix : downwardMatrix P ν →ₙₐ[k] downwardMatrix P ({i} + ν) :=
  MatEnd.mapEmbHom k F (appendDown_injective i) (blackAct_downObj P i)

theorem blackMatrix_apply (f : downwardMatrix P ν) :
    blackMatrix P i f = MatEnd.mapEmb F (blackAct_downObj P i) f := rfl

theorem blackMatrix_downE (s : Seq μ) :
    blackMatrix P i (downE P s) = downE P (appendBlackLoading i ν s) := by
  by_cases hs : IsRedOrdered s
  · rw [downE_of_ordered P ⟨s, hs⟩, blackMatrix_apply, MatEnd.mapEmb_single, MatEnd.conjF_id]
    exact (downE_of_ordered P (appendDown i ⟨s, hs⟩)).symm
  · rw [downE_of_unordered P s hs, map_zero, downE_of_unordered P _
      (fun h => hs ((appendBlackLoading_ordered_iff i ν s).mp h))]

theorem appendDown_lbl_appendPos (s : Ord) (a : Fin m) :
    (appendDown i s).val.lbl (appendPos i ν a) = s.val.lbl a :=
  appendBlackLoading_lbl_appendPos i ν s.val a

theorem downLayer_congr {ν' : Multiset I}
    (s t : {s : Seq (stendhalWeight ℓ ν') // IsRedOrdered s})
    {u u' v v' : List (DoubleStrand I ℓ)} (g : Move I ℓ) (hu : u = u') (hv : v = v')
    (hs ht hs' ht') :
    downLayer P s t u g v hs ht = downLayer P s t u' g v' hs' ht' := by
  subst hu hv
  rfl

theorem conjF_downLayer (s t : Ord) (u : List (DoubleStrand I ℓ)) (g : Move I ℓ)
    (v : List (DoubleStrand I ℓ))
    (hs : u ++ g.bottom ++ v = (word s.val).map DoubleStrand.down)
    (ht : u ++ g.top ++ v = (word t.val).map DoubleStrand.down) :
    MatEnd.conjF F (blackAct_downObj P i) (downLayer P s t u g v hs ht) =
      downLayer P (appendDown i s) (appendDown i t) u g (v ++ [.inl (false, i)])
        (by rw [word_appendDown, ← hs]; simp only [List.append_assoc])
        (by rw [word_appendDown, ← ht]; simp only [List.append_assoc]) := by
  unfold MatEnd.conjF
  rw [blackAct_downLayer]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Category.comp_id]

theorem take_word_appendDown (s : Ord) {n : ℕ} (hn : n ≤ m) :
    (word (appendDown i s).val).take n = (word s.val).take n := by
  rw [word_appendBlackLoading, List.take_append_of_le_length (by simpa using hn)]

theorem drop_word_appendDown (s : Ord) {n : ℕ} (hn : n ≤ m) :
    ((word (appendDown i s).val).drop n).map DoubleStrand.down =
      ((word s.val).drop n).map DoubleStrand.down ++ [.inl (false, i)] := by
  rw [word_appendBlackLoading, List.drop_append_of_le_length (by simpa using hn),
    List.map_append]
  rfl

/-- `Fᵢ` sends the dot on an old black strand to the dot on the same strand. -/
theorem conjF_downDot (s : Ord) (a : Fin m) :
    MatEnd.conjF F (blackAct_downObj P i) (downDot P s a) =
      downDot P (appendDown i s) (appendPos i ν a) := by
  rcases h : s.val.lbl a with i' | r
  · have h' : (appendDown i s).val.lbl (appendPos i ν a) = .inl i' := by
      rw [appendDown_lbl_appendPos, h]
    rw [downDot_of_black P s a i' h, downDot_of_black P _ _ i' h']
    unfold downBlackDot
    dsimp only
    refine (conjF_downLayer P i _ _ _ _ _ _ _).trans ?_
    exact downLayer_congr P _ _ _
      (by rw [show ((appendPos i ν a : ℕ)) = a from rfl,
        take_word_appendDown i s (Nat.le_of_lt a.isLt)])
      (drop_word_appendDown i s a.isLt).symm _ _ _ _
  · have h' : ((appendDown i s).val.lbl (appendPos i ν a)).isRight := by
      rw [appendDown_lbl_appendPos, h]; rfl
    rw [downDot_eq_zero_of_red P s a (by rw [h]; rfl), downDot_eq_zero_of_red P _ _ h',
      MatEnd.conjF_zero]

theorem downCross_of_not_adj {ν' : Multiset I}
    (s t : {s : Seq (stendhalWeight ℓ ν') // IsRedOrdered s}) (j : ℕ)
    (ht : t.val ≠ sadj (Multiset.card (stendhalWeight ℓ ν')) j • s.val) :
    downCross P s t j = 0 := by
  unfold downCross
  split_ifs <;> rfl

theorem downCross_of_none {ν' : Multiset I}
    (s t : {s : Seq (stendhalWeight ℓ ν') // IsRedOrdered s}) (j : ℕ)
    (hj : j + 1 < Multiset.card (stendhalWeight ℓ ν'))
    (hg : downCrossMove (s.val.lbl ⟨j, by omega⟩) (s.val.lbl ⟨j + 1, hj⟩) = none) :
    downCross P s t j = 0 := by
  unfold downCross
  rw [dite_eq_left hj]
  split_ifs
  · split
    · rfl
    · rename_i g hg'
      rw [hg] at hg'
      cases hg'
  · rfl

/-- `Fᵢ` sends a crossing of two old strands to the same crossing. -/
theorem conjF_downCross (s t : Ord) {j : ℕ} (hj : j + 1 < m) :
    MatEnd.conjF F (blackAct_downObj P i) (downCross P s t j) =
      downCross P (appendDown i s) (appendDown i t) j := by
  have hj' : j + 1 < Multiset.card (stendhalWeight ℓ ({i} + ν)) := by
    rw [card_stendhalWeight_cons]; omega
  by_cases ht : t.val = sadj m j • s.val
  · have ht' : (appendDown i t).val =
        sadj (Multiset.card (stendhalWeight ℓ ({i} + ν))) j • (appendDown i s).val := by
      change appendBlackLoading i ν t.val = _
      rw [ht]
      exact appendBlackLoading_sadj i ν s.val hj
    have hl0 : (appendDown i s).val.lbl ⟨j, by omega⟩ = s.val.lbl ⟨j, by omega⟩ :=
      appendDown_lbl_appendPos i s ⟨j, by omega⟩
    have hl1 : (appendDown i s).val.lbl ⟨j + 1, hj'⟩ = s.val.lbl ⟨j + 1, hj⟩ :=
      appendDown_lbl_appendPos i s ⟨j + 1, hj⟩
    rcases hg : downCrossMove (s.val.lbl ⟨j, by omega⟩) (s.val.lbl ⟨j + 1, hj⟩) with _ | g
    · rw [downCross_of_none P s t j hj hg,
        downCross_of_none P _ _ j hj' (by rw [hl0, hl1]; exact hg), MatEnd.conjF_zero]
    · rw [downCross_of_move P s t j hj ht g hg,
        downCross_of_move P _ _ j hj' ht' g (by rw [hl0, hl1]; exact hg)]
      unfold downCrossLayer
      dsimp only
      refine (conjF_downLayer P i _ _ _ _ _ _ _).trans ?_
      exact downLayer_congr P _ _ _ (by rw [take_word_appendDown i s (by omega)])
        (drop_word_appendDown i s (by omega)).symm _ _ _ _
  · have ht' : (appendDown i t).val ≠
        sadj (Multiset.card (stendhalWeight ℓ ({i} + ν))) j • (appendDown i s).val := by
      intro h
      rw [← appendBlackLoading_sadj i ν s.val hj] at h
      exact ht (appendBlackLoading_injective i ν h)
    rw [downCross_of_not_adj P s t j ht, downCross_of_not_adj P _ _ j ht', MatEnd.conjF_zero]

/-- A crossing from an appended loading lands in an appended loading. -/
theorem downCross_appendDown_of_not_mem (s : Ord)
    (b : {s : Seq (stendhalWeight ℓ ({i} + ν)) // IsRedOrdered s})
    (hb : ∀ t, appendDown i t ≠ b)
    {j : ℕ} (hj : j + 1 < m) : downCross P (appendDown i s) b j = 0 := by
  by_cases ht :
    b.val = sadj (Multiset.card (stendhalWeight ℓ ({i} + ν))) j • (appendDown i s).val
  · exfalso
    have hb' : b.val = appendBlackLoading i ν (sadj m j • s.val) := by
      rw [ht]
      exact (appendBlackLoading_sadj i ν s.val hj).symm
    have ho : IsRedOrdered (sadj m j • s.val) :=
      (appendBlackLoading_ordered_iff i ν _).mp (hb' ▸ b.property)
    exact hb ⟨_, ho⟩ (Subtype.ext hb'.symm)
  · exact downCross_of_not_adj P _ _ j ht

/-- The image of the dot at an old position is the dot at the same position, cut down by the
image of `1`. -/
theorem blackMatrix_downX (a : Fin m) :
    blackMatrix P i (downX P a) = downX P (appendPos i ν a) * blackMatrix P i 1 := by
  ext x y
  rw [blackMatrix_apply, blackMatrix_apply]
  by_cases hx : ∃ s, appendDown i s = x
  · obtain ⟨s, rfl⟩ := hx
    rw [MatEnd.mul_mapEmb_one_apply_emb F (appendDown_injective i) (blackAct_downObj P i) _ s y]
    by_cases hy : ∃ t, appendDown i t = y
    · obtain ⟨t, rfl⟩ := hy
      rw [MatEnd.mapEmb_apply_emb F (appendDown_injective i) (blackAct_downObj P i)]
      by_cases hst : s = t
      · subst hst
        rw [downX_apply_self, downX_apply_self, conjF_downDot]
      · rw [downX_apply_of_ne P a hst, MatEnd.conjF_zero,
          downX_apply_of_ne P _ (fun h => hst (appendDown_injective i h))]
    · simp only [not_exists] at hy
      rw [MatEnd.mapEmb_apply_of_right F (blackAct_downObj P i) hy,
        downX_apply_of_ne P _ (hy s)]
  · simp only [not_exists] at hx
    rw [MatEnd.mapEmb_apply_of_left F (blackAct_downObj P i) hx,
      MatEnd.mul_mapEmb_one_apply_of_left F (blackAct_downObj P i) _ hx]

/-- The image of a crossing of two old strands is the same crossing, cut down by the image
of `1`. -/
theorem blackMatrix_downΨ {j : ℕ} (hj : j + 1 < m) :
    blackMatrix P i (downΨ P (ν := ν) j) = downΨ P j * blackMatrix P i 1 := by
  ext x y
  rw [blackMatrix_apply, blackMatrix_apply]
  by_cases hx : ∃ s, appendDown i s = x
  · obtain ⟨s, rfl⟩ := hx
    rw [MatEnd.mul_mapEmb_one_apply_emb F (appendDown_injective i) (blackAct_downObj P i) _ s y]
    by_cases hy : ∃ t, appendDown i t = y
    · obtain ⟨t, rfl⟩ := hy
      rw [MatEnd.mapEmb_apply_emb F (appendDown_injective i) (blackAct_downObj P i)]
      exact conjF_downCross P i s t hj
    · simp only [not_exists] at hy
      rw [MatEnd.mapEmb_apply_of_right F (blackAct_downObj P i) hy]
      exact (downCross_appendDown_of_not_mem P i s y hy hj).symm
  · simp only [not_exists] at hx
    rw [MatEnd.mapEmb_apply_of_left F (blackAct_downObj P i) hx,
      MatEnd.mul_mapEmb_one_apply_of_left F (blackAct_downObj P i) _ hx]

end Matrix

end Categorification.Stendhal.DoubleDiagram
