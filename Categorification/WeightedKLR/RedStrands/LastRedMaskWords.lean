/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedMaskComparison
import Categorification.WeightedKLR.RedStrands.ParabolicAffineQuotients

/-!
# Factor words of the last-red shuffle

In Webster, arXiv:1309.3796v2, §§4.6–4.7, the earlier factor of a surviving shuffle
receives its prefix together with the left-assigned black suffix. The final factor receives
its single red strand followed by the right-assigned black subword.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR KLRAlgebra KL2

variable {I J : Type*} {m : ℕ}

private theorem maskSubword_pre (c : Bool) (p : List J) (t : List (J × Bool)) :
    maskSubword c (p.map (fun z => (z,false)) ++ t) =
      (if c then [] else p) ++ maskSubword c t := by
  induction p with
  | nil => cases c <;> rfl
  | cons j p ih => cases c <;> simp_all [maskSubword]

private theorem maskSubword_map (c : Bool) (f : I → J) (t : List (I × Bool)) :
    maskSubword c (t.map (Prod.map f id)) = (maskSubword c t).map f := by
  induction t with
  | nil => rfl
  | cons z t ih => rcases z with ⟨j,b⟩; cases b <;> cases c <;> simp_all [maskSubword]

variable (w : TensorWord I (m+1))

/-- Earlier factor word of a suffix mask, with the previously assigned black letters in order. -/
def prefixMaskWord (c : Fin (lastRedWord w).2.length → Bool) : TensorWord I m :=
  appendOrdinaryBlack (lastRedWord w).1 (maskSubword false (tagMask (lastRedWord w).2 c))

/-- Ordered black string received by the final factor. -/
def finalMaskLetters (c : Fin (lastRedWord w).2.length → Bool) : List I :=
  maskSubword true (tagMask (lastRedWord w).2 c)

/-- The left masked loading is the relabelled earlier factor word. -/
theorem lastRedBlackTags_left (c : Fin (lastRedWord w).2.length → Bool) :
    maskSubword false (lastRedBlackTags w c) = (expandDiv (prefixMaskWord w c).blocks).map (addRedColor m) := by
  rw [lastRedBlackTags,maskSubword_pre,prefixMaskWord,appendOrdinaryBlack_blocks,List.map_append]
  change _ ++ maskSubword false ((tagMask (lastRedWord w).2 c).map (Prod.map Sum.inl id)) = _
  rw [maskSubword_map,List.map_map]
  rfl

/-- The right masked loading is the final red followed by its masked black string. -/
theorem lastRedBlackTags_right (c : Fin (lastRedWord w).2.length → Bool) :
    maskSubword true (lastRedBlackTags w c) =
      Sum.inr (Fin.last m) :: (finalMaskLetters w c).map Sum.inl := by
  rw [lastRedBlackTags,maskSubword_pre]
  change Sum.inr (Fin.last m) :: maskSubword true ((tagMask (lastRedWord w).2 c).map (Prod.map Sum.inl id)) = _
  rw [maskSubword_map]
  rfl

variable [DecidableEq I]

omit [DecidableEq I] in
/-- A wrong earlier diagram content is precisely a wrong earlier black weight. -/
theorem prefixMaskContent_iff (θ : Multiset I) (c : Fin (lastRedWord w).2.length → Bool) :
    (maskSubword false (lastRedBlackTags w c) : Multiset (I ⊕ Fin (m+1))) =
        (stendhalWeight m θ).map (addRedColor m) ↔ (prefixMaskWord w c).content.toMultiset = θ := by
  rw [lastRedBlackTags_left, ← Multiset.map_coe, TensorWord.blocks_weight]
  have hinj : Function.Injective (addRedColor m : I ⊕ Fin m → _) :=
    Sum.map_injective.mpr ⟨Function.injective_id,Fin.castSucc_injective m⟩
  rw [(Multiset.map_injective hinj).eq_iff,stendhalWeight,stendhalWeight,add_left_inj,
    (Multiset.map_injective Sum.inl_injective).eq_iff]

omit [DecidableEq I] in
/-- A wrong final diagram content is precisely a wrong content of the right-assigned black string. -/
theorem finalMaskContent_iff (β : Multiset I) (c : Fin (lastRedWord w).2.length → Bool) :
    (maskSubword true (lastRedBlackTags w c) : Multiset (I ⊕ Fin (m+1))) =
        (stendhalWeight 1 β).map (Sum.map id (fun _ : Fin 1 => Fin.last m)) ↔
        (finalMaskLetters w c : Multiset I) = β := by
  rw [lastRedBlackTags_right, ← lastRedBlackWeight (ℓ := m) β]
  change {Sum.inr (Fin.last m)} + (↑((finalMaskLetters w c).map (Sum.inl : I → I ⊕ Fin (m+1))) : Multiset (I ⊕ Fin (m+1))) = _ ↔ _
  rw [← Multiset.map_coe,add_right_inj,(Multiset.map_injective Sum.inl_injective).eq_iff]

variable {α β : Multiset (I ⊕ Fin (m+1))} (s : Seq (α+β))
  (hw : List.ofFn s.1 = expandDiv w.blocks)
  (u : {u : ShuffleOf α β s // (List.ofFn u.split.2.1).head? = some (.inr (Fin.last m))})

/-- The earlier input of the parabolic permutation is the prescribed earlier factor word. -/
theorem ordinaryShuffleEquiv_left_word :
    List.ofFn u.1.split.1.1 = (expandDiv (prefixMaskWord w (ordinaryShuffleEquiv w s hw u).1).blocks).map
      (addRedColor m) := by
  rw [u.1.ofFn_split_fst, ← lastRedBlackTags_left, ordinaryShuffleEquiv_tags]
  exact (maskSubword_shuffleTags s u.1 false).symm

/-- The final input of the parabolic permutation is the last red followed by its black string. -/
theorem ordinaryShuffleEquiv_right_word :
    List.ofFn u.1.split.2.1 =
      Sum.inr (Fin.last m) :: (finalMaskLetters w (ordinaryShuffleEquiv w s hw u).1).map Sum.inl := by
  rw [u.1.ofFn_split_snd, ← lastRedBlackTags_right, ordinaryShuffleEquiv_tags]
  exact (maskSubword_shuffleTags s u.1 true).symm

end Categorification.Stendhal.FirstWeight
