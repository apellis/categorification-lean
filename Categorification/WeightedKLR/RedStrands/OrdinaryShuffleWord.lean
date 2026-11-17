/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OrdinaryShuffleSum
import Categorification.WeightedKLR.RedStrands.TensorLatticeCoordinates

/-!
# Last-red factor tests on ordinary tensor words

Webster, arXiv:1309.3796v2, §4.6–4.7, (5.10). The cut used to expand the ordinary
tensor vector is the cut at the last red in its ordered loading. An arbitrary pair
of linear tests evaluates this expansion as a weighted sum of products of factor tests.
-/
noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KL2 LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped TensorProduct

variable {I : Type*} {m : ℕ}

/-- Append a list of ordinary black letters to an earlier loading. -/
def appendOrdinaryBlack (w : TensorWord I m) (s : List I) : TensorWord I m :=
  s.foldl (fun v i => v.black i 1) w

/-- The underlying list of colours of an ordinary loading. -/
theorem ofFn_loading [DecidableEq I] (w : TensorWord I m) :
    List.ofFn w.loading.1 = expandDiv w.blocks := by
  let s := expandDiv w.blocks
  have h : s.length = (stendhalWeight m w.content.toMultiset).card :=
    (congrArg Multiset.card w.blocks_weight)
  exact (List.ofFn_congr h s.get).symm.trans (List.ofFn_get s)

private theorem blocks_red_list (w : TensorWord I m) :
    expandDiv w.red.blocks = (expandDiv w.blocks).map (addRedColor m) ++ [.inr (Fin.last m)] := by
  simp [TensorWord.blocks,expandDiv, List.flatMap_map, List.map_flatMap]

private theorem blocks_black_list (w : TensorWord I m) (i : I) (n : ℕ) :
    expandDiv (w.black i n).blocks = expandDiv w.blocks ++ List.replicate n (.inl i) := by
  simp [TensorWord.blocks,expandDiv]

/-- Ordinary black letters append unchanged to the ordered word. -/
theorem appendOrdinaryBlack_blocks (w : TensorWord I m) (s : List I) :
    expandDiv (appendOrdinaryBlack w s).blocks = expandDiv w.blocks ++ s.map Sum.inl := by
  induction s generalizing w with
  | nil => simp [appendOrdinaryBlack]
  | cons i s ih =>
    change expandDiv (appendOrdinaryBlack (w.black i 1) s).blocks = _
    rw [ih,blocks_black_list]
    simp

/-- The earlier word produced by cutting the tensor vector at its final red has exactly
the prefix of the categorical loading; the remaining labels are its black suffix. -/
theorem lastRedWord_blocks : ∀ w : TensorWord I (m+1), expandDiv w.blocks =
    (expandDiv (lastRedWord w).1.blocks).map (addRedColor m) ++
      .inr (Fin.last m) :: (lastRedWord w).2.map Sum.inl
  | .red w => by simp [lastRedWord,blocks_red_list]
  | .black w i n => by
    rw [lastRedWord,blocks_black_list,lastRedWord_blocks w]
    simp [List.append_assoc]

private theorem last_not_mem_prefix (w : TensorWord I m) :
    Sum.inr (Fin.last m) ∉ (expandDiv w.blocks).map (addRedColor m) := by
  intro h
  obtain ⟨j,_,hj⟩ := List.mem_map.1 h
  cases j with
  | inl => contradiction
  | inr i => exact (Fin.castSucc_lt_last i).ne (Sum.inr.inj hj)

/-- The identifying red colour is absent on both sides of the final red cut. -/
theorem lastRedWord_unique (w : TensorWord I (m+1)) :
    Sum.inr (Fin.last m) ∉ (expandDiv (lastRedWord w).1.blocks).map (addRedColor m) ∧
      Sum.inr (Fin.last m) ∉ (lastRedWord w).2.map (Sum.inl : I → I ⊕ Fin (m+1)) :=
  ⟨last_not_mem_prefix _,by simp⟩

variable {Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I} {R : D.RootDatum Y}
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

variable (wt : Fin (m+1) → Dom R)
local notation "wt₀" => fun j : Fin m => wt (Fin.castSucc j)
local notation "V₀" => TensorSpace wt₀
local notation "V₁" => IrreducibleModule R v (Subtype.val (wt (Fin.last m)))
local notation "A₁" => fun i => Algebra.lsmul L L V₁ (F R v i)

private theorem ordinarySuffix_apply_word (weight : Fin m → Dom R) (w : TensorWord I m) (s : List I) :
    ordinarySuffixOp (fun i => barTensorRepresentation weight (F R v i)) s (barOrdinaryWord w weight) =
      barOrdinaryWord (appendOrdinaryBlack w s) weight := by
  induction s generalizing w with
  | nil => rfl
  | cons i s ih =>
    change ordinarySuffixOp _ s (barTensorRepresentation weight (F R v i) (barOrdinaryWord w weight)) = _
    have h : barTensorRepresentation weight (F R v i) (barOrdinaryWord w weight) =
        barOrdinaryWord (w.black i 1) weight := by simp [barOrdinaryWord]
    rw [h, ih]
    rfl

/-- Product tests on ordinary tensor words are the sum of the two factor tests against the
masked subwords, with the Laurent monomial from the bar coproduct. -/
theorem factorTensorTest_barOrdinaryWord {A B : Type*}
    (f : A → V₀ →ₗ[L] L) (g : B → V₁ →ₗ[L] L) (a : A) (b : B) (w : TensorWord I (m+1)) :
    factorTensorTest f g a b (tensorSplitLast wt (barOrdinaryWord w wt)) =
      ∑ c : Fin (lastRedWord w).2.length → Bool,
        let t := tagMask (lastRedWord w).2 c
        v ^ suffixMaskExponent R (wt (Fin.last m)).1 t *
          (f a (barOrdinaryWord (appendOrdinaryBlack (lastRedWord w).1 (maskSubword false t)) wt₀) *
           g b (ordinarySuffixOp A₁ (maskSubword true t) (IrreducibleModule.hwv R v (wt (Fin.last m)).1))) := by
  rw [barOrdinaryWord_eq_sum_masks, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp only [suffixMaskTerm,map_smul,appendTensor, LinearEquiv.apply_symm_apply,
    factorTensorTest_tmul,smul_eq_mul,ordinarySuffix_apply_word]

end Categorification.Stendhal.FirstWeight
