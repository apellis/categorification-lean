/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Crystal.GradedIndShuffle
import Categorification.KLR.Rouquier.Polynomial
import Categorification.QuantumGroup.UDotWords
import Categorification.WeightedKLR.RedStrands.ParabolicAffineQuotients
import Categorification.WeightedKLR.RedStrands.TensorShuffleRecurrence

/-!
# The degree of a standardization shuffle

For the two parabolic inputs of Webster, arXiv:1309.3796v2, §§4.6–4.7, the
graded induction shuffle formula of Khovanov–Lauda I, Lemma 2.20, counts
right-before-left crossings. At an ordered output and a nonviolating final
input, the later strand of every such pair is black. A red strand contributes
its weight pairing, and a black strand contributes minus its Cartan pairing.
These are the exponents of the bar-coproduct recurrence.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA QuantumGroup QuantumGroup.PreF

variable {J I : Type*} {n : ℕ}

/-- Pairwise crossing degrees of a tagged output word. The true positions
come from the right input and the false positions from the left input. -/
def shuffleCrossingSum (f : J → J → ℤ) : List (J × Bool) → ℤ
  | [] => 0
  | (a,b)::w => (if b then (w.map (fun z => if z.2 then 0 else f a z.1)).sum else 0) +
      shuffleCrossingSum f w

private theorem maskInv_eq_list (f : J → J → ℤ) (w : Fin n → J) (b : Fin n → Bool) :
    maskInv f w b = shuffleCrossingSum f (List.ofFn fun j => (w j,b j)) := by
  induction n with
  | zero => simp [maskInv,shuffleCrossingSum]
  | succ n ih =>
    rw [List.ofFn_succ,shuffleCrossingSum,← ih]
    unfold maskInv
    rw [Fin.sum_univ_succ]
    congr 1
    · rw [Fin.sum_univ_succ,List.map_ofFn,List.sum_ofFn]
      simp only [lt_irrefl,false_and,↓reduceIte,zero_add,Fin.succ_pos,true_and,Function.comp_apply]
      cases b 0
      · simp
      · simp
        apply Finset.sum_congr rfl
        intro j _
        cases b j.succ <;> simp
    · apply Finset.sum_congr rfl
      intro j _
      rw [Fin.sum_univ_succ]
      simp only [Fin.not_lt_zero,false_and,↓reduceIte,zero_add,Fin.succ_lt_succ_iff]

/-- Removing the last letter keeps the old degree and adds exactly the
crossings of the new left-assigned letter with the previous right subword. -/
theorem shuffleCrossingSum_snoc (f : J → J → ℤ) (w : List (J × Bool)) (i : J) (b : Bool) :
    shuffleCrossingSum f (w++[(i,b)]) = shuffleCrossingSum f w +
      if b then 0 else (((w.filter Prod.snd).map fun z => f z.1 i).sum) := by
  induction w with
  | nil => simp [shuffleCrossingSum]
  | cons z w ih =>
    rcases z with ⟨j,c⟩
    cases c <;> cases b <;> simp [shuffleCrossingSum,ih]
    abel

variable {ℓ : ℕ} (C : CartanDatum I) (highest : I →₀ ℕ)

/-- Contribution of an inverted output pair at the last-red cut. The right
strand is supplied first; the later, left-input black strand supplies the
coroot in the red/black pairing. -/
def lastRedCrossing : (I ⊕ Fin (ℓ+1)) → (I ⊕ Fin (ℓ+1)) → ℤ
  | .inr _, .inl i => C.dot i i / 2 * (highest i : ℤ)
  | .inl j, .inl i => -C.dot i j
  | _, .inr _ => 0

variable {k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    {C : CartanDatum I} (hQ : IsRouquierQ C Q) (Λ : Fin (ℓ+1) → I →₀ ℕ)
    {θ β : Multiset I}

local notation "Lwt" => Multiset.map (addRedColor (I := I) ℓ) (stendhalWeight ℓ θ)
local notation "Rwt" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "lastWt" => Λ (Fin.last ℓ)
local notation "crossing" => lastRedCrossing (ℓ := ℓ) C (lastWt)
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2)
  (fun i => Eq.symm (QuantumGroup.UDot.two_mul_di C i))
local notation "splitCard" => Seq.card_add' (Lwt) (Rwt)

variable {s : KLR.Seq ((Multiset.map (addRedColor (I := I) ℓ) (stendhalWeight ℓ θ)) +
    Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β))}
    (u : KLRAlgebra.ShuffleOf (Multiset.map (addRedColor (I := I) ℓ) (stendhalWeight ℓ θ))
      (Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)) s)

private theorem right_position {a : Fin (Lwt+Rwt).card} (ha : u.mask a = true) :
    ∃ j : Fin (Rwt).card, u.1.1 a = blockEquiv (splitCard) (.inr j) ∧
      s.lbl a = u.split.2.lbl j := by
  obtain ⟨j,hj⟩ := (shuffleMask_eq_true_iff (splitCard) u.1.1 a).1 ha
  refine ⟨j,hj,?_⟩
  rw [show u.split.2.lbl j = _ from u.split_snd_apply j,← hj]
  exact congrArg s.lbl (u.1.1.symm_apply_apply a).symm

private theorem right_red (a : Fin (Lwt+Rwt).card) (ha : u.mask a = true)
    {r : Fin (ℓ+1)} (hr : s.lbl a = .inr r) : r = Fin.last ℓ := by
  obtain ⟨j,_,he⟩ := right_position u ha
  exact parabolicLast_red_eq_last (ℓ := ℓ) β _ _ (he.symm.trans hr)

private theorem inverted_left_black (ho : IsRedOrdered s) (hv : ¬ IsViolated u.split.2)
    {a c : Fin (Lwt+Rwt).card} (hac : a < c) (ha : u.mask a = true) :
    ∃ i, s.lbl c = .inl i := by
  have hn : 0 < (Rwt).card := by simp [stendhalWeight]
  let z : Fin (Rwt).card := ⟨0,hn⟩
  have hz : u.split.2.lbl z = .inr (Fin.last ℓ) := by
    cases he : u.split.2.lbl z with
    | inl i => exact (hv ⟨hn,by change (u.split.2.lbl z).isLeft; rw [he]; rfl⟩).elim
    | inr r => exact congrArg Sum.inr (parabolicLast_red_eq_last (ℓ := ℓ) β _ _ he)
  let p := u.1.1⁻¹ (blockEquiv (splitCard) (.inr z))
  have hred : s.lbl p = .inr (Fin.last ℓ) := (u.split_snd_apply z).symm.trans hz
  obtain ⟨j,hj,_⟩ := right_position u ha
  have hp : p ≤ a := by
    have hp := u.1.2.2.monotone (show z ≤ j from Nat.zero_le _)
    change u.1.1.symm (blockEquiv (splitCard) (.inr z)) ≤
      u.1.1.symm (blockEquiv (splitCard) (.inr j)) at hp
    rwa [←hj,Equiv.symm_apply_apply] at hp
  cases he : s.lbl c with
  | inl i => exact ⟨i,rfl⟩
  | inr r => exact (not_lt_of_ge (Fin.le_last r) (ho p c _ r (lt_of_le_of_lt hp hac) hred he)).elim

/-- Actual graded induction degree at an ordered Stendhal loading with a
nonviolating last-factor input, expressed by the signed red/black and
black/black crossing contributions of its tagged output word. -/
theorem lastRed_indShuffleDegree (ho : IsRedOrdered s) (hv : ¬ IsViolated u.split.2) :
    (G).indShuffleDegree u.1 s =
      shuffleCrossingSum (crossing) (List.ofFn fun j => (s.lbl j,u.mask j)) := by
  classical
  rw [GradingDatum.indShuffleDegree_eq_maskInv,←maskInv_eq_list (crossing) s.lbl u.mask]
  unfold maskInv
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  change (if a < c ∧ u.mask a = true ∧ u.mask c = false then _ else 0) = _
  split_ifs with hh
  · obtain ⟨i,hi⟩ := inverted_left_black u ho hv hh.1 hh.2.1
    change (G).degΨ (s.lbl c) (s.lbl a) = crossing (s.lbl a) (s.lbl c)
    rw [hi]
    cases he : s.lbl a with
    | inl j => rfl
    | inr r => rw [right_red u a hh.2.1 he]; rfl
  · rfl

private theorem maskedRightContent {m : ℕ} (v : Fin m → J) (b : Fin m → Bool) :
    (((List.ofFn fun j => (v j,b j)).filter Prod.snd).map Prod.fst : Multiset J) =
      wt (maskWord v b true) := by
  apply congrArg ((↑) : List J → Multiset J)
  change _ = ((List.finRange m).filter (fun j => b j == true)).map v
  simp only [List.ofFn_eq_map,List.filter_map,List.map_map,Function.comp_def]
  rw [show (fun j => b j == true) = b from funext fun j => by cases b j <;> rfl]

/-- The full right subword of any parabolic shuffle has the final red
strand and exactly the black content of the final factor. -/
theorem lastRed_shuffle_rightContent :
    (((List.ofFn fun j => (s.lbl j,u.mask j)).filter Prod.snd).map Prod.fst :
      Multiset (I ⊕ Fin (ℓ+1))) = β.map Sum.inl + {Sum.inr (Fin.last ℓ)} := by
  exact (maskedRightContent s.lbl u.mask).trans
    (u.wt_mask_true.trans ((lastRedBlackWeight (ℓ := ℓ) β).symm.trans (add_comm _ _)))

omit [DecidableEq I] in
/-- Summing the charges against the right input gives the symmetrized
coroot pairing with its remaining highest weight. -/
theorem lastRedCrossing_sum_right (C : CartanDatum I) (highest : I →₀ ℕ) (β : Multiset I)
    (w : List ((I ⊕ Fin (ℓ+1)) × Bool)) (i : I)
    (h : ((w.filter Prod.snd).map Prod.fst : Multiset (I ⊕ Fin (ℓ+1))) =
      β.map Sum.inl + {Sum.inr (Fin.last ℓ)}) :
    ((w.filter Prod.snd).map (fun z => lastRedCrossing C highest z.1 (.inl i))).sum =
      C.dot i i / 2 * (highest i : ℤ) - (β.map (C.dot i)).sum := by
  have he := congrArg (fun a : Multiset (I ⊕ Fin (ℓ+1)) =>
    (a.map (fun j => lastRedCrossing C highest j (.inl i))).sum) h
  simp only [Multiset.map_coe,Multiset.sum_coe,List.map_map,Multiset.map_add,Multiset.sum_add,
    Multiset.map_map,Multiset.map_singleton,Multiset.sum_singleton,Function.comp_def,lastRedCrossing] at he
  change ((w.filter Prod.snd).map (fun z => lastRedCrossing C highest z.1 (.inl i))).sum = _
  have hn : (β.map (fun j => -C.dot i j)).sum = -(β.map (C.dot i)).sum := by
    exact Multiset.sum_map_neg
  simpa only [lastRedCrossing,hn,sub_eq_add_neg,add_comm] using he

/-- Removing a final right-assigned letter does not change the shuffle degree. -/
theorem lastRed_indShuffleDegree_snoc_right (ho : IsRedOrdered s) (hv : ¬ IsViolated u.split.2)
    (w : List ((I ⊕ Fin (ℓ+1)) × Bool)) (z : I ⊕ Fin (ℓ+1))
    (hw : (List.ofFn fun j => (s.lbl j,u.mask j)) = w ++ [(z,true)]) :
    (G).indShuffleDegree u.1 s = shuffleCrossingSum (crossing) w := by
  rw [lastRed_indShuffleDegree hQ Λ u ho hv,hw,shuffleCrossingSum_snoc]
  simp

/-- Removing a final left-assigned black letter subtracts precisely the
final red weight pairing minus all right-input black Cartan pairings, the
ordinary bar-coproduct coefficient in Webster, §§4.6–4.7. -/
theorem lastRed_indShuffleDegree_snoc_left (ho : IsRedOrdered s) (hv : ¬ IsViolated u.split.2)
    (w : List ((I ⊕ Fin (ℓ+1)) × Bool)) (i : I)
    (hw : (List.ofFn fun j => (s.lbl j,u.mask j)) = w ++ [(.inl i,false)]) :
    (G).indShuffleDegree u.1 s = shuffleCrossingSum (crossing) w +
      (C.dot i i / 2 * (lastWt i : ℤ) - (β.map (C.dot i)).sum) := by
  have hc := lastRed_shuffle_rightContent u
  rw [hw] at hc
  rw [List.filter_append,show List.filter Prod.snd [((Sum.inl i : I ⊕ Fin (ℓ+1)),false)] = [] from rfl,
    List.append_nil] at hc
  rw [lastRed_indShuffleDegree hQ Λ u ho hv,hw,shuffleCrossingSum_snoc]
  exact congrArg (_ + ·) (lastRedCrossing_sum_right C (lastWt) β w i hc)

open LieLean.QuantumGroup in
/-- The ordinary bar-coproduct exponent equals the actual degree increment
on a final left-assigned black letter. The list of right black colours can
be any word of the prescribed right black content. -/
theorem lastRed_indShuffleDegree_snoc_weight {Y : Type*} [AddCommGroup Y]
    {R : C.toLusztig.RootDatum Y} (highest : Y →+ ℤ) (i : I)
    (hwgt : highest (R.coroot i) = (lastWt i : ℤ)) (right : List I) (hb : (right : Multiset I) = β)
    (ho : IsRedOrdered s) (hv : ¬ IsViolated u.split.2)
    (w : List ((I ⊕ Fin (ℓ+1)) × Bool))
    (hw : (List.ofFn fun j => (s.lbl j,u.mask j)) = w ++ [(.inl i,false)]) :
    (G).indShuffleDegree u.1 s = shuffleCrossingSum (crossing) w +
      (highest - (right.map R.root).sum) (ktilde R i) := by
  have hd : (C.toLusztig.d i : ℤ) = C.dot i i / 2 := by
    have h := C.toLusztig.two_mul_d i
    change 2 * (C.toLusztig.d i : ℤ) = C.dot i i at h
    omega
  have hsum : (β.map (C.dot i)).sum = (right.map (C.toLusztig.dot i)).sum := by
    rw [← hb,Multiset.map_coe,Multiset.sum_coe]
    rfl
  rw [lastRed_indShuffleDegree_snoc_left hQ Λ u ho hv w i hw,
    FirstWeight.shuffleExponent_eq_crossings,hwgt,hd,hsum]

end Categorification.Stendhal
