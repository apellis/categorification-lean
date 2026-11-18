/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OrdinaryShuffleWord

/-!
# The last-red shuffle sum in two factor coordinates

Webster, arXiv:1309.3796v2, §4.6–4.7 and (5.10). The last-red cut of an ordinary
tensor word determines its surviving parabolic permutations. Their sum is the bar
coproduct in a pair of factor coordinates supported on the prescribed contents.
-/
noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR KLRAlgebra KL2 LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped TensorProduct

variable {I J : Type*} {m : ℕ}

/-- The tagged diagram indexed by a bit at each black suffix position. -/
def lastRedBlackTags (w : TensorWord I (m+1)) (b : Fin (lastRedWord w).2.length → Bool) :
    List ((I ⊕ Fin (m+1)) × Bool) :=
  ((expandDiv (lastRedWord w).1.blocks).map (addRedColor m)).map (fun j => (j,false)) ++
    (.inr (Fin.last m),true) :: (tagMask (lastRedWord w).2 b).map (Prod.map Sum.inl id)

private def mapMaskEquiv (s : List I) (f : I → J) :
    (Fin (s.map f).length → Bool) ≃ (Fin s.length → Bool) :=
  Equiv.arrowCongr (finCongr (by simp)) (Equiv.refl Bool)

private theorem tagMask_map (s : List I) (f : I → J) (b : Fin (s.map f).length → Bool) :
    tagMask (s.map f) b = (tagMask s (mapMaskEquiv s f b)).map (Prod.map f id) := by
  apply List.ext_getElem
  · simp [tagMask]
  · intro j hj hj'
    simp [tagMask, mapMaskEquiv, List.get_eq_getElem, Equiv.arrowCongr, finCongr]

variable [DecidableEq I] {α β : Multiset (I ⊕ Fin (m+1))}
variable (w : TensorWord I (m+1)) (s : Seq (α+β))

/-- The two masked subwords have the prescribed contents of the two factors. -/
def fitsLastRedContents (b : Fin (lastRedWord w).2.length → Bool) : Prop :=
  (maskSubword false (lastRedBlackTags w b) : Multiset (I ⊕ Fin (m+1))) = α ∧
  (maskSubword true (lastRedBlackTags w b) : Multiset (I ⊕ Fin (m+1))) = β

/-- Surviving permutations of an ordinary loading, indexed by masks of black positions. -/
def ordinaryShuffleEquiv (hw : List.ofFn s.1 = expandDiv w.blocks) :
    {u : ShuffleOf α β s // (List.ofFn u.split.2.1).head? = some (.inr (Fin.last m))} ≃
      {c : Fin (lastRedWord w).2.length → Bool // fitsLastRedContents (α := α) (β := β) w c} := by
  let pre := (expandDiv (lastRedWord w).1.blocks).map (addRedColor m)
  let r : I ⊕ Fin (m+1) := .inr (Fin.last m)
  let z := (lastRedWord w).2
  let f : I → I ⊕ Fin (m+1) := Sum.inl
  refine (lastRedShuffleMaskEquiv s pre r (z.map f) (hw.trans (lastRedWord_blocks w))
    (lastRedWord_unique w).1 (lastRedWord_unique w).2).trans ?_
  refine Equiv.subtypeEquiv (mapMaskEquiv z f) fun b => ?_
  change (_ ∧ _) ↔ (_ ∧ _)
  simp only [lastRedMask, lastRedBlackTags, tagMask_map, pre, r, z, f]

/-- The black-suffix mask reconstructs the full tagged output of the parabolic permutation. -/
theorem ordinaryShuffleEquiv_tags (hw : List.ofFn s.1 = expandDiv w.blocks)
    (u : {u : ShuffleOf α β s // (List.ofFn u.split.2.1).head? = some (.inr (Fin.last m))}) :
    lastRedBlackTags w (ordinaryShuffleEquiv w s hw u).1 = shuffleTags s u.1 := by
  have h := lastRedShuffleMaskEquiv_tags s _ _ _ (hw.trans (lastRedWord_blocks w))
    (lastRedWord_unique w).1 (lastRedWord_unique w).2 u
  change _ ++ _ :: _ = _
  rw [← h,lastRedMask, tagMask_map]
  rfl

/-- Restrict a finite sum to the support of its summand. -/
private theorem sum_supported {K M : Type*} [Fintype K] [AddCommMonoid M]
    (p : K → Prop) [DecidablePred p] (f : K → M) (hf : ∀ k, ¬ p k → f k = 0) :
    ∑ k, f k = ∑ k : {k // p k}, f k.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  suffices h : ∑ k : {k // ¬ p k}, f k.1 = 0 by rw [h,add_zero]
  exact Finset.sum_eq_zero fun k _ => hf k.1 k.2

variable {Y : Type*} [AddCommGroup Y] {D : LusztigCartanDatum I} {R : D.RootDatum Y}
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩
variable (wt : Fin (m+1) → Dom R)
local notation "wt₀" => fun j : Fin m => wt (Fin.castSucc j)
local notation "V₀" => TensorSpace wt₀
local notation "V₁" => IrreducibleModule R v (Subtype.val (wt (Fin.last m)))
local notation "A₁" => fun i => Algebra.lsmul L L V₁ (F R v i)

/-- The earlier vector occurring in a suffix mask of an ordinary word. -/
def prefixMaskVector (b : Fin (lastRedWord w).2.length → Bool) : V₀ :=
  barOrdinaryWord (appendOrdinaryBlack (lastRedWord w).1
    (maskSubword false (tagMask (lastRedWord w).2 b))) wt₀

/-- The final highest-weight vector with the mask's ordinary lowerings applied. -/
def finalMaskVector (b : Fin (lastRedWord w).2.length → Bool) : V₁ :=
  ordinarySuffixOp A₁ (maskSubword true (tagMask (lastRedWord w).2 b))
    (IrreducibleModule.hwv R v (wt (Fin.last m)).1)

/-- Reindex the full weighted sum of parabolic shuffles and evaluate it in two
factor coordinates. The hypotheses concern individual factor word values, support, and
the degree of one mask; the conclusion compares the two complete sums. -/
theorem shuffleSum_eq_factorTensorTest {A B : Type*}
    (f : A → V₀ →ₗ[L] L) (g : B → V₁ →ₗ[L] L) (a : A) (b : B)
    (hw : List.ofFn s.1 = expandDiv w.blocks) (d : ShuffleOf α β s → ℤ)
    (x : Seq α → L) (y : Seq β → L)
    (hy0 : ∀ t : Seq β, (List.ofFn t.1).head? ≠ some (.inr (Fin.last m)) → y t = 0)
    (hd : ∀ u, d u.1 = suffixMaskExponent R (wt (Fin.last m)).1
      (tagMask (lastRedWord w).2 (ordinaryShuffleEquiv w s hw u).1))
    (hx : ∀ u, x u.1.split.1 = f a (prefixMaskVector w wt (ordinaryShuffleEquiv w s hw u).1))
    (hy : ∀ u, y u.1.split.2 = g b (finalMaskVector w wt (ordinaryShuffleEquiv w s hw u).1))
    (hf0 : ∀ c, (maskSubword false (lastRedBlackTags w c) : Multiset _) ≠ α →
      f a (prefixMaskVector w wt c) = 0)
    (hg0 : ∀ c, (maskSubword true (lastRedBlackTags w c) : Multiset _) ≠ β →
      g b (finalMaskVector w wt c) = 0) :
    ∑ u : ShuffleOf α β s, v ^ d u * (x u.split.1 * y u.split.2) =
      factorTensorTest f g a b (tensorSplitLast wt (barOrdinaryWord w wt)) := by
  classical
  let E := ordinaryShuffleEquiv w s hw
  let term (c : Fin (lastRedWord w).2.length → Bool) :=
    v ^ suffixMaskExponent R (wt (Fin.last m)).1 (tagMask (lastRedWord w).2 c) *
      (f a (prefixMaskVector w wt c) * g b (finalMaskVector w wt c))
  rw [factorTensorTest_barOrdinaryWord]
  change _ = ∑ c, term c
  rw [sum_supported (fun u : ShuffleOf α β s => (List.ofFn u.split.2.1).head? = some (.inr (Fin.last m)))
      _ (fun u hn => by rw [hy0 _ hn,mul_zero,mul_zero]),
    sum_supported (fitsLastRedContents (α := α) (β := β) w) term (fun c hc => ?_),
    ← E.sum_comp (fun c => term c.1)]
  · apply Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
    intro u _
    rw [hd u,hx u,hy u]
  · unfold fitsLastRedContents at hc
    by_cases ha : (maskSubword false (lastRedBlackTags w c) : Multiset _) = α
    · simp [term,hg0 c (fun h => hc ⟨ha,h⟩)]
    · simp [term,hf0 c ha]

end Categorification.Stendhal.FirstWeight
