/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.Parabolic
import Categorification.TypeA.NormalForm

/-!
# Reduced words with a common prefix outside an interval

For the PBW coordinates at an interleaved column in Webster, arXiv:1309.3796v2,
§6.1, proof of Lemma 6.8 after (6.21), permutations in the same right interval
coset receive the same exterior reduced word. Both outside blocks can have
arbitrary permutations.
-/

noncomputable section
namespace Categorification.TypeA
open Equiv

variable {p n r m : ℕ}
local notation "S" t:arg => Perm (Fin t)

private def rightBlocks {a b N : ℕ} (h : a+b=N) : S a × S b × Shuffle h ≃ S N :=
  ((Equiv.prodCongr (Equiv.inv _) (Equiv.prodCongr (Equiv.inv _) (Equiv.refl _))).trans
    (parabolicEquiv h)).trans (Equiv.inv _)

private theorem rightBlocks_apply {a b N : ℕ} (h : a+b=N) (x : S a) (y : S b) (u : Shuffle h) :
    rightBlocks h (x,y,u) = u.val⁻¹ * blockPerm h x y := by
  change (blockPerm h x⁻¹ y⁻¹ * u.val)⁻¹ = _
  rw [mul_inv_rev, blockPerm_inv, inv_inv, inv_inv]

private theorem length_rightBlocks {a b N : ℕ} (h : a+b=N) (x : S a) (y : S b) (u : Shuffle h) :
    length N (rightBlocks h (x,y,u)) = length a x + length b y + length N u.val := by
  change length N (blockPerm h x⁻¹ y⁻¹ * u.val)⁻¹ = _
  rw [length_inv, length_blockPerm_mul h _ _ u.property, length_inv, length_inv]

variable (h : p+(n+r)=m)

/-- Embed a permutation of the interval of `n` positions beginning at `p`;
the two exterior blocks have sizes `p` and `r`. -/
def intervalPerm (v : S n) : S m :=
  blockPerm h 1 (blockPerm (n := n) (n' := r) rfl v 1)

/-- The interval embedding acts on position `p+i` by the local permutation. -/
theorem intervalPerm_pos (v : S n) (i : Fin n) :
    intervalPerm h v ⟨p+i.val,by omega⟩ = ⟨p+(v i).val,by omega⟩ := by
  change blockPerm h 1 (blockPerm (show n+r=n+r from rfl) v 1)
    (blockEquiv h (.inr (blockEquiv (show n+r=n+r from rfl) (.inl i)))) = _
  rw [blockPerm_inr, blockPerm_inl]
  rfl

/-- An adjacent generator in the interval is the corresponding shifted ambient crossing. -/
theorem intervalPerm_sadj (j : ℕ) (hj : j+1 < n) :
    intervalPerm h (sadj n j) = sadj m (p+j) := by
  rw [intervalPerm, ← sadj_eq_blockPerm_left (n' := r) rfl hj, ← sadj_eq_blockPerm_right h (by omega)]

/-- The minimal exterior representative and the relative permutation of the
interval, with the exterior permutations on both sides retained. -/
def rightIntervalSplit (w : S m) : S m × S n :=
  let a := (rightBlocks h).symm w
  let b := (rightBlocks (a := n) (b := r) rfl).symm a.2.1
  (rightBlocks h (a.1,rightBlocks rfl (1,b.2.1,b.2.2),a.2.2), b.1)

private theorem rightIntervalSplit_blocks (x : S p) (y : S n) (z : S r)
    (u : Shuffle h) (v : Shuffle (show n+r=n+r from rfl)) :
    rightIntervalSplit h (rightBlocks h (x,rightBlocks rfl (y,z,v),u)) =
      (rightBlocks h (x,rightBlocks rfl (1,z,v),u),y) := by
  simp only [rightIntervalSplit, Equiv.symm_apply_apply]

private theorem rightBlocks_mul_interval (x : S p) (y y' : S n) (z : S r)
    (u : Shuffle h) (v : Shuffle (show n+r=n+r from rfl)) :
    rightBlocks h (x,rightBlocks rfl (y,z,v),u) * intervalPerm h y' =
      rightBlocks h (x,rightBlocks rfl (y*y',z,v),u) := by
  simp only [rightBlocks_apply, intervalPerm, mul_assoc, blockPerm_mul, mul_one]

private theorem exists_rightBlocks (w : S m) :
    ∃ (x : S p) (y : S n) (z : S r) (u : Shuffle h) (v : Shuffle (show n+r=n+r from rfl)),
      w = rightBlocks h (x,rightBlocks rfl (y,z,v),u) := by
  obtain ⟨⟨x,b,u⟩,rfl⟩ := (rightBlocks h).surjective w
  obtain ⟨⟨y,z,v⟩,rfl⟩ := (rightBlocks (a := n) (b := r) rfl).surjective b
  exact ⟨x,y,z,u,v,rfl⟩

/-- Right multiplication by any permutation of the interval leaves the exterior
representative unchanged and multiplies the relative permutation on the right. -/
theorem rightIntervalSplit_mul (w : S m) (v : S n) :
    rightIntervalSplit h (w * intervalPerm h v) =
      ((rightIntervalSplit h w).1,(rightIntervalSplit h w).2 * v) := by
  obtain ⟨x,y,z,u,t,rfl⟩ := exists_rightBlocks h w
  rw [rightBlocks_mul_interval, rightIntervalSplit_blocks, rightIntervalSplit_blocks]

theorem rightIntervalSplit_factor (w : S m) :
    (rightIntervalSplit h w).1 * intervalPerm h (rightIntervalSplit h w).2 = w := by
  obtain ⟨x,y,z,u,t,rfl⟩ := exists_rightBlocks h w
  rw [rightIntervalSplit_blocks, rightBlocks_mul_interval, one_mul]

theorem length_rightIntervalSplit (w : S m) :
    length m w = length m (rightIntervalSplit h w).1 + length n (rightIntervalSplit h w).2 := by
  obtain ⟨x,y,z,u,t,rfl⟩ := exists_rightBlocks h w
  rw [rightIntervalSplit_blocks]
  simp only [length_rightBlocks, length_one, zero_add]
  omega

/-- The common exterior representative is increasing on the given interval. -/
theorem rightIntervalSplit_sorted (w : S m) :
    StrictMono (fun i : Fin n => (rightIntervalSplit h w).1 ⟨p+i.val, by omega⟩) := by
  obtain ⟨x,y,z,u,t,rfl⟩ := exists_rightBlocks h w
  rw [rightIntervalSplit_blocks]
  intro i j hij
  change rightBlocks h (x,rightBlocks rfl (1,z,t),u)
      (blockEquiv h (.inr (blockEquiv (show n+r=n+r from rfl) (.inl i)))) <
    rightBlocks h (x,rightBlocks rfl (1,z,t),u)
      (blockEquiv h (.inr (blockEquiv (show n+r=n+r from rfl) (.inl j))))
  simp only [rightBlocks_apply, Perm.mul_apply, blockPerm_inr, blockPerm_inl, Perm.one_apply]
  exact u.property.2 (t.property.1 hij)

/-- A permutation already increasing on the interval is its own exterior representative. -/
theorem rightIntervalSplit_of_sorted (w : S m)
    (hw : StrictMono (fun i : Fin n => w ⟨p+i.val,by omega⟩)) :
    rightIntervalSplit h w = (w,1) := by
  let s := rightIntervalSplit h w
  have hw' (i : Fin n) : w ⟨p+i.val,by omega⟩ = s.1 ⟨p+(s.2 i).val,by omega⟩ := by
    calc
      _ = (s.1 * intervalPerm h s.2) ⟨p+i.val,by omega⟩ :=
        congrArg (fun a : S m => a ⟨p+i.val,by omega⟩) (rightIntervalSplit_factor h w).symm
      _ = _ := by rw [Perm.mul_apply, intervalPerm_pos]
  have hc : StrictMono s.2 := by
    intro i j hij
    apply (rightIntervalSplit_sorted h w).lt_iff_lt.mp
    exact (hw' i) ▸ (hw' j) ▸ hw hij
  have ident : s.2 = 1 := by
    have eq := Subsingleton.elim (hc.orderIsoOfSurjective _ s.2.surjective) (OrderIso.refl _)
    ext i
    exact congrArg Fin.val (congrArg (fun a : Fin n ≃o Fin n => a i) eq)
  have fac : s.1 * intervalPerm h s.2 = w := rightIntervalSplit_factor h w
  rw [ident, intervalPerm, blockPerm_one, blockPerm_one, mul_one] at fac
  exact Prod.ext fac ident

/-- A reduced choice in which all members of a right interval coset have a
common exterior prefix. -/
def rightIntervalWord (w : S m) : List ℕ :=
  canWord m (rightIntervalSplit h w).1 ++ shiftWord p (canWord n (rightIntervalSplit h w).2)

theorem rightIntervalWord_mul (w : S m) (v : S n) :
    rightIntervalWord h (w * intervalPerm h v) = canWord m (rightIntervalSplit h w).1 ++
      shiftWord p (canWord n ((rightIntervalSplit h w).2 * v)) := by
  rw [rightIntervalWord, rightIntervalSplit_mul]

/-- Any local reduced suffix representing the relative permutation can be appended
to the fixed exterior reduced word. -/
theorem rightIntervalSplit_append (w : S m) (l : List ℕ) (hl : IsReduced n l)
    (hv : wordProd n l = (rightIntervalSplit h w).2) :
    let e := canWord m (rightIntervalSplit h w).1 ++ shiftWord p l
    IsReduced m e ∧ wordProd m e = w := by
  intro e
  have hwide : ValidWord (n+r) l := hl.1.of_le (by omega)
  have prod : wordProd m e = w := by
    rw [show e = canWord m (rightIntervalSplit h w).1 ++ shiftWord p l from rfl,
      wordProd_append, wordProd_canWord, wordProd_shiftWord h hwide,
      wordProd_eq_blockPerm_left (n' := r) rfl hl.1, hv]
    exact rightIntervalSplit_factor h w
  refine ⟨⟨validWord_append.2 ⟨validWord_canWord _ _, hwide.shiftWord h⟩,?_⟩,prod⟩
  rw [prod]
  change (canWord m (rightIntervalSplit h w).1 ++ shiftWord p l).length = _
  rw [List.length_append, length_shiftWord, length_canWord, hl.2, hv]
  exact (length_rightIntervalSplit h w).symm

theorem rightIntervalWord_choice (w : S m) :
    IsReduced m (rightIntervalWord h w) ∧ wordProd m (rightIntervalWord h w) = w :=
  rightIntervalSplit_append h w _ (isReduced_canWord _ _) (wordProd_canWord _ _)

end Categorification.TypeA
