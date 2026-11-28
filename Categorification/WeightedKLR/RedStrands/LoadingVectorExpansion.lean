/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorPartialLowering

/-!
# Expanding the loading vector over block assignments

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Lemma 5.19
and its proof. For a word `lbl` of black and red letters whose red letters are numbered in order,
the loading vector (Webster's `v^κ_i`) is the sum over the block assignments `g` that put no
black letter left of every red letter of `q^{-e(g)}` times the pure tensor whose factor `r` is
`F_{i_k} ⋯ F_{i_1} v_{λ_r}` for the black letters `i_1, …, i_k` assigned to block `r + 1`. The
exponent `e(g)` sums a crossing degree over the pairs of letters whose order the assignment
reverses.

## Main definitions

* `FirstWeight.wordVec`, `FirstWeight.blockWord`, `FirstWeight.assignVector`,
  `FirstWeight.crossExp`, `FirstWeight.expansionTerm`.

## Main results

* `FirstWeight.loadingVector_ofFn_eq_sum`: the expansion.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local instance : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y} {ℓ : ℕ}

private abbrev Factor (wt : Dom R) := IrreducibleModule R 𝕍 wt.1

section WordVector

/-- `F_{i_k} ⋯ F_{i_1} v_λ` for the word `i_1 ⋯ i_k`. -/
def wordVec (w : Dom R) (L : List I) : Factor w :=
  L.foldl (fun x i => F R 𝕍 i • x) (IrreducibleModule.hwv R 𝕍 w.1)

@[simp] theorem wordVec_nil (w : Dom R) : wordVec w [] = IrreducibleModule.hwv R 𝕍 w.1 := rfl

theorem wordVec_append_singleton (w : Dom R) (L : List I) (i : I) :
    wordVec w (L ++ [i]) = F R 𝕍 i • wordVec w L := by
  simp [wordVec, List.foldl_append]

theorem K_smul_F_smul {M : Type*} [AddCommGroup M] [Module 𝕂 M]
    [Module (LieLean.QuantumGroup R 𝕍) M] [IsScalarTower 𝕂 (LieLean.QuantumGroup R 𝕍) M]
    (a : Y) (i : I) (x : M) :
    K R 𝕍 a • F R 𝕍 i • x = 𝕍 ^ (-R.root i a) • F R 𝕍 i • K R 𝕍 a • x := by
  rw [← mul_smul, K_mul_F, smul_assoc, mul_smul]

/-- `F_{i_k} ⋯ F_{i_1} v_λ` has weight `λ - α_{i_1} - ⋯ - α_{i_k}`. -/
theorem K_smul_wordVec (w : Dom R) (a : Y) (L : List I) :
    K R 𝕍 a • wordVec w L = 𝕍 ^ (w.1 a - (L.map fun j => R.root j a).sum) • wordVec w L := by
  induction L using List.reverseRecOn with
  | nil =>
    simp only [wordVec_nil, List.map_nil, List.sum_nil, sub_zero]
    rw [IrreducibleModule.hwv, ← Submodule.Quotient.mk_smul, VermaModule.K_smul_hwv,
      Submodule.Quotient.mk_smul]
  | append_singleton L i ih =>
    rw [wordVec_append_singleton, K_smul_F_smul, ih, smul_comm (F R 𝕍 i), smul_smul,
      ← zpow_add₀ RatFunc.X_ne_zero]
    congr 2
    simp
    ring

end WordVector

section Assignments

variable {m : ℕ}

/-- The colour of a letter if it is black and assigned to block `r + 1`. -/
def blockLetter (lbl : Fin m → I ⊕ Fin ℓ) (g : Fin m → ℕ) (r : ℕ) (p : Fin m) : List I :=
  Sum.elim (fun i => if g p = r + 1 then [i] else []) (fun _ => []) (lbl p)

/-- The black letters that `g` assigns to block `r + 1` (right of the red letter `r`), in order. -/
def blockWord (lbl : Fin m → I ⊕ Fin ℓ) (g : Fin m → ℕ) (r : ℕ) : List I :=
  (List.ofFn (blockLetter lbl g r)).flatten

/-- The pure tensor of a block assignment: factor `r` is `F_{i_k} ⋯ F_{i_1} v_{λ_r}` for the
black letters `i_1, …, i_k` of block `r + 1`. -/
def assignVector (wt : Fin ℓ → Dom R) (lbl : Fin m → I ⊕ Fin ℓ) (g : Fin m → ℕ) :
    TensorSpace wt :=
  PiTensorProduct.tprod 𝕂 (fun r => wordVec (wt r) (blockWord lbl g r))

/-- The crossing exponent: `cross` summed over the pairs `p < q` of letters whose order the
assignment reverses. -/
def crossExp (cross : I ⊕ Fin ℓ → I ⊕ Fin ℓ → ℤ) (lbl : Fin m → I ⊕ Fin ℓ) (g : Fin m → ℕ) : ℤ :=
  ∑ p, ∑ q, if p < q ∧ assignKey lbl g q < assignKey lbl g p then cross (lbl p) (lbl q) else 0

/-- No black letter is assigned to block `0`, left of every red letter (Webster's set `Φ`
inside `Φ̃`). -/
def IsNonviolating (lbl : Fin m → I ⊕ Fin ℓ) (g : Fin m → ℕ) : Prop :=
  ∀ p, (lbl p).isRight = false → g p ≠ 0

instance (lbl : Fin m → I ⊕ Fin ℓ) (g : Fin m → ℕ) : Decidable (IsNonviolating lbl g) := by
  unfold IsNonviolating; infer_instance

/-- The term of a block assignment in Webster's Lemma 5.19. -/
def expansionTerm (wt : Fin ℓ → Dom R) (cross : I ⊕ Fin ℓ → I ⊕ Fin ℓ → ℤ)
    (lbl : Fin m → I ⊕ Fin ℓ) (g : Fin m → ℕ) : TensorSpace wt :=
  if IsNonviolating lbl g then 𝕍 ^ (-crossExp cross lbl g) • assignVector wt lbl g else 0

omit [DecidableEq I] in
theorem blockWord_snoc (lbl : Fin (m + 1) → I ⊕ Fin ℓ) (g : Fin m → ℕ) (a r : ℕ) :
    blockWord lbl (Fin.snoc (α := fun _ => ℕ) g a) r =
      blockWord (fun q => lbl q.castSucc) g r ++
        Sum.elim (fun i => if a = r + 1 then [i] else []) (fun _ => []) (lbl (Fin.last m)) := by
  rw [blockWord, List.ofFn_succ', List.concat_eq_append, List.flatten_append, blockWord]
  simp [blockLetter]
  rfl

omit [DecidableEq I] in
theorem assignKey_snoc_castSucc (lbl : Fin (m + 1) → I ⊕ Fin ℓ) (g : Fin m → ℕ) (a : ℕ)
    (p : Fin m) :
    assignKey lbl (Fin.snoc (α := fun _ => ℕ) g a) p.castSucc =
      assignKey (fun q => lbl q.castSucc) g p := by
  simp [assignKey]

omit [DecidableEq I] in
theorem assignKey_snoc_last (lbl : Fin (m + 1) → I ⊕ Fin ℓ) (g : Fin m → ℕ) (a : ℕ) :
    assignKey lbl (Fin.snoc (α := fun _ => ℕ) g a) (Fin.last m) =
      2 * a + if (lbl (Fin.last m)).isRight then 1 else 0 := by
  simp [assignKey]

omit [DecidableEq I] in
theorem crossExp_snoc (cross : I ⊕ Fin ℓ → I ⊕ Fin ℓ → ℤ) (lbl : Fin (m + 1) → I ⊕ Fin ℓ)
    (g : Fin m → ℕ) (a : ℕ) :
    crossExp cross lbl (Fin.snoc (α := fun _ => ℕ) g a) =
      crossExp cross (fun q => lbl q.castSucc) g +
        ∑ p : Fin m, if assignKey lbl (Fin.snoc (α := fun _ => ℕ) g a) (Fin.last m) <
            assignKey (fun q => lbl q.castSucc) g p then cross (lbl p.castSucc) (lbl (Fin.last m))
          else 0 := by
  rw [crossExp, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_castSucc (n := m), assignKey_snoc_castSucc, Fin.castSucc_lt_castSucc_iff,
    Fin.castSucc_lt_last, true_and, lt_irrefl, false_and, ite_false, Finset.sum_const_zero,
    add_zero, not_lt.2 (Fin.castSucc_lt_last _).le]
  rw [crossExp, ← Finset.sum_add_distrib]

omit [DecidableEq I] in
theorem isNonviolating_snoc (lbl : Fin (m + 1) → I ⊕ Fin ℓ) (g : Fin m → ℕ) (a : ℕ) :
    IsNonviolating lbl (Fin.snoc (α := fun _ => ℕ) g a) ↔
      IsNonviolating (fun q => lbl q.castSucc) g ∧
        ((lbl (Fin.last m)).isRight = false → a ≠ 0) := by
  simp [IsNonviolating, Fin.forall_fin_succ']

omit [DecidableEq I] in
/-- With the red letters numbered in order, summing a function of the red labels over the red
letters sums it over the first `redCount` labels. -/
theorem sum_red_letters (f : Fin ℓ → ℤ) :
    ∀ {m : ℕ} (lbl : Fin m → I ⊕ Fin ℓ),
      (∀ p r, lbl p = .inr r → (r : ℕ) = redsBefore lbl p) →
      (∑ p, Sum.elim (fun _ => 0) f (lbl p)) =
        ∑ r ∈ Finset.univ.filter (fun r : Fin ℓ => (r : ℕ) < redCount (List.ofFn lbl)), f r
  | 0, lbl, _ => by simp
  | m + 1, lbl, h => by
    have h0 : ∀ p r, (fun q => lbl q.castSucc) p = .inr r →
        (r : ℕ) = redsBefore (fun q => lbl q.castSucc) p := fun p r hp => by
      rw [← redsBefore_castSucc]; exact h _ _ hp
    rw [Fin.sum_univ_castSucc, sum_red_letters f (fun q => lbl q.castSucc) h0, List.ofFn_succ',
      List.concat_eq_append, redCount_append]
    rcases hl : lbl (Fin.last m) with i | r
    · simp
    · have hr := h _ _ hl
      rw [redsBefore_last] at hr
      rw [Sum.elim_inr, redCount_singleton_inr]
      set c := redCount (List.ofFn fun q => lbl q.castSucc)
      have hs : (Finset.univ.filter fun r' : Fin ℓ => (r' : ℕ) < c + 1) =
          insert r (Finset.univ.filter fun r' : Fin ℓ => (r' : ℕ) < c) := by
        ext r'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hs, Finset.sum_insert (by simp; omega), add_comm]

omit [DecidableEq I] in
theorem sum_blockWord (lbl : Fin m → I ⊕ Fin ℓ) (g : Fin m → ℕ) (r : ℕ) (f : I → ℤ) :
    ((blockWord lbl g r).map f).sum =
      ∑ p, Sum.elim (fun l => if g p = r + 1 then f l else 0) (fun _ => 0) (lbl p) := by
  rw [blockWord, List.map_flatten, List.sum_flatten, List.map_ofFn, List.map_ofFn,
    List.sum_ofFn]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Function.comp_apply, blockLetter]
  rcases lbl p with l | r'
  · by_cases h : g p = r + 1 <;> simp [h]
  · simp

omit [DecidableEq I] in
theorem mem_assignChoices {lbl : Fin m → I ⊕ Fin ℓ} {g : Fin m → ℕ} (hg : g ∈ assignments lbl)
    (p : Fin m) : g p ∈ assignChoices lbl p :=
  mem_assignList.1 hg p

omit [DecidableEq I] in
theorem assign_le_redCount {lbl : Fin m → I ⊕ Fin ℓ} {g : Fin m → ℕ} (hg : g ∈ assignments lbl)
    (p : Fin m) : g p ≤ redCount (List.ofFn lbl) := by
  have h := mem_assignChoices hg p
  have h' := redsBefore_le_redCount lbl p
  unfold assignChoices at h
  split_ifs at h with hp
  · simp at h; omega
  · simp at h; omega

omit [DecidableEq I] in
theorem assign_red {lbl : Fin m → I ⊕ Fin ℓ} {g : Fin m → ℕ} (hg : g ∈ assignments lbl)
    {p : Fin m} {r : Fin ℓ} (hp : lbl p = .inr r)
    (hidx : ∀ p r, lbl p = .inr r → (r : ℕ) = redsBefore lbl p) : g p = r := by
  have h := mem_assignChoices hg p
  unfold assignChoices at h
  rw [hp] at h
  simp at h
  rw [h, hidx p r hp]

omit [DecidableEq I] in
/-- **The exponent of the new letter**: assigning a final black letter `i` to block `r + 1`, it
crosses the red letters `r < j < c` and the black letters of the blocks after `r + 1`. -/
theorem crossExp_snoc_black (wt : Fin ℓ → Dom R) (cross : I ⊕ Fin ℓ → I ⊕ Fin ℓ → ℤ)
    (hred : ∀ j i, cross (.inr j) (.inl i) = (wt j).1 (ktilde R i))
    (hblack : ∀ l i, cross (.inl l) (.inl i) = -R.root l (ktilde R i))
    (lbl : Fin (m + 1) → I ⊕ Fin ℓ) {i : I} (hi : lbl (Fin.last m) = .inl i)
    (hidx : ∀ p r, lbl p = .inr r → (r : ℕ) = redsBefore lbl p)
    (hc : redCount (List.ofFn fun q => lbl q.castSucc) ≤ ℓ)
    {g : Fin m → ℕ} (hg : g ∈ assignments fun q => lbl q.castSucc) (r : Fin ℓ) :
    crossExp cross lbl (Fin.snoc (α := fun _ => ℕ) g (r + 1)) =
      crossExp cross (fun q => lbl q.castSucc) g +
        ∑ j : Fin ℓ, if r < j ∧ (j : ℕ) < redCount (List.ofFn fun q => lbl q.castSucc) then
          (wt j).1 (ktilde R i) -
            ((blockWord (fun q => lbl q.castSucc) g j).map fun l => R.root l (ktilde R i)).sum
          else 0 := by
  set lbl0 : Fin m → I ⊕ Fin ℓ := fun q => lbl q.castSucc
  set c := redCount (List.ofFn lbl0)
  have hidx0 : ∀ p r, lbl0 p = .inr r → (r : ℕ) = redsBefore lbl0 p := fun p r hp => by
    rw [← redsBefore_castSucc]; exact hidx _ _ hp
  rw [crossExp_snoc, assignKey_snoc_last, hi]
  congr 1
  have hsplit : ∀ p : Fin m,
      (if 2 * ((r : ℕ) + 1) + (if (Sum.inl i : I ⊕ Fin ℓ).isRight then 1 else 0) <
          assignKey lbl0 g p then cross (lbl0 p) (.inl i) else 0) =
        Sum.elim (fun _ => 0) (fun r' : Fin ℓ => if r < r' then (wt r').1 (ktilde R i) else 0)
            (lbl0 p) +
          Sum.elim (fun l => if (r : ℕ) + 1 < g p then -R.root l (ktilde R i) else 0)
            (fun _ => 0) (lbl0 p) := by
    intro p
    rcases hp : lbl0 p with l | r'
    · simp only [Sum.isRight_inl, Bool.false_eq_true, ite_false, add_zero, assignKey, hp,
        Sum.elim_inl, zero_add, hblack]
      by_cases h : (r : ℕ) + 1 < g p
      · rw [ite_eq_left (by omega), ite_eq_left h]
      · rw [ite_eq_right (by omega), ite_eq_right h]
    · have hgp := assign_red hg hp hidx0
      simp only [Sum.isRight_inl, Bool.false_eq_true, ite_false, add_zero, assignKey, hp,
        Sum.isRight_inr, ite_true, Sum.elim_inr, add_zero, hred, hgp]
      by_cases h : r < r'
      · rw [ite_eq_left (by rw [Fin.lt_def] at h; omega), ite_eq_left h]
      · rw [ite_eq_right (by rw [Fin.lt_def] at h; omega), ite_eq_right h]
  rw [Finset.sum_congr rfl fun p _ => hsplit p, Finset.sum_add_distrib,
    sum_red_letters _ lbl0 hidx0, Finset.sum_filter]
  have hb : ∀ p : Fin m,
      Sum.elim (fun l => if (r : ℕ) + 1 < g p then -R.root l (ktilde R i) else 0) (fun _ => 0)
          (lbl0 p) =
        -∑ j : Fin ℓ, if r < j ∧ (j : ℕ) < c then
          Sum.elim (fun l => if g p = (j : ℕ) + 1 then R.root l (ktilde R i) else 0) (fun _ => 0)
            (lbl0 p) else 0 := by
    intro p
    rcases lbl0 p with l | r'
    · simp only [Sum.elim_inl]
      have hgc : g p ≤ c := assign_le_redCount hg p
      by_cases h : (r : ℕ) + 1 < g p
      · rw [ite_eq_left h, Finset.sum_eq_single ⟨g p - 1, by omega⟩]
        · rw [ite_eq_left ⟨by rw [Fin.lt_def]; simp; omega, by simp; omega⟩,
            ite_eq_left (by simp; omega)]
        · intro j _ hj
          split_ifs with h1 h2
          · exact absurd (Fin.ext (by simp; omega)) hj
          · rfl
          · rfl
        · simp
      · rw [ite_eq_right h]
        symm
        rw [neg_eq_zero]
        refine Finset.sum_eq_zero fun j _ => ?_
        split_ifs with h1 h2
        · rw [Fin.lt_def] at h1; omega
        · rfl
        · rfl
    · simp
  rw [Finset.sum_congr rfl fun p _ => hb p, Finset.sum_neg_distrib, Finset.sum_comm,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_blockWord]
  by_cases h : r < j ∧ (j : ℕ) < c
  · rw [ite_eq_left h.2, ite_eq_left h.1, ite_eq_left h, Finset.sum_congr rfl fun p _ =>
      ite_eq_left (c := r < j ∧ (j : ℕ) < c) h, sub_eq_add_neg]
  · rw [ite_eq_right h, Finset.sum_congr rfl fun p _ => ite_eq_right (c := r < j ∧ (j : ℕ) < c) h,
      Finset.sum_const_zero, neg_zero, add_zero]
    by_cases h' : (j : ℕ) < c
    · rw [ite_eq_left h', ite_eq_right (fun h'' => h ⟨h'', h'⟩)]
    · rw [ite_eq_right h']

theorem tprod_smul_factors (wt : Fin ℓ → Dom R) (e : Fin ℓ → ℤ) (x : ∀ j, Factor (wt j)) :
    PiTensorProduct.tprod 𝕂 (fun j => 𝕍 ^ e j • x j) =
      𝕍 ^ (∑ j, e j) • PiTensorProduct.tprod 𝕂 x := by
  rw [MultilinearMap.map_smul_univ]
  congr 1
  generalize (Finset.univ : Finset (Fin ℓ)) = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih => rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, zpow_add₀ RatFunc.X_ne_zero]

/-- **One lowering of an assignment vector**: `F_i` in factor `r` with `K̃_{-i}` on the factors
`r < j < c` gives the assignment vector with a final letter `i` in block `r + 1`, scaled by the
weights of the factors it passes. -/
theorem lowerAt_assignVector (wt : Fin ℓ → Dom R) (lbl : Fin (m + 1) → I ⊕ Fin ℓ) {i : I}
    (hi : lbl (Fin.last m) = .inl i) (c : ℕ) (g : Fin m → ℕ) (r : Fin ℓ) :
    lowerAt wt c i r (assignVector wt (fun q => lbl q.castSucc) g) =
      𝕍 ^ (-∑ j : Fin ℓ, if r < j ∧ (j : ℕ) < c then
          (wt j).1 (ktilde R i) -
            ((blockWord (fun q => lbl q.castSucc) g j).map fun l => R.root l (ktilde R i)).sum
          else 0) •
        assignVector wt lbl (Fin.snoc (α := fun _ => ℕ) g (r + 1)) := by
  rw [assignVector, lowerAt_tprod, assignVector, ← Finset.sum_neg_distrib,
    ← tprod_smul_factors]
  congr 1
  funext j
  rw [blockWord_snoc, hi]
  simp only [Sum.elim_inl]
  unfold lowerFactor
  by_cases hj : j = r
  · subst hj
    rw [ite_eq_left rfl, ite_eq_right (fun h => lt_irrefl _ h.1), ite_eq_left rfl,
      neg_zero, zpow_zero, one_smul, wordVec_append_singleton]
    rfl
  · have hne : ¬ ((r : ℕ) + 1 = (j : ℕ) + 1) := fun h => hj (Fin.ext (by omega))
    rw [ite_eq_right hj, ite_eq_right hne, List.append_nil]
    by_cases hc : r < j ∧ (j : ℕ) < c
    · rw [ite_eq_left hc, ite_eq_left hc, DistribSMul.toLinearMap_apply, K_smul_wordVec]
      congr 2
      simp only [map_neg]
      have hneg : ∀ L : List I, (L.map fun l => -R.root l (ktilde R i)).sum =
          -(L.map fun l => R.root l (ktilde R i)).sum := by
        intro L; induction L with
        | nil => simp
        | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring
      rw [hneg]
      ring
    · rw [ite_eq_right hc, ite_eq_right hc, neg_zero, zpow_zero, one_smul]
      rfl

omit [DecidableEq I] in
theorem list_sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (l : List α) (f : α → List β)
    (h : β → M) : ((l.flatMap f).map h).sum = (l.map fun a => ((f a).map h).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

omit [DecidableEq I] in
theorem sum_filter_lt_eq_list {M : Type*} [AddCommMonoid M] {c : ℕ} (hc : c ≤ ℓ) (F : ℕ → M) :
    ∑ r ∈ Finset.univ.filter (fun r : Fin ℓ => (r : ℕ) < c), F r = ((List.range c).map F).sum := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun a => if a < c then F a else 0),
    ← Finset.sum_filter, show (Finset.range ℓ).filter (· < c) = Finset.range c by
      ext a; simp; omega]
  clear hc
  induction c with
  | zero => simp
  | succ c ih => rw [Finset.sum_range_succ, ih, ← List.sum_range_succ]

omit [DecidableEq I] in
theorem assignments_succ (lbl : Fin (m + 1) → I ⊕ Fin ℓ) :
    assignments lbl = (assignments fun q => lbl q.castSucc).flatMap fun g =>
      (assignChoices lbl (Fin.last m)).map fun a => Fin.snoc (α := fun _ => ℕ) g a := by
  change assignList (m + 1) _ = _
  rw [assignList]
  congr 2
  funext p
  simp [assignChoices, redsBefore_castSucc]

end Assignments

section Expansion

/-- **Webster's Lemma 5.19, expansion form** (arXiv:1309.3796v3): for a word whose red letters are
numbered in order, the loading vector is the sum, over the block assignments `g ∈ Φ` (no black
letter left of every red letter), of `q^{-e(g)}` times the assignment vector, where `e(g)` sums
`cross` over the pairs of letters that `g` reverses. Here `cross` is the crossing degree of a red
strand `λ_j` over a black strand `i` (`⟨λ_j, α̃_i⟩`) and of two black strands (`-α_l(α̃_i)`). -/
theorem loadingVector_ofFn_eq_sum (wt : Fin ℓ → Dom R) (cross : I ⊕ Fin ℓ → I ⊕ Fin ℓ → ℤ)
    (hred : ∀ j i, cross (.inr j) (.inl i) = (wt j).1 (ktilde R i))
    (hblack : ∀ l i, cross (.inl l) (.inl i) = -R.root l (ktilde R i)) :
    ∀ {m : ℕ} (lbl : Fin m → I ⊕ Fin ℓ),
      (∀ p r, lbl p = .inr r → (r : ℕ) = redsBefore lbl p) → redCount (List.ofFn lbl) ≤ ℓ →
      loadingVector wt (List.ofFn lbl) = ((assignments lbl).map (expansionTerm wt cross lbl)).sum
  | 0, lbl, _, _ => by
    rw [List.ofFn_zero, loadingVector_nil]
    change _ = (List.map (expansionTerm wt cross lbl) [fun p => p.elim0]).sum
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, expansionTerm]
    rw [ite_eq_left (show IsNonviolating lbl (fun p => p.elim0) from fun p => p.elim0)]
    simp [crossExp, assignVector, blockWord]
  | m + 1, lbl, hidx, hcount => by
    set lbl0 : Fin m → I ⊕ Fin ℓ := fun q => lbl q.castSucc
    have hidx0 : ∀ p r, lbl0 p = .inr r → (r : ℕ) = redsBefore lbl0 p := fun p r hp => by
      rw [← redsBefore_castSucc]; exact hidx _ _ hp
    have hsplit : List.ofFn lbl = List.ofFn lbl0 ++ [lbl (Fin.last m)] := by
      rw [List.ofFn_succ', List.concat_eq_append]
    have hc0 : redCount (List.ofFn lbl0) ≤ ℓ := by
      rw [hsplit, redCount_append] at hcount; omega
    have ih := loadingVector_ofFn_eq_sum wt cross hred hblack lbl0 hidx0 hc0
    rw [hsplit, assignments_succ, list_sum_map_flatMap]
    rcases hl : lbl (Fin.last m) with i | r
    · rw [loadingVector_append_inl, ih, map_list_sum, List.map_map]
      refine congrArg List.sum (List.map_congr_left fun g hg => ?_)
      simp only [Function.comp_apply, assignChoices, hl, Sum.isRight_inl, Bool.false_eq_true,
        ite_false, redsBefore_last, List.range_succ_eq_map, List.map_cons, List.sum_cons,
        List.map_map]
      have h0 : expansionTerm wt cross lbl (Fin.snoc (α := fun _ => ℕ) g 0) = 0 := by
        unfold expansionTerm
        rw [ite_eq_right]
        intro h
        exact ((isNonviolating_snoc lbl g 0).1 h).2 (by simp [hl]) rfl
      rw [h0, zero_add]
      by_cases hv : IsNonviolating lbl0 g
      · unfold expansionTerm
        rw [ite_eq_left hv, map_smul, partialLower, LinearMap.sum_apply, Finset.smul_sum]
        rw [Finset.sum_congr rfl fun (r : Fin ℓ) hr => show
            𝕍 ^ (-crossExp cross lbl0 g) • lowerAt wt (redCount (List.ofFn lbl0)) i r
              (assignVector wt lbl0 g) =
            expansionTerm wt cross lbl (Fin.snoc (α := fun _ => ℕ) g ((r : ℕ) + 1)) by
          unfold expansionTerm
          rw [ite_eq_left ((isNonviolating_snoc lbl g _).2 ⟨hv, fun _ => by omega⟩),
            crossExp_snoc_black wt cross hred hblack lbl hl hidx hc0 hg r,
            lowerAt_assignVector wt lbl hl, smul_smul, ← zpow_add₀ RatFunc.X_ne_zero, neg_add]]
        rw [sum_filter_lt_eq_list hc0
          (fun a => expansionTerm wt cross lbl (Fin.snoc (α := fun _ => ℕ) g (a + 1)))]
        rfl
      · have hz : ∀ a : ℕ, expansionTerm wt cross lbl (Fin.snoc (α := fun _ => ℕ) g (a + 1)) = 0 :=
          fun a => by
            unfold expansionTerm
            rw [ite_eq_right]
            intro h
            exact hv ((isNonviolating_snoc lbl g _).1 h).1
        unfold expansionTerm
        rw [ite_eq_right hv, map_zero]
        symm
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
        exact hz a
    · rw [loadingVector_append_inr, ih]
      refine congrArg List.sum (List.map_congr_left fun g hg => ?_)
      simp only [assignChoices, hl, Sum.isRight_inr, ite_true, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      set c := redsBefore lbl (Fin.last m)
      have hv : IsNonviolating lbl (Fin.snoc (α := fun _ => ℕ) g c) ↔ IsNonviolating lbl0 g := by
        rw [isNonviolating_snoc, hl]
        simp only [Sum.isRight_inr, Bool.true_eq_false, false_implies, and_true]
        rfl
      have he : crossExp cross lbl (Fin.snoc (α := fun _ => ℕ) g c) = crossExp cross lbl0 g := by
        rw [crossExp_snoc, assignKey_snoc_last, hl, Finset.sum_eq_zero, add_zero]
        intro p _
        rw [ite_eq_right]
        intro h
        have hp := assign_le_redCount hg p
        have hc : c = redCount (List.ofFn lbl0) := redsBefore_last lbl
        simp only [Sum.isRight_inr, ite_true, assignKey] at h
        split_ifs at h <;> omega
      have ha : assignVector wt lbl (Fin.snoc (α := fun _ => ℕ) g c) = assignVector wt lbl0 g := by
        unfold assignVector
        congr 1
        funext j
        rw [blockWord_snoc, hl]
        simp only [Sum.elim_inr, List.append_nil]
        rfl
      unfold expansionTerm
      by_cases h : IsNonviolating lbl0 g
      · rw [ite_eq_left h, ite_eq_left (hv.2 h), he, ha]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (hv.1 h'))]

end Expansion


end Categorification.Stendhal.FirstWeight
