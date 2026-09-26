/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.DividedPowerCharacters
import Categorification.KLR.Prop213

/-!
# KL I, Proposition 2.13, Corollary 2.14 and Corollary 2.15 for divided-power expressions

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.5 (TeX lines ~1640–1721).

`Categorification.KLR.Prop213` proves Proposition 2.13 and Corollary 2.14 for idempotents
`divIdem t bs` given by a sequence `t` and a list `bs` of divided-power blocks away from the
positions being changed. Here we

* identify these with the idempotents `1_i = divIdemOf d h` of divided-power expressions
  `i = i_1^{(n_1)} ⋯ i_r^{(n_r)}` (lists `d` of pairs `(i_a, n_a)`): blocks of size `1` are
  trivial (`divIdem_bigBlocks`), the product of the blocks does not depend on their order
  (`divIdem_perm`), and `divIdemOf (d' ++ mid ++ d'')` is `divIdem` of the expansion with the
  context blocks of `d'`, `d''` and the big blocks of `mid` (`divIdemOf_append_mid`);
* restate Proposition 2.13 for `divIdemOf` (`prop213_zero_divIdemOf`,
  `prop213_neg_one_divIdemOf`);
* prove the **graded** Corollary 2.14 (`cor214_zero_graded`, `cor214_neg_one_graded`:
  `(1_{…iji…} M)_d ≅ (1_{…i^{(2)}j…} M)_{d+1} × (1_{…ji^{(2)}…} M)_{d+1}`, i.e.
  `1_{…iji…} M {1} ≅ 1_{…i^{(2)}j…} M ⊕ 1_{…ji^{(2)}…} M`) and its graded-dimension forms;
* prove **Corollary 2.15** for the characters `ch(M, i) = q^{-⟨i⟩} gdim (1_i M)`:
  `cor215_zero` (`ch(M, …ij…) = ch(M, …ji…)` for `i · j = 0`), `cor215_neg_one`
  (`ch(M, …iji…) = ch(M, …i^{(2)}j…) + ch(M, …ji^{(2)}…)` for `i · j = -1`) and `cor215_divided`
  (`ch(M, …i^{(a)}i^{(b)}…) = [a+b choose a] ch(M, …i^{(a+b)}…)`, from
  `Categorification.KLR.DividedPowerCharacters`).

Throughout, `i · j = 0` means `i ≠ j` and `i`, `j` are not joined by an edge of the simply-laced
graph `Γ`, and `i · j = -1` means that they are joined by an edge.
-/

noncomputable section

namespace Categorification.KLR

open Graded HahnSeries KLRAlgebra TypeA

/-! ### Lists -/

section Lists

variable {α : Type*}

theorem getElem_append_swap (pre post : List α) (x y : α) {n : ℕ}
    (hn : n < (pre ++ y :: x :: post).length) :
    (pre ++ y :: x :: post)[n] =
      (pre ++ x :: y :: post)[swapNat pre.length n]'(by
        have := swapNat_cases pre.length n
        simp only [List.length_append, List.length_cons] at hn ⊢; omega) := by
  rcases swapNat_cases pre.length n with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · simp only [h2]; subst h1; simp
  · simp only [h2]; subst h1; simp
  · simp only [h3]
    by_cases h : n < pre.length
    · rw [List.getElem_append_left h, List.getElem_append_left h]
    · have h' : pre.length + 2 ≤ n := by omega
      rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h'
      simp [show pre.length + 2 + r - pre.length = r + 2 by omega]

end Lists

/-! ### Blocks of divided-power expressions -/

section Blocks

variable {I : Type*}

theorem blocksDiv_append (d₁ d₂ : List (I × ℕ)) (p : ℕ) :
    blocksDiv (d₁ ++ d₂) p = blocksDiv d₁ p ++ blocksDiv d₂ (p + (expandDiv d₁).length) := by
  induction d₁ generalizing p with
  | nil => simp [blocksDiv, expandDiv]
  | cons q d ih =>
    simp only [List.cons_append, blocksDiv, ih, List.cons_append, List.cons.injEq, true_and]
    congr 2
    simp [expandDiv, List.flatMap_cons]
    omega

theorem add_le_of_mem_blocksDiv {d : List (I × ℕ)} {p : ℕ} {b : ℕ × ℕ}
    (h : b ∈ blocksDiv d p) : b.1 + b.2 ≤ p + (expandDiv d).length := by
  induction d generalizing p with
  | nil => simp [blocksDiv] at h
  | cons q d ih =>
    have hl : (expandDiv (q :: d)).length = q.2 + (expandDiv d).length := by
      simp [expandDiv, List.flatMap_cons]
    rw [hl]
    rcases List.mem_cons.1 h with rfl | h
    · simp only; omega
    · have := ih h; omega

/-- The divided-power blocks of size at least `2` (blocks of size `0` or `1` are trivial). -/
def bigBlocks (bs : List (ℕ × ℕ)) : List (ℕ × ℕ) := bs.filter fun b => 2 ≤ b.2

theorem mem_bigBlocks {bs : List (ℕ × ℕ)} {b : ℕ × ℕ} : b ∈ bigBlocks bs ↔ b ∈ bs ∧ 2 ≤ b.2 := by
  simp [bigBlocks]

theorem bigBlocks_append (bs bs' : List (ℕ × ℕ)) :
    bigBlocks (bs ++ bs') = bigBlocks bs ++ bigBlocks bs' := List.filter_append _ _

variable [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν : Multiset I}

local notation "A" => KLRAlgebra k Q ν

theorem blocksElt_bigBlocks (bs : List (ℕ × ℕ)) :
    (blocksElt (bigBlocks bs) : A) = blocksElt bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [blocksElt_cons, bigBlocks, List.filter_cons]
    split_ifs with h
    · rw [blocksElt_cons]; exact congrArg _ ih
    · have hb : b.2 = 0 ∨ b.2 = 1 := by simp at h; omega
      rw [← bigBlocks, ih]
      rcases hb with hb | hb
      · rw [hb, blockElt_zero, one_mul]
      · rw [hb, blockElt_one, one_mul]

theorem divIdem_bigBlocks (t : Seq ν) (bs : List (ℕ × ℕ)) :
    (divIdem t (bigBlocks bs) : A) = divIdem t bs := by
  rw [divIdem, divIdem, blocksElt_bigBlocks]

omit [DecidableEq I] in
theorem KLRAlgebra.IsBlocks.sublist {t : Seq ν} {bs bs' : List (ℕ × ℕ)} (h : IsBlocks t bs)
    (hs : bs'.Sublist bs) : IsBlocks t bs' :=
  ⟨fun b hb => h.le b (hs.subset hb), fun b hb => h.const b (hs.subset hb), h.disj.sublist hs⟩

omit [DecidableEq I] in
theorem KLRAlgebra.IsBlocks.perm {t : Seq ν} {bs bs' : List (ℕ × ℕ)} (h : IsBlocks t bs)
    (hp : bs.Perm bs') : IsBlocks t bs' :=
  ⟨fun b hb => h.le b (hp.mem_iff.2 hb), fun b hb => h.const b (hp.mem_iff.2 hb),
    (hp.pairwise_iff fun {_ _} h => h.symm).1 h.disj⟩

/-- The product of disjoint blocks does not depend on their order. -/
theorem divIdem_perm {t : Seq ν} {bs bs' : List (ℕ × ℕ)} (h : IsBlocks t bs)
    (hp : bs.Perm bs') : (divIdem t bs : A) = divIdem t bs' := by
  rw [divIdem, divIdem, blocksElt, blocksElt]
  congr 1
  refine (hp.map _).prod_eq' ?_
  refine List.Pairwise.map _ (fun b c hbc => ?_) h.disj
  exact commute_blockElt_blockElt hbc

end Blocks

/-! ### Divided-power expressions `d' ++ mid ++ d''` -/

section Expr

variable {I : Type*} {ν : Multiset I}

theorem expandDiv_append (d₁ d₂ : List (I × ℕ)) :
    expandDiv (d₁ ++ d₂) = expandDiv d₁ ++ expandDiv d₂ := List.flatMap_append

/-- The context blocks of `d' ++ mid ++ d''`: the big blocks of `d'` and of `d''`, where `mid`
has expansion of length `r`. -/
def ctxBlocks (d' d'' : List (I × ℕ)) (r : ℕ) : List (ℕ × ℕ) :=
  bigBlocks (blocksDiv d' 0) ++ bigBlocks (blocksDiv d'' ((expandDiv d').length + r))

theorem ctxBlocks_avoid (d' d'' : List (I × ℕ)) (r : ℕ) :
    ∀ b ∈ ctxBlocks d' d'' r, b.1 + b.2 ≤ (expandDiv d').length ∨
      (expandDiv d').length + r ≤ b.1 := by
  intro b hb
  rcases List.mem_append.1 hb with hb | hb
  · have := add_le_of_mem_blocksDiv (mem_bigBlocks.1 hb).1; left; omega
  · have := le_of_mem_blocksDiv (mem_bigBlocks.1 hb).1; right; omega

theorem bigBlocks_blocksDiv_append (d' mid d'' : List (I × ℕ)) :
    bigBlocks (blocksDiv (d' ++ mid ++ d'') 0) =
      bigBlocks (blocksDiv d' 0) ++ bigBlocks (blocksDiv mid (expandDiv d').length) ++
        bigBlocks (blocksDiv d'' ((expandDiv d').length + (expandDiv mid).length)) := by
  rw [blocksDiv_append, blocksDiv_append, bigBlocks_append, bigBlocks_append, expandDiv_append,
    List.length_append, zero_add, zero_add]

/-- `Seq.ofList (pre ++ x :: y :: post) = s_{|pre|} • Seq.ofList (pre ++ y :: x :: post)`. -/
theorem Seq.ofList_swap (pre post : List I) (x y : I)
    (h : ((pre ++ y :: x :: post : List I) : Multiset I) = ν)
    (h' : ((pre ++ x :: y :: post : List I) : Multiset I) = ν) :
    Seq.ofList (pre ++ x :: y :: post) h' =
      sadj (Multiset.card ν) pre.length • Seq.ofList (pre ++ y :: x :: post) h := by
  have hm : (pre ++ y :: x :: post).length = Multiset.card ν := by
    rw [← Multiset.coe_card, h]
  apply Subtype.ext
  funext a
  have ha : (a : ℕ) < (pre ++ x :: y :: post).length := by
    simp only [List.length_append, List.length_cons] at hm ⊢; omega
  rw [Seq.smul_apply, sadj_symm]
  change (Seq.ofList _ h').lbl a = (Seq.ofList _ h).lbl _
  rw [Seq.ofList_lbl, Seq.ofList_lbl, getElem_append_swap pre post y x ha]
  congr 1
  rw [sadj_val_of_lt (by simp only [List.length_append, List.length_cons] at hm; omega)]

theorem Seq.ofList_lbl_length (pre rest : List I) (x : I)
    (h : ((pre ++ x :: rest : List I) : Multiset I) = ν) (hp : pre.length < Multiset.card ν) :
    (Seq.ofList (pre ++ x :: rest) h).lbl ⟨pre.length, hp⟩ = x := by
  rw [Seq.ofList_lbl]; simp

end Expr

/-! ### `divIdemOf` in the `(t, bs)` form of `Categorification.KLR.Prop213` -/

section Link

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ν : Multiset I}

local notation "A" => KLRAlgebra k Q ν

omit [DecidableEq I] in
theorem isBlocks_bigBlocks_ofList (d : List (I × ℕ)) (h : (expandDiv d : Multiset I) = ν) :
    IsBlocks (Seq.ofList (expandDiv d) h) (bigBlocks (blocksDiv d 0)) :=
  (isBlocks_ofList d h).sublist List.filter_sublist

/-- **`divIdemOf` as `divIdem`**: for `d = d' ++ mid ++ d''`, `1_d = divIdem î bs` where `bs`
consists of the big blocks of `mid` followed by the context blocks of `d'` and `d''`. -/
theorem divIdemOf_append_mid (d' mid d'' : List (I × ℕ))
    (h : (expandDiv (d' ++ mid ++ d'') : Multiset I) = ν) :
    (divIdemOf (d' ++ mid ++ d'') h : A) = divIdem (Seq.ofList _ h)
      (bigBlocks (blocksDiv mid (expandDiv d').length) ++
        ctxBlocks d' d'' (expandDiv mid).length) := by
  rw [divIdemOf, ← divIdem_bigBlocks]
  refine divIdem_perm (isBlocks_bigBlocks_ofList _ h) ?_
  rw [bigBlocks_blocksDiv_append, ctxBlocks, ← List.append_assoc]
  exact (List.perm_append_comm.append_right _).trans (by rw [List.append_assoc])

omit [DecidableEq I] in
theorem isBlocks_ctxBlocks (d' mid d'' : List (I × ℕ))
    (h : (expandDiv (d' ++ mid ++ d'') : Multiset I) = ν) :
    IsBlocks (Seq.ofList _ h) (bigBlocks (blocksDiv mid (expandDiv d').length) ++
      ctxBlocks d' d'' (expandDiv mid).length) := by
  refine (isBlocks_bigBlocks_ofList _ h).perm ?_
  rw [bigBlocks_blocksDiv_append, ctxBlocks, ← List.append_assoc]
  exact (List.perm_append_comm.append_right _).trans (by rw [List.append_assoc])

theorem divIdemOf_single_single (d' d'' : List (I × ℕ)) (i j : I)
    (h : (expandDiv (d' ++ [(i, 1), (j, 1)] ++ d'') : Multiset I) = ν) :
    (divIdemOf (d' ++ [(i, 1), (j, 1)] ++ d'') h : A) =
      divIdem (Seq.ofList _ h) (ctxBlocks d' d'' 2) := by
  rw [divIdemOf_append_mid]
  simp [blocksDiv, bigBlocks, expandDiv]

theorem divIdemOf_iji (d' d'' : List (I × ℕ)) (i j : I)
    (h : (expandDiv (d' ++ [(i, 1), (j, 1), (i, 1)] ++ d'') : Multiset I) = ν) :
    (divIdemOf (d' ++ [(i, 1), (j, 1), (i, 1)] ++ d'') h : A) =
      divIdem (Seq.ofList _ h) (ctxBlocks d' d'' 3) := by
  rw [divIdemOf_append_mid]
  simp [blocksDiv, bigBlocks, expandDiv]

theorem divIdemOf_i2j (d' d'' : List (I × ℕ)) (i j : I)
    (h : (expandDiv (d' ++ [(i, 2), (j, 1)] ++ d'') : Multiset I) = ν) :
    (divIdemOf (d' ++ [(i, 2), (j, 1)] ++ d'') h : A) =
      divIdem (Seq.ofList _ h) (((expandDiv d').length, 2) :: ctxBlocks d' d'' 3) := by
  rw [divIdemOf_append_mid]
  simp [blocksDiv, bigBlocks, expandDiv]

theorem divIdemOf_ji2 (d' d'' : List (I × ℕ)) (i j : I)
    (h : (expandDiv (d' ++ [(j, 1), (i, 2)] ++ d'') : Multiset I) = ν) :
    (divIdemOf (d' ++ [(j, 1), (i, 2)] ++ d'') h : A) =
      divIdem (Seq.ofList _ h) (((expandDiv d').length + 1, 2) :: ctxBlocks d' d'' 3) := by
  rw [divIdemOf_append_mid]
  simp [blocksDiv, bigBlocks, expandDiv]

end Link

/-! ### Proposition 2.13 for divided-power expressions -/

section Prop213

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {Γ : SimpleGraph I}
  [DecidableRel Γ.Adj] {ν : Multiset I}

local notation "A" => R1 k Γ ν

omit [DecidableEq I] in
theorem expandDiv_ij (d' d'' : List (I × ℕ)) (i j : I) :
    expandDiv (d' ++ [(i, 1), (j, 1)] ++ d'') = expandDiv d' ++ i :: j :: expandDiv d'' := by
  rw [expandDiv_append, expandDiv_append]; simp [expandDiv]

omit [DecidableEq I] in
theorem expandDiv_iji (d' d'' : List (I × ℕ)) (i j : I) :
    expandDiv (d' ++ [(i, 1), (j, 1), (i, 1)] ++ d'') =
      expandDiv d' ++ i :: j :: i :: expandDiv d'' := by
  rw [expandDiv_append, expandDiv_append]; simp [expandDiv]

omit [DecidableEq I] in
theorem expandDiv_i2j (d' d'' : List (I × ℕ)) (i j : I) :
    expandDiv (d' ++ [(i, 2), (j, 1)] ++ d'') =
      (expandDiv d' ++ [i]) ++ i :: j :: expandDiv d'' := by
  rw [expandDiv_append, expandDiv_append]; simp [expandDiv]

omit [DecidableEq I] in
theorem expandDiv_ji2 (d' d'' : List (I × ℕ)) (i j : I) :
    expandDiv (d' ++ [(j, 1), (i, 2)] ++ d'') =
      expandDiv d' ++ j :: i :: (i :: expandDiv d'') := by
  rw [expandDiv_append, expandDiv_append]; simp [expandDiv]

omit [DecidableEq I] in
theorem card_eq_length {l : List I} (h : (l : Multiset I) = ν) : Multiset.card ν = l.length := by
  rw [← h, Multiset.coe_card]

/-- **KL I, Proposition 2.13, case `i · j = -1`**, for divided-power expressions:
`1_{…iji…}` is the sum of two orthogonal idempotents `f₁ + f₂` with
`1_{…i^{(2)}j…} = a₁ b₁`, `f₁ = b₁ a₁` and `1_{…ji^{(2)}…} = a₂ b₂`, `f₂ = b₂ a₂`, where `a₁, a₂`
have degree `1` and `b₁, b₂` degree `-1` (the entries of the paper's matrices `B₀` and `B₁`,
`prop213_neg_one`). -/
theorem prop213_neg_one_divIdemOf (d' d'' : List (I × ℕ)) {i j : I} (hadj : Γ.Adj i j)
    (h₁ : (expandDiv (d' ++ [(i, 1), (j, 1), (i, 1)] ++ d'') : Multiset I) = ν)
    (h₂ : (expandDiv (d' ++ [(i, 2), (j, 1)] ++ d'') : Multiset I) = ν)
    (h₃ : (expandDiv (d' ++ [(j, 1), (i, 2)] ++ d'') : Multiset I) = ν) :
    ∃ f₁ f₂ a₁ b₁ a₂ b₂ : A, IsOrthDecomp (divIdemOf _ h₁) f₁ f₂ ∧
      IsEquivPair a₁ b₁ (divIdemOf _ h₂) f₁ ∧ IsEquivPair a₂ b₂ (divIdemOf _ h₃) f₂ ∧
      a₁ ∈ (klGradingDatum k Γ).grade ν 1 ∧ b₁ ∈ (klGradingDatum k Γ).grade ν (-1) ∧
      a₂ ∈ (klGradingDatum k Γ).grade ν 1 ∧ b₂ ∈ (klGradingDatum k Γ).grade ν (-1) := by
  set pre := expandDiv d'
  set post := expandDiv d''
  have e₁ := expandDiv_iji d' d'' i j
  have h₁' : ((pre ++ i :: j :: i :: post : List I) : Multiset I) = ν := e₁ ▸ h₁
  set t := Seq.ofList (pre ++ i :: j :: i :: post) h₁'
  have ht₁ : Seq.ofList _ h₁ = t := Seq.ofList_congr e₁ _ _
  have ht₂ : Seq.ofList _ h₂ = sadj (Multiset.card ν) (pre.length + 1) • t := by
    have e₂ := expandDiv_i2j d' d'' i j
    rw [Seq.ofList_congr e₂ h₂ (e₂ ▸ h₂), Seq.ofList_swap (pre ++ [i]) post i j
      (by rw [List.append_assoc]; exact h₁'), List.length_append, List.length_singleton]
    congr 1
    exact Seq.ofList_congr (by simp) _ _
  have ht₃ : Seq.ofList _ h₃ = sadj (Multiset.card ν) pre.length • t := by
    have e₃ := expandDiv_ji2 d' d'' i j
    rw [Seq.ofList_congr e₃ h₃ (e₃ ▸ h₃), Seq.ofList_swap pre (i :: post) j i h₁']
  have hlen := card_eq_length h₁'
  simp only [List.length_append, List.length_cons] at hlen
  have hm : pre.length + 2 < Multiset.card ν := by omega
  have hb : IsBlocks t (ctxBlocks d' d'' 3) := by
    have := isBlocks_ctxBlocks d' [(i, 1), (j, 1), (i, 1)] d'' h₁
    rw [show bigBlocks (blocksDiv [(i, 1), (j, 1), (i, 1)] pre.length) = [] by
      simp [blocksDiv, bigBlocks], show (expandDiv [(i, 1), (j, 1), (i, 1)]).length = 3 by
      simp [expandDiv], List.nil_append, ht₁] at this
    exact this
  have hl0 : t.lbl ⟨pre.length, by omega⟩ = i := Seq.ofList_lbl_length _ _ _ _ _
  have hl1 : t.lbl ⟨pre.length + 1, by omega⟩ = j := by
    rw [Seq.ofList_lbl]; simp
  have hl2 : t.lbl ⟨pre.length + 2, hm⟩ = i := by
    rw [Seq.ofList_lbl]; simp
  have ht : t.lbl ⟨pre.length, by omega⟩ = t.lbl ⟨pre.length + 2, hm⟩ := by rw [hl0, hl2]
  have hadj' : Γ.Adj (t.lbl ⟨pre.length, by omega⟩) (t.lbl ⟨pre.length + 1, by omega⟩) := by
    rw [hl0, hl1]; exact hadj
  have H := prop213_neg_one (k := k) hb hm ht hadj' (ctxBlocks_avoid d' d'' 3)
  have D := prop213_neg_one_degrees (k := k) hb hm ht hadj' (ctxBlocks_avoid d' d'' 3)
  rw [divIdemOf_iji, divIdemOf_i2j, divIdemOf_ji2, ht₁, ht₂, ht₃]
  exact ⟨_, _, _, _, _, _, H.1, H.2.1, H.2.2, D.1, D.2.2.1, D.2.1, D.2.2.2⟩

/-- **KL I, Proposition 2.13, case `i · j = 0`**, for divided-power expressions:
`1_{…ij…} = a b` and `1_{…ji…} = b a` with `a, b` of degree `0` (multiplication by the
crossing, `prop213_zero`). -/
theorem prop213_zero_divIdemOf (d' d'' : List (I × ℕ)) {i j : I} (hne : i ≠ j)
    (hadj : ¬ Γ.Adj i j)
    (h₁ : (expandDiv (d' ++ [(i, 1), (j, 1)] ++ d'') : Multiset I) = ν)
    (h₂ : (expandDiv (d' ++ [(j, 1), (i, 1)] ++ d'') : Multiset I) = ν) :
    ∃ a b : A, IsEquivPair a b (divIdemOf _ h₁) (divIdemOf _ h₂) ∧
      a ∈ (klGradingDatum k Γ).grade ν 0 ∧ b ∈ (klGradingDatum k Γ).grade ν 0 := by
  set pre := expandDiv d'
  set post := expandDiv d''
  have e₁ := expandDiv_ij d' d'' i j
  have h₁' : ((pre ++ i :: j :: post : List I) : Multiset I) = ν := e₁ ▸ h₁
  set t := Seq.ofList (pre ++ i :: j :: post) h₁'
  have ht₁ : Seq.ofList _ h₁ = t := Seq.ofList_congr e₁ _ _
  have ht₂ : Seq.ofList _ h₂ = sadj (Multiset.card ν) pre.length • t := by
    have e₂ := expandDiv_ij d' d'' j i
    rw [Seq.ofList_congr e₂ h₂ (e₂ ▸ h₂), Seq.ofList_swap pre post j i h₁']
  have hlen := card_eq_length h₁'
  simp only [List.length_append, List.length_cons] at hlen
  have hm : pre.length + 1 < Multiset.card ν := by omega
  have hb : IsBlocks t (ctxBlocks d' d'' 2) := by
    have := isBlocks_ctxBlocks d' [(i, 1), (j, 1)] d'' h₁
    rw [show bigBlocks (blocksDiv [(i, 1), (j, 1)] pre.length) = [] by
      simp [blocksDiv, bigBlocks], show (expandDiv [(i, 1), (j, 1)]).length = 2 by
      simp [expandDiv], List.nil_append, ht₁] at this
    exact this
  have hl0 : t.lbl ⟨pre.length, by omega⟩ = i := Seq.ofList_lbl_length _ _ _ _ _
  have hl1 : t.lbl ⟨pre.length + 1, hm⟩ = j := by
    rw [Seq.ofList_lbl]; simp
  have hne' : t.lbl ⟨pre.length, by omega⟩ ≠ t.lbl ⟨pre.length + 1, hm⟩ := by rw [hl0, hl1]; exact hne
  have hadj' : ¬ Γ.Adj (t.lbl ⟨pre.length, by omega⟩) (t.lbl ⟨pre.length + 1, hm⟩) := by
    rw [hl0, hl1]; exact hadj
  have H := prop213_zero (k := k) hb hm hne' hadj' (ctxBlocks_avoid d' d'' 2)
  have D := prop213_zero_degrees (k := k) hb hm hne' hadj' (ctxBlocks_avoid d' d'' 2)
  rw [divIdemOf_single_single, divIdemOf_single_single, ht₁, ht₂]
  exact ⟨_, _, H, D.1, D.2⟩

end Prop213

/-! ### Corollaries 2.14 (graded) and 2.15 -/

section Cor

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {Γ : SimpleGraph I}
  [DecidableRel Γ.Adj] {ν : Multiset I}

local notation "A" => R1 k Γ ν

omit [DecidableEq I] in
theorem divAngle_append (d₁ d₂ : List (I × ℕ)) : divAngle (d₁ ++ d₂) = divAngle d₁ + divAngle d₂ := by
  simp [divAngle]

/-- **KL I, Corollary 2.14, case `i · j = -1`, graded**: for every graded `R(ν)`-module `M`
and every degree `e`,
`(1_{…iji…} M)_e ≅ (1_{…i^{(2)}j…} M)_{e+1} × (1_{…ji^{(2)}…} M)_{e+1}`,
i.e. `1_{…iji…} M {1} ≅ 1_{…i^{(2)}j…} M ⊕ 1_{…ji^{(2)}…} M`. -/
theorem cor214_neg_one_graded (M : GMod ((klGradingDatum k Γ).grade ν)) (d' d'' : List (I × ℕ))
    {i j : I} (hadj : Γ.Adj i j)
    (h₁ : (expandDiv (d' ++ [(i, 1), (j, 1), (i, 1)] ++ d'') : Multiset I) = ν)
    (h₂ : (expandDiv (d' ++ [(i, 2), (j, 1)] ++ d'') : Multiset I) = ν)
    (h₃ : (expandDiv (d' ++ [(j, 1), (i, 2)] ++ d'') : Multiset I) = ν) (e : ℤ) :
    Nonempty (idem M.grading (divIdemOf _ h₁ : A) e ≃ₗ[k]
      idem M.grading (divIdemOf _ h₂ : A) (e + 1) × idem M.grading (divIdemOf _ h₃ : A) (e + 1)) := by
  obtain ⟨f₁, f₂, a₁, b₁, a₂, b₂, H, H₁, H₂, ha₁, hb₁, ha₂, hb₂⟩ :=
    prop213_neg_one_divIdemOf (k := k) d' d'' hadj h₁ h₂ h₃
  have S := isSplitting_of_isOrthDecomp H H₁ H₂
  have E := idemSplitEquiv (ℳ := M.grading) (dg := ![-1, -1]) S
    (fun j => by fin_cases j <;> simpa) (fun j => by fin_cases j <;> simpa) e
  rw [show e + 1 = e - -1 by ring]
  exact ⟨E.trans (LinearEquiv.piFinTwo k _)⟩

/-- **KL I, Corollary 2.14, case `i · j = 0`, graded**: `(1_{…ij…} M)_e ≅ (1_{…ji…} M)_e`. -/
theorem cor214_zero_graded (M : GMod ((klGradingDatum k Γ).grade ν)) (d' d'' : List (I × ℕ))
    {i j : I} (hne : i ≠ j) (hadj : ¬ Γ.Adj i j)
    (h₁ : (expandDiv (d' ++ [(i, 1), (j, 1)] ++ d'') : Multiset I) = ν)
    (h₂ : (expandDiv (d' ++ [(j, 1), (i, 1)] ++ d'') : Multiset I) = ν) (e : ℤ) :
    Nonempty (idem M.grading (divIdemOf _ h₁ : A) e ≃ₗ[k] idem M.grading (divIdemOf _ h₂ : A) e) := by
  obtain ⟨a, b, H, ha, hb⟩ := prop213_zero_divIdemOf (k := k) d' d'' hne hadj h₁ h₂
  have E := idemSplitEquiv (ℳ := M.grading) (dg := fun _ => 0) (isSplitting_of_isEquivPair H)
    (fun _ => ha) (fun _ => by simpa using hb) e
  exact ⟨E.trans ((LinearEquiv.funUnique Unit k _).trans
    (LinearEquiv.ofEq _ _ (congrArg (idem M.grading _) (sub_zero e))))⟩

/-- Graded dimensions, case `i · j = -1`:
`gdim (1_{…iji…} M) = q^{-1} (gdim (1_{…i^{(2)}j…} M) + gdim (1_{…ji^{(2)}…} M))`. -/
theorem gdim_divIdemOf_neg_one (M : GMod ((klGradingDatum k Γ).grade ν)) [HasGdim M.grading]
    (d' d'' : List (I × ℕ)) {i j : I} (hadj : Γ.Adj i j)
    (h₁ : (expandDiv (d' ++ [(i, 1), (j, 1), (i, 1)] ++ d'') : Multiset I) = ν)
    (h₂ : (expandDiv (d' ++ [(i, 2), (j, 1)] ++ d'') : Multiset I) = ν)
    (h₃ : (expandDiv (d' ++ [(j, 1), (i, 2)] ++ d'') : Multiset I) = ν) :
    gdim (idem M.grading (divIdemOf _ h₁ : A)) =
      single (-1) 1 * gdim (idem M.grading (divIdemOf _ h₂ : A)) +
        single (-1) 1 * gdim (idem M.grading (divIdemOf _ h₃ : A)) := by
  obtain ⟨f₁, f₂, a₁, b₁, a₂, b₂, H, H₁, H₂, ha₁, hb₁, ha₂, hb₂⟩ :=
    prop213_neg_one_divIdemOf (k := k) d' d'' hadj h₁ h₂ h₃
  exact gdim_idem_of_isOrthDecomp H H₁ H₂ (by simpa using ha₁) hb₁ (by simpa using ha₂) hb₂

/-- Graded dimensions, case `i · j = 0`: `gdim (1_{…ij…} M) = gdim (1_{…ji…} M)`. -/
theorem gdim_divIdemOf_zero (M : GMod ((klGradingDatum k Γ).grade ν)) [HasGdim M.grading]
    (d' d'' : List (I × ℕ)) {i j : I} (hne : i ≠ j) (hadj : ¬ Γ.Adj i j)
    (h₁ : (expandDiv (d' ++ [(i, 1), (j, 1)] ++ d'') : Multiset I) = ν)
    (h₂ : (expandDiv (d' ++ [(j, 1), (i, 1)] ++ d'') : Multiset I) = ν) :
    gdim (idem M.grading (divIdemOf _ h₁ : A)) = gdim (idem M.grading (divIdemOf _ h₂ : A)) := by
  obtain ⟨a, b, H, ha, hb⟩ := prop213_zero_divIdemOf (k := k) d' d'' hne hadj h₁ h₂
  rw [gdim_idem_of_isEquivPair H ha (by simpa using hb), single_zero_one, one_mul]

/-- **KL I, Corollary 2.15, first equality**: `ch(M, …ij…) = ch(M, …ji…)` if `i · j = 0`. -/
theorem cor215_zero (M : GMod ((klGradingDatum k Γ).grade ν)) [HasGdim M.grading]
    (d' d'' : List (I × ℕ)) {i j : I} (hne : i ≠ j) (hadj : ¬ Γ.Adj i j)
    (h₁ : (expandDiv (d' ++ [(i, 1), (j, 1)] ++ d'') : Multiset I) = ν)
    (h₂ : (expandDiv (d' ++ [(j, 1), (i, 1)] ++ d'') : Multiset I) = ν) :
    chDiv Γ M (d' ++ [(i, 1), (j, 1)] ++ d'') h₁ = chDiv Γ M (d' ++ [(j, 1), (i, 1)] ++ d'') h₂ := by
  rw [chDiv, chDiv, gdim_divIdemOf_zero M d' d'' hne hadj h₁ h₂]
  congr 3
  simp [divAngle_append, divAngle]

/-- **KL I, Corollary 2.15, second equality**:
`ch(M, …iji…) = ch(M, …i^{(2)}j…) + ch(M, …ji^{(2)}…)` if `i · j = -1`. -/
theorem cor215_neg_one (M : GMod ((klGradingDatum k Γ).grade ν)) [HasGdim M.grading]
    (d' d'' : List (I × ℕ)) {i j : I} (hadj : Γ.Adj i j)
    (h₁ : (expandDiv (d' ++ [(i, 1), (j, 1), (i, 1)] ++ d'') : Multiset I) = ν)
    (h₂ : (expandDiv (d' ++ [(i, 2), (j, 1)] ++ d'') : Multiset I) = ν)
    (h₃ : (expandDiv (d' ++ [(j, 1), (i, 2)] ++ d'') : Multiset I) = ν) :
    chDiv Γ M (d' ++ [(i, 1), (j, 1), (i, 1)] ++ d'') h₁ =
      chDiv Γ M (d' ++ [(i, 2), (j, 1)] ++ d'') h₂ +
        chDiv Γ M (d' ++ [(j, 1), (i, 2)] ++ d'') h₃ := by
  rw [chDiv, chDiv, chDiv, gdim_divIdemOf_neg_one M d' d'' hadj h₁ h₂ h₃]
  have e₁ : divAngle (d' ++ [(i, 1), (j, 1), (i, 1)] ++ d'') = divAngle d' + divAngle d'' := by
    simp [divAngle_append, divAngle]
  have e₂ : divAngle (d' ++ [(i, 2), (j, 1)] ++ d'') = divAngle d' + divAngle d'' + 1 := by
    simp [divAngle_append, divAngle]; omega
  have e₃ : divAngle (d' ++ [(j, 1), (i, 2)] ++ d'') = divAngle d' + divAngle d'' + 1 := by
    simp [divAngle_append, divAngle]; omega
  rw [e₁, e₂, e₃, mul_add, ← mul_assoc, ← mul_assoc, single_mul_single, one_mul]
  congr 3 <;> push_cast <;> ring_nf

/-- **KL I, Corollary 2.15, third equality**:
`ch(M, …i^{(a)} i^{(b)}…) = [a+b choose a] ch(M, …i^{(a+b)}…)`. -/
theorem cor215_divided (M : GMod ((klGradingDatum k Γ).grade ν)) [HasGdim M.grading]
    (d' d'' : List (I × ℕ)) (c : I) (a b : ℕ)
    (h₁ : (expandDiv (d' ++ (c, a) :: (c, b) :: d'') : Multiset I) = ν)
    (h₂ : (expandDiv (d' ++ (c, a + b) :: d'') : Multiset I) = ν) :
    chDiv Γ M (d' ++ (c, a) :: (c, b) :: d'') h₁ =
      QuantumGroup.qbinom qUnitLS (a + b) a * chDiv Γ M (d' ++ (c, a + b) :: d'') h₂ :=
  chDiv_append_pair M d' d'' c a b h₁ h₂

end Cor

end Categorification.KLR
