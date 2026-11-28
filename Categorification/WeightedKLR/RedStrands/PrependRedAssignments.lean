/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PhiDiagrams
import Categorification.WeightedKLR.RedStrands.PrependRed
import Categorification.TypeA.Inversions

/-!
# Block assignments after adding a red strand on the left

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Corollary 5.23. Let `w'` be the word obtained from `w` by adding a red letter `λ₀` in front
(the old red labels shifted by one). A block assignment `g` of `w` extends to one of `w'` by
putting `λ₀` in block `0` and every old letter in block `g(p) + 1` (`extAssign`). The extended
assignments are exactly those whose bottom begins with `λ₀`
(`exists_extAssign_of_head_eq`): any other assignment moves a black letter into the block
left of `λ₀`. The bottom of an extended assignment is `λ₀` followed by the old bottom
(`assignWord_extAssign`), and its inversions are those of the old one, shifted
(`sum_invSet_keyPerm_extAssign`).

The statements are for a word `w'` of any length `M = m + 1`, described by its letters at
positions `0` and `p + 1`.

## Main definitions

* `extAssign`: the extended block assignment.

## Main results

* `extAssign_mem`, `extAssign_injective`, `exists_extAssign_of_head_eq`.
* `assignWord_extAssign`, `sum_invSet_keyPerm_extAssign`, `ofFn_eq_cons_map_prependRedColor`.
-/

namespace Categorification.Stendhal

open TypeA

section CountSort

variable {α : Type*}

private theorem countSort_cons_of_key_eq_one (K : α → ℕ) (N : ℕ) (x : α) (L : List α)
    (hx : K x = 1) (hL : ∀ y ∈ L, 2 ≤ K y) :
    countSort K (N + 2) (x :: L) = x :: countSort K (N + 2) L := by
  have hL0 : L.filter (fun a => K a = 0) = [] :=
    List.filter_eq_nil_iff.2 fun a ha => by have := hL a ha; simp; omega
  have hL1 : L.filter (fun a => K a = 1) = [] :=
    List.filter_eq_nil_iff.2 fun a ha => by have := hL a ha; simp; omega
  unfold countSort
  rw [show N + 2 = 2 + N by omega, List.range_add, List.flatMap_append, List.flatMap_append]
  simp only [show List.range 2 = [0, 1] from rfl, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.filter_cons, hx, hL0, hL1, List.flatMap_map]
  simp only [decide_eq_true_eq, one_ne_zero, ↓reduceIte, List.nil_append, List.cons_append]
  congr 1
  refine List.flatMap_congr fun c _ => ?_
  have : ¬ (1 = 2 + c) := by omega
  simp [this]

private theorem countSort_add_two (K : α → ℕ) (N : ℕ) (L : List α) :
    countSort (fun a => K a + 2) (N + 2) L = countSort K N L := by
  unfold countSort
  rw [show N + 2 = 2 + N by omega, List.range_add, List.flatMap_append, List.flatMap_map]
  have h0 : (List.range 2).flatMap (fun c => L.filter fun a => K a + 2 = c) = [] := by
    simp only [show List.range 2 = [0, 1] from rfl, List.flatMap_cons, List.flatMap_nil]
    simp
  rw [h0, List.nil_append]
  refine List.flatMap_congr fun c _ => ?_
  congr 1
  funext a
  simp only [decide_eq_decide]
  omega

end CountSort

variable {I : Type*} {ℓ m M : ℕ}

/-- Extend a block assignment of `w` to `λ₀ w`: block `0` for `λ₀`, block `g p + 1` for the
old letter `p`. -/
def extAssign (hM : M = m + 1) (g : Fin m → ℕ) : Fin M → ℕ := fun a =>
  if h : a.val = 0 then 0 else g ⟨a.val - 1, by have := a.2; omega⟩ + 1

variable {lbl : Fin m → I ⊕ Fin ℓ} {lbl' : Fin M → I ⊕ Fin (ℓ + 1)}

/-- The letters of `λ₀ w`. -/
theorem ofFn_eq_cons_map_prependRedColor (hM : M = m + 1) (h0 : ∀ a : Fin M, a.val = 0 → lbl' a = .inr 0)
    (hp : ∀ (a : Fin M) (p : Fin m), a.val = p.val + 1 → lbl' a = prependRedColor ℓ (lbl p)) :
    List.ofFn lbl' = .inr 0 :: (List.ofFn lbl).map (prependRedColor ℓ) := by
  subst hM
  rw [List.ofFn_succ, h0 0 rfl, List.map_ofFn]
  congr 1
  exact List.ofFn_inj.2 (funext fun p => hp _ p rfl)

private theorem redsBefore_zero' (a : Fin M) (ha : a.val = 0) : redsBefore lbl' a = 0 := by
  simp [redsBefore, ha]

private theorem redsBefore_succ' (hM : M = m + 1)
    (h0 : ∀ a : Fin M, a.val = 0 → lbl' a = .inr 0)
    (hp : ∀ (a : Fin M) (p : Fin m), a.val = p.val + 1 → lbl' a = prependRedColor ℓ (lbl p))
    (a : Fin M) (p : Fin m) (ha : a.val = p.val + 1) :
    redsBefore lbl' a = redsBefore lbl p + 1 := by
  unfold redsBefore
  rw [ofFn_eq_cons_map_prependRedColor hM h0 hp, ha, List.take_succ_cons, redCount, List.countP_cons, ← List.map_take,
    List.countP_map, redCount]
  have : ((fun y : I ⊕ Fin (ℓ + 1) => y.isRight) ∘ prependRedColor ℓ) = fun y => y.isRight :=
    funext fun y => prependRedColor_isRight y
  rw [this]
  simp

/-- The extended assignment is a block assignment of `λ₀ w`. -/
theorem extAssign_mem (hM : M = m + 1) (h0 : ∀ a : Fin M, a.val = 0 → lbl' a = .inr 0)
    (hp : ∀ (a : Fin M) (p : Fin m), a.val = p.val + 1 → lbl' a = prependRedColor ℓ (lbl p))
    {g : Fin m → ℕ} (hg : g ∈ assignments lbl) :
    extAssign hM g ∈ assignments lbl' := by
  refine mem_assignList.2 fun a => ?_
  unfold assignChoices
  by_cases ha : a.val = 0
  · have hz : extAssign hM g a = 0 := by simp [extAssign, ha]
    rw [hz, h0 a ha, redsBefore_zero' a ha]
    simp
  · set p : Fin m := ⟨a.val - 1, by have := a.2; omega⟩
    have hpa : a.val = p.val + 1 := by simp [p]; omega
    have hz : extAssign hM g a = g p + 1 := by simp [extAssign, ha, p]
    have hgp := mem_assignList.1 hg p
    unfold assignChoices at hgp
    rw [hz, hp a p hpa, prependRedColor_isRight, redsBefore_succ' hM h0 hp a p hpa]
    split_ifs at hgp ⊢ with hr
    · rw [List.mem_singleton.1 hgp]; simp
    · simp only [List.mem_range] at hgp ⊢
      omega

/-- Extension is injective. -/
theorem extAssign_injective (hM : M = m + 1) : Function.Injective (extAssign (m := m) hM) := by
  intro g g' h
  funext p
  have := congrFun h ⟨p.val + 1, by omega⟩
  simpa [extAssign] using this

private theorem assignKey_extAssign_zero (hM : M = m + 1)
    (h0 : ∀ a : Fin M, a.val = 0 → lbl' a = .inr 0) (g : Fin m → ℕ) (a : Fin M)
    (ha : a.val = 0) : assignKey lbl' (extAssign hM g) a = 1 := by
  simp [assignKey, extAssign, ha, h0 a ha]

private theorem assignKey_extAssign_succ (hM : M = m + 1)
    (hp : ∀ (a : Fin M) (p : Fin m), a.val = p.val + 1 → lbl' a = prependRedColor ℓ (lbl p))
    (g : Fin m → ℕ) (a : Fin M) (p : Fin m) (ha : a.val = p.val + 1) :
    assignKey lbl' (extAssign hM g) a = assignKey lbl g p + 2 := by
  have hne : a.val ≠ 0 := by omega
  have hp' : (⟨a.val - 1, by have := a.2; omega⟩ : Fin m) = p := Fin.ext (by simp; omega)
  simp only [assignKey, extAssign, hne, ↓reduceDIte, hp', hp a p ha, prependRedColor_isRight]
  ring

/-- **The bottom of an extended assignment** is `λ₀` followed by the old bottom. -/
theorem assignWord_extAssign (hM : M = m + 1) (h0 : ∀ a : Fin M, a.val = 0 → lbl' a = .inr 0)
    (hp : ∀ (a : Fin M) (p : Fin m), a.val = p.val + 1 → lbl' a = prependRedColor ℓ (lbl p))
    (g : Fin m → ℕ) :
    assignWord lbl' (extAssign hM g) = .inr 0 :: (assignWord lbl g).map (prependRedColor ℓ) := by
  subst hM
  unfold assignWord
  rw [List.finRange_succ, show 2 * (m + 1) + 2 = (2 * m + 2) + 2 by ring,
    countSort_cons_of_key_eq_one _ _ _ _ (assignKey_extAssign_zero rfl h0 g 0 rfl)]
  · rw [List.map_cons, h0 0 rfl, countSort_map]
    have hk : (assignKey lbl' (extAssign rfl g) ∘ Fin.succ) = fun p => assignKey lbl g p + 2 :=
      funext fun p => assignKey_extAssign_succ rfl hp g p.succ p rfl
    rw [hk, countSort_add_two, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun p _ => ?_
    simp [Function.comp, hp p.succ p rfl]
  · intro y hy
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 hy
    rw [assignKey_extAssign_succ rfl hp g p.succ p rfl]
    omega

/-- **The inversions of an extended assignment** are those of the old one, shifted by one: a
sum over the inversion set of `φ_{ιg}` of a function of the two letters equals the sum over
the inversion set of `φ_g` with the letters recoloured. -/
theorem sum_invSet_keyPerm_extAssign {A : Type*} [AddCommMonoid A] (hM : M = m + 1)
    (h0 : ∀ a : Fin M, a.val = 0 → lbl' a = .inr 0)
    (hp : ∀ (a : Fin M) (p : Fin m), a.val = p.val + 1 → lbl' a = prependRedColor ℓ (lbl p))
    (g : Fin m → ℕ) (f : I ⊕ Fin (ℓ + 1) → I ⊕ Fin (ℓ + 1) → A) :
    ∑ x ∈ TypeA.invSet M (keyPerm (assignKey lbl' (extAssign hM g))), f (lbl' x.1) (lbl' x.2) =
      ∑ x ∈ TypeA.invSet m (keyPerm (assignKey lbl g)),
        f (prependRedColor ℓ (lbl x.1)) (prependRedColor ℓ (lbl x.2)) := by
  subst hM
  have k0 := assignKey_extAssign_zero rfl h0 g 0 rfl
  have ks : ∀ p : Fin m, assignKey lbl' (extAssign rfl g) p.succ = assignKey lbl g p + 2 :=
    fun p => assignKey_extAssign_succ rfl hp g p.succ p rfl
  let e : Fin m × Fin m ↪ Fin (m + 1) × Fin (m + 1) := (Fin.succEmb m).prodMap (Fin.succEmb m)
  have hset : TypeA.invSet (m + 1) (keyPerm (assignKey lbl' (extAssign rfl g))) =
      (TypeA.invSet m (keyPerm (assignKey lbl g))).map e := by
    ext ⟨a, b⟩
    simp only [Finset.mem_map, TypeA.mem_invSet, keyPerm_lt_iff, Prod.exists, e,
      Function.Embedding.coe_prodMap, Fin.coe_succEmb, Prod.map_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨hab, hba⟩
      cases a using Fin.cases with
      | zero =>
        cases b using Fin.cases with
        | zero => exact absurd hab (lt_irrefl _)
        | succ q => rw [ks, k0] at hba; omega
      | succ p =>
        cases b using Fin.cases with
        | zero => exact absurd hab (Fin.not_lt_zero _)
        | succ q =>
          rw [ks, ks] at hba
          refine ⟨p, q, ⟨Fin.succ_lt_succ_iff.1 hab, ?_⟩, rfl, rfl⟩
          rcases hba with h | ⟨h, h'⟩
          · exact Or.inl (by omega)
          · exact Or.inr ⟨by omega, Fin.succ_lt_succ_iff.1 h'⟩
    · rintro ⟨p, q, ⟨hpq, hqp⟩, rfl, rfl⟩
      refine ⟨Fin.succ_lt_succ_iff.2 hpq, ?_⟩
      rw [ks, ks]
      rcases hqp with h | ⟨h, h'⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, Fin.succ_lt_succ_iff.2 h'⟩
  rw [hset, Finset.sum_map]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [e, Function.Embedding.coe_prodMap, Fin.coe_succEmb, Prod.map_fst, Prod.map_snd]
  rw [hp x.1.succ x.1 rfl, hp x.2.succ x.2 rfl]

/-- **The assignments extended from `w`** are exactly those whose bottom begins with `λ₀`. -/
theorem exists_extAssign_of_head_eq (hM : M = m + 1)
    (h0 : ∀ a : Fin M, a.val = 0 → lbl' a = .inr 0)
    (hp : ∀ (a : Fin M) (p : Fin m), a.val = p.val + 1 → lbl' a = prependRedColor ℓ (lbl p))
    {g' : Fin M → ℕ} (hg' : g' ∈ assignments lbl')
    (hhead : (assignWord lbl' g').head? = .some (.inr 0)) :
    ∃ g ∈ assignments lbl, extAssign hM g = g' := by
  subst hM
  have hmem := mem_assignList.1 hg'
  have hg0 : g' 0 = 0 := by
    have := hmem 0
    unfold assignChoices at this
    rw [h0 0 rfl, redsBefore_zero' 0 rfl] at this
    simpa using this
  -- the letters of `w'` equal to `λ₀` sit at position `0`
  have hpos : ∀ a : Fin (m + 1), lbl' a = .inr 0 → a = 0 := by
    intro a ha
    cases a using Fin.cases with
    | zero => rfl
    | succ p =>
      rw [hp p.succ p rfl] at ha
      obtain ⟨q, _, hq⟩ := prependRedColor_eq_inr ha
      exact absurd hq (Fin.succ_ne_zero q)
  have hpos1 : ∀ p : Fin m, 1 ≤ g' p.succ := by
    intro p
    by_contra hlt
    have hz : g' p.succ = 0 := by omega
    set K := assignKey lbl' g'
    have hK : K p.succ = 0 := by
      have := hmem p.succ
      unfold assignChoices at this
      rw [hp p.succ p rfl, prependRedColor_isRight, redsBefore_succ' rfl h0 hp p.succ p rfl] at this
      split_ifs at this with hr
      · rw [List.mem_singleton] at this; omega
      · simp only [K, assignKey, hz, hp p.succ p rfl, prependRedColor_isRight, hr]
        simp
    have hF : p.succ ∈ (List.finRange (m + 1)).filter fun a => K a = 0 := by
      simp [hK]
    obtain ⟨x, F', hxF⟩ : ∃ x F', (List.finRange (m + 1)).filter (fun a => K a = 0) = x :: F' := by
      rcases h : (List.finRange (m + 1)).filter (fun a => K a = 0) with _ | ⟨x, F'⟩
      · rw [h] at hF; simp at hF
      · exact ⟨x, F', rfl⟩
    have hx : K x = 0 := by
      have : x ∈ (List.finRange (m + 1)).filter fun a => K a = 0 := by rw [hxF]; simp
      simpa using this
    have hcs : (countSort K (2 * (m + 1) + 2) (List.finRange (m + 1))).head? = some x := by
      unfold countSort
      rw [show 2 * (m + 1) + 2 = (2 * (m + 1) + 1) + 1 by ring, List.range_succ_eq_map,
        List.flatMap_cons, hxF]
      simp
    have hlx : lbl' x = .inr 0 := by
      unfold assignWord at hhead
      rw [List.head?_map, hcs] at hhead
      simpa using hhead
    have hx0 := hpos x hlx
    rw [hx0] at hx
    have : K 0 = 1 := by simp [K, assignKey, hg0, h0 0 rfl]
    omega
  refine ⟨fun p => g' p.succ - 1, mem_assignList.2 fun p => ?_, ?_⟩
  · have := hmem p.succ
    have h1 := hpos1 p
    unfold assignChoices at this ⊢
    rw [hp p.succ p rfl, prependRedColor_isRight, redsBefore_succ' rfl h0 hp p.succ p rfl] at this
    split_ifs at this ⊢
    · rw [List.mem_singleton] at this ⊢; omega
    · simp only [List.mem_range] at this ⊢; omega
  · funext a
    cases a using Fin.cases with
    | zero => simp [extAssign, hg0]
    | succ p =>
      have := hpos1 p
      simp only [extAssign, Fin.val_succ, Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel,
        Fin.eta]
      omega

end Categorification.Stendhal
