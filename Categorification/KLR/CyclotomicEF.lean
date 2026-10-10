/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicMirror

/-!
# `e(β, i) R(β + α_i) e(β, i)`: Kang–Kashiwara Proposition 3.4 and Corollary 3.5

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, §3.

* `wordProd_descRun_symm_val`, `shuffleLast`: the shuffles of `S_n × S_1 ⊆ S_{n+1}` are the
  cycles `wordProd (descRun a (n - a))` (`a ≤ n`), and `descRun a (n - a)` is a reduced word.
-/

namespace Categorification.KLR

open Equiv TypeA

/-! ### Shuffles of `S_n × S_1` -/

section ShuffleLast

theorem wordProd_descRun_symm_val {m b l : ℕ} (h : b + l < m) (y : Fin m) :
    ((wordProd m (descRun b l)).symm y).val =
      if y.val < b then y.val else if y.val < b + l then y.val + 1
      else if y.val = b + l then b else y.val := by
  induction l generalizing b with
  | zero =>
    rw [descRun_zero, wordProd_nil]
    show y.val = _
    split_ifs <;> omega
  | succ l ih =>
    have e1 : (wordProd m (descRun b (l + 1))).symm y =
        sadj m b ((wordProd m (descRun (b + 1) l)).symm y) := by
      rw [descRun_succ, wordProd_append, wordProd_singleton]
      show (sadj m b).symm ((wordProd m (descRun (b + 1) l)).symm y) = _
      rw [KLRAlgebra.sadj_symm]
    have hz := ih (b := b + 1) (by omega)
    rw [e1, KLRAlgebra.sadj_apply_val (by omega), hz]
    split_ifs <;> omega

variable {n m : ℕ} (h : n + 1 = m)

/-- The last position `n` of `Fin m`, `m = n + 1`. -/
def lastFin : Fin m := ⟨n, by omega⟩

/-- The cycle `c_a = s_{n-1} ⋯ s_a`, sending `a` to `n` and `b > a` to `b - 1`. -/
def cycA (a : ℕ) : Perm (Fin m) := wordProd m (descRun a (n - a))

include h in
theorem cycA_symm_val {a : ℕ} (ha : a ≤ n) (y : Fin m) :
    ((cycA (n := n) a).symm y).val =
      if y.val < a then y.val else if y.val < n then y.val + 1 else a := by
  rw [cycA, wordProd_descRun_symm_val (by omega)]
  have := y.2
  split_ifs <;> omega

/-! #### Shuffles for the blocks `n + 1` -/

variable {n' : ℕ} (hb : n + n' = m) (h1 : n' = 1)

/-- The position of the second block. -/
def lastB : Fin m := blockEquiv hb (Sum.inr ⟨0, h1 ▸ Nat.one_pos⟩)

include h1 in
theorem mem_range_inl_iff (w : Perm (Fin m)) (z : Fin m) :
    (∃ x, w⁻¹ (blockEquiv hb (Sum.inl x)) = z) ↔ z ≠ w⁻¹ (lastB hb h1) := by
  constructor
  · rintro ⟨x, rfl⟩ hx
    have := (blockEquiv hb).injective (w⁻¹.injective hx)
    exact Sum.inl_ne_inr this
  · intro hz
    rcases hs : (blockEquiv hb).symm (w z) with x | y
    · refine ⟨x, ?_⟩
      rw [← hs, Equiv.apply_symm_apply]; exact w.symm_apply_apply z
    · exfalso
      apply hz
      have hy : y = ⟨0, by omega⟩ := Fin.ext (by have := y.2; omega)
      rw [lastB, ← hy, ← hs, Equiv.apply_symm_apply]; exact (w.symm_apply_apply z).symm

include h1 in
theorem eq_of_isShuffle_last {u v : Perm (Fin m)} (hu : IsShuffle hb u) (hv : IsShuffle hb v)
    (he : u⁻¹ (lastB hb h1) = v⁻¹ (lastB hb h1)) : u = v := by
  have hf : (fun x => u⁻¹ (blockEquiv hb (Sum.inl x))) = (fun x => v⁻¹ (blockEquiv hb (Sum.inl x))) := by
    rw [← StrictMono.range_inj_of_wellFoundedLT hu.1 hv.1]
    ext z
    simp only [Set.mem_range]
    rw [mem_range_inl_iff hb h1, mem_range_inl_iff hb h1, he]
  have hinv : u⁻¹ = v⁻¹ := by
    ext1 z
    obtain ⟨s, rfl⟩ := (blockEquiv hb).surjective z
    rcases s with x | y
    · exact congrFun hf x
    · have hy : y = ⟨0, by omega⟩ := Fin.ext (by have := y.2; omega)
      rw [hy]; exact he
  exact inv_injective hinv

include h hb in
theorem isShuffle_cycA {a : ℕ} (ha : a ≤ n) : IsShuffle hb (cycA (m := m) (n := n) a) := by
  refine ⟨fun x x' hxx' => ?_, fun y y' hyy' => ?_⟩
  · rw [Fin.lt_def] at hxx' ⊢
    show ((cycA (n := n) a).symm _).val < ((cycA (n := n) a).symm _).val
    rw [cycA_symm_val h ha, cycA_symm_val h ha, blockEquiv_inl_val, blockEquiv_inl_val]
    have := x'.2
    split_ifs <;> omega
  · exfalso; rw [Fin.lt_def] at hyy'; have := y'.2; omega

include h in
theorem cycA_symm_lastB {a : ℕ} (ha : a ≤ n) :
    ((cycA (m := m) (n := n) a)⁻¹ (lastB hb h1)).val = a := by
  show ((cycA (n := n) a).symm _).val = a
  rw [cycA_symm_val h ha, lastB, blockEquiv_inr_val]
  split_ifs <;> omega

include h in
theorem symm_lastB_le (u : Perm (Fin m)) : (u⁻¹ (lastB hb h1)).val ≤ n := by
  have := (u⁻¹ (lastB hb h1)).2; omega

include h in
theorem eq_cycA (u : Shuffle hb) :
    u.1 = cycA (m := m) (n := n) (u.1⁻¹ (lastB hb h1)).val :=
  eq_of_isShuffle_last hb h1 u.2 (isShuffle_cycA h hb (symm_lastB_le h hb h1 u.1))
    (Fin.ext (by rw [cycA_symm_lastB h hb h1 (symm_lastB_le h hb h1 u.1)]))

/-- The shuffles of `S_n × S_1`, indexed by the position `a ≤ n` of the last strand. -/
def shLast : Fin (n + 1) ≃ Shuffle hb where
  toFun a := ⟨cycA (n := n) a.val, isShuffle_cycA h hb (Nat.lt_succ_iff.1 a.2)⟩
  invFun u := ⟨(u.1⁻¹ (lastB hb h1)).val, Nat.lt_succ_of_le (symm_lastB_le h hb h1 u.1)⟩
  left_inv a := Fin.ext (cycA_symm_lastB h hb h1 (Nat.lt_succ_iff.1 a.2))
  right_inv u := Subtype.ext (eq_cycA h hb h1 u).symm

theorem shLast_apply (a : Fin (n + 1)) : (shLast h hb h1 a).1 = cycA (n := n) a.val := rfl

include h in
theorem isReduced_descRun {a : ℕ} (ha : a ≤ n) : IsReduced m (descRun a (n - a)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : a = 0 := by omega
    have := isReduced_canWord m (wordProd m (codeWord []))
    rwa [canWord_wordProd_codeWord isCode_nil (by simp; omega)] at this
  · have hc : IsCode (a :: idCode (n - 1)) := ⟨by simp; omega, isCode_idCode _⟩
    have hl : (a :: idCode (n - 1)).length = m - 1 := by simp; omega
    have hw : codeWord (a :: idCode (n - 1)) = descRun a (n - a) := by
      rw [codeWord_cons, codeWord_idCode, List.nil_append, length_idCode,
        show n - 1 + 1 - a = n - a by omega]
    have := isReduced_canWord m (wordProd m (codeWord (a :: idCode (n - 1))))
    rwa [canWord_wordProd_codeWord hc hl, hw] at this

end ShuffleLast

/-! ### `R(β + i) 1_{β,i}` is a free right `R(β) ⊗ R(i)`-module on `ψ_a ⋯ ψ_{n-1}` -/

section RightFreeLast

open MvPolynomial
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] [IsDomain k]
  {Q : I → I → MvPolynomial (Fin 2) k} {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

namespace KLRAlgebra

variable (i : I) (β : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "T0" => KLRAlgebra k Q β ⊗[k] KLRAlgebra k Q Si

omit [DecidableEq I] in
theorem card_add_single_eq : Multiset.card β + 1 = Multiset.card (β + Si) := by simp

omit [DecidableEq I] in
theorem card_single' : Multiset.card Si = 1 := Multiset.card_singleton i

/-- The explicit reduced word `[n - 1, …, a]` of the shuffle moving the last strand to `a`. -/
noncomputable def lastW (u : Shuffle (Seq.card_add' β Si)) : List ℕ :=
  descRun (u.1⁻¹ (lastB (Seq.card_add' β Si) (card_single' i))).val
    (Multiset.card β - (u.1⁻¹ (lastB (Seq.card_add' β Si) (card_single' i))).val)

omit [DecidableEq I] in
theorem lastW_spec (u : Shuffle (Seq.card_add' β Si)) :
    IsReduced (Multiset.card (β + Si)) (lastW i β u) ∧
      wordProd (Multiset.card (β + Si)) (lastW i β u) = u.1 :=
  ⟨isReduced_descRun (card_add_single_eq i β)
      (symm_lastB_le (card_add_single_eq i β) _ (card_single' i) u.1),
    (eq_cycA (card_add_single_eq i β) _ (card_single' i) u).symm⟩

/-- `ψ_a ψ_{a+1} ⋯ ψ_{n-1}`. -/
noncomputable def upW (a n : ℕ) : List ℕ := List.range' a (n - a)

omit [IsDomain k] in
theorem hflip_hatW_lastW (a : Fin (Multiset.card β + 1)) :
    hflip (hatW (Q := Q) (lastW i β) (shLast (card_add_single_eq i β) _ (card_single' i) a)) =
      ψw (upW a.val (Multiset.card β)) * oneConcat Q β Si := by
  rw [hatW, hflip_mul, hflip_oneConcat_eq, hflip_ψw]
  congr 2
  rw [lastW, upW, descRun, List.reverse_reverse]
  rw [shLast_apply, cycA_symm_lastB (card_add_single_eq i β) _ _ (Nat.lt_succ_iff.1 a.2)]

end KLRAlgebra

end RightFreeLast

end Categorification.KLR
