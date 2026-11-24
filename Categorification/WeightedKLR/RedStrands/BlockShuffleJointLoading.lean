/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockShufflePermutation

/-!
# Ascents at supported black–red joints

For Webster (arXiv:1309.3796v2), §6.1, Lemma 6.8, the right crossing at a
black–red bottom joint is an ascent on every matching shuffle with a
nonviolated block split in the same red order.
-/

namespace Categorification.Stendhal.RedBlock

open KLR TypeA Equiv
open Categorification.Stendhal.BraidedStendhalAlgebra

variable {I : Type} {ℓ : ℕ}

/-- The inverse row shuffle is increasing on each input block. -/
theorem shufflePerm_inv_preservesBlockOrder : ∀ (row : List (RedBlock I ℓ))
    (u : ShuffleIndex row), PreservesBlockOrder row (fun x => (shufflePerm row u)⁻¹ x)
  | [], _ => trivial
  | B :: row, u => by
    let h := Seq.card_add' B.weight (weightSum row)
    let p := (shufflePerm row u.2)⁻¹
    let E := blockPerm h 1 p
    have he : (shufflePerm (B :: row) u)⁻¹ = u.1.1⁻¹ * E := by
      rw [shufflePerm_cons, mul_inv_rev, blockPerm_inv, inv_one]
    rw [he]
    constructor
    · change StrictMono (fun x => u.1.1⁻¹ (E (Seq.posL (weightSum row) x)))
      simpa only [E, Seq.posL, blockPerm_inl, Perm.one_apply] using u.1.2.1
    · have e : (fun x => (u.1.1⁻¹ * E) (Seq.posR B.weight x)) =
          (fun x => u.1.1⁻¹ (Seq.posR B.weight x)) ∘ p := by
        funext x
        simp only [Perm.mul_apply,Function.comp_apply,E,Seq.posR,blockPerm_inr]
      change PreservesBlockOrder row (fun x => (u.1.1⁻¹ * E) (Seq.posR B.weight x))
      rw [e]
      exact PreservesBlockOrder.comp_right _ u.1.2.2 row _ (shufflePerm_inv_preservesBlockOrder row u.2)

/-- A supported black-red joint in the preserved red order is an ascent of
the actual row shuffle whenever the split into blocks is nonviolated. -/
theorem shufflePerm_lt_at_black_red (row : List (RedBlock I ℓ)) (u : ShuffleIndex row)
    (s : Seq (weightSum row)) (v : Loadings row)
    (hm : shufflePerm row u • s = place row v) (hn : ¬ Violated row v)
    {ν : Multiset I} (h : weightSum row = stendhalWeight ℓ ν)
    (ho : redWord (Seq.cast h s) = redWord (Seq.cast h (place row v)))
    {x y : Fin (weightSum row).card} {i : I} {r : Fin ℓ}
    (hx : s.lbl x = .inl i) (hy : s.lbl y = .inr r) (hxy : x < y) :
    shufflePerm row u x < shufflePerm row u y := by
  let p := shufflePerm row u
  have hs : p⁻¹ • place row v = s := by rw [← hm, inv_smul_smul]
  have hord := red_order_cast h p⁻¹ (place row v) (by rwa [hs])
  have hlx : (place row v).lbl (p x) = .inl i := by
    rw [← hm]
    change s.lbl (p.symm (p x)) = _
    rwa [p.symm_apply_apply]
  have hly : (place row v).lbl (p y) = .inr r := by
    rw [← hm]
    change s.lbl (p.symm (p y)) = _
    rwa [p.symm_apply_apply]
  by_contra hLt
  have hp : p y < p x := lt_of_le_of_ne (not_lt.mp hLt) (fun e => (ne_of_gt hxy) (p.injective e))
  have hbad := red_before_black row v (fun x => p⁻¹ x) (shufflePerm_inv_preservesBlockOrder row u)
    hn hord _ _ _ _ hly hlx hp
  have : y < x := by simpa using hbad
  exact (not_lt_of_ge hxy.le) this

variable {k : Type*} [CommRing k] [DecidableEq I]
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}

local notation "row" => adjacentRow L M f β

/-- A nonzero projected bottom idempotent forces an ascent at a black–red joint
of the source order. The supporting local loading is nonviolated. -/
theorem shufflePerm_lt_of_nonzero_indexedProjector
    (h : weightSum row = stendhalWeight ℓ ν) (u : ShuffleIndex row)
    (s : Seq (weightSum row)) (z : diagrams Q Λ row)
    (hp : IndexedLoadingProjector Q Λ row u s z)
    (hnz : projection Q Λ row z ≠ 0)
    (ho : redWord (Seq.cast h s) = L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst)
    {a b : Fin (weightSum row).card} {i : I} {r : Fin ℓ}
    (ha : s.lbl a = .inl i) (hb : s.lbl b = .inr r) (hab : a < b) :
    shufflePerm row u a < shufflePerm row u b := by
  rcases hp.support with hz | ⟨v, hmatch, htop, hz⟩
  · exact (hnz (by rw [hz, map_zero])).elim
  have hn : ¬ Violated row v := fun hv =>
    hnz (hz.symm ▸ projection_loadingIdem_eq_zero Q Λ row v hv)
  exact shufflePerm_lt_at_black_red row u s v htop hn h
    (redWord_place_eq_of_shuffleLoading L M f β h s v hmatch ho) ha hb hab

end Categorification.Stendhal.RedBlock
