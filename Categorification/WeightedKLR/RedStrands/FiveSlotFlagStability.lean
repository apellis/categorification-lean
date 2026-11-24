/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotFlagPositions
import Categorification.WeightedKLR.RedStrands.TwoBlackFlagIdeal

/-!
# Stability of the five-slot polynomial flags

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 after (6.21).
The two flag relations are preserved by the generators of the asymmetric
polynomial action and give a polynomial flag test in the violated quotient.
-/

namespace Categorification.Stendhal.FiveSlotFlag

open KLR KLRAlgebra KLR.PolyRep MvPolynomial TypeA TwoBlackFlag

variable {k : Type*} [CommRing k] (Λ : Fin 3 → Unit →₀ ℕ)

local notation "m" => Multiset.card weight
local notation "R" => MvPolynomial (Fin m) k
local notation "a[" s "]" => firstBlack s
local notation "b[" s "]" => secondBlack s
local notation "B[" s "," a "]" => flagBound Λ s a

/-- The two-black flag ideal at a fixed positional loading. -/
noncomputable def loadingIdeal (s : Seq weight) : Ideal R :=
  ideal a[s] b[s] B[s,a[s]] B[s,b[s]]

private theorem bounds_le (s : Seq weight) : B[s,a[s]] ≤ B[s,b[s]] := by
  exact Finset.sum_le_sum_of_subset (blackPositions s).2.2.2

private theorem bound_add {s t : Seq weight} {a b : Fin m} {r : Fin 3}
    (hn : r ∉ redsBefore s a) (h : redsBefore t b = insert r (redsBefore s a)) :
    B[t,b] = B[s,a] + Λ r () := by
  rw [flagBound, h, Finset.sum_insert hn, add_comm]
  rfl

theorem loadingIdeal_eq_top_of_violated (s : Seq weight) (hv : IsViolated s) :
    loadingIdeal (k := k) Λ s = ⊤ := by
  rw [loadingIdeal, firstBound_eq_zero_of_violated Λ s hv, ideal, pow_zero]
  rw [Ideal.eq_top_iff_one]
  exact Ideal.subset_span (Set.mem_insert _ _)

private theorem transport_black_red (s : Seq weight) (j : ℕ) (h : j + 1 < m) (r : Fin 3)
    (hl : s.lbl ⟨j, by omega⟩ = .inl ()) (hr : s.lbl ⟨j + 1, h⟩ = .inr r)
    (p : R) (hp : p ∈ loadingIdeal Λ s) :
    X (⟨j + 1, h⟩ : Fin m) ^ Λ r () * rename (sadj m j) p ∈ loadingIdeal Λ (sadj m j • s) := by
  let t := sadj m j • s
  obtain ⟨ha, hb, hs⟩ := slots_black_red s j h r hl hr
  have hm := rename_mem (sadj m j) hp
  rw [← ha, ← hb] at hm
  rw [mul_comm]
  change _ ∈ ideal a[t] b[t] B[t,a[t]] B[t,b[t]]
  by_cases hfirst : a[s] = ⟨j, by omega⟩
  · rw [ite_eq_left hfirst] at hs
    obtain ⟨hn, h₁, h₂⟩ := hs
    rw [bound_add Λ hn h₁, show B[t,b[t]] = B[s,b[s]] from
      congrArg (fun X : Finset (Fin 3) => ∑ u ∈ X, Λ u ()) h₂,
      ← show a[t] = ⟨j + 1, h⟩ by rw [ha, hfirst, sadj_apply_left h]]
    exact push_first (Λ r ()) hm
  · rw [ite_eq_right hfirst] at hs
    obtain ⟨hsecond, hn, h₂, h₁⟩ := hs
    rw [bound_add Λ hn h₂, show B[t,a[t]] = B[s,a[s]] from
      congrArg (fun X : Finset (Fin 3) => ∑ u ∈ X, Λ u ()) h₁,
      ← show b[t] = ⟨j + 1, h⟩ by rw [hb, hsecond, sadj_apply_left h]]
    exact (mul_second_pow_mem_iff (blackPositions t).2.2.1.ne (bounds_le Λ s) (Λ r ()) _).2 hm

private theorem transport_red_black (s : Seq weight) (j : ℕ) (h : j + 1 < m) (r : Fin 3)
    (hl : s.lbl ⟨j, by omega⟩ = .inr r) (hr : s.lbl ⟨j + 1, h⟩ = .inl ())
    (p : R) (hp : p ∈ loadingIdeal Λ s) :
    rename (sadj m j) p ∈ loadingIdeal Λ (sadj m j • s) := by
  let t := sadj m j • s
  have ht : sadj m j • t = s := sadj_smul_sadj_smul s j
  have htl : t.lbl ⟨j, by omega⟩ = .inl () := by
    dsimp only [t]
    simp only [KLR.Seq.lbl, KLR.Seq.smul_apply, KLR.PolyRep.sadj_eq h, Equiv.symm_swap, Equiv.swap_apply_left]
    exact hr
  have htr : t.lbl ⟨j + 1, h⟩ = .inr r := by
    dsimp only [t]
    simp only [KLR.Seq.lbl, KLR.Seq.smul_apply, KLR.PolyRep.sadj_eq h, Equiv.symm_swap, Equiv.swap_apply_right]
    exact hl
  obtain ⟨ha, hb, hs⟩ := slots_black_red t j h r htl htr
  rw [ht] at ha hb hs
  have h₁ : sadj m j a[s] = a[t] := by rw [ha, TypeA.sadj_sadj_apply]
  have h₂ : sadj m j b[s] = b[t] := by rw [hb, TypeA.sadj_sadj_apply]
  have hm := rename_mem (sadj m j) hp
  rw [h₁, h₂] at hm
  change _ ∈ ideal a[t] b[t] B[t,a[t]] B[t,b[t]]
  by_cases hfirst : a[t] = ⟨j, by omega⟩
  · rw [ite_eq_left hfirst] at hs
    obtain ⟨hn, he₁, he₂⟩ := hs
    rw [bound_add Λ hn he₁, show B[s,b[s]] = B[t,b[t]] from
      congrArg (fun X : Finset (Fin 3) => ∑ u ∈ X, Λ u ()) he₂] at hm
    exact restrict_first hm
  · rw [ite_eq_right hfirst] at hs
    obtain ⟨_, hn, he₂, he₁⟩ := hs
    rw [bound_add Λ hn he₂, show B[s,a[s]] = B[t,a[t]] from
      congrArg (fun X : Finset (Fin 3) => ∑ u ∈ X, Λ u ()) he₁] at hm
    exact restrict_second (bounds_le Λ t) hm

theorem loadingIdeal_preservesFlags : PreservesFlags Λ (loadingIdeal (k := k) Λ) := by
  intro s j h p hp
  rcases hleft : s.lbl ⟨j, by omega⟩ with i | r <;>
    rcases hright : s.lbl ⟨j + 1, h⟩ with i' | d
  · cases i; cases i'
    obtain ⟨ha, hb, hs⟩ := slots_black_black s j h hleft hright
    have ht : sadj m j • s = s := by
      rw [KLR.PolyRep.sadj_eq h]
      exact swap_smul_eq_self (hleft.trans hright.symm)
    rw [ht, crossComp, hleft, hright, ite_eq_left rfl]
    have he : B[s,a[s]] = B[s,b[s]] := congrArg (fun X : Finset (Fin 3) => ∑ u ∈ X, Λ u ()) hs
    unfold loadingIdeal at hp ⊢
    rw [← ha, ← hb, ← he]
    rw [← he] at hp
    exact ddiff_mem_ideal (blackPositions s).2.2.1.ne hp
  · cases i
    simp only [crossComp, hleft, hright, reduceCtorEq, ↓reduceIte, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, flagP, map_pow,
      rename_X, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact transport_black_red Λ s j h d hleft hright p hp
  · cases i'
    simp only [crossComp, hleft, hright, reduceCtorEq, ↓reduceIte, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, flagP, map_one, one_mul]
    exact transport_red_black Λ s j h r hleft hright p hp
  · have hn : r ≠ d := by
      intro he
      subst d
      have hh := eq_of_lbl_eq_inr hleft hright
      exact (by omega : j ≠ j+1) (congrArg Fin.val hh)
    have hl : (s.lbl ⟨j, by omega⟩).isRight := by rw [hleft]; rfl
    have hr : (s.lbl ⟨j+1,h⟩).isRight := by rw [hright]; rfl
    obtain ⟨ha, hb, h₁, h₂⟩ := slots_red_red s j h hl hr
    have hm := rename_mem (sadj m j) hp
    rw [← ha, ← hb] at hm
    rw [crossComp, hleft, hright, ite_eq_right (fun he => hn (Sum.inr.inj he))]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply, flagP]
    split_ifs
    · rw [map_one, one_mul, loadingIdeal, flagBound, flagBound, h₁, h₂]
      exact hm
    · rw [map_zero, zero_mul]
      exact zero_mem _

end Categorification.Stendhal.FiveSlotFlag
