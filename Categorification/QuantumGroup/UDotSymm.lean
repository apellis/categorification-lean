/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotForm

/-!
# Symmetry of the bilinear form on `'U 1_λ`

Khovanov–Lauda III, arXiv:0807.3250v1, Proposition 2.2 (v) and (iii), (iv), for the form
`UDot.B` on the free version `'U 1_λ` of `U̇ 1_λ`.

The key step is the identity `(1_λ, E_w 1_λ) = (E_w 1_λ, 1_λ)` (`UDot.φ_eq_B_one`). Both
sides respect the commutation relation (KL III eq. (2.4)), so by *normal ordering*
(`UDot.normal_induction`: induction on the length and the number of inversions `+ … -` of a
signed sequence, as at the end of the proof of KL III Theorem 2.7) it suffices to treat
sequences `(-c)(+b)` with all negative entries first; there both sides are explicit multiples
of the form on `'f` (compare KL III Lemmas 2.8–2.10), and they agree by symmetry of that form.

## Main results

* `UDot.normal_induction` — the normal-ordering induction principle;
* `UDot.φ_eq_B_one` — `(1_λ, E_w 1_λ) = (E_w 1_λ, 1_λ)`;
* `UDot.B_rhoE_right` — property (iii) in the second argument;
* `UDot.B_symm` — **property (v)**: `B` is symmetric;
* `UDot.B_posF_posF` — **property (iv)**: `(x⁺ 1_λ, x'⁺ 1_λ) = (x, x')` for `x, x' ∈ 'f`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical
open PreF

namespace UDot

variable {I : Type*} {K : Type*} [Field K] {C : CartanDatum I} {q : Kˣ} {c : I → K}

/-! ### Normal ordering -/

/-- The number of inversions of a signed sequence: pairs `(+i … -j)` with the positive entry
to the left of the negative one. -/
def inv : List (Bool × I) → ℕ
  | [] => 0
  | (b, _) :: w => (if b then Multiset.card (negMS w) else 0) + inv w

theorem inv_append_swap (a b : List (Bool × I)) (i j : I) :
    inv (a ++ (true, i) :: (false, j) :: b) = inv (a ++ (false, j) :: (true, i) :: b) + 1 := by
  induction a with
  | nil => simp [inv]; ring
  | cons l a ih =>
    obtain ⟨x, k⟩ := l
    simp only [List.cons_append, inv, ih, negMS_append, negMS_cons_true, negMS_cons_false]
    ring

theorem inv_append_le (a b : List (Bool × I)) (i j : I) :
    inv (a ++ b) ≤ inv (a ++ (true, i) :: (false, j) :: b) := by
  induction a with
  | nil => simp [inv]
  | cons l a ih =>
    obtain ⟨x, k⟩ := l
    simp only [List.cons_append, inv, negMS_append, negMS_cons_true, negMS_cons_false]
    cases x
    · simpa using ih
    · simp only [if_true, Multiset.card_add, Multiset.card_cons]
      omega

theorem normal_or_inversion (w : List (Bool × I)) :
    (∃ c b, w = negW c ++ posW b) ∨ ∃ a i j b, w = a ++ (true, i) :: (false, j) :: b := by
  induction w with
  | nil => exact Or.inl ⟨[], [], rfl⟩
  | cons l w ih =>
    obtain ⟨x, k⟩ := l
    rcases ih with ⟨c, b, rfl⟩ | ⟨a, i, j, b, rfl⟩
    · cases x
      · exact Or.inl ⟨k :: c, b, rfl⟩
      · cases c with
        | nil => exact Or.inl ⟨[], k :: b, rfl⟩
        | cons c0 c' => exact Or.inr ⟨[], k, c0, negW c' ++ posW b, rfl⟩
    · exact Or.inr ⟨(x, k) :: a, i, j, b, rfl⟩

/-- **Normal-ordering induction.** A property of signed sequences holds for all sequences if it
holds for the normal-ordered ones `(-c)(+b)` and it passes from `a (-j)(+i) b` and `a b` to
`a (+i)(-j) b`. -/
theorem normal_induction {P : List (Bool × I) → Prop} (hN : ∀ c b, P (negW c ++ posW b))
    (hS : ∀ a i j b, P (a ++ (false, j) :: (true, i) :: b) → P (a ++ b) →
      P (a ++ (true, i) :: (false, j) :: b))
    (w : List (Bool × I)) : P w := by
  obtain ⟨n, hn⟩ : ∃ n, w.length = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing w with
  | _ n ihn =>
  obtain ⟨k, hk⟩ : ∃ k, inv w = k := ⟨_, rfl⟩
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ihk =>
  rcases normal_or_inversion w with ⟨c, b, rfl⟩ | ⟨a, i, j, b, rfl⟩
  · exact hN c b
  · refine hS a i j b ?_ ?_
    · exact ihk _ (by rw [← hk, inv_append_swap]; omega) _ (by simp at hn ⊢; omega) rfl
    · exact ihn _ (by simp at hn ⊢; omega) _ rfl

/-! ### Exponent identities -/

variable (C) in
theorem rcx_append (m : I → ℤ) (s s' : List (Bool × I)) :
    rcx C m (s ++ s') = rcx C m s + rcx C (fun k => m k - aS C k s) s' := by
  induction s generalizing m with
  | nil => simp [rcx]
  | cons l s ih =>
    obtain ⟨b, i⟩ := l
    simp only [List.cons_append, rcx, ih, add_assoc]
    congr 3
    funext k; simp; ring

theorem aS_negW (k : I) (c' : List I) : aS C k (negW c') = -msA C k c' := by
  rw [aS_eq]; simp

theorem aS_posW (k : I) (c' : List I) : aS C k (posW c') = msA C k c' := by
  rw [aS_eq]; simp

variable (C) in
theorem rcx_negW (m : I → ℤ) (c' : List I) :
    2 * rcx C m (negW c') = 2 * S1 C m c' + wdot C.dot c' c' := by
  induction c' generalizing m with
  | nil => simp [rcx]
  | cons j c' ih =>
    have hm : (fun k => m k - sgn false * A C k j) = fun k => m k + msA C k {j} := by
      funext k; simp [msA_singleton]
    simp only [negW_cons, rcx, hm]
    rw [mul_add, ih, S1_add_msA, ← Multiset.cons_coe, S1_cons, wdot_cons_left, wdot_cons_right,
      wdot_cons_right, wdot_singleton, ← wdot_singleton_comm C.dot C.symm j c', ← two_mul_di]
    simp only [sgn_false]
    ring

variable (C) in
theorem rcx_posW (m : I → ℤ) (c' : List I) :
    2 * rcx C m (posW c') = wdot C.dot c' c' - 2 * S1 C m c' := by
  induction c' generalizing m with
  | nil => simp [rcx]
  | cons j c' ih =>
    have hm : (fun k => m k - sgn true * A C k j) = fun k => m k - msA C k {j} := by
      funext k; simp [msA_singleton]
    simp only [posW_cons, rcx, hm]
    rw [mul_add, ih, S1_sub_msA, ← Multiset.cons_coe, S1_cons, wdot_cons_left, wdot_cons_right,
      wdot_cons_right, wdot_singleton, ← wdot_singleton_comm C.dot C.symm j c', ← two_mul_di]
    simp only [sgn_true]
    ring

/-! ### `(1_λ, E_w 1_λ) = (E_w 1_λ, 1_λ)` -/

theorem word_ofList_reverse_wt (c' : List I) :
    wt (FreeMonoid.ofList c'.reverse) = (c' : Multiset I) := by
  simp [wt]

/-- The key identity `(1_λ, E_w 1_λ) = (E_w 1_λ, 1_λ)`, by normal ordering. -/
theorem φ_eq_B_one (ℓ : I → ℤ) (w : List (Bool × I)) :
    φ C q c ℓ (ew w) = B C q c ℓ (ew w) 1 := by
  induction w using normal_induction with
  | hN c' b =>
    rw [← ew_nil, B_ew_ew, List.append_nil, ρW_append, ρW_posW, ρW_negW, φ_negW_posW,
      φ_negW_posW, List.reverse_reverse, wl_nil]
    by_cases hbc : (b : Multiset I) = c'
    · rw [fF_symm (word (FreeMonoid.ofList c'.reverse))]
      have e : Kx C ℓ c' = rcx C ℓ (negW c' ++ posW b) + Kx C ℓ b.reverse := by
        have hfun : (fun k => ℓ k - aS C k (negW c')) = fun k => ℓ k + msA C k c' := by
          funext k; rw [aS_negW, sub_neg_eq_add]
        have h1 := rcx_negW C ℓ c'
        have h2 := rcx_posW C (fun k => ℓ k + msA C k c') b
        have h3 := two_mul_hsq C (c' : Multiset I)
        have h4 := two_mul_hsq C (b.reverse : Multiset I)
        rw [S1_add_msA] at h2
        rw [rcx_append, hfun, Kx, Kx]
        rw [Multiset.coe_reverse, hbc] at h4 ⊢
        rw [hbc] at h2
        omega
      rw [e, qp_add]; ring
    · have h1 : fF C q c (word (FreeMonoid.ofList b)) (word (FreeMonoid.ofList c'.reverse)) = 0 := by
        rw [fF, form_eq_zero_of_wt_ne]
        rw [word_ofList_reverse_wt]; simpa [wt] using hbc
      have h2 : fF C q c (word (FreeMonoid.ofList c'.reverse)) (word (FreeMonoid.ofList b)) = 0 := by
        rw [fF_symm, h1]
      rw [h1, h2]; simp
  | hS a i j b h1 h2 =>
    rw [φ_comm, B_comm_left, h1, h2]

theorem B_one_left_eq (ℓ : I → ℤ) (y : Free K I) : B C q c ℓ 1 y = B C q c ℓ y 1 := by
  rw [B_one_left]
  induction y using Free.induction with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy]
  | smul_ew w r => rw [map_smul, map_smul, LinearMap.smul_apply, φ_eq_B_one]

/-! ### Property (iii) in the second argument, and symmetry -/

/-- `(x, E_{εi} y) = (ρ̄(E_{εi}) x, y)`. -/
theorem B_rhoE_right (ℓ : I → ℤ) (x : Free K I) (l : Bool × I) (t : List (Bool × I)) :
    B C q c ℓ x (ew (l :: t)) = B C q c ℓ (rhoE C q ℓ l x) (ew t) := by
  induction x using Free.induction with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | smul_ew s r =>
    rw [map_smul, LinearMap.smul_apply, map_smul, map_smul, LinearMap.smul_apply]
    congr 1
    obtain ⟨b, i⟩ := l
    rw [rhoE_ew, map_smul, LinearMap.smul_apply, B_ew_ew, B_ew_ew, smul_eq_mul, rcx, ρW_cons,
      List.append_assoc, List.singleton_append, Bool.not_not]
    have hw : (fun k => wl C ℓ t k - sgn (!b) * A C k i) = wl C ℓ ((b, i) :: t) := by
      rw [wl_cons]; funext k; simp
    rw [hw]
    by_cases hφ : φ C q c ℓ (ew (ρW s ++ (b, i) :: t)) = 0
    · simp [hφ]
    · have hbal := wl_eq_of_balanced (C := C) ℓ (balanced_of_φ_ne_zero ℓ hφ)
      have hi : wl C ℓ s i = wl C ℓ t i + sgn b * 2 := by
        rw [hbal, wl_cons]; simp [A_self]
      have e : di C i * (1 - sgn b * wl C ℓ s i) + di C i * (1 - sgn (!b) * wl C ℓ t i) = 0 := by
        rw [hi, sgn_not]
        have := sgn_mul_self b
        linear_combination (-(2 : ℤ) * di C i) * this
      dsimp only
      rw [← mul_assoc, ← qp_add, ← add_assoc, e, zero_add]

/-- **KL III Prop. 2.2 (v)**: the form on `'U 1_λ` is symmetric. -/
theorem B_symm (ℓ : I → ℤ) (x y : Free K I) : B C q c ℓ x y = B C q c ℓ y x := by
  induction x using Free.induction generalizing y with
  | zero => simp
  | add x x' hx hx' => rw [map_add, LinearMap.add_apply, hx, hx', map_add]
  | smul_ew s r =>
    rw [map_smul, LinearMap.smul_apply, map_smul]
    congr 1
    induction s generalizing y with
    | nil => rw [ew_nil, B_one_left_eq]
    | cons l s ih => rw [B_rhoE, ih, B_rhoE_right]

/-! ### Property (iv) -/

/-- **KL III Prop. 2.2 (iv)**: `(x⁺ 1_λ, x'⁺ 1_λ) = (x, x')` for `x, x' ∈ 'f`. -/
theorem B_posF_posF (ℓ : I → ℤ) (x x' : PreF K I) :
    B C q c ℓ (posF x) (posF x') = fF C q c x x' := by
  have : (B C q c ℓ).compl₁₂ (posF (K := K) (I := I)).toLinearMap posF.toLinearMap =
      fF C q c := by
    refine PreF.lhom_ext fun u => PreF.lhom_ext fun u' => ?_
    simp only [LinearMap.compl₁₂_apply, AlgHom.toLinearMap_apply, posF_word]
    rw [B_ew_ew, ρW_posW, φ_negW_posW, List.reverse_reverse,
      FreeMonoid.ofList_toList, FreeMonoid.ofList_toList]
    by_cases hbc : wt u = wt u'
    · rw [fF_symm (word u')]
      have e : rcx C (wl C ℓ (posW u'.toList)) (posW u.toList) + Kx C ℓ u.toList.reverse = 0 := by
        have h2 := rcx_posW C (wl C ℓ (posW u'.toList)) u.toList
        have hw : wl C ℓ (posW u'.toList) = fun k => ℓ k + msA C k (u'.toList : Multiset I) := by
          funext k; simp [wl, aS_posW]
        rw [hw, S1_add_msA] at h2
        have h4 := two_mul_hsq C (u.toList.reverse : Multiset I)
        have hu : (u'.toList : Multiset I) = (u.toList : Multiset I) := hbc.symm
        rw [hw, Kx, Multiset.coe_reverse]
        rw [Multiset.coe_reverse] at h4
        have h5 : wdot C.dot (u.toList : Multiset I) (u'.toList : Multiset I) =
            wdot C.dot (u.toList : Multiset I) (u.toList : Multiset I) := by rw [hu]
        omega
      rw [← mul_assoc, ← qp_add, e, qp_zero, one_mul]
    · have h1 : fF C q c (word u') (word u) = 0 := by
        rw [fF, form_eq_zero_of_wt_ne]; exact Ne.symm hbc
      rw [h1, mul_zero, mul_zero, fF, form_eq_zero_of_wt_ne hbc]
  rw [← this]; rfl

end UDot

end Categorification.QuantumGroup

end
