/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.UDotNondegModel

/-!
# The form on `'U 1_λ` is a tensor product form in the model

Khovanov–Lauda III, arXiv:0807.3250v1, §2.1.3 (Proposition 2.2 and the proof of Proposition 2.5).
On the model `M = 'f ⊗ 'f` of `Categorification.QuantumGroup.UDotNondegModel` let
`ndP (x ⊗ y, x' ⊗ y') = (x, x') (y, y')` (`UDot.ndP`), the tensor square of the form on `'f`.
For KL III's normalisation `(θ_i, θ_i) = (1 - q_i²)⁻¹` we prove:

* `UDot.ndP_ndE`, `UDot.ndP_ndF` — `ndP` is contravariant for the model action, with the same
  factors as `ρ̄` (`(E_i m, m') = q_i^{1 - ⟨i, μ'⟩} (m, F_i m')`,
  `(F_i m, m') = q_i^{1 + ⟨i, μ'⟩} (m, E_i m')` for `m'` of weight `μ'`);
* **`UDot.B_eq_ndP`** — the form `( , )` on `'U 1_λ` (`UDot.B`) is
  `(z, w) = ndP (ndNF z, ndNF w)`.

The proof of `B_eq_ndP` is a uniqueness argument at the level of the free algebra: both sides
satisfy property (iii) of Prop. 2.2 for `E_{±i}`, respect the commutation relations in the
second argument, are symmetric and restrict to the form on `'f` on `x⁺ 1_λ` (property (iv));
normal ordering (`UDot.normal_induction`) then identifies them.
-/

noncomputable section

namespace Categorification.QuantumGroup

open scoped Classical
open PreF

namespace UDot

variable {I : Type*} {K : Type*} [Field K] (C : CartanDatum I) (q : Kˣ) (c : I → K)

/-! ### The tensor square of the form on `'f` -/

/-- The form `(x ⊗ y, x' ⊗ y') = (x, x')(y, y')` on `M = 'f ⊗ 'f`. -/
def ndP : M K I →ₗ[K] M K I →ₗ[K] K :=
  Finsupp.linearCombination K fun p => Finsupp.linearCombination K fun p' =>
    fF C q c (word p.1) (word p'.1) * fF C q c (word p.2) (word p'.2)

variable {C q c}

theorem ndP_tm_word (u w u' w' : FreeMonoid I) :
    ndP C q c (tm (word u) (word w)) (tm (word u') (word w')) =
      fF C q c (word u) (word u') * fF C q c (word w) (word w') := by
  rw [tm_word_word, tm_word_word, ndP, Finsupp.linearCombination_single, one_smul,
    Finsupp.linearCombination_single, one_smul]

theorem ndP_tm_word_left (u w : FreeMonoid I) (x' y' : PreF K I) :
    ndP C q c (tm (word u) (word w)) (tm x' y') = fF C q c (word u) x' * fF C q c (word w) y' := by
  induction x' using induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']; ring
  | smul_word u' r =>
    induction y' using induction_linear with
    | zero => simp
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, mul_add]
    | smul_word w' s =>
      simp only [map_smul, LinearMap.smul_apply, ndP_tm_word, smul_eq_mul]
      ring

theorem ndP_tm (x y x' y' : PreF K I) :
    ndP C q c (tm x y) (tm x' y') = fF C q c x x' * fF C q c y y' := by
  induction x using induction_linear with
  | zero => simp
  | add x x₁ hx hx₁ => rw [map_add, LinearMap.add_apply, map_add, LinearMap.add_apply, hx, hx₁,
      map_add, LinearMap.add_apply, add_mul]
  | smul_word u r =>
    induction y using induction_linear with
    | zero => simp
    | add y y₁ hy hy₁ => rw [map_add, map_add, LinearMap.add_apply, hy, hy₁, map_add,
        LinearMap.add_apply, mul_add]
    | smul_word w s =>
      simp only [map_smul, LinearMap.smul_apply, ndP_tm_word_left, smul_eq_mul]
      ring

/-- A linear map out of `M` vanishing on the basis vanishes. -/
theorem M_induction {motive : M K I → Prop} (v : M K I) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (smul : ∀ (r : K) x, motive x → motive (r • x))
    (basis : ∀ u w : FreeMonoid I, motive (tm (word u) (word w))) : motive v := by
  induction v using Finsupp.induction_linear with
  | zero => exact zero
  | add x y hx hy => exact add x y hx hy
  | single p r =>
    have : (Finsupp.single p r : M K I) = r • tm (word p.1) (word p.2) := by
      rw [tm_word_word, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [this]
    exact smul r _ (basis p.1 p.2)

theorem ndP_symm (m m' : M K I) : ndP C q c m m' = ndP C q c m' m := by
  induction m using M_induction generalizing m' with
  | zero => simp
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, map_add]
  | smul r x hx => simp only [map_smul, LinearMap.smul_apply, hx, smul_eq_mul]
  | basis u w =>
    induction m' using M_induction with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, map_add, LinearMap.add_apply]
    | smul r x hx => rw [map_smul, hx, map_smul, LinearMap.smul_apply]
    | basis u' w' => rw [ndP_tm_word, ndP_tm_word, fF_symm (word u), fF_symm (word w)]

/-! ### Contravariance -/

/-- `(x, y) = 0` unless `x`, `y` have the same weight, for `x` in a span of words. -/
theorem fF_eq_zero_of_supp {S : Set (FreeMonoid I)} {x : PreF K I}
    (hx : x ∈ (supp S : Submodule K (PreF K I))) {u' : FreeMonoid I} (h : ∀ v ∈ S, wt v ≠ wt u') :
    fF C q c x (word u') = 0 :=
  eqOn_supp ((fF C q c).flip (word u')) 0 (fun v hv => by
    simp only [LinearMap.flip_apply, LinearMap.zero_apply, fF]
    exact form_eq_zero_of_wt_ne (h v hv)) x hx

theorem fF_d_word_eq_zero (i : I) {u u' : FreeMonoid I} (h : i ::ₘ wt u' ≠ wt u) :
    fF C q c (PreF.d C.dot q⁻¹ i (word u)) (word u') = 0 :=
  fF_eq_zero_of_supp (d_word_mem_supp i u) fun v hv hvu => h (by
    simp only [Set.mem_setOf_eq] at hv; rw [← hv, hvu])

theorem fF_θ_mul (i : I) (x y : PreF K I) :
    fF C q c (θ i * x) y = c i * fF C q c x (PreF.d C.dot q⁻¹ i y) := form_θ_mul i x y

theorem fF_word_eq_zero {w w' : FreeMonoid I} (h : wt w ≠ wt w') :
    fF C q c (word w) (word w') = 0 := form_eq_zero_of_wt_ne h

variable (hc : ∀ i, c i = (1 - ((qi C q i : Kˣ) : K) ^ 2)⁻¹)
include hc

theorem qp_mul_ndG (i : I) : qp q (di C i) * ndG C q i = c i := by
  rw [ndG, hc, ← mul_assoc, ← qp_add, add_neg_cancel, qp_zero, one_mul]
  congr 2
  rw [show (2 : ℤ) * di C i = di C i + di C i by ring, qp_add, pow_two]
  rfl

theorem ndP_ndE_word (ℓ : I → ℤ) (i : I) (u w u' w' : FreeMonoid I) :
    ndP C q c (ndE C q ℓ i (tm (word u) (word w))) (tm (word u') (word w')) =
      qp q (di C i * (1 - ndWn C ℓ i u' w')) *
        ndP C q c (tm (word u) (word w)) (ndF C q ℓ i (tm (word u') (word w'))) := by
  have hg := qp_mul_ndG hc i
  rw [ndE_tm_word, ndF_tm_word, map_add, map_add, map_smul, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, ndP_tm, ndP_tm, ndP_tm, ndP_tm, smul_eq_mul, smul_eq_mul]
  rw [fF_θ_mul, fF_symm (word u) (θ i * word u'), fF_θ_mul, fF_symm (word u')]
  -- the `d_i x` term vanishes unless the weights match
  have e2 : ∀ n : ℤ, qp q (di C i * (1 - n)) * (ndG C q i * qp q (di C i * n)) =
      qp q (di C i) * ndG C q i := fun n => by
    rw [mul_left_comm, ← qp_add, mul_comm]; congr 2; ring
  rw [← hg]
  by_cases hw : i ::ₘ wt u' = wt u ∧ wt w = wt w'
  · obtain ⟨h1, h2⟩ := hw
    have hn : ndWn C ℓ i u' w' = ndWn C ℓ i u w + 2 := by
      simp only [ndWn, ← h1, ← h2, msA_cons, A_self]; ring
    rw [hn]
    have e1 : qp q (di C i * (1 - (ndWn C ℓ i u w + 2))) * (qp q (di C i) * ndG C q i) =
        ndG C q i * qp q (-(di C i * ndWn C ℓ i u w)) := by
      rw [← mul_assoc, ← qp_add, mul_comm]; congr 2; ring
    linear_combination (-(fF C q c (PreF.d C.dot q⁻¹ i (word u)) (word u') *
        fF C q c (word w) (word w'))) * e1 -
      (fF C q c (word u) (word u') * fF C q c (word w) (PreF.d C.dot q⁻¹ i (word w'))) *
        e2 (ndWn C ℓ i u w + 2)
  · have hz : fF C q c (PreF.d C.dot q⁻¹ i (word u)) (word u') * fF C q c (word w) (word w') = 0 := by
      by_cases h1 : i ::ₘ wt u' = wt u
      · rw [fF_word_eq_zero (fun h2 => hw ⟨h1, h2⟩), mul_zero]
      · rw [fF_d_word_eq_zero i h1, zero_mul]
    linear_combination (ndG C q i * qp q (-(di C i * ndWn C ℓ i u w)) -
        qp q (di C i * (1 - ndWn C ℓ i u' w')) * (qp q (di C i) * ndG C q i)) * hz -
      (fF C q c (word u) (word u') * fF C q c (word w) (PreF.d C.dot q⁻¹ i (word w'))) *
        e2 (ndWn C ℓ i u' w')

theorem ndP_ndF_word (ℓ : I → ℤ) (i : I) (u w u' w' : FreeMonoid I) :
    ndP C q c (ndF C q ℓ i (tm (word u) (word w))) (tm (word u') (word w')) =
      qp q (di C i * (1 + ndWn C ℓ i u' w')) *
        ndP C q c (tm (word u) (word w)) (ndE C q ℓ i (tm (word u') (word w'))) := by
  have hg := qp_mul_ndG hc i
  rw [ndF_tm_word, ndE_tm_word, map_add, map_add, map_smul, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, ndP_tm, ndP_tm, ndP_tm, ndP_tm, smul_eq_mul, smul_eq_mul]
  rw [fF_θ_mul, fF_symm (word w) (θ i * word w'), fF_θ_mul, fF_symm (word w')]
  have e3 : ∀ n : ℤ, qp q (di C i * (1 + n)) * (ndG C q i * qp q (-(di C i * n))) =
      qp q (di C i) * ndG C q i := fun n => by
    rw [mul_left_comm, ← qp_add, mul_comm]; congr 2; ring
  rw [← hg]
  by_cases hw : wt u = wt u' ∧ i ::ₘ wt w' = wt w
  · obtain ⟨h1, h2⟩ := hw
    have hn : ndWn C ℓ i u w = ndWn C ℓ i u' w' + 2 := by
      simp only [ndWn, ← h1, ← h2, msA_cons, A_self]; ring
    rw [hn]
    have e4 : qp q (di C i * (1 + ndWn C ℓ i u' w')) * (qp q (di C i) * ndG C q i) =
        ndG C q i * qp q (di C i * (ndWn C ℓ i u' w' + 2)) := by
      rw [← mul_assoc, ← qp_add, mul_comm]; congr 2; ring
    linear_combination (-(fF C q c (word u) (word u') *
        fF C q c (PreF.d C.dot q⁻¹ i (word w)) (word w'))) * e4 -
      (fF C q c (word u) (PreF.d C.dot q⁻¹ i (word u')) * fF C q c (word w) (word w')) *
        e3 (ndWn C ℓ i u' w')
  · have hz : fF C q c (word u) (word u') * fF C q c (PreF.d C.dot q⁻¹ i (word w)) (word w') = 0 := by
      by_cases h1 : wt u = wt u'
      · rw [fF_d_word_eq_zero i (fun h2 => hw ⟨h1, h2⟩), mul_zero]
      · rw [fF_word_eq_zero h1, zero_mul]
    linear_combination (ndG C q i * qp q (di C i * ndWn C ℓ i u w) -
        qp q (di C i * (1 + ndWn C ℓ i u' w')) * (qp q (di C i) * ndG C q i)) * hz -
      (fF C q c (word u) (PreF.d C.dot q⁻¹ i (word u')) * fF C q c (word w) (word w')) *
        e3 (ndWn C ℓ i u' w')

/-- Contravariance for `E_i`: `(E_i m, m') = q_i^{1 - ⟨i, μ'⟩} (m, F_i m')` for `m'` of
signed weight `P - N` (`⟨i, μ'⟩ = ⟨i, λ + P - N⟩`). -/
theorem ndP_ndE (ℓ : I → ℤ) (i : I) {P N : Multiset I} {m' : M K I} (hm' : m' ∈ Msupp P N)
    (m : M K I) :
    ndP C q c (ndE C q ℓ i m) m' =
      qp q (di C i * (1 - (ℓ i + msA C i P - msA C i N))) * ndP C q c m (ndF C q ℓ i m') := by
  refine Msupp_induction (motive := fun m' => ∀ m, ndP C q c (ndE C q ℓ i m) m' =
      qp q (di C i * (1 - (ℓ i + msA C i P - msA C i N))) * ndP C q c m (ndF C q ℓ i m'))
    hm' (by simp) (fun x y hx hy m => by
      simp only [map_add, LinearMap.add_apply, hx m, hy m]; ring)
    (fun r x hx m => by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx m]; ring)
    (fun u' w' h m => ?_) m
  have hn : ndWn C ℓ i u' w' = ℓ i + msA C i P - msA C i N := by
    have := congrArg (msA C i) h
    simp only [msA_add] at this
    simp only [ndWn]; linarith
  induction m using M_induction with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]; ring
  | smul r x hx => simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx]; ring
  | basis u w => rw [ndP_ndE_word hc, hn]

/-- Contravariance for `F_i`: `(F_i m, m') = q_i^{1 + ⟨i, μ'⟩} (m, E_i m')`. -/
theorem ndP_ndF (ℓ : I → ℤ) (i : I) {P N : Multiset I} {m' : M K I} (hm' : m' ∈ Msupp P N)
    (m : M K I) :
    ndP C q c (ndF C q ℓ i m) m' =
      qp q (di C i * (1 + (ℓ i + msA C i P - msA C i N))) * ndP C q c m (ndE C q ℓ i m') := by
  refine Msupp_induction (motive := fun m' => ∀ m, ndP C q c (ndF C q ℓ i m) m' =
      qp q (di C i * (1 + (ℓ i + msA C i P - msA C i N))) * ndP C q c m (ndE C q ℓ i m'))
    hm' (by simp) (fun x y hx hy m => by
      simp only [map_add, LinearMap.add_apply, hx m, hy m]; ring)
    (fun r x hx m => by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx m]; ring)
    (fun u' w' h m => ?_) m
  have hn : ndWn C ℓ i u' w' = ℓ i + msA C i P - msA C i N := by
    have := congrArg (msA C i) h
    simp only [msA_add] at this
    simp only [ndWn]; linarith
  induction m using M_induction with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]; ring
  | smul r x hx => simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx]; ring
  | basis u w => rw [ndP_ndF_word hc, hn]

omit hc in
variable (C q c) in
/-- The form `(z, w) ↦ ndP (ndNF z, ndNF w)` on `'U 1_λ`. -/
def ndB (ℓ : I → ℤ) : Free K I →ₗ[K] Free K I →ₗ[K] K :=
  (ndP C q c).compl₁₂ (ndNF C q ℓ) (ndNF C q ℓ)

omit hc in
theorem ndB_apply (ℓ : I → ℤ) (z w : Free K I) :
    ndB C q c ℓ z w = ndP C q c (ndNF C q ℓ z) (ndNF C q ℓ w) := rfl

/-- `ndB` satisfies property (iii) of KL III Prop. 2.2 for the generators `E_{±i}`. -/
theorem ndB_rhoE (ℓ : I → ℤ) (l : Bool × I) (s : List (Bool × I)) (y : Free K I) :
    ndB C q c ℓ (ew (l :: s)) y = ndB C q c ℓ (ew s) (rhoE C q ℓ l y) := by
  induction y using Free.induction with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  | smul_ew t r =>
    simp only [map_smul, rhoE_ew, smul_eq_mul, LinearMap.smul_apply]
    congr 1
    rw [ndB_apply, ndB_apply, ndNF_ew_cons, ndNF_ew_cons]
    obtain ⟨b, i⟩ := l
    have hwl : wl C ℓ t i = ℓ i + msA C i (posMS t) - msA C i (negMS t) := by
      rw [wl, aS_eq]; ring
    cases b
    · change ndP C q c (ndF C q ℓ i _) _ = _
      rw [ndP_ndF hc ℓ i (ndNF_mem_Msupp ℓ t), hwl]
      simp only [Bool.not_false, sgn_false]
      change _ = _ * ndP C q c _ (ndE C q ℓ i _)
      congr 2; ring
    · change ndP C q c (ndE C q ℓ i _) _ = _
      rw [ndP_ndE hc ℓ i (ndNF_mem_Msupp ℓ t), hwl]
      simp only [Bool.not_true, sgn_true]
      change _ = _ * ndP C q c _ (ndF C q ℓ i _)
      congr 2; ring

theorem ndB_append (ℓ : I → ℤ) (s s' : List (Bool × I)) (y : Free K I) :
    ndB C q c ℓ (ew (s ++ s')) y = ndB C q c ℓ (ew s') (R C q ℓ s y) := by
  induction s generalizing y with
  | nil => rfl
  | cons l s ih => rw [List.cons_append, ndB_rhoE hc, ih]; rfl

omit hc in
theorem ndB_symm (ℓ : I → ℤ) (z w : Free K I) : ndB C q c ℓ z w = ndB C q c ℓ w z := by
  rw [ndB_apply, ndB_apply, ndP_symm]

omit hc in
theorem ndB_posF_posF (ℓ : I → ℤ) (x x' : PreF K I) :
    ndB C q c ℓ (posF x) (posF x') = fF C q c x x' := by
  rw [ndB_apply, ndNF_posF, ndNF_posF, ndP_tm, fF, form_one_one, one_mul]

omit hc in
theorem ndB_comm_right (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ℓ : I → ℤ) (x : Free K I)
    (a b : List (Bool × I)) (i j : I) :
    ndB C q c ℓ x (ew (a ++ (true, i) :: (false, j) :: b)) =
      ndB C q c ℓ x (ew (a ++ (false, j) :: (true, i) :: b)) +
        if j = i then qbr (qi C q i) (wl C ℓ b i) * ndB C q c ℓ x (ew (a ++ b)) else 0 := by
  rw [ndB_apply, ndNF_comm hq, map_add, ndB_apply, ndB_apply]
  split_ifs <;> simp

/-- The value of `ndB` and `B` on normal-ordered sequences against `1_λ`. -/
theorem ndB_normal_one (ℓ : I → ℤ) (c' b : List I) :
    ndB C q c ℓ (ew (negW c' ++ posW b)) 1 = B C q c ℓ (ew (negW c' ++ posW b)) 1 := by
  rw [ndB_append hc, B_append, ← ew_nil,
    R_of_mem_Fg _ _ (ew_mem_Fg ([] : List (Bool × I))), map_smul, map_smul, ρW_negW, ew_nil,
    mul_one]
  have e1 : ew (posW b) = posF (word (FreeMonoid.ofList b) : PreF K I) := by
    rw [posF_word, FreeMonoid.toList_ofList]
  have e2 : ew (posW c'.reverse) = posF (word (FreeMonoid.ofList c'.reverse) : PreF K I) := by
    rw [posF_word, FreeMonoid.toList_ofList]
  rw [e1, e2, ndB_posF_posF, B_posF_posF]

/-- **The form `( , )` on `'U 1_λ` is the tensor-square form in the model**:
`(z, w) = ndP (ndNF z, ndNF w)` (for KL III's normalisation of the form on `'f`). -/
theorem B_eq_ndP (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (ℓ : I → ℤ) (z w : Free K I) :
    B C q c ℓ z w = ndP C q c (ndNF C q ℓ z) (ndNF C q ℓ w) := by
  rw [← ndB_apply]
  -- reduce to `z = 1` using property (iii)
  have hone : ∀ y, B C q c ℓ 1 y = ndB C q c ℓ 1 y := by
    intro y
    induction y using Free.induction with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | smul_ew t r =>
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      congr 1
      induction t using normal_induction with
      | hN c' b =>
        rw [B_symm, ndB_symm]
        exact (ndB_normal_one hc ℓ c' b).symm
      | hS a i j b h1 h2 =>
        rw [B_comm_right, ndB_comm_right hq, h1, h2]
  induction z using Free.induction generalizing w with
  | zero => simp
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, map_add, LinearMap.add_apply]
  | smul_ew s r =>
    rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply]
    congr 1
    have h1 := B_append (C := C) (q := q) (c := c) ℓ s [] w
    have h2 := ndB_append hc ℓ s [] w
    rw [List.append_nil] at h1 h2
    rw [h1, h2, ew_nil, hone]

end UDot

end Categorification.QuantumGroup

end
