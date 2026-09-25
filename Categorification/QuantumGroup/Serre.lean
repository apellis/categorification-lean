/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.Grading
import Categorification.QuantumGroup.Radical
import Categorification.QuantumGroup.Cartan

/-!
# The quantum Serre relations for a symmetric Cartan datum

Lusztig, *Introduction to quantum groups*, Proposition 1.4.3: for `i ≠ j` in a Cartan datum
and `N = 1 - 2 (i·j)/(i·i)`, the element
`Σ_{p + p' = N} (-1)^{p'} θ_i^{(p)} θ_j θ_i^{(p')}` lies in the radical `ℐ` of `( , )`.

We prove this in the form of iterated *twisted commutators*, which avoids quantum binomial
coefficients and works over any commutative ring `K` with a unit `v`:
`x₀ = θ_j`, `x_{m+1} = θ_i x_m - v^{|x_m|·i} x_m θ_i`, where `|x_m| = j + m i`
(`PreF.serreSeq`). By the quantum binomial theorem
`x_N = Σ_p (-1)^p [N choose p]_{v_i} θ_i^{N-p} θ_j θ_i^p = [N]_{v_i}^! · (Lusztig's element)`;
we do not formalise that expansion, but we check that `x₁` and `x₂` are the simply-laced
Serre elements `PreF.serreComm` and `PreF.serreCubic` (`PreF.serreSeq_one`,
`PreF.serreSeq_two`).

## Main results

* `PreF.serreSeq_mem_radical` — `x_N ∈ ℐ` whenever `2 (i·j) = (i·i)(1 - N)` and `N ≥ 1`
  (for a symmetric pairing `dot`).
* `CartanDatum.serre` — for a Cartan datum `C` and `i ≠ j`, the image of `x_N` in `f`
  vanishes, `N = 1 - 2(i·j)/(i·i)` (KL II's setting of general symmetric Cartan data).

The proof follows Lusztig 1.4.3: `x_N` has no constant term and is killed by every `d k`.
Here `d j x_m = 0` for `m ≥ 1`, and `d i x_{m+1} = β_{m+1} x_m` with
`β_m = Σ_{l<m} v^{(i·i)(m-1-l)} (1 - v^{2(j·i) + 2l(i·i)})`, which vanishes at `m = N`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open Finset
open scoped Classical

namespace PreF

variable {I : Type*} {K : Type*} [CommRing K] {dot : I → I → ℤ} {v : Kˣ}

/-- The twisted Leibniz rule for `d i` with a homogeneous left factor. -/
theorem d_mul_of_mem_grade (i : I) {μ : Multiset I} {x : PreF K I} (hx : x ∈ grade K μ)
    (y : PreF K I) :
    d dot v i (x * y) =
      d dot v i x * y + ((v ^ wdot dot μ {i} : Kˣ) : K) • (x * d dot v i y) := by
  refine eqOn_supp ((d dot v i) ∘ₗ LinearMap.mulRight K y)
    (LinearMap.mulRight K y ∘ₗ d dot v i +
      ((v ^ wdot dot μ {i} : Kˣ) : K) • LinearMap.mulRight K (d dot v i y)) ?_ x hx
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulRight_apply,
    LinearMap.add_apply, LinearMap.smul_apply, d_word_mul, hw]

theorem wdot_replicate (i : I) (m : ℕ) : wdot dot (Multiset.replicate m i) {i} = m * dot i i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Multiset.replicate_succ, wdot_cons_left, wdot_singleton, ih]
    push_cast
    ring

variable (dot v) in
/-- The iterated twisted commutators `x₀ = θ_j`,
`x_{m+1} = θ_i x_m - v^{(j + m i)·i} x_m θ_i` (a form of Lusztig's Serre element, 1.4.3). -/
def serreSeq (i j : I) : ℕ → PreF K I
  | 0 => θ j
  | m + 1 => θ i * serreSeq i j m -
      ((v ^ (dot j i + m * dot i i) : Kˣ) : K) • (serreSeq i j m * θ i)

theorem serreSeq_zero (i j : I) : serreSeq dot v i j 0 = (θ j : PreF K I) := rfl

theorem serreSeq_succ (i j : I) (m : ℕ) :
    serreSeq dot v i j (m + 1) = θ i * serreSeq dot v i j m -
      ((v ^ (dot j i + m * dot i i) : Kˣ) : K) • (serreSeq dot v i j m * θ i) := rfl

theorem serreSeq_mem_grade (i j : I) (m : ℕ) :
    (serreSeq dot v i j m : PreF K I) ∈ grade K (j ::ₘ Multiset.replicate m i) := by
  induction m with
  | zero => exact θ_mem_grade j
  | succ m ih =>
    have e1 : {i} + j ::ₘ Multiset.replicate m i = j ::ₘ Multiset.replicate (m + 1) i := by
      rw [Multiset.replicate_succ, Multiset.singleton_add, Multiset.cons_swap]
    have e2 : j ::ₘ Multiset.replicate m i + {i} = j ::ₘ Multiset.replicate (m + 1) i := by
      rw [add_comm, e1]
    rw [serreSeq_succ]
    refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_)
    · rw [← e1]; exact SetLike.mul_mem_graded (θ_mem_grade i) ih
    · rw [← e2]; exact SetLike.mul_mem_graded ih (θ_mem_grade i)

theorem counit_θ (i : I) : counit (θ i : PreF K I) = 0 := by
  rw [← mul_one (θ i), counit_θ_mul]

theorem counit_serreSeq (i j : I) (m : ℕ) : counit (serreSeq dot v i j m : PreF K I) = 0 := by
  induction m with
  | zero => exact counit_θ j
  | succ m ih => rw [serreSeq_succ, map_sub, map_smul, counit_θ_mul, counit_mul, ih, zero_mul,
      smul_zero, sub_zero]

theorem d_serreSeq_of_ne (i j k : I) (hi : i ≠ k) (hj : j ≠ k) (m : ℕ) :
    d dot v k (serreSeq dot v i j m : PreF K I) = 0 := by
  induction m with
  | zero => rw [serreSeq_zero, d_θ, if_neg hj]
  | succ m ih =>
    rw [serreSeq_succ, map_sub, map_smul, d_θ_mul, if_neg hi, ih,
      d_mul_of_mem_grade k (serreSeq_mem_grade i j m), ih, d_θ, if_neg hi]
    simp

theorem d_serreSeq_right (hdot : ∀ i j, dot i j = dot j i) (i j : I) (hij : i ≠ j) (m : ℕ) :
    d dot v j (serreSeq dot v i j (m + 1) : PreF K I) = 0 := by
  induction m with
  | zero =>
    rw [serreSeq_succ, serreSeq_zero, map_sub, map_smul, d_θ_mul, d_θ_mul, d_θ, d_θ,
      if_neg hij, if_pos rfl, hdot i j]
    simp [hij]
  | succ m ih =>
    rw [serreSeq_succ (m := m + 1), map_sub, map_smul, d_θ_mul, if_neg hij, ih,
      d_mul_of_mem_grade j (serreSeq_mem_grade i j (m + 1)), ih, d_θ, if_neg hij]
    simp

variable (dot v) in
/-- The coefficients `β_m` with `d_i x_m = β_m x_{m-1}`:
`β₀ = 0`, `β_{m+1} = 1 - v^{2(j + m i)·i} + v^{i·i} β_m`. -/
def serreβ (i j : I) : ℕ → K
  | 0 => 0
  | m + 1 => 1 - ((v ^ (dot j i + m * dot i i) : Kˣ) : K) ^ 2 +
      ((v ^ dot i i : Kˣ) : K) * serreβ i j m

theorem d_serreSeq_left (i j : I) (hij : i ≠ j) (m : ℕ) :
    d dot v i (serreSeq dot v i j (m + 1) : PreF K I) =
      serreβ dot v i j (m + 1) • serreSeq dot v i j m := by
  have hw : ∀ m : ℕ, wdot dot (j ::ₘ Multiset.replicate m i) {i} = dot j i + m * dot i i := by
    intro m; rw [wdot_cons_left, wdot_singleton, wdot_replicate]
  induction m with
  | zero =>
    simp only [serreSeq_succ, serreSeq_zero, map_sub, map_smul, d_θ_mul, d_θ, if_true,
      if_neg (Ne.symm hij), smul_zero, add_zero, mul_zero, mul_one, serreβ, Nat.cast_zero,
      zero_mul]
    module
  | succ m ih =>
    rw [serreSeq_succ (m := m + 1), map_sub, map_smul, d_θ_mul, if_pos rfl, ih,
      d_mul_of_mem_grade i (serreSeq_mem_grade i j (m + 1)), ih, d_θ, if_pos rfl, hw, mul_one]
    have hc : ((v ^ (dot j i + ((m + 1 : ℕ) : ℤ) * dot i i) : Kˣ) : K) =
        ((v ^ dot i i : Kˣ) : K) * ((v ^ (dot j i + (m : ℤ) * dot i i) : Kˣ) : K) := by
      rw [← Units.val_mul, ← zpow_add]; congr 2; push_cast; ring
    have hx := serreSeq_succ (dot := dot) (v := v) (K := K) i j m
    have hβ : serreβ dot v i j (m + 1 + 1) = 1 - ((v ^ (dot j i + ((m + 1 : ℕ) : ℤ) * dot i i) :
        Kˣ) : K) ^ 2 + ((v ^ dot i i : Kˣ) : K) * serreβ dot v i j (m + 1) := rfl
    rw [hβ]
    simp only [smul_mul_assoc, mul_smul_comm]
    linear_combination (norm := module)
      (-(((v ^ dot i i : Kˣ) : K) * serreβ dot v i j (m + 1))) • hx +
        (-serreβ dot v i j (m + 1)) • hc • (serreSeq dot v i j m * θ i)

theorem serreβ_eq (i j : I) (m : ℕ) :
    serreβ dot v i j m = ∑ l ∈ range m,
      (((v ^ (dot i i * ((m : ℤ) - 1 - l)) : Kˣ) : K) -
        ((v ^ (dot i i * ((m : ℤ) - 1 - l) + 2 * (dot j i + l * dot i i)) : Kˣ) : K)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [serreβ, ih, sum_range_succ, mul_sum]
    have : ∀ l ∈ range m,
        ((v ^ dot i i : Kˣ) : K) * (((v ^ (dot i i * ((m : ℤ) - 1 - l)) : Kˣ) : K) -
          ((v ^ (dot i i * ((m : ℤ) - 1 - l) + 2 * (dot j i + l * dot i i)) : Kˣ) : K)) =
        ((v ^ (dot i i * (((m + 1 : ℕ) : ℤ) - 1 - l)) : Kˣ) : K) -
          ((v ^ (dot i i * (((m + 1 : ℕ) : ℤ) - 1 - l) + 2 * (dot j i + l * dot i i)) : Kˣ) :
            K) := by
      intro l _
      rw [mul_sub, ← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add]
      congr 3 <;> push_cast <;> ring
    rw [sum_congr rfl this]
    have e1 : dot i i * (((m + 1 : ℕ) : ℤ) - 1 - m) = 0 := by push_cast; ring
    rw [e1, zpow_zero, Units.val_one, zero_add, ← Units.val_pow_eq_pow_val, ← zpow_natCast,
      ← zpow_mul]
    rw [mul_comm (dot j i + _) ((2 : ℕ) : ℤ)]
    push_cast
    ring

theorem serreβ_eq_zero (hdot : ∀ i j, dot i j = dot j i) (i j : I) {N : ℕ}
    (hN : 2 * dot i j = dot i i * (1 - N)) : serreβ dot v i j N = 0 := by
  rw [serreβ_eq, sum_sub_distrib, sub_eq_zero]
  have h1 : ∀ l ∈ range N, ((v ^ (dot i i * ((N : ℤ) - 1 - l) + 2 * (dot j i + l * dot i i)) :
      Kˣ) : K) = ((v ^ (dot i i * l)) : Kˣ) := by
    intro l _
    congr 2
    rw [← hdot i j]
    linear_combination hN
  rw [sum_congr rfl h1, ← sum_range_reflect]
  refine sum_congr rfl fun l hl => ?_
  rw [mem_range] at hl
  congr 3
  push_cast [Nat.sub_sub, Nat.cast_sub (by omega : 1 + l ≤ N)]
  ring

/-- **Lusztig, Proposition 1.4.3** (quantum Serre relations), for a symmetric pairing `dot`:
if `i ≠ j`, `N ≥ 1` and `2 (i·j) = (i·i)(1 - N)`, then the iterated twisted commutator
`x_N = serreSeq dot v i j N` lies in the radical `ℐ` of the form `( , )` (for any values
`c`). -/
theorem serreSeq_mem_radical (c : I → K) (hdot : ∀ i j, dot i j = dot j i) {i j : I}
    (hij : i ≠ j) {N : ℕ} (hN1 : 1 ≤ N) (hN : 2 * dot i j = dot i i * (1 - N)) :
    serreSeq dot v i j N ∈ radical dot v c := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  refine mem_radical_of_d hdot (counit_serreSeq i j _) fun k => ?_
  have : d dot v k (serreSeq dot v i j (M + 1) : PreF K I) = 0 := by
    by_cases hki : i = k
    · subst hki
      rw [d_serreSeq_left i j hij, serreβ_eq_zero hdot i j hN, zero_smul]
    · by_cases hkj : j = k
      · subst hkj; exact d_serreSeq_right hdot i j hij M
      · exact d_serreSeq_of_ne i j k hki hkj _
  rw [this]
  exact Submodule.zero_mem _

/-! ### Comparison with the simply-laced Serre elements -/

theorem serreSeq_one (i j : I) (h0 : dot j i = 0) :
    serreSeq dot v i j 1 = (serreComm i j : PreF K I) := by
  simp [serreSeq, serreComm, h0]

theorem serreSeq_two (i j : I) (hii : dot i i = 2) (h1 : dot j i = -1) :
    serreSeq dot v i j 2 = (serreCubic v i j : PreF K I) := by
  have hvv : (v : K) * ((v⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [serreSeq, serreCubic, hii, h1, Nat.cast_zero, Nat.cast_one, zero_mul, add_zero,
    one_mul, zpow_neg, zpow_one, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc,
    smul_sub]
  have e : (-1 + 2 : ℤ) = 1 := by norm_num
  rw [e, zpow_one]
  linear_combination (norm := module) hvv • (θ j * (θ i * θ i) : PreF K I)

end PreF

/-! ### Cartan data -/

namespace CartanDatum

variable {I : Type*} (C : CartanDatum I)

/-- `N = 1 - 2(i·j)/(i·i)`, the length of the Serre relation for `i ≠ j`. -/
def serreN (i j : I) : ℕ := (1 - 2 * C.dot i j / C.dot i i).toNat

theorem two_mul_dot_div (i j : I) :
    ∃ q : ℤ, 2 * C.dot i j = C.dot i i * q ∧ 2 * C.dot i j / C.dot i i = q := by
  obtain ⟨q, hq⟩ := C.dvd_two_mul i j
  exact ⟨q, hq, by rw [hq, Int.mul_ediv_cancel_left _ (C.dot_self_pos i).ne']⟩

theorem one_le_serreN {i j : I} (hij : i ≠ j) : 1 ≤ C.serreN i j := by
  have hpos := C.dot_self_pos i
  have hnp := C.dot_nonpos i j hij
  obtain ⟨q, hq, hq'⟩ := C.two_mul_dot_div i j
  have : q ≤ 0 := by nlinarith
  unfold serreN
  omega

theorem two_mul_dot_eq {i j : I} (hij : i ≠ j) :
    2 * C.dot i j = C.dot i i * (1 - (C.serreN i j : ℤ)) := by
  have hpos := C.dot_self_pos i
  have hnp := C.dot_nonpos i j hij
  obtain ⟨q, hq, hq'⟩ := C.two_mul_dot_div i j
  have : q ≤ 0 := by nlinarith
  have hN : (C.serreN i j : ℤ) = 1 - q := by
    unfold serreN; omega
  rw [hN, sub_sub_cancel, hq]

/-- **Lusztig 1.4.3 for a Cartan datum** (KL II's general symmetric Cartan data): for
`i ≠ j`, the Serre element `x_N`, `N = 1 - 2(i·j)/(i·i)`, lies in the radical of the form,
for any unit `v` and any values `c i = (θ i, θ i)`. -/
theorem serre_mem_radical {K : Type*} [CommRing K] (v : Kˣ) (c : I → K) {i j : I}
    (hij : i ≠ j) :
    PreF.serreSeq C.dot v i j (C.serreN i j) ∈ PreF.radical C.dot v c :=
  PreF.serreSeq_mem_radical c C.symm hij (C.one_le_serreN hij) (C.two_mul_dot_eq hij)

/-- The quantum Serre relations hold in `f` (Lusztig 1.4.3). -/
theorem serre {K : Type*} [CommRing K] (v : Kˣ) (c : I → K) {i j : I} (hij : i ≠ j) :
    PreF.π C.dot v c (PreF.serreSeq C.dot v i j (C.serreN i j)) = 0 :=
  PreF.π_eq_zero_iff.2 (C.serre_mem_radical v c hij)

/-- The Serre elements `x_N` (`i ≠ j`, `N = 1 - 2(i·j)/(i·i)`) of the Cartan datum `C`. -/
def serreSet {K : Type*} [CommRing K] (v : Kˣ) : Set (PreF K I) :=
  {x | ∃ i j, i ≠ j ∧ x = PreF.serreSeq C.dot v i j (C.serreN i j)}

/-- **Statement only (not proved here).** The quantum Gabber–Kac theorem (Lusztig 33.1.3) for
the Cartan datum `C`: the radical of `( , )` is the two-sided ideal generated by the Serre
elements. Lusztig proves it for `K = ℚ(v)` and his normalisation `c = lusztigC C.dot v`; it
must only ever be used as an explicit hypothesis. -/
def GabberKac {K : Type*} [CommRing K] (v : Kˣ) (c : I → K) : Prop :=
  PreF.radical C.dot v c = TwoSidedIdeal.asIdeal (TwoSidedIdeal.span (C.serreSet v))

/-- The inclusion `⊇` of the Gabber–Kac theorem, proved here (Lusztig 1.4.3). -/
theorem span_serreSet_le_radical {K : Type*} [CommRing K] (v : Kˣ) (c : I → K) :
    TwoSidedIdeal.asIdeal (TwoSidedIdeal.span (C.serreSet v)) ≤ PreF.radical C.dot v c := by
  have h : TwoSidedIdeal.span (C.serreSet v) ≤ (PreF.radical C.dot v c).toTwoSided := by
    rw [TwoSidedIdeal.span_le]
    rintro x ⟨i, j, hij, rfl⟩
    exact Ideal.mem_toTwoSided.2 (C.serre_mem_radical v c hij)
  intro x hx
  exact Ideal.mem_toTwoSided.1 (h (TwoSidedIdeal.mem_asIdeal.1 hx))

end CartanDatum

end Categorification.QuantumGroup

end
