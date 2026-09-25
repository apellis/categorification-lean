/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.PreF

/-!
# Lusztig's bilinear form on `'f`

Lusztig, *Introduction to quantum groups*, Proposition 1.2.3: there is a unique bilinear
form `( , )` on `'f` with `(1, 1) = 1` and

* (a) `(θ i, θ j) = δ_{ij} (1 - v_i^{-2})^{-1}`,
* (b) `(x, y' y'') = (r x, y' ⊗ y'')`,
* (c) `(x' x'', y) = (x' ⊗ x'', r y)`,

where `(x₁ ⊗ x₂, y₁ ⊗ y₂) = (x₁, y₁)(x₂, y₂)` on `'f ⊗ 'f`; the form is symmetric.
Khovanov–Lauda (arXiv:0803.4121v2, §3.1, the paragraph after Proposition 3.3 =
`prop-pairing-prop`) use the form "uniquely determined by the same conditions" as their
Proposition 3.3: `(1,1) = 1`, `([P_i],[P_j]) = δ_{ij}(1 - q²)^{-1}`,
`(x, yy') = ([Res] x, y ⊗ y')`, `(xx', y) = (x ⊗ x', [Res] y)`; with their `q = v⁻¹` and
`i · i = 2` this is exactly Lusztig's normalisation `(1 - v^{-2})^{-1}`.

We work over an arbitrary commutative ring `K` with a unit `v`, a pairing
`dot : I → I → ℤ`, and *arbitrary* values `c i = (θ i, θ i) ∈ K`; Lusztig's normalisation is
the specialisation `c i = (1 - v^{-(i·i)})⁻¹` (`lusztigC`) over a field.

## Construction

Using the twisted derivations `d i` of `Categorification.QuantumGroup.PreF`, we define
`(θ i x, y) = c i (x, d i y)` and `(1, y) = ε(y)` (recursion on the first argument, which is
a word). Property (c) then follows from `r ∘ d i = (d i ⊗ 1) ∘ r` and `(ε ⊗ 1) ∘ r = id`;
property (b) follows from the twisted Leibniz rule for `d i` and orthogonality of distinct
weight spaces, and needs `dot` to be symmetric. Uniqueness is by induction on the length of
the first argument, and symmetry follows from uniqueness.

## Main results

* `PreF.form dot v c` — the bilinear form.
* `PreF.form_one_one`, `PreF.form_θ_θ`, `PreF.form_mul_left` (property (c)),
  `PreF.form_mul_right` (property (b)).
* `PreF.form_unique` — uniqueness; `PreF.form_symm` — symmetry;
  `PreF.existsUnique_form` — Lusztig 1.2.3 as an `∃!` statement.
* `PreF.form_eq_zero_of_wt_ne` — distinct weight spaces are orthogonal.
-/

noncomputable section

namespace Categorification.QuantumGroup

open TwistedMonoidAlgebra (single)
open scoped Classical

namespace PreF

variable {I : Type*} {K : Type*} [CommRing K] {dot : I → I → ℤ} {v : Kˣ}

/-! ### The induced form on the tensor square -/

/-- The bilinear form `(x₁ ⊗ x₂, y₁ ⊗ y₂) = B(x₁, y₁) B(x₂, y₂)` on `'f ⊗ 'f` induced by a
bilinear form `B` on `'f` (Lusztig 1.2.3). -/
def pair (B : PreF K I →ₗ[K] PreF K I →ₗ[K] K) :
    TwSq K I dot v →ₗ[K] TwSq K I dot v →ₗ[K] K :=
  TwistedMonoidAlgebra.lift fun p =>
    TwistedMonoidAlgebra.lift fun q => B (word p.1) (word q.1) * B (word p.2) (word q.2)

variable (B : PreF K I →ₗ[K] PreF K I →ₗ[K] K)

theorem pair_single_single (a b c e : FreeMonoid I) (r s : K) :
    pair (dot := dot) (v := v) B (single (a, b) r) (single (c, e) s) =
      r * (s * (B (word a) (word c) * B (word b) (word e))) := by
  simp [pair, smul_eq_mul]

theorem single_eq_smul_tw (a b : FreeMonoid I) (s : K) :
    (single (a, b) s : TwSq K I dot v) = s • tw dot v (word a) (word b) := by
  rw [tw_word, TwistedMonoidAlgebra.smul_single, mul_one]

theorem pair_single_tw (a b : FreeMonoid I) (s : K) (y₁ y₂ : PreF K I) :
    pair B (single (a, b) s) (tw dot v y₁ y₂) = s * (B (word a) y₁ * B (word b) y₂) := by
  induction y₁ using induction_linear with
  | zero => simp
  | add y y' hy hy' => rw [tw_add_left, map_add, hy, hy', map_add]; ring
  | smul_word w c =>
    induction y₂ using induction_linear with
    | zero => simp
    | add y y' hy hy' => rw [tw_add_right, map_add, hy, hy', map_add (B (word b))]; ring
    | smul_word w' c' =>
      rw [tw_smul_left, tw_smul_right, tw_word, map_smul, map_smul, pair_single_single]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring

theorem pair_tw_tw (x₁ x₂ y₁ y₂ : PreF K I) :
    pair B (tw dot v x₁ x₂) (tw dot v y₁ y₂) = B x₁ y₁ * B x₂ y₂ := by
  induction x₁ using induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [tw_add_left, map_add, LinearMap.add_apply, hx, hx', map_add,
      LinearMap.add_apply]; ring
  | smul_word u c =>
    induction x₂ using induction_linear with
    | zero => simp
    | add x x' hx hx' => rw [tw_add_right, map_add, LinearMap.add_apply, hx, hx', map_add B x,
        LinearMap.add_apply]; ring
    | smul_word u' c' =>
      rw [tw_smul_left, tw_smul_right, tw_word, TwistedMonoidAlgebra.smul_single,
        TwistedMonoidAlgebra.smul_single, pair_single_tw]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring

theorem pair_tw_single (x₁ x₂ : PreF K I) (c e : FreeMonoid I) (s : K) :
    pair B (tw dot v x₁ x₂) (single (c, e) s) = s * (B x₁ (word c) * B x₂ (word e)) := by
  rw [single_eq_smul_tw, map_smul, pair_tw_tw, smul_eq_mul]

theorem one_eq_tw : (1 : TwSq K I dot v) = tw dot v 1 1 := by
  rw [tw, map_one, map_one, one_mul]

theorem pair_flip (X Y : TwSq K I dot v) : pair B.flip X Y = pair B Y X := by
  induction X using TwistedMonoidAlgebra.induction_linear with
  | zero => simp
  | add X X' hX hX' => rw [map_add, LinearMap.add_apply, hX, hX', map_add]
  | single p r =>
    induction Y using TwistedMonoidAlgebra.induction_linear with
    | zero => simp
    | add Y Y' hY hY' => rw [map_add, hY, hY', map_add, LinearMap.add_apply]
    | single q s =>
      obtain ⟨a, b⟩ := p
      obtain ⟨c, e⟩ := q
      rw [pair_single_single, pair_single_single]
      simp only [LinearMap.flip_apply]
      ring

/-! ### The form -/

variable (dot v) (c : I → K)

/-- The functional `(w, -)` for a word `w` (given as a list), by recursion:
`(1, y) = ε(y)` and `(θ i u, y) = c i (u, d i y)`. -/
def formW : List I → (PreF K I →ₗ[K] K)
  | [] => counit
  | i :: u => c i • (formW u ∘ₗ d dot v i)

/-- Lusztig's bilinear form on `'f` (Lusztig 1.2.3; KL I §3.1) with `(θ i, θ i) = c i`. -/
def form : PreF K I →ₗ[K] PreF K I →ₗ[K] K :=
  linLift fun u => formW dot v c (FreeMonoid.toList u)

variable {dot v c}

theorem form_one (y : PreF K I) : form dot v c 1 y = counit y := by
  rw [← word_one, form, linLift_word]
  rfl

theorem form_θ_mul (i : I) (x y : PreF K I) :
    form dot v c (θ i * x) y = c i * form dot v c x (d dot v i y) := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [mul_add, map_add, LinearMap.add_apply, hx, hx', map_add,
      LinearMap.add_apply, mul_add]
  | smul_word w r =>
    rw [mul_smul_comm, map_smul, LinearMap.smul_apply, ← word_of_mul, form, linLift_word,
      map_smul, LinearMap.smul_apply, linLift_word, FreeMonoid.toList_of_mul, smul_eq_mul,
      smul_eq_mul]
    simp only [formW, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply, smul_eq_mul]
    ring

theorem form_one_one : form dot v c (1 : PreF K I) 1 = 1 := by
  rw [form_one, counit_one]

theorem form_θ (i : I) (y : PreF K I) :
    form dot v c (θ i) y = c i * counit (d dot v i y) := by
  rw [← mul_one (θ i), form_θ_mul, form_one]

theorem form_θ_θ (i j : I) :
    form dot v c (θ i : PreF K I) (θ j) = if i = j then c i else 0 := by
  rw [form_θ, d_θ]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-! ### Orthogonality of weight spaces -/

theorem form_word_apply_eq_zero (a : FreeMonoid I) :
    ∀ x ∈ (supp {w | wt w ≠ wt a} : Submodule K (PreF K I)), form dot v c (word a) x = 0 := by
  induction a using FreeMonoid.inductionOn' with
  | one =>
    refine eqOn_supp (form dot v c (word 1)) 0 ?_
    intro w hw
    simp only [Set.mem_setOf_eq, wt_one] at hw
    rw [word_one, form_one, counit_word, if_neg (by rintro rfl; exact hw rfl),
      LinearMap.zero_apply]
  | mul_of i a ih =>
    intro x hx
    rw [word_of_mul, form_θ_mul, ih, mul_zero]
    refine map_supp_le (d dot v i) ?_ x hx
    intro w hw
    refine supp_mono ?_ (d_word_mem_supp i w)
    intro w' hw'
    simp only [Set.mem_setOf_eq, wt_of_mul] at hw hw' ⊢
    rintro h
    exact hw (by rw [← hw', h])

/-- Distinct weight spaces are orthogonal. -/
theorem form_eq_zero_of_wt_ne {a b : FreeMonoid I} (h : wt a ≠ wt b) :
    form dot v c (word a : PreF K I) (word b) = 0 :=
  form_word_apply_eq_zero a _ (word_mem_supp (Ne.symm h))

/-! ### Property (c): `(x' x'', y) = (x' ⊗ x'', r y)` -/

theorem pair_tw_one_left (x : PreF K I) (Y : TwSq K I dot v) :
    pair (form dot v c) (tw dot v 1 x) Y = form dot v c x (E1 dot v Y) := by
  induction Y using TwistedMonoidAlgebra.induction_linear with
  | zero => simp
  | add Y Y' hY hY' => rw [map_add, hY, hY', map_add, map_add]
  | single p s =>
    obtain ⟨a, b⟩ := p
    rw [pair_tw_single, E1_single, form_one, counit_word, map_smul, smul_eq_mul]
    split_ifs <;> simp

theorem pair_tw_θ_mul_left (i : I) (x x'' : PreF K I) (Y : TwSq K I dot v) :
    pair (form dot v c) (tw dot v (θ i * x) x'') Y =
      c i * pair (form dot v c) (tw dot v x x'') (dL dot v i Y) := by
  induction Y using TwistedMonoidAlgebra.induction_linear with
  | zero => simp
  | add Y Y' hY hY' => rw [map_add, hY, hY', map_add, map_add, mul_add]
  | single p s =>
    obtain ⟨a, b⟩ := p
    rw [pair_tw_single, dL_single, map_smul, pair_tw_tw, form_θ_mul, smul_eq_mul]
    ring

/-- Lusztig 1.2.3(c) / KL I Prop. 3.3(4): `(x' x'', y) = (x' ⊗ x'', r y)`. -/
theorem form_mul_left (x' x'' y : PreF K I) :
    form dot v c (x' * x'') y = pair (form dot v c) (tw dot v x' x'') (r dot v y) := by
  induction x' using induction_linear generalizing x'' y with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, map_add, LinearMap.add_apply, hx, hx', tw_add_left, map_add,
      LinearMap.add_apply]
  | smul_word u s =>
    rw [smul_mul_assoc, map_smul, LinearMap.smul_apply, tw_smul_left, map_smul,
      LinearMap.smul_apply]
    congr 1
    induction u using FreeMonoid.inductionOn' generalizing x'' y with
    | one => rw [word_one, one_mul, pair_tw_one_left, E1_r]
    | mul_of i u ih =>
      rw [word_of_mul, mul_assoc, form_θ_mul, ih, r_d, pair_tw_θ_mul_left]

/-! ### Property (b): `(x, y' y'') = (r x, y' ⊗ y'')` -/

theorem counit_mul (x y : PreF K I) : counit (x * y) = counit x * counit y := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, add_mul]
  | smul_word u r =>
    induction y using induction_linear with
    | zero => simp
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add]
    | smul_word w s =>
      rw [smul_mul_smul_comm, ← word_mul, map_smul, map_smul, map_smul, counit_word, counit_word,
        counit_word, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      by_cases hu : u = 1
      · subst hu; simp
      · have : u * w ≠ 1 := by
          intro h
          have := congrArg FreeMonoid.length h
          simp only [FreeMonoid.length_mul, FreeMonoid.length_one, Nat.add_eq_zero_iff,
            FreeMonoid.length_eq_zero] at this
          exact hu this.1
        simp [hu, this]

theorem pair_gen_mul_tw (hdot : ∀ i j, dot i j = dot j i) (i : I) (a : FreeMonoid I)
    (y : PreF K I) (X : TwSq K I dot v) :
    pair (form dot v c) ((inl dot v (θ i) + inr dot v (θ i)) * X) (tw dot v (word a) y) =
      c i * (pair (form dot v c) X (tw dot v (d dot v i (word a)) y) +
        ((v ^ wdot dot (wt a) {i} : Kˣ) : K) *
          pair (form dot v c) X (tw dot v (word a) (d dot v i y))) := by
  induction X using TwistedMonoidAlgebra.induction_linear with
  | zero => simp
  | add X X' hX hX' =>
    simp only [mul_add, map_add, LinearMap.add_apply, hX, hX']
    ring
  | single p s =>
    obtain ⟨e, f⟩ := p
    rw [add_mul, inl_θ_mul_single, inr_θ_mul_single, map_add, LinearMap.add_apply,
      pair_single_tw, pair_single_tw, pair_single_tw, pair_single_tw, word_of_mul, word_of_mul,
      form_θ_mul, form_θ_mul]
    by_cases h : wt e = wt a
    · rw [h, wdot_comm dot hdot {i} (wt a)]
      ring
    · rw [form_eq_zero_of_wt_ne h]
      ring

/-- Lusztig 1.2.3(b) / KL I Prop. 3.3(3): `(x, y' y'') = (r x, y' ⊗ y'')`, for a symmetric
pairing `dot`. -/
theorem form_mul_right (hdot : ∀ i j, dot i j = dot j i) (x y' y'' : PreF K I) :
    form dot v c x (y' * y'') = pair (form dot v c) (r dot v x) (tw dot v y' y'') := by
  induction x using induction_linear generalizing y' y'' with
  | zero => simp
  | add x x' hx hx' => rw [map_add, LinearMap.add_apply, hx, hx', map_add, map_add,
      LinearMap.add_apply]
  | smul_word u s =>
    rw [map_smul, LinearMap.smul_apply, map_smul, map_smul, LinearMap.smul_apply]
    congr 1
    induction u using FreeMonoid.inductionOn' generalizing y' y'' with
    | one =>
      rw [word_one, form_one, map_one, one_eq_tw, pair_tw_tw, form_one, form_one, counit_mul]
    | mul_of i u ih =>
      induction y' using induction_linear with
      | zero => simp
      | add y y' hy hy' => rw [add_mul, map_add, hy, hy', tw_add_left, map_add]
      | smul_word a t =>
        rw [smul_mul_assoc, map_smul, tw_smul_left, map_smul]
        congr 1
        rw [word_of_mul, form_θ_mul, d_word_mul, map_add, map_smul, ih, ih, ← word_of_mul,
          r_word_of_mul, pair_gen_mul_tw hdot, smul_eq_mul]

/-! ### Uniqueness and symmetry -/

private theorem eq_zero_of_eq_two_mul {x : K} (h : x = x * 1 + 1 * x) : x = 0 := by
  linear_combination -h

section Unique

variable {B : PreF K I →ₗ[K] PreF K I →ₗ[K] K}

theorem unique_one_θ (h1 : B 1 1 = 1)
    (h3 : ∀ x' x'' y, B (x' * x'') y = pair B (tw dot v x' x'') (r dot v y)) (j : I) :
    B 1 (θ j) = 0 := by
  have := h3 1 1 (θ j)
  rw [one_mul, r_θ', map_add, pair_tw_tw, pair_tw_tw, h1] at this
  exact eq_zero_of_eq_two_mul this

theorem unique_one (h1 : B 1 1 = 1)
    (h3 : ∀ x' x'' y, B (x' * x'') y = pair B (tw dot v x' x'') (r dot v y))
    (h4 : ∀ x y' y'', B x (y' * y'') = pair B (r dot v x) (tw dot v y' y''))
    (y : PreF K I) : B 1 y = counit y := by
  induction y using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add]
  | smul_word w s =>
    rw [map_smul, map_smul]
    congr 1
    induction w using FreeMonoid.inductionOn' with
    | one => rw [word_one, h1, counit_one]
    | mul_of j w _ =>
      rw [word_of_mul, h4, map_one, one_eq_tw, pair_tw_tw, unique_one_θ h1 h3 j, zero_mul,
        counit_θ_mul]

theorem unique_θ (h1 : B 1 1 = 1) (h2 : ∀ i j, B (θ i) (θ j) = if i = j then c i else 0)
    (h3 : ∀ x' x'' y, B (x' * x'') y = pair B (tw dot v x' x'') (r dot v y))
    (h4 : ∀ x y' y'', B x (y' * y'') = pair B (r dot v x) (tw dot v y' y''))
    (i : I) (y : PreF K I) : B (θ i) y = c i * counit (d dot v i y) := by
  have hθ1 : B (θ i) 1 = 0 := by
    have := h4 (θ i) 1 1
    rw [one_mul, r_θ', map_add, LinearMap.add_apply, pair_tw_tw, pair_tw_tw, h1] at this
    exact eq_zero_of_eq_two_mul this
  induction y using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, mul_add]
  | smul_word w s =>
    rw [map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm]
    congr 1
    induction w using FreeMonoid.inductionOn' with
    | one => rw [word_one, hθ1, d_one, map_zero, mul_zero]
    | mul_of j w _ =>
      rw [word_of_mul, h4, r_θ', map_add, LinearMap.add_apply, pair_tw_tw, pair_tw_tw, h2,
        unique_one h1 h3 h4, unique_one_θ h1 h3 j, d_θ_mul, map_add, map_smul, counit_θ_mul,
        smul_zero, add_zero]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]

/-- Uniqueness in Lusztig 1.2.3: a bilinear form on `'f` satisfying `(1,1) = 1`,
`(θ i, θ j) = δ_{ij} c i` and properties (b), (c) is `form dot v c`. -/
theorem form_unique (h1 : B 1 1 = 1) (h2 : ∀ i j, B (θ i) (θ j) = if i = j then c i else 0)
    (h3 : ∀ x' x'' y, B (x' * x'') y = pair B (tw dot v x' x'') (r dot v y))
    (h4 : ∀ x y' y'', B x (y' * y'') = pair B (r dot v x) (tw dot v y' y'')) :
    B = form dot v c := by
  refine lhom_ext fun u => ?_
  refine LinearMap.ext fun y => ?_
  induction u using FreeMonoid.inductionOn' generalizing y with
  | one => rw [word_one, unique_one h1 h3 h4, form_one]
  | mul_of i u ih =>
    rw [word_of_mul, h3, form_mul_left]
    congr 1
    refine TwistedMonoidAlgebra.lhom_ext fun p => ?_
    obtain ⟨a, b⟩ := p
    rw [pair_tw_single, pair_tw_single, unique_θ h1 h2 h3 h4, form_θ, ih]

end Unique

/-- Lusztig 1.2.3: the form is symmetric (for a symmetric pairing `dot`). -/
theorem form_symm (hdot : ∀ i j, dot i j = dot j i) (x y : PreF K I) :
    form dot v c x y = form dot v c y x := by
  have : (form dot v c).flip = form dot v c := by
    refine form_unique (B := (form dot v c).flip) ?_ ?_ ?_ ?_
    · simp [form_one_one]
    · intro i j
      rw [LinearMap.flip_apply, form_θ_θ]
      by_cases h : i = j
      · subst h; rfl
      · simp [h, Ne.symm h]
    · intro x' x'' y
      rw [LinearMap.flip_apply, form_mul_right hdot, pair_flip]
    · intro x y' y''
      rw [LinearMap.flip_apply, form_mul_left, pair_flip]
  rw [← this, LinearMap.flip_apply, this]

/-- **Lusztig, Proposition 1.2.3** (KL I §3.1): for a symmetric pairing `dot` and any values
`c i ∈ K`, there is a unique bilinear form `B` on `'f` such that `B(1,1) = 1`,
`B(θ i, θ j) = δ_{ij} c i`, `B(x, y'y'') = B(r x, y' ⊗ y'')` and
`B(x'x'', y) = B(x' ⊗ x'', r y)`. It is `form dot v c`, and it is symmetric. -/
theorem existsUnique_form (hdot : ∀ i j, dot i j = dot j i) :
    ∃! B : PreF K I →ₗ[K] PreF K I →ₗ[K] K,
      B 1 1 = 1 ∧ (∀ i j, B (θ i) (θ j) = if i = j then c i else 0) ∧
      (∀ x y' y'', B x (y' * y'') = pair B (r dot v x) (tw dot v y' y'')) ∧
      (∀ x' x'' y, B (x' * x'') y = pair B (tw dot v x' x'') (r dot v y)) :=
  ⟨form dot v c, ⟨form_one_one, form_θ_θ, form_mul_right hdot, form_mul_left⟩,
    fun _ ⟨h1, h2, h4, h3⟩ => form_unique h1 h2 h3 h4⟩

end PreF

end Categorification.QuantumGroup

end
