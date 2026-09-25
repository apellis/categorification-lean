/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.Form

/-!
# The algebra `f = 'f / ℐ` and the quantum Serre relations

Lusztig, *Introduction to quantum groups*, 1.2.4–1.2.5 and 1.4.3; Khovanov–Lauda,
arXiv:0803.4121v2, §3.1:

* the radical `ℐ` of the bilinear form `( , )` on `'f` is a two-sided ideal
  (`PreF.radical`, with `Ideal.IsTwoSided` instance);
* `f = 'f / ℐ` (`PreF.F`, with the quotient map `PreF.π : 'f →ₐ[K] f`);
* the form descends to a nondegenerate symmetric form on `f` (`PreF.formF`,
  `PreF.formF_nondegenerate`);
* the quantum Serre relations hold in `f` in the simply-laced cases:
  `θ i θ j = θ j θ i` if `i · j = 0` (`PreF.serreComm_mem_radical`), and
  `θ i² θ j - (v + v⁻¹) θ i θ j θ i + θ j θ i² = 0` if `i · i = 2`, `i · j = -1`
  (`PreF.serreCubic_mem_radical`). These are exactly the relations listed in KL I §1 and
  §3.1 (where KL write `(q + q⁻¹)θ_iθ_jθ_i = θ_i²θ_j + θ_jθ_i²`; KL's display
  "`θ_iθ_j − θ_iθ_j` for `i·j = 0`" in §3.1 is a typo for `θ_iθ_j − θ_jθ_i`).

The method is Lusztig's (1.4.3 / 1.2.13): an element of positive weight killed by every
`d k` lies in the radical (`PreF.mem_radical_of_d`).

The converse, that `ℐ` is *generated* by the Serre elements (the quantum Gabber–Kac
theorem, Lusztig 33.1.3, used in KL I §3.1 for the injectivity of `γ`), is **not** proved
here. It is recorded as the proposition `PreF.GabberKac`, to be used only as an explicit
hypothesis.
-/

noncomputable section

namespace Categorification.QuantumGroup

open TwistedMonoidAlgebra (single)
open scoped Classical

namespace PreF

variable {I : Type*} {K : Type*} [CommRing K] {dot : I → I → ℤ} {v : Kˣ} {c : I → K}

theorem pair_tw_eq_zero_of_left {x : PreF K I} (hx : ∀ y, form dot v c x y = 0) (z : PreF K I)
    (Y : TwSq K I dot v) : pair (form dot v c) (tw dot v x z) Y = 0 := by
  induction Y using TwistedMonoidAlgebra.induction_linear with
  | zero => simp
  | add Y Y' hY hY' => rw [map_add, hY, hY', add_zero]
  | single p s =>
    obtain ⟨a, b⟩ := p
    rw [pair_tw_single, hx, zero_mul, mul_zero]

theorem pair_tw_eq_zero_of_right {x : PreF K I} (hx : ∀ y, form dot v c x y = 0) (z : PreF K I)
    (Y : TwSq K I dot v) : pair (form dot v c) (tw dot v z x) Y = 0 := by
  induction Y using TwistedMonoidAlgebra.induction_linear with
  | zero => simp
  | add Y Y' hY hY' => rw [map_add, hY, hY', add_zero]
  | single p s =>
    obtain ⟨a, b⟩ := p
    rw [pair_tw_single, hx, mul_zero, mul_zero]

variable (dot v c) in
/-- The radical `ℐ = {x | (x, y) = 0 for all y}` of the bilinear form on `'f`
(Lusztig 1.2.4; KL I §3.1). It is a two-sided ideal. -/
def radical : Ideal (PreF K I) where
  carrier := {x | ∀ y, form dot v c x y = 0}
  add_mem' hx hy y := by simp [hx y, hy y]
  zero_mem' y := by simp
  smul_mem' z x hx y := by
    rw [smul_eq_mul, form_mul_left, pair_tw_eq_zero_of_right hx]

theorem mem_radical {x : PreF K I} : x ∈ radical dot v c ↔ ∀ y, form dot v c x y = 0 := Iff.rfl

instance radical_isTwoSided : (radical dot v c).IsTwoSided :=
  ⟨fun z hx y => by rw [form_mul_left, pair_tw_eq_zero_of_left hx]⟩

/-- For symmetric `dot` the left and right radicals agree. -/
theorem mem_radical_iff' (hdot : ∀ i j, dot i j = dot j i) {x : PreF K I} :
    x ∈ radical dot v c ↔ ∀ y, form dot v c y x = 0 := by
  simp only [mem_radical, form_symm hdot _ x]

variable (dot v c) in
/-- Lusztig's algebra `f = 'f / ℐ` (Lusztig 1.2.5; KL I §3.1). -/
def F : Type _ := PreF K I ⧸ radical dot v c

instance instRingF : Ring (F dot v c) := Ideal.Quotient.ring _

instance instAlgebraF : Algebra K (F dot v c) := Ideal.Quotient.algebra K

variable (dot v c) in
/-- The quotient map `'f → f`. -/
def π : PreF K I →ₐ[K] F dot v c := Ideal.Quotient.mkₐ K (radical dot v c)

theorem π_apply (x : PreF K I) :
    π dot v c x = (Ideal.Quotient.mk (radical dot v c) x : PreF K I ⧸ radical dot v c) := rfl

theorem π_surjective : Function.Surjective (π dot v c) := Ideal.Quotient.mk_surjective

theorem π_eq_zero_iff {x : PreF K I} : π dot v c x = 0 ↔ x ∈ radical dot v c :=
  Ideal.Quotient.eq_zero_iff_mem

theorem π_eq_π_iff {x y : PreF K I} : π dot v c x = π dot v c y ↔ x - y ∈ radical dot v c := by
  rw [← sub_eq_zero, ← map_sub, π_eq_zero_iff]

/-! ### The descended form -/

variable (dot v c) in
/-- The bilinear form on `f` induced by `( , )` (Lusztig 1.2.5). -/
def formF (hdot : ∀ i j, dot i j = dot j i) (x y : F dot v c) : K :=
  Quotient.liftOn₂' x y (fun a b => form dot v c a b) fun a₁ b₁ a₂ b₂ ha hb => by
    have ha' : a₁ - a₂ ∈ radical dot v c := (Submodule.quotientRel_def _).1 ha
    have hb' : b₁ - b₂ ∈ radical dot v c := (Submodule.quotientRel_def _).1 hb
    have e1 := ha' b₁
    have e2 := (mem_radical_iff' hdot).1 hb' a₂
    simp only [map_sub, LinearMap.sub_apply, sub_eq_zero] at e1 e2
    exact e1.trans e2

theorem formF_π (hdot : ∀ i j, dot i j = dot j i) (x y : PreF K I) :
    formF dot v c hdot (π dot v c x) (π dot v c y) = form dot v c x y := rfl

theorem formF_symm (hdot : ∀ i j, dot i j = dot j i) (x y : F dot v c) :
    formF dot v c hdot x y = formF dot v c hdot y x := by
  obtain ⟨a, rfl⟩ := π_surjective (dot := dot) (v := v) (c := c) x
  obtain ⟨b, rfl⟩ := π_surjective (dot := dot) (v := v) (c := c) y
  rw [formF_π, formF_π, form_symm hdot]

/-- The form on `f` is nondegenerate (Lusztig 1.2.5; used in KL I §3.1). -/
theorem formF_nondegenerate (hdot : ∀ i j, dot i j = dot j i) {x : F dot v c}
    (hx : ∀ y, formF dot v c hdot x y = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := π_surjective (dot := dot) (v := v) (c := c) x
  rw [π_eq_zero_iff]
  intro y
  rw [← formF_π hdot]
  exact hx _

/-! ### A criterion for membership in the radical -/

/-- An element with no constant term all of whose derivatives `d k x` lie in the radical lies
in the radical (compare Lusztig 1.2.15, 1.4.3). -/
theorem mem_radical_of_d (hdot : ∀ i j, dot i j = dot j i) {x : PreF K I}
    (h0 : counit x = 0) (hd : ∀ k, d dot v k x ∈ radical dot v c) : x ∈ radical dot v c := by
  rw [mem_radical_iff' hdot]
  suffices (form dot v c).flip x = 0 from fun y => LinearMap.congr_fun this y
  refine lhom_ext fun u => ?_
  rw [LinearMap.flip_apply, LinearMap.zero_apply]
  induction u using FreeMonoid.inductionOn' with
  | one => rw [word_one, form_one, h0]
  | mul_of k u _ =>
    rw [word_of_mul, form_θ_mul, form_symm hdot, hd k, mul_zero]

/-! ### The quantum Serre relations (simply-laced case) -/

/-- The Serre element `θ i θ j - θ j θ i` (for `i · j = 0`). -/
def serreComm (i j : I) : PreF K I := θ i * θ j - θ j * θ i

variable (v) in
/-- The Serre element `θ i² θ j - (v + v⁻¹) θ i θ j θ i + θ j θ i²` (for `i · i = 2`,
`i · j = -1`; Lusztig 1.4.3 with `a_{ij} = -1`, KL I §1). -/
def serreCubic (i j : I) : PreF K I :=
  θ i * (θ i * θ j) - ((v : K) + ((v⁻¹ : Kˣ) : K)) • (θ i * (θ j * θ i)) + θ j * (θ i * θ i)

theorem serreCubic_eq (i j : I) :
    (serreCubic v i j : PreF K I) =
      θ i ^ 2 * θ j - ((v : K) + ((v⁻¹ : Kˣ) : K)) • (θ i * θ j * θ i) + θ j * θ i ^ 2 := by
  simp [serreCubic, pow_two, mul_assoc]

theorem d_θ_mul_θ (k i j : I) :
    d dot v k (θ i * θ j : PreF K I) =
      (if i = k then θ j else 0) + ((v ^ dot i k : Kˣ) : K) • (if j = k then θ i else 0) := by
  rw [d_θ_mul, d_θ]
  split_ifs <;> simp

/-- Lusztig 1.4.3 (simply-laced, `i · j = 0`): `θ i θ j - θ j θ i ∈ ℐ`. -/
theorem serreComm_mem_radical (hdot : ∀ i j, dot i j = dot j i) {i j : I} (hij : i ≠ j)
    (h0 : dot i j = 0) : serreComm i j ∈ radical dot v c := by
  refine mem_radical_of_d hdot ?_ fun k => ?_
  · simp [serreComm, counit_θ_mul]
  · have : d dot v k (serreComm i j : PreF K I) = 0 := by
      rw [serreComm, map_sub, d_θ_mul_θ, d_θ_mul_θ]
      by_cases hki : i = k
      · subst hki; simp [hij, Ne.symm hij, hdot j i, h0]
      · by_cases hkj : j = k
        · subst hkj; simp [hki, h0]
        · simp [hki, hkj]
    rw [this]
    exact Submodule.zero_mem _

/-- Lusztig 1.4.3 (simply-laced, `i · j = -1`):
`θ i² θ j - (v + v⁻¹) θ i θ j θ i + θ j θ i² ∈ ℐ`. -/
theorem serreCubic_mem_radical (hdot : ∀ i j, dot i j = dot j i) {i j : I} (hij : i ≠ j)
    (hii : dot i i = 2) (h1 : dot i j = -1) : serreCubic v i j ∈ radical dot v c := by
  have h1' : dot j i = -1 := by rw [hdot, h1]
  have hvv : (v : K) * ((v⁻¹ : Kˣ) : K) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine mem_radical_of_d hdot ?_ fun k => ?_
  · simp [serreCubic, counit_θ_mul]
  · have : d dot v k (serreCubic v i j : PreF K I) = 0 := by
      simp only [serreCubic, map_add, map_sub, map_smul, d_θ_mul, d_θ]
      by_cases hki : i = k
      · subst hki
        simp only [hii, h1', if_true, if_neg (Ne.symm hij), smul_zero, add_zero, zero_add,
          mul_zero, mul_one, zpow_neg, zpow_one, zpow_ofNat, Units.val_pow_eq_pow_val, pow_one,
          mul_smul_comm, mul_add, smul_add]
        linear_combination (norm := module)
          (-(((v : K) * ((v⁻¹ : Kˣ) : K)) + 1) - (v : K) ^ 2) • hvv • (θ i * θ j : PreF K I) +
            (v : K) • hvv • (θ j * θ i : PreF K I)
      · by_cases hkj : j = k
        · subst hkj
          simp only [hki, h1, if_true, if_false, smul_zero, add_zero, zero_add, mul_zero,
            mul_one, zpow_neg, zpow_one, hii, zpow_ofNat, if_neg hij, Units.val_pow_eq_pow_val,
            pow_one, mul_smul_comm]
          linear_combination (norm := module) (-1 : K) • hvv • (θ i * θ i : PreF K I)
        · simp [hki, hkj]
    rw [this]
    exact Submodule.zero_mem _

/-! ### The quantum Gabber–Kac theorem (statement only) -/

variable (dot v) in
/-- The simply-laced Serre elements: `θ i θ j - θ j θ i` for `i ≠ j`, `i · j = 0`, and
`θ i² θ j - (v + v⁻¹) θ i θ j θ i + θ j θ i²` for `i ≠ j`, `i · j = -1`. -/
def serreSet : Set (PreF K I) :=
  {x | ∃ i j, i ≠ j ∧ dot i j = 0 ∧ x = serreComm i j} ∪
    {x | ∃ i j, i ≠ j ∧ dot i j = -1 ∧ x = serreCubic v i j}

variable (dot v c) in
/-- **Statement only (not proved here).** The quantum Gabber–Kac theorem (Lusztig 33.1.3,
cited in KL I §3.1) for a simply-laced pairing: the radical `ℐ` is the two-sided ideal
generated by the Serre elements `serreSet dot v`. This is a deep theorem; it must only ever be
used as an explicit hypothesis. -/
def GabberKac : Prop :=
  radical dot v c = TwoSidedIdeal.asIdeal (TwoSidedIdeal.span (serreSet dot v))

/-- The inclusion `⊇` of the Gabber–Kac theorem, which is the part proved here (for a
simply-laced pairing with `i · i = 2`): the two-sided ideal generated by the Serre elements lies
in `ℐ`. -/
theorem span_serre_le_radical (hdot : ∀ i j, dot i j = dot j i) (hii : ∀ i, dot i i = 2) :
    TwoSidedIdeal.asIdeal (TwoSidedIdeal.span (serreSet dot v)) ≤ radical dot v c := by
  have h : TwoSidedIdeal.span (serreSet dot v) ≤ (radical dot v c).toTwoSided := by
    rw [TwoSidedIdeal.span_le]
    rintro x (⟨i, j, hij, h0, rfl⟩ | ⟨i, j, hij, h1, rfl⟩)
    · exact Ideal.mem_toTwoSided.2 (serreComm_mem_radical hdot hij h0)
    · exact Ideal.mem_toTwoSided.2 (serreCubic_mem_radical hdot hij (hii i) h1)
  intro x hx
  exact Ideal.mem_toTwoSided.1 (h (TwoSidedIdeal.mem_asIdeal.1 hx))

/-- Under the Gabber–Kac hypothesis, `f` is the quotient of `'f` by the Serre relations. -/
theorem π_eq_zero_iff_of_gabberKac (hGK : GabberKac dot v c) {x : PreF K I} :
    π dot v c x = 0 ↔ x ∈ TwoSidedIdeal.span (serreSet dot v) := by
  rw [π_eq_zero_iff, hGK, TwoSidedIdeal.mem_asIdeal]

end PreF

end Categorification.QuantumGroup

end
