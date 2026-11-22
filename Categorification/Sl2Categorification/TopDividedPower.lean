/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Sl2Categorification.DividedPowers

/-!
# The top divided power of a lowest-weight simple object

Chuang–Rouquier, arXiv:math/0407205v2, Proposition 5.20 (a), in the case `F S = 0`: for a
simple object `S` of a weak `𝔰𝔩₂`-categorification with nilHecke actions on `E` and `F`, if
`F S = 0` and `n = h₊([S])` is the length of the `e`-string through `[S]`, then `E^{(n)} S` is
simple.

The argument is a class computation. By Lemma 4.3 (3), `eⁿ [S] = α [T]` for a simple `T` with
`E T = 0` and some `α > 0`, and `fⁿ [T] = ((n!)² / α) [S]`. Lemma 5.13 gives
`[Eⁿ S] = n! [E^{(n)} S]` and `[Fⁿ T] = n! [F^{(n)} T]`; the two coefficients `α / n!` and
`n! / α` are natural numbers (multiplicities of composition factors), so both equal `1` and
`[E^{(n)} S] = [T]`. An object whose class is a basis vector is simple.

## Main results

* `K0Data.simple_of_cls_eq_basis`: an object whose class is the class of a simple object is
  simple.
* `WeakSl2.simple_divObj_top_of_F_eq_zero`: **Chuang–Rouquier, Proposition 5.20 (a)**, case
  `F S = 0`.
-/

namespace Categorification.Sl2

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace K0Data

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V] (K : K0Data C ι V)

/-- A nonzero object has a composition factor. -/
lemma exists_repr_pos_of_not_isZero [∀ X : C, IsArtinianObject X] {X : C} (hX : ¬IsZero X) :
    ∃ j, 0 < K.B.repr (K.cls X) j :=
  ⟨_, K.repr_cls_pos_of_mono_of_epi (𝟙 X) (simpleSubobjectArrow hX)⟩

/-- The class of an object under a functor whose class map is `φ`, iterated. -/
lemma cls_Epow_obj {F : C ⥤ C} {φ : Module.End ℚ V} (hF : ∀ X, K.cls (F.obj X) = φ (K.cls X))
    (n : ℕ) (M : C) : K.cls ((Epow F n).obj M) = (φ ^ n) (K.cls M) := by
  induction n with
  | zero => simp [Epow]
  | succ n ih =>
    change K.cls (F.obj ((Epow F n).obj M)) = _
    rw [hF, ih, pow_succ', Module.End.mul_apply]

/-- A nonzero object whose class is supported on `B c` has coordinate at least `1` there. -/
lemma one_le_repr_of_not_isZero [∀ X : C, IsArtinianObject X] {Y : C} (hY : ¬IsZero Y) {c : ι}
    (h : ∀ j, j ≠ c → K.B.repr (K.cls Y) j = 0) : 1 ≤ K.B.repr (K.cls Y) c := by
  obtain ⟨j, hj⟩ := K.exists_repr_pos_of_not_isZero hY
  have hjc : j = c := by
    by_contra hjc
    rw [h j hjc] at hj
    exact lt_irrefl _ hj
  subst hjc
  obtain ⟨m, hm⟩ := K.cls_int Y j
  rw [hm] at hj ⊢
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hj)

/-- If the class of `X` is a basis vector `B c`, then `X` is simple. -/
theorem simple_of_cls_eq_basis [∀ X : C, IsArtinianObject X] {X : C} {c : ι}
    (h : K.cls X = K.B c) : Simple X := by
  classical
  have hX : ¬IsZero X := by
    intro hz
    have := K.cls_eq_zero_of_isZero hz
    rw [h] at this
    exact K.B.ne_zero c this
  have hXc : ∀ j, K.B.repr (K.cls X) j = if j = c then 1 else 0 := by
    intro j
    rw [h, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hj : j = c
    · simp [hj]
    · simp [hj, Ne.symm hj]
  refine ⟨fun {Y} f _ ↦ ⟨fun hiso h0 ↦ hX ?_, fun hf ↦ ?_⟩⟩
  · subst h0
    rw [IsZero.iff_id_eq_zero, ← IsIso.inv_hom_id (0 : Y ⟶ X), comp_zero]
  · have hadd := K.cls_add_of_mono f
    have hcoord : ∀ j, K.B.repr (K.cls X) j =
        K.B.repr (K.cls Y) j + K.B.repr (K.cls (cokernel f)) j := by
      intro j; rw [hadd, map_add, Finsupp.add_apply]
    have hY0 : ∀ j, j ≠ c → K.B.repr (K.cls Y) j = 0 := by
      intro j hj
      have h1 := hcoord j
      simp only [hXc, hj, ↓reduceIte] at h1
      have := K.cls_mem_cone Y j
      have := K.cls_mem_cone (cokernel f) j
      linarith
    have hQ0 : ∀ j, j ≠ c → K.B.repr (K.cls (cokernel f)) j = 0 := by
      intro j hj
      have h1 := hcoord j
      simp only [hXc, hj, ↓reduceIte] at h1
      have := K.cls_mem_cone Y j
      have := K.cls_mem_cone (cokernel f) j
      linarith
    have hYnz : ¬IsZero Y := fun hz ↦ hf (hz.eq_of_src f 0)
    have hY1 := K.one_le_repr_of_not_isZero hYnz hY0
    have hQ : IsZero (cokernel f) := by
      by_contra hQ
      have hQ1 := K.one_le_repr_of_not_isZero hQ hQ0
      have h1 := hcoord c
      simp only [hXc, ↓reduceIte] at h1
      linarith
    have : Epi f := Preadditive.epi_of_isZero_cokernel f hQ
    exact isIso_of_mono_of_epi f

end K0Data

namespace WeakSl2

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V] (A : WeakSl2 C ι V)
variable [A.E.Additive] [A.F.Additive] (DE : NilHeckeData A.E)
variable (k : Type*) [CommRing k] [IsDomain k] [Linear k C]

/-- **Chuang–Rouquier, Proposition 5.20 (a)**, case `F S = 0`: if `S` is simple and `F S = 0`,
then the top divided power `E^{(n)} S`, `n = h₊([S])`, is simple. -/
theorem simple_divObj_top_of_F_eq_zero [∀ X : C, IsArtinianObject X] (DF : NilHeckeData A.F)
    {S : C} (hS : Simple S) (hFS : IsZero (A.F.obj S)) :
    Simple (DE.divObj k (hPlus A.e (A.cls S)) S) := by
  classical
  have hclsS : A.cls S = A.B (A.idx S hS) := A.cls_simple S hS
  set b := A.idx S hS
  have hfb : A.f (A.B b) = 0 := by
    rw [← hclsS, ← A.cls_F]; exact A.toK0Data.cls_eq_zero_of_isZero hFS
  obtain ⟨c, -, α, hα, htop⟩ := A.posBasis.exists_top_eq_smul hfb
  rw [hclsS]
  set n := hPlus A.e (A.B b)
  have hn : (0 : ℚ) < n.factorial := by exact_mod_cast n.factorial_pos
  -- the class of `X = E^{(n)} S`
  have hX : A.cls (DE.divObj k n S) = (α / n.factorial) • A.B c := by
    have h1 := DE.cls_Epow k A.toK0Data n S
    rw [A.toK0Data.cls_Epow_obj A.cls_E, hclsS, htop, ← Nat.cast_smul_eq_nsmul ℚ] at h1
    rw [div_eq_inv_mul, ← smul_smul, h1, smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
  -- the class of `Y = F^{(n)} T` for the simple `T` of class `B c`
  have hT : A.cls (A.simple c) = A.B c := by rw [A.cls_simple _ (A.simple_simple c), A.idx_simple]
  have hfe := pow_f_pow_e_eq A.sl2 hfb (A.posBasis.hOp_of_f_eq_zero hfb) (le_refl n)
  rw [Nat.descFactorial_self, htop, map_smul] at hfe
  have hY : A.cls (DF.divObj k n (A.simple c)) = (n.factorial / α) • A.B b := by
    have h1 := DF.cls_Epow k A.toK0Data n (A.simple c)
    rw [A.toK0Data.cls_Epow_obj A.cls_F, hT, ← Nat.cast_smul_eq_nsmul ℚ] at h1
    have h2 : (A.f ^ n) (A.B c) = ((n.factorial * n.factorial : ℕ) / α : ℚ) • A.B b := by
      rw [div_eq_inv_mul, ← smul_smul, ← hfe, smul_smul, inv_mul_cancel₀ hα.ne', one_smul]
    rw [h2] at h1
    have h3 : A.cls (DF.divObj k n (A.simple c)) =
        (n.factorial : ℚ)⁻¹ • ((n.factorial * n.factorial : ℕ) / α : ℚ) • A.B b := by
      rw [h1, smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
    rw [h3, smul_smul]
    congr 1
    push_cast
    field_simp
  -- both coefficients are natural numbers, so both are `1`
  obtain ⟨m, hm⟩ := A.cls_int (DE.divObj k n S) c
  obtain ⟨m', hm'⟩ := A.cls_int (DF.divObj k n (A.simple c)) b
  rw [hX] at hm
  rw [hY] at hm'
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] at hm hm'
  have hmm : ((m * m' : ℕ) : ℚ) = 1 := by
    push_cast
    rw [← hm, ← hm']
    field_simp
  have hm1 : m = 1 := Nat.eq_one_of_mul_eq_one_right (by exact_mod_cast hmm)
  refine A.toK0Data.simple_of_cls_eq_basis (c := c) ?_
  rw [hX, hm, hm1, Nat.cast_one, one_smul]

end WeakSl2

end Categorification.Sl2
