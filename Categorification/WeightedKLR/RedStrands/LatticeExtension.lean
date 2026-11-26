/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Prop318
import LieLean.Algebra.QuantumGroup.LusztigF.IntegralForm

/-!
# Extending maps from a spanning `ℤ[q, q⁻¹]`-lattice

Let `V` be a vector space over `ℚ(v)`, with `ℤ[q, q⁻¹]` acting through `q ↦ v`
(`LusztigF.integralLaurentEval`), and let `L ⊆ V` be a `ℤ[q, q⁻¹]`-submodule whose `ℚ(v)`-span
is `V`. Since `ℚ(v)` is the fraction field of `ℤ[q, q⁻¹]` (`KLGamma.exists_eq_laurentEval_div`),
every vector has a nonzero Laurent polynomial multiple in `L`. An additive map from `L` to a
`ℚ(v)`-vector space that is linear along `q ↦ v` therefore extends uniquely to a `ℚ(v)`-linear map
on `V`.

This is used to read Webster's classes in `K₀` (arXiv:1309.3796v2, Theorem 4.38) as linear
functionals on the rational tensor product.

## Main results

* `Lattice.exists_eval_mul_eq`: every element of `ℚ(v)` is `a(v) / b(v)` with `b ≠ 0`.
* `Lattice.exists_eval_smul_mem`: every vector of `V` has a nonzero multiple in `L`.
* `Lattice.extend`, `Lattice.extend_apply`, `Lattice.extend_unique`.
-/

noncomputable section

namespace Categorification.Stendhal.Lattice

open LusztigF

local notation "𝕂" => RatFunc ℚ
local notation "LP" => LaurentPolynomial ℤ
local notation "ev" => integralLaurentEval
local notation "QVQ" => Categorification.QuantumGroup.vQ

theorem integralLaurentEval_eq_laurentEval :
    integralLaurentEval = Categorification.QuantumGroup.laurentEval QVQ := by
  refine RingHom.ext fun p ↦ ?_
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | C_mul_T n a =>
    rw [map_mul, map_mul, Categorification.KLR.KLGamma.laurentEval_C, integralLaurentEval_T,
      Categorification.QuantumGroup.laurentEval_T, integralLaurentEval, LaurentPolynomial.eval₂_C]
    simp [Categorification.QuantumGroup.vQ_val]

/-- Every element of `ℚ(v)` is a quotient of two Laurent polynomials in `v`. -/
theorem exists_eval_mul_eq (z : 𝕂) : ∃ a b : LP, b ≠ 0 ∧ z * ev b = ev a := by
  obtain ⟨x, y, hz⟩ := Categorification.KLR.KLGamma.exists_eq_laurentEval_div z
  rw [← integralLaurentEval_eq_laurentEval] at hz
  by_cases hy : ev y = 0
  · exact ⟨0, 1, one_ne_zero, by rw [hz, hy, div_zero, zero_mul, map_zero]⟩
  · refine ⟨x, y, fun h ↦ hy (by rw [h, map_zero]), ?_⟩
    rw [hz, div_mul_cancel₀ _ hy]

theorem eval_ne_zero {b : LP} (hb : b ≠ 0) : ev b ≠ 0 :=
  fun h ↦ hb (integralLaurentEval_injective (by rw [h, map_zero]))

variable {V W : Type*} [AddCommGroup V] [Module 𝕂 V] [AddCommGroup W] [Module 𝕂 W]

/-- A `ℤ[q, q⁻¹]`-lattice of a `ℚ(v)`-vector space: an additive subgroup closed under the
action of `ℤ[q, q⁻¹]` through `q ↦ v`. -/
structure IsLattice (L : AddSubgroup V) : Prop where
  smul_mem : ∀ (a : LP) {x : V}, x ∈ L → ev a • x ∈ L
  span_eq : Submodule.span 𝕂 (L : Set V) = ⊤

variable {L : AddSubgroup V} (hL : IsLattice L)
include hL

/-- Every vector has a nonzero Laurent polynomial multiple in the lattice. -/
theorem exists_eval_smul_mem (x : V) : ∃ b : LP, b ≠ 0 ∧ ev b • x ∈ L := by
  have hx : x ∈ Submodule.span 𝕂 (L : Set V) := by rw [hL.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rwa [map_one, one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨b, hb, hby⟩ := hy
    obtain ⟨c, hc, hcz⟩ := hz
    refine ⟨c * b, mul_ne_zero hc hb, ?_⟩
    rw [smul_add, map_mul, mul_smul, mul_comm, mul_smul]
    exact L.add_mem (hL.smul_mem c hby) (hL.smul_mem b hcz)
  | smul c y _ hy =>
    obtain ⟨b, hb, hby⟩ := hy
    obtain ⟨a', b', hb', hc⟩ := exists_eval_mul_eq c
    refine ⟨b' * b, mul_ne_zero hb' hb, ?_⟩
    rw [map_mul, mul_smul, smul_smul, smul_smul, show ev b' * ev b * c = ev a' * ev b by
      rw [← hc]; ring, ← smul_smul]
    exact hL.smul_mem a' hby

variable (g : L →+ W) (hg : ∀ (a : LP) (x : V) (hx : x ∈ L),
  g ⟨ev a • x, hL.smul_mem a hx⟩ = ev a • g ⟨x, hx⟩)
include hg

private theorem extend_wd (x : V) {b c : LP} (hb : b ≠ 0) (hc : c ≠ 0) (hbx : ev b • x ∈ L)
    (hcx : ev c • x ∈ L) :
    (ev b)⁻¹ • g ⟨ev b • x, hbx⟩ = (ev c)⁻¹ • g ⟨ev c • x, hcx⟩ := by
  have h₁ := hg c _ hbx
  have h₂ := hg b _ hcx
  have he : ev c • ev b • x = ev b • ev c • x := smul_comm _ _ _
  have h₃ : g ⟨ev c • ev b • x, hL.smul_mem c hbx⟩ = g ⟨ev b • ev c • x, hL.smul_mem b hcx⟩ :=
    congrArg g (Subtype.ext he)
  rw [h₁, h₂] at h₃
  have hb' := eval_ne_zero hb
  have hc' := eval_ne_zero hc
  rw [inv_smul_eq_iff₀ hb', smul_comm (ev b) (ev c)⁻¹, ← h₃, inv_smul_smul₀ hc']

/-- The `ℚ(v)`-linear extension of a map defined on a spanning lattice. -/
def extend : V →ₗ[𝕂] W where
  toFun x := (ev (exists_eval_smul_mem hL x).choose)⁻¹ •
    g ⟨_, (exists_eval_smul_mem hL x).choose_spec.2⟩
  map_add' x y := by
    obtain ⟨b, hb, hbx⟩ := exists_eval_smul_mem hL x
    obtain ⟨c, hc, hcy⟩ := exists_eval_smul_mem hL y
    have hxy : ev (c * b) • (x + y) ∈ L := by
      rw [smul_add, map_mul, mul_smul, mul_comm, mul_smul]
      exact L.add_mem (hL.smul_mem c hbx) (hL.smul_mem b hcy)
    rw [extend_wd hL g hg (x + y) (exists_eval_smul_mem hL _).choose_spec.1 (mul_ne_zero hc hb)
        _ hxy, extend_wd hL g hg x (exists_eval_smul_mem hL _).choose_spec.1 hb _ hbx,
      extend_wd hL g hg y (exists_eval_smul_mem hL _).choose_spec.1 hc _ hcy]
    have hsplit : (⟨ev (c * b) • (x + y), hxy⟩ : L) =
        ⟨ev c • ev b • x, hL.smul_mem c hbx⟩ + ⟨ev b • ev c • y, hL.smul_mem b hcy⟩ := by
      apply Subtype.ext
      simp only [AddSubgroup.coe_add, map_mul, smul_add, mul_smul]
      rw [smul_comm (ev c) (ev b) y]
    rw [hsplit, map_add, hg c _ hbx, hg b _ hcy, smul_add, map_mul, mul_inv]
    have hb' := eval_ne_zero hb
    have hc' := eval_ne_zero hc
    simp only [smul_smul]
    congr 1 <;> congr 1 <;> field_simp
  map_smul' r x := by
    obtain ⟨b, hb, hbx⟩ := exists_eval_smul_mem hL x
    obtain ⟨a', b', hb', hr⟩ := exists_eval_mul_eq r
    have hrx : ev (b' * b) • (r • x) ∈ L := by
      rw [map_mul, mul_smul, smul_smul, smul_smul, show ev b' * ev b * r = ev a' * ev b by
        rw [← hr]; ring, ← smul_smul]
      exact hL.smul_mem a' hbx
    simp only [RingHom.id_apply]
    rw [extend_wd hL g hg (r • x) (exists_eval_smul_mem hL _).choose_spec.1 (mul_ne_zero hb' hb)
        _ hrx, extend_wd hL g hg x (exists_eval_smul_mem hL _).choose_spec.1 hb _ hbx]
    have hrw : (⟨ev (b' * b) • (r • x), hrx⟩ : L) = ⟨ev a' • ev b • x, hL.smul_mem a' hbx⟩ := by
      apply Subtype.ext
      change ev (b' * b) • (r • x) = ev a' • ev b • x
      rw [map_mul, mul_smul, smul_smul, smul_smul, show ev b' * ev b * r = ev a' * ev b by
        rw [← hr]; ring, ← smul_smul]
    rw [hrw, hg a' _ hbx, ← hr, map_mul, mul_inv]
    have hb'0 := eval_ne_zero hb'
    simp only [smul_smul]
    congr 1
    field_simp

/-- The extension agrees with the given map on the lattice. -/
theorem extend_apply {x : V} (hx : x ∈ L) : extend hL g hg x = g ⟨x, hx⟩ := by
  change (ev (exists_eval_smul_mem hL x).choose)⁻¹ • g ⟨_, _⟩ = _
  rw [extend_wd hL g hg x (exists_eval_smul_mem hL x).choose_spec.1 one_ne_zero _
    (by rwa [map_one, one_smul])]
  simp only [map_one, inv_one, one_smul]

omit hg in
/-- Two `ℚ(v)`-linear maps that agree on a spanning lattice are equal. -/
theorem ext_of_lattice {f f' : V →ₗ[𝕂] W} (h : ∀ x ∈ L, f x = f' x) : f = f' :=
  LinearMap.ext_on hL.span_eq h

/-- Uniqueness of the extension. -/
theorem extend_unique (f : V →ₗ[𝕂] W) (hf : ∀ (x : V) (hx : x ∈ L), f x = g ⟨x, hx⟩) :
    f = extend hL g hg :=
  ext_of_lattice hL fun x hx ↦ by rw [hf x hx, extend_apply]

end Categorification.Stendhal.Lattice
