/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorFormWordSymmetry
import Categorification.WeightedKLR.RedStrands.BraidingComposite

set_option backward.isDefEq.respectTransparency false

/-!
# The tensor form at `v = 1` is invariant under permuting the factors

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.15: at `q = 1` the braiding becomes the permutation of the tensor factors, which
preserves the form on `V_λ = V_{λ_1} ⊗ ⋯ ⊗ V_{λ_ℓ}`.

The ordered form is `B(x, y) = B_fac(x, Θ y)`, where `B_fac` is the product of the one-factor
forms and `Θ` the inverse of the intertwiner from the bar coproduct to the coproduct
(`tensorCoproductEquiv`). On the integral lattice `Θ ≡ 1` modulo `v - 1`: `Θ` sends the word
vector of a tensor word to its entrywise bar (`tensorCoproductEquiv_word`, `entrywiseBar_word`),
and the entrywise bar is the identity modulo `v - 1`, because on `U⁻_ℤ` the bar involution is
(`exists_sub_negBar_eq_smul`). The factorwise form is invariant under permuting the factors
(`orderedFactorwise_tensorPermute`). Hence, for lattice vectors `a`, `b`, the values
`B_{λ ∘ σ}(σ a, σ b)` and `B_λ(a, b)` are Laurent polynomials with the same value at `v = 1`
(`orderedForm_tensorPermute_evalOne`), provided the forms are integral on the lattices
(`orderedForm_integralTensor`, Theorem 4.38).
-/

noncomputable section

namespace Categorification.Stendhal.TensorPairing

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF TensorProduct FirstWeight
open scoped TensorProduct

local notation "𝕂" => RatFunc ℚ
local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "LP" => LaurentPolynomial ℤ
local notation "ev" => integralLaurentEval
local notation "hvt" => transcendental_ratFunc_X
local instance : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

variable {I Y : Type*} [DecidableEq I] [AddCommGroup Y] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y} [Finite I] (hR : R.IsXRegular) {n : ℕ}

/-! ### The lattice modulo `v - 1` -/

/-- `(v - v⁻¹) x` lies in `(v - 1)` times the lattice for a lattice vector `x`. -/
theorem sub_inv_smul_mem_vOneTensor {wt : Fin n → Dom R} {x : TensorSpace wt}
    (hx : x ∈ integralTensor wt) : (𝕍 - 𝕍⁻¹) • x ∈ vOneTensor wt := by
  have h := (integralTensor wt).smul_mem (1 + LaurentPolynomial.T (-1) : LP) hx
  rw [tensor_laurent_smul, map_add, map_one, integralLaurentEval_T] at h
  rw [show (𝕍 - 𝕍⁻¹) • x = (𝕍 - 1) • ((1 + 𝕍 ^ (-1 : ℤ)) • x) by
    rw [smul_smul, zpow_neg_one]
    congr 1
    have : (𝕍 : 𝕂) ≠ 0 := RatFunc.X_ne_zero
    field_simp
    ring]
  exact sub_one_smul_mem_vOneTensor h

/-- `(c - c̄) x` lies in `(v - 1)` times the lattice for `c ∈ ℤ[v, v⁻¹]` and a lattice vector
`x`. -/
theorem sub_invert_smul_mem_vOneTensor {wt : Fin n → Dom R} (c : LP) {x : TensorSpace wt}
    (hx : x ∈ integralTensor wt) :
    (ev c - ev (LaurentPolynomial.invert c)) • x ∈ vOneTensor wt := by
  obtain ⟨d, hd⟩ := exists_sub_invert_eq_mul c
  have h := (integralTensor wt).smul_mem d hx
  rw [tensor_laurent_smul] at h
  rw [← map_sub, hd, map_mul, map_sub, integralLaurentEval_T, integralLaurentEval_T, zpow_one,
    zpow_neg_one, mul_smul]
  exact sub_inv_smul_mem_vOneTensor h

/-- On `V_ℤ(λ)` the bar involution is the identity modulo `v - v⁻¹`. -/
theorem exists_sub_hwBar_eq_smul (w : Dom R) {m : IrreducibleModule R 𝕍 w.1}
    (hm : m ∈ hwIntegral w) :
    ∃ y ∈ hwIntegral w, m - hwBar hR w m = (𝕍 - 𝕍⁻¹) • y := by
  obtain ⟨x, hx, rfl⟩ := hm
  obtain ⟨y, hy, hxy⟩ := exists_sub_negBar_eq_smul D hx
  exact ⟨evq hvt w y, ⟨y, hy, rfl⟩, by rw [hwBar_evq, ← map_sub, hxy, map_smul]⟩

/-- Changing the factors of a pure lattice tensor by multiples of `v - v⁻¹` changes it by
`(v - 1)` times the lattice. -/
theorem tprod_sub_mem_vOneTensor {wt : Fin n → Dom R} (z : ∀ j, IrreducibleModule R 𝕍 (wt j).1)
    (hz : ∀ j, z j ∈ hwIntegral (wt j)) :
    ∀ (s : Finset (Fin n)) (z' : ∀ j, IrreducibleModule R 𝕍 (wt j).1),
      (∀ j, z' j ∈ hwIntegral (wt j)) →
      (∀ j, ∃ y ∈ hwIntegral (wt j), z' j - z j = (𝕍 - 𝕍⁻¹) • y) → (∀ j ∉ s, z' j = z j) →
      PiTensorProduct.tprod 𝕂 z' - PiTensorProduct.tprod 𝕂 z ∈ vOneTensor wt := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro z' _ _ hs
    rw [show z' = z from funext fun j => hs j (Finset.notMem_empty j), sub_self]
    exact zero_mem _
  | insert j s hj ih =>
    intro z' hz' hd hs
    let z'' := Function.update z' j (z j)
    have h₁ : PiTensorProduct.tprod 𝕂 z'' - PiTensorProduct.tprod 𝕂 z ∈ vOneTensor wt := by
      refine ih z'' (fun i => ?_) (fun i => ?_) (fun i hi => ?_)
      · by_cases h : i = j
        · subst h; simp only [z'', Function.update_self]; exact hz i
        · simp only [z'', Function.update_of_ne h]; exact hz' i
      · by_cases h : i = j
        · subst h; exact ⟨0, zero_mem _, by simp [z'']⟩
        · simp only [z'', Function.update_of_ne h]; exact hd i
      · by_cases h : i = j
        · subst h; simp [z'']
        · simp only [z'', Function.update_of_ne h]
          exact hs i (by simp [h, hi])
    obtain ⟨y, hy, hyd⟩ := hd j
    have h₂ : PiTensorProduct.tprod 𝕂 z' - PiTensorProduct.tprod 𝕂 z'' =
        (𝕍 - 𝕍⁻¹) • PiTensorProduct.tprod 𝕂 (Function.update z' j y) := by
      have e := (PiTensorProduct.tprod 𝕂).map_update_sub z' j (z' j) (z j)
      rw [Function.update_eq_self] at e
      rw [← e, hyd, (PiTensorProduct.tprod 𝕂).map_update_smul]
    have hmem : PiTensorProduct.tprod 𝕂 (Function.update z' j y) ∈ integralTensor wt := by
      refine Submodule.subset_span ⟨Function.update z' j y, fun i => ?_, rfl⟩
      by_cases h : i = j
      · subst h; simp only [Function.update_self]; exact hy
      · simp only [Function.update_of_ne h]; exact hz' i
    rw [show PiTensorProduct.tprod 𝕂 z' - PiTensorProduct.tprod 𝕂 z =
      (PiTensorProduct.tprod 𝕂 z' - PiTensorProduct.tprod 𝕂 z'') +
        (PiTensorProduct.tprod 𝕂 z'' - PiTensorProduct.tprod 𝕂 z) by abel, h₂]
    exact add_mem (sub_inv_smul_mem_vOneTensor hmem) h₁

/-! ### The entrywise bar -/

/-- The entrywise bar of a pure tensor. -/
theorem entrywiseBar_tprod : ∀ {n : ℕ} (wt : Fin n → Dom R)
    (z : ∀ j, IrreducibleModule R 𝕍 (wt j).1),
    entrywiseBar hR wt (PiTensorProduct.tprod 𝕂 z) =
      PiTensorProduct.tprod 𝕂 fun j => hwBar hR (wt j) (z j)
  | 0, wt, z => by
    let e := PiTensorProduct.isEmptyEquiv (R := 𝕂)
      (s := fun j => IrreducibleModule R 𝕍 (wt j).1) (Fin 0)
    apply e.injective
    change e (e.symm (RatFunc.bar (e _))) = _
    rw [e.apply_symm_apply, PiTensorProduct.isEmptyEquiv_apply_tprod,
      PiTensorProduct.isEmptyEquiv_apply_tprod, map_one]
  | m + 1, wt, z => by
    have hsplit : ∀ x : ∀ j, IrreducibleModule R 𝕍 (wt j).1, PiTensorProduct.tprod 𝕂 x =
        appendTensor wt (PiTensorProduct.tprod 𝕂 fun j => x (Fin.castSucc j)) (x (Fin.last m)) :=
      fun x => (tensorSplitLast wt).injective (by
        rw [tensorSplitLast_tprod]
        exact ((tensorSplitLast wt).apply_symm_apply _).symm)
    rw [hsplit z, entrywiseBar_append, entrywiseBar_tprod, hsplit]

theorem entrywiseBar_entrywiseBar (wt : Fin n → Dom R) (x : TensorSpace wt) :
    entrywiseBar hR wt (entrywiseBar hR wt x) = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c z =>
    rw [map_smulₛₗ, map_smulₛₗ, entrywiseBar_tprod, entrywiseBar_tprod]
    simp only [hwBar_hwBar]
    congr 1
    exact RatFunc.bar_bar c
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem entrywiseBar_laurent_smul (wt : Fin n → Dom R) (c : LP) (x : TensorSpace wt) :
    entrywiseBar hR wt (c • x) = LaurentPolynomial.invert c • entrywiseBar hR wt x := by
  rw [tensor_laurent_smul, map_smulₛₗ, tensor_laurent_smul]
  congr 1
  exact bar_integralLaurentEval c

/-- **The entrywise bar is the identity modulo `v - 1`** on the integral lattice. -/
theorem entrywiseBar_mem_and_sub_mem (wt : Fin n → Dom R) {x : TensorSpace wt}
    (hx : x ∈ integralTensor wt) :
    entrywiseBar hR wt x ∈ integralTensor wt ∧ entrywiseBar hR wt x - x ∈ vOneTensor wt := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    rw [entrywiseBar_tprod]
    refine ⟨Submodule.subset_span ⟨_, fun j => hwBar_mem_hwIntegral hR (wt j) (hz j), rfl⟩, ?_⟩
    have hd : ∀ j, ∃ y ∈ hwIntegral (wt j),
        hwBar hR (wt j) (z j) - z j = (𝕍 - 𝕍⁻¹) • y := fun j => by
      obtain ⟨y, hy, hyd⟩ := exists_sub_hwBar_eq_smul hR (wt j) (hz j)
      exact ⟨-y, neg_mem hy, by rw [smul_neg, ← hyd, neg_sub]⟩
    exact tprod_sub_mem_vOneTensor z hz Finset.univ _
      (fun j => hwBar_mem_hwIntegral hR (wt j) (hz j)) hd
      (fun j hj => absurd (Finset.mem_univ j) hj)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    refine ⟨add_mem hx.1 hy.1, ?_⟩
    rw [show entrywiseBar hR wt x + entrywiseBar hR wt y - (x + y) =
      (entrywiseBar hR wt x - x) + (entrywiseBar hR wt y - y) by abel]
    exact add_mem hx.2 hy.2
  | smul c x hx' hx =>
    rw [entrywiseBar_laurent_smul]
    refine ⟨(integralTensor wt).smul_mem _ hx.1, ?_⟩
    have h₁ := (vOneTensor wt).smul_mem (LaurentPolynomial.invert c) hx.2
    rw [tensor_laurent_smul] at h₁
    rw [tensor_laurent_smul, tensor_laurent_smul]
    have e : ev (LaurentPolynomial.invert c) • entrywiseBar hR wt x - ev c • x =
        ev (LaurentPolynomial.invert c) • (entrywiseBar hR wt x - x) -
          (ev c - ev (LaurentPolynomial.invert c)) • x := by
      rw [smul_sub, show (ev c - ev (LaurentPolynomial.invert c)) • x =
        ev c • x - ev (LaurentPolynomial.invert c) • x by
          rw [sub_eq_add_neg, add_smul, neg_smul, ← sub_eq_add_neg]]
      abel
    rw [e]
    exact sub_mem h₁ (sub_invert_smul_mem_vOneTensor c hx')

/-! ### The intertwiner modulo `v - 1` -/

theorem tensorWordVector_mem (wt : Fin n → Dom R) (w : TensorWord I n) :
    tensorWordVector w wt ∈ integralTensor wt :=
  span_tensorWordVector wt ▸ Submodule.subset_span (Set.mem_range_self w)

/-- `Θ = (tensorCoproductEquiv)⁻¹` is the identity modulo `v - 1` on the lattice. -/
theorem tensorCoproductEquiv_symm_sub_mem (wt : Fin n → Dom R) {y : TensorSpace wt}
    (hy : y ∈ integralTensor wt) :
    (tensorCoproductEquiv hR wt).symm y - y ∈ vOneTensor wt := by
  rw [← span_tensorWordVector wt] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    rw [(LinearEquiv.symm_apply_eq _).2 (tensorCoproductEquiv_word hR w wt).symm,
      ← entrywiseBar_word hR w wt]
    exact (entrywiseBar_mem_and_sub_mem hR wt (tensorWordVector_mem wt w)).2
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, show (tensorCoproductEquiv hR wt).symm x + (tensorCoproductEquiv hR wt).symm y -
      (x + y) = ((tensorCoproductEquiv hR wt).symm x - x) +
        ((tensorCoproductEquiv hR wt).symm y - y) by abel]
    exact add_mem hx hy
  | smul c x _ hx =>
    have h := (vOneTensor wt).smul_mem c hx
    rwa [smul_sub, tensor_laurent_smul, tensor_laurent_smul, ← map_smul,
      ← tensor_laurent_smul] at h

/-- The intertwiner `tensorCoproductEquiv` preserves the lattice. -/
theorem tensorCoproductEquiv_mem (wt : Fin n → Dom R) {x : TensorSpace wt}
    (hx : x ∈ integralTensor wt) : tensorCoproductEquiv hR wt x ∈ integralTensor wt := by
  suffices h : ∀ y ∈ integralTensor wt,
      tensorCoproductEquiv hR wt (entrywiseBar hR wt y) ∈ integralTensor wt by
    rw [← entrywiseBar_entrywiseBar hR wt x]
    exact h _ (entrywiseBar_mem_and_sub_mem hR wt hx).1
  intro y hy
  rw [← span_tensorWordVector wt] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    rw [entrywiseBar_word, tensorCoproductEquiv_word]
    exact tensorWordVector_mem wt w
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [entrywiseBar_laurent_smul, tensor_laurent_smul, map_smul, ← tensor_laurent_smul]
    exact (integralTensor wt).smul_mem _ hx

/-! ### Permuting the factors -/

/-- **The factorwise form is invariant under permuting the factors.** -/
theorem orderedFactorwise_tensorPermute (wt : Fin n → Dom R) (σ : Equiv.Perm (Fin n))
    (x y : TensorSpace wt) :
    orderedFactorwise hR (wt ∘ σ) (tensorPermute wt σ x) (tensorPermute wt σ y) =
      orderedFactorwise hR wt x y := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c z =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod c' z' =>
      simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply,
        tensorPermute_tprod, orderedFactorwise_tprod]
      congr 2
      exact (orderedFactorwise_tprod hR (wt ∘ σ) (fun j => z (σ j)) (fun j => z' (σ j))).trans
        (Equiv.prod_comp σ (fun j => SingleBlack.websterForm (wt j) hR (z j) (z' j)))
    | add y y' hy hy' => simp only [map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

theorem orderedForm_eq_orderedFactorwise (wt : Fin n → Dom R) (x y : TensorSpace wt) :
    orderedForm hR wt x y = orderedFactorwise hR wt x ((tensorCoproductEquiv hR wt).symm y) :=
  rfl

/-- The form at a lattice vector differs from the factorwise form by `v - 1` times a value of
the form, which is integral when the form is. -/
theorem exists_orderedForm_eq_orderedFactorwise (wt : Fin n → Dom R)
    (hint : ∀ a ∈ integralTensor wt, ∀ b ∈ integralTensor wt, ∃ p : LP, orderedForm hR wt a b = ev p)
    {a b : TensorSpace wt} (ha : a ∈ integralTensor wt) (hb : b ∈ integralTensor wt) :
    ∃ r : LP, orderedForm hR wt a b = orderedFactorwise hR wt a b + (𝕍 - 1) * ev r := by
  obtain ⟨u, hu, hue⟩ := mem_vOneTensor_iff.1 (tensorCoproductEquiv_symm_sub_mem hR wt hb)
  obtain ⟨r, hr⟩ := hint a ha _ (tensorCoproductEquiv_mem hR wt hu)
  refine ⟨r, ?_⟩
  rw [orderedForm_eq_orderedFactorwise, show (tensorCoproductEquiv hR wt).symm b =
    b + (𝕍 - 1) • u by rw [← hue, add_sub_cancel], map_add, map_smul, ← hr,
    orderedForm_eq_orderedFactorwise, LinearEquiv.symm_apply_apply, smul_eq_mul]

/-- **Permuting the factors preserves the form at `v = 1`** (Webster, arXiv:1309.3796v3, proof
of Theorem 6.15): for lattice vectors `a`, `b`, the values `B_{λ ∘ σ}(σ a, σ b)` and
`B_λ(a, b)` are Laurent polynomials with the same value at `v = 1`, provided both forms are
integral on the lattices (`orderedForm_integralTensor`). -/
theorem orderedForm_tensorPermute_evalOne (wt : Fin n → Dom R) (σ : Equiv.Perm (Fin n))
    (hint : ∀ a ∈ integralTensor wt, ∀ b ∈ integralTensor wt, ∃ p : LP, orderedForm hR wt a b = ev p)
    (hint' : ∀ a ∈ integralTensor (wt ∘ σ), ∀ b ∈ integralTensor (wt ∘ σ),
      ∃ p : LP, orderedForm hR (wt ∘ σ) a b = ev p)
    {a b : TensorSpace wt} (ha : a ∈ integralTensor wt) (hb : b ∈ integralTensor wt) :
    ∃ p q : LP, orderedForm hR (wt ∘ σ) (tensorPermute wt σ a) (tensorPermute wt σ b) = ev p ∧
      orderedForm hR wt a b = ev q ∧ Categorification.evalOne p = Categorification.evalOne q := by
  obtain ⟨q, hq⟩ := hint a ha b hb
  obtain ⟨r, hr⟩ := exists_orderedForm_eq_orderedFactorwise hR wt hint ha hb
  obtain ⟨r', hr'⟩ := exists_orderedForm_eq_orderedFactorwise hR (wt ∘ σ) hint'
    (tensorPermute_mem σ ha) (tensorPermute_mem σ hb)
  rw [orderedFactorwise_tensorPermute] at hr'
  refine ⟨q + (LaurentPolynomial.T 1 - 1) * (r' - r), q, ?_, hq, ?_⟩
  · rw [hr', map_add, ← hq, hr, map_mul, map_sub, map_sub, integralLaurentEval_T, zpow_one,
      map_one]
    ring
  · simp

end Categorification.Stendhal.TensorPairing
