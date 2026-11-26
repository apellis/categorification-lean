/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AdjacentBraidingLattice
import Categorification.WeightedKLR.RedStrands.TensorClassFunctional
import Categorification.KLR.Crystal.Thm317Graded

/-!
# The form against the adjacent braiding at `v = 1`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11: at `q = 1` the braiding is an isometry for the form, because it becomes the flip
of the tensor factors. On the integral tensor lattices the form `B` takes values in
`ℤ[v, v⁻¹]` (`orderedForm_integralTensor`: through Webster's identification of Theorem 4.38,
its values are graded Hom dimensions between projectives). For lattice vectors `a, b`, the
values `B(R a, b)` and `B(flip a, b)`, with `R` the braiding of two adjacent factors, are
Laurent polynomials with the same value at `v = 1` (`orderedForm_adjacentBraiding_evalOne`).
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "𝕂" => RatFunc ℚ
local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "ev" => integralLaurentEval

/-! ### Integrality of the form -/

section Integral

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

local notation "Kr" => rightTensorProjectiveGroup C hQ Λ
local notation "η'" => rightTensorModuleEquiv C hQ hR Λ wt hwt
local notation "B" => TensorPairing.orderedForm hR wt

variable [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]

include C hQ Λ hwt in
/-- **The form is integral on the integral tensor lattice**: for `a, b ∈ integralTensor`,
`B(a, b) ∈ ℤ[v, v⁻¹]` (Webster, arXiv:1309.3796v2, Theorem 4.38 and Lemma 4.36: the values are
graded Hom dimensions between projectives). -/
theorem orderedForm_integralTensor {a b : TensorSpace wt} (ha : a ∈ integralTensor wt)
    (hb : b ∈ integralTensor wt) : ∃ p : LP, B a b = ev p := by
  suffices key : ∀ y x, ∃ p : LP, B (η' y : TensorSpace wt) (η' x : TensorSpace wt) = ev p by
    obtain ⟨y, hy⟩ := (η').surjective ⟨a, ha⟩
    obtain ⟨x, hx⟩ := (η').surjective ⟨b, hb⟩
    have hay : a = (η' y : TensorSpace wt) := by rw [hy]
    have hbx : b = (η' x : TensorSpace wt) := by rw [hx]
    rw [hay, hbx]
    exact key y x
  intro y x
  induction y using DirectSum.induction_on with
  | zero => exact ⟨0, by rw [map_zero, ZeroMemClass.coe_zero, map_zero, LinearMap.zero_apply,
      map_zero]⟩
  | add y y' hy hy' =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨p', hp'⟩ := hy'
    exact ⟨p + p', by rw [map_add, Submodule.coe_add, map_add, LinearMap.add_apply, hp, hp',
      map_add]⟩
  | of ν z =>
    rw [← DirectSum.lof_eq_of LP]
    induction z using K0.induction_on with
    | of P =>
      rw [← classFunctional_projective C hQ hR Λ wt hwt ν P, classFunctional_eta]
      exact ⟨_, rfl⟩
    | zero => exact ⟨0, by rw [map_zero, map_zero, ZeroMemClass.coe_zero, map_zero,
        LinearMap.zero_apply, map_zero]⟩
    | add z z' hz hz' =>
      obtain ⟨p, hp⟩ := hz
      obtain ⟨p', hp'⟩ := hz'
      exact ⟨p + p', by rw [map_add, map_add, Submodule.coe_add, map_add, LinearMap.add_apply, hp,
        hp', map_add]⟩
    | neg z hz =>
      obtain ⟨p, hp⟩ := hz
      exact ⟨-p, by rw [map_neg, map_neg, Submodule.coe_neg, map_neg, LinearMap.neg_apply, hp,
        map_neg]⟩

end Integral

/-! ### The adjacent braiding at `v = 1` -/

variable {I : Type} {k Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {n m : ℕ} (Λ : Fin (n + 2 + m) → I →₀ ℕ)
    (wt : Fin (n + 2 + m) → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    (Λ' : Fin (n + 2 + m) → I →₀ ℕ) (wt' : Fin (n + 2 + m) → Dom R)
    (hwt' : ∀ r i, (Λ' r i : ℤ) = (wt' r).1 (R.coroot i))
    (h₁ : ∀ i : Fin n, wt' (Fin.castAdd m (Fin.castAdd 2 i)) = wt (Fin.castAdd m (Fin.castAdd 2 i)))
    (h₂ : wt' (Fin.castAdd m (Fin.natAdd n 0)) = wt (Fin.castAdd m (Fin.natAdd n 1)))
    (h₃ : wt' (Fin.castAdd m (Fin.natAdd n 1)) = wt (Fin.castAdd m (Fin.natAdd n 0)))
    (h₄ : ∀ i : Fin m, wt' (Fin.natAdd (n + 2) i) = wt (Fin.natAdd (n + 2) i))
    [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ' ν)ᵐᵒᵖ]

include C hQ Λ' hwt' in
/-- **At `v = 1` the adjacent braiding is an isometry onto the flip** (Webster,
arXiv:1309.3796v2, proof of Lemma 6.11): for `a` in the integral lattice of `V_λ` and `b` in
that of the exchanged product, `B(R a, b)` and `B(flip a, b)` are Laurent polynomials with the
same value at `v = 1`. -/
theorem orderedForm_adjacentBraiding_evalOne {a : TensorSpace wt} (ha : a ∈ integralTensor wt)
    {b : TensorSpace wt'} (hb : b ∈ integralTensor wt') :
    ∃ p q : LP, TensorPairing.orderedForm hR wt' (adjacentBraiding hR wt wt' h₁ h₂ h₃ h₄ a) b =
        ev p ∧ TensorPairing.orderedForm hR wt' (adjacentFlip wt wt' h₁ h₂ h₃ h₄ a) b = ev q ∧
      evalOne p = evalOne q := by
  obtain ⟨y, hy, hyeq⟩ := adjacentBraiding_sub_adjacentFlip_mem hR wt wt' h₁ h₂ h₃ h₄ ha
  have hRa := adjacentBraiding_mem_integralTensor hR wt wt' h₁ h₂ h₃ h₄ ha
  have hvy : (𝕍 - 1) • y ∈ integralTensor wt' := by
    have h := (integralTensor wt').smul_mem (LaurentPolynomial.T 1 - 1 : LP) hy
    rwa [tensor_laurent_smul, map_sub, integralLaurentEval_T, map_one, zpow_one] at h
  have hfa : adjacentFlip wt wt' h₁ h₂ h₃ h₄ a ∈ integralTensor wt' := by
    rw [show adjacentFlip wt wt' h₁ h₂ h₃ h₄ a =
      adjacentBraiding hR wt wt' h₁ h₂ h₃ h₄ a - (𝕍 - 1) • y by rw [← hyeq, sub_sub_cancel]]
    exact sub_mem hRa hvy
  obtain ⟨q, hq⟩ := orderedForm_integralTensor C hQ hR Λ' wt' hwt' hfa hb
  obtain ⟨r, hr⟩ := orderedForm_integralTensor C hQ hR Λ' wt' hwt' hy hb
  refine ⟨q + (LaurentPolynomial.T (-1) - 1) * r, q, ?_, hq, ?_⟩
  · rw [show adjacentBraiding hR wt wt' h₁ h₂ h₃ h₄ a =
        adjacentFlip wt wt' h₁ h₂ h₃ h₄ a + (𝕍 - 1) • y by rw [← hyeq, add_sub_cancel],
      map_add, map_smulₛₗ,
      LinearMap.add_apply, LinearMap.smul_apply, hq, hr, smul_eq_mul, map_add, map_mul]
    congr 2
    rw [map_sub ev, map_one, integralLaurentEval_T, map_sub, map_one]
    change RatFunc.bar (RatFunc.X : 𝕂) - 1 = _
    rw [← zpow_one (RatFunc.X : 𝕂), bar_zpow_X, zpow_one]
  · simp

end Categorification.Stendhal.FirstWeight
