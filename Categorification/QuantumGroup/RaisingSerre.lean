/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LieLean.Algebra.QuantumGroup.Triangular

/-!
# Raising Serre relations on a cyclic highest-weight space

The skew derivatives annihilate a Serre element (Lusztig, §1.4.3).
Consequently the corresponding raising polynomial commutes with every
lowering operator. If the lowering operators generate the space from a
primitive vector, the raising Serre relation holds throughout.
-/

noncomputable section
namespace Categorification.QuantumGroup
open LieLean LieLean.QuantumGroup LusztigF

variable {I Y k M : Type*} [DecidableEq I] [AddCommGroup Y] [Field k]
    [AddCommGroup M] [Module k M] {D : LusztigCartanDatum I} {R : D.RootDatum Y}
    {v : k} {e f : I → Module.End k M} {κ : Multiplicative Y →* Module.End k M}

/-- The binomial raising Serre operator commutes with every lowering generator
under the torus and mixed Chevalley relations. -/
theorem raisingSerre_commute (h : PreRelations R v e f κ) (hv : v ≠ 0) {i j : I}
    (hij : i ≠ j) (l : I) :
    Commute (qSerre (v ^ D.d i) (1-D.cartanMatrix i j).toNat (e i) (e j)) (f l) := by
  let S := qSerre (v ^ D.d i) (1-D.cartanMatrix i j).toNat (θ k i) (θ k j)
  have he : FreeAlgebra.lift k e S = qSerre (v ^ D.d i) (1-D.cartanMatrix i j).toNat (e i) (e j) := by
    simp [S, map_qSerre, θ]
  have H := h.lift_mul_sub hv l S
  have hr : rDeriv D v l S = 0 := rDeriv_qSerre hv hij l
  have hl : lDeriv D v l S = 0 := lDeriv_qSerre hv hij l
  rw [hr, hl, map_zero, zero_mul, mul_zero, he] at H
  exact sub_eq_zero.mp (H.trans (by module))

/-- Lowering generation from a primitive vector implies all positive Serre
relations, once the torus and Chevalley commutator relations hold. -/
theorem raisingSerre_of_cyclic (h : PreRelations R v e f κ) (hv : v ≠ 0) {w : M}
    (hw : ∀ i, e i w = 0)
    (hgen : ∀ V : Submodule k M, w ∈ V → (∀ i x, x ∈ V → f i x ∈ V) → V = ⊤)
    {i j : I} (hij : i ≠ j) :
    qSerre (v ^ D.d i) (1-D.cartanMatrix i j).toNat (e i) (e j) = 0 := by
  let S := qSerre (v ^ D.d i) (1-D.cartanMatrix i j).toNat (e i) (e j)
  have h0 : S w = 0 := by
    simp only [S, qSerre, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    apply Finset.sum_eq_zero
    intro r _
    cases r with
    | zero => simp [hw]
    | succ r => rw [pow_succ (e i), Module.End.mul_apply, hw, map_zero, map_zero, map_zero, smul_zero]
  apply LinearMap.ker_eq_top.mp
  apply hgen (LinearMap.ker S) h0
  intro l x hx
  have H := congrArg (fun g : Module.End k M => g x) (raisingSerre_commute h hv hij l).eq
  change S (f l x) = 0
  exact H.trans (by change f l (S x) = 0; rw [show S x = 0 from hx, map_zero])

/-- Reversing both the parameter and the torus preserves the quantum-group
relations (Lusztig, 3.1.1, the bar symmetry of 3.1.12). -/
theorem relations_inv (h : Relations R v e f κ) :
    Relations R v⁻¹ e f (κ.comp invMonoidHom) where
  K_mul_E y i := by
    simpa only [MonoidHom.comp_apply, invMonoidHom_apply, ← ofAdd_neg,
      map_neg, inv_zpow', neg_neg] using h.K_mul_E (-y) i
  K_mul_F y i := by
    simpa only [MonoidHom.comp_apply, invMonoidHom_apply, ← ofAdd_neg,
      map_neg, inv_zpow', neg_neg] using h.K_mul_F (-y) i
  E_mul_F i j := by
    rw [h.E_mul_F]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, ite_eq_left rfl]
      simp only [ MonoidHom.comp_apply, invMonoidHom_apply,
        ← ofAdd_neg, neg_neg, inv_pow, inv_inv]
      rw [← neg_sub (v ^ D.d i) _, inv_neg, neg_smul, ← smul_neg, neg_sub]
    · rw [ite_eq_right hij, ite_eq_right hij]
  serre_E i j hij := by rw [inv_pow, qSerre_inv]; exact h.serre_E i j hij
  serre_F i j hij := by rw [inv_pow, qSerre_inv]; exact h.serre_F i j hij

end Categorification.QuantumGroup
