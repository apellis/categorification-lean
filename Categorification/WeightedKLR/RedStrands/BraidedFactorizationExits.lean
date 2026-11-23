/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationCancel
import Categorification.WeightedKLR.RedStrands.BraidedRedOrder
import Categorification.TypeA.Exits
import Categorification.TypeA.Matsumoto

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor products of braided Stendhal corners: additive pairs and exits

Part of the proof of Webster, arXiv:1309.3796v2, Lemma 6.5, for one red-red crossing: the
red strands of `κ₀ = L ++ a :: b :: M` and `κ₁ = L ++ b :: a :: M` differ by exchanging the
adjacent labels `a` and `b`, and `b` comes before `a` in `κ₂`.

The class `ψ_u ⊗ ψ_v x^p e(i)` vanishes unless the red strands of `i`, `v • i` and `u v • i`
read `κ₀`, `κ₁` and `κ₂`. In that case `v` inverts exactly the red strands `q < p` of `i`
labelled `a` and `b`, and `u v` inverts them as well. When `ℓ(u v) = ℓ(u) + ℓ(v)`, simple
transpositions of `v` other than the red crossing can be moved to `u` until `v = s e` for an
exit `e` of `u v` (`TypeA.IsExit`), and the class does not depend on the exit modulo lower
degree, since exits are connected by squares and hexagons (`TypeA.exitRel_connected`).
-/

namespace Categorification.Stendhal

open KLR TypeA Equiv MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "R" => KLR.KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)

namespace BraidedStendhalAlgebra

variable {κ₂ κ₁ κ₀ : List (Fin ℓ)}

/-! ### The outer idempotents -/

/-- Left multiplication by the left idempotent does not change `gen`. -/
theorem gen_redIdem_mul (x y : R) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ (redIdem k Q Λ κ₂ * x) y = gen κ₂ κ₁ κ₀ x y := by
  have h := isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ₂
  simp only [gen, map_mul]
  rw [CornerTensor.tmul_corner (x := ofKLR k Q Λ ν _ * _),
    CornerTensor.tmul_corner (x := ofKLR k Q Λ ν x)]
  congr 1
  rw [show ofKLR k Q Λ ν (redIdem k Q Λ κ₂) = redProj k Q Λ ν κ₂ from rfl, ← mul_assoc,
    h.eq]

/-- Right multiplication by the right idempotent does not change `gen`. -/
theorem gen_mul_redIdem_right (x y : R) :
    gen (Q := Q) (Λ := Λ) κ₂ κ₁ κ₀ x (y * redIdem k Q Λ κ₀) = gen κ₂ κ₁ κ₀ x y := by
  have h := isIdempotentElem_redProj (k := k) (Q := Q) (Λ := Λ) (ν := ν) κ₀
  simp only [gen, map_mul]
  rw [CornerTensor.tmul_corner (y := ofKLR k Q Λ ν y * _),
    CornerTensor.tmul_corner (y := ofKLR k Q Λ ν y)]
  congr 1
  rw [show ofKLR k Q Λ ν (redIdem k Q Λ κ₀) = redProj k Q Λ ν κ₀ from rfl, ← mul_assoc,
    mul_assoc _ (redProj k Q Λ ν κ₀), h.eq]

variable {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (hρ : IsReducedChoice ρ)

/-- `pgen u v p i` vanishes unless the red strands of `i` read `κ₀`. -/
theorem pgen_eq_zero_right (u v : Perm (Fin m)) (p : MvPolynomial (Fin m) k) (i : Seq μ)
    (h : redWord i ≠ κ₀) :
    pgen (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ u v p i = 0 := by
  rw [pgen, ← gen_mul_redIdem_right, mul_assoc, e_mul_redIdem, ite_eq_right h, mul_zero,
    gen_zero_right]

include hρ

/-- `pgen u v p i` vanishes unless the red strands of `u v • i` read `κ₂`. -/
theorem pgen_eq_zero_left (u v : Perm (Fin m)) (p : MvPolynomial (Fin m) k) (i : Seq μ)
    (h : redWord ((u * v) • i) ≠ κ₂) :
    pgen (Q := Q) (Λ := Λ) (κ₂ := κ₂) (κ₁ := κ₁) (κ₀ := κ₀) ρ u v p i = 0 := by
  by_cases hv : redWord (v • i) = κ₁
  swap
  · exact pgen_eq_zero hρ u v p i hv
  have hy := e_mul_std (Q := Q) (Λ := Λ) (ρ v) p i
  rw [(hρ v).2] at hy
  have h₁ : (redIdem k Q Λ κ₁ * KLRAlgebra.e (v • i) : R) = KLRAlgebra.e (v • i) := by
    rw [redIdem_mul_e, ite_eq_left hv]
  have h₂ : (KLRAlgebra.e (v • i) * redIdem k Q Λ κ₁ : R) = KLRAlgebra.e (v • i) := by
    rw [e_mul_redIdem, ite_eq_left hv]
  rw [pgen, ← hy, ← gen_mul_corner _ _ _ h₁ h₂, KLRAlgebra.ψw_mul_e, (hρ u).2, ← mul_smul,
    ← gen_redIdem_mul, ← mul_assoc, redIdem_mul_e, ite_eq_right h, zero_mul, gen_zero_left]

end BraidedStendhalAlgebra

end Categorification.Stendhal
