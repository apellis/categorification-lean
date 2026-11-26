/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicSplit

/-!
# Composing a block embedding with a multiplicative map

A block embedding `B : R(μ) → e_T R(ν) e_T` followed by a multiplicative linear map
`C : R(ν) → R(ρ)` is the block embedding `D : R(μ) → e_U R(ρ) e_U` as soon as the two agree on
the images of the generators: `C(e_T) = e_U`, `C(e_{F_B i}) = e_{F_D i}`, and `C` sends the dots
and crossings of the block of `B`, cut by `e_T`, to those of the block of `D`, cut by `e_U`
(`BlockEmb.map_hom_val_eq`). This is used to compare the block maps of Webster's
Proposition 5.3 for `ℓ` and `ℓ + 1` red strands (arXiv:1309.3796v3, §5.1).
-/

namespace Categorification.KLR

open MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

namespace KLRAlgebra

namespace BlockEmb

variable {μ μ' ν ρ : Multiset I} {T : Finset (Seq ν)} {U : Finset (Seq ρ)}
  {Q Q' : I → I → MvPolynomial (Fin 2) k}
  (B : BlockEmb μ ν T) (D : BlockEmb μ' ρ U)
  (C : KLRAlgebra k Q ν →ₙₐ[k] KLRAlgebra k Q' ρ) (φ : KLRAlgebra k Q μ →ₐ[k] KLRAlgebra k Q' μ')

/-- **A multiplicative map carries a block embedding to a block embedding** when it does so on
generators: if `C` sends `e_T` to `e_U` and the images under `B` of the generators of `R(μ)` to
the images under `D` of their images under `φ`, then `C ∘ B = D ∘ φ`. -/
theorem map_hom_val_eq (h1 : C (eSum Q T) = eSum Q' U)
    (he : ∀ i, C (B.eF Q i) = (D.hom Q' (φ (e i))).val)
    (hx : ∀ a, C (x (B.pos a) * eSum Q T) = (D.hom Q' (φ (x a))).val)
    (hψ : ∀ j, j + 1 < Multiset.card μ →
      C (ψ (B.o + j) * eSum Q T) = (D.hom Q' (φ (ψ j))).val)
    (hψ0 : ∀ j, ¬ j + 1 < Multiset.card μ → (D.hom Q' (φ (ψ j))).val = 0)
    (a : KLRAlgebra k Q μ) : C (B.hom Q a).val = (D.hom Q' (φ a)).val := by
  induction a using klr_induction with
  | hadd u v hu hv => rw [map_add, Corner.val_add, map_add, hu, hv, map_add, map_add,
      Corner.val_add]
  | hmul u v hu hv => rw [map_mul, Corner.val_mul, map_mul, hu, hv, map_mul, map_mul,
      Corner.val_mul]
  | hr r =>
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes, Corner.val_algebraMap,
      Corner.val_algebraMap, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, h1]
  | he s => rw [hom_e, val_gE, he]
  | hx b => rw [hom_x, val_polCorner, pol_X, hx]
  | hψ j =>
    rw [hom_ψ]
    by_cases hj : j + 1 < Multiset.card μ
    · rw [B.val_gψ hj, hψ j hj]
    · rw [B.gψ_of_not_lt hj, Corner.val_zero, map_zero, hψ0 j hj]

end BlockEmb

end KLRAlgebra

end Categorification.KLR
