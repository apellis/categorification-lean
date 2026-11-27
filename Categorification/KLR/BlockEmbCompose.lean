/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicSplit

/-!
# Composing a block embedding with a multiplicative map

Let `B : R(μ) → e_T R(ν) e_T` and `D : R(μ') → e_U R(ρ) e_U` be block embeddings, `C : R(ν) → R(ρ)`
a multiplicative linear map with `C(e_T) = e_U`, and `φ : R(μ₀) → R(μ)`, `φ' : R(μ₀) → R(μ')`
algebra maps. If `C ∘ B ∘ φ` and `D ∘ φ'` agree on the idempotents, dots and crossings of
`R(μ₀)`, they agree everywhere (`BlockEmb.map_hom_val_eq`). This is used to compare the block maps of Webster's
Proposition 5.3 for `ℓ` and `ℓ + 1` red strands (arXiv:1309.3796v3, §5.1).
-/

namespace Categorification.KLR

open MvPolynomial

variable {I₀ I J : Type*} [DecidableEq I₀] [DecidableEq I] [DecidableEq J] {k : Type*} [CommRing k]

namespace KLRAlgebra

namespace BlockEmb

variable {μ₀ : Multiset I₀} {μ ν : Multiset I} {μ' ρ : Multiset J} {T : Finset (Seq ν)}
  {U : Finset (Seq ρ)} {Q₀ : I₀ → I₀ → MvPolynomial (Fin 2) k} {Q : I → I → MvPolynomial (Fin 2) k}
  {Q' : J → J → MvPolynomial (Fin 2) k}
  (B : BlockEmb μ ν T) (D : BlockEmb μ' ρ U)
  (C : KLRAlgebra k Q ν →ₙₐ[k] KLRAlgebra k Q' ρ)
  (φ : KLRAlgebra k Q₀ μ₀ →ₐ[k] KLRAlgebra k Q μ) (φ' : KLRAlgebra k Q₀ μ₀ →ₐ[k] KLRAlgebra k Q' μ')

/-- **A multiplicative map carries a block embedding to a block embedding** when it does so on
generators: if `C` sends `e_T` to `e_U`, and for every generator `g` of `R(μ₀)` the image of
`B(φ g)` is `D(φ' g)`, then `C ∘ B ∘ φ = D ∘ φ'`. -/
theorem map_hom_val_eq (h1 : C (eSum Q T) = eSum Q' U)
    (he : ∀ i, C (B.hom Q (φ (e i))).val = (D.hom Q' (φ' (e i))).val)
    (hx : ∀ a, C (B.hom Q (φ (x a))).val = (D.hom Q' (φ' (x a))).val)
    (hψ : ∀ j, C (B.hom Q (φ (ψ j))).val = (D.hom Q' (φ' (ψ j))).val)
    (a : KLRAlgebra k Q₀ μ₀) : C (B.hom Q (φ a)).val = (D.hom Q' (φ' a)).val := by
  induction a using klr_induction with
  | hadd u v hu hv => rw [map_add, map_add, Corner.val_add, map_add, hu, hv, map_add, map_add,
      Corner.val_add]
  | hmul u v hu hv => rw [map_mul, map_mul, Corner.val_mul, map_mul, hu, hv, map_mul, map_mul,
      Corner.val_mul]
  | hr r =>
    rw [AlgHom.commutes, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes,
      Corner.val_algebraMap, Corner.val_algebraMap, ← Algebra.smul_def, ← Algebra.smul_def,
      map_smul, h1]
  | he s => exact he s
  | hx b => exact hx b
  | hψ j => exact hψ j

end BlockEmb

end KLRAlgebra

end Categorification.KLR
