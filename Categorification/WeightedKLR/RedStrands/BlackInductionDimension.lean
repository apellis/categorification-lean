/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.IdempotentDimension
import Categorification.Algebra.InductionAlongTensor
import Categorification.WeightedKLR.RedStrands.BlackInductionExact

/-!
# Additivity of the dimension of `F_i`

Webster, arXiv:1309.3796v3, proof of Proposition 5.5. Induction `F_i` of left modules along
`appendBlack` (with its `k`-structure through `T^λ_{i+ν}`, `IndK`) is exact for Rouquier
polynomials (`appendBlack_ind_map_injective`, `appendBlack_ind_map_exact`; Theorem 4.31).
Hence the `k`-dimension of `F_i` is additive on short exact sequences of `T^λ_ν`-modules
(`finrank_indK_appendBlack_of_exact`).
-/

noncomputable section

namespace Categorification.Stendhal

open InductionAlong KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {i : I} {ν : Multiset I}

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "Φ" => appendBlackNU (Q := Q) (Λ := Λ) i ν

/-- **The dimension of `F_i` is additive on short exact sequences** (Webster,
arXiv:1309.3796v3, proof of Proposition 5.5, using Theorem 4.31): for a short exact sequence
`0 → N → N' → N'' → 0` of `T^λ_ν`-modules with `F_i N'` finite-dimensional,
`dim F_i N' = dim F_i N + dim F_i N''`. -/
theorem finrank_indK_appendBlack_of_exact {N N' N'' : Type w} [AddCommGroup N] [Module T N]
    [AddCommGroup N'] [Module T N'] [AddCommGroup N''] [Module T N'']
    (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
    {f : N →ₗ[T] N'} {g : N' →ₗ[T] N''} (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [FiniteDimensional k (IndK k N' Φ)] :
    Module.finrank k (IndK k N' Φ) =
      Module.finrank k (IndK k N Φ) + Module.finrank k (IndK k N'' Φ) := by
  let F : IndK k N Φ →ₗ[TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)]
      IndK k N' Φ := Ind.map (φ := Φ) f
  let G : IndK k N' Φ →ₗ[TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)]
      IndK k N'' Φ := Ind.map (φ := Φ) g
  have h := pieceDim_of_exact k (a := (1 : TensorProductAlgebra k Q Λ
      ((Singleton.singleton i : Multiset I) + ν))) (IsIdempotentElem.one) F G
    (appendBlack_ind_map_injective C hQ hf) (Ind.map_surjective hg)
    (appendBlack_ind_map_exact C hQ hfg)
  rw [← finrank_eq_pieceDim_one, ← finrank_eq_pieceDim_one, ← finrank_eq_pieceDim_one] at h
  exact h

/-- `F_i` of the middle term of a short exact sequence is finite-dimensional when it is so for
the outer terms (Webster, arXiv:1309.3796v3, proof of Proposition 5.5). -/
theorem finiteDimensional_indK_appendBlack_of_exact {N N' N'' : Type w} [AddCommGroup N]
    [Module T N] [AddCommGroup N'] [Module T N'] [AddCommGroup N''] [Module T N'']
    {f : N →ₗ[T] N'} {g : N' →ₗ[T] N''} (C : QuantumGroup.CartanDatum I)
    (hQ : IsRouquierQ C Q) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [FiniteDimensional k (IndK k N Φ)] [FiniteDimensional k (IndK k N'' Φ)] :
    FiniteDimensional k (IndK k N' Φ) := by
  let F : IndK k N Φ →ₗ[k] IndK k N' Φ :=
    { toFun := Ind.map (φ := Φ) f
      map_add' := map_add _
      map_smul' := fun c x => (Ind.map (φ := Φ) f).map_smul (algebraMap k _ c) x }
  let G : IndK k N' Φ →ₗ[k] IndK k N'' Φ :=
    { toFun := Ind.map (φ := Φ) g
      map_add' := map_add _
      map_smul' := fun c x => (Ind.map (φ := Φ) g).map_smul (algebraMap k _ c) x }
  exact Module.Finite.of_exact (f := F) (g := G) (appendBlack_ind_map_exact C hQ hfg)
    (Ind.map_surjective hg)

end Categorification.Stendhal
