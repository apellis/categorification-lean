/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardModule

/-!
# Endomorphisms of a loading standard

For the standards of Webster, arXiv:1309.3796v2, Definition 5.1, an
endomorphism is determined by its value on the loading generator. Every
vector fixed by the same loading idempotent occurs. This reduces the
endomorphism calculation in §8.2, Proposition 8.4, to the corresponding
loading corner.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s)

local notation "A" => TensorProductAlgebra k Q Λ ν
local notation "S" => leftStandard Q Λ s hs
local notation "e" => seqIdem Q Λ s hs
local notation "g" => leftStandardUnit Q Λ s hs

private theorem loading_smul_unit : e • g = g := by
  rw [leftStandardUnit, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (seqIdem_mul_self Q Λ s hs)

/-- Evaluation on the loading generator identifies endomorphisms of the
standard with its fixed loading subspace. -/
def leftStandardEndEquivFixed : Module.End A S ≃ₗ[k] fixSub k S e := by
  let f : Module.End A S →ₗ[k] fixSub k S e :=
    { toFun := fun h => ⟨h g, by
        change e • h g = h g
        rw [← h.map_smul, loading_smul_unit]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  apply LinearEquiv.ofBijective f
  refine ⟨?_, ?_⟩
  · intro a b h
    exact leftStandard_hom_ext s hs (congrArg Subtype.val h)
  · intro z
    let h := leftStandardLift (Q := Q) (Λ := Λ) s hs z.val fun t ht a hst => by
      rw [mul_smul, seqIdem_smul_leftStandard_eq_zero Q Λ hs ht hst]
    exact ⟨h, Subtype.ext (leftStandardLift_unit (Q := Q) (Λ := Λ) s hs _ z.property _)⟩

end Categorification.Stendhal
