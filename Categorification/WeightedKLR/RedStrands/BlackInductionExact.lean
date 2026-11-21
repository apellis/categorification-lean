/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongExact
import Categorification.WeightedKLR.RedStrands.BlackRestrictionProjective
import Categorification.WeightedKLR.RedStrands.BlackModuleFunctors

/-!
# Exactness of `Fᵢ`

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6. The functor
`Fᵢ = - ⊗_{T^λ_ν} e' T^λ_{ν+i}` on right modules (`blackF`) is exact. Its corner `e' T^λ_{ν+i}`,
read in the opposite ring, is the right black cut of the regular module (`blackCornerEquiv`),
which is projective over `T^λ_ν` by Theorem 4.31 (`projective_blackRes_regular`). Hence
`InductionAlong.Ind.map_injective` and `InductionAlong.Ind.map_exact` apply:

* `blackF_map_injective`: `Fᵢ` preserves injections;
* `blackF_map_surjective`: `Fᵢ` preserves surjections;
* `blackF_map_exact`: `Fᵢ` preserves exactness in the middle.

The hypotheses are those of Theorem 4.31: a field `k` and Rouquier polynomials `Q`.
-/

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe u

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} (i : I) (ν : Multiset I)

local notation "T" => TensorProductAlgebra k Q Λ ν
local notation "T'" => TensorProductAlgebra k Q Λ ((Singleton.singleton i : Multiset I) + ν)

/-- The corner `e' T^λ_{ν+i}` of `Fᵢ`, read in the opposite ring, is the right black cut of the
regular module. -/
noncomputable def blackCornerEquiv :
    BlackRes (Q := Q) (Λ := Λ) i ν T' ≃ₛₗ[((RingEquiv.opOp T : T ≃+* Tᵐᵒᵖᵐᵒᵖ) : T →+* Tᵐᵒᵖᵐᵒᵖ)]
      Corner (appendBlackOp Q Λ i ν) where
  toFun w := ⟨op w.1, by
    rw [mem_lIdeal]
    change op (appendBlack Q Λ i ν 1 * w.1) = op w.1
    exact congrArg op w.2⟩
  invFun z := ⟨z.1.unop, by
    rw [mem_fixSub]
    exact congrArg unop z.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The corner of `Fᵢ` is projective (Webster, Theorem 4.31). -/
theorem projective_blackCorner (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q) :
    Module.Projective Tᵐᵒᵖᵐᵒᵖ (Corner (appendBlackOp Q Λ i ν)) := by
  have := projective_blackRes_regular (Q := Q) (Λ := Λ) i ν C hQ
  exact Module.Projective.of_equiv (blackCornerEquiv i ν)

variable {i ν}
variable {M M' M'' : ModuleCat.{u} (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ}

/-- **`Fᵢ` preserves injections** (Webster, §4.6, Theorem 4.31). -/
theorem blackF_map_injective (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
    {f : M ⟶ M'} (hf : Function.Injective f.hom) :
    Function.Injective ((blackF Q Λ i ν).map f).hom := by
  have := projective_blackCorner (Q := Q) (Λ := Λ) i ν C hQ
  exact Ind.map_injective hf

/-- `Fᵢ` preserves surjections. -/
theorem blackF_map_surjective {f : M ⟶ M'} (hf : Function.Surjective f.hom) :
    Function.Surjective ((blackF Q Λ i ν).map f).hom :=
  Ind.map_surjective hf

/-- **`Fᵢ` is exact in the middle** (Webster, §4.6, Theorem 4.31). -/
theorem blackF_map_exact (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
    {f : M ⟶ M'} {g : M' ⟶ M''} (h : Function.Exact f.hom g.hom) :
    Function.Exact ((blackF Q Λ i ν).map f).hom ((blackF Q Λ i ν).map g).hom := by
  have := projective_blackCorner (Q := Q) (Λ := Λ) i ν C hQ
  exact Ind.map_exact h

end Categorification.Stendhal
