/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EraseRed
import Categorification.KLR.CyclotomicAbsentColour
import Categorification.Algebra.IdempotentEquiv
import Mathlib.Algebra.Category.ModuleCat.Simple

/-!
# The extremal projective of one black strand

Webster, arXiv:1309.3796v2, Proposition 7.2 for a one-letter word with
a coroot pairing of one. The single-red tensor product block is
one-dimensional, and the actual red-first loading projective is simple.
-/

open CategoryTheory MulOpposite

namespace Categorification.Stendhal

open KLR KLRAlgebra

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 1 → I →₀ ℕ) (i : I)

local notation "ν" => (Singleton.singleton i : Multiset I)
local notation "A" => TensorProductAlgebra k Q Λ ν
local notation "a" => fun j : I => (Polynomial.X ^ Λ 0 j : Polynomial k)
local notation "f" => SingleRed.mk Q Λ ν
  (StendhalAlgebraAllOrders.e (SingleRed.insertWord ν (default : Seq ν)))

/-- The red-first loading is the unit in the one-red, one-black block. -/
theorem oneBlack_extremal_loadingIdem_eq_one : f = 1 := by
  rw [← SingleRed.insertRed_e, e_single, map_one]

/-- At a highest coroot pairing of one, the terminal one-black block is
one-dimensional over the ground field. -/
theorem oneBlack_extremal_finrank (h : Λ 0 i = 1) : Module.finrank k A = 1 := by
  let e := (cyclotomicSingleFinEquiv Q i a (Polynomial.monic_X_pow _)).trans
    (SingleRed.cyclotomicEquiv Q Λ ν).toLinearEquiv
  rw [← e.finrank_eq]
  simp [h]

/-- Webster, arXiv:1309.3796v2, Proposition 7.2, for a one-letter word of
multiplicity one. The actual red-first loading projective is simple. -/
theorem oneBlack_extremal_projective_simple (h : Λ 0 i = 1) :
    Simple (ModuleCat.of Aᵐᵒᵖ (rIdeal f)) := by
  let e : A ≃ₗ[Aᵐᵒᵖ] rIdeal f :=
    { toFun := fun x => ⟨x, by rw [mem_rIdeal, oneBlack_extremal_loadingIdem_eq_one Q Λ i, one_mul]⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun z => Subtype.ext (by rfl)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hb := (Algebra.finrank_eq_one_iff_bijective_algebraMap (F := k) (E := A)).mp
    (oneBlack_extremal_finrank Q Λ i h)
  let c : A ≃ₐ[k] k := (AlgEquiv.ofBijective (Algebra.ofId k A) hb).symm
  let _ : Simple (ModuleCat.of Aᵐᵒᵖ A) := by
    apply simple_iff_isSimpleModule.mpr
    apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
    refine ⟨c.symm.injective.nontrivial, ?_⟩
    intro x hx y
    have hx' : c x ≠ 0 := fun hz => hx (c.injective (hz.trans c.map_zero.symm))
    refine ⟨op (c.symm ((c x)⁻¹ * c y)), ?_⟩
    change x * c.symm ((c x)⁻¹ * c y) = y
    apply c.injective
    rw [map_mul, c.apply_symm_apply, ← mul_assoc, mul_inv_cancel₀ hx', one_mul]
  exact Simple.of_iso e.symm.toModuleIso

end

end Categorification.Stendhal
