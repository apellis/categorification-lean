/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockPartialStandardTensor
import Categorification.WeightedKLR.RedStrands.StandardPartialKernel

/-!
# The partial standard at a rigid cut is the standard module

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Proposition 6.9 (v3: Proposition
6.10). The loading projective `e(t) T` is the corner `e(t) V e_κ` (`loadingRIdealEquiv`). At a
loading of red order `L ++ b :: a :: M` whose cut at `a` is rigid, the partial standard of
Lemma 6.8 is the standard module of Definition 5.1 (`partialStandardEquivStandard`), by
step 1 (`mem_violStandardUpper_iff_mem_blockUpperIdeal`).
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ)

local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "P" => rIdeal (orderedLoadingIdem Q Λ t)
local notation "K" => blockLoadingKernel Q Λ t a b

/-- The ideals of retained-higher loadings do not depend on the order of the pair. -/
theorem blockUpperIdeal_swap (α : Fin ℓ → I → ℕ) (κ : List (Fin ℓ)) :
    blockUpperIdeal k Q Λ ν a b α κ = blockUpperIdeal k Q Λ ν b a α κ := by
  have hs : (adjacentBlockRoot a b : KLR.Seq (stendhalWeight ℓ ν) → _) = adjacentBlockRoot b a :=
    funext (adjacentBlockRoot_swap a b)
  unfold blockUpperIdeal
  rw [hs]

/-- The loading projective `e(t) T` as the corner `e(t) V e_κ`. -/
def loadingRIdealEquiv : P ≃ₗ[Tᵐᵒᵖ] violCorner k Q Λ ν t (redWord t) where
  toFun x := ⟨x.1.1, mem_violCorner_iff.2 ⟨congrArg Subtype.val x.2,
    ((Subsemigroup.mem_corner_iff (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))).1
      x.1.2).2⟩⟩
  invFun y := ⟨⟨y.1, (Subsemigroup.mem_corner_iff
      (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))).2
      ⟨by
        have h := (mem_violCorner_iff.1 y.2).1
        rw [← h, ← mul_assoc, ← map_mul, redProj_mul_e, ite_eq_left rfl],
       (mem_violCorner_iff.1 y.2).2⟩⟩,
    Subtype.ext (mem_violCorner_iff.1 y.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem loadingRIdealEquiv_val (x : P) : (loadingRIdealEquiv Q Λ t x).1 = x.1.1 := rfl

variable {Q Λ t a b} in
/-- **The partial standard at a rigid cut is the standard module** (Webster,
arXiv:1309.3796v2, §6.1, proof of Proposition 6.9). At a loading `t` of red order
`L ++ b :: a :: M` whose cut at `a` is rigid, the partial standard `e(t) T / K` of Lemma 6.8 is
the standard module of Definition 5.1. -/
def partialStandardEquivStandard {L M : List (Fin ℓ)} (ht : redWord t = L ++ b :: a :: M)
    (hrig : IsRigidCut t a) :
    PartialStandardQuotient Q Λ t a b ≃ₗ[Tᵐᵒᵖ]
      ViolLoadingStandard (k := k) (Q := Q) (Λ := Λ) t (redWord t) :=
  Submodule.Quotient.equiv K (violStandardUpper t (redWord t)) (loadingRIdealEquiv Q Λ t) (by
    ext y
    rw [mem_violStandardUpper_iff_mem_blockUpperIdeal ht hrig, blockUpperIdeal_swap,
      adjacentBlockRoot_swap]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨(loadingRIdealEquiv Q Λ t).symm y, hy, (loadingRIdealEquiv Q Λ t).apply_symm_apply y⟩)

end Categorification.Stendhal.BraidedStendhalAlgebra
