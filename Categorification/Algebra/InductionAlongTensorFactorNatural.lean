/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongTensorFactorAction

/-!
# Naturality of induction along a map of the second tensor factor

For `φ : A → B` and `ψ : C ⊗ A → C ⊗ B` with `ψ (c ⊗ a) = c ⊗ φ a`, the identification
`(Ind_ψ N)|_B ≅ Ind_φ (N|_A)` (`indRightFactorEquivB`) is natural in maps of `C ⊗ A`-modules
(`indRightFactorEquivB_map`). In B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, proof of Proposition 5.5, `F`-part, this carries the action of an algebra
commuting with `T^{λ'} ⊗ R^{λ_ℓ}(β)` through the induction `₂Fᵢ` along the last factor.
-/

namespace Categorification

open MulOpposite
open scoped TensorProduct

noncomputable section

namespace InductionAlong

universe u w

variable {k : Type*} [CommRing k] {A : Type u} [Ring A] [Algebra k A] {C : Type u} [Ring C]
  [Algebra k C] {B : Type u} [Ring B] [Algebra k B] (φ : A →ₙ+* B)
  (hφ : ∀ (c : k) (t : A), φ (c • t) = c • φ t)
  (ψ : C ⊗[k] A →ₙ+* C ⊗[k] B) (hψ : ∀ (c : C) (a : A), ψ (c ⊗ₜ a) = c ⊗ₜ φ a)
  {N N' : Type w} [AddCommGroup N] [Module k N] [Module (C ⊗[k] A) N]
  [IsScalarTower k (C ⊗[k] A) N] [AddCommGroup N'] [Module k N'] [Module (C ⊗[k] A) N']
  [IsScalarTower k (C ⊗[k] A) N']

/-- A map of `C ⊗ A`-modules as a map of the restrictions to `A`. -/
def rightFactorResMap (G : N →ₗ[C ⊗[k] A] N') :
    RightFactorRes k A C N →ₗ[A] RightFactorRes k A C N' where
  toFun n := (show N' from G (show N from n))
  map_add' n n' := G.map_add (show N from n) (show N from n')
  map_smul' a n := G.map_smul ((1 : C) ⊗ₜ[k] a) (show N from n)

theorem rightFactorFwdLin_map (G : N →ₗ[C ⊗[k] A] N') (y : C ⊗[k] B) (n : N) :
    rightFactorFwdLin φ hφ y (G n) = (IndK.map (rightFactorResMap G) (rightFactorFwdLin φ hφ y n) :
      IndK k (RightFactorRes k A C N') φ) := by
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => rw [map_add, LinearMap.add_apply, hy, hy', map_add, LinearMap.add_apply,
      map_add]
  | tmul c b =>
    rw [rightFactorFwdLin_tmul, rightFactorFwdLin_tmul, IndK.map_tmul]
    change IndK.tmul _ (show RightFactorRes k A C N' from ((c ⊗ₜ[k] (1 : A)) • G n)) =
      IndK.tmul _ (show RightFactorRes k A C N' from G ((c ⊗ₜ[k] (1 : A)) • n))
    rw [G.map_smul]

/-- **`indRightFactorEquivB` is natural** in maps of `C ⊗ A`-modules. -/
theorem indRightFactorEquivB_map (G : N →ₗ[C ⊗[k] A] N') (t : IndK k N ψ) :
    indRightFactorEquivB φ hφ ψ hψ (show RightFactorRes k B C (IndK k N' ψ) from IndK.map G t) =
      IndK.map (rightFactorResMap G) (indRightFactorEquivB φ hφ ψ hψ t) := by
  induction t using Ind.induction_on with
  | zero =>
    exact (congrArg (indRightFactorEquiv φ hφ ψ hψ) (map_zero _)).trans
      ((map_zero _).trans ((map_zero _).symm.trans
        (congrArg (IndK.map (rightFactorResMap G)) (map_zero _).symm)))
  | tmul z n => exact rightFactorFwdLin_map φ hφ G z.1 n
  | add s t hs ht =>
    exact (congrArg (indRightFactorEquiv φ hφ ψ hψ) (map_add _ s t)).trans
      ((map_add _ _ _).trans ((congrArg₂ (· + ·) hs ht).trans
        ((map_add _ _ _).symm.trans
          (congrArg (IndK.map (rightFactorResMap G)) (map_add _ s t).symm))))

end InductionAlong

end

end Categorification
