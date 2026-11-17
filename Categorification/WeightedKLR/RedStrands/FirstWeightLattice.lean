/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FirstWeightBoundary
import Categorification.WeightedKLR.RedStrands.FirstWeightProjectives
import Categorification.WeightedKLR.RedStrands.FirstWeightTensor

/-!
# Projective classes and Webster's first lowering weight vectors

Webster, arXiv:1309.3796v2, §4.7, Theorem 4.38. In the first lowering block
with positive multiplicity at every red strand, the surviving boundary
projectives identify with Webster's prefix-lowering vectors in the integral
tensor-product lattice.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop Categorification.Graded LusztigF

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "LP" => LaurentPolynomial ℤ
local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
private abbrev laurentInvert : LP ≃+* LP := (LaurentPolynomial.invert (R := ℤ)).toRingEquiv

local instance : RingHomInvPair laurentInvert.toRingHom laurentInvert.toRingHom :=
  RingHomInvPair.of_ringEquiv laurentInvert

private def invertCoordinates (ℓ : ℕ) : (Fin ℓ → LP) ≃ₛₗ[laurentInvert.toRingHom] (Fin ℓ → LP) where
  toFun f r := laurentInvert (f r)
  invFun f r := laurentInvert.symm (f r)
  left_inv f := funext fun r => laurentInvert.symm_apply_apply (f r)
  right_inv f := funext fun r => laurentInvert.apply_symm_apply (f r)
  map_add' f g := funext fun r => map_add laurentInvert (f r) (g r)
  map_smul' a f := funext fun r => map_mul laurentInvert a (f r)

variable {I : Type} [Finite I] [DecidableEq I] {Y : Type*} [AddCommGroup Y]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y} {ℓ : ℕ} (i : I) (weights : Fin ℓ → Dom R)
  {k : Type*} [Field k] {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ}
  (G : KLR.GradingDatum (stendhalQ Q Λ)) (hR : R.IsXRegular)
  (hwt : ∀ r, (weights r).1 (R.coroot i) = (Λ r i : ℤ))
  (hX : ∀ a, 0 < G.degX a) (hΛ : ∀ r, 0 < Λ r i)

private def basisByRed :
    Module.Basis (Fin ℓ) LP (K0 (tensorProductGrade G {i})) :=
  (sequenceProjBasis G hX hΛ).reindex (boundaryEquiv i ℓ).symm

/-- The generator identification of Webster, arXiv:1309.3796v2, §4.7,
Theorem 4.38, at the first lowering weight. This intermediate statement
uses positive red multiplicities at the black color and positive dot degrees.
Scalar inversion translates the grading shift convention of Webster §1.2. -/
def sequenceLatticeEquiv :
    K0 (tensorProductGrade G {i}) ≃ₛₗ[laurentInvert.toRingHom] tensorFirstLattice weights i hR :=
  let b := basisByRed i G hX hΛ
  let c := pVectorBasis weights i hR (fun r => by rw [hwt r]; exact_mod_cast hΛ r)
  (b.equivFun.trans (invertCoordinates ℓ)).trans c.equivFun.symm

/-- The generator assignment of Theorem 4.38 sends the projective of the
boundary with its black strand just after red strand `r` to `pᵢ^κ`. -/
@[simp] theorem sequenceLatticeEquiv_boundary (r : Fin ℓ) :
    (sequenceLatticeEquiv i weights G hR hwt hX hΛ
      (K0.of (sequenceProj G (boundaryAt i ℓ r).1 (boundaryAt i ℓ r).2.1)) :
      TensorSpace weights) = pVector weights i r := by
  let b := basisByRed i G hX hΛ
  let c := pVectorBasis weights i hR (fun r => by rw [hwt r]; exact_mod_cast hΛ r)
  have hb : b r = K0.of (sequenceProj G (boundaryAt i ℓ r).1 (boundaryAt i ℓ r).2.1) := by
    simp [b, basisByRed, Module.Basis.reindex_apply]
  have hc : invertCoordinates ℓ (b.equivFun (b r)) = c.equivFun (c r) := by
    funext j
    change laurentInvert (b.equivFun (b r) j) = c.equivFun (c r) j
    rw [Module.Basis.equivFun_self, Module.Basis.equivFun_self]
    split <;> simp
  rw [← hb]
  change ((c.equivFun.symm (invertCoordinates ℓ (b.equivFun (b r)))) : TensorSpace weights) = _
  rw [hc, LinearEquiv.symm_apply_apply, pVectorBasis_apply]

/-- The repository shift by `a` acts by `q⁻ᵃ` in Webster's convention. -/
theorem sequenceLatticeEquiv_boundary_shift (r : Fin ℓ) (a : ℤ) :
    (sequenceLatticeEquiv i weights G hR hwt hX hΛ
      (K0.of ((sequenceProj G (boundaryAt i ℓ r).1 (boundaryAt i ℓ r).2.1).shift a)) :
      TensorSpace weights) = 𝕍 ^ (-a) • pVector weights i r := by
  rw [← K0.T_smul_of, LinearEquiv.map_smulₛₗ]
  change integralLaurentEval (LaurentPolynomial.invert (LaurentPolynomial.T a)) •
    (sequenceLatticeEquiv i weights G hR hwt hX hΛ
      (K0.of (sequenceProj G (boundaryAt i ℓ r).1 (boundaryAt i ℓ r).2.1)) :
      TensorSpace weights) = _
  rw [LaurentPolynomial.invert_T, integralLaurentEval_T, sequenceLatticeEquiv_boundary]

end Categorification.Stendhal.FirstWeight
