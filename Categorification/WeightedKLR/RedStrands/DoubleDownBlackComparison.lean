/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDownBlackMatrix
import Categorification.WeightedKLR.RedStrands.DoubleDownComparison
import Categorification.WeightedKLR.RedStrands.DoubleDownCLComparison
import Categorification.WeightedKLR.RedStrands.BlackRescale

/-!
# The matrix map of `Fᵢ` and adjoining a black strand

Webster, arXiv:1309.3796v3, §5, Proposition 5.3. On the all-down block, the matrix map of the
word `Fᵢ` (`blackMatrix`) intertwines the map of Lemma 4.28 (`ordinaryToDownwardMatrix`) with
Webster's map adjoining a black strand on the right of the tensor product algebra
(`appendBlack`, §4.6 after Theorem 4.31).
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLR.Diagram TypeA
open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (scalars : I → I → kˣ) (i : I) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "labels" => (Subtype.val ∘ Λ)
local notation "R" => affineCoverQ Q exponents
local notation "P↓" => addDownRelations RD labels R P
local notation "P₁" => addRedUpRelations RD labels k
  (addMixedBlackRelations RD labels k scalars (P↓))
local notation "hwt" => stendhalWeight_black_cons (ℓ := ℓ) i ν

omit [CommRing k] in
theorem cast_append_eq_appendBlackLoading (s : Seq (stendhalWeight ℓ ν)) :
    Seq.cast hwt (Seq.cast (add_comm _ _) (s.append default)) = appendBlackLoading i ν s := by
  apply Subtype.ext
  funext a
  rfl

/-- Lemma 4.28 after adjoining a black strand, on the affine KLR cover. -/
private def appendSide : KLRAlgebra k R μ →ₙₐ[k] downwardMatrix (P₁) ({i} + ν) :=
  ((ordinaryToDownwardMatrix P Q exponents scalars (ν := {i} + ν)).toNonUnitalAlgHom.comp
    (appendBlack Q exponents i ν)).comp (affineTensorProjection exponents ν).toNonUnitalAlgHom

/-- The matrix map of `Fᵢ` after Lemma 4.28, on the affine KLR cover. -/
private def matrixSide : KLRAlgebra k R μ →ₙₐ[k] downwardMatrix (P₁) ({i} + ν) :=
  (blackMatrix (P₁) i).comp
    ((ordinaryToDownwardMatrix P Q exponents scalars (ν := ν)).toNonUnitalAlgHom.comp
      (affineTensorProjection exponents ν).toNonUnitalAlgHom)

private theorem appendSide_apply (x : KLRAlgebra k R μ) :
    appendSide P Q exponents scalars i ν x =
      ordinaryToDownwardMatrix P Q exponents scalars (ν := {i} + ν)
        (affineTensorProjection exponents ({i} + ν)
          (KLRAlgebra.castKLR R hwt (KLRAlgebra.cL R (Sum.inl i) μ x))) :=
  congrArg (ordinaryToDownwardMatrix P Q exponents scalars) (appendBlack_affineTensorProjection ..)

private theorem matrixSide_apply (x : KLRAlgebra k R μ) :
    matrixSide P Q exponents scalars i ν x =
      blackMatrix (P₁) i (ordinaryToDownwardMatrix P Q exponents scalars (ν := ν)
        (affineTensorProjection exponents ν x)) := rfl

private theorem sides_e (s : Seq μ) :
    appendSide P Q exponents scalars i ν (KLRAlgebra.e s) =
      matrixSide P Q exponents scalars i ν (KLRAlgebra.e s) := by
  rw [appendSide_apply, matrixSide_apply, KLRAlgebra.cL_e, KLRAlgebra.castKLR_e,
    cast_append_eq_appendBlackLoading, ordinaryToDownwardMatrix_e, ordinaryToDownwardMatrix_e,
    blackMatrix_downE]

private theorem sides_one :
    appendSide P Q exponents scalars i ν 1 = matrixSide P Q exponents scalars i ν 1 := by
  rw [← KLRAlgebra.sum_e, map_sum, map_sum]
  exact Finset.sum_congr rfl fun s _ => sides_e P Q exponents scalars i ν s

private theorem sides_x (a : Fin (Multiset.card μ)) :
    appendSide P Q exponents scalars i ν (KLRAlgebra.x a) =
      matrixSide P Q exponents scalars i ν (KLRAlgebra.x a) := by
  rw [appendSide_apply, KLRAlgebra.cL_x, map_mul, map_mul, map_mul,
    ← appendSide_apply, sides_one, matrixSide_apply, matrixSide_apply, map_one, map_one,
    KLRAlgebra.castKLR_x, ordinaryToDownwardMatrix_x, ordinaryToDownwardMatrix_x,
    blackMatrix_downX]
  rfl

private theorem sides_ψ (j : ℕ) :
    appendSide P Q exponents scalars i ν (KLRAlgebra.ψ j) =
      matrixSide P Q exponents scalars i ν (KLRAlgebra.ψ j) := by
  by_cases hj : j + 1 < Multiset.card μ
  · rw [appendSide_apply, KLRAlgebra.cL_ψ _ _ hj, map_mul, map_mul, map_mul,
      ← appendSide_apply, sides_one, matrixSide_apply, matrixSide_apply, map_one, map_one,
      KLRAlgebra.castKLR_ψ, ordinaryToDownwardMatrix_ψ, ordinaryToDownwardMatrix_ψ,
      blackMatrix_downΨ _ _ hj]
  · rw [KLRAlgebra.ψ_eq_zero j (by omega), map_zero, map_zero]

private theorem appendSide_eq (x : KLRAlgebra k R μ) :
    appendSide P Q exponents scalars i ν x = matrixSide P Q exponents scalars i ν x := by
  induction x using KLRAlgebra.klr_induction with
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]
  | hmul x y hx hy => rw [map_mul, map_mul, hx, hy]
  | hr c => rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, sides_one]
  | he s => exact sides_e P Q exponents scalars i ν s
  | hx a => exact sides_x P Q exponents scalars i ν a
  | hψ j => exact sides_ψ P Q exponents scalars i ν j

/-- On the all-down block, the matrix map of `Fᵢ` intertwines the map of Webster,
arXiv:1309.3796v3, Lemma 4.28, with adjoining a black strand on the right of the tensor product
algebra. -/
theorem ordinaryToDownwardMatrix_appendBlack (z : TensorProductAlgebra k Q exponents ν) :
    ordinaryToDownwardMatrix P Q exponents scalars (ν := {i} + ν)
        (appendBlack Q exponents i ν z) =
      blackMatrix (P₁) i (ordinaryToDownwardMatrix P Q exponents scalars (ν := ν) z) := by
  obtain ⟨x, rfl⟩ := affineTensorProjection_surjective (Q := Q) exponents ν z
  exact appendSide_eq P Q exponents scalars i ν x

/-- The rescaled comparison of Lemma 4.28 intertwines adjoining a black strand with the matrix
map of `Fᵢ`. -/
theorem rescaledToDownwardMatrix_appendBlack (Qd : I → I → MvPolynomial (Fin 2) k)
    {s : I → I → kˣ} (hs : ∀ a, s a a = 1)
    (hQ : ∀ a b, a ≠ b → Q a b = MvPolynomial.C ((s a b * s b a : kˣ) : k) * Qd a b)
    (z : TensorProductAlgebra k Q exponents ν) :
    rescaledToDownwardMatrix P exponents scalars (ν := {i} + ν) Q Qd hs hQ
        (appendBlack Q exponents i ν z) =
      blackMatrix (addRedUpRelations RD labels k (addMixedBlackRelations RD labels k scalars
          (addDownRelations RD labels (affineCoverQ Qd exponents) P))) i
        (rescaledToDownwardMatrix P exponents scalars Q Qd hs hQ z) := by
  simp only [rescaledToDownwardMatrix, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [tensorRescale_appendBlack, ordinaryToDownwardMatrix_appendBlack]

/-- **The matrix map of `Fᵢ` and the repaired Lemma 4.29** (arXiv:1309.3796v3): the
comparison at the Cautis–Lauda parameters intertwines adjoining a black strand to `T^λ` with
the matrix map of `Fᵢ` on the all-down block. -/
theorem clToDownwardMatrix_appendBlack (S : KL3.Diagram.CL.CLScalars C k)
    (z : TensorProductAlgebra k (KL3.Diagram.CL.qCL S) exponents ν) :
    clToDownwardMatrix P exponents scalars (ν := {i} + ν) S
        (appendBlack (KL3.Diagram.CL.qCL S) exponents i ν z) =
      blackMatrix (addRedUpRelations RD labels k (addMixedBlackRelations RD labels k scalars
          (addDownRelations RD labels (affineCoverQ (clDownwardQ S) exponents) P))) i
        (clToDownwardMatrix P exponents scalars S z) :=
  rescaledToDownwardMatrix_appendBlack P (KL3.Diagram.CL.qCL S) exponents scalars i ν _ _ _ z

end Categorification.Stendhal.DoubleDiagram
