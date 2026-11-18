/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDownComparison
import Categorification.WeightedKLR.RedStrands.DoubleDownScalars
import Categorification.WeightedKLR.RedStrands.TensorRescale

/-!
# The all-down comparison with Cautis–Lauda downward relations

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §4.5,
Lemma 4.28 (Lemma 4.29 in v3). With Webster's pitchforks (2.2a), the downward KLR
relations of (2.5e) are inconsistent (`DoubleDiagram.printedPitchfork_no_injection`).
The repair records the downward relations with the Cautis–Lauda dual parameters
(Cautis–Lauda, arXiv:1111.1431v3, §2.2): after the reflection of `DoubleBlackDiagram`,
the downward crossings satisfy the KLR relations for
`Q↓ i j = (t_ij t_ji)⁻¹ Q i j` (`reflectedDownward_qCL`).

The comparison is the composite of the crossing rescaling `T^λ(Q) ≅ T^λ(Q↓)` with
the ordinary all-down map at the parameters `Q↓`. It sends each idempotent and dot to the
same diagram, and multiplies each black crossing `ψ_j e(i)` by `t(i_j, i_{j+1})`.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory MvPolynomial QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLR.Diagram
  KL3.Diagram.CL
open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (exponents : Fin ℓ → I →₀ ℕ) (scalars : I → I → kˣ) {ν : Multiset I}

/-- The all-down comparison of arXiv:1309.3796v2, Lemma 4.28, with downward relations at
parameters `Qd` related to `Q` by `Q a b = s a b * s b a * Qd a b`: rescale the black
crossings of `T^λ(Q)` and apply the ordinary comparison at `Qd`. -/
def rescaledToDownwardMatrix (Q Qd : I → I → MvPolynomial (Fin 2) k) {s : I → I → kˣ}
    (hs : ∀ a, s a a = 1) (hQ : ∀ a b, a ≠ b → Q a b = MvPolynomial.C ((s a b * s b a : kˣ) : k) * Qd a b) :
    TensorProductAlgebra k Q exponents ν →ₐ[k]
      downwardMatrix (addRedUpRelations RD (Subtype.val ∘ Λ) k
        (addMixedBlackRelations RD (Subtype.val ∘ Λ) k scalars
          (addDownRelations RD (Subtype.val ∘ Λ) (affineCoverQ Qd exponents) P))) ν :=
  (ordinaryToDownwardMatrix P Qd exponents scalars).comp
    (tensorRescale exponents ν hs hQ).toAlgHom

theorem rescaledToDownwardMatrix_e (Q Qd : I → I → MvPolynomial (Fin 2) k) {s : I → I → kˣ}
    (hs : ∀ a, s a a = 1) (hQ : ∀ a b, a ≠ b → Q a b = MvPolynomial.C ((s a b * s b a : kˣ) : k) * Qd a b)
    (t : Seq (stendhalWeight ℓ ν)) :
    rescaledToDownwardMatrix P exponents scalars Q Qd hs hQ
        (affineTensorProjection exponents ν (KLRAlgebra.e t)) =
      downE (addRedUpRelations RD (Subtype.val ∘ Λ) k
        (addMixedBlackRelations RD (Subtype.val ∘ Λ) k scalars
          (addDownRelations RD (Subtype.val ∘ Λ) (affineCoverQ Qd exponents) P))) t := by
  rw [rescaledToDownwardMatrix, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, tensorRescale_e,
    ordinaryToDownwardMatrix_e]

theorem rescaledToDownwardMatrix_x (Q Qd : I → I → MvPolynomial (Fin 2) k) {s : I → I → kˣ}
    (hs : ∀ a, s a a = 1) (hQ : ∀ a b, a ≠ b → Q a b = MvPolynomial.C ((s a b * s b a : kˣ) : k) * Qd a b)
    (a : Fin (stendhalWeight ℓ ν).card) :
    rescaledToDownwardMatrix P exponents scalars Q Qd hs hQ
        (affineTensorProjection exponents ν (KLRAlgebra.x a)) =
      downX (addRedUpRelations RD (Subtype.val ∘ Λ) k
        (addMixedBlackRelations RD (Subtype.val ∘ Λ) k scalars
          (addDownRelations RD (Subtype.val ∘ Λ) (affineCoverQ Qd exponents) P))) a := by
  rw [rescaledToDownwardMatrix, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, tensorRescale_x,
    ordinaryToDownwardMatrix_x]

/-- The Cautis–Lauda downward parameters, read in the reflected black diagrams:
`Q↓ i j = (t_ij t_ji)⁻¹ Q_ij` (Cautis–Lauda, arXiv:1111.1431v3, §2.2). -/
def clDownwardQ (S : CLScalars C k) (i j : I) : MvPolynomial (Fin 2) k :=
  rename ![(1 : Fin 2), 0] (qCL S.dual j i)

/-- **The repaired comparison of arXiv:1309.3796v2, Lemma 4.28 (v3 Lemma 4.29).**
Webster's `T^λ` at the Cautis–Lauda parameters `Q_ij` maps to the all-down block whose
downward relations use the Cautis–Lauda dual parameters. It fixes idempotents and dots and
rescales the black crossing `ψ_j e(i)` by `t(i_j, i_{j+1})`. -/
def clToDownwardMatrix (S : CLScalars C k) :
    TensorProductAlgebra k (qCL S) exponents ν →ₐ[k]
      downwardMatrix (addRedUpRelations RD (Subtype.val ∘ Λ) k
        (addMixedBlackRelations RD (Subtype.val ∘ Λ) k scalars
          (addDownRelations RD (Subtype.val ∘ Λ) (affineCoverQ (clDownwardQ S) exponents) P))) ν :=
  rescaledToDownwardMatrix P exponents scalars (qCL S) (clDownwardQ S) S.t_self
    fun a b _ => (rescaledDownward_qCL S a b).symm

end Categorification.Stendhal.DoubleDiagram
