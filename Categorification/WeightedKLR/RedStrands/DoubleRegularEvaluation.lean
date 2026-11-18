/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleDownComparison
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Regular-module detection of ordinary diagrams in the signed corner

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, pp. 42–43. The final
step evaluates the signed action at the weight-zero identity. If the resulting
operators are ordinary left multiplications on the generating diagrams, the
entire ordinary action is left regular and evaluation at the unit detects its
kernel. This criterion leaves the construction of the signed action as an input.
The cited injectivity argument is the one revised in version 3; arXiv:1309.3796v2,
§4.5, Lemma 4.28, argues via Lemma 4.26 instead.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR KLR.Diagram KLRAlgebra
open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type w} [CommRing k]
  (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λ)) k)
  (Q : I → I → MvPolynomial (Fin 2) k) (exponents : Fin ℓ → I →₀ ℕ)
  (scalars : I → I → kˣ) (ν : Multiset I)

local notation "μ" => stendhalWeight ℓ ν
local notation "R" => affineCoverQ Q exponents
local notation "P↓" => addDownRelations RD (Subtype.val ∘ Λ) R P
local notation "B" => addRedUpRelations RD (Subtype.val ∘ Λ) k
  (addMixedBlackRelations RD (Subtype.val ∘ Λ) k scalars P↓)
local notation "T" => TensorProductAlgebra k Q exponents ν
local notation "π" => affineTensorProjection (Q := Q) exponents ν
local notation "f" => ordinaryToDownwardMatrix P Q exponents scalars (ν := ν)

/-- It suffices for the signed operator on the regular module to have the
correct value on each of the three families of ordinary generators. -/
theorem ordinaryToDownwardMatrix_regularAction
    (act : downwardMatrix B ν →ₐ[k] Module.End k T)
    (he : ∀ s : Seq μ, act (downE B s) = Algebra.lmul k T (π (e s)))
    (hx : ∀ a : Fin (Multiset.card μ), act (downX B a) = Algebra.lmul k T (π (x a)))
    (hψ : ∀ j : ℕ, act (downΨ B (ν := ν) j) = Algebra.lmul k T (π (ψ j))) :
    act.comp f = Algebra.lmul k T := by
  classical
  have h : (act.comp f).comp π = (Algebra.lmul k T).comp π := by
    apply RingQuot.ringQuot_ext'
    apply FreeAlgebra.hom_ext
    funext g
    cases g with
    | idem s =>
      change act (f (π (e s))) = _
      rw [ordinaryToDownwardMatrix_e]
      exact he s
    | dot a =>
      change act (f (π (x a))) = _
      rw [ordinaryToDownwardMatrix_x]
      exact hx a
    | cross j =>
      change act (f (π (ψ j))) = _
      rw [ordinaryToDownwardMatrix_ψ]
      exact hψ j
  apply AlgHom.ext
  intro a
  obtain ⟨z, rfl⟩ := affineTensorProjection_surjective exponents ν a
  exact DFunLike.congr_fun h z

/-- Evaluating the ordinary diagram operator at the unit detects its class.
The hypotheses are generator checks on a signed action, as in the last
paragraph of Webster's proof of Lemma 4.29. -/
theorem ordinaryToDownwardMatrix_injective_of_regularAction
    (act : downwardMatrix B ν →ₐ[k] Module.End k T)
    (he : ∀ s : Seq μ, act (downE B s) = Algebra.lmul k T (π (e s)))
    (hx : ∀ a : Fin (Multiset.card μ), act (downX B a) = Algebra.lmul k T (π (x a)))
    (hψ : ∀ j : ℕ, act (downΨ B (ν := ν) j) = Algebra.lmul k T (π (ψ j))) :
    Function.Injective f := by
  have h := ordinaryToDownwardMatrix_regularAction P Q exponents scalars ν act he hx hψ
  intro a b hab
  apply (Algebra.lmul_injective : Function.Injective (Algebra.lmul k T))
  exact (DFunLike.congr_fun h a).symm.trans ((congrArg act hab).trans (DFunLike.congr_fun h b))

end Categorification.Stendhal.DoubleDiagram
