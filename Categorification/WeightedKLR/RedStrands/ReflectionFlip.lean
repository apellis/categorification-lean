/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AppendStrandReflection

/-!
# The two descriptions of horizontal reflection agree

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §4: the
graded anti-involution `tensorReflection` of `T^λ` and the anti-automorphism `tensorFlip` are both
induced by horizontal reflection of KLR diagrams, so they are equal.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

theorem tensorReflection_projection (G : GradingDatum (stendhalQ Q Λ))
    (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a)
    (a : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)) :
    tensorReflection (ν := ν) G hsymm (stendhalTensorProjection (Q := Q) Λ ν a) =
      stendhalTensorProjection (Q := Q) Λ ν (hflip a) :=
  congrArg unop (DFunLike.congr_fun (tensorRepresentationLift_comp _ _) a)

/-- Horizontal reflection, as a graded anti-involution, is `tensorFlip`. -/
theorem tensorReflection_apply (G : GradingDatum (stendhalQ Q Λ))
    (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a) (z : TensorProductAlgebra k Q Λ ν) :
    tensorReflection (ν := ν) G hsymm z = tensorFlip z := by
  obtain ⟨a, rfl⟩ := stendhalTensorProjection_surjective (Q := Q) (Λ := Λ) (ν := ν) z
  rw [tensorReflection_projection, tensorFlip_projection]

end Categorification.Stendhal
