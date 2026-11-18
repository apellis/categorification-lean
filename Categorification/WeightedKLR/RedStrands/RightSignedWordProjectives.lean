/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.EqualBlackProjectives
import Categorification.WeightedKLR.RedStrands.RightBoundaryProjectives

/-!
# Signed-word decompositions of right projectives

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.35.
Horizontal reflection carries shifted copies of the deletion projective
to shifted copies of the right deletion projective.
-/

noncomputable section

namespace Categorification.Stendhal

open Categorification.Graded FirstWeight

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
    (ψ : GradedAntiInvolution 𝒜)

/-- Right twisting takes a sum of shifted projectives to the same sum of shifted
right projectives. -/
def rightTwistSumShiftsIso (P : GProj 𝒜) (s : ℕ → ℤ) (n : ℕ) :
    ((sumShifts P s n).rightTwist ψ).Iso (sumShifts (P.rightTwist ψ) s n) := by
  induction n with
  | zero =>
    change ((GProj.zeroObj 𝒜).rightTwist ψ).Iso (GProj.zeroObj (oppositeGrade 𝒜))
    letI : Subsingleton ((GProj.zeroObj 𝒜).rightTwist ψ).carrier :=
      inferInstanceAs (Subsingleton (GProj.zeroObj 𝒜).carrier)
    exact GProj.isoOfSubsingleton _ _
  | succ n ih =>
    let e : ((P.shift (s n)).rightTwist ψ).Iso ((P.rightTwist ψ).shift (s n)) :=
      GMod.rightTwistShiftIso ψ P.toGMod (s n)
    exact (GMod.rightTwistProdIso ψ (sumShifts P s n).toGMod (P.shift (s n)).toGMod).trans
      (GProj.prodCongrIso ih e)

/-- Transport a signed-word decomposition of the kind in Webster,
arXiv:1309.3796v2, Lemma 4.35, to graded right projectives, with the same
degree shifts on the copies of the projective obtained by deletion. -/
theorem rightTwistWordDecomposition {P Q D : GProj 𝒜} {s : ℕ → ℤ} {n : ℕ}
    (h : Nonempty (P.Iso (Q.prod (sumShifts D s n)))) :
    Nonempty ((P.rightTwist ψ).Iso ((Q.rightTwist ψ).prod (sumShifts (D.rightTwist ψ) s n))) :=
  h.map fun e =>
    let f : (Q.rightTwist ψ).Iso (Q.rightTwist ψ) := GradedEquiv.refl _
    (GMod.rightTwistIso ψ e).trans
      ((GMod.rightTwistProdIso ψ Q.toGMod (sumShifts D s n).toGMod).trans
        (GProj.prodCongrIso f (rightTwistSumShiftsIso ψ D s n)))

end Categorification.Stendhal
