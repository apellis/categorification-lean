/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidClassMap
import Categorification.WeightedKLR.RedStrands.GradedBraidResolution

/-!
# The braid class map on braid-concentrated modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Corollary 6.10. If `N` has a finite projective resolution `P_•` and its derived braid
`N ⊗ᴸ B` is concentrated in degree zero, then `braidClass σ (η Σ (-1)^j [P_j])` is the class
functional of `𝔅_σ N` (`braidClass_resolution_of_braidConcentrated`).
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF MulOpposite Equiv
open scoped RatFunc
open DG DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra
local notation "LP" => LaurentPolynomial ℤ

universe w

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]
    (σ : Perm (Fin ℓ)) (ν : Multiset I)

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2)
  (dotDegree C hQ)
local notation "Kr" => rightTensorProjectiveGroup C hQ Λ
local notation "η'" => rightTensorModuleEquiv C hQ hR Λ wt hwt
local notation "𝒜" ν => oppositeGrade (tensorProductGrade G ν)
local notation "cf'" => classFunctional C hQ hR (Λ ∘ σ) (wt ∘ σ) (fun r i => hwt (σ r) i)

variable [HasDerivedCategory.{w} (IsIdempotentElem.Corner
    (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj k Q Λ ν (List.finRange ℓ)))ᵐᵒᵖ]
  [HasDerivedCategory.{w} (IsIdempotentElem.Corner
    (BraidedStendhalAlgebra.isIdempotentElem_violMk_redProj k Q Λ ν
      (List.map σ (List.finRange ℓ))))ᵐᵒᵖ]

/-- **The braid class map on a braid-concentrated module** (Webster, arXiv:1309.3796v2, proof of
Corollary 6.10): if `N` has a finite projective resolution `P_•` and `N ⊗ᴸ B` has no cohomology
outside degree zero, then `braidClass σ (η Σ (-1)^j [P_j]) = classFunctional (𝔅_σ N)`. -/
theorem braidClass_resolution_of_braidConcentrated {N : GFin (𝒜 ν)}
    {Ps : List (GProj (𝒜 ν))} (r : GFin.Resolution N (Ps.map GProj.toGFin))
    (hN : BraidedStendhalAlgebra.BraidConcentrated.{w} Λ ν (isReducedChoice_canChoice ν)
      hQ.klrSymm σ hQ N) :
    braidClass C hQ hR Λ wt hwt σ
        (η' (altSum (Ps.map fun P => DirectSum.lof LP _ Kr ν (K0.of P)))) =
      ConjDual.of (cf' ν (braidF C hQ Λ σ ν N)) :=
  braidClass_resolution C hQ hR Λ wt hwt σ ν r
    (BraidedStendhalAlgebra.preserved_of_braidConcentrated.{w} _ _ σ hQ r hN fun P hP => by
      obtain ⟨P', _, rfl⟩ := List.mem_map.mp hP
      have : Module.Projective (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ P'.toGFin.carrier := P'.projective
      exact BraidedStendhalAlgebra.braidConcentrated_of_projective.{w} _ _ σ hQ P'.toGFin)

end Categorification.Stendhal.FirstWeight
