/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RightRowStandardGenerator
import Categorification.WeightedKLR.RedStrands.RowFigureFiveBraid
import Categorification.WeightedKLR.RedStrands.GradedBraidResolutionClass
import Categorification.WeightedKLR.RedStrands.RightStandardProjectiveDimension
import Categorification.Algebra.Graded.FiniteResolution

set_option backward.isDefEq.respectTransparency false

/-!
# The class of the braid of a right row standard module

Part of the proof of Webster, arXiv:1309.3796v2, §6.1, Corollary 6.10. The class functional of
the right standard module at the row loading of `u` is the form against the word tensor of `u`
(`classFunctional_rightRowStandard_eq`). For `n + 2 + m` red strands and `u_{n+2}` empty, the
braid functor along the transposition `π` of `λ_{n+1}, λ_{n+2}` sends the word tensor of `u` to
the form against `v^{-(⟨|u_{n+1}|, λ_{n+2}⟩ - 2)}` times the word tensor of the swapped words
(`braidClass_wordTensor`). Hypotheses: the route hypothesis `AllFiniteDeltaInjective` of
Corollary 5.22 and those of Proposition 6.9 at the row of `u` (`RowFigureFiveHypotheses`).
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ
local notation "𝕂" => RatFunc ℚ

section Class

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2)
  (dotDegree C hQ)
local notation "Kr" => rightTensorProjectiveGroup C hQ Λ
local notation "η" => tensorModuleEquiv C hQ hR Λ wt hwt
local notation "η'" => rightTensorModuleEquiv C hQ hR Λ wt hwt
local notation "B" => TensorPairing.orderedForm hR wt

variable [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]

/-- **Proposition 5.6 for right row standards, as functionals** (Webster, arXiv:1309.3796v2,
Definition 5.1 and Proposition 5.6): the class functional of the right standard module at the
row loading of `u` is `B(F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_ℓ} v_{λ_ℓ}, -)`. -/
theorem classFunctional_rightRowStandard_eq (u : Fin ℓ → List I) :
    classFunctional C hQ hR Λ wt hwt (blockContent u) (rightRowStandard C hQ Λ u) =
      B (wordTensor C wt u) := by
  have key : ∀ x : DirectSum (Multiset I) Kr,
      classFunctional C hQ hR Λ wt hwt (blockContent u) (rightRowStandard C hQ Λ u) (η' x) =
        B (wordTensor C wt u) (η' x) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero, ZeroMemClass.coe_zero]
    | add x y hx hy => rw [map_add, Submodule.coe_add, map_add, map_add, hx, hy]
    | of γ y =>
      rw [← DirectSum.lof_eq_of LP]
      by_cases hγ : blockContent u = γ
      · subst hγ
        exact classFunctional_rightRowStandard C hQ hR Λ wt hwt u y
      · obtain ⟨y', rfl⟩ := (K0.rightTwistEquiv (tensorReflectionG C hQ Λ γ)).surjective y
        rw [classFunctional_eta, rightTensorModuleEquiv_lof_rightTwist,
          orderedForm_wordTensor_block C hQ hR Λ wt hwt u hγ y',
          DirectSum.lof_eq_of, DirectSum.of_eq_of_ne γ (blockContent u) _ hγ,
          map_zero, map_zero]
  refine Lattice.ext_of_lattice (isLattice_integralTensor C hR wt) fun z hz => ?_
  obtain ⟨x, hx⟩ := (η').surjective ⟨z, hz⟩
  have hzx : z = (η' x : TensorSpace wt) := by rw [hx]
  rw [hzx]
  exact key x

/-- The class functional of a right standard module does not see a transport of its black
content. -/
theorem classFunctional_rightStandard_cast {ν ν' : Multiset I} (hν : ν' = ν)
    (s : Seq (stendhalWeight ℓ ν')) (hs : redWord s = List.finRange ℓ)
    (hs' : redWord (KLR.Seq.cast (congrArg (stendhalWeight ℓ) hν) s) = List.finRange ℓ) :
    classFunctional C hQ hR Λ wt hwt ν (BraidedStendhalAlgebra.rightStandard
        (isReducedChoice_canChoice ν) hQ.klrSymm (KLR.Seq.cast (congrArg (stendhalWeight ℓ) hν) s)
        G hs') =
      classFunctional C hQ hR Λ wt hwt ν' (BraidedStendhalAlgebra.rightStandard
        (isReducedChoice_canChoice ν') hQ.klrSymm s G hs) := by
  subst hν
  rfl

omit [Finite I] in
/-- Corollary 5.22 gives the right row standard a finite graded projective resolution. -/
theorem exists_resolution_rightRowStandard
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ.klrSymm)
    (u : Fin ℓ → List I) :
    ∃ Ps : List (GProj (oppositeGrade (tensorProductGrade G (blockContent u)))),
      Nonempty (GFin.Resolution (rightRowStandard C hQ Λ u) (Ps.map GProj.toGFin)) := by
  obtain ⟨N, hN⟩ := BraidedStendhalAlgebra.exists_hasProjectiveDimensionLT_rightStandard
    (Λ := Λ) (isReducedChoice_canChoice _) hQ.klrSymm hQ hall (isRedOrdered_rowLoading ℓ u)
  have : CategoryTheory.HasProjectiveDimensionLT
      (ModuleCat.of _ (rightRowStandard C hQ Λ u).carrier) N := hN
  exact GFin.exists_resolution_of_hasProjectiveDimensionLT N (rightRowStandard C hQ Λ u)
    (CategoryTheory.hasProjectiveDimensionLT_of_ge (X := ModuleCat.of _
      (rightRowStandard C hQ Λ u).carrier) (n := N) (N + 1) (Nat.le_succ N))

end Class

end Categorification.Stendhal.FirstWeight
