/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidFactorizationCoend
import Categorification.WeightedKLR.RedStrands.BraidingAuxiliaryDerived
import Categorification.Algebra.DiagramWeightCornerComp
import Categorification.WeightedKLR.RedStrands.BraidingFunctorCompose

set_option backward.isDefEq.respectTransparency false

/-!
# Composites of the graded braiding functors

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Lemma 6.12,
second clause, for the graded braiding functors of Definition 6.6: when the inversions of the
red orders `upper, middle, lower` add and the higher `Tor` of `B(middle, lower)` against the
rows of `B(upper, middle)` vanish, `𝔅(upper, middle) ⋙ 𝔅(middle, lower) ≅ 𝔅(upper, lower)`
in the auxiliary grading (`auxiliaryGradedBraidingFunctorCompIso`), under the same ungraded
`Tor`-vanishing hypothesis `hv` as `braidingFunctorCompIso`: forgetting the weights reflects
quasi-isomorphisms, so the graded `Tor` condition follows from the ungraded one. For
permutations whose lengths add, the ungraded `Tor` vanishing of Lemma 6.11 gives the graded
composite with the route hypotheses of `braidingFunctorCompIsoOfLengthAdd`
(`auxiliaryGradedBraidingFunctorCompIsoOfLengthAdd`).
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA Equiv CategoryTheory DG QuantumGroup
open scoped List DG.DegreeZero

universe u

variable {I : Type} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  {lower middle upper : List (Fin ℓ)}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight ℓ ν))) → List ℕ}
  (C : CartanDatum I) (hQ : IsRouquierQ C Q)

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

local notation "hE" κ:arg => isIdempotentElem_violMk_redProj k Q Λ ν κ
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (UDot.di C)
  (fun i => Eq.trans (IsRouquierQ.gradingDatum_degX hQ i) (Eq.symm (UDot.two_mul_di C i)))
local notation "V" => violAuxiliaryGrade (ν := ν) G
local notation "H₀" κ:arg => redProj_mem_violAuxiliaryGrade (ν := ν) G κ
local notation "S" κ:arg => Graded.oppositeGrade (Graded.cornerGrading V (hE κ))

/-- **Webster, Lemma 6.12, second clause, for the graded braiding functors of Definition 6.6**
(arXiv:1309.3796v3), red-order form: when the inversions of `upper, middle, lower` add and
`Tor_{>0}(B(upper, middle), B(middle, lower)) = 0` (ungraded, as in `braidingFunctorCompIso`),
the graded braiding functors compose, `𝔅(upper, middle) ⋙ 𝔅(middle, lower) ≅ 𝔅(upper, lower)`
in the auxiliary grading. -/
def auxiliaryGradedBraidingFunctorCompIso (hρ : IsReducedChoice ρ)
    (h0 : lower.Nodup) (hp : lower.Perm middle)
    (H : ∀ x y, [x, y] <+ lower → [y, x] <+ middle → [y, x] <+ upper) :
    letI := Graded.cornerGradedAlgebra V (hE upper) (H₀ upper)
    letI := Graded.cornerGradedAlgebra V (hE middle) (H₀ middle)
    letI := Graded.cornerGradedAlgebra V (hE lower) (H₀ lower)
    letI := gradedAlgebraInternalGrading (S upper)
    letI := gradedAlgebraInternalGrading (S middle)
    letI := gradedAlgebraInternalGrading (S lower)
    letI := gradedAlgebraBigradedDGRing (S upper)
    letI := gradedAlgebraBigradedDGRing (S middle)
    letI := gradedAlgebraBigradedDGRing (S lower)
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory (hE upper).Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory (hE middle).Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{u,u} (WeightCategory (hE lower).Cornerᵐᵒᵖ)] →
    [DG.HasDerivedCategory.{u,u} (hE upper).Cornerᵐᵒᵖ] →
    [DG.HasDerivedCategory.{u,u} (hE middle).Cornerᵐᵒᵖ] →
    [DG.HasDerivedCategory.{u,u} (hE lower).Cornerᵐᵒᵖ] →
    (∀ n : ℤ, n ≠ 0 → Limits.IsZero
      ((DG.DerivedCategory.homologyFunctor (A := (hE lower).Cornerᵐᵒᵖ) ℤ n).obj
        ((braidingFunctor.{u} k Q Λ ν middle lower).obj
          (DG.DerivedCategory.Q.obj (DGModuleCat.of (hE middle).Cornerᵐᵒᵖ
            (cornerOpDZ (hE upper) (violMk k Q Λ ν (redProj k Q Λ ν middle)))))))) →
    (Iso (C := CatModule.DerivedCategory.{u,u} (WeightCategory (hE upper).Cornerᵐᵒᵖ) ⥤
        CatModule.DerivedCategory.{u,u} (WeightCategory (hE lower).Cornerᵐᵒᵖ))
      (Functor.comp
        (C := CatModule.DerivedCategory.{u,u} (WeightCategory (hE upper).Cornerᵐᵒᵖ))
        (D := CatModule.DerivedCategory.{u,u} (WeightCategory (hE middle).Cornerᵐᵒᵖ))
        (E := CatModule.DerivedCategory.{u,u} (WeightCategory (hE lower).Cornerᵐᵒᵖ))
        (auxiliaryGradedBraidingFunctor.{u} G upper middle)
        (auxiliaryGradedBraidingFunctor.{u} G middle lower))
      (auxiliaryGradedBraidingFunctor.{u} G upper lower)) := by
  letI := Graded.cornerGradedAlgebra V (hE upper) (H₀ upper)
  letI := Graded.cornerGradedAlgebra V (hE middle) (H₀ middle)
  letI := Graded.cornerGradedAlgebra V (hE lower) (H₀ lower)
  letI := gradedAlgebraInternalGrading (S upper)
  letI := gradedAlgebraInternalGrading (S middle)
  letI := gradedAlgebraInternalGrading (S lower)
  letI := gradedAlgebraBigradedDGRing (S upper)
  letI := gradedAlgebraBigradedDGRing (S middle)
  letI := gradedAlgebraBigradedDGRing (S lower)
  intro _ _ _ _ _ _ hv
  exact diagramCornerWeightDerivedRightTensorCompIso V (hE upper) (hE middle) (hE lower)
    (H₀ upper) (H₀ middle) (H₀ lower)
    (diagramCornerWeight_isInternal V (H₀ middle) (H₀ lower))
    (diagramCornerWeight_isInternal V (H₀ upper) (H₀ middle))
    (diagramCornerWeight_isInternal V (H₀ upper) (H₀ lower))
    (braidFactorizationCoend_bijective C hQ hρ h0 hp H) hv

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.FirstWeight

open KLR Categorification.Graded QuantumGroup LieLean.QuantumGroup.GrandLoop Equiv
open BraidedStendhalAlgebra CategoryTheory DG
open scoped List DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ}
  [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I), Module.Finite k (TensorProductAlgebra k Q Ω ν)]
  [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (κ : List (Fin ℓ)),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Ω) (ν := ν) κ)]
  [∀ (Ω : Fin ℓ → I →₀ ℕ) (ν : Multiset I) (κ : List (Fin ℓ)),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k) (Q := Q) (Λ := Ω) (ν := ν) κ)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} ℤ]

local notation "G" Λ:arg => stendhalGradingDatum Λ hQ.gradingDatum (UDot.di C)
  (fun i => Eq.trans (IsRouquierQ.gradingDatum_degX hQ i) (Eq.symm (UDot.two_mul_di C i)))
local notation "V" Λ:arg ν:arg => violAuxiliaryGrade (ν := ν) (G Λ)
local notation "hE" Λ:arg ν:arg κ:arg => isIdempotentElem_violMk_redProj k Q Λ ν κ
local notation "H₀" Λ:arg ν:arg κ:arg => redProj_mem_violAuxiliaryGrade (ν := ν) (G Λ) κ
local notation "S" Λ:arg ν:arg κ:arg =>
  Graded.oppositeGrade (Graded.cornerGrading (V Λ ν) (hE Λ ν κ))

include hR in
/-- **Webster, Lemma 6.12, second clause, for the graded braiding functors of Definition 6.6**
(arXiv:1309.3796v3), red-order form: for permutations `τ` and `s ≠ 1` of the red strands whose
lengths add, `𝔅((1, …, ℓ), τ) ⋙ 𝔅(τ, τ s) ≅ 𝔅((1, …, ℓ), τ s)` in the auxiliary grading.
Webster's statement is the case of an adjacent transposition `s`. Route hypotheses: those of the
ungraded `braidingFunctorCompIsoOfLengthAdd` (Corollary 6.10, through Lemma 6.11). -/
def auxiliaryGradedBraidingFunctorCompIsoOfLengthAdd
    (hall : ∀ (n : ℕ) (Λ' : Fin (n + 1) → I →₀ ℕ), AllFiniteDeltaInjective Q Λ' hQ.klrSymm)
    (H : ∀ (n m : ℕ), n + 2 + m = ℓ → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
      (u : Fin (n + 2 + m) → List I) (hu : u (rightPos n m) = []),
      RowFigureFiveHypotheses C hQ Ω u hu)
    (Λ : Fin ℓ → I →₀ ℕ) (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    (ν : Multiset I) (τ s : Perm (Fin ℓ)) (hs : s ≠ 1)
    (hL : ∀ x y, [x, y] <+ (List.finRange ℓ).map ⇑(τ * s) → [y, x] <+ (List.finRange ℓ).map τ →
      [y, x] <+ List.finRange ℓ) :
    letI := Graded.cornerGradedAlgebra (V Λ ν) (hE Λ ν (List.finRange ℓ))
      (H₀ Λ ν (List.finRange ℓ))
    letI := Graded.cornerGradedAlgebra (V Λ ν) (hE Λ ν ((List.finRange ℓ).map τ))
      (H₀ Λ ν ((List.finRange ℓ).map τ))
    letI := Graded.cornerGradedAlgebra (V Λ ν) (hE Λ ν ((List.finRange ℓ).map ⇑(τ * s)))
      (H₀ Λ ν ((List.finRange ℓ).map ⇑(τ * s)))
    letI := gradedAlgebraInternalGrading (S Λ ν (List.finRange ℓ))
    letI := gradedAlgebraInternalGrading (S Λ ν ((List.finRange ℓ).map τ))
    letI := gradedAlgebraInternalGrading (S Λ ν ((List.finRange ℓ).map ⇑(τ * s)))
    letI := gradedAlgebraBigradedDGRing (S Λ ν (List.finRange ℓ))
    letI := gradedAlgebraBigradedDGRing (S Λ ν ((List.finRange ℓ).map τ))
    letI := gradedAlgebraBigradedDGRing (S Λ ν ((List.finRange ℓ).map ⇑(τ * s)))
    [CatModule.HasDerivedCategory.{0, 0}
      (WeightCategory (hE Λ ν (List.finRange ℓ)).Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{0, 0}
      (WeightCategory (hE Λ ν ((List.finRange ℓ).map τ)).Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{0, 0}
      (WeightCategory (hE Λ ν ((List.finRange ℓ).map ⇑(τ * s))).Cornerᵐᵒᵖ)] →
    (Iso (C := CatModule.DerivedCategory.{0, 0}
        (WeightCategory (hE Λ ν (List.finRange ℓ)).Cornerᵐᵒᵖ) ⥤
        CatModule.DerivedCategory.{0, 0}
          (WeightCategory (hE Λ ν ((List.finRange ℓ).map ⇑(τ * s))).Cornerᵐᵒᵖ))
      (Functor.comp
        (C := CatModule.DerivedCategory.{0, 0}
          (WeightCategory (hE Λ ν (List.finRange ℓ)).Cornerᵐᵒᵖ))
        (D := CatModule.DerivedCategory.{0, 0}
          (WeightCategory (hE Λ ν ((List.finRange ℓ).map τ)).Cornerᵐᵒᵖ))
        (E := CatModule.DerivedCategory.{0, 0}
          (WeightCategory (hE Λ ν ((List.finRange ℓ).map ⇑(τ * s))).Cornerᵐᵒᵖ))
        (auxiliaryGradedBraidingFunctor.{0} (G Λ) (List.finRange ℓ) ((List.finRange ℓ).map τ))
        (auxiliaryGradedBraidingFunctor.{0} (G Λ) ((List.finRange ℓ).map τ)
          ((List.finRange ℓ).map ⇑(τ * s))))
      (auxiliaryGradedBraidingFunctor.{0} (G Λ) (List.finRange ℓ)
        ((List.finRange ℓ).map ⇑(τ * s)))) :=
  auxiliaryGradedBraidingFunctorCompIso C hQ (isReducedChoice_canChoice ν)
    ((List.nodup_finRange ℓ).map (τ * s).injective)
    ((List.perm_ext_iff_of_nodup ((List.nodup_finRange ℓ).map (τ * s).injective)
      ((List.nodup_finRange ℓ).map τ.injective)).2 fun a => by
        simp only [List.mem_map, List.mem_finRange, true_and]
        exact ⟨fun _ => ⟨τ.symm a, τ.apply_symm_apply a⟩,
          fun _ => ⟨(τ * s).symm a, (τ * s).apply_symm_apply a⟩⟩) hL
    (isZero_braidingFunctor_homology_of_lengthAdd C hQ hR hall H Λ wt hwt ν τ s hs)

end Categorification.Stendhal.FirstWeight
