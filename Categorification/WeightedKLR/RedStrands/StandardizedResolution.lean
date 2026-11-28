/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedStandardizationExact
import Categorification.WeightedKLR.RedStrands.StandardizedProjectiveDimension
import Categorification.Algebra.Graded.UpResolutionProjDim

/-!
# Standardization of resolutions in `C↑`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 5.28 (step for several red strands): for Rouquier parameters and nonnegative dot degrees,
if a finite graded module `N` over `T^{λ'}_θ ⊗ R^{λ_ℓ}_β` has a graded projective resolution in
`C↑`, so does its standardization `S(N)` over `T^λ_{θ+β}`, with a constant shifted by an amount
depending only on `θ` and `β` (`exists_upResolution_standardizationGFin`).

Standardization is exact (Proposition 5.7), so it turns a resolution `P_• → N` into an exact
complex `S(P_•) → S(N)`. Each `S(P_n)` has projective dimension below a bound independent of `n`
(`exists_hasProjectiveDimensionLT_stdOf_projective`) and vanishes below degree `n - c + b`
(`exists_standardizationGFin_grading_eq_bot`), so it has a resolution in `C↑` with constant
`C₀ + c - n` (`GFin.UpResolution.exists_of_hasProjectiveDimensionLT`); the total complex
(`GFin.UpResolution.ofResolution`) resolves `S(N)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR KLRAlgebra Categorification.Graded DirectSum
open scoped TensorProduct Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin (ℓ+1) → I →₀ ℕ)
  (G : GradingDatum (stendhalQ Q Λ)) (θ β : Multiset I) (hsym : KLRSymm Q)

local notation "D" => parabolicFactorAlgebra Q Λ θ β
local notation "T" => TensorProductAlgebra k Q Λ (θ + β)
local notation "𝓓" => tensorGrading (tensorProductGrade (restrictRedGrading Q Λ G) θ)
  (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β)

/-- The graded standardization of `N`, as the standardization `S(N)` of `stdOf`. -/
def standardizationStdOfEquiv (N : GFin 𝓓) :
    (standardizationGFin Λ G θ β hsym N).carrier ≃ₗ[T]
      stdOf Q Λ hsym θ β (ModuleCat.of D N.carrier) :=
  let f : (standardizationGFin Λ G θ β hsym N).carrier →ₗ[T]
      stdOf Q Λ hsym θ β (ModuleCat.of D N.carrier) :=
    { toFun := parabolicStandardMap Q Λ θ β
        (show N.carrier →ₗ[D] KMod (k := k) (ModuleCat.of D N.carrier) from LinearMap.id)
      map_add' := map_add _
      map_smul' := fun t z => parabolicStandardMap_action Q Λ θ β hsym _ t z }
  LinearEquiv.ofBijective f
    ⟨parabolicStandardMap_injective Q Λ θ β hsym _ fun _ _ h => h,
      parabolicStandardMap_surjective Q Λ θ β hsym _ fun x => ⟨x, rfl⟩⟩

/-- Standardization of a graded isomorphism. -/
def standardizationIso {N N' : GFin 𝓓} (e : N.Iso N') :
    (standardizationGFin Λ G θ β hsym N).Iso (standardizationGFin Λ G θ β hsym N') :=
  GradedEquiv.ofBijective
    (standardizationHom_preservesGrading Λ G θ β hsym (g := e.toLinearEquiv.toLinearMap)
      fun _ _ hx => e.map_mem' hx)
    ⟨parabolicStandardMap_injective Q Λ θ β hsym _ e.toLinearEquiv.injective,
      parabolicStandardMap_surjective Q Λ θ β hsym _ e.toLinearEquiv.surjective⟩

variable {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
include hR

/-- **Standardization of resolutions in `C↑`** (Webster, arXiv:1309.3796v3, proof of
Theorem 5.28): for Rouquier parameters and nonnegative dot degrees there is `C₀` such that a
resolution of `N` in `C↑` with constant `c` gives one of `S(N)` with constant `C₀ + c`. -/
theorem exists_upResolution_standardizationGFin (hG : ∀ a, 0 ≤ G.degX a) :
    ∃ C₀ : ℤ, ∀ (N : GFin 𝓓) (c : ℤ), GFin.UpResolution N c →
      Nonempty (GFin.UpResolution (standardizationGFin Λ G θ β hsym N) (C₀ + c)) := by
  obtain ⟨nD, hnD⟩ := exists_hasProjectiveDimensionLT_stdOf_projective Q Λ hsym θ β hR
  obtain ⟨b, hb⟩ := exists_standardizationGFin_grading_eq_bot Λ G θ β hsym hG
  have : Module.Finite k T := tensorProductAlgebra_finite Λ (θ + β) hR
  obtain ⟨L₀, U₀, hL₀⟩ := Graded.exists_bounds (ℳ := tensorProductGrade G (θ + β))
  refine ⟨nD + 1 - b - (nD + 1) * min L₀ 0, fun N c R => ?_⟩
  have hX : ∀ n : ℕ, Nonempty (GFin.UpResolution (standardizationGFin Λ G θ β hsym (R.term n))
      (nD + 1 - b - (nD + 1) * min L₀ 0 + c - n)) := fun n => by
    have := R.projective n
    have : Module.Finite D (R.term n).carrier := Module.Finite.of_restrictScalars_finite k D _
    have hpd : HasProjectiveDimensionLT (stdOf Q Λ hsym θ β (ModuleCat.of D (R.term n).carrier))
        (nD + 1) := by
      have := hnD (ModuleCat.of D (R.term n).carrier)
      exact hasProjectiveDimensionLT_of_ge _ nD _ (Nat.le_succ nD)
    have hpd' : HasProjectiveDimensionLT
        (ModuleCat.of T (standardizationGFin Λ G θ β hsym (R.term n)).carrier) (nD + 1) :=
      @Retract.hasProjectiveDimensionLT _ _ _ _ _
        (standardizationStdOfEquiv Λ G θ β hsym (R.term n)).toModuleIso.retract _ hpd
    obtain ⟨R'⟩ := GFin.UpResolution.exists_of_hasProjectiveDimensionLT
      (𝒜 := tensorProductGrade G (θ + β)) (a := min L₀ 0)
      (fun j hj => hL₀ j (Or.inl (lt_of_lt_of_le hj (min_le_left _ _)))) (min_le_right _ _) nD
      (standardizationGFin Λ G θ β hsym (R.term n)) (m := n - c + b)
      (hb _ _ (fun j hj => R.vanish n j hj)) hpd'
    exact ⟨R'.mono (le_of_eq (by ring))⟩
  exact ⟨(GFin.UpResolution.ofResolution (fun n => standardizationGFin Λ G θ β hsym (R.syz n))
    (fun n => standardizationGFin Λ G θ β hsym (R.term n)) _
    (fun n => standardizationSES Λ G θ β hsym (R.ses n)) fun n => (hX n).some).congr
      (standardizationIso Λ G θ β hsym R.iso)⟩

end Categorification.Stendhal
