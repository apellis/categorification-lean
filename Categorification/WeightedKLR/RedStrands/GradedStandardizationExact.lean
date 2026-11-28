/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedStandardization
import Categorification.WeightedKLR.RedStrands.ParabolicStandardExact
import Categorification.Algebra.Graded.UpResolutionTensor
import Categorification.KLR.Simple

/-!
# Graded standardization is an exact functor

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5,
Proposition 5.7, for finite graded modules. A degree-preserving map of finite graded modules over
the earlier tensor block and the final cyclotomic factor induces a degree-preserving map of their
standardizations (`Stendhal.standardizationHom`), and a short exact sequence of such modules
gives a short exact sequence of standardizations (`Stendhal.standardizationSES`).
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra Categorification.Graded DirectSum
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w
variable {I : Type} [DecidableEq I] {k : Type w} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin (ℓ+1) → I →₀ ℕ)
  (G : GradingDatum (stendhalQ Q Λ)) (θ β : Multiset I) (hsym : KLRSymm Q)
local notation "D" => parabolicFactorAlgebra Q Λ θ β
local notation "T" => TensorProductAlgebra k Q Λ (θ + β)

variable {N N' : GFin (tensorGrading (tensorProductGrade (restrictRedGrading Q Λ G) θ)
    (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β))}

/-- The map of standardizations induced by a map of factor modules. -/
def standardizationHom (g : N.carrier →ₗ[D] N'.carrier) :
    (standardizationGFin Λ G θ β hsym N).carrier →ₗ[T]
      (standardizationGFin Λ G θ β hsym N').carrier where
  toFun := parabolicStandardMap Q Λ θ β g
  map_add' := map_add _
  map_smul' t z := parabolicStandardMap_action Q Λ θ β hsym g t z

theorem standardizationHom_apply (g : N.carrier →ₗ[D] N'.carrier)
    (z : (standardizationGFin Λ G θ β hsym N).carrier) :
    standardizationHom Λ G θ β hsym g z = parabolicStandardMap Q Λ θ β g z := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Standardization of a degree-preserving map is degree-preserving. -/
theorem standardizationHom_preservesGrading {g : N.carrier →ₗ[D] N'.carrier}
    (hg : PreservesGrading N.grading N'.grading g) :
    PreservesGrading (standardizationGFin Λ G θ β hsym N).grading
      (standardizationGFin Λ G θ β hsym N').grading (standardizationHom Λ G θ β hsym g) := by
  intro d z hz
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hz
  exact Submodule.mem_map.2 ⟨parabolicShuffleMap Q Λ θ β g y,
    mapRight_mem_balancedGrading (g := parabolicInputHom Q Λ θ β g) (fun _ _ hx => hg hx) hy,
    rfl⟩

/-- **Standardization is exact** (Webster, arXiv:1309.3796v3, Proposition 5.7), for finite
graded modules. -/
def standardizationSES {N'' : GFin (tensorGrading (tensorProductGrade (restrictRedGrading Q Λ G) θ)
    (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β))} (S : GFin.ShortExact N N' N'') :
    GFin.ShortExact (standardizationGFin Λ G θ β hsym N) (standardizationGFin Λ G θ β hsym N')
      (standardizationGFin Λ G θ β hsym N'') where
  f := standardizationHom Λ G θ β hsym S.f
  g := standardizationHom Λ G θ β hsym S.g
  preservesGrading_f := standardizationHom_preservesGrading Λ G θ β hsym S.preservesGrading_f
  preservesGrading_g := standardizationHom_preservesGrading Λ G θ β hsym S.preservesGrading_g
  injective := parabolicStandardMap_injective Q Λ θ β hsym S.f S.injective
  surjective := parabolicStandardMap_surjective Q Λ θ β hsym S.g S.surjective
  exact := parabolicStandardMap_exact Q Λ θ β hsym S.f S.g S.exact

local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
  (stendhalWeight 1 β)

set_option backward.isDefEq.respectTransparency false in
/-- **Standardization lowers degrees by at most a constant**: if dots have nonnegative degree,
there is `b` such that the standardization of a module vanishing in degrees `< m` vanishes in
degrees `< m + b`. -/
theorem exists_standardizationGFin_grading_eq_bot (hG : ∀ a, 0 ≤ G.degX a) :
    ∃ b : ℤ, ∀ (N : GFin (tensorGrading (tensorProductGrade (restrictRedGrading Q Λ G) θ)
        (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β))) (m : ℤ),
      (∀ j < m, N.grading j = ⊥) →
        ∀ d < m + b, (standardizationGFin Λ G θ β hsym N).grading d = ⊥ := by
  obtain ⟨b, hb⟩ := KLRAlgebra.exists_grade_eq_bot G (ν := α + δ) hG
  refine ⟨b, fun N m hN d hd => ?_⟩
  have hbim : ∀ i < b, G.bimodGrading α δ i = ⊥ := fun i hi => by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : KLRAlgebra k (stendhalQ Q Λ) (α + δ)) ∈ G.grade (α + δ) i := hx
    rw [hb i hi, Submodule.mem_bot] at hx'
    exact (Submodule.mem_bot _).2 (Subtype.ext hx')
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hz
  obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.1 hy
  rw [tensorGrading_eq_bot (𝒩 := (parabolicInputGFin Λ G θ β N).grading) hbim hN (by omega),
    Submodule.mem_bot] at ht
  subst ht
  simp

end Categorification.Stendhal
