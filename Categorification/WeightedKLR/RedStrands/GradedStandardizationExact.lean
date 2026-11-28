/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedStandardization
import Categorification.WeightedKLR.RedStrands.ParabolicStandardExact

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

end Categorification.Stendhal
