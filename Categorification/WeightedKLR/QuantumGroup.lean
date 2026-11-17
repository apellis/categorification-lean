/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Rouquier.IntegralMap
import Categorification.WeightedKLR.GradedK0.QuantumRelations

/-!
# The quantum-group map to weighted graded Grothendieck groups

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, Theorem 2.19, p. 12, asserts a natural map from the positive quantum group.
For loop-free graphs over a coefficient field, the integral divided-power form
maps to the weighted graded Grothendieck algebra, whose multiplication is
graded induction. The corresponding map over `ℚ(v)` lands in its scalar
extension along `q ↦ v⁻¹`.

The divided-power classes come from the graded loading-family matrix corner
of Proposition 2.14. The classes satisfy the quantum factorial identities and
the divided-power Serre relations, which give the map by quantum Gabber–Kac
and integral descent. The graded dimensions for scalar injectivity follow
from the standing hypotheses.
-/

noncomputable section

namespace Categorification.WeightedKLR.WeightedGraph.Standing

open Categorification.Graded Categorification.KLR Categorification.QuantumGroup

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  (hS : Γ.Standing) (hD : Γ.Dagger) (hne : ∀ e, Γ.head e ≠ Γ.tail e)
  (hl : ∀ i, Γ.loop i = none)

local notation "G" => hS.gradingDatum
local notation "C" => hS.cartanDatum

private def integralMapData : Rouquier.IntegralMapData C (G).K0W (G).K0Q where
  embed := (G).toK0Q
  injective_embed := by
    have : ∀ ν : I →₀ ℕ, HasGdim ((G).klrGrade ν) := fun ν =>
      GalleryAlgebra.hasGdim_klrGrade (ν := ν) hD (fun e he => (hne e he).elim) hS
    exact (G).toK0Q_injective
  embed_smul := (G).toK0Q_smul
  divided i n := GradingDatum.spacedClsDiv hS hD hne hl [(i, n)]
  factorial := GradingDatum.toK0Q_spacedClsDiv_factorial hS hD hne hl
  serre _ _ hij := GradingDatum.spacedClsDiv_serre_mul hS hD hne hl hij

/-- The map over `ℚ(v)` in Webster, arXiv:1209.2463v4, §2.4, Theorem 2.19,
for a loop-free weighted graph over a coefficient field. -/
def rationalQuantumGroupMap : (C).F →ₐ[RatFunc ℚ] (G).K0Q :=
  (integralMapData hS hD hne hl).rationalMap

/-- The integral quantum-group map of Webster, arXiv:1209.2463v4, §2.4,
Theorem 2.19, for a loop-free weighted graph over a coefficient field. -/
def quantumGroupMap : (C).Af →+* (G).K0W :=
  (integralMapData hS hD hne hl).integralMap

/-- The integral map agrees with the rational map after scalar extension. -/
theorem embed_quantumGroupMap (x : (C).Af) :
    (G).toK0Q (hS.quantumGroupMap hD hne hl x) = hS.rationalQuantumGroupMap hD hne hl x :=
  (integralMapData hS hD hne hl).embed_integralMap x

/-- Each integral divided power maps to the corresponding weighted projective class. -/
theorem quantumGroupMap_dpow (i : I) (n : ℕ) :
    hS.quantumGroupMap hD hne hl
        ⟨PreF.dpowF (C).dot vQ (C).c i n, PreF.dpowF_mem_Af i n⟩ =
      GradingDatum.spacedClsDiv hS hD hne hl [(i, n)] :=
  (integralMapData hS hD hne hl).integralMap_dpow i n

/-- Each simple generator maps to the regular one-strand projective class. -/
theorem quantumGroupMap_generator (i : I) :
    hS.quantumGroupMap hD hne hl ⟨PreF.π (C).dot vQ (C).c (PreF.θ i), PreF.π_θ_mem_Af i⟩ =
      DirectSum.of (G).K0fam (Finsupp.single i 1)
        (K0.of (GProj.regular ((G).klrGrade (Finsupp.single i 1)))) := by
  calc
    _ = GradingDatum.spacedClsDiv hS hD hne hl [(i, 1)] :=
      (integralMapData hS hD hne hl).integralMap_generator i
    _ = (G).spacedClsSeq [i] := GradingDatum.spacedClsDiv_single_one hS hD hne hl i
    _ = _ := (G).spacedClsSeq_single i

/-- The integral map is linear over `ℤ[q,q⁻¹]`, with `q` acting on the quantum
group as `v⁻¹` and on the weighted Grothendieck group by the grading shift. -/
theorem quantumGroupMap_smul (p : LaurentPolynomial ℤ) (x : (C).Af) :
    hS.quantumGroupMap hD hne hl
        ⟨algebraMap (RatFunc ℚ) (C).F (KLGamma.qToV p) * x,
          Subring.mul_mem _ (KL2Gamma.algebraMap_qToV_mem_Af2 C p) x.2⟩ =
      p • hS.quantumGroupMap hD hne hl x :=
  (integralMapData hS hD hne hl).integralMap_smul p x

end Categorification.WeightedKLR.WeightedGraph.Standing
