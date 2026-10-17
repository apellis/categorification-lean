/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.IntegralDescent
import Categorification.Diagrams.KL3.IntegralBaseChange

/-!
# KL III nondegeneracy from an integral spanning family

KL III, arXiv:0807.3250v1, Proposition 3.11 and §6.4, paragraph
“Simple nondegeneracy observations”. This uses the concrete presentation
base-change equivalence, not an assumed equivalence. The integral spanning
family and its rational image are explicit intermediate inputs in this file;
`IntegralFamily` constructs them and supplies the final descent theorem.
-/

noncomputable section
namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Module
open scoped TensorProduct

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y} [Finite I]

section Field

variable {k : Type w} [Field k]

/-- A homogeneous KL spanning family is a basis of the entire Hom module
when the calculus is nondegenerate. This collects the degreewise bases using
the existing direct-sum grading of the presentation. -/
def basisOfCalculusNondeg (hnd : CalculusNondeg RD k) (μ : X) (s t : List (Letter I))
    (b : SpanIdx s t → ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)))
    (hb : IsSpanFamily RD k μ s t b) :
    Basis (SpanIdx s t) k ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) := by
  let bd : ∀ d, Basis {x : SpanIdx s t // spanDeg C (RD.ellOf μ) x = d} k (HomD RD k μ s t d) :=
    fun d => (Basis.span ((finrank_eq_iff_linearIndependent μ s t hb d).mp (hnd μ s t d))).map
      (LinearEquiv.ofEq _ _ (hb.2 d))
  exact ((isInternal_homDeg (RD := RD) (k := k) (ob RD μ s) (ob RD μ t)).collectedBasis bd).reindex
    (Equiv.sigmaFiberEquiv (spanDeg C (RD.ellOf μ)))

@[simp] theorem basisOfCalculusNondeg_apply (hnd : CalculusNondeg RD k) (μ : X)
    (s t : List (Letter I))
    (b : SpanIdx s t → ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)))
    (hb : IsSpanFamily RD k μ s t b) (x : SpanIdx s t) :
    basisOfCalculusNondeg hnd μ s t b hb x = b x := by
  simp [basisOfCalculusNondeg, DirectSum.IsInternal.collectedBasis_coe]

end Field

/-- **Rational to arbitrary-ring descent for the actual KL Hom presentation.**

Only integral spanning and compatibility of the chosen integral family with a
rational graded spanning family remain hypotheses. The comparison map and the
presentation tensor equivalence are constructed, not assumed. The rational
nondegeneracy hypothesis supplies independence, after which integral freeness
is established before tensoring. -/
def basisOfIntegralSpanning (k : Type w) [CommRing k] (hnd : CalculusNondeg RD ℚ)
    (μ : X) (s t : List (Letter I))
    (bZ : SpanIdx s t → ((pres RD ℤ).obj (ob RD μ s) ⟶ (pres RD ℤ).obj (ob RD μ t)))
    (hspan : Submodule.span ℤ (Set.range bZ) = ⊤)
    (bQ : SpanIdx s t → ((pres RD ℚ).obj (ob RD μ s) ⟶ (pres RD ℚ).obj (ob RD μ t)))
    (hQ : IsSpanFamily RD ℚ μ s t bQ)
    (hq : ∀ x, IntegralScalars.homMap ℚ RD _ _ (bZ x) = bQ x) :
    Basis (SpanIdx s t) k ((pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t)) := by
  have hli : LinearIndependent ℚ bQ := by
    have he : ⇑(basisOfCalculusNondeg hnd μ s t bQ hQ) = bQ :=
      funext fun x => basisOfCalculusNondeg_apply hnd μ s t bQ hQ x
    rw [← he]
    exact (basisOfCalculusNondeg hnd μ s t bQ hQ).linearIndependent
  exact IntegralDescent.ringBasis bZ bQ (IntegralScalars.homMap ℚ RD _ _) hq hspan hli
    (IntegralScalars.homBaseChange k RD _ _)

@[simp] theorem basisOfIntegralSpanning_apply (k : Type w) [CommRing k]
    (hnd : CalculusNondeg RD ℚ) (μ : X) (s t : List (Letter I))
    (bZ : SpanIdx s t → ((pres RD ℤ).obj (ob RD μ s) ⟶ (pres RD ℤ).obj (ob RD μ t)))
    (hspan : Submodule.span ℤ (Set.range bZ) = ⊤)
    (bQ : SpanIdx s t → ((pres RD ℚ).obj (ob RD μ s) ⟶ (pres RD ℚ).obj (ob RD μ t)))
    (hQ : IsSpanFamily RD ℚ μ s t bQ)
    (hq : ∀ x, IntegralScalars.homMap ℚ RD _ _ (bZ x) = bQ x) (x : SpanIdx s t) :
    basisOfIntegralSpanning k hnd μ s t bZ hspan bQ hQ hq x =
      IntegralScalars.homMap k RD _ _ (bZ x) := by
  simp [basisOfIntegralSpanning]

end Categorification.KL3.Diagram
