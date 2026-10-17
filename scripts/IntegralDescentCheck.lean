import Categorification.Diagrams.KL3.IntegralFamily
import Mathlib.Data.ZMod.Basic

/-! Importing consumers for KL III §6.4 integral descent, including a nonflat
coefficient ring. Run with `lake env lean -DwarningAsError=true`.
-/

open Categorification.KL3.Diagram Module
open Categorification CategoryTheory StringDiagrams QuantumGroup UDot
open scoped TensorProduct

noncomputable section

-- The algebraic descent does not assume that the coefficient ring is flat.
example : Function.Bijective
    (Finsupp.linearCombination (ZMod 4) (fun _ : Unit => (1 : ZMod 4))) := by
  refine IntegralDescent.basisMap_bijective
    (fun _ : Unit => (1 : ℤ)) (fun _ : Unit => (1 : ℚ))
    (fun _ : Unit => (1 : ZMod 4)) (Algebra.linearMap ℤ ℚ)
    ?_ ?_ ?_ (TensorProduct.AlgebraTensorModule.rid ℤ (ZMod 4) (ZMod 4)) ?_
  · intro i; simp
  · have hb : ⇑(Basis.singleton Unit ℤ) = (fun _ : Unit => (1 : ℤ)) :=
      funext fun i => Basis.singleton_apply Unit ℤ i
    rw [← hb]
    exact (Basis.singleton Unit ℤ).span_eq
  · have hb : ⇑(Basis.singleton Unit ℚ) = (fun _ : Unit => (1 : ℚ)) :=
      funext fun i => Basis.singleton_apply Unit ℚ i
    rw [← hb]
    exact (Basis.singleton Unit ℚ).linearIndependent
  · intro i; simp

universe u v w
variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y} [Finite I]

-- The presentation, integral spanning, and family comparison are not hypotheses.
example (hnd : CalculusNondeg RD ℚ) (μ : X) (s t : List (Letter I)) :
    Function.Bijective (Finsupp.linearCombination (ZMod 4)
      (IntegralSpanning.twoB RD (ZMod 4) μ s t)) := by
  let b := integralNondegBasis (ZMod 4) hnd μ s t
  have he : ⇑b = IntegralSpanning.twoB RD (ZMod 4) μ s t :=
    funext fun x => integralNondegBasis_apply (ZMod 4) hnd μ s t x
  rw [← he, ← b.coe_repr_symm]
  exact b.repr.symm.bijective

example (hnd : CalculusNondeg RD ℚ) (μ : X) (s t : List (Letter I)) :
    Basis (SpanIdx s t) ℤ ((pres RD ℤ).obj (ob RD μ s) ⟶ (pres RD ℤ).obj (ob RD μ t)) :=
  integralCanonicalBasis hnd μ s t

example {k : Type w} [Field k] (hnd : CalculusNondeg RD ℚ) : CalculusNondeg RD k :=
  calculusNondeg_of_rational k hnd

#print axioms IntegralScalars.homBaseChange
#print axioms IntegralSpanning.span_twoB
#print axioms integralCanonicalBasis
#print axioms integralNondegBasis
#print axioms integralNondegBasis_apply
#print axioms calculusNondeg_of_rational
