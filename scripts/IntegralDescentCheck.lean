import Categorification
import Mathlib.Data.ZMod.Basic

/-! Root-importing consumers for KL III §6.4 integral descent, including a nonflat
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

-- Presentation base change and spanning do not require rational nondegeneracy.
omit [Finite I] in
example (μ : X) (s t : List (Letter I)) :
    (ZMod 4) ⊗[ℤ] ((pres RD ℤ).obj (ob RD μ s) ⟶ (pres RD ℤ).obj (ob RD μ t)) ≃ₗ[ZMod 4]
      ((pres RD (ZMod 4)).obj (ob RD μ s) ⟶ (pres RD (ZMod 4)).obj (ob RD μ t)) :=
  IntegralScalars.homBaseChange (ZMod 4) RD _ _

omit [Finite I] in
example (μ : X) (s t : List (Letter I)) :
    Submodule.span (ZMod 4) (Set.range (IntegralSpanning.twoB RD (ZMod 4) μ s t)) = ⊤ := by
  classical
  exact IntegralSpanning.span_twoB μ s t

omit [Finite I] in
example (μ : X) (s t : List (Letter I)) (x : SpanIdx s t) :
    IntegralScalars.homBaseChange (ZMod 4) RD _ _
      (1 ⊗ₜ[ℤ] IntegralSpanning.twoB RD ℤ μ s t x) =
        IntegralSpanning.twoB RD (ZMod 4) μ s t x := by
  simp

-- Over fields the ring family is the existing KL family, not a new basis choice.
omit [Finite I] in
example {k : Type w} [Field k] (μ : X) (s t : List (Letter I)) :
    IntegralSpanning.twoB RD k μ s t = twoB RD k μ s t := rfl

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
