/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.GdimBound
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Integral descent for the KL III diagram basis

Khovanov–Lauda, *A categorification of quantum sl(n)*, arXiv:0807.3250v1,
paragraph “Simple nondegeneracy observations” in §6.4 (TeX lines 9806–9816), states
that nondegeneracy over `ℚ` implies nondegeneracy over `ℤ` and every commutative
ring. Proposition 3.11 supplies diagrammatic spanning.

The mechanism here first proves that the integral basis map is an isomorphism,
using independence after mapping to a characteristic-zero Hom module. It then
extends that **basis**, not merely an independent family, to the target ring.
No flatness or torsion-freeness hypothesis is imposed on a Hom module or on the
target ring.

These are intermediate descent results: integral spanning, the map to rational
Hom, and the presentation base-change equivalence are explicit inputs here.
`IntegralSpanning`, `IntegralBaseChange`, and `IntegralFamily` construct the
actual calculus inputs and assemble full-Hom descent, collecting the rational
graded bases first. `scalarHomD` below is the existing presentation's homogeneous
submodule over a commutative ring, not a different model of the calculus.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Module
open scoped TensorProduct

namespace IntegralDescent

variable {ι MZ MQ : Type*} [AddCommGroup MZ] [AddCommGroup MQ] [Module ℚ MQ]

/-- Independence of the rational diagram family detects the kernel of the
integral basis map. Only the coefficients of a finite integral linear
combination are embedded in characteristic zero; injectivity of `q` is not
assumed. -/
theorem integral_linearIndependent (bZ : ι → MZ) (bQ : ι → MQ)
    (q : MZ →ₗ[ℤ] MQ) (hq : ∀ i, q (bZ i) = bQ i)
    (hQ : LinearIndependent ℚ bQ) : LinearIndependent ℤ bZ := by
  have h : LinearIndependent ℤ bQ := hQ.restrict_scalars' ℤ
  apply LinearIndependent.of_comp q
  simpa only [Function.comp_def, hq] using h

/-- The integral spanning family is a basis once its rational image is
independent (KL III, “Simple nondegeneracy observations”). -/
def integralBasis (bZ : ι → MZ) (bQ : ι → MQ)
    (q : MZ →ₗ[ℤ] MQ) (hq : ∀ i, q (bZ i) = bQ i)
    (hspan : Submodule.span ℤ (Set.range bZ) = ⊤)
    (hQ : LinearIndependent ℚ bQ) : Basis ι ℤ MZ :=
  Basis.mk (integral_linearIndependent bZ bQ q hq hQ) hspan.ge

@[simp] theorem integralBasis_apply (bZ : ι → MZ) (bQ : ι → MQ)
    (q : MZ →ₗ[ℤ] MQ) (hq : ∀ i, q (bZ i) = bQ i)
    (hspan : Submodule.span ℤ (Set.range bZ) = ⊤)
    (hQ : LinearIndependent ℚ bQ) (i : ι) :
    integralBasis bZ bQ q hq hspan hQ i = bZ i :=
  Basis.mk_apply _ _ i

variable {k MK : Type*} [CommRing k] [AddCommGroup MK] [Module k MK]

/-- Tensor the already established integral basis and transport it along the
presentation base-change equivalence. This works even for nonflat `k`. -/
def ringBasis (bZ : ι → MZ) (bQ : ι → MQ)
    (q : MZ →ₗ[ℤ] MQ) (hq : ∀ i, q (bZ i) = bQ i)
    (hspan : Submodule.span ℤ (Set.range bZ) = ⊤)
    (hQ : LinearIndependent ℚ bQ) (e : k ⊗[ℤ] MZ ≃ₗ[k] MK) : Basis ι k MK :=
  ((integralBasis bZ bQ q hq hspan hQ).baseChange k).map e

@[simp] theorem ringBasis_apply (bZ : ι → MZ) (bQ : ι → MQ)
    (q : MZ →ₗ[ℤ] MQ) (hq : ∀ i, q (bZ i) = bQ i)
    (hspan : Submodule.span ℤ (Set.range bZ) = ⊤)
    (hQ : LinearIndependent ℚ bQ) (e : k ⊗[ℤ] MZ ≃ₗ[k] MK) (i : ι) :
    ringBasis bZ bQ q hq hspan hQ e i = e (1 ⊗ₜ[ℤ] bZ i) := by
  simp [ringBasis]

/-- The target diagram basis map is bijective, provided base change carries
the integral diagrams to the target diagrams. This is not specialization of
linear independence: `ringBasis` first establishes integral freeness. -/
theorem basisMap_bijective (bZ : ι → MZ) (bQ : ι → MQ) (bK : ι → MK)
    (q : MZ →ₗ[ℤ] MQ) (hq : ∀ i, q (bZ i) = bQ i)
    (hspan : Submodule.span ℤ (Set.range bZ) = ⊤)
    (hQ : LinearIndependent ℚ bQ) (e : k ⊗[ℤ] MZ ≃ₗ[k] MK)
    (he : ∀ i, e (1 ⊗ₜ[ℤ] bZ i) = bK i) :
    Function.Bijective (Finsupp.linearCombination k bK) := by
  let b := ringBasis bZ bQ q hq hspan hQ e
  have hb : ⇑b = bK := funext fun i => (ringBasis_apply _ _ _ _ _ _ _ i).trans (he i)
  rw [← hb]
  rw [← b.coe_repr_symm]
  exact b.repr.symm.bijective

end IntegralDescent

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)

/-- The homogeneous submodule of the existing KL presentation over an arbitrary
commutative ring. For a field this is definitionally `HomD`. -/
abbrev scalarHomD (k : Type w) [CommRing k] (μ : X)
    (s t : List (Letter I)) (d : ℤ) :=
  (pres RD k).homDeg (deg RD) (ob RD μ s) (ob RD μ t) d

variable {RD} [Finite I]

/-- **KL III integral descent, on one homogeneous Hom module.**

The rational family is any graded spanning family indexed by the KL diagrams.
The integral family, its spanning property, its comparison with that rational
family, and the presentation base-change equivalence are explicit intermediate
hypotheses. `CalculusNondeg RD ℚ` supplies precisely the remaining independence
input. No property of an integral Hom module is assumed beyond spanning. -/
def homBasisOfRational (k : Type w) [CommRing k] (hnd : CalculusNondeg RD ℚ)
    (μ : X) (s t : List (Letter I)) (d : ℤ)
    (bQ : SpanIdx s t → ((pres RD ℚ).obj (ob RD μ s) ⟶ (pres RD ℚ).obj (ob RD μ t)))
    (hQ : IsSpanFamily RD ℚ μ s t bQ)
    (bZ : {x : SpanIdx s t // spanDeg C (RD.ellOf μ) x = d} → scalarHomD RD ℤ μ s t d)
    (hspan : Submodule.span ℤ (Set.range bZ) = ⊤)
    (q : scalarHomD RD ℤ μ s t d →ₗ[ℤ]
      ((pres RD ℚ).obj (ob RD μ s) ⟶ (pres RD ℚ).obj (ob RD μ t)))
    (hq : ∀ x, q (bZ x) = bQ x.1)
    (e : k ⊗[ℤ] scalarHomD RD ℤ μ s t d ≃ₗ[k] scalarHomD RD k μ s t d) :
    Basis {x : SpanIdx s t // spanDeg C (RD.ellOf μ) x = d} k (scalarHomD RD k μ s t d) :=
  IntegralDescent.ringBasis bZ (fun x => bQ x.1) q hq hspan
    ((finrank_eq_iff_linearIndependent μ s t hQ d).mp (hnd μ s t d)) e

/-- The source-grounded inputs to integral descent for fixed boundary words.

`spanning` is the integral form of Proposition 3.11. `toRational` and its
compatibility express scalar change on the diagram family. This degreewise
interface keeps its inputs explicit. The completed full-Hom route in
`IntegralFamily` constructs ring-valued spanning rather than specializing a
field-only spanning theorem. -/
structure IntegralHomFamily (μ : X) (s t : List (Letter I)) where
  rational : SpanIdx s t →
    ((pres RD ℚ).obj (ob RD μ s) ⟶ (pres RD ℚ).obj (ob RD μ t))
  rational_spanning : IsSpanFamily RD ℚ μ s t rational
  integral (d : ℤ) :
    {x : SpanIdx s t // spanDeg C (RD.ellOf μ) x = d} → scalarHomD RD ℤ μ s t d
  spanning (d : ℤ) : Submodule.span ℤ (Set.range (integral d)) = ⊤
  toRational (d : ℤ) : scalarHomD RD ℤ μ s t d →ₗ[ℤ]
    ((pres RD ℚ).obj (ob RD μ s) ⟶ (pres RD ℚ).obj (ob RD μ t))
  toRational_integral (d : ℤ) (x) : toRational d (integral d x) = rational x.1

namespace IntegralHomFamily

variable {μ : X} {s t : List (Letter I)} (H : IntegralHomFamily (RD := RD) μ s t)

/-- The integral Hom module is free on the proposed diagrams, before making
any specialization of scalars. -/
def integralBasis (hnd : CalculusNondeg RD ℚ) (d : ℤ) :
    Basis {x : SpanIdx s t // spanDeg C (RD.ellOf μ) x = d} ℤ (scalarHomD RD ℤ μ s t d) :=
  IntegralDescent.integralBasis (H.integral d) (fun x => H.rational x.1)
    (H.toRational d) (H.toRational_integral d) (H.spanning d)
    ((finrank_eq_iff_linearIndependent μ s t H.rational_spanning d).mp (hnd μ s t d))

@[simp] theorem integralBasis_apply (hnd : CalculusNondeg RD ℚ) (d : ℤ) (x) :
    H.integralBasis hnd d x = H.integral d x :=
  IntegralDescent.integralBasis_apply _ _ _ _ _ _ x

/-- Nondegeneracy over an arbitrary commutative ring, conditional only on the
integral inputs and the presentation base-change equivalence. -/
def basis (k : Type w) [CommRing k] (hnd : CalculusNondeg RD ℚ) (d : ℤ)
    (e : k ⊗[ℤ] scalarHomD RD ℤ μ s t d ≃ₗ[k] scalarHomD RD k μ s t d) :
    Basis {x : SpanIdx s t // spanDeg C (RD.ellOf μ) x = d} k (scalarHomD RD k μ s t d) :=
  ((H.integralBasis hnd d).baseChange k).map e

@[simp] theorem basis_apply (k : Type w) [CommRing k] (hnd : CalculusNondeg RD ℚ) (d : ℤ)
    (e : k ⊗[ℤ] scalarHomD RD ℤ μ s t d ≃ₗ[k] scalarHomD RD k μ s t d) (x) :
    H.basis k hnd d e x = e (1 ⊗ₜ[ℤ] H.integral d x) := by
  simp [basis]

end IntegralHomFamily

/-- The field-valued `CalculusNondeg` API follows from integral descent.

This intermediate theorem records precisely the remaining integral-spanning
and presentation-base-change inputs; it does not claim they follow from the
currently field-valued `prop311` API. The target field may have any
characteristic. For an arbitrary commutative ring use `IntegralHomFamily.basis`
instead, since `CalculusNondeg` itself is defined only over fields. -/
theorem calculusNondeg_of_integralBaseChange (k : Type w) [Field k]
    (hnd : CalculusNondeg RD ℚ)
    (H : ∀ (μ : X) (s t : List (Letter I)), IntegralHomFamily (RD := RD) μ s t)
    (e : ∀ (μ : X) (s t : List (Letter I)) (d : ℤ),
      k ⊗[ℤ] scalarHomD RD ℤ μ s t d ≃ₗ[k] scalarHomD RD k μ s t d) :
    CalculusNondeg RD k := by
  intro μ s t d
  have := (prop_3_12 (s := s) (t := t) RD μ d).1
  let := Fintype.ofFinite {x : SpanIdx s t // spanDeg C (RD.ellOf μ) x = d}
  rw [Module.finrank_eq_card_basis ((H μ s t).basis k hnd d (e μ s t d))]
  exact_mod_cast card_fiber_eq (RD := RD) μ s t d

end Categorification.KL3.Diagram
