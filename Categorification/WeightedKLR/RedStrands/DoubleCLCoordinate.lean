/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLLocalMap
import Categorification.WeightedKLR.RedStrands.CyclotomicCoverVacuumEvaluation
import Categorification.WeightedKLR.RedStrands.DoubleDownComparison

/-!
# Double diagrams in coordinates and their cyclotomic evaluation

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29 (arXiv:1309.3796v2,
§4.5, Lemma 4.28). The extended Cartan datum `C'` on `I ⊕ Fin ℓ` of a family of
dominant weights `Λ` has the coordinate realization
`cyclotomicCoverWeightDatum`. Its restriction to the black vertices is a weight
datum of `C` (`coordinateDatum`) in which the red weights `-α_r` are dominant,
with coroot pairings `Λ_r` (`coordinateRedWeights_pair`). So the double diagrams
of this datum carry exactly the cyclotomic exponents `Λ`
(`corootExponents_coordinateRedWeights`).

A double diagram of this datum is reflected into the KL 2-category of `C'`
(`coverLin`, with the sign `-1` on same-colour black crossings) and evaluated by
the Cautis–Lauda action on the cyclotomic KLR algebras of `C'`
(`coverEval`). No relation of the double presentation is imposed: the
evaluation is defined on free linear combinations of double diagrams, and is
linear in them. Which relations it respects, up to maps killed by the
projection to the tensor product algebra, is proved separately.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction
  Diagrams.BicatInterp DoubleDiagram

universe u v w

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)

local notation "D" => I ⊕ Fin ℓ
local notation "Wgt" => cyclotomicCoverWeightDatum Λ C

/-- The extended Cartan datum restricts to `C` on the black vertices. -/
theorem extendedCartanDatum_dot_inl (i j : I) :
    (extendedCartanDatum C Λ).dot (.inl i) (.inl j) = C.dot i j := rfl

/-- The weight datum of `C` on the coordinates of the extended datum. -/
abbrev coordinateDatum : WeightDatum C (D → ℤ) ((D → ℤ) →+ ℤ) :=
  blackDatum Wgt (extendedCartanDatum_dot_inl Λ C)

/-- In coordinates, the red weight `-α_r` pairs with the black coroot `i` to the
multiplicity `Λ_r(i)`. -/
theorem coordinateRedWeights_pair (r : Fin ℓ) (i : I) :
    (coordinateDatum Λ C).pair ((coordinateDatum Λ C).iY i) (redWeight Wgt r) = Λ r i := by
  change -(UDot.A (extendedCartanDatum C Λ) (.inl i) (.inr r)) = _
  rw [cover_black_red]
  simp

/-- The red weights of the coordinate datum, as dominant weights. -/
def coordinateRedWeights (r : Fin ℓ) :
    {x : D → ℤ // ∀ i, 0 ≤ (coordinateDatum Λ C).pair ((coordinateDatum Λ C).iY i) x} :=
  ⟨redWeight Wgt r, fun i => by rw [coordinateRedWeights_pair]; positivity⟩

/-- The double diagrams of the coordinate datum have the cyclotomic exponents `Λ`. -/
theorem corootExponents_coordinateRedWeights
    (hfin : ∀ r : Fin ℓ, (Function.support (fun i => ((coordinateDatum Λ C).pair
      ((coordinateDatum Λ C).iY i) (coordinateRedWeights Λ C r).val).toNat)).Finite) :
    corootExponents (RD := coordinateDatum Λ C) (Λ := coordinateRedWeights Λ C) hfin = Λ := by
  funext r
  ext i
  have h := corootExponents_pair (Λ := coordinateRedWeights Λ C) hfin r i
  rw [show (coordinateRedWeights Λ C r).val = redWeight Wgt r from rfl,
    coordinateRedWeights_pair] at h
  exact_mod_cast h

section Evaluation

variable [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)

local notation "S" => cyclotomicCoverQ C Λ Q
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "Sc" => cyclotomicScalars sym lead Wgt deg
local notation "hC" => extendedCartanDatum_dot_inl Λ C
local notation "L" => cyclotomicCoverHighest (I := I) (ℓ := ℓ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "Fam" => cyclotomicFamily.{u, v, w} sym lead
  (cyclotomicCoverPolynomial_monic (k := k)) Wgt L (cyclotomicCoverPolynomial_natDegree (k := k) Λ C) deg
local notation "PCL" => KL3.Diagram.CL.presCL Wgt k Sc
local notation "Sig" => signature (coordinateDatum Λ C) (redWeight Wgt)

/-- The reflected image of a double linear combination in `presCL` of the
extended datum, with the sign `-1` on same-colour black crossings. -/
abbrev coverCL (o : D → ℤ) {a b : Obj Sig} (f : LinDiagram k a b) :=
  coverLin Wgt hC o PCL coverSign f

/-- **Cyclotomic evaluation of double diagrams.** A free linear combination of
double diagrams of the coordinate datum, reflected into the KL 2-category of
the extended datum, acts between the cyclotomic weight spaces through the
Cautis–Lauda action, at the outer regions `s`, `t`. -/
def coverEval (o : D → ℤ) {s t : D → ℤ} {a b : Obj Sig}
    (ha : Cond s t ((coverColourMap Wgt hC o).obj ((coverMirror Wgt hC o).obj a)))
    (hb : Cond s t ((coverColourMap Wgt hC o).obj ((coverMirror Wgt hC o).obj b)))
    (f : LinDiagram k a b) :=
  admissibleQuotientMap (RouqFamily.genImg Fam Sc) PCL
    (fun r _ _ ha hb => RouqFamily.presCL_rel Fam Sc
      (cyclotomicFamily_brundanUpKLR sym lead (cyclotomicCoverPolynomial_monic (k := k)) Wgt L
        (cyclotomicCoverPolynomial_natDegree (k := k) Λ C) deg fun i j h =>
          coeff_eq_zero_of_lt_of_hom _ (IsRouquierQ.homogeneous hS i j h))
      (cyclotomicFamily_mixedInversion Wgt L sym lead (cyclotomicCoverPolynomial_monic (k := k))
        (cyclotomicCoverPolynomial_natDegree (k := k) Λ C) deg) (fun _ => rfl)
      (kkScalars_s_eq_zero _ sym _ (IsRouquierQ.homogeneous hS)) r ha hb)
    Signature.IsEven.odd_eq_false ha hb (coverCL Λ C hQ o f)

end Evaluation

end Categorification.Stendhal
