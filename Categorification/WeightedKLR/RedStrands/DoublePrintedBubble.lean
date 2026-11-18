/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBubbleRelations
import Categorification.WeightedKLR.RedStrands.DoubleAllDownBoundary
import Categorification.WeightedKLR.RedStrands.SingleBlack
import Categorification.QuantumGroup.UDotKL3

/-!
# The printed bubble bound and the all-down corner

Webster, arXiv:1309.3796v2, §2.2, (2.2b), p. 9 (v3, (2.3b)), prints the bounds
`-n-1 ≤ k ≤ j+n+1` and gives the identity at `j=-2`. For `n<0` the interval at
`j=-2` is empty. Adjoining even this constant coefficient in the exterior region
annihilates every all-down matrix with negative exterior coroot coordinate.
For one fundamental red and one black strand in type A₁ this precludes the
injection of v2, §4.5, Lemma 4.28 (v3, Lemma 4.29). The corrected inverse-series
relation in `DoubleBubbleRelations` instead has upper bound `j-n+1`.
-/

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams
open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) {ℓ : ℕ} (Λ : Fin ℓ → X) (k : Type w) [CommRing k]

private abbrev ExteriorIndex := X × List (DoubleStrand I ℓ) × I

private abbrev exteriorObj (p : ExteriorIndex (I := I) (X := X) (ℓ := ℓ)) :=
  obj RD Λ p.1 (p.2.1 ++ blackWord [] ++ [])

private def printedConstant (p : ExteriorIndex (I := I) (X := X) (ℓ := ℓ)) :
    LinDiagram k (exteriorObj RD Λ p) (exteriorObj RD Λ p) :=
  let η := endWeight RD Λ p.1 p.2.1
  let n := ip RD p.2.2 η
  blackLinear RD Λ k p.1 p.2.1 []
    ((∑ t ∈ Finset.Icc (-n - 1) (-2 + n + 1),
      ccwL RD k η p.2.2 t ≫ cwL RD k η p.2.2 (-2 - t)) - LinDiagram.of (𝟙 (ob RD η [])))

/-- Adjoin just the `j = -2` instance of the printed bubble identity in the far-right
region. Any other signed diagram relations may be included in `P`. -/
def addPrintedBubbleConstant (P : Presentation.{w, max u v} (signature RD Λ) k) :
    Presentation.{w, max u v} (signature RD Λ) k :=
  P.addRels _ (exteriorObj RD Λ) (exteriorObj RD Λ) (printedConstant RD Λ k)

variable {k} (P : Presentation.{w, max u v} (signature RD Λ) k)
local notation "B" => addPrintedBubbleConstant RD Λ k P

/-- The printed bounds give `𝟙 = 0` at any negative exterior coordinate, independently
of all bubble values. -/
theorem printedBubble_id_eq_zero (μ : X) (L : List (DoubleStrand I ℓ)) (i : I)
    (h : ip RD i (endWeight RD Λ μ L) < 0) : 𝟙 ((B).obj (obj RD Λ μ L)) = 0 := by
  let η := endWeight RD Λ μ L
  let n := ip RD i η
  have hempty : Finset.Icc (-n - 1) (-2 + n + 1) = ∅ := Finset.Icc_eq_empty (by dsimp [n, η]; omega)
  have he := (B).lin_rel_self (.inr (μ, L, i))
  change (B).lin (blackLinear RD Λ k μ L []
    ((∑ t ∈ Finset.Icc (-n - 1) (-2 + n + 1), ccwL RD k η i t ≫ cwL RD k η i (-2 - t)) -
      LinDiagram.of (𝟙 (ob RD η [])))) = 0 at he
  rw [hempty, Finset.sum_empty, zero_sub, map_neg, Presentation.lin_neg, neg_eq_zero,
    blackLinear_of, Presentation.lin_of, blackDiagram_id, Presentation.diag_id] at he
  have hw : L ++ blackWord ([] : List (Letter I)) ++ ([] : List (DoubleStrand I ℓ)) = L := by
    change L ++ [] ++ [] = L
    simp
  rwa [hw] at he

section Corner
variable {RD} {Λd : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
  (P : Presentation.{w, max u v} (signature RD (Subtype.val ∘ Λd)) k)
local notation "B'" => addPrintedBubbleConstant RD (Subtype.val ∘ Λd) k P

/-- In the violating quotient, every entry of the physical all-down matrix algebra
vanishes when its common right weight has negative coroot coordinate. -/
theorem printedBubble_downwardMatrix_subsingleton (ν : Multiset I) (i : I)
    (h : ip RD i (downRightWeight RD Λd ν) < 0) : Subsingleton (downwardMatrix B' ν) := by
  constructor
  intro f g
  apply KLR.Diagram.MatEnd.ext
  intro s t
  let a : BoundaryCategory B' (downRightWeight RD Λd ν) := downTriple RD Λd s
  have hw : endWeight RD (Subtype.val ∘ Λd) 0 a.val.word = downRightWeight RD Λd ν := a.property
  have he := printedBubble_id_eq_zero RD (Subtype.val ∘ Λd) P 0 a.val.word i (by rw [hw]; exact h)
  have hpre : 𝟙 a = 0 := InducedCategory.hom_ext he
  have hz : 𝟙 (downObj B' s) = 0 :=
    ((violatingFunctor B' _).map_id a).symm.trans
      ((congrArg (violatingFunctor B' _).map hpre).trans ((violatingFunctor B' _).map_zero _ _))
  have hzero (m : downObj B' s ⟶ downObj B' t) : m = 0 := by
    rw [← Category.id_comp m, hz, Limits.zero_comp]
  exact (hzero _).trans (hzero _).symm

end Corner

/-- One fundamental red and one downward black have right weight `1-2=-1`. Consequently
no algebra injection from the ordinary one-red/one-black block can obey the literal
constant bubble relation, even with arbitrary additional signed relations. -/
theorem printedBubble_no_injection_sl2
    (P : Presentation (signature sl2RootDatum (fun _ : Fin 1 => (1 : ℤ))) ℚ) :
    let fundamental : Fin 1 → {x : ℤ // ∀ i, 0 ≤ sl2RootDatum.pair (sl2RootDatum.iY i) x} :=
      fun _ => ⟨1, fun _ => by decide +revert⟩
    let exponents : Fin 1 → Unit →₀ ℕ := fun _ => Finsupp.single () 1
    let Q : Unit → Unit → MvPolynomial (Fin 2) ℚ := fun _ _ => 0
    let printed := addPrintedBubbleConstant sl2RootDatum (Subtype.val ∘ fundamental) ℚ P
    ¬ ∃ f : TensorProductAlgebra ℚ Q exponents {()} →ₐ[ℚ] downwardMatrix (Λ := fundamental) printed {()},
        Function.Injective f := by
  intro fundamental exponents Q printed
  have h : ip sl2RootDatum () (downRightWeight sl2RootDatum fundamental {()}) < 0 := by
    norm_num [ip, sl2RootDatum, downRightWeight, fundamental, List.ofFn_succ]
  have := printedBubble_downwardMatrix_subsingleton (Λd := fundamental) P {()} () h
  have : Nontrivial (AdjoinRoot (Polynomial.X ^ exponents 0 () : Polynomial ℚ)) :=
    AdjoinRoot.nontrivial _ (by simp [exponents])
  rintro ⟨f, hf⟩
  have hz := hf (Subsingleton.elim (f 1) (f 0))
  let e := SingleBlack.oneBlackOneRedEquiv () Q exponents
  exact one_ne_zero ((map_one e).symm.trans ((congrArg e hz).trans (map_zero e)))

end Categorification.Stendhal.DoubleDiagram
