/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftNegBubbles
import Categorification.Diagrams.KL3.LocalizationShiftBubbles
import Categorification.Diagrams.KL3.LocalizationShiftDownup


/-!
# Assembling the relation check for the weight shift of `U′` (Webster Prop. 3.30)

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. This file collects the relation checks `shift_rel_*` for the weight shift
`shiftFree RD k δ a b` under Webster's condition `a i - b i = -⟨i, δ⟩` (`hab`) into
`ShiftRelations`.

`shiftRelations_of` is an intermediate statement: it takes the four relation families still to be
checked (the curls `curlR`, `curlL` and the decompositions `decompEF`, `decompFE` of KL III
Definition 3.1) as hypotheses. Every other relation of `presLoc` (zigzags, dot and crossing
cyclicity, bubble relations, sideways crossings of distinct colours, KLR relations, and the
localization relations of Webster Definition 3.28) is discharged here.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (δ : X) (a b : I → ℤ)

/-- The relations of `U′` hold for the images of the generators under the weight shift
(Webster arXiv:1309.3796v2, Proposition 3.30), given the curl and decomposition relations.
Intermediate statement: the hypotheses `hcurlR`, `hcurlL`, `hEF`, `hFE` are the remaining
relation checks. -/
theorem shiftRelations_of [DecidableEq I] (hab : ∀ i, a i - b i = -ip RD i δ)
    (hcurlR : ∀ i lam, (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.curlR i lam)))) = 0)
    (hcurlL : ∀ i μ, (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.curlL i μ)))) = 0)
    (hEF : ∀ i lam, (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.decompEF i lam)))) = 0)
    (hFE : ∀ i lam, (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.decompFE i lam)))) = 0) :
    ShiftRelations RD k δ a b := by
  rintro (((r0 | c | c) | r) | r)
  · exact r0.elim
  · exact shift_rel_zigL (RD := RD) (k := k) (δ := δ) (a := a) (b := b) c
  · exact shift_rel_zigR (RD := RD) (k := k) (δ := δ) (a := a) (b := b) c
  · cases r with
    | cycDotR i μ => exact shift_rel_cycDotR (RD := RD) (k := k) (δ := δ) (a := a) (b := b) i μ
    | cycDotL i μ => exact shift_rel_cycDotL (RD := RD) (k := k) (δ := δ) (a := a) (b := b) i μ
    | cwNeg i lam α h =>
      exact shift_rel_cwNeg (RD := RD) (k := k) (δ := δ) (a := a) (b := b) hab i lam α h
    | ccwNeg i lam α h =>
      exact shift_rel_ccwNeg (RD := RD) (k := k) (δ := δ) (a := a) (b := b) hab i lam α h
    | cwOne i lam h =>
      exact shift_rel_cwOne (RD := RD) (k := k) (δ := δ) (a := a) (b := b) hab i lam h
    | ccwOne i lam h =>
      exact shift_rel_ccwOne (RD := RD) (k := k) (δ := δ) (a := a) (b := b) hab i lam h
    | curlR i lam => exact hcurlR i lam
    | curlL i μ => exact hcurlL i μ
    | decompEF i lam => exact hEF i lam
    | decompFE i lam => exact hFE i lam
    | cycCrossR j i μ =>
      exact shift_rel_cycCrossR (RD := RD) (k := k) (δ := δ) (a := a) (b := b) j i μ
    | cycCrossL j i μ =>
      exact shift_rel_cycCrossL (RD := RD) (k := k) (δ := δ) (a := a) (b := b) j i μ
    | downupEF i j h μ =>
      exact shift_rel_downupEF (RD := RD) (k := k) (δ := δ) (a := a) (b := b) i j h μ
    | downupFE i j h μ =>
      exact shift_rel_downupFE (RD := RD) (k := k) (δ := δ) (a := a) (b := b) i j h μ
    | klr μ r => exact shift_rel_klr (RD := RD) (k := k) (δ := δ) (a := a) (b := b) μ r
  · cases r with
    | invLeft i μ => exact shift_rel_invLeft (RD := RD) (k := k) (δ := δ) (a := a) (b := b) i μ
    | invRight i μ => exact shift_rel_invRight (RD := RD) (k := k) (δ := δ) (a := a) (b := b) i μ
    | cw lam i n => exact shift_rel_cw (RD := RD) (k := k) (δ := δ) (a := a) (b := b) hab lam i n
    | ccw lam i n => exact shift_rel_ccw (RD := RD) (k := k) (δ := δ) (a := a) (b := b) hab lam i n

end Categorification.KL3.Diagram
