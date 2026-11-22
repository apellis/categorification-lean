/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftAssembly
import Categorification.Diagrams.KL3.LocalizationShiftCurlR
import Categorification.Diagrams.KL3.LocalizationShiftCurlL
import Categorification.Diagrams.KL3.LocalizationShiftRelDecompFE

/-!
# The weight-shift functor of `U′` (Webster Prop. 3.30)

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. Under Webster's condition `a i - b i = -⟨i, δ⟩` (in the library's pairing,
with `δ = μ′ - μ`), every relation of the presentation `presLoc` of `U′` is sent to `0` by the
map on generators `shiftImg` (`shiftRelations`), so the map induces a functor
`shiftFunctorOf hab` of the presented category of `U′`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (δ : X) (a b : I → ℤ)

/-- Every relation of `U′` holds for the images of the generators under the weight shift,
under Webster's condition (Webster arXiv:1309.3796v2, Proposition 3.30). -/
theorem shiftRelations [DecidableEq I] (hab : ∀ i, a i - b i = -ip RD i δ) :
    ShiftRelations RD k δ a b :=
  shiftRelations_of RD k δ a b hab
    (fun i lam => shift_rel_curlR RD k δ a b hab i lam)
    (fun i lam => shift_rel_curlL RD k δ a b hab i lam)
    (fun i lam => shift_rel_decompEF RD k δ a b hab i lam)
    (fun i lam => shift_rel_decompFE RD k δ a b hab i lam)

/-- The weight-shift functor of `U′` (Webster arXiv:1309.3796v2, Proposition 3.30): regions
are shifted by `δ`, dots and crossings are fixed, and cups and caps acquire the dot powers
`a i`, `b i`, under the condition `a i - b i = -⟨i, δ⟩`. -/
def shiftFunctorOf [DecidableEq I] (hab : ∀ i, a i - b i = -ip RD i δ) :
    (presLoc RD k).Presented ⥤ (presLoc RD k).Presented :=
  shiftFunctor RD k δ a b (shiftRelations RD k δ a b hab)

/-- The reverse shift `(-δ, -a, -b)` satisfies Webster's condition whenever `(δ, a, b)` does. -/
theorem shift_neg_condition (hab : ∀ i, a i - b i = -ip RD i δ) (i : I) :
    -a i - -b i = -ip RD i (-δ) := by
  have h := hab i
  have hn : ip RD i (-δ) = -ip RD i δ := map_neg _ _
  rw [hn]; omega

/-- The candidate inverse of `shiftFunctorOf hab`: the weight shift by `-δ` with exponents
`-a`, `-b` (Webster arXiv:1309.3796v2, Proposition 3.30). -/
def shiftFunctorInv [DecidableEq I] (hab : ∀ i, a i - b i = -ip RD i δ) :
    (presLoc RD k).Presented ⥤ (presLoc RD k).Presented :=
  shiftFunctorOf RD k (-δ) (fun i => -a i) (fun i => -b i) (shift_neg_condition RD δ a b hab)

end Categorification.KL3.Diagram
