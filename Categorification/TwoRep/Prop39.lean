/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.BBwProof
import Categorification.TwoRep.DotNondegNeg

/-!
# CL Lemma 3.6 and Proposition 3.9 without additional hypotheses

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §3. The library proves Lemma 3.6 (`BBw.dotNondeg`, `BBw.dotNondegNeg`) and
Proposition 3.9 (`BBw.adjHyp`) under the boundedness hypothesis (BB_w). Since (BB_w) holds in every
strong 2-representation of `sl₂` (`StrongSl2.bbw`, `BBwProof.lean`), these hold as printed, in the
ambient setting of the library (graded `k`-linear bicategory with Hom-finite Hom categories;
idempotent-complete Hom categories as in CL Definition 1.2; for Proposition 3.9 the shift-coherence
mixin `GradedBicategory.ShiftCoherence`, which CL's graded 2-categories satisfy tacitly).

## Main declarations

* `StrongSl2.numAdj`: the numerical form of (3.2) at every weight.
* `StrongSl2.dotNondeg`, `StrongSl2.dotNondegNeg`: **CL Lemma 3.6** (both halves).
* `StrongSl2.adjHyp_all`: **CL Proposition 3.9**: `(E 1_n)_L ≅ 1_n F ⟨-n-1⟩` at every weight `n`.
-/

noncomputable section

namespace Categorification.TwoRep.StrongSl2

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [∀ a b : B, HomFinite k (a ⟶ b)]

/-- **The numerical form of (3.2) at every weight** (CL §3.2): for word-generated test 1-morphisms,
`dim Hom(x ≫ F, y) = dim Hom(x, y ≫ E⟨-n-1⟩)` and `dim Hom(x, F ≫ y) = dim Hom(E⟨-n-1⟩ ≫ x, y)`. -/
theorem numAdj (S : StrongSl2 k B) (r : ℤ) : S.NumAdj r :=
  S.bbw.numAdj r

/-- **CL Lemma 3.6** (`n ≥ 2`): every decomposition datum of `E F 1_n` has nondegenerate
subdiagonal dot entries. -/
theorem dotNondeg [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (S : StrongSl2 k B) {r : ℤ}
    (hn : 0 ≤ S.wt (r + 1)) (h2 : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) (e : S.EFDecomp (r + 1)) :
    DotNondeg e :=
  S.bbw.dotNondeg hn h2 e

/-- **CL Lemma 3.6** (`n ≤ -2`, Remark 3.11): every decomposition datum of `F E 1_n` has
nondegenerate subdiagonal dot entries. -/
theorem dotNondegNeg [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (S : StrongSl2 k B) {r : ℤ}
    (e : S.FEDecomp r) : DotNondegNeg e :=
  S.bbw.dotNondegNeg e

/-- **CL Proposition 3.9**: in every strong 2-representation of `sl₂` (with shift coherence and
idempotent-complete Hom categories), the left adjoint of `E 1_n` is `1_n F ⟨-n-1⟩` at every weight
`n`, i.e. `E` and `F` are biadjoint up to the shifts of (3.2). -/
theorem adjHyp_all [GradedBicategory.ShiftCoherence B] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
    (S : StrongSl2 k B) (r : ℤ) : S.AdjHyp r :=
  S.bbw.adjHyp r

end Categorification.TwoRep.StrongSl2
