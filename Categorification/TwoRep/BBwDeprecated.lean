/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.AdjointWeightNegOne
import Categorification.TwoRep.DotNondegNeg

/-!
# Deprecated names from the time when (BB_w) was a hypothesis

The condition (BB_w) (`StrongSl2.BBw`) holds in every strong 2-representation
(`StrongSl2.bbw`), so the results that used to take it as an argument are now stated without it.
This file keeps the main former names as deprecated aliases.
-/

noncomputable section

namespace Categorification.TwoRep.StrongSl2

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Module
open KrullSchmidtCat (HomFinite)

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.IsLinear B k] [∀ a b : B, HomFinite k (a ⟶ b)] {S : StrongSl2 k B}

@[deprecated _root_.Categorification.TwoRep.StrongSl2.homBddBelow_wordGen (since := "2026-10-09")]
theorem BBw.homBddBelow (_ : S.BBw) {r s : ℤ} {X Z : S.obj r ⟶ S.obj s} (hX : S.WordGen r s X)
    (hZ : S.WordGen r s Z) : HomBddBelow k X Z :=
  S.homBddBelow_wordGen hX hZ

@[deprecated _root_.Categorification.TwoRep.StrongSl2.numAdj (since := "2026-10-09")]
theorem BBw.numAdj (_ : S.BBw) (r : ℤ) : S.NumAdj r :=
  S.numAdj r

@[deprecated _root_.Categorification.TwoRep.StrongSl2.dotNondeg (since := "2026-10-09")]
theorem BBw.dotNondeg [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (_ : S.BBw) {r : ℤ}
    (hn : 0 ≤ S.wt (r + 1)) (h2 : ¬ IsZero (𝟙 (S.obj (r + 1 + 1)))) (e : S.EFDecomp (r + 1)) :
    DotNondeg e :=
  S.dotNondeg hn h2 e

@[deprecated _root_.Categorification.TwoRep.StrongSl2.dotNondegNeg (since := "2026-10-09")]
theorem BBw.dotNondegNeg [∀ a b : B, IsIdempotentComplete (a ⟶ b)] (_ : S.BBw) {r : ℤ}
    (e : S.FEDecomp r) : DotNondegNeg e :=
  S.dotNondegNeg e

variable [GradedBicategory.ShiftCoherence B] [∀ a b : B, IsIdempotentComplete (a ⟶ b)]

@[deprecated _root_.Categorification.TwoRep.StrongSl2.adjHyp (since := "2026-10-09")]
theorem BBw.adjHyp (_ : S.BBw) (r : ℤ) : S.AdjHyp r :=
  S.adjHyp r

@[deprecated _root_.Categorification.TwoRep.StrongSl2.adjHyp (since := "2026-10-09")]
theorem adjHyp_all (S : StrongSl2 k B) (r : ℤ) : S.AdjHyp r :=
  S.adjHyp r

end Categorification.TwoRep.StrongSl2
