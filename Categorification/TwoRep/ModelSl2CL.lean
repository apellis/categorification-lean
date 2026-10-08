/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelSl2Interp
import Categorification.Diagrams.CL.Rescale
import Categorification.Diagrams.CL.Specialize

/-!
# The interpretation of `U_Q(sl₂)` for every choice of scalars

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §2.6.1 (`sec:sl2convs`): for a single vertex, rescaling the crossing by `r_i`
identifies `U_Q(sl₂)` with `U(sl₂)` (`r_i = 1`). With the rescaling isomorphism of
`Categorification.Diagrams.CL.Rescale` (`RescaleDatum.equiv`; here `sl2Rescale`: crossing times
`r`, dots and cups unchanged) and the interpretation `interpU` of `U(sl₂)`
(`Categorification.TwoRep.ModelSl2Interp`), a strong 2-representation of `sl₂` satisfying (BB_w)
gives, on hom categories, a linear functor from `U_Q(sl₂)` for every choice of scalars `Q`
(`interpUQ`): CL Theorem 5.5 for `g = sl₂`. The relations between differently labelled strands
are vacuous for `sl₂`, so `U_Q(sl₂)` depends only on `r` (`presCL_congr`).

## Main declarations

* `StrongSl2.sl2Rescale`, `StrongSl2.sl2Rescale_presCL`;
* `StrongSl2.respects_sl2_kl`, `StrongSl2.interpUQ`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe w v u

section Model

open GradedHomBicat GradedHomCat
open QuantumGroup UDot KL3.Diagram KL3.Diagram.CL StringDiagrams Diagrams.BicatInterp
open KrullSchmidtCat (HomFinite)

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]

namespace StrongSl2

variable {S : StrongSl2 k B} (hS : S.BBw)

/-- The rescaling datum for `sl₂` taking the scalars `Q = (t, s, r)` to `r = 1`: the crossing is
multiplied by `r`, dots and cups are unchanged (CL §2.6.1). -/
def sl2Rescale (Sc : CLScalars (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) k) :
    RescaleDatum sl2RootDatum k where
  dot _ := 1
  cross _ _ := Sc.r ()
  cup _ := 1
  cup_up _ _ := by simp

omit [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)] in
/-- After rescaling, `U_Q(sl₂)` is KL III's `U(sl₂)` (CL §2.6.1). -/
theorem sl2Rescale_presCL (Sc : CLScalars (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) k) :
    presCL sl2RootDatum k ((sl2Rescale Sc).mapScalars Sc) =
      presCL sl2RootDatum k CLScalars.kl := by
  refine presCL_congr (fun i j h => (h (Subsingleton.elim _ _)).elim)
    (fun i j _ _ h => (h (Subsingleton.elim _ _)).elim) ?_
  funext i
  cases i
  simp [RescaleDatum.mapScalars, sl2Rescale]

/-- The `sl₂` model respects the relations of `U(sl₂)` presented as CL's `U_Q(sl₂)` with the
KL scalars. -/
theorem respects_sl2_kl {s₀ : ℤ} (hs : ∃ q : ℤ, s₀ = S.n₀ + 2 * q) (t₀ : ℤ) :
    (presCL sl2RootDatum k CLScalars.kl).Respects (interp (genImg hS) s₀ t₀).functor := by
  rw [presCL_kl]
  exact respects_sl2 hS hs t₀

/-- **The 2-representation of `U_Q(sl₂)` defined by a strong 2-representation satisfying
(BB_w)**, on hom categories, for every choice of scalars `Q` (CL Theorem 5.5 for `g = sl₂`): the
rescaling isomorphism `U_Q(sl₂) ≅ U(sl₂)` of CL §2.6.1 followed by the interpretation of
`U(sl₂)` (`interpU`). -/
def interpUQ (Sc : CLScalars (CartanDatum.ofGraph (⊥ : SimpleGraph Unit)) k) {s₀ : ℤ}
    (hs : ∃ q : ℤ, s₀ = S.n₀ + 2 * q) (t₀ : ℤ) :
    (presCL sl2RootDatum k Sc).Presented ⥤
      (S.model.lift.obj (fo (S := psig sl2RootDatum) t₀) ⟶
        S.model.lift.obj (fo (S := psig sl2RootDatum) s₀)) :=
  ((sl2Rescale Sc).equiv Sc (sl2Rescale_presCL Sc)).functor ⋙
    (presCL sl2RootDatum k CLScalars.kl).lift (respects_sl2_kl hS hs t₀)

end StrongSl2

end Model

end Categorification.TwoRep
