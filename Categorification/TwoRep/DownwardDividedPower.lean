/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.DownwardNilHecke
import Categorification.TwoRep.DividedPowerDot

/-!
# The divided power `F^(2)` on the actual downward factors

The object is `F (r + 1) ≫ F r`, with no residual adjunction shifts. Its nilHecke
datum uses the actual first and second factor dots and the actual `ffCross`,
with the original unit-valued scalar `rQ`. The two transported dot-slide names
are interchanged when filling `NH2.slide₁` and `NH2.slide₂`.

`NH2` uses left-to-right shifted composition, not multiplication in `End`.
Thus no change is made to the native reversed `End` multiplication or to the
`-rQ⁻¹` crossing normalization of `DownwardNilHeckeRepresentation`.

`exists_F2` splits the degree-zero nilHecke idempotent in the **original** Hom
category. No idempotent-completeness of the finite-sum graded-Hom category is
assumed. `exists_F2_dot` supplies an actual dot-isomorphism on the common
summand, with the same original-category splitting convention as `exists_E2_dot`.
The supplied adjunctions, shift coherence and linearity remain explicit inputs;
this does not derive biadjointness or prove CL Lemma 3.6 or Proposition 3.9.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

namespace StrongSl2

universe w v u

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  (S : StrongSl2 k B)

/-- The honest nilHecke datum on actual `FF`, retaining the unit `rQ` and the
unnormalized crossing. The first factor is `F (r + 1)`, the second is `F r`. -/
def nhF (r : ℤ) : NH2 (k := k) (S.F (r + 1) ≫ S.F r) where
  xL := shWhiskerRight (S.fDot (r + 1)) (S.F r)
  xR := shWhiskerLeft (S.F (r + 1)) (S.fDot r)
  τ := S.ffCross r
  r := S.rQ
  τ_sq := S.ffCross_sq r
  slide₁ := S.f_dot_slide_right r
  slide₂ := S.f_dot_slide_left r

/-- `xL` is exactly the transported first dot, now identified with a genuine
whiskering of the actual downward dot. -/
theorem nhF_xL (r : ℤ) : (S.nhF r).xL = S.ffDotFirst r :=
  (S.ffDotFirst_eq r).symm

/-- `xR` is exactly the transported second dot. -/
theorem nhF_xR (r : ℤ) : (S.nhF r).xR = S.ffDotSecond r :=
  (S.ffDotSecond_eq r).symm

/-- The degree-zero idempotent is `rQ⁻¹` times first-dot then crossing, without
an opposite-ring or normalization convention hidden in its formula. -/
theorem nhF_e (r : ℤ) : (S.nhF r).e =
    ((S.rQ⁻¹ : kˣ) : k) • (S.ffDotFirst r).comp (S.ffCross r)
      (by norm_num : (-2 : ℤ) + 2 = 0) := by
  rw [NH2.e, nhF_xL]
  rfl

variable [∀ a b : B, IsIdempotentComplete (a ⟶ b)]

/-- The downward divided power in the original Hom category: the image of the
actual nilHecke idempotent, shifted by `-1`, gives the two summands of `FF`. -/
theorem exists_F2 (r : ℤ) : ∃ F2 : S.obj (r + 1 + 1) ⟶ S.obj r,
    Nonempty (S.F (r + 1) ≫ S.F r ≅ F2⟦(1 : ℤ)⟧ ⊞ F2⟦(-1 : ℤ)⟧) := by
  obtain ⟨P, ⟨e⟩⟩ := (S.nhF r).exists_iso_biprod
  refine ⟨P⟦(-1 : ℤ)⟧, ⟨e ≪≫ biprod.mapIso
    ((shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by norm_num)).app P).symm
    ((shiftFunctorAdd' _ (-1 : ℤ) (-1) (-2) (by norm_num)).app P)⟩⟩

/-- An original-category splitting `FF ≅ P ⊞ P⟨-2⟩`, with `P = F^(2)⟨1⟩`,
such that the first actual downward dot induces an isomorphism
`P → P⟨-2⟩⟨2⟩` on the common summand. -/
theorem exists_F2_dot (r : ℤ) : ∃ (P : S.obj (r + 1 + 1) ⟶ S.obj r)
    (i : P ⟶ S.F (r + 1) ≫ S.F r) (p : S.F (r + 1) ≫ S.F r ⟶ P)
    (i' : P⟦(-2 : ℤ)⟧ ⟶ S.F (r + 1) ≫ S.F r)
    (p' : S.F (r + 1) ≫ S.F r ⟶ P⟦(-2 : ℤ)⟧),
    i ≫ p = 𝟙 P ∧ i' ≫ p' = 𝟙 _ ∧ i ≫ p' = 0 ∧ i' ≫ p = 0 ∧
      p ≫ i + p' ≫ i' = 𝟙 _ ∧
      IsIso (i ≫ (shWhiskerRight (S.fDot (r + 1)) (S.F r) :
        _ ⟶ (S.F (r + 1) ≫ S.F r)⟦(2 : ℤ)⟧) ≫ p'⟦(2 : ℤ)⟧') :=
  (S.nhF r).exists_decomp_dot

end StrongSl2

end Categorification.TwoRep
