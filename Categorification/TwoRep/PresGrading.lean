/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Karoubi
import Categorification.Diagrams.RevBicat
import Categorification.TwoRep.ShiftEnvelope

/-!
# The grading of a presented 2-category

For a presentation `P` of an even signature with a grading `deg` of its generators, the
2-morphisms of the presented bicategory (read in `RevBicat P.Bicat`) are graded by the degree of
diagrams (`StringDiagrams.Presentation.homDeg`): composition adds degrees, whiskering preserves
them, and the associators and unitors (transports along equalities of words) have degree `0`
(`presGrading`). The hom categories of `RevBicat P.Bicat` are preadditive and `R`-linear with
additive whiskering (the structures of the presented category).

With this grading, `ShiftEnv (presGrading P deg)` is the 2-category whose 1-morphisms are the
shifted words `x⟨t⟩` and whose 2-morphisms `x⟨t⟩ ⟶ y⟨t'⟩` are the 2-morphisms `x ⟶ y` of degree
`t' - t` (Khovanov–Lauda's `U` before direct sums, with `x{t} = x⟨-t⟩`).
-/

noncomputable section

namespace Categorification.PresGrading

open CategoryTheory Bicategory StringDiagrams Presentation GradedBicat

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} [S.IsEven] {R : Type w} [CommRing R]
  (P : Presentation.{w, v} S R) (deg : S.Gen → ℤ)

instance revPreadditive (a b : RevBicat P.Bicat) : Preadditive (a ⟶ b) where
  homGroup x y := inferInstanceAs (AddCommGroup
    (P.obj (x : Bicat.Hom b.as a.as).obj ⟶ P.obj (y : Bicat.Hom b.as a.as).obj))
  add_comp x y z η θ ι := Preadditive.add_comp (P.obj (x : Bicat.Hom b.as a.as).obj)
    (P.obj (y : Bicat.Hom b.as a.as).obj) (P.obj (z : Bicat.Hom b.as a.as).obj) η θ ι
  comp_add x y z η θ ι := Preadditive.comp_add (P.obj (x : Bicat.Hom b.as a.as).obj)
    (P.obj (y : Bicat.Hom b.as a.as).obj) (P.obj (z : Bicat.Hom b.as a.as).obj) η θ ι

instance revLinear (a b : RevBicat P.Bicat) : Linear R (a ⟶ b) where
  homModule x y := inferInstanceAs (Module R
    (P.obj (x : Bicat.Hom b.as a.as).obj ⟶ P.obj (y : Bicat.Hom b.as a.as).obj))
  smul_comp x y z r η θ := Linear.smul_comp (P.obj (x : Bicat.Hom b.as a.as).obj)
    (P.obj (y : Bicat.Hom b.as a.as).obj) (P.obj (z : Bicat.Hom b.as a.as).obj) r η θ
  comp_smul x y z η r θ := Linear.comp_smul (P.obj (x : Bicat.Hom b.as a.as).obj)
    (P.obj (y : Bicat.Hom b.as a.as).obj) (P.obj (z : Bicat.Hom b.as a.as).obj) η r θ

instance revPreadditiveBicategory : PreadditiveBicategory (RevBicat P.Bicat) where
  whiskerLeft_add _ _ _ _ _ := P.wRAt_add _ _ _ _ _
  add_whiskerRight _ _ _ := P.wL_add _ _ _

/-- **The grading of the presented bicategory** by the degrees of diagrams. -/
def presGrading : GradedTwoCells R (RevBicat P.Bicat) where
  deg x y n := P.homDeg deg (x : Bicat.Hom _ _).obj (y : Bicat.Hom _ _).obj n
  id_mem x := P.id_mem_homDeg deg _
  comp_mem hη hθ := comp_mem_homDeg hη hθ
  whiskerLeft_mem := by intros; exact wRAt_mem_homDeg ‹_› _ _ _
  whiskerRight_mem := by intros; exact wL_mem_homDeg _ ‹_›
  associator_hom_mem _ _ _ := eqToHom_mem_homDeg (Obj.tensor_assoc _ _ _).symm
  associator_inv_mem _ _ _ := eqToHom_mem_homDeg (Obj.tensor_assoc _ _ _)
  leftUnitor_hom_mem {_ a} _ := eqToHom_mem_homDeg (Obj.tensor_nil _ a.as.region)
  leftUnitor_inv_mem {_ a} _ := eqToHom_mem_homDeg (Obj.tensor_nil _ a.as.region).symm
  rightUnitor_hom_mem f := eqToHom_mem_homDeg (Obj.nil_tensor (Bicat.Hom.start_eq f))
  rightUnitor_inv_mem f := eqToHom_mem_homDeg (Obj.nil_tensor (Bicat.Hom.start_eq f)).symm

end Categorification.PresGrading
