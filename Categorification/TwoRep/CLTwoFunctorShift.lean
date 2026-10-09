/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.CLTwoFunctor
import Categorification.TwoRep.ModelQStrongGraded
import Categorification.TwoRep.PresGrading
import Categorification.TwoRep.ShiftEnvRealize

/-!
# CL Theorem 1.1 with grading shifts: a 2-functor into the target bicategory

S. Cautis, A. D. Lauda, arXiv:1111.1431v3, Theorem 1.1. The 2-category `U_Q(g)` of CL
Definition 1.1 is graded: its 1-morphisms are the shifted words `x⟨t⟩`, and its 2-morphisms
`x⟨t⟩ → y⟨t'⟩` are the diagrams `x → y` of degree `t' - t` (CL §2.1.2: `Hom^l(A, B) = Hom(A, B⟨l⟩)`;
KL III's `x{t}` is `x⟨-t⟩`). Here this is the shift envelope
`UQShift RD S₀ = ShiftEnv (presGrading (presCL RD k S₀) (deg RD))` of the presented bicategory
(`Categorification.TwoRep.ShiftEnvelope`, `Categorification.TwoRep.PresGrading`); formal direct sums
and the Karoubi completion are added on top of this 2-functor.

The pseudofunctor `QStrong.twoFunctorHOM` of `Categorification.TwoRep.CLTwoFunctor` preserves
degrees up to the offsets `cWord` of words (`Categorification.TwoRep.ModelQStrongGraded`: the image
of `F_i 1_μ` is the right adjoint of `E_i 1_{μ-α_i}`, which is CL's `F_i 1_μ` shifted by
`⟨(α_i, μ - α_i) + d_i⟩`). Hence (`QStrong.gradedHOM`) it induces a pseudofunctor of shift
envelopes, which is realized in the target bicategory `B` itself (`ShiftEnvK.realize`):

* `QStrong.twoFunctorShift : UQShift RD S₀ ⥤ᵖ B`, a graded 2-functor: `x⟨t⟩` goes to the image of
  `x` (composite of `E_i` and of the right adjoints `R`) shifted by `t + cWord x`
  (`twoFunctorShift_map`), so that `F_i 1_μ ⟨t⟩` goes to `R⟨t - (α_i, μ - α_i) - d_i⟩ = F_i 1_μ⟨t⟩`;
  on 2-morphisms it is `twoFunctorHOM`, i.e. `interpUQ`, conjugated by the shift isomorphisms
  (`toShiftEnv_map₂_twoFunctorShift_map₂`);
* `QStrong.twoFunctorShift_mapShift`: it commutes with the shift, `F(x⟨t⟩) ≅ F(x⟨0⟩)⟨t⟩`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory
open KrullSchmidtCat (HomFinite)

universe w v u u₁

section Model

open GradedHomBicat GradedHomCat ShiftEnv ShiftEnvK PresGrading
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B]
  [∀ a b : B, HasZeroObject (a ⟶ b)] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]
  [GradedBicategory.ShiftCoherence B] [GradedBicategory.IsLinear B k]
  [∀ a b : B, IsIdempotentComplete (a ⟶ b)] [∀ a b : B, HomFinite k (a ⟶ b)]
  {I : Type*} [DecidableEq I] {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X]
  [AddCommGroup Y] {RD : RootDatum C X Y}

/-- **Rescaling preserves degrees** (a graded strict 2-functor, offset `0`). -/
def gradedRescale {S' : Signature} [S'.IsEven] {χ : S'.Gen → kˣ} {P P' : Presentation S' k}
    (h : ∀ i, P'.lin (CL.Rescale.scL χ (P.rel i)) = 0) (dg : S'.Gen → ℤ) :
    GradedPseudofunctor (presGrading P dg) (presGrading P' dg) where
  F := CL.Rescale.pseudofunctor h
  c _ := 0
  c_id _ := rfl
  c_comp _ _ := rfl
  map₂_mem hη := (presGrading P' dg).mem_of_eq (CL.Rescale.functor_homDeg h hη) (by ring)
  mapId_hom_mem _ := (presGrading P' dg).id_mem _
  mapId_inv_mem _ := (presGrading P' dg).id_mem _
  mapComp_hom_mem _ _ := (presGrading P' dg).id_mem _
  mapComp_inv_mem _ _ := (presGrading P' dg).id_mem _

variable (RD) in
/-- The graded 2-category `U_Q(g)` before direct sums: shifted words `x⟨t⟩`, and diagrams
`x → y` of degree `t' - t` as 2-morphisms `x⟨t⟩ → y⟨t'⟩`. -/
abbrev UQShift (S₀ : CL.CLScalars C k) : Type _ :=
  ShiftEnv (presGrading (CL.presCL RD k S₀) (deg RD))

namespace QStrong

/-- The offset of a 1-morphism of a presented 2-category on the signature of `U`: the offset of its
word. -/
abbrev cHom {P : Presentation (psig RD) k} {a b : RevBicat P.Bicat} (x : a ⟶ b) : ℤ :=
  cWord RD (x : Presentation.Bicat.Hom b.as a.as).obj.word

variable {Q : I → I → MvPolynomial (Fin 2) k} (S : QStrong B C RD k Q) (Sc : CL.CLScalars C k)
  (hP : ∀ s₀ t₀ : X, (CL.presCL RD k Sc).Respects (interp (S.genImg Sc) s₀ t₀).functor)

/-- **The pseudofunctor of the model preserves degrees** up to the offsets of words. -/
def gradedPres : GradedPseudofunctor (presGrading (CL.presCL RD k Sc) (deg RD))
    (ghbGrading k B) where
  F := presPseudofunctor (S.genImg Sc) (CL.presCL RD k Sc) hP
  c x := cHom x
  c_id _ := rfl
  c_comp f g := (cWord_append' _ _).trans (add_comm _ _)
  map₂_mem {a b x y η n} hη :=
    ((isHomogeneous_eqToHom _).comp ((S.isHomogeneous_lift_degOff Sc (CL.presCL RD k Sc)
      b.as.region a.as.region (hP _ _) hη).comp (isHomogeneous_eqToHom _) rfl) rfl).of_eq
      (by simp only [add_zero, zero_add])
  mapId_hom_mem _ := (ghbGrading k B).id_mem _
  mapId_inv_mem _ := (ghbGrading k B).id_mem _
  mapComp_hom_mem f g := mem_ghbGrading.2 (isHomogeneous_lift_map₂ S.model.pre (PresPseudo.splitR f g).hom)
  mapComp_inv_mem f g := mem_ghbGrading.2 (isHomogeneous_lift_map₂ S.model.pre (PresPseudo.splitR f g).inv)

variable (S₀ : CL.CLScalars C k) (S : QStrong B C RD k (CL.qCL S₀))
  (hrQ : ∀ i, S.rQ i = S₀.r i)

/-- The pseudofunctor of shift envelopes induced by `twoFunctorHOM`: rescaling, then the model. -/
abbrev shiftHOM :
    Pseudofunctor (UQShift RD S₀) (ShEnvK k B) :=
  (ShiftEnv.map (gradedRescale ((clRescale RD S₀).inv.lin_scL_rel_inv
      ((clRescale RD S₀).mapScalars S₀) (clRescale_presCL S₀)) (deg RD))).comp
    (ShiftEnv.map (S.gradedPres ((clRescale RD S₀).mapScalars S₀) (respects_clRescale S₀ S hrQ)))

include hrQ in
/-- **CL Theorem 1.1 with grading shifts** (arXiv:1111.1431v3, any symmetrizable Cartan datum,
CL's hypotheses only): a `Q`-strong 2-representation whose KLR action is given by `Q = qCL S₀` and
`r_i = S₀.r i` defines a pseudofunctor from the graded 2-category `U_{S₀}(g)` before direct sums
(shifted words, degree-zero 2-morphisms) to the target bicategory `B`. -/
def twoFunctorShift : Pseudofunctor (UQShift RD S₀) B :=
  realize (shiftHOM S₀ S hrQ)

/-- On 2-morphisms, the induced pseudofunctor of shift envelopes is `twoFunctorHOM`. -/
theorem val₂_shiftHOM_map₂ {a b : UQShift RD S₀} {f g : a ⟶ b} (η : f ⟶ g) :
    val₂ ((shiftHOM S₀ S hrQ).map₂ η) = (twoFunctorHOM S₀ S hrQ).map₂ (val₂ η) := rfl

/-- `x⟨t⟩` goes to the image of the word `x` shifted by `t + cWord x`. -/
theorem twoFunctorShift_map {a b : UQShift RD S₀} (f : a ⟶ b) :
    (twoFunctorShift S₀ S hrQ).map f =
      (bHom ((shiftHOM S₀ S hrQ).map f))⟦f.sh + 0 + cHom ((clRescale₂ S₀).map f.hom)⟧ := rfl

/-- On 2-morphisms, `twoFunctorShift` is `twoFunctorHOM` (hence `interpUQ`) conjugated by the shift
isomorphisms `x⟦t⟧ ≅ x` of the graded-Hom bicategory. -/
theorem toShiftEnv_map₂_twoFunctorShift_map₂ {a b : UQShift RD S₀} {f g : a ⟶ b}
    (η : f ⟶ g) :
    (toShiftEnv k B).map₂ ((twoFunctorShift S₀ S hrQ).map₂ η) =
      (shiftEnvIso ((shiftHOM S₀ S hrQ).map f)).hom ≫
        (shiftHOM S₀ S hrQ).map₂ η ≫
          (shiftEnvIso ((shiftHOM S₀ S hrQ).map g)).inv :=
  toShiftEnv_map₂_realize_map₂ _ η

/-- **Compatibility with the shift**: `F(x⟨t⟩) ≅ F(x⟨0⟩)⟨t⟩`. -/
def twoFunctorShift_mapShift {a b : UQShift RD S₀} (x : a ⟶ b) (t : ℤ) :
    (twoFunctorShift S₀ S hrQ).map (⟨x.hom, t⟩ : a ⟶ b) ≅
      ((twoFunctorShift S₀ S hrQ).map (⟨x.hom, 0⟩ : a ⟶ b))⟦t⟧ :=
  (shiftFunctorAdd' _ (0 + 0 + cHom ((clRescale₂ S₀).map x.hom)) t
    (t + 0 + cHom ((clRescale₂ S₀).map x.hom)) (by ring)).app _

end QStrong

end Model

end Categorification.TwoRep
