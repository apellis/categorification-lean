/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalBraidProjectives
import Categorification.WeightedKLR.Rigidity.FundamentalBraidComplex
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Homology of the fundamental projective resolution tensored with the braid

In Webster, arXiv:1309.3796v2, Proposition 7.11, tensoring the
projective resolution of the fundamental middle head with the positive
braid gives a single homology line in resolution degree one. This uses
the ordinary balanced tensors over the diagonal source ring, with all
maps induced by the differentials of that resolution.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory
local notation "S" => fundamentalBraidCutComplex
private abbrev forgetQ := ModuleCat.restrictScalars (Int.castRingHom ℚ)

private theorem up_comm (z : braidTensorMiddle) :
    braidTensorTerminalEquiv (braidTensorD₂ z) = (S).f (braidTensorMiddleEquiv z) :=
  Subtype.ext (fundamentalBraidSourceResolution_tensor.1 z)

private theorem down_comm (z : braidTensorTerminal) :
    braidTensorMiddleEquiv (braidTensorD₁ z) = (S).g (braidTensorTerminalEquiv z) :=
  Subtype.ext (fundamentalBraidSourceResolution_tensor.2 z)

/-- The balanced tensor of the fundamental middle projective resolution
with Webster's braid bimodule, as a complex of abelian groups. -/
def fundamentalBraidTensorComplex : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (ModuleCat.ofHom braidTensorD₂.toIntLinearMap) (ModuleCat.ofHom braidTensorD₁.toIntLinearMap) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change braidTensorD₁ (braidTensorD₂ z) = 0
    apply braidTensorMiddleEquiv.injective
    rw [map_zero,down_comm,up_comm]
    exact (S).moduleCat_zero_apply _)

private def termIso {X : Type} [AddCommGroup X] (Y : ModuleCat ℚ) (e : X ≃+ Y) :
    ModuleCat.of ℤ X ≅ forgetQ.obj Y := e.toIntLinearEquiv.toModuleIso

/-- The comparison between the balanced tensor and the loading cuts is a
chain isomorphism for the fundamental resolution in Webster v2, Proposition 7.11. -/
def fundamentalBraidTensorCutIso : fundamentalBraidTensorComplex ≅ (S).map forgetQ :=
  ShortComplex.isoMk (termIso (S).X₁ braidTensorMiddleEquiv.toAddEquiv)
    (termIso (S).X₂ braidTensorTerminalEquiv.toAddEquiv) (termIso (S).X₃ braidTensorMiddleEquiv.toAddEquiv)
    (by apply ModuleCat.hom_ext; exact LinearMap.ext fun z => (up_comm z).symm)
    (by apply ModuleCat.hom_ext; exact LinearMap.ext fun z => (down_comm z).symm)

/-- The balanced tensor complex for Webster v2, Proposition 7.11 has
no degree-zero or degree-two homology and one rational line in degree one. -/
def fundamentalBraidTensorHomologyIso :
    fundamentalBraidTensorComplex.homology ≅ forgetQ.obj (ModuleCat.of ℚ ℚ) :=
  (ShortComplex.homologyFunctor (ModuleCat ℤ)).mapIso fundamentalBraidTensorCutIso ≪≫
    (S).mapHomologyIso forgetQ ≪≫ forgetQ.mapIso fundamentalBraidCutComplex_homologyIso

theorem fundamentalBraidTensorComplex_ends :
    Function.Injective fundamentalBraidTensorComplex.f ∧ Function.Surjective fundamentalBraidTensorComplex.g := by
  constructor
  · intro x y he
    apply braidTensorMiddleEquiv.injective
    apply fundamentalBraidCutComplex_ends.1
    exact (up_comm _).symm.trans ((congrArg braidTensorTerminalEquiv he).trans (up_comm _))
  · intro z
    obtain ⟨y,hy⟩ := fundamentalBraidCutComplex_ends.2 (braidTensorMiddleEquiv z)
    obtain ⟨x,rfl⟩ := braidTensorTerminalEquiv.surjective y
    exact ⟨x,braidTensorMiddleEquiv.injective ((down_comm x).trans hy)⟩

end Categorification.Stendhal.FundamentalCorner
