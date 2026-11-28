/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.TensorRepresentedFunctor

/-!
# Invariance of tensor representability

Being represented by tensoring with the value on the ring (`IsTensorRepresented`) is invariant
under natural isomorphism (`IsTensorRepresented.of_iso`) and does not see a restriction of
scalars on the target (`isTensorRepresented_comp_restrictScalars_iff`): the Eilenberg–Watts map
of `F ⋙ restrictScalars ψ` is that of `F`.

Used to identify the standardization functors of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, §5, with tensor products with the standard
bimodules, for the proof of Lemma 7.19.
-/

noncomputable section

namespace Categorification.TensorRepresented

open CategoryTheory DG MulOpposite

universe u

variable {A B : Type u} [Ring A] [Ring B] {F G : ModuleCat.{u} B ⥤ ModuleCat.{u} A}
  [F.Additive] [G.Additive]

/-- A natural isomorphism `F ≅ G` at the regular module, as an isomorphism of right
`B`-modules `F(B) ≅ G(B)`. -/
def bimodEquivOfIso (e : F ≅ G) : Bimod F ≃ₗ[Bᵐᵒᵖ] Bimod G where
  toFun := (e.hom.app (ModuleCat.of B B)).hom
  invFun := (e.inv.app (ModuleCat.of B B)).hom
  map_add' := map_add _
  map_smul' b p := by
    change (e.hom.app _).hom ((F.map (rmul (ModuleCat.of B B) b.unop)).hom p) =
      (G.map (rmul (ModuleCat.of B B) b.unop)).hom ((e.hom.app _).hom p)
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, e.hom.naturality]
  left_inv p := by
    change (e.hom.app _ ≫ e.inv.app _).hom p = p
    rw [Iso.hom_inv_id_app]; rfl
  right_inv p := by
    change (e.inv.app _ ≫ e.hom.app _).hom p = p
    rw [Iso.inv_hom_id_app]; rfl

theorem ewMap_of_iso (e : F ≅ G) (Z : ModuleCat.{u} B) (t : TensorProductOver B (Bimod F) Z) :
    ewMap G Z (TensorProductOver.map (bimodEquivOfIso e).toLinearMap LinearMap.id t) =
      (e.hom.app Z).hom (ewMap F Z t) := by
  induction t using TensorProductOver.induction_on with
  | zero => simp only [map_zero]
  | tmul p z =>
    change (G.map (rmul Z z)).hom ((e.hom.app _).hom p) = (e.hom.app Z).hom
      ((F.map (rmul Z z)).hom p)
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, e.hom.naturality]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **Tensor representability is invariant under natural isomorphism.** -/
theorem IsTensorRepresented.of_iso (e : F ≅ G) (hF : IsTensorRepresented F) :
    IsTensorRepresented G := by
  intro Z
  have hm := tensorProductOver_map_bijective (bimodEquivOfIso e) (LinearEquiv.refl B Z)
  have he : Function.Bijective (e.hom.app Z).hom :=
    ((e.app Z).toLinearEquiv).bijective
  have : (ewMap G Z).comp (TensorProductOver.map (bimodEquivOfIso e).toLinearMap
      (LinearEquiv.refl B Z).toLinearMap) = (e.hom.app Z).hom.toAddMonoidHom.comp (ewMap F Z) :=
    AddMonoidHom.ext fun t => ewMap_of_iso e Z t
  have hcomp : Function.Bijective ((ewMap G Z).comp (TensorProductOver.map
      (bimodEquivOfIso e).toLinearMap (LinearEquiv.refl B Z).toLinearMap)) := by
    rw [this]; exact he.comp (hF Z)
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · obtain ⟨x', rfl⟩ := hm.2 x
    obtain ⟨y', rfl⟩ := hm.2 y
    exact congrArg _ (hcomp.1 hxy)
  · obtain ⟨x, hx⟩ := hcomp.2 y
    exact ⟨_, hx⟩

variable {A' : Type u} [Ring A'] (ψ : A' →+* A)

/-- Restricting scalars on the target does not change the Eilenberg–Watts maps. -/
theorem isTensorRepresented_comp_restrictScalars_iff :
    IsTensorRepresented (F ⋙ ModuleCat.restrictScalars.{u} ψ) ↔ IsTensorRepresented F :=
  Iff.rfl

end Categorification.TensorRepresented
