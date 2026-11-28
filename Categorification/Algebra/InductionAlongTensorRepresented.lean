/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongRes
import Categorification.Algebra.TensorRepresentedFunctor

/-!
# Induction and restriction along nonunital maps are tensoring with bimodules

For a nonunital ring map `φ : A →ₙ+* B`, induction `N ↦ B φ(1) ⊗_A N` and restriction
`M ↦ φ(1) M` are represented by tensoring with their values on the regular module
(`InductionAlong.isTensorRepresented_functor`, `InductionAlong.isTensorRepresented_resFunctor`).

A natural transformation between two functors represented by tensoring is invertible as soon
as its component at the regular module is bijective
(`TensorRepresented.isIso_of_bijective_app_regular`). This is how the commutation
`Eᵢ Fⱼ ≅ Fⱼ Eᵢ` (`i ≠ j`) of Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v3, Theorem 4.31, on all right modules over the tensor product algebras is
reduced to the regular module (Brundan, arXiv:1501.00350v1, (1.7)).
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.TensorProductOver.RightAction

universe u

namespace TensorRepresented

variable {A B : Type u} [Ring A] [Ring B] {F G : ModuleCat.{u} B ⥤ ModuleCat.{u} A}
  [F.Additive] [G.Additive]

/-- The component of a natural transformation at the regular module, as a map of right
`B`-modules. -/
def bimodMap (α : F ⟶ G) : Bimod F →ₗ[Bᵐᵒᵖ] Bimod G where
  toFun := (α.app (ModuleCat.of B B)).hom
  map_add' := map_add _
  map_smul' b p := by
    change (α.app _).hom ((F.map (rmul (ModuleCat.of B B) b.unop)).hom p) =
      (G.map (rmul (ModuleCat.of B B) b.unop)).hom ((α.app _).hom p)
    rw [← ModuleCat.comp_apply, α.naturality]
    rfl

/-- The Eilenberg–Watts maps intertwine a natural transformation with its component at the
regular module. -/
theorem app_ewMap (α : F ⟶ G) (Z : ModuleCat.{u} B) (t : TensorProductOver B (Bimod F) Z) :
    (α.app Z).hom (ewMap F Z t) =
      ewMap G Z (TensorProductOver.map (bimodMap α) LinearMap.id t) := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul p z =>
    rw [TensorProductOver.map_tmul, ewMap_tmul, ewMap_tmul, LinearMap.id_apply]
    change (α.app Z).hom ((F.map (rmul Z z)).hom p) = (G.map (rmul Z z)).hom ((α.app _).hom p)
    rw [← ModuleCat.comp_apply, α.naturality]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

/-- **A natural transformation of functors represented by tensoring is invertible when its
component at the regular module is bijective.** -/
theorem isIso_of_bijective_app_regular (hF : IsTensorRepresented F)
    (hG : IsTensorRepresented G) (α : F ⟶ G)
    (h : Function.Bijective (α.app (ModuleCat.of B B)).hom) : IsIso α := by
  have hm : ∀ Z : ModuleCat.{u} B, Function.Bijective (α.app Z).hom := fun Z => by
    let e : Bimod F ≃ₗ[Bᵐᵒᵖ] Bimod G := LinearEquiv.ofBijective (bimodMap α) h
    have hmap := tensorProductOver_map_bijective e (LinearEquiv.refl B Z)
    have hcomp : (α.app Z).hom ∘ ewMap F Z =
        ewMap G Z ∘ TensorProductOver.map (bimodMap α) LinearMap.id := funext (app_ewMap α Z)
    have hr : Function.Bijective ((α.app Z).hom ∘ ewMap F Z) := by
      rw [hcomp]
      exact (hG Z).comp hmap
    refine ⟨fun x y hxy => ?_, fun y => ?_⟩
    · obtain ⟨x', rfl⟩ := (hF Z).2 x
      obtain ⟨y', rfl⟩ := (hF Z).2 y
      exact congrArg _ (hr.1 hxy)
    · obtain ⟨x, hx⟩ := hr.2 y
      exact ⟨_, hx⟩
  have : ∀ Z, IsIso (α.app Z) := fun Z => (ConcreteCategory.isIso_iff_bijective _).2 (hm Z)
  exact NatIso.isIso_of_isIso_app α

end TensorRepresented

namespace InductionAlong

open TensorRepresented

variable {A B : Type u} [Ring A] [Ring B] (φ : A →ₙ+* B)

/-- The generator `z ⊗ 1` of the induction of the regular module. -/
def indGen (z : Corner φ) : Bimod (functor.{u, u} φ) := (Ind.tmul z (1 : A) : Ind A φ)

/-- The inverse of the Eilenberg–Watts map of induction: `z ⊗ n ↦ (z ⊗ 1) ⊗ n`. -/
def indEwInv (Z : ModuleCat.{u} A) :
    Ind Z φ →+ TensorProductOver A (Bimod (functor.{u, u} φ)) Z :=
  Ind.liftAdd (fun z n => TensorProductOver.tmul A (indGen φ z) n)
    (fun z z' n => by
      rw [show indGen φ (z + z') = indGen φ z + indGen φ z' from Ind.add_tmul z z' 1,
        TensorProductOver.add_tmul])
    (fun z n n' => TensorProductOver.tmul_add _ n n')
    (fun z a n => by
      rw [← TensorProductOver.op_smul_tmul]
      congr 1
      change (Ind.tmul (op a • z) 1 : Ind A φ) = Ind.tmul z ((1 : A) • a)
      rw [Ind.op_smul_tmul, smul_eq_mul, smul_eq_mul, mul_one, one_mul])

/-- **Induction along a nonunital ring map is tensoring with `B φ(1)`.** -/
theorem isTensorRepresented_functor : IsTensorRepresented (functor.{u, u} φ) := by
  intro Z
  let F := functor.{u, u} φ
  have key : ∀ (p : Ind A φ) (z : Z), indEwInv φ Z (ewMap F Z
      (TensorProductOver.tmul A (show Bimod F from p) z)) =
        TensorProductOver.tmul A (show Bimod F from p) z := fun p z => by
    induction p using Ind.induction_on with
    | zero =>
      change indEwInv φ Z (ewMap F Z (TensorProductOver.tmul A (0 : Bimod F) z)) =
        TensorProductOver.tmul A (0 : Bimod F) z
      rw [TensorProductOver.zero_tmul, map_zero]
      exact map_zero (indEwInv φ Z)
    | tmul w x =>
      change TensorProductOver.tmul A (indGen φ w) (x • z) = _
      rw [← TensorProductOver.op_smul_tmul]
      congr 1
      change (Ind.tmul w ((1 : A) • x) : Ind A φ) = Ind.tmul w x
      rw [smul_eq_mul, one_mul]
    | add s t hs ht =>
      change indEwInv φ Z (ewMap F Z (TensorProductOver.tmul A
        ((show Bimod F from s) + (show Bimod F from t)) z)) =
          TensorProductOver.tmul A ((show Bimod F from s) + (show Bimod F from t)) z
      rw [TensorProductOver.add_tmul, map_add]
      exact (map_add (indEwInv φ Z) _ _).trans (by rw [hs, ht])
  have hl : ∀ t, indEwInv φ Z (ewMap F Z t) = t := fun t => by
    induction t using TensorProductOver.induction_on with
    | zero => rw [map_zero]; exact map_zero (indEwInv φ Z)
    | tmul p z => exact key p z
    | add x y hx hy => rw [map_add]; exact (map_add (indEwInv φ Z) _ _).trans (by rw [hx, hy])
  have hr : ∀ y : Ind Z φ, ewMap F Z (indEwInv φ Z y) = (show F.obj Z from y) := fun y => by
    induction y using Ind.induction_on with
    | zero => rw [map_zero, map_zero]; rfl
    | tmul w n =>
      change (Ind.tmul w ((1 : A) • n) : Ind Z φ) = Ind.tmul w n
      rw [one_smul]
    | add s t hs ht => rw [map_add, map_add, hs, ht]; rfl
  exact ⟨Function.LeftInverse.injective hl, fun y => ⟨indEwInv φ Z y, hr y⟩⟩

/-- **Restriction along a nonunital ring map is tensoring with `φ(1) B`.** -/
theorem isTensorRepresented_resFunctor : IsTensorRepresented (resFunctor.{u, u} φ) := by
  intro Z
  let e : Bimod (resFunctor.{u, u} φ) := (Res.mk (φ 1) (unit_mul_unit φ) : Res φ B)
  let ψ : Res φ Z →+ TensorProductOver B (Bimod (resFunctor.{u, u} φ)) Z :=
    { toFun := fun m => TensorProductOver.tmul B e m.val
      map_zero' := TensorProductOver.tmul_zero e
      map_add' := fun m m' => TensorProductOver.tmul_add e m.val m'.val }
  have hl : ∀ t, ψ (ewMap (resFunctor.{u, u} φ) Z t) = t := fun t => by
    induction t using TensorProductOver.induction_on with
    | zero => rw [map_zero]; exact map_zero ψ
    | tmul p z =>
      change TensorProductOver.tmul B e ((show Res φ B from p).val • z) = _
      rw [← TensorProductOver.op_smul_tmul]
      congr 1
      apply Res.ext
      change φ 1 * (show Res φ B from p).val = (show Res φ B from p).val
      exact (show Res φ B from p).prop
    | add x y hx hy => rw [map_add]; exact (map_add ψ _ _).trans (by rw [hx, hy])
  refine ⟨Function.LeftInverse.injective hl, fun m => ⟨ψ m, ?_⟩⟩
  apply Res.ext
  change φ 1 • m.val = m.val
  exact m.prop

end InductionAlong

end Categorification
