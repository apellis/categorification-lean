/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import DG.Module.TensorProductOver

/-!
# Functors of module categories given by tensoring with their value on the ring

For an additive functor `F : ModuleCat B ⥤ ModuleCat A`, the value `F(B)` on the regular module
is an `(A, B)`-bimodule, `B` acting through `F` of the right multiplications
(`TensorRepresented.Bimod`). The **Eilenberg–Watts map**
`θ_Z : F(B) ⊗_B Z → F(Z)`, `p ⊗ z ↦ F(b ↦ b z)(p)`, is natural and `A`-linear
(`TensorRepresented.ewMap`). `F` is *represented by tensoring* when every `θ_Z` is bijective
(`IsTensorRepresented`); then `F(Z) ≅ F(B) ⊗_B Z` naturally (`ewEquiv`, `ewEquiv_natural`).

The class is closed under composition (`IsTensorRepresented.comp`), and restriction of
scalars along a ring map is represented by tensoring (`isTensorRepresented_restrictScalars`).
This is how the standardization functors of B. Webster, *Knot invariants and higher
representation theory*, arXiv:1309.3796v3, §5, built in stages from inductions, quotients and
restrictions, are identified with tensor products with the standard bimodules, as used in the
proof of Lemma 7.19.
-/

noncomputable section

namespace Categorification

open CategoryTheory DG MulOpposite
open scoped DG.TensorProductOver.RightAction

universe u

namespace TensorRepresented

variable {A B : Type u} [Ring A] [Ring B] (F : ModuleCat.{u} B ⥤ ModuleCat.{u} A) [F.Additive]

/-- The map `b ↦ b • z` from the regular module. -/
abbrev rmul (Z : ModuleCat.{u} B) (z : Z) : ModuleCat.of B B ⟶ Z :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton B Z z)

/-- `F(B)`, as an `(A, B)`-bimodule. -/
abbrev Bimod : Type u := F.obj (ModuleCat.of B B)

/-- The identification of `Bimod F` with `F(B)`. -/
def toBimod : F.obj (ModuleCat.of B B) ≃ₗ[A] Bimod F := LinearEquiv.refl A _

theorem rmul_comp_rmul (b c : B) :
    rmul (ModuleCat.of B B) b ≫ rmul (ModuleCat.of B B) c =
      rmul (ModuleCat.of B B) (b * c) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change (x • b) • c = x • (b * c)
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_assoc]

theorem rmul_comp_rmul' (Z : ModuleCat.{u} B) (b : B) (z : Z) :
    rmul (ModuleCat.of B B) b ≫ rmul Z z = rmul Z (b • z) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change (x • b) • z = x • b • z
  rw [smul_eq_mul, mul_smul]

instance : SMul Bᵐᵒᵖ (Bimod F) where
  smul b p := (F.map (rmul (ModuleCat.of B B) b.unop)).hom p

omit [F.Additive] in
theorem op_smul_def (b : Bᵐᵒᵖ) (p : Bimod F) :
    b • p = (F.map (rmul (ModuleCat.of B B) b.unop)).hom p := rfl

instance : Module Bᵐᵒᵖ (Bimod F) where
  one_smul p := by
    rw [op_smul_def]
    have : rmul (ModuleCat.of B B) (unop 1) = 𝟙 _ := by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      change x • (1 : B) = x
      rw [smul_eq_mul, mul_one]
    rw [this, F.map_id]; rfl
  mul_smul b c p := by
    rw [op_smul_def, op_smul_def, op_smul_def, unop_mul, ← rmul_comp_rmul, F.map_comp]; rfl
  smul_zero b := map_zero _
  smul_add b := map_add _
  add_smul b c p := by
    rw [op_smul_def, op_smul_def, op_smul_def]
    have : rmul (ModuleCat.of B B) (unop (b + c)) =
        rmul (ModuleCat.of B B) b.unop + rmul (ModuleCat.of B B) c.unop := by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      change x • (unop b + unop c) = x • unop b + x • unop c
      rw [smul_add]
    rw [this, F.map_add]; rfl
  zero_smul p := by
    rw [op_smul_def]
    have : rmul (ModuleCat.of B B) (unop 0) = 0 := by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_); change x • (0 : B) = 0; rw [smul_zero]
    rw [this, F.map_zero]; rfl

instance : SMulCommClass A Bᵐᵒᵖ (Bimod F) where
  smul_comm a b p := ((F.map (rmul (ModuleCat.of B B) b.unop)).hom.map_smul a p).symm

/-- **The Eilenberg–Watts map** `θ_Z : F(B) ⊗_B Z → F(Z)`, `p ⊗ z ↦ F(b ↦ b z)(p)`. -/
def ewMap (Z : ModuleCat.{u} B) : TensorProductOver B (Bimod F) Z →+ F.obj Z :=
  TensorProductOver.lift
    { toFun := fun p =>
        { toFun := fun z => (F.map (rmul Z z)).hom p
          map_zero' := by
            have : rmul Z 0 = 0 := by
              refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
              exact smul_zero x
            rw [this, F.map_zero]; rfl
          map_add' := fun z z' => by
            have : rmul Z (z + z') = rmul Z z + rmul Z z' := by
              refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_); exact smul_add x z z'
            rw [this, F.map_add]; rfl }
      map_zero' := by ext z; exact map_zero (F.map (rmul Z z)).hom
      map_add' := fun p p' => by ext z; exact map_add (F.map (rmul Z z)).hom p p' }
    (fun b p z => by
      change (F.map (rmul Z z)).hom ((F.map (rmul (ModuleCat.of B B) b)).hom p) =
        (F.map (rmul Z (b • z))).hom p
      rw [← rmul_comp_rmul', F.map_comp]; rfl)

@[simp]
theorem ewMap_tmul (Z : ModuleCat.{u} B) (p : Bimod F) (z : Z) :
    ewMap F Z (TensorProductOver.tmul B p z) = (F.map (rmul Z z)).hom p := rfl

theorem ewMap_smul (Z : ModuleCat.{u} B) (a : A) (t : TensorProductOver B (Bimod F) Z) :
    ewMap F Z (a • t) = a • ewMap F Z t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul p z =>
    rw [TensorProductOver.smul_tmul, ewMap_tmul, ewMap_tmul]
    exact (F.map (rmul Z z)).hom.map_smul a p
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The Eilenberg–Watts map as an `A`-linear map. -/
def ewLinear (Z : ModuleCat.{u} B) : TensorProductOver B (Bimod F) Z →ₗ[A] F.obj Z where
  toFun := ewMap F Z
  map_add' := map_add _
  map_smul' := ewMap_smul F Z

/-- Naturality of the Eilenberg–Watts map. -/
theorem ewMap_natural {Z Y : ModuleCat.{u} B} (g : Z ⟶ Y) (t : TensorProductOver B (Bimod F) Z) :
    (F.map g).hom (ewMap F Z t) =
      ewMap F Y (TensorProductOver.map LinearMap.id g.hom t) := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul p z =>
    rw [TensorProductOver.map_tmul, ewMap_tmul, ewMap_tmul, LinearMap.id_apply]
    have : rmul Z z ≫ g = rmul Y (g.hom z) := by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_); exact g.hom.map_smul x z
    rw [← this, F.map_comp]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

end TensorRepresented

open TensorRepresented

/-- `F` is **represented by tensoring** with `F(B)`: every Eilenberg–Watts map is bijective. -/
def IsTensorRepresented {A B : Type u} [Ring A] [Ring B]
    (F : ModuleCat.{u} B ⥤ ModuleCat.{u} A) [F.Additive] : Prop :=
  ∀ Z : ModuleCat.{u} B, Function.Bijective (ewMap F Z)

namespace TensorRepresented

variable {A B : Type u} [Ring A] [Ring B] (F : ModuleCat.{u} B ⥤ ModuleCat.{u} A) [F.Additive]

/-- **`F(Z) ≅ F(B) ⊗_B Z`** for a functor represented by tensoring. -/
def ewEquiv (hF : IsTensorRepresented F) (Z : ModuleCat.{u} B) :
    TensorProductOver B (Bimod F) Z ≃ₗ[A] F.obj Z :=
  LinearEquiv.ofBijective (ewLinear F Z) (hF Z)

theorem ewEquiv_apply (hF : IsTensorRepresented F) (Z : ModuleCat.{u} B)
    (t : TensorProductOver B (Bimod F) Z) : ewEquiv F hF Z t = ewMap F Z t := rfl

theorem ewEquiv_natural (hF : IsTensorRepresented F) {Z Y : ModuleCat.{u} B} (g : Z ⟶ Y)
    (t : TensorProductOver B (Bimod F) Z) :
    (F.map g).hom (ewEquiv F hF Z t) =
      ewEquiv F hF Y (TensorProductOver.map LinearMap.id g.hom t) :=
  ewMap_natural F g t

end TensorRepresented

section MapEquiv

variable {R : Type*} [Ring R] {M M' N N' : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [AddCommGroup M'] [Module Rᵐᵒᵖ M'] [AddCommGroup N] [Module R N] [AddCommGroup N']
  [Module R N']

/-- The tensor product of two linear equivalences is bijective. -/
theorem tensorProductOver_map_bijective (e : M ≃ₗ[Rᵐᵒᵖ] M') (e' : N ≃ₗ[R] N') :
    Function.Bijective (TensorProductOver.map e.toLinearMap e'.toLinearMap) := by
  have h₁ : (TensorProductOver.map e.symm.toLinearMap e'.symm.toLinearMap).comp
      (TensorProductOver.map e.toLinearMap e'.toLinearMap) = AddMonoidHom.id _ :=
    TensorProductOver.addHom_ext fun m n => by simp
  have h₂ : (TensorProductOver.map e.toLinearMap e'.toLinearMap).comp
      (TensorProductOver.map e.symm.toLinearMap e'.symm.toLinearMap) = AddMonoidHom.id _ :=
    TensorProductOver.addHom_ext fun m n => by simp
  refine ⟨Function.LeftInverse.injective (g := TensorProductOver.map e.symm.toLinearMap
    e'.symm.toLinearMap) fun t => DFunLike.congr_fun h₁ t, Function.RightInverse.surjective
    (g := TensorProductOver.map e.symm.toLinearMap e'.symm.toLinearMap) fun t =>
      DFunLike.congr_fun h₂ t⟩

end MapEquiv

namespace TensorRepresented

/-- **Restriction of scalars is represented by tensoring**: `B' ⊗_{B'} Z ≅ Z` over `B`. -/
theorem isTensorRepresented_restrictScalars {B B' : Type u} [Ring B] [Ring B'] (φ : B →+* B') :
    IsTensorRepresented (ModuleCat.restrictScalars.{u} φ) := by
  intro Z
  let ψ : (ModuleCat.restrictScalars.{u} φ).obj Z →+
      TensorProductOver B' (Bimod (ModuleCat.restrictScalars.{u} φ)) Z :=
    (TensorProductOver.tmulAddHom B' _ Z) (show B' from 1)
  have hl : ∀ t, ψ (ewMap _ Z t) = t := fun t => by
    induction t using TensorProductOver.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul p z =>
      change TensorProductOver.tmul B' (show B' from 1) ((show B' from p) • z) = _
      rw [← TensorProductOver.op_smul_tmul]
      congr 1
      change (show B' from 1) • (show B' from p) = p
      rw [smul_eq_mul, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  refine ⟨Function.LeftInverse.injective hl, fun z => ⟨ψ z, ?_⟩⟩
  change (show B' from 1) • z = z
  exact one_smul B' z

variable {A B C : Type u} [Ring A] [Ring B] [Ring C] (F : ModuleCat.{u} B ⥤ ModuleCat.{u} A)
  [F.Additive] (G : ModuleCat.{u} A ⥤ ModuleCat.{u} C) [G.Additive]

/-- The Eilenberg–Watts map of `G` at `F(B)`, as a map of right `B`-modules. -/
def compBimodEquiv (hG : IsTensorRepresented G) :
    TensorProductOver A (Bimod G) (Bimod F) ≃ₗ[Bᵐᵒᵖ] Bimod (F ⋙ G) where
  toFun := ewMap G (F.obj (ModuleCat.of B B))
  invFun := (ewEquiv G hG (F.obj (ModuleCat.of B B))).symm
  map_add' := map_add _
  map_smul' b t := by
    change ewMap G _ (TensorProductOver.rightAct A (Bimod G) (Bimod F) b t) =
      (G.map (F.map (rmul (ModuleCat.of B B) b.unop))).hom (ewMap G _ t)
    rw [ewMap_natural]
    exact congrArg _ (DFunLike.congr_fun (TensorProductOver.addHom_ext
      (f := TensorProductOver.rightAct A (Bimod G) (Bimod F) b)
      (g := TensorProductOver.map LinearMap.id (F.map (rmul (ModuleCat.of B B) b.unop)).hom)
      fun _ _ => rfl) t)
  left_inv t := (ewEquiv G hG _).symm_apply_apply t
  right_inv t := (ewEquiv G hG _).apply_symm_apply t

/-- **Functors represented by tensoring compose.** -/
theorem IsTensorRepresented.comp (hF : IsTensorRepresented F) (hG : IsTensorRepresented G) :
    IsTensorRepresented (F ⋙ G) := by
  intro Z
  let m₁ := TensorProductOver.map (compBimodEquiv F G hG).toLinearMap
    (LinearEquiv.refl B Z).toLinearMap
  let a := TensorProductOver.assoc A B (Bimod G) (Bimod F) Z
  let m₂ := TensorProductOver.map (LinearEquiv.refl Aᵐᵒᵖ (Bimod G)).toLinearMap
    (ewEquiv F hF Z).toLinearMap
  have hm₁ := tensorProductOver_map_bijective (compBimodEquiv F G hG) (LinearEquiv.refl B Z)
  have hm₂ := tensorProductOver_map_bijective (LinearEquiv.refl Aᵐᵒᵖ (Bimod G))
    (ewEquiv F hF Z)
  have ha : Function.Bijective a :=
    ⟨Function.LeftInverse.injective (g := TensorProductOver.assocInv A B _ _ Z)
      (TensorProductOver.assocInv_assoc (A := A) (B := B)),
     Function.RightInverse.surjective (g := TensorProductOver.assocInv A B _ _ Z)
      (TensorProductOver.assoc_assocInv (A := A) (B := B))⟩
  have hcomm : ∀ t, ewMap (F ⋙ G) Z (m₁ t) = ewMap G (F.obj Z) (m₂ (a t)) := fun t => by
    induction t using TensorProductOver.induction_on with
    | zero => simp only [map_zero]
    | tmul x z =>
      induction x using TensorProductOver.induction_on with
      | zero => simp only [TensorProductOver.zero_tmul, map_zero]
      | tmul g f =>
        change (G.map (F.map (rmul Z z))).hom ((G.map (rmul _ f)).hom g) =
          (G.map (rmul (F.obj Z) ((F.map (rmul Z z)).hom f))).hom g
        have h : (G.map (F.map (rmul Z z))).hom ((G.map (rmul _ f)).hom g) =
            (G.map (rmul _ f ≫ F.map (rmul Z z))).hom g := by
          rw [G.map_comp]; rfl
        have h' : rmul _ f ≫ F.map (rmul Z z) = rmul (F.obj Z) ((F.map (rmul Z z)).hom f) :=
          ModuleCat.hom_ext (LinearMap.ext fun (c : A) => (F.map (rmul Z z)).hom.map_smul c f)
        rw [h, h']
      | add x y hx hy => rw [TensorProductOver.add_tmul, map_add, map_add, hx, hy, map_add,
          map_add, map_add]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add]
  have hθ : ewMap (F ⋙ G) Z = (ewMap G (F.obj Z)).comp (m₂.comp (a.comp
      (TensorProductOver.map (compBimodEquiv F G hG).symm.toLinearMap
        (LinearEquiv.refl B Z).toLinearMap))) := by
    refine TensorProductOver.addHom_ext fun q z => ?_
    have := hcomm (TensorProductOver.tmul B ((compBimodEquiv F G hG).symm q) z)
    simp only [m₁, TensorProductOver.map_tmul, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearEquiv.refl_apply] at this
    simpa [AddMonoidHom.comp_apply] using this
  rw [hθ]
  exact (hG (F.obj Z)).comp (hm₂.comp (ha.comp
    (tensorProductOver_map_bijective (compBimodEquiv F G hG).symm (LinearEquiv.refl B Z))))

end TensorRepresented

end Categorification
