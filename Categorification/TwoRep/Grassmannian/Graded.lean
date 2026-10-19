/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Grassmannian.Bicategory

/-!
# The graded bicategory of graded bimodules

The bicategory `GrAlg k` of graded bimodules (`Grassmannian/Bicategory.lean`) is a graded additive
`k`-linear bicategory in the sense of `GradedBicategory`: the Hom categories are `k`-linear with
zero object and binary biproducts, and whiskering is additive, `k`-linear and commutes with the
grading shift. The shift isomorphisms `X ⊗_B Y⟨n⟩ ≅ (X ⊗_B Y)⟨n⟩ ≅ X⟨n⟩ ⊗_B Y` are the identity on
underlying vector spaces.

This is the ambient 2-category for the strong 2-representations of `sl₂` (S. Cautis, A. D. Lauda,
*Implicit structure in 2-representations of quantum groups*, arXiv:1111.1431v3, Definition 1.2)
built from cohomology rings of Grassmannians in `Grassmannian/StrongSl2.lean`.
-/

noncomputable section

namespace Categorification.TwoRep.Grassmannian

open CategoryTheory CategoryTheory.Limits TensorProduct Bicategory

universe u

variable {k : Type u} [Field k]

namespace GBim

variable {A B C : GrAlg k}

/-- `X ⊗ Y⟨n⟩ ≅ (X ⊗ Y)⟨n⟩`, the identity on underlying vector spaces. -/
def whiskerLeftShift (X : GBim A B) (Y : GBim B C) (n : ℤ) :
    comp X (Y.shiftObj n) ≅ (comp X Y).shiftObj n where
  hom := mkHomₗ (cmap (X' := X) (Y' := Y) LinearMap.id LinearMap.id (fun _ _ => rfl) (fun _ _ => rfl))
    (fun a => comp_ext fun x y => rfl) (fun c => comp_ext fun x y => rfl)
    (comp_ext fun x y => by
      simp only [LinearMap.comp_apply, comp_D_tmk, shiftObj_D, LinearMap.sub_apply, map_add,
        map_sub, cmap_tmk, LinearMap.id_apply, LinearMap.smul_apply, Module.End.one_apply,
        tmul_sub, tmul_smul, map_zsmul]
      abel)
  inv := mkHomₗ (cmap (X := X) (Y := Y) LinearMap.id LinearMap.id (fun _ _ => rfl) (fun _ _ => rfl))
    (fun a => comp_ext fun x y => rfl) (fun c => comp_ext fun x y => rfl)
    (comp_ext fun x y => by
      simp only [LinearMap.comp_apply, comp_D_tmk, shiftObj_D, LinearMap.sub_apply, map_add,
        map_sub, cmap_tmk, LinearMap.id_apply, LinearMap.smul_apply, Module.End.one_apply,
        tmul_sub, tmul_smul, map_zsmul]
      abel)
  hom_inv_id := hom_ext (comp_ext fun x y => rfl)
  inv_hom_id := hom_ext (comp_ext fun x y => rfl)

/-- `X⟨n⟩ ⊗ Y ≅ (X ⊗ Y)⟨n⟩`, the identity on underlying vector spaces. -/
def whiskerRightShift (X : GBim A B) (Y : GBim B C) (n : ℤ) :
    comp (X.shiftObj n) Y ≅ (comp X Y).shiftObj n where
  hom := mkHomₗ (cmap (X' := X) (Y' := Y) LinearMap.id LinearMap.id (fun _ _ => rfl) (fun _ _ => rfl))
    (fun a => comp_ext fun x y => rfl) (fun c => comp_ext fun x y => rfl)
    (comp_ext fun x y => by
      simp only [LinearMap.comp_apply, comp_D_tmk, shiftObj_D, LinearMap.sub_apply, map_add,
        map_sub, cmap_tmk, LinearMap.id_apply, LinearMap.smul_apply, Module.End.one_apply,
        sub_tmul, ← smul_tmul', map_zsmul]
      abel)
  inv := mkHomₗ (cmap (X := X) (Y := Y) LinearMap.id LinearMap.id (fun _ _ => rfl) (fun _ _ => rfl))
    (fun a => comp_ext fun x y => rfl) (fun c => comp_ext fun x y => rfl)
    (comp_ext fun x y => by
      simp only [LinearMap.comp_apply, comp_D_tmk, shiftObj_D, LinearMap.sub_apply, map_add,
        map_sub, cmap_tmk, LinearMap.id_apply, LinearMap.smul_apply, Module.End.one_apply,
        sub_tmul, ← smul_tmul', map_zsmul]
      abel)
  hom_inv_id := hom_ext (comp_ext fun x y => rfl)
  inv_hom_id := hom_ext (comp_ext fun x y => rfl)

theorem whiskerLeft_add (X : GBim A B) {Y Y' : GBim B C} (η θ : Y ⟶ Y') :
    whiskerLeft X (η + θ) = whiskerLeft X η + whiskerLeft X θ :=
  hom_ext (comp_ext fun x y => by
    simp only [whiskerLeft_val, add_val, cmap_tmk, LinearMap.add_apply, tmul_add, map_add])

theorem whiskerRight_add {X X' : GBim A B} (η θ : X ⟶ X') (Y : GBim B C) :
    whiskerRight (η + θ) Y = whiskerRight η Y + whiskerRight θ Y :=
  hom_ext (comp_ext fun x y => by
    simp only [whiskerRight_val, add_val, cmap_tmk, LinearMap.add_apply, add_tmul, map_add])

theorem whiskerLeft_smul (X : GBim A B) {Y Y' : GBim B C} (c : k) (η : Y ⟶ Y') :
    whiskerLeft X (c • η) = c • whiskerLeft X η :=
  hom_ext (comp_ext fun x y => by
    simp only [whiskerLeft_val, smul_val, cmap_tmk, LinearMap.smul_apply, LinearMap.id_apply,
      tmul_smul, map_smul])

theorem whiskerRight_smul {X X' : GBim A B} (c : k) (η : X ⟶ X') (Y : GBim B C) :
    whiskerRight (c • η) Y = c • whiskerRight η Y :=
  hom_ext (comp_ext fun x y => by
    simp only [whiskerRight_val, smul_val, cmap_tmk, LinearMap.smul_apply, LinearMap.id_apply,
      ← smul_tmul', map_smul])

end GBim

namespace GrAlg

open GBim

variable {A B C D : GrAlg k}

@[simp] theorem bicategory_whiskerLeft (f : A ⟶ B) {g h : B ⟶ C} (η : g ⟶ h) :
    f ◁ η = GBim.whiskerLeft f η := rfl

@[simp] theorem bicategory_whiskerRight {f g : A ⟶ B} (η : f ⟶ g) (h : B ⟶ C) :
    η ▷ h = GBim.whiskerRight η h := rfl

@[simp] theorem bicategory_associator (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    α_ f g h = GBim.associator f g h := rfl

@[simp] theorem bicategory_leftUnitor (f : A ⟶ B) : λ_ f = GBim.leftUnitor f := rfl

@[simp] theorem bicategory_rightUnitor (f : A ⟶ B) : ρ_ f = GBim.rightUnitor f := rfl

instance (A B : GrAlg k) : Preadditive (A ⟶ B) := inferInstanceAs (Preadditive (GBim A B))
instance (A B : GrAlg k) : Linear k (A ⟶ B) := inferInstanceAs (Linear k (GBim A B))
instance (A B : GrAlg k) : HasShift (A ⟶ B) ℤ := inferInstanceAs (HasShift (GBim A B) ℤ)
instance (A B : GrAlg k) : HasZeroObject (A ⟶ B) := inferInstanceAs (HasZeroObject (GBim A B))
instance (A B : GrAlg k) : HasBinaryBiproducts (A ⟶ B) :=
  inferInstanceAs (HasBinaryBiproducts (GBim A B))
instance (A B : GrAlg k) : KrullSchmidtCat.HomFinite k (A ⟶ B) :=
  inferInstanceAs (KrullSchmidtCat.HomFinite k (GBim A B))

instance precompCommShift {A B : GrAlg k} (C : GrAlg k) (f : A ⟶ B) :
    (precomp C f).CommShift ℤ where
  commShiftIso n := NatIso.ofComponents (fun g => whiskerLeftShift f g n)
    (fun _ => hom_ext (comp_ext fun _ _ => rfl))
  commShiftIso_zero := Iso.ext (NatTrans.ext (funext fun _ => hom_ext (comp_ext fun _ _ => rfl)))
  commShiftIso_add _ _ :=
    Iso.ext (NatTrans.ext (funext fun _ => hom_ext (comp_ext fun _ _ => rfl)))

instance postcompCommShift (A : GrAlg k) {B C : GrAlg k} (g : B ⟶ C) :
    (postcomp A g).CommShift ℤ where
  commShiftIso n := NatIso.ofComponents (fun f => whiskerRightShift f g n)
    (fun _ => hom_ext (comp_ext fun _ _ => rfl))
  commShiftIso_zero := Iso.ext (NatTrans.ext (funext fun _ => hom_ext (comp_ext fun _ _ => rfl)))
  commShiftIso_add _ _ :=
    Iso.ext (NatTrans.ext (funext fun _ => hom_ext (comp_ext fun _ _ => rfl)))

/-- **Graded bimodules form a graded bicategory.** -/
instance gradedBicategory : GradedBicategory (GrAlg k) where
  precomp_additive := fun _ _ => { map_add := fun {_ _ η θ} => GBim.whiskerLeft_add _ η θ }
  postcomp_additive := @fun _ _ _ _ => { map_add := fun {_ _ η θ} => GBim.whiskerRight_add η θ _ }
  shift_additive := fun _ _ n => GBim.shift_additive n
  precomp_commShift := fun C f => precompCommShift C f
  postcomp_commShift := @fun A _ _ g => postcompCommShift A g

instance isLinear : GradedBicategory.IsLinear (GrAlg k) k where
  precomp_linear := fun _ _ => { map_smul := fun {_ _} η c => GBim.whiskerLeft_smul _ c η }
  postcomp_linear := @fun _ _ _ _ => { map_smul := fun {_ _} η c => GBim.whiskerRight_smul c η _ }
  shift_linear := fun _ _ n => GBim.shift_linear n

end GrAlg

end Categorification.TwoRep.Grassmannian
