/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ShiftEnvelope
import Categorification.TwoRep.GradedHomBicategory
import StringDiagrams.Biadjunction.ConjPseudofunctor

/-!
# Realizing pseudofunctors into the shift envelope of the graded-Hom bicategory

For a graded bicategory `B` with shift coherence, the graded-Hom bicategory `K^• = GradedHomBicat B`
is graded by homogeneity (`ghbGrading`). Its shift envelope `ShiftEnv (ghbGrading B)` has the
1-morphisms `(f, t)` and the 2-morphisms `(f, t) ⟶ (g, t')` the homogeneous 2-morphisms `f ⟶ g`
of degree `t' - t`, i.e. the 2-morphisms `f ⟶ g⟦t' - t⟧` of `B`.

`B` embeds in it (`toShiftEnv`: `f ↦ (f, 0)`, fully faithful on 2-morphisms, `toShiftEnvPre`), and
every 1-morphism `(f, t)` is isomorphic to the image of `f⟦t⟧` (`shiftEnvIso`, from the shift
isomorphisms `f⟦t⟧ ≅ f` of degree `t`). Hence any pseudofunctor `Q : 𝒳 ⥤ᵖ ShiftEnv (ghbGrading B)`
is realized as a pseudofunctor `realize Q : 𝒳 ⥤ᵖ B` with `realize Q x = Q x` on objects and
`realize Q f = (Q f).hom⟦(Q f).sh⟧` on 1-morphisms (`realize_map`): first replace the 1-morphisms
`Q f` by the isomorphic `(f⟦t⟧, 0)` (`StringDiagrams.PseudofunctorCopy.copy`), then lift along the
embedding (`StringDiagrams.PseudofunctorLift.lift`). On 2-morphisms, `realize Q` is the 2-morphism
of `B` whose image is `Q` conjugated by the shift isomorphisms (`toShiftEnv_map₂_realize_map₂`).
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory Bicategory GradedHomBicat GradedHomCat StringDiagrams

universe w v u w₁ v₁ u₁

variable {k : Type*} [Field k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]
  [GradedBicategory.IsLinear B k]

variable (k B) in
/-- The grading of the graded-Hom bicategory by homogeneity. -/
def ghbGrading : GradedTwoCells k (GradedHomBicat B) where
  deg f g n :=
    { carrier := {φ | IsHomogeneous φ n}
      add_mem' := fun hφ hψ => IsHomogeneous.add hφ hψ
      zero_mem' := isHomogeneous_zero n
      smul_mem' := fun r _ hφ => IsHomogeneous.smul hφ r }
  id_mem f := isHomogeneous_id _
  comp_mem hη hθ := IsHomogeneous.comp hη hθ (add_comm _ _)
  whiskerLeft_mem := by intros; apply isHomogeneous_whiskerLeft; assumption
  whiskerRight_mem h hη := isHomogeneous_whiskerRight hη h
  associator_hom_mem f g h := isHomogeneous_associator_hom f g h
  associator_inv_mem f g h := isHomogeneous_associator_inv f g h
  leftUnitor_hom_mem f := isHomogeneous_leftUnitor_hom f
  leftUnitor_inv_mem f := isHomogeneous_leftUnitor_inv f
  rightUnitor_hom_mem f := isHomogeneous_rightUnitor_hom f
  rightUnitor_inv_mem f := isHomogeneous_rightUnitor_inv f

@[simp] theorem mem_ghbGrading {a b : GradedHomBicat B} {f g : a ⟶ b} {φ : f ⟶ g} {n : ℤ} :
    φ ∈ (ghbGrading k B).deg f g n ↔ IsHomogeneous φ n := by
  unfold ghbGrading; rfl

variable (k B) in
/-- The shift envelope of the graded-Hom bicategory. -/
abbrev ShEnvK := ShiftEnv (ghbGrading k B)

namespace ShiftEnvK

open ShiftEnv

/-- The underlying object of `B` of an object of the shift envelope. -/
def bObj (a : ShEnvK k B) : B := a.as

/-- The underlying 1-morphism of `B` of a 1-morphism of the shift envelope. -/
def bHom {a b : ShEnvK k B} (f : a ⟶ b) : bObj a ⟶ bObj b := f.hom.as

variable (k B) in
/-- **The embedding** `B ⥤ᵖ ShiftEnv (ghbGrading B)`, `f ↦ (f, 0)`. -/
def toShiftEnv : Pseudofunctor B (ShEnvK k B) where
  obj a := ⟨of a⟩
  map f := ⟨GradedHomCat.mk f, 0⟩
  map₂ η := mk₂ (incl₂ η) ((isHomogeneous_incl₂ η).of_eq (sub_self _).symm)
  map₂_id f := hom₂_ext (incl₂_id f)
  map₂_comp η θ := hom₂_ext (incl₂_comp η θ)
  mapId a := Iso.refl _
  mapComp f g := ShiftEnv.isoMk (Iso.refl _) (by simp) (isHomogeneous_id _) (isHomogeneous_id _)
  map₂_whisker_left f g h η := hom₂_ext (by
    show incl₂ (f ◁ η) = 𝟙 _ ≫ of₁ f ◁ incl₂ η ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, whiskerLeft_incl₂])
  map₂_whisker_right η h := hom₂_ext (by
    show incl₂ (η ▷ h) = 𝟙 _ ≫ incl₂ η ▷ of₁ h ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, incl₂_whiskerRight])
  map₂_associator f g h := hom₂_ext (by
    show incl₂ (α_ f g h).hom = 𝟙 _ ≫ 𝟙 _ ▷ of₁ h ≫ (α_ (of₁ f) (of₁ g) (of₁ h)).hom ≫
      of₁ f ◁ 𝟙 _ ≫ 𝟙 _
    rw [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.id_comp, Category.id_comp,
      Category.comp_id, associator_hom_eq])
  map₂_left_unitor f := hom₂_ext (by
    show incl₂ (λ_ f).hom = 𝟙 _ ≫ 𝟙 _ ▷ of₁ f ≫ (λ_ (of₁ f)).hom
    rw [id_whiskerRight, Category.id_comp, Category.id_comp, leftUnitor_hom_eq])
  map₂_right_unitor f := hom₂_ext (by
    show incl₂ (ρ_ f).hom = 𝟙 _ ≫ of₁ f ◁ 𝟙 _ ≫ (ρ_ (of₁ f)).hom
    rw [whiskerLeft_id, Category.id_comp, Category.id_comp, rightUnitor_hom_eq])

/-- The preimage of a 2-morphism `(f, 0) ⟶ (g, 0)` (homogeneous of degree `0`). -/
def toShiftEnvPre {a b : B} {f g : a ⟶ b}
    (x : (toShiftEnv k B).map f ⟶ (toShiftEnv k B).map g) : f ⟶ g :=
  (exists_incl₂_of_isHomogeneous (f := f) (g := g)
    ((ghbGrading k B).mem_of_eq (show val₂ x ∈ (ghbGrading k B).deg (of₁ f) (of₁ g) (0 - 0)
      from x.2) (sub_self _))).choose

theorem toShiftEnv_map₂_pre {a b : B} {f g : a ⟶ b}
    (x : (toShiftEnv k B).map f ⟶ (toShiftEnv k B).map g) :
    (toShiftEnv k B).map₂ (toShiftEnvPre x) = x :=
  hom₂_ext ((exists_incl₂_of_isHomogeneous (f := f) (g := g)
    ((ghbGrading k B).mem_of_eq (show val₂ x ∈ (ghbGrading k B).deg (of₁ f) (of₁ g) (0 - 0)
      from x.2) (sub_self _))).choose_spec.symm)

theorem toShiftEnvPre_map₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    toShiftEnvPre ((toShiftEnv k B).map₂ η) = η :=
  incl₂_injective (congrArg val₂ (toShiftEnv_map₂_pre ((toShiftEnv k B).map₂ η)))

/-- `(f, t) ≅ (f⟦t⟧, 0)` in the shift envelope. -/
def shiftEnvIso {a b : ShEnvK k B} (f : a ⟶ b) :
    (toShiftEnv k B).map ((bHom f)⟦f.sh⟧) ≅ f where
  hom := mk₂ (shiftIso₁ (bHom f) f.sh).hom
    ((shiftIso₁_hom_isHomogeneous _ _).of_eq (by show f.sh = f.sh - 0; rw [sub_zero]))
  inv := mk₂ (shiftIso₁ (bHom f) f.sh).inv
    ((shiftIso₁_inv_isHomogeneous _ _).of_eq (by show -f.sh = 0 - f.sh; rw [zero_sub]))
  hom_inv_id := hom₂_ext (Iso.hom_inv_id _)
  inv_hom_id := hom₂_ext (Iso.inv_hom_id _)

variable {𝒳 : Type u₁} [Bicategory.{w₁, v₁} 𝒳] (Q : Pseudofunctor 𝒳 (ShEnvK k B))

/-- The 1-morphism of `B` realizing `Q f = (g, t)`: `g⟦t⟧`. -/
abbrev realizeMap {x y : 𝒳} (f : x ⟶ y) : bObj (Q.obj x) ⟶ bObj (Q.obj y) :=
  (bHom (Q.map f))⟦(Q.map f).sh⟧

/-- `Q` with its 1-morphisms replaced by the images `(g⟦t⟧, 0)` of the realizing 1-morphisms. -/
abbrev realizeCopy : Pseudofunctor 𝒳 (ShEnvK k B) :=
  PseudofunctorCopy.copy Q (fun f => (toShiftEnv k B).map (realizeMap Q f))
    (fun f => shiftEnvIso (Q.map f))

-- The associator field unifies the copied structure maps definitionally.
set_option maxHeartbeats 2000000 in
/-- **The realization** of a pseudofunctor into the shift envelope of `K^•` as a pseudofunctor into
`B`: `x ↦ Q x`, `f ↦ g⟦t⟧` for `Q f = (g, t)`. -/
def realize : Pseudofunctor 𝒳 B :=
  PseudofunctorLift.lift (toShiftEnv k B) toShiftEnvPre toShiftEnv_map₂_pre toShiftEnvPre_map₂
    (fun x => bObj (Q.obj x)) (fun f => realizeMap Q f) (fun η => (realizeCopy Q).map₂ η)
    (fun x => (realizeCopy Q).mapId x) (fun f g => (realizeCopy Q).mapComp f g)
    (fun f => (realizeCopy Q).map₂_id f) (fun η θ => (realizeCopy Q).map₂_comp η θ)
    (fun f _ _ η => (realizeCopy Q).map₂_whisker_left f η)
    (fun η h => (realizeCopy Q).map₂_whisker_right η h)
    (fun f g h => (realizeCopy Q).map₂_associator f g h)
    (fun f => (realizeCopy Q).map₂_left_unitor f)
    (fun f => (realizeCopy Q).map₂_right_unitor f)

theorem realize_obj (x : 𝒳) : (realize Q).obj x = bObj (Q.obj x) := rfl

theorem realize_map {x y : 𝒳} (f : x ⟶ y) :
    (realize Q).map f = (bHom (Q.map f))⟦(Q.map f).sh⟧ := rfl

/-- On 2-morphisms, `realize Q` is `Q` conjugated by the shift isomorphisms. -/
theorem toShiftEnv_map₂_realize_map₂ {x y : 𝒳} {f g : x ⟶ y} (η : f ⟶ g) :
    (toShiftEnv k B).map₂ ((realize Q).map₂ η) =
      (shiftEnvIso (Q.map f)).hom ≫ Q.map₂ η ≫ (shiftEnvIso (Q.map g)).inv :=
  toShiftEnv_map₂_pre _

theorem toShiftEnv_map₂_injective {a b : B} {f g : a ⟶ b} {η θ : f ⟶ g}
    (h : (toShiftEnv k B).map₂ η = (toShiftEnv k B).map₂ θ) : η = θ := by
  rw [← toShiftEnvPre_map₂ (k := k) η, ← toShiftEnvPre_map₂ (k := k) θ, h]

theorem toShiftEnv_map₂_add {a b : B} {f g : a ⟶ b} (η θ : f ⟶ g) :
    (toShiftEnv k B).map₂ (η + θ) = (toShiftEnv k B).map₂ η + (toShiftEnv k B).map₂ θ :=
  hom₂_ext ((GradedHomCat.incl (a ⟶ b)).map_add)

theorem toShiftEnv_map₂_smul {a b : B} {f g : a ⟶ b} (r : k) (η : f ⟶ g) :
    (toShiftEnv k B).map₂ (r • η) = r • (toShiftEnv k B).map₂ η :=
  hom₂_ext ((GradedHomCat.incl (a ⟶ b)).map_smul r η)

/-- The realization is additive on 2-morphisms if `Q` is. -/
theorem realize_map₂_add [∀ x y : 𝒳, Preadditive (x ⟶ y)]
    (hQ : ∀ {x y : 𝒳} {f g : x ⟶ y} (η θ : f ⟶ g), Q.map₂ (η + θ) = Q.map₂ η + Q.map₂ θ)
    {x y : 𝒳} {f g : x ⟶ y} (η θ : f ⟶ g) :
    (realize Q).map₂ (η + θ) = (realize Q).map₂ η + (realize Q).map₂ θ := by
  apply toShiftEnv_map₂_injective (k := k)
  rw [toShiftEnv_map₂_add, toShiftEnv_map₂_realize_map₂, toShiftEnv_map₂_realize_map₂,
    toShiftEnv_map₂_realize_map₂, hQ]
  erw [Preadditive.add_comp, Preadditive.comp_add]
  rfl

/-- The realization is `k`-linear on 2-morphisms if `Q` is. -/
theorem realize_map₂_smul [∀ x y : 𝒳, Preadditive (x ⟶ y)] [∀ x y : 𝒳, Linear k (x ⟶ y)]
    (hQ : ∀ {x y : 𝒳} {f g : x ⟶ y} (r : k) (η : f ⟶ g), Q.map₂ (r • η) = r • Q.map₂ η)
    {x y : 𝒳} {f g : x ⟶ y} (r : k) (η : f ⟶ g) :
    (realize Q).map₂ (r • η) = r • (realize Q).map₂ η := by
  apply toShiftEnv_map₂_injective (k := k)
  rw [toShiftEnv_map₂_smul, toShiftEnv_map₂_realize_map₂, toShiftEnv_map₂_realize_map₂, hQ]
  erw [Linear.smul_comp, Linear.comp_smul]
  rfl

end ShiftEnvK

end Categorification.TwoRep
