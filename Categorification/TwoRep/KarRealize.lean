/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.MatKarFunctor
import StringDiagrams.Biadjunction.ConjPseudofunctor
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Realizing pseudofunctors into the envelopes of an additive, idempotent complete bicategory

S. Cautis, A. D. Lauda, arXiv:1111.1431v3, §2.1.2: a 2-category `K` whose hom categories are
idempotent complete is isomorphic to its Karoubi completion `K̇`, and an additive 2-functor into
such a `K` extends uniquely to the Karoubi completion of its source.

For a bicategory `B`:

* `KarBicat.toKar B : B ⥤ᵖ KarBicat B` (`f ↦ (f, 1)`) is fully faithful on 2-morphisms, and when the
  hom categories of `B` are idempotent complete every 1-morphism `(f, e)` of `KarBicat B` is
  isomorphic to the image of a splitting of `e`. Hence a pseudofunctor `Q : 𝒳 ⥤ᵖ KarBicat B` is
  realized as a pseudofunctor `KarBicat.realize Q : 𝒳 ⥤ᵖ B` (`StringDiagrams.PseudofunctorCopy`,
  `StringDiagrams.PseudofunctorLift`);
* `MatBicat.toMat B : B ⥤ᵖ MatBicat B` (`f ↦ (f)`) is fully faithful on 2-morphisms, and when the
  hom categories of `B` have finite biproducts every formal direct sum `(f_i)_i` is isomorphic to
  the image of `⨁ f_i`; a pseudofunctor `Q : 𝒳 ⥤ᵖ MatBicat B` is realized as
  `MatBicat.realize Q : 𝒳 ⥤ᵖ B`.

In both cases the realization agrees with `Q` on objects, and on 2-morphisms it is `Q` conjugated
by the chosen isomorphisms (`toKar_map₂_realize_map₂`, `toMat_map₂_realize_map₂`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Categorification

open CategoryTheory Bicategory Limits Idempotents StringDiagrams

universe w v u w₁ v₁ u₁

/-! ## The idempotent completion -/

namespace KarBicat

open StringDiagrams.KarBicat StringDiagrams.Karoubi

variable (B : Type u) [Bicategory.{w, v} B]

/-- `B` in its idempotent completion: `f ↦ (f, 1)`. -/
def toKar : Pseudofunctor B (StringDiagrams.KarBicat B) where
  obj a := ⟨a⟩
  map f := of f
  map₂ η := ⟨η, by simp⟩
  map₂_id f := Karoubi.hom_ext _ _ rfl
  map₂_comp η θ := Karoubi.hom_ext _ _ rfl
  mapId a := Iso.refl _
  mapComp f g := mkIso (Iso.refl _) (by
    show 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ hcomp₂ (𝟙 f) (𝟙 g)
    simp [hcomp₂])
  map₂_whisker_left f g h η := Karoubi.hom_ext _ _ (by
    simp [hcomp₂, StringDiagrams.Karoubi.mkIso])
  map₂_whisker_right η h := Karoubi.hom_ext _ _ (by
    simp [hcomp₂, StringDiagrams.Karoubi.mkIso])
  map₂_associator f g h := Karoubi.hom_ext _ _ (by
    simp [hcomp₂, StringDiagrams.Karoubi.mkIso, StringDiagrams.KarBicat.associator_hom_eq])
  map₂_left_unitor f := Karoubi.hom_ext _ _ (by
    simp [hcomp₂, StringDiagrams.Karoubi.mkIso, StringDiagrams.KarBicat.leftUnitor_hom_eq])
  map₂_right_unitor f := Karoubi.hom_ext _ _ (by
    simp [hcomp₂, StringDiagrams.Karoubi.mkIso, StringDiagrams.KarBicat.rightUnitor_hom_eq])

variable {B}

/-- The preimage of a 2-morphism `(f, 1) ⟶ (g, 1)`. -/
def toKarPre {a b : B} {f g : a ⟶ b} (x : (toKar B).map f ⟶ (toKar B).map g) : f ⟶ g := x.f

theorem toKar_map₂_pre {a b : B} {f g : a ⟶ b} (x : (toKar B).map f ⟶ (toKar B).map g) :
    (toKar B).map₂ (toKarPre x) = x :=
  Karoubi.hom_ext _ _ rfl

theorem toKarPre_map₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : toKarPre ((toKar B).map₂ η) = η :=
  rfl

variable [∀ a b : B, IsIdempotentComplete (a ⟶ b)]
  {𝒳 : Type u₁} [Bicategory.{w₁, v₁} 𝒳] (Q : Pseudofunctor 𝒳 (StringDiagrams.KarBicat B))

/-- A 1-morphism of `B` realizing `Q f` (a splitting of its idempotent). -/
def realizeMap {x y : 𝒳} (f : x ⟶ y) : (Q.obj x).obj ⟶ (Q.obj y).obj :=
  (toKaroubi ((Q.obj x).obj ⟶ (Q.obj y).obj)).objPreimage (Q.map f)

/-- `(toKar B).map (realizeMap Q f) ≅ Q f`. -/
def realizeIso {x y : 𝒳} (f : x ⟶ y) : (toKar B).map (realizeMap Q f) ≅ Q.map f :=
  (toKaroubi ((Q.obj x).obj ⟶ (Q.obj y).obj)).objObjPreimageIso (Q.map f)

/-- `Q` with its 1-morphisms replaced by the images of the realizing 1-morphisms. -/
abbrev realizeCopy : Pseudofunctor 𝒳 (StringDiagrams.KarBicat B) :=
  PseudofunctorCopy.copy Q (fun f => (toKar B).map (realizeMap Q f)) (fun f => realizeIso Q f)

/-- **The realization** in `B` (with idempotent complete hom categories) of a pseudofunctor into
the idempotent completion of `B`. -/
def realize : Pseudofunctor 𝒳 B :=
  PseudofunctorLift.lift (toKar B) toKarPre toKar_map₂_pre toKarPre_map₂
    (fun x => (Q.obj x).obj) (fun f => realizeMap Q f) (fun η => (realizeCopy Q).map₂ η)
    (fun x => (realizeCopy Q).mapId x) (fun f g => (realizeCopy Q).mapComp f g)
    (fun f => (realizeCopy Q).map₂_id f) (fun η θ => (realizeCopy Q).map₂_comp η θ)
    (fun f _ _ η => (realizeCopy Q).map₂_whisker_left f η)
    (fun η h => (realizeCopy Q).map₂_whisker_right η h)
    (fun f g h => (realizeCopy Q).map₂_associator f g h)
    (fun f => (realizeCopy Q).map₂_left_unitor f)
    (fun f => (realizeCopy Q).map₂_right_unitor f)

theorem realize_obj (x : 𝒳) : (realize Q).obj x = (Q.obj x).obj := rfl

theorem realize_map {x y : 𝒳} (f : x ⟶ y) : (realize Q).map f = realizeMap Q f := rfl

theorem toKar_map₂_realize_map₂ {x y : 𝒳} {f g : x ⟶ y} (η : f ⟶ g) :
    (toKar B).map₂ ((realize Q).map₂ η) =
      (realizeIso Q f).hom ≫ Q.map₂ η ≫ (realizeIso Q g).inv :=
  toKar_map₂_pre _

theorem toKar_map₂_injective {a b : B} {f g : a ⟶ b} {η θ : f ⟶ g}
    (h : (toKar B).map₂ η = (toKar B).map₂ θ) : η = θ := by
  rw [← toKarPre_map₂ η, ← toKarPre_map₂ θ, h]

theorem realize_map₂_add [∀ a b : B, Preadditive (a ⟶ b)] [∀ x y : 𝒳, Preadditive (x ⟶ y)]
    (hQ : ∀ {x y : 𝒳} {f g : x ⟶ y} (η θ : f ⟶ g), Q.map₂ (η + θ) = Q.map₂ η + Q.map₂ θ)
    {x y : 𝒳} {f g : x ⟶ y} (η θ : f ⟶ g) :
    (realize Q).map₂ (η + θ) = (realize Q).map₂ η + (realize Q).map₂ θ := by
  apply toKar_map₂_injective
  rw [show (toKar B).map₂ ((realize Q).map₂ η + (realize Q).map₂ θ) =
      (toKar B).map₂ ((realize Q).map₂ η) + (toKar B).map₂ ((realize Q).map₂ θ) from
    Karoubi.hom_ext _ _ rfl, toKar_map₂_realize_map₂, toKar_map₂_realize_map₂,
    toKar_map₂_realize_map₂, hQ]
  erw [Preadditive.add_comp, Preadditive.comp_add]
  rfl

theorem realize_map₂_smul {R : Type*} [CommRing R] [∀ a b : B, Preadditive (a ⟶ b)]
    [∀ a b : B, Linear R (a ⟶ b)] [∀ x y : 𝒳, Preadditive (x ⟶ y)]
    [∀ x y : 𝒳, Linear R (x ⟶ y)]
    (hQ : ∀ {x y : 𝒳} {f g : x ⟶ y} (r : R) (η : f ⟶ g), Q.map₂ (r • η) = r • Q.map₂ η)
    {x y : 𝒳} {f g : x ⟶ y} (r : R) (η : f ⟶ g) :
    (realize Q).map₂ (r • η) = r • (realize Q).map₂ η := by
  apply toKar_map₂_injective
  rw [show (toKar B).map₂ (r • (realize Q).map₂ η) = r • (toKar B).map₂ ((realize Q).map₂ η) from
    Karoubi.hom_ext _ _ rfl, toKar_map₂_realize_map₂, toKar_map₂_realize_map₂, hQ]
  erw [Linear.smul_comp, Linear.comp_smul]
  rfl

end KarBicat

/-! ## The additive envelope -/

namespace MatBicat

open StringDiagrams.MatBicat StringDiagrams.Mat_

/-- In an additive envelope, a formal direct sum is isomorphic to the one-by-one matrix of its
biproduct. -/
def matIsoC {D : Type*} [Category D] [Preadditive D] [HasFiniteBiproducts D] (M : Mat_ D) :
    (⟨PUnit, fun _ => ⨁ M.X⟩ : Mat_ D) ≅ M where
  hom := (fun _ i => biproduct.π M.X i : CategoryTheory.Mat_.Hom ⟨PUnit, fun _ => ⨁ M.X⟩ M)
  inv := (fun i _ => biproduct.ι M.X i : CategoryTheory.Mat_.Hom M ⟨PUnit, fun _ => ⨁ M.X⟩)
  hom_inv_id := by
    apply CategoryTheory.Mat_.hom_ext
    intro u v
    obtain rfl : u = v := Subsingleton.elim _ _
    rw [CategoryTheory.Mat_.id_apply_self]
    exact biproduct.total (f := M.X)
  inv_hom_id := by
    classical
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    exact (Fintype.sum_unique (fun _ : PUnit => biproduct.ι M.X i ≫ biproduct.π M.X j)).trans
      ((biproduct.ι_π M.X i j).trans (CategoryTheory.Mat_.id_apply M i j).symm)


variable (B : Type u) [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [PreadditiveBicategory B]

/-- A one-element index type. -/
@[instance_reducible] def uniqueSingleι {a b : B} (f : a ⟶ b) :
    Unique (single f : (⟨a⟩ : StringDiagrams.MatBicat B) ⟶ ⟨b⟩).ι :=
  ⟨⟨PUnit.unit⟩, fun _ => rfl⟩

/-- A one-element index type. -/
@[instance_reducible] def uniqueCompι {a b c : StringDiagrams.MatBicat B} (M : a ⟶ b) (N : b ⟶ c) [Unique M.ι]
    [Unique N.ι] : Unique (M ≫ N).ι :=
  ⟨⟨((default : M.ι), (default : N.ι))⟩, fun _ =>
    Prod.ext (Unique.eq_default (α := M.ι) _) (Unique.eq_default (α := N.ι) _)⟩

/-- A one-element index type. -/
@[instance_reducible] def uniqueIdι (a : StringDiagrams.MatBicat B) : Unique (𝟙 a : a ⟶ a).ι :=
  ⟨⟨PUnit.unit⟩, fun _ => rfl⟩

attribute [local instance] uniqueSingleι uniqueCompι uniqueIdι

omit [PreadditiveBicategory B] in
theorem comp_apply_unique {a b : StringDiagrams.MatBicat B} {M N P : a ⟶ b} [Unique N.ι]
    (φ : M ⟶ N) (ψ : N ⟶ P) (i : M.ι) (k : P.ι) :
    (φ ≫ ψ) i k = φ i default ≫ ψ default k := by
  rw [StringDiagrams.MatBicat.comp_apply, Fintype.sum_unique]

omit [PreadditiveBicategory B] in
theorem id_apply_subsingleton {a b : StringDiagrams.MatBicat B} (M : a ⟶ b) [Subsingleton M.ι]
    (i j : M.ι) : (𝟙 M : M ⟶ M) i j = eqToHom (congrArg M.X (Subsingleton.elim i j)) := by
  obtain rfl : i = j := Subsingleton.elim _ _
  rw [StringDiagrams.MatBicat.id_apply_self, eqToHom_refl]

omit [PreadditiveBicategory B] in
theorem permMat_apply_subsingleton {D : Type*} [Category D] [Preadditive D] {ι κ : Type}
    [Fintype ι] [Fintype κ] [Subsingleton κ] {X : ι → D} {Y : κ → D} (e : ι ≃ κ)
    (φ : ∀ i, X i ⟶ Y (e i)) (i : ι) (j : κ) :
    permMat e φ i j = φ i ≫ eqToHom (congrArg Y (Subsingleton.elim _ _)) := by
  unfold permMat
  exact dite_eq_left (Subsingleton.elim _ _)

variable {B} in
/-- A 2-morphism as a one-by-one matrix. -/
def mat1 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    (single f : (⟨a⟩ : StringDiagrams.MatBicat B) ⟶ ⟨b⟩) ⟶ single g := fun _ _ => η

omit [PreadditiveBicategory B] in
variable {B} in
@[simp] theorem mat1_apply {a b : B} {f g : a ⟶ b} (η : f ⟶ g) (i j) : mat1 η i j = η := rfl

variable {B} in
/-- The composition constraint of `toMat`, forwards. -/
def singleCompHom {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (single (f ≫ g) : (⟨a⟩ : StringDiagrams.MatBicat B) ⟶ ⟨c⟩) ⟶ single f ≫ single g :=
  fun _ _ => 𝟙 _

variable {B} in
/-- The composition constraint of `toMat`, backwards. -/
def singleCompInv {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (single f ≫ single g : (⟨a⟩ : StringDiagrams.MatBicat B) ⟶ ⟨c⟩) ⟶ single (f ≫ g) :=
  fun _ _ => 𝟙 _

variable {B} in
/-- The composition constraint of `toMat`. -/
def singleComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (single (f ≫ g) : (⟨a⟩ : StringDiagrams.MatBicat B) ⟶ ⟨c⟩) ≅ single f ≫ single g where
  hom := singleCompHom f g
  inv := singleCompInv f g
  hom_inv_id := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    obtain rfl : i = j := Subsingleton.elim _ _
    rw [StringDiagrams.MatBicat.comp_apply, Fintype.sum_unique,
      StringDiagrams.MatBicat.id_apply_self]
    exact Category.id_comp _
  inv_hom_id := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    obtain rfl : i = j := Subsingleton.elim _ _
    rw [StringDiagrams.MatBicat.comp_apply, Fintype.sum_unique,
      StringDiagrams.MatBicat.id_apply_self]
    exact Category.id_comp _

/-- `B` in its additive envelope: `f ↦ (f)`. -/
def toMat : Pseudofunctor B (StringDiagrams.MatBicat B) where
  obj a := ⟨a⟩
  map f := single f
  map₂ η := mat1 η
  map₂_id f := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    exact (StringDiagrams.MatBicat.id_apply_self (single f) i).symm
  map₂_comp η θ := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    rw [StringDiagrams.MatBicat.comp_apply, Fintype.sum_unique]
    rfl
  mapId a := Iso.refl _
  mapComp f g := singleComp f g
  map₂_whisker_left f g h η := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    simp [comp_apply_unique, id_apply_subsingleton, singleComp, singleCompHom, singleCompInv,
      StringDiagrams.MatBicat.whiskerLeft_eq, hcomp₂]
  map₂_whisker_right η h := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    simp [comp_apply_unique, id_apply_subsingleton, singleComp, singleCompHom, singleCompInv,
      StringDiagrams.MatBicat.whiskerRight_eq, hcomp₂]
  map₂_associator f g h := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    simp [comp_apply_unique, id_apply_subsingleton, singleComp, singleCompHom, singleCompInv,
      StringDiagrams.MatBicat.whiskerLeft_eq, StringDiagrams.MatBicat.whiskerRight_eq, hcomp₂,
      StringDiagrams.MatBicat.associator_hom_eq, permMat_apply_subsingleton]
  map₂_left_unitor f := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    simp [comp_apply_unique, singleComp, singleCompHom,
      StringDiagrams.MatBicat.leftUnitor_hom_eq, permMat_apply_subsingleton]
  map₂_right_unitor f := by
    apply CategoryTheory.Mat_.hom_ext
    intro i j
    simp [comp_apply_unique, singleComp, singleCompHom,
      StringDiagrams.MatBicat.rightUnitor_hom_eq, permMat_apply_subsingleton]

variable {B}

/-- The preimage of a 2-morphism between one-by-one matrices. -/
def toMatPre {a b : B} {f g : a ⟶ b} (x : (toMat B).map f ⟶ (toMat B).map g) : f ⟶ g :=
  x PUnit.unit PUnit.unit

theorem toMat_map₂_pre {a b : B} {f g : a ⟶ b} (x : (toMat B).map f ⟶ (toMat B).map g) :
    (toMat B).map₂ (toMatPre x) = x := by
  apply CategoryTheory.Mat_.hom_ext
  intro i j
  rfl

theorem toMatPre_map₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : toMatPre ((toMat B).map₂ η) = η :=
  rfl

variable [∀ a b : B, HasFiniteBiproducts (a ⟶ b)]

/-- A formal direct sum is isomorphic to the image of its biproduct. -/
def matIso {a b : B} (M : (⟨a⟩ : StringDiagrams.MatBicat B) ⟶ ⟨b⟩) :
    (toMat B).map (⨁ M.X) ≅ M :=
  matIsoC (D := a ⟶ b) M

variable {𝒳 : Type u₁} [Bicategory.{w₁, v₁} 𝒳] (Q : Pseudofunctor 𝒳 (StringDiagrams.MatBicat B))

/-- `Q` with its 1-morphisms replaced by the images of the biproducts. -/
abbrev realizeCopy : Pseudofunctor 𝒳 (StringDiagrams.MatBicat B) :=
  PseudofunctorCopy.copy Q (fun f => (toMat B).map (⨁ (Q.map f).X)) (fun f => matIso (Q.map f))

/-- **The realization** in `B` (with finite biproducts in its hom categories) of a pseudofunctor
into the additive envelope of `B`: formal direct sums go to biproducts. -/
def realize : Pseudofunctor 𝒳 B :=
  PseudofunctorLift.lift (toMat B) toMatPre toMat_map₂_pre toMatPre_map₂
    (fun x => (Q.obj x).obj) (fun f => ⨁ (Q.map f).X) (fun η => (realizeCopy Q).map₂ η)
    (fun x => (realizeCopy Q).mapId x) (fun f g => (realizeCopy Q).mapComp f g)
    (fun f => (realizeCopy Q).map₂_id f) (fun η θ => (realizeCopy Q).map₂_comp η θ)
    (fun f _ _ η => (realizeCopy Q).map₂_whisker_left f η)
    (fun η h => (realizeCopy Q).map₂_whisker_right η h)
    (fun f g h => (realizeCopy Q).map₂_associator f g h)
    (fun f => (realizeCopy Q).map₂_left_unitor f)
    (fun f => (realizeCopy Q).map₂_right_unitor f)

theorem realize_obj (x : 𝒳) : (realize Q).obj x = (Q.obj x).obj := rfl

theorem realize_map {x y : 𝒳} (f : x ⟶ y) : (realize Q).map f = ⨁ (Q.map f).X := rfl

theorem toMat_map₂_realize_map₂ {x y : 𝒳} {f g : x ⟶ y} (η : f ⟶ g) :
    (toMat B).map₂ ((realize Q).map₂ η) =
      (matIso (Q.map f)).hom ≫ Q.map₂ η ≫ (matIso (Q.map g)).inv := by
  exact toMat_map₂_pre (B := B) ((realizeCopy Q).map₂ η)

theorem toMat_map₂_injective {a b : B} {f g : a ⟶ b} {η θ : f ⟶ g}
    (h : (toMat B).map₂ η = (toMat B).map₂ θ) : η = θ := by
  rw [← toMatPre_map₂ η, ← toMatPre_map₂ θ, h]

theorem realize_map₂_add [∀ x y : 𝒳, Preadditive (x ⟶ y)]
    (hQ : ∀ {x y : 𝒳} {f g : x ⟶ y} (η θ : f ⟶ g), Q.map₂ (η + θ) = Q.map₂ η + Q.map₂ θ)
    {x y : 𝒳} {f g : x ⟶ y} (η θ : f ⟶ g) :
    (realize Q).map₂ (η + θ) = (realize Q).map₂ η + (realize Q).map₂ θ := by
  apply toMat_map₂_injective
  rw [show (toMat B).map₂ ((realize Q).map₂ η + (realize Q).map₂ θ) =
      (toMat B).map₂ ((realize Q).map₂ η) + (toMat B).map₂ ((realize Q).map₂ θ) from
    CategoryTheory.Mat_.hom_ext _ _ fun _ _ => rfl, toMat_map₂_realize_map₂,
    toMat_map₂_realize_map₂, toMat_map₂_realize_map₂, hQ]
  erw [Preadditive.add_comp, Preadditive.comp_add]
  rfl

theorem realize_map₂_smul {R : Type*} [CommRing R] [∀ a b : B, Linear R (a ⟶ b)]
    [∀ x y : 𝒳, Preadditive (x ⟶ y)] [∀ x y : 𝒳, Linear R (x ⟶ y)]
    (hQ : ∀ {x y : 𝒳} {f g : x ⟶ y} (r : R) (η : f ⟶ g), Q.map₂ (r • η) = r • Q.map₂ η)
    {x y : 𝒳} {f g : x ⟶ y} (r : R) (η : f ⟶ g) :
    (realize Q).map₂ (r • η) = r • (realize Q).map₂ η := by
  apply toMat_map₂_injective
  rw [show (toMat B).map₂ (r • (realize Q).map₂ η) = r • (toMat B).map₂ ((realize Q).map₂ η) from
    CategoryTheory.Mat_.hom_ext _ _ fun _ _ => rfl, toMat_map₂_realize_map₂,
    toMat_map₂_realize_map₂, hQ]
  erw [Linear.smul_comp, Linear.comp_smul]
  rfl

end MatBicat

end Categorification
