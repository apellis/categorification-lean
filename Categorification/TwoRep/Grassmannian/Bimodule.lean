/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Basic

/-!
# Graded bimodules over finite-dimensional commutative algebras

The 2-category used for the cohomology-of-Grassmannians model of a strong 2-representation of
`sl₂` (S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Definition 1.2) has as objects finite-dimensional graded commutative
`k`-algebras and as 1-morphisms finite-dimensional graded bimodules. This file sets up the
categories of 1-morphisms.

A grading is encoded by a **degree operator**: a graded algebra `A` (`GrAlg`) carries a
`k`-linear derivation `deg` (on the degree-`d` part it is multiplication by `d`), and a graded
`(A, B)`-bimodule `X` (`GBim A B`) carries a linear operator `deg` satisfying the Leibniz rule for
both actions, together with an integer offset `off`. The effective degree operator is
`X.D = X.deg + off`, and 2-morphisms (`GBim.Hom`) are bimodule maps commuting with `D`. The grading
shift `X⟦n⟧` changes only the offset, `off ↦ off - n`, so a 2-morphism `X ⟶ Y⟦n⟧` raises degrees
by `n`; in particular the shift isomorphisms have identity underlying maps.

## Main definitions

* `GrAlg k`, `GBim A B`, `GBim.D`, `GBim.homSubmodule`;
* the `k`-linear preadditive category of graded bimodules with finite-dimensional Hom spaces,
  a zero object, binary biproducts (`GBim.prod`) and the grading shift (`GBim.shift`).
-/

noncomputable section

namespace Categorification.TwoRep.Grassmannian

open CategoryTheory CategoryTheory.Limits

universe u

variable (k : Type u) [Field k]

/-- A finite-dimensional commutative `k`-algebra with a degree derivation `deg`. -/
structure GrAlg where
  /-- The underlying type. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra k carrier]
  [finite : Module.Finite k carrier]
  /-- The degree derivation. -/
  deg : carrier →ₗ[k] carrier
  deg_mul : ∀ a b, deg (a * b) = deg a * b + a * deg b

attribute [instance] GrAlg.commRing GrAlg.algebra GrAlg.finite

instance : CoeSort (GrAlg k) (Type u) := ⟨GrAlg.carrier⟩

variable {k}

theorem GrAlg.deg_one (A : GrAlg k) : A.deg 1 = 0 := by
  have h := A.deg_mul 1 1
  simp only [mul_one, one_mul] at h
  have h2 : A.deg 1 + A.deg 1 = A.deg 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

variable (A B : GrAlg k)

/-- A finite-dimensional graded `(A, B)`-bimodule: a `k`-vector space with commuting actions of
`A` and `B`, a degree operator `deg` satisfying the Leibniz rule for both actions, and an integer
offset `off` (the effective degree operator is `D = deg + off`). -/
structure GBim where
  /-- The underlying type. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module k carrier]
  [finite : Module.Finite k carrier]
  /-- The action of `A`. -/
  actL : A →ₐ[k] Module.End k carrier
  /-- The action of `B`. -/
  actR : B →ₐ[k] Module.End k carrier
  comm : ∀ a b, actL a * actR b = actR b * actL a
  /-- The degree operator, without the offset. -/
  deg : Module.End k carrier
  deg_actL : ∀ a, deg * actL a = actL a * deg + actL (A.deg a)
  deg_actR : ∀ b, deg * actR b = actR b * deg + actR (B.deg b)
  /-- The offset of the grading. -/
  off : ℤ

attribute [instance] GBim.addCommGroup GBim.module GBim.finite

namespace GBim

variable {A B}

instance : CoeSort (GBim A B) (Type u) := ⟨GBim.carrier⟩

/-- The effective degree operator `deg + off`. -/
def D (X : GBim A B) : Module.End k X := X.deg + X.off • 1

theorem D_actL (X : GBim A B) (a : A) : X.D * X.actL a = X.actL a * X.D + X.actL (A.deg a) := by
  simp only [D, add_mul, mul_add, X.deg_actL, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  abel

theorem D_actR (X : GBim A B) (b : B) : X.D * X.actR b = X.actR b * X.D + X.actR (B.deg b) := by
  simp only [D, add_mul, mul_add, X.deg_actR, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  abel

/-- The 2-morphisms `X ⟶ Y`: bimodule maps commuting with the effective degree operators. -/
def homSubmodule (X Y : GBim A B) : Submodule k (X →ₗ[k] Y) where
  carrier := {f | (∀ a, f ∘ₗ X.actL a = Y.actL a ∘ₗ f) ∧ (∀ b, f ∘ₗ X.actR b = Y.actR b ∘ₗ f) ∧
    f ∘ₗ X.D = Y.D ∘ₗ f}
  zero_mem' := ⟨fun _ => by simp, fun _ => by simp, by simp⟩
  add_mem' := by
    rintro f g ⟨hf₁, hf₂, hf₃⟩ ⟨hg₁, hg₂, hg₃⟩
    refine ⟨fun a => ?_, fun b => ?_, ?_⟩
    · rw [LinearMap.add_comp, LinearMap.comp_add, hf₁, hg₁]
    · rw [LinearMap.add_comp, LinearMap.comp_add, hf₂, hg₂]
    · rw [LinearMap.add_comp, LinearMap.comp_add, hf₃, hg₃]
  smul_mem' := by
    rintro c f ⟨hf₁, hf₂, hf₃⟩
    refine ⟨fun a => ?_, fun b => ?_, ?_⟩
    · rw [LinearMap.smul_comp, LinearMap.comp_smul, hf₁]
    · rw [LinearMap.smul_comp, LinearMap.comp_smul, hf₂]
    · rw [LinearMap.smul_comp, LinearMap.comp_smul, hf₃]

theorem mem_homSubmodule {X Y : GBim A B} {f : X →ₗ[k] Y} :
    f ∈ homSubmodule X Y ↔ (∀ a, f ∘ₗ X.actL a = Y.actL a ∘ₗ f) ∧
      (∀ b, f ∘ₗ X.actR b = Y.actR b ∘ₗ f) ∧ f ∘ₗ X.D = Y.D ∘ₗ f := Iff.rfl

theorem id_mem (X : GBim A B) : LinearMap.id ∈ homSubmodule X X :=
  ⟨fun _ => by simp, fun _ => by simp, by simp⟩

theorem comp_mem {X Y Z : GBim A B} {f : X →ₗ[k] Y} {g : Y →ₗ[k] Z} (hf : f ∈ homSubmodule X Y)
    (hg : g ∈ homSubmodule Y Z) : g ∘ₗ f ∈ homSubmodule X Z := by
  obtain ⟨hf₁, hf₂, hf₃⟩ := hf
  obtain ⟨hg₁, hg₂, hg₃⟩ := hg
  refine ⟨fun a => ?_, fun b => ?_, ?_⟩
  · rw [LinearMap.comp_assoc, hf₁, ← LinearMap.comp_assoc, hg₁, LinearMap.comp_assoc]
  · rw [LinearMap.comp_assoc, hf₂, ← LinearMap.comp_assoc, hg₂, LinearMap.comp_assoc]
  · rw [LinearMap.comp_assoc, hf₃, ← LinearMap.comp_assoc, hg₃, LinearMap.comp_assoc]

instance category : Category (GBim A B) where
  Hom X Y := homSubmodule X Y
  id X := ⟨LinearMap.id, id_mem X⟩
  comp f g := ⟨g.1 ∘ₗ f.1, comp_mem f.2 g.2⟩

@[ext]
theorem hom_ext {X Y : GBim A B} {f g : X ⟶ Y} (h : f.1 = g.1) : f = g := Subtype.ext h

@[simp] theorem id_val (X : GBim A B) : (𝟙 X : X ⟶ X).1 = LinearMap.id := rfl

@[simp] theorem comp_val {X Y Z : GBim A B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = g.1 ∘ₗ f.1 := rfl

theorem comp_apply {X Y Z : GBim A B} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).1 x = g.1 (f.1 x) := rfl

/-- A 2-morphism from a linear map satisfying the conditions. -/
def mkHom {X Y : GBim A B} (f : X →ₗ[k] Y) (h₁ : ∀ a x, f (X.actL a x) = Y.actL a (f x))
    (h₂ : ∀ b x, f (X.actR b x) = Y.actR b (f x)) (h₃ : ∀ x, f (X.D x) = Y.D (f x)) : X ⟶ Y :=
  ⟨f, fun a => LinearMap.ext (h₁ a), fun b => LinearMap.ext (h₂ b), LinearMap.ext h₃⟩

@[simp] theorem mkHom_val {X Y : GBim A B} (f : X →ₗ[k] Y) (h₁ h₂ h₃) :
    (mkHom f h₁ h₂ h₃).1 = f := rfl

theorem hom_actL {X Y : GBim A B} (f : X ⟶ Y) (a : A) (x : X) :
    f.1 (X.actL a x) = Y.actL a (f.1 x) := LinearMap.congr_fun (f.2.1 a) x

theorem hom_actR {X Y : GBim A B} (f : X ⟶ Y) (b : B) (x : X) :
    f.1 (X.actR b x) = Y.actR b (f.1 x) := LinearMap.congr_fun (f.2.2.1 b) x

theorem hom_D {X Y : GBim A B} (f : X ⟶ Y) (x : X) : f.1 (X.D x) = Y.D (f.1 x) :=
  LinearMap.congr_fun f.2.2.2 x

instance preadditive : Preadditive (GBim A B) where
  homGroup X Y := inferInstanceAs (AddCommGroup (homSubmodule X Y))
  add_comp _ _ _ _ _ _ := hom_ext (LinearMap.comp_add _ _ _)
  comp_add _ _ _ _ _ _ := hom_ext (LinearMap.add_comp _ _ _)

@[simp] theorem add_val {X Y : GBim A B} (f g : X ⟶ Y) : (f + g).1 = f.1 + g.1 := rfl

@[simp] theorem zero_val (X Y : GBim A B) : (0 : X ⟶ Y).1 = 0 := rfl

@[simp] theorem neg_val {X Y : GBim A B} (f : X ⟶ Y) : (-f).1 = -f.1 := rfl

@[simp] theorem sub_val {X Y : GBim A B} (f g : X ⟶ Y) : (f - g).1 = f.1 - g.1 := rfl

instance linear : Linear k (GBim A B) where
  homModule X Y := inferInstanceAs (Module k (homSubmodule X Y))
  smul_comp _ _ _ _ _ _ := hom_ext (LinearMap.comp_smul _ _ _)
  comp_smul _ _ _ _ _ _ := hom_ext (LinearMap.smul_comp _ _ _)

@[simp] theorem smul_val {X Y : GBim A B} (c : k) (f : X ⟶ Y) : (c • f).1 = c • f.1 := rfl

instance homFinite : KrullSchmidtCat.HomFinite k (GBim A B) where
  finiteDimensional X Y := inferInstanceAs (Module.Finite k (homSubmodule X Y))

/-! ### The zero object -/

/-- The algebra map to the endomorphisms of a zero space. -/
def toTrivialAlgHom (R : Type u) [CommRing R] [Algebra k R] (M : Type u) [AddCommGroup M]
    [Module k M] [Subsingleton M] : R →ₐ[k] Module.End k M where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := rfl
  map_add' _ _ := Subsingleton.elim _ _
  commutes' _ := Subsingleton.elim _ _

/-- The zero bimodule. -/
def zero (A B : GrAlg k) : GBim A B where
  carrier := PUnit
  actL := toTrivialAlgHom A PUnit
  actR := toTrivialAlgHom B PUnit
  comm _ _ := Subsingleton.elim _ _
  deg := 0
  deg_actL _ := Subsingleton.elim _ _
  deg_actR _ := Subsingleton.elim _ _
  off := 0

theorem isZero_of_subsingleton (X : GBim A B) [Subsingleton X] : IsZero X := by
  refine ⟨fun Y => ⟨⟨0⟩, fun f => hom_ext (LinearMap.ext fun x => ?_)⟩,
    fun Y => ⟨⟨0⟩, fun f => hom_ext (LinearMap.ext fun x => Subsingleton.elim _ _)⟩⟩
  rw [Subsingleton.elim x 0, map_zero, map_zero]

theorem isZero_zero (A B : GrAlg k) : IsZero (zero A B) := by
  have : Subsingleton (zero A B).carrier := inferInstanceAs (Subsingleton PUnit)
  exact isZero_of_subsingleton _

instance hasZeroObject : HasZeroObject (GBim A B) := (isZero_zero A B).hasZeroObject

/-- A bimodule whose underlying space is zero-dimensional is a zero object. -/
theorem isZero_of_finrank_eq_zero (X : GBim A B) (h : Module.finrank k X = 0) : IsZero X := by
  have : Subsingleton X := Module.finrank_zero_iff.mp h
  exact isZero_of_subsingleton X

/-! ### Binary biproducts -/

/-- The direct sum `X ⊕ Y` (with offset `0`; the degree operator is the sum of the effective
degree operators). -/
abbrev prod (X Y : GBim A B) : GBim A B where
  carrier := X.carrier × Y.carrier
  actL := (LinearMap.prodMapAlgHom k X.carrier Y.carrier).comp (X.actL.prod Y.actL)
  actR := (LinearMap.prodMapAlgHom k X.carrier Y.carrier).comp (X.actR.prod Y.actR)
  comm a b := by
    show (X.actL a).prodMap (Y.actL a) * (X.actR b).prodMap (Y.actR b) =
      (X.actR b).prodMap (Y.actR b) * (X.actL a).prodMap (Y.actL a)
    rw [LinearMap.prodMap_mul, LinearMap.prodMap_mul, X.comm, Y.comm]
  deg := X.D.prodMap Y.D
  deg_actL a := by
    show X.D.prodMap Y.D * (X.actL a).prodMap (Y.actL a) =
      (X.actL a).prodMap (Y.actL a) * X.D.prodMap Y.D +
        (X.actL (A.deg a)).prodMap (Y.actL (A.deg a))
    rw [LinearMap.prodMap_mul, LinearMap.prodMap_mul, ← LinearMap.prodMap_add, X.D_actL,
      Y.D_actL]
  deg_actR b := by
    show X.D.prodMap Y.D * (X.actR b).prodMap (Y.actR b) =
      (X.actR b).prodMap (Y.actR b) * X.D.prodMap Y.D +
        (X.actR (B.deg b)).prodMap (Y.actR (B.deg b))
    rw [LinearMap.prodMap_mul, LinearMap.prodMap_mul, ← LinearMap.prodMap_add, X.D_actR,
      Y.D_actR]
  off := 0

theorem prod_D (X Y : GBim A B) : (prod X Y).D = X.D.prodMap Y.D := by
  show X.D.prodMap Y.D + (0 : ℤ) • 1 = _
  rw [zero_smul, add_zero]

/-- The biproduct bicone on `prod X Y`. -/
def prodBicone (X Y : GBim A B) : BinaryBicone X Y where
  pt := prod X Y
  fst := mkHom (LinearMap.fst k X Y) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun x => by rw [prod_D]; rfl)
  snd := mkHom (LinearMap.snd k X Y) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun x => by rw [prod_D]; rfl)
  inl := mkHom (LinearMap.inl k X Y) (fun a _ => Prod.ext rfl (map_zero (Y.actL a)).symm)
    (fun b _ => Prod.ext rfl (map_zero (Y.actR b)).symm) (fun x => by
      show (X.D x, (0 : Y.carrier)) = (X.prod Y).D (x, 0)
      rw [prod_D]; exact Prod.ext rfl (map_zero Y.D).symm)
  inr := mkHom (LinearMap.inr k X Y) (fun a _ => Prod.ext (map_zero (X.actL a)).symm rfl)
    (fun b _ => Prod.ext (map_zero (X.actR b)).symm rfl) (fun y => by
      show ((0 : X.carrier), Y.D y) = (X.prod Y).D (0, y)
      rw [prod_D]; exact Prod.ext (map_zero X.D).symm rfl)
  inl_fst := hom_ext (LinearMap.fst_comp_inl k X Y)
  inl_snd := hom_ext (LinearMap.snd_comp_inl k X Y)
  inr_fst := hom_ext (LinearMap.fst_comp_inr k X Y)
  inr_snd := hom_ext (LinearMap.snd_comp_inr k X Y)

instance hasBinaryBiproducts : HasBinaryBiproducts (GBim A B) where
  has_binary_biproduct X Y := hasBinaryBiproduct_of_total (prodBicone X Y)
    (hom_ext (LinearMap.ext fun ⟨x, y⟩ => Prod.ext (add_zero x) (zero_add y)))

/-! ### The grading shift -/

/-- The shift `X⟦n⟧`: the offset becomes `off - n`. -/
abbrev shiftObj (X : GBim A B) (n : ℤ) : GBim A B := { X with off := X.off - n }

@[simp] theorem shiftObj_carrier (X : GBim A B) (n : ℤ) : (X.shiftObj n).carrier = X.carrier :=
  rfl

theorem shiftObj_D (X : GBim A B) (n : ℤ) : (X.shiftObj n).D = X.D - n • 1 := by
  simp only [D, shiftObj, sub_smul]
  abel

/-- The identity linear map as a 2-morphism between bimodules differing only in their offsets. -/
def ofOff (X : GBim A B) {m n : ℤ} (h : m = n) : { X with off := m } ⟶ { X with off := n } :=
  mkHom LinearMap.id (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => by subst h; rfl)

@[simp] theorem ofOff_val (X : GBim A B) {m n : ℤ} (h : m = n) : (X.ofOff h).1 = LinearMap.id :=
  rfl

/-- The isomorphism given by the identity between bimodules differing only in their offsets. -/
def isoOff (X : GBim A B) {m n : ℤ} (h : m = n) : { X with off := m } ≅ { X with off := n } where
  hom := X.ofOff h
  inv := X.ofOff h.symm

theorem eqToHom_val_of_off (X : GBim A B) {m n : ℤ}
    (h : ({ X with off := m } : GBim A B) = { X with off := n }) :
    (eqToHom h).1 = LinearMap.id := by
  have : m = n := congrArg GBim.off h
  subst this
  rfl

/-- The shift functor. -/
def shiftFunctor (n : ℤ) : GBim A B ⥤ GBim A B where
  obj X := X.shiftObj n
  map f := mkHom f.1 (hom_actL f) (hom_actR f) (fun x => by
    simp only [shiftObj_D, LinearMap.sub_apply, map_sub, hom_D, Module.End.one_apply,
      LinearMap.smul_apply, map_zsmul])

@[simp] theorem shiftFunctor_map_val (n : ℤ) {X Y : GBim A B} (f : X ⟶ Y) :
    ((shiftFunctor n).map f).1 = f.1 := rfl

/-- The data of the grading shift. -/
def shiftMkCore : ShiftMkCore (GBim A B) ℤ where
  F := shiftFunctor
  zero := NatIso.ofComponents (fun X => X.isoOff (sub_zero X.off)) (fun _ => rfl)
  add m n := NatIso.ofComponents (fun X => X.isoOff (by omega : X.off - (m + n) = X.off - m - n))
    (fun _ => rfl)
  assoc_hom_app m₁ m₂ m₃ X := by
    ext x
    simp only [comp_val, LinearMap.comp_apply]
    erw [eqToHom_val_of_off]
    rfl
  zero_add_hom_app n X := by
    ext x
    simp only [comp_val, LinearMap.comp_apply]
    erw [eqToHom_val_of_off]
    rfl
  add_zero_hom_app n X := by
    ext x
    simp only [comp_val, LinearMap.comp_apply]
    erw [eqToHom_val_of_off]
    rfl

instance hasShift : HasShift (GBim A B) ℤ := hasShiftMk _ _ shiftMkCore

theorem shift_obj (X : GBim A B) (n : ℤ) : X⟦n⟧ = X.shiftObj n := rfl

@[simp] theorem shift_map_val (n : ℤ) {X Y : GBim A B} (f : X ⟶ Y) : (f⟦n⟧').1 = f.1 := rfl

theorem shiftFunctorAdd_hom_val (X : GBim A B) (m n : ℤ) :
    ((CategoryTheory.shiftFunctorAdd (GBim A B) m n).hom.app X).1 = LinearMap.id := rfl

theorem shiftFunctorAdd_inv_val (X : GBim A B) (m n : ℤ) :
    ((CategoryTheory.shiftFunctorAdd (GBim A B) m n).inv.app X).1 = LinearMap.id := rfl

theorem shiftFunctorZero_hom_val (X : GBim A B) :
    ((CategoryTheory.shiftFunctorZero (GBim A B) ℤ).hom.app X).1 = LinearMap.id := rfl

theorem shiftFunctorZero_inv_val (X : GBim A B) :
    ((CategoryTheory.shiftFunctorZero (GBim A B) ℤ).inv.app X).1 = LinearMap.id := rfl

instance shift_additive (n : ℤ) : (CategoryTheory.shiftFunctor (GBim A B) n).Additive where
  map_add := rfl

instance shift_linear (n : ℤ) : (CategoryTheory.shiftFunctor (GBim A B) n).Linear k where
  map_smul _ _ := rfl

end GBim

end Categorification.TwoRep.Grassmannian
