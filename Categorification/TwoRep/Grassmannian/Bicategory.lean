/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.Grassmannian.Bimodule

/-!
# The bicategory of graded bimodules

Objects are graded algebras `GrAlg k`, 1-morphisms `A ⟶ B` are graded bimodules `GBim A B`, and
composition (in diagrammatic order) is the relative tensor product: `X ≫ Y = X ⊗_B Y`, the
quotient of `X ⊗[k] Y` by the balancing relations `x b ⊗ y = x ⊗ b y`, with degree operator
`D ⊗ 1 + 1 ⊗ D`. The identity 1-morphism is the regular bimodule.

This is the 2-category in which the cohomology rings of Grassmannians carry the strong
2-representations of `sl₂` of S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of
quantum groups*, arXiv:1111.1431v3 (Definition 1.2); see `Grassmannian/StrongSl2.lean`.

## Main definitions

* `GBim.comp`, `GBim.tmk` (the class of `x ⊗ y` in `X ⊗_B Y`), `GBim.id`;
* `GrAlg.bicategory`: the bicategory structure;
* `GrAlg.gradedBicategory`, `GrAlg.isLinear`: whiskering is additive, `k`-linear and commutes
  with the grading shift.
-/

noncomputable section

namespace Categorification.TwoRep.Grassmannian

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

variable {k : Type u} [Field k]

namespace GBim

variable {A B C D E : GrAlg k}

/-! ### The relative tensor product -/

section Tens

variable (X : GBim A B) (Y : GBim B C)

/-- The balancing relations `x b ⊗ y - x ⊗ b y`. -/
def rel : Submodule k (X ⊗[k] Y) :=
  Submodule.span k {t | ∃ (b : B) (x : X) (y : Y), t = X.actR b x ⊗ₜ y - x ⊗ₜ Y.actL b y}

/-- The relative tensor product `X ⊗_B Y` as a vector space. -/
abbrev Tens : Type u := (X ⊗[k] Y) ⧸ rel X Y

variable {X Y}

theorem rel_le_ker {M : Type*} [AddCommGroup M] [Module k M] (f : X ⊗[k] Y →ₗ[k] M)
    (hf : ∀ b x y, f (X.actR b x ⊗ₜ y) = f (x ⊗ₜ Y.actL b y)) : rel X Y ≤ LinearMap.ker f := by
  rw [rel, Submodule.span_le]
  rintro _ ⟨b, x, y, rfl⟩
  simp [hf]

/-- Descent of a balanced map to the relative tensor product. -/
def tdesc {M : Type*} [AddCommGroup M] [Module k M] (f : X ⊗[k] Y →ₗ[k] M)
    (hf : ∀ b x y, f (X.actR b x ⊗ₜ y) = f (x ⊗ₜ Y.actL b y)) : Tens X Y →ₗ[k] M :=
  (rel X Y).liftQ f (rel_le_ker f hf)

theorem tdesc_mk {M : Type*} [AddCommGroup M] [Module k M] (f : X ⊗[k] Y →ₗ[k] M) (hf)
    (t : X ⊗[k] Y) : tdesc f hf (Submodule.Quotient.mk t) = f t := rfl

theorem mk_actR_tmul (b : B) (x : X) (y : Y) :
    (Submodule.Quotient.mk (X.actR b x ⊗ₜ y) : Tens X Y) = Submodule.Quotient.mk (x ⊗ₜ Y.actL b y) :=
  (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨b, x, y, rfl⟩)

theorem tens_ext {M : Type*} [AddCommGroup M] [Module k M] {f g : Tens X Y →ₗ[k] M}
    (h : ∀ x y, f (Submodule.Quotient.mk (x ⊗ₜ y)) = g (Submodule.Quotient.mk (x ⊗ₜ y))) :
    f = g :=
  Submodule.linearMap_qext _ (TensorProduct.ext' h)

variable {X' : GBim A B} {Y' : GBim B C}

/-- The map `f ⊗ g` on relative tensor products, for `f` right `B`-linear and `g` left
`B`-linear. -/
def tmap (f : X →ₗ[k] X') (g : Y →ₗ[k] Y') (hf : ∀ b x, f (X.actR b x) = X'.actR b (f x))
    (hg : ∀ b y, g (Y.actL b y) = Y'.actL b (g y)) : Tens X Y →ₗ[k] Tens X' Y' :=
  tdesc ((rel X' Y').mkQ ∘ₗ TensorProduct.map f g) (fun b x y => by
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, hf, hg, Submodule.mkQ_apply]
    exact mk_actR_tmul _ _ _)

theorem tmap_mk (f : X →ₗ[k] X') (g : Y →ₗ[k] Y') (hf hg) (x : X) (y : Y) :
    tmap f g hf hg (Submodule.Quotient.mk (x ⊗ₜ y)) = Submodule.Quotient.mk (f x ⊗ₜ g y) := rfl

end Tens

/-- The left action of `A` on `X ⊗_B Y`. -/
def tensActL (X : GBim A B) (Y : GBim B C) : A →ₐ[k] Module.End k (Tens X Y) where
  toFun a := tmap (X.actL a) LinearMap.id
    (fun b x => LinearMap.congr_fun (X.comm a b) x) (fun _ _ => rfl)
  map_one' := tens_ext fun x y => by simp [tmap_mk]
  map_mul' a a' := tens_ext fun x y => by simp [tmap_mk]
  map_zero' := tens_ext fun x y => by simp [tmap_mk]
  map_add' a a' := tens_ext fun x y => by simp [tmap_mk, add_tmul]
  commutes' c := tens_ext fun x y => by
    show (rel X Y).mkQ (X.actL (algebraMap k A c) x ⊗ₜ y) =
      (algebraMap k (Module.End k (Tens X Y)) c) ((rel X Y).mkQ (x ⊗ₜ y))
    rw [X.actL.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← map_smul,
      TensorProduct.smul_tmul']

/-- The right action of `C` on `X ⊗_B Y`. -/
def tensActR (X : GBim A B) (Y : GBim B C) : C →ₐ[k] Module.End k (Tens X Y) where
  toFun c := tmap LinearMap.id (Y.actR c) (fun _ _ => rfl)
    (fun b y => (LinearMap.congr_fun (Y.comm b c) y).symm)
  map_one' := tens_ext fun x y => by simp [tmap_mk]
  map_mul' a a' := tens_ext fun x y => by simp [tmap_mk]
  map_zero' := tens_ext fun x y => by simp [tmap_mk]
  map_add' a a' := tens_ext fun x y => by simp [tmap_mk, tmul_add]
  commutes' c := tens_ext fun x y => by
    simp [tmap_mk, Module.algebraMap_end_apply, TensorProduct.tmul_smul]

theorem D_actR_apply (X : GBim A B) (b : B) (x : X) :
    X.D (X.actR b x) = X.actR b (X.D x) + X.actR (B.deg b) x :=
  LinearMap.congr_fun (X.D_actR b) x

theorem D_actL_apply (X : GBim A B) (a : A) (x : X) :
    X.D (X.actL a x) = X.actL a (X.D x) + X.actL (A.deg a) x :=
  LinearMap.congr_fun (X.D_actL a) x

/-- The degree operator `D ⊗ 1 + 1 ⊗ D` on `X ⊗_B Y`. -/
def tensDeg (X : GBim A B) (Y : GBim B C) : Module.End k (Tens X Y) :=
  tdesc ((rel X Y).mkQ ∘ₗ (TensorProduct.map X.D LinearMap.id + TensorProduct.map LinearMap.id Y.D))
    (fun b x y => by
      simp only [LinearMap.comp_apply, LinearMap.add_apply, TensorProduct.map_tmul,
        LinearMap.id_apply, Submodule.mkQ_apply, D_actR_apply, D_actL_apply, add_tmul, tmul_add,
        Submodule.Quotient.mk_add, mk_actR_tmul]
      abel)

theorem tensDeg_mk (X : GBim A B) (Y : GBim B C) (x : X) (y : Y) :
    tensDeg X Y (Submodule.Quotient.mk (x ⊗ₜ y)) =
      Submodule.Quotient.mk (X.D x ⊗ₜ y) + Submodule.Quotient.mk (x ⊗ₜ Y.D y) := rfl

/-- **Composition of 1-morphisms**: the relative tensor product `X ⊗_B Y`. -/
def comp (X : GBim A B) (Y : GBim B C) : GBim A C where
  carrier := Tens X Y
  actL := tensActL X Y
  actR := tensActR X Y
  comm a c := tens_ext fun x y => by simp [tensActL, tensActR, tmap_mk]
  deg := tensDeg X Y
  deg_actL a := tens_ext fun x y => by
    simp only [Module.End.mul_apply, LinearMap.add_apply, tensActL, AlgHom.coe_mk,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, tmap_mk, tensDeg_mk, map_add,
      LinearMap.id_apply, D_actL_apply, add_tmul, Submodule.Quotient.mk_add]
    abel
  deg_actR c := tens_ext fun x y => by
    simp only [Module.End.mul_apply, LinearMap.add_apply, tensActR, AlgHom.coe_mk,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, tmap_mk, tensDeg_mk, map_add,
      LinearMap.id_apply, D_actR_apply, tmul_add, Submodule.Quotient.mk_add]
    abel
  off := 0

section comp

variable {X X' X'' : GBim A B} {Y Y' Y'' : GBim B C}

variable (X Y) in
/-- The class of `x ⊗ y` in `X ⊗_B Y`. -/
def tmk : X ⊗[k] Y →ₗ[k] (comp X Y).carrier := (rel X Y).mkQ

theorem tmk_actR (b : B) (x : X) (y : Y) :
    tmk X Y (X.actR b x ⊗ₜ y) = tmk X Y (x ⊗ₜ Y.actL b y) :=
  mk_actR_tmul b x y

@[simp] theorem comp_actL_tmk (a : A) (x : X) (y : Y) :
    (comp X Y).actL a (tmk X Y (x ⊗ₜ y)) = tmk X Y (X.actL a x ⊗ₜ y) := rfl

@[simp] theorem comp_actR_tmk (c : C) (x : X) (y : Y) :
    (comp X Y).actR c (tmk X Y (x ⊗ₜ y)) = tmk X Y (x ⊗ₜ Y.actR c y) := rfl

variable (X Y) in
theorem comp_D : (comp X Y).D = tensDeg X Y := by
  show tensDeg X Y + (0 : ℤ) • 1 = tensDeg X Y
  rw [zero_smul, add_zero]

@[simp] theorem comp_D_tmk (x : X) (y : Y) :
    (comp X Y).D (tmk X Y (x ⊗ₜ y)) = tmk X Y (X.D x ⊗ₜ y) + tmk X Y (x ⊗ₜ Y.D y) := by
  rw [comp_D]
  rfl

theorem comp_ext {M : Type*} [AddCommGroup M] [Module k M] {f g : (comp X Y).carrier →ₗ[k] M}
    (h : ∀ x y, f (tmk X Y (x ⊗ₜ y)) = g (tmk X Y (x ⊗ₜ y))) : f = g :=
  tens_ext h

theorem comp_induction {P : (comp X Y).carrier → Prop} (p : (comp X Y).carrier)
    (hadd : ∀ p q, P p → P q → P (p + q)) (ht : ∀ x y, P (tmk X Y (x ⊗ₜ y))) : P p := by
  obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective (rel X Y) p
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact ht x y
  | add s t hs ht => rw [map_add]; exact hadd _ _ hs ht

/-- Descent of a balanced map to `X ⊗_B Y`. -/
def cdesc {M : Type*} [AddCommGroup M] [Module k M] (f : X ⊗[k] Y →ₗ[k] M)
    (hf : ∀ b x y, f (X.actR b x ⊗ₜ y) = f (x ⊗ₜ Y.actL b y)) : (comp X Y).carrier →ₗ[k] M :=
  tdesc f hf

@[simp] theorem cdesc_tmk {M : Type*} [AddCommGroup M] [Module k M] (f : X ⊗[k] Y →ₗ[k] M) (hf)
    (t : X ⊗[k] Y) : cdesc f hf (tmk X Y t) = f t := rfl

/-- `f ⊗ g` on relative tensor products. -/
def cmap (f : X →ₗ[k] X') (g : Y →ₗ[k] Y') (hf : ∀ b x, f (X.actR b x) = X'.actR b (f x))
    (hg : ∀ b y, g (Y.actL b y) = Y'.actL b (g y)) :
    (comp X Y).carrier →ₗ[k] (comp X' Y').carrier :=
  tmap f g hf hg

@[simp] theorem cmap_tmk (f : X →ₗ[k] X') (g : Y →ₗ[k] Y') (hf hg) (x : X) (y : Y) :
    cmap f g hf hg (tmk X Y (x ⊗ₜ y)) = tmk X' Y' (f x ⊗ₜ g y) := rfl

end comp

/-! ### Whiskering -/

/-- A 2-morphism from a linear map, with the conditions stated for linear maps. -/
def mkHomₗ {X Y : GBim A B} (f : X →ₗ[k] Y) (h₁ : ∀ a, f ∘ₗ X.actL a = Y.actL a ∘ₗ f)
    (h₂ : ∀ b, f ∘ₗ X.actR b = Y.actR b ∘ₗ f) (h₃ : f ∘ₗ X.D = Y.D ∘ₗ f) : X ⟶ Y :=
  ⟨f, h₁, h₂, h₃⟩

@[simp] theorem mkHomₗ_val {X Y : GBim A B} (f : X →ₗ[k] Y) (h₁ h₂ h₃) :
    (mkHomₗ f h₁ h₂ h₃).1 = f := rfl

/-- Left whiskering `X ◁ η`. -/
def whiskerLeft (X : GBim A B) {Y Y' : GBim B C} (η : Y ⟶ Y') : comp X Y ⟶ comp X Y' :=
  mkHomₗ (cmap LinearMap.id η.1 (fun _ _ => rfl) (hom_actL η))
    (fun a => comp_ext fun x y => by simp)
    (fun c => comp_ext fun x y => by simp [hom_actR])
    (comp_ext fun x y => by simp [hom_D])

@[simp] theorem whiskerLeft_val (X : GBim A B) {Y Y' : GBim B C} (η : Y ⟶ Y') :
    (whiskerLeft X η).1 = cmap LinearMap.id η.1 (fun _ _ => rfl) (hom_actL η) := rfl

/-- Right whiskering `η ▷ Y`. -/
def whiskerRight {X X' : GBim A B} (η : X ⟶ X') (Y : GBim B C) : comp X Y ⟶ comp X' Y :=
  mkHomₗ (cmap η.1 LinearMap.id (hom_actR η) (fun _ _ => rfl))
    (fun a => comp_ext fun x y => by simp [hom_actL])
    (fun c => comp_ext fun x y => by simp)
    (comp_ext fun x y => by simp [hom_D])

@[simp] theorem whiskerRight_val {X X' : GBim A B} (η : X ⟶ X') (Y : GBim B C) :
    (whiskerRight η Y).1 = cmap η.1 LinearMap.id (hom_actR η) (fun _ _ => rfl) := rfl

/-! ### The associator -/

section Assoc

variable (X : GBim A B) (Y : GBim B C) (Z : GBim C D)

/-- `x ↦ y ↦ z ↦ x ⊗ (y ⊗ z)`. -/
def assocAux : X →ₗ[k] Y →ₗ[k] Z →ₗ[k] (comp X (comp Y Z)).carrier :=
  ((LinearMap.llcomp k Z (comp Y Z).carrier _).comp
    ((TensorProduct.mk k X (comp Y Z).carrier).compr₂ (tmk X (comp Y Z)))).compl₂
    ((TensorProduct.mk k Y Z).compr₂ (tmk Y Z))

theorem assocAux_apply (x : X) (y : Y) (z : Z) :
    assocAux X Y Z x y z = tmk X (comp Y Z) (x ⊗ₜ tmk Y Z (y ⊗ₜ z)) := rfl

/-- `(x ⊗ y) ↦ z ↦ x ⊗ (y ⊗ z)`. -/
def assocMid : (comp X Y).carrier →ₗ[k] Z →ₗ[k] (comp X (comp Y Z)).carrier :=
  cdesc (TensorProduct.lift (assocAux X Y Z)) (fun b x y => LinearMap.ext fun z => by
    simp only [TensorProduct.lift.tmul, assocAux_apply]
    rw [tmk_actR]
    rfl)

theorem assocMid_tmk (x : X) (y : Y) (z : Z) :
    assocMid X Y Z (tmk X Y (x ⊗ₜ y)) z = tmk X (comp Y Z) (x ⊗ₜ tmk Y Z (y ⊗ₜ z)) := by
  simp [assocMid, assocAux_apply]

/-- The associator `(X ⊗ Y) ⊗ Z → X ⊗ (Y ⊗ Z)` as a linear map. -/
def assocHomₗ : (comp (comp X Y) Z).carrier →ₗ[k] (comp X (comp Y Z)).carrier :=
  cdesc (TensorProduct.lift (assocMid X Y Z)) (fun c p z => by
    simp only [TensorProduct.lift.tmul]
    induction p using comp_induction with
    | hadd p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
    | ht x y =>
      rw [comp_actR_tmk, assocMid_tmk, assocMid_tmk, tmk_actR])

@[simp] theorem assocHomₗ_tmk (x : X) (y : Y) (z : Z) :
    assocHomₗ X Y Z (tmk (comp X Y) Z (tmk X Y (x ⊗ₜ y) ⊗ₜ z)) =
      tmk X (comp Y Z) (x ⊗ₜ tmk Y Z (y ⊗ₜ z)) := by
  simp [assocHomₗ, assocMid_tmk]

/-- `y ↦ z ↦ x ↦ (x ⊗ y) ⊗ z`. -/
def assocInvAux : Y →ₗ[k] Z →ₗ[k] X →ₗ[k] (comp (comp X Y) Z).carrier :=
  (((LinearMap.llcomp k X (comp X Y).carrier _).comp
    ((TensorProduct.mk k (comp X Y).carrier Z).compr₂ (tmk (comp X Y) Z)).flip).compl₂
    ((TensorProduct.mk k X Y).compr₂ (tmk X Y)).flip).flip

theorem assocInvAux_apply (x : X) (y : Y) (z : Z) :
    assocInvAux X Y Z y z x = tmk (comp X Y) Z (tmk X Y (x ⊗ₜ y) ⊗ₜ z) := rfl

/-- `(y ⊗ z) ↦ x ↦ (x ⊗ y) ⊗ z`. -/
def assocInvMid : (comp Y Z).carrier →ₗ[k] X →ₗ[k] (comp (comp X Y) Z).carrier :=
  cdesc (TensorProduct.lift (assocInvAux X Y Z)) (fun c y z => LinearMap.ext fun x => by
    simp only [TensorProduct.lift.tmul, assocInvAux_apply]
    rw [← comp_actR_tmk, tmk_actR])

theorem assocInvMid_tmk (x : X) (y : Y) (z : Z) :
    assocInvMid X Y Z (tmk Y Z (y ⊗ₜ z)) x = tmk (comp X Y) Z (tmk X Y (x ⊗ₜ y) ⊗ₜ z) := by
  simp [assocInvMid, assocInvAux_apply]

/-- The inverse associator `X ⊗ (Y ⊗ Z) → (X ⊗ Y) ⊗ Z` as a linear map. -/
def assocInvₗ : (comp X (comp Y Z)).carrier →ₗ[k] (comp (comp X Y) Z).carrier :=
  cdesc (TensorProduct.lift (assocInvMid X Y Z).flip) (fun b x w => by
    simp only [TensorProduct.lift.tmul, LinearMap.flip_apply]
    induction w using comp_induction with
    | hadd p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
    | ht y z =>
      rw [comp_actL_tmk, assocInvMid_tmk, assocInvMid_tmk, tmk_actR])

@[simp] theorem assocInvₗ_tmk (x : X) (y : Y) (z : Z) :
    assocInvₗ X Y Z (tmk X (comp Y Z) (x ⊗ₜ tmk Y Z (y ⊗ₜ z))) =
      tmk (comp X Y) Z (tmk X Y (x ⊗ₜ y) ⊗ₜ z) := by
  simp [assocInvₗ, assocInvMid_tmk]

end Assoc

/-- Extensionality for maps out of `(X ⊗ Y) ⊗ Z`. -/
theorem comp_ext₂ {X : GBim A B} {Y : GBim B C} {Z : GBim C D} {M : Type*} [AddCommGroup M]
    [Module k M] {f g : (comp (comp X Y) Z).carrier →ₗ[k] M}
    (h : ∀ x y z, f (tmk _ Z (tmk X Y (x ⊗ₜ y) ⊗ₜ z)) = g (tmk _ Z (tmk X Y (x ⊗ₜ y) ⊗ₜ z))) :
    f = g :=
  comp_ext fun p z => by
    induction p using comp_induction with
    | hadd p q hp hq => simp only [add_tmul, map_add, hp, hq]
    | ht x y => exact h x y z

/-- Extensionality for maps out of `X ⊗ (Y ⊗ Z)`. -/
theorem comp_ext₂' {X : GBim A B} {Y : GBim B C} {Z : GBim C D} {M : Type*} [AddCommGroup M]
    [Module k M] {f g : (comp X (comp Y Z)).carrier →ₗ[k] M}
    (h : ∀ x y z, f (tmk X _ (x ⊗ₜ tmk Y Z (y ⊗ₜ z))) = g (tmk X _ (x ⊗ₜ tmk Y Z (y ⊗ₜ z)))) :
    f = g :=
  comp_ext fun x w => by
    induction w using comp_induction with
    | hadd p q hp hq => simp only [tmul_add, map_add, hp, hq]
    | ht y z => exact h x y z

/-- Extensionality for maps out of `((W ⊗ X) ⊗ Y) ⊗ Z`. -/
theorem comp_ext₃ {W : GBim A B} {X : GBim B C} {Y : GBim C D} {Z : GBim D E} {M : Type*}
    [AddCommGroup M] [Module k M] {f g : (comp (comp (comp W X) Y) Z).carrier →ₗ[k] M}
    (h : ∀ w x y z, f (tmk _ Z (tmk _ Y (tmk W X (w ⊗ₜ x) ⊗ₜ y) ⊗ₜ z)) =
      g (tmk _ Z (tmk _ Y (tmk W X (w ⊗ₜ x) ⊗ₜ y) ⊗ₜ z))) : f = g :=
  comp_ext fun p z => by
    induction p using comp_induction with
    | hadd p q hp hq => simp only [add_tmul, map_add, hp, hq]
    | ht q y =>
      induction q using comp_induction with
      | hadd p q hp hq => simp only [add_tmul, map_add, hp, hq]
      | ht w x => exact h w x y z

/-- The associator. -/
def associator (X : GBim A B) (Y : GBim B C) (Z : GBim C D) :
    comp (comp X Y) Z ≅ comp X (comp Y Z) where
  hom := mkHomₗ (assocHomₗ X Y Z) (fun a => comp_ext₂ fun x y z => by simp)
    (fun d => comp_ext₂ fun x y z => by simp) (comp_ext₂ fun x y z => by simp [tmul_add, add_tmul, add_assoc])
  inv := mkHomₗ (assocInvₗ X Y Z) (fun a => comp_ext₂' fun x y z => by simp)
    (fun d => comp_ext₂' fun x y z => by simp) (comp_ext₂' fun x y z => by simp [tmul_add, add_tmul, add_assoc])
  hom_inv_id := hom_ext (comp_ext₂ fun x y z => by simp)
  inv_hom_id := hom_ext (comp_ext₂' fun x y z => by simp)

@[simp] theorem associator_hom_val (X : GBim A B) (Y : GBim B C) (Z : GBim C D) :
    (associator X Y Z).hom.1 = assocHomₗ X Y Z := rfl

@[simp] theorem associator_inv_val (X : GBim A B) (Y : GBim B C) (Z : GBim C D) :
    (associator X Y Z).inv.1 = assocInvₗ X Y Z := rfl

/-! ### Identities and unitors -/

/-- The regular bimodule, the identity 1-morphism. -/
def id (A : GrAlg k) : GBim A A where
  carrier := A
  actL := Algebra.lmul k A
  actR := Algebra.lmul k A
  comm a b := LinearMap.ext fun x => by simp [mul_left_comm]
  deg := A.deg
  deg_actL a := LinearMap.ext fun x => by simp [A.deg_mul, add_comm]
  deg_actR a := LinearMap.ext fun x => by simp [A.deg_mul, add_comm]
  off := 0

/-- The identification of `A` with the carrier of the regular bimodule. -/
def idEquiv (A : GrAlg k) : A ≃ₗ[k] (id A).carrier := LinearEquiv.refl k A

@[simp] theorem id_actL (a x : A) : (id A).actL a (idEquiv A x) = idEquiv A (a * x) := rfl

@[simp] theorem id_actR (a x : A) : (id A).actR a (idEquiv A x) = idEquiv A (a * x) := rfl

@[simp] theorem id_D (x : A) : (id A).D (idEquiv A x) = idEquiv A (A.deg x) := by
  show A.deg x + ((0 : ℤ) • (1 : Module.End k A)) x = _
  simp
  rfl

theorem comp_ext_idL {X : GBim A B} {M : Type*} [AddCommGroup M] [Module k M]
    {f g : (comp (id A) X).carrier →ₗ[k] M}
    (h : ∀ a x, f (tmk (id A) X (idEquiv A a ⊗ₜ x)) = g (tmk (id A) X (idEquiv A a ⊗ₜ x))) :
    f = g :=
  comp_ext fun a x => by simpa using h ((idEquiv A).symm a) x

theorem comp_ext_idR {X : GBim A B} {M : Type*} [AddCommGroup M] [Module k M]
    {f g : (comp X (id B)).carrier →ₗ[k] M}
    (h : ∀ x b, f (tmk X (id B) (x ⊗ₜ idEquiv B b)) = g (tmk X (id B) (x ⊗ₜ idEquiv B b))) :
    f = g :=
  comp_ext fun x b => by simpa using h x ((idEquiv B).symm b)

@[simp] theorem tmk_one_actL (X : GBim A B) (a : A) (x : X) :
    tmk (id A) X (idEquiv A 1 ⊗ₜ X.actL a x) = tmk (id A) X (idEquiv A a ⊗ₜ x) := by
  rw [← tmk_actR, id_actR, mul_one]

@[simp] theorem tmk_actR_one (X : GBim A B) (b : B) (x : X) :
    tmk X (id B) (X.actR b x ⊗ₜ idEquiv B 1) = tmk X (id B) (x ⊗ₜ idEquiv B b) := by
  rw [tmk_actR, id_actL, mul_one]

/-- `a ⊗ x ↦ a x`. -/
def leftUnitorₗ (X : GBim A B) : (comp (id A) X).carrier →ₗ[k] X :=
  cdesc (TensorProduct.lift (X.actL.toLinearMap ∘ₗ (idEquiv A).symm.toLinearMap))
    (fun b a x => by
      obtain ⟨a, rfl⟩ := (idEquiv A).surjective a
      simp [mul_comm b a])

@[simp] theorem leftUnitorₗ_tmk (X : GBim A B) (a : A) (x : X) :
    leftUnitorₗ X (tmk (id A) X (idEquiv A a ⊗ₜ x)) = X.actL a x := rfl

/-- `x ↦ 1 ⊗ x`. -/
def leftUnitorInvₗ (X : GBim A B) : X →ₗ[k] (comp (id A) X).carrier :=
  tmk (id A) X ∘ₗ TensorProduct.mk k (id A).carrier X (idEquiv A 1)

@[simp] theorem leftUnitorInvₗ_apply (X : GBim A B) (x : X) :
    leftUnitorInvₗ X x = tmk (id A) X (idEquiv A 1 ⊗ₜ x) := rfl

/-- The left unitor. -/
def leftUnitor (X : GBim A B) : comp (id A) X ≅ X where
  hom := mkHomₗ (leftUnitorₗ X)
    (fun a => comp_ext_idL fun a' x => by simp)
    (fun b => comp_ext_idL fun a x => by simp [← Module.End.mul_apply, X.comm])
    (comp_ext_idL fun a x => by simp [D_actL_apply, add_comm])
  inv := mkHomₗ (leftUnitorInvₗ X)
    (fun a => LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, leftUnitorInvₗ_apply, tmk_one_actL]
      rw [comp_actL_tmk, id_actL, mul_one])
    (fun b => LinearMap.ext fun x => rfl)
    (LinearMap.ext fun x => by simp [GrAlg.deg_one])
  hom_inv_id := hom_ext (comp_ext_idL fun a x => by simp)
  inv_hom_id := hom_ext (LinearMap.ext fun x => by simp)

@[simp] theorem leftUnitor_hom_val (X : GBim A B) : (leftUnitor X).hom.1 = leftUnitorₗ X := rfl

@[simp] theorem leftUnitor_inv_val (X : GBim A B) :
    (leftUnitor X).inv.1 = leftUnitorInvₗ X := rfl

/-- `x ⊗ b ↦ x b`. -/
def rightUnitorₗ (X : GBim A B) : (comp X (id B)).carrier →ₗ[k] X :=
  cdesc (TensorProduct.lift (X.actR.toLinearMap.flip.compl₂ (idEquiv B).symm.toLinearMap))
    (fun b x b' => by
      obtain ⟨b', rfl⟩ := (idEquiv B).surjective b'
      simp [mul_comm b b'])

@[simp] theorem rightUnitorₗ_tmk (X : GBim A B) (x : X) (b : B) :
    rightUnitorₗ X (tmk X (id B) (x ⊗ₜ idEquiv B b)) = X.actR b x := rfl

/-- `x ↦ x ⊗ 1`. -/
def rightUnitorInvₗ (X : GBim A B) : X →ₗ[k] (comp X (id B)).carrier :=
  tmk X (id B) ∘ₗ (TensorProduct.mk k X (id B).carrier).flip (idEquiv B 1)

@[simp] theorem rightUnitorInvₗ_apply (X : GBim A B) (x : X) :
    rightUnitorInvₗ X x = tmk X (id B) (x ⊗ₜ idEquiv B 1) := rfl

/-- The right unitor. -/
def rightUnitor (X : GBim A B) : comp X (id B) ≅ X where
  hom := mkHomₗ (rightUnitorₗ X)
    (fun a => comp_ext_idR fun x b => by simp [← Module.End.mul_apply, X.comm])
    (fun c => comp_ext_idR fun x b => by simp)
    (comp_ext_idR fun x b => by simp [D_actR_apply])
  inv := mkHomₗ (rightUnitorInvₗ X)
    (fun a => LinearMap.ext fun x => rfl)
    (fun b => LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, rightUnitorInvₗ_apply, tmk_actR_one]
      rw [comp_actR_tmk, id_actR, mul_one])
    (LinearMap.ext fun x => by simp [GrAlg.deg_one])
  hom_inv_id := hom_ext (comp_ext_idR fun x b => by simp)
  inv_hom_id := hom_ext (LinearMap.ext fun x => by simp)

@[simp] theorem rightUnitor_hom_val (X : GBim A B) : (rightUnitor X).hom.1 = rightUnitorₗ X := rfl

@[simp] theorem rightUnitor_inv_val (X : GBim A B) :
    (rightUnitor X).inv.1 = rightUnitorInvₗ X := rfl

theorem whiskerRight_comp_law {X X' : GBim A B} (η : X ⟶ X') (Y : GBim B C) (Z : GBim C D) :
    whiskerRight η (comp Y Z) = (associator X Y Z).inv ≫ whiskerRight (whiskerRight η Y) Z ≫
      (associator X' Y Z).hom :=
  hom_ext (comp_ext₂' fun x y z => by simp)

theorem whisker_assoc_law (X : GBim A B) {Y Y' : GBim B C} (η : Y ⟶ Y') (Z : GBim C D) :
    whiskerRight (whiskerLeft X η) Z = (associator X Y Z).hom ≫
      whiskerLeft X (whiskerRight η Z) ≫ (associator X Y' Z).inv :=
  hom_ext (comp_ext₂ fun x y z => by simp)

theorem triangle_law (X : GBim A B) (Y : GBim B C) :
    (associator X (id B) Y).hom ≫ whiskerLeft X (leftUnitor Y).hom =
      whiskerRight (rightUnitor X).hom Y :=
  hom_ext (comp_ext₂ fun x b y => by
    obtain ⟨b, rfl⟩ := (idEquiv B).surjective b
    simp [tmk_actR])

end GBim

namespace GrAlg

open GBim

/-- **The bicategory of graded bimodules.** -/
instance bicategory : Bicategory (GrAlg k) where
  Hom A B := GBim A B
  id A := GBim.id A
  comp X Y := GBim.comp X Y
  homCategory A B := GBim.category
  whiskerLeft X _ _ η := GBim.whiskerLeft X η
  whiskerRight η Y := GBim.whiskerRight η Y
  associator X Y Z := GBim.associator X Y Z
  leftUnitor X := GBim.leftUnitor X
  rightUnitor X := GBim.rightUnitor X
  whiskerLeft_id X Y := hom_ext (comp_ext fun x y => by simp)
  whiskerLeft_comp X _ _ _ η θ := hom_ext (comp_ext fun x y => by simp)
  id_whiskerLeft η := hom_ext (comp_ext_idL fun a x => by simp [hom_actL])
  comp_whiskerLeft X Y _ _ η := hom_ext (comp_ext₂ fun x y z => by simp)
  id_whiskerRight X Y := hom_ext (comp_ext fun x y => by simp)
  comp_whiskerRight η θ Y := hom_ext (comp_ext fun x y => by simp)
  whiskerRight_id η := hom_ext (comp_ext_idR fun x b => by simp [hom_actR])
  whiskerRight_comp η Y Z := whiskerRight_comp_law η Y Z
  whisker_assoc X _ _ η Z := whisker_assoc_law X η Z
  whisker_exchange η θ := hom_ext (comp_ext fun x y => by simp)
  pentagon W X Y Z := hom_ext (comp_ext₃ fun w x y z => by simp)
  triangle X Y := triangle_law X Y

end GrAlg

end Categorification.TwoRep.Grassmannian
