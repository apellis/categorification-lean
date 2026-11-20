/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.PiLinear
import Categorification.TwoRep.LinFunBiproduct
import Categorification.TwoRep.RouqFullCL
import Categorification.KLR.Symmetries

/-!
# Products of Rouquier families

Given a family `S j` of Rouquier families (Brundan, arXiv:1501.00350v1, Def. 1.1) in `LinearCat k`
over a common weight datum, the product `RouqFamily.pi S` assigns to a weight `x` the product
category `∏_j (S j).obj x`, with `E_i`, `F_i`, dots, crossings and adjunctions acting
componentwise. All single-colour relations hold componentwise.

This is the black part of the categorical action on the region categories of Webster,
*Knot invariants and higher representation theory*, arXiv:1309.3796v3, Thm. 4.25: a region of a
red/black diagram carries the product over red labellings of cyclotomic weight categories.
-/

noncomputable section

open CategoryTheory CategoryTheory.Bicategory

namespace Categorification.TwoRep

universe w v u u₀ u₁

section PiFunctor

variable {J : Type u₀} {C D : J → Type*} [∀ j, Category (C j)] [∀ j, Category (D j)]
  [∀ j, Preadditive (C j)] [∀ j, Preadditive (D j)]

instance pi_additive (F : ∀ j, C j ⥤ D j) [∀ j, (F j).Additive] :
    (Functor.pi F).Additive where
  map_add := funext fun _ => Functor.map_add _

instance pi_linear (R : Type*) [Semiring R] [∀ j, Linear R (C j)] [∀ j, Linear R (D j)]
    (F : ∀ j, C j ⥤ D j) [∀ j, (F j).Linear R] : (Functor.pi F).Linear R where
  map_smul _ _ := funext fun j => Functor.map_smul (F j) _ _

end PiFunctor

/-- A family of adjunctions gives an adjunction of the product functors. -/
def Adjunction.piFamily {J : Type u₀} {C D : J → Type*} [∀ j, Category (C j)]
    [∀ j, Category (D j)] {F : ∀ j, C j ⥤ D j} {G : ∀ j, D j ⥤ C j}
    (adj : ∀ j, F j ⊣ G j) : Functor.pi F ⊣ Functor.pi G where
  unit :=
    { app := fun X j => (adj j).unit.app (X j)
      naturality := fun _ _ f => funext fun j => (adj j).unit.naturality (f j) }
  counit :=
    { app := fun X j => (adj j).counit.app (X j)
      naturality := fun _ _ f => funext fun j => (adj j).counit.naturality (f j) }
  left_triangle_components X := funext fun j => (adj j).left_triangle_components (X j)
  right_triangle_components X := funext fun j => (adj j).right_triangle_components (X j)

namespace LinearCat

variable {k : Type w} [CommRing k] {J : Type u₀}

/-- The product of a family of 1-morphisms of `LinearCat k`. -/
def piHom {A B : J → LinearCat.{w, v, u} k} (F : ∀ j, A j ⟶ B j) : pi A ⟶ pi B :=
  ⟨Functor.pi fun j => (F j).obj,
    ⟨pi_additive (C := fun j => A j) (D := fun j => B j) _,
      pi_linear (C := fun j => A j) (D := fun j => B j) k _⟩⟩

@[simp] theorem piHom_obj_obj {A B : J → LinearCat.{w, v, u} k} (F : ∀ j, A j ⟶ B j)
    (X : pi A) (j : J) : (piHom F).obj.obj X j = (F j).obj.obj (X j) := rfl

theorem piHom_obj_map {A B : J → LinearCat.{w, v, u} k} (F : ∀ j, A j ⟶ B j)
    {X Y : pi A} (f : X ⟶ Y) (j : J) :
    (piHom F).obj.map f j = (F j).obj.map (f j) := rfl

/-- A 2-morphism between 1-morphisms of products, given by its components. -/
def piTwo {A B : J → LinearCat.{w, v, u} k} {F G : pi A ⟶ pi B}
    (c : ∀ X j, F.obj.obj X j ⟶ G.obj.obj X j)
    (nat : ∀ (X Y : pi A) (f : X ⟶ Y) j, F.obj.map f j ≫ c Y j = c X j ≫ G.obj.map f j) :
    F ⟶ G :=
  ObjectProperty.homMk
    { app := fun X j => c X j
      naturality := fun X Y f => funext fun j => nat X Y f j }

@[simp] theorem piTwo_app {A B : J → LinearCat.{w, v, u} k} {F G : pi A ⟶ pi B}
    (c : ∀ X j, F.obj.obj X j ⟶ G.obj.obj X j) (nat) (X : pi A) (j : J) :
    (piTwo c nat).hom.app X j = c X j := rfl

/-- The product of a family of 2-morphisms. -/
def piCell {A B : J → LinearCat.{w, v, u} k} {F G : ∀ j, A j ⟶ B j}
    (η : ∀ j, F j ⟶ G j) :
    piHom F ⟶ piHom G :=
  piTwo (fun X j => (η j).hom.app (X j)) (fun _ _ f j => (η j).hom.naturality (f j))

theorem pi_hom_ext {A B : J → LinearCat.{w, v, u} k} {F G : pi A ⟶ pi B} {η θ : F ⟶ G}
    (h : ∀ X j, η.hom.app X j = θ.hom.app X j) : η = θ :=
  ObjectProperty.hom_ext _ (NatTrans.ext (funext fun X => funext fun j => h X j))

section Eval

variable {A B : J → LinearCat.{w, v, u} k} {F G H : pi A ⟶ pi B}

@[simp] theorem pi_comp_app (η : F ⟶ G) (θ : G ⟶ H) (X : pi A) (j : J) :
    (η ≫ θ).hom.app X j = η.hom.app X j ≫ θ.hom.app X j := rfl

@[simp] theorem pi_id_app (X : pi A) (j : J) : (𝟙 F : F ⟶ F).hom.app X j = 𝟙 _ := rfl

@[simp] theorem pi_add_app (η θ : F ⟶ G) (X : pi A) (j : J) :
    (η + θ).hom.app X j = η.hom.app X j + θ.hom.app X j := rfl

@[simp] theorem pi_sub_app (η θ : F ⟶ G) (X : pi A) (j : J) :
    (η - θ).hom.app X j = η.hom.app X j - θ.hom.app X j := rfl

@[simp] theorem pi_neg_app (η : F ⟶ G) (X : pi A) (j : J) :
    (-η).hom.app X j = -η.hom.app X j := rfl

@[simp] theorem pi_zero_app (X : pi A) (j : J) : (0 : F ⟶ G).hom.app X j = 0 := rfl

@[simp] theorem pi_smul_app (c : k) (η : F ⟶ G) (X : pi A) (j : J) :
    (c • η).hom.app X j = c • η.hom.app X j := rfl

/-- Evaluation of a 2-morphism of products at an object and a component. -/
def piEvalAdd (X : pi A) (j : J) : (F ⟶ G) →+ (F.obj.obj X j ⟶ G.obj.obj X j) where
  toFun η := η.hom.app X j
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem pi_sum_app {ι : Type*} (s : Finset ι) (η : ι → (F ⟶ G)) (X : pi A) (j : J) :
    (∑ m ∈ s, η m).hom.app X j = ∑ m ∈ s, (η m).hom.app X j :=
  map_sum (piEvalAdd (F := F) (G := G) X j) η s

/-- Evaluation of endomorphisms of a 1-morphism of products is a `k`-algebra homomorphism. -/
def piEvalAlg (X : pi A) (j : J) : End F →ₐ[k] End (F.obj.obj X j) where
  toFun η := η.hom.app X j
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem piEvalAlg_apply (X : pi A) (j : J) (η : End F) :
    piEvalAlg X j η = η.hom.app X j := rfl

@[simp] theorem pi_whiskerLeft_app {C' : J → LinearCat.{w, v, u} k} (K : pi C' ⟶ pi A)
    (η : F ⟶ G) (X : pi C') (j : J) : (K ◁ η).hom.app X j = η.hom.app (K.obj.obj X) j := rfl

@[simp] theorem pi_whiskerRight_piHom_app {C' : J → LinearCat.{w, v, u} k}
    (η : F ⟶ G) (K : ∀ j, B j ⟶ C' j) (X : pi A) (j : J) :
    (η ▷ piHom K).hom.app X j = (K j).obj.map (η.hom.app X j) := rfl

@[simp] theorem pi_associator_hom_app {C' D' : J → LinearCat.{w, v, u} k} (F : pi A ⟶ pi B)
    (G : pi B ⟶ pi C') (H : pi C' ⟶ pi D') (X : pi A) (j : J) :
    (α_ F G H).hom.hom.app X j = 𝟙 _ := rfl

@[simp] theorem pi_associator_inv_app {C' D' : J → LinearCat.{w, v, u} k} (F : pi A ⟶ pi B)
    (G : pi B ⟶ pi C') (H : pi C' ⟶ pi D') (X : pi A) (j : J) :
    (α_ F G H).inv.hom.app X j = 𝟙 _ := rfl

@[simp] theorem pi_leftUnitor_hom_app (F : pi A ⟶ pi B) (X : pi A) (j : J) :
    (λ_ F).hom.hom.app X j = 𝟙 _ := rfl

@[simp] theorem pi_leftUnitor_inv_app (F : pi A ⟶ pi B) (X : pi A) (j : J) :
    (λ_ F).inv.hom.app X j = 𝟙 _ := rfl

@[simp] theorem pi_rightUnitor_hom_app (F : pi A ⟶ pi B) (X : pi A) (j : J) :
    (ρ_ F).hom.hom.app X j = 𝟙 _ := rfl

@[simp] theorem pi_rightUnitor_inv_app (F : pi A ⟶ pi B) (X : pi A) (j : J) :
    (ρ_ F).inv.hom.app X j = 𝟙 _ := rfl

end Eval

theorem pi_hom_ext' {A B : J → LinearCat.{w, v, u} k} {F G : pi A ⟶ pi B} {η θ : F ⟶ G}
    (h : ∀ X j, piEvalAdd X j η = piEvalAdd X j θ) : η = θ :=
  pi_hom_ext h

/-- Evaluation of endomorphisms of a 1-morphism of `LinearCat k` at an object. -/
def evalAlg {C' D' : LinearCat.{w, v, u} k} {F : C' ⟶ D'} (Y : C') :
    End F →ₐ[k] End (F.obj.obj Y) where
  toFun η := η.hom.app Y
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem pi_hom_ext_alg {A B : J → LinearCat.{w, v, u} k} {F : pi A ⟶ pi B} {η θ : F ⟶ F}
    (h : ∀ X j, piEvalAlg X j η = piEvalAlg X j θ) : η = θ :=
  pi_hom_ext h

theorem piEvalAlg_ncEval {A B : J → LinearCat.{w, v, u} k} {F : pi A ⟶ pi B} (X : ∀ j, A j)
    (j : J) {n : ℕ} (y : Fin n → End F) (p : MvPolynomial (Fin n) k) :
    piEvalAlg X j (KLR.ncEval (A := End F) y p) =
      KLR.ncEval (A := End ((F.obj.obj X) j)) (fun a => piEvalAlg X j (y a)) p :=
  KLR.ncEval_map _ y p

theorem evalAlg_ncEval {C' D' : LinearCat.{w, v, u} k} {F : C' ⟶ D'} (Y : C') {n : ℕ}
    (y : Fin n → End F) (p : MvPolynomial (Fin n) k) :
    evalAlg Y (KLR.ncEval (A := End F) y p) =
      KLR.ncEval (A := End (F.obj.obj Y)) (fun a => evalAlg Y (y a)) p :=
  KLR.ncEval_map _ y p

theorem powComp_piCell {A B : J → LinearCat.{w, v, u} k} {F : ∀ j, A j ⟶ B j}
    (η : ∀ j, F j ⟶ F j) (n : ℕ) :
    powComp (piCell η) n = piCell fun j => powComp (η j) n := by
  induction n with
  | zero => exact pi_hom_ext fun _ _ => rfl
  | succ n ih => rw [powComp_succ, ih]; exact pi_hom_ext fun _ _ => rfl

/-- Evaluation of a 2-morphism of `LinearCat k` at an object. -/
def evalAdd {C' D' : LinearCat.{w, v, u} k} {F G : C' ⟶ D'} (Y : C') :
    (F ⟶ G) →+ (F.obj.obj Y ⟶ G.obj.obj Y) where
  toFun η := η.hom.app Y
  map_zero' := rfl
  map_add' _ _ := rfl

end LinearCat

open LinearCat

variable {k : Type w} [CommRing k] {J : Type u₀}
  {I : Type*} {C : QuantumGroup.CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : QuantumGroup.UDot.WeightDatum C X Y}

namespace RouqFamily

variable (S : J → RouqFamily (B := LinearCat.{w, v, u} k) RD)

/-- The product of the families `E_i`. -/
abbrev piE (i : I) {x y : X} (h : x + RD.iX i = y) :
    (LinearCat.pi fun j => (S j).obj x) ⟶ LinearCat.pi fun j => (S j).obj y :=
  piHom fun j => (S j).E i h

/-- The product of the families `F_i`. -/
abbrev piF (i : I) {x y : X} (h : x + RD.iX i = y) :
    (LinearCat.pi fun j => (S j).obj y) ⟶ LinearCat.pi fun j => (S j).obj x :=
  piHom fun j => (S j).F i h

/-- The product of the dots. -/
abbrev piDot (i : I) {x y : X} (h : x + RD.iX i = y) : piE S i h ⟶ piE S i h :=
  piCell fun j => (S j).dot i h

/-- The product of the crossings. -/
abbrev piCross (i i' : I) {a b c d : X} (h₁ : a + RD.iX i' = b) (h₂ : b + RD.iX i = d)
    (h₃ : a + RD.iX i = c) (h₄ : c + RD.iX i' = d) :
    piE S i' h₁ ≫ piE S i h₂ ⟶ piE S i h₃ ≫ piE S i' h₄ :=
  piCell (F := fun j => (S j).E i' h₁ ≫ (S j).E i h₂)
    (G := fun j => (S j).E i h₃ ≫ (S j).E i' h₄)
    fun j => (S j).cross i i' h₁ h₂ h₃ h₄

/-- The product of the adjunctions. -/
abbrev piAdj (i : I) {x y : X} (h : x + RD.iX i = y) : piE S i h ⊣ piF S i h :=
  ofAdjunction k (Adjunction.piFamily fun j => toAdjunction ((S j).adj i h))

/-- The local Rouquier relations of the product. -/
def piLoc (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) :
    RouqLoc (piAdj S i h₁) (piAdj S i h₂) (piDot S i h₁) (piDot S i h₂)
      (piCross S i i h₁ h₂ h₁ h₂) (RD.pair (RD.iY i) b) where
  slide_left := pi_hom_ext fun X j => by
    exact congrArg (fun t => t.hom.app (X j)) ((S j).loc i h₁ h₂).slide_left
  slide_right := pi_hom_ext fun X j => by
    exact congrArg (fun t => t.hom.app (X j)) ((S j).loc i h₁ h₂).slide_right
  invPos hh :=
    { f' := piTwo (fun X j => (((S j).loc i h₁ h₂).invPos hh).f'.hom.app (X j))
        (fun _ _ f j => (((S j).loc i h₁ h₂).invPos hh).f'.hom.naturality (f j))
      g' m := piTwo (fun X j => ((((S j).loc i h₁ h₂).invPos hh).g' m).hom.app (X j))
        (fun _ _ f j => ((((S j).loc i h₁ h₂).invPos hh).g' m).hom.naturality (f j))
      total := pi_hom_ext' fun X j => by
        have h := congrArg (evalAdd (X j)) (((S j).loc i h₁ h₂).invPos hh).total
        simp only [map_add, map_sum] at h
        simp only [map_add, map_sum, powComp_piCell]
        exact h
      ff := pi_hom_ext fun X j => by
        exact congrArg (fun t => t.hom.app (X j)) (((S j).loc i h₁ h₂).invPos hh).ff
      fg m hm := pi_hom_ext fun X j => by
        rw [powComp_piCell]
        exact congrArg (fun t => t.hom.app (X j)) ((((S j).loc i h₁ h₂).invPos hh).fg m hm)
      gf m hm := pi_hom_ext fun X j => by
        exact congrArg (fun t => t.hom.app (X j)) ((((S j).loc i h₁ h₂).invPos hh).gf m hm)
      gg m m' hm hm' := pi_hom_ext fun X j => by
        have h := congrArg (fun t => t.hom.app (X j))
          ((((S j).loc i h₁ h₂).invPos hh).gg m m' hm hm')
        rw [powComp_piCell]
        split_ifs at h ⊢ <;> exact h }
  invNeg hh :=
    { f' := piTwo (fun X j => (((S j).loc i h₁ h₂).invNeg hh).f'.hom.app (X j))
        (fun _ _ f j => (((S j).loc i h₁ h₂).invNeg hh).f'.hom.naturality (f j))
      g' m := piTwo (fun X j => ((((S j).loc i h₁ h₂).invNeg hh).g' m).hom.app (X j))
        (fun _ _ f j => ((((S j).loc i h₁ h₂).invNeg hh).g' m).hom.naturality (f j))
      total := pi_hom_ext' fun X j => by
        have h := congrArg (evalAdd (X j)) (((S j).loc i h₁ h₂).invNeg hh).total
        simp only [map_add, map_sum] at h
        simp only [map_add, map_sum, powComp_piCell]
        exact h
      ff := pi_hom_ext fun X j => by
        exact congrArg (fun t => t.hom.app (X j)) (((S j).loc i h₁ h₂).invNeg hh).ff
      fg m hm := pi_hom_ext fun X j => by
        exact congrArg (fun t => t.hom.app (X j)) ((((S j).loc i h₁ h₂).invNeg hh).fg m hm)
      gf m hm := pi_hom_ext fun X j => by
        rw [powComp_piCell]
        exact congrArg (fun t => t.hom.app (X j)) ((((S j).loc i h₁ h₂).invNeg hh).gf m hm)
      gg m m' hm hm' := pi_hom_ext fun X j => by
        have h := congrArg (fun t => t.hom.app (X j))
          ((((S j).loc i h₁ h₂).invNeg hh).gg m m' hm hm')
        rw [powComp_piCell]
        split_ifs at h ⊢ <;> exact h }

/-- **The product of Rouquier families**: weight categories, `E_i`, `F_i`, dots, crossings and
adjunctions are the products of those of the factors. -/
def pi : RouqFamily (B := LinearCat.{w, max u₀ v, max u₀ u} k) RD where
  obj x := LinearCat.pi fun j => (S j).obj x
  E i _ _ h := piE S i h
  F i _ _ h := piF S i h
  dot i _ _ h := piDot S i h
  cross i i' _ _ _ _ h₁ h₂ h₃ h₄ := piCross S i i' h₁ h₂ h₃ h₄
  adj i _ _ h := piAdj S i h
  square i _ _ _ h₁ h₂ := pi_hom_ext fun X j => by
    exact congrArg (fun t => t.hom.app (X j)) ((S j).square i h₁ h₂)
  braid i _ _ _ _ h₁ h₂ h₃ := pi_hom_ext fun X j => by
    exact congrArg (fun t => t.hom.app (X j)) ((S j).braid i h₁ h₂ h₃)
  loc i _ _ _ h₁ h₂ := piLoc S i h₁ h₂

variable {S}

/-- The mixed upward KLR relations hold in a product when they hold in every factor. -/
theorem _root_.Categorification.TwoRep.RouqUpKLR.pi {Q : I → I → MvPolynomial (Fin 2) k}
    (H : ∀ j, RouqUpKLR (S j) Q) : RouqUpKLR (pi S) Q where
  square i i' hii' _ _ _ _ h₁ h₂ h₃ h₄ := pi_hom_ext_alg fun X j => by
    have h := congrArg (evalAlg (X j)) ((H j).square i i' hii' h₁ h₂ h₃ h₄)
    rw [evalAlg_ncEval] at h
    erw [piEvalAlg_ncEval]
    refine h.trans ?_
    congr 1
    funext a
    fin_cases a <;> rfl
  slide_left i i' hii' _ _ _ _ h₁ h₂ h₃ h₄ := pi_hom_ext fun X j => by
    exact congrArg (fun t => t.hom.app (X j)) ((H j).slide_left i i' hii' h₁ h₂ h₃ h₄)
  slide_right i i' hii' _ _ _ _ h₁ h₂ h₃ h₄ := pi_hom_ext fun X j => by
    exact congrArg (fun t => t.hom.app (X j)) ((H j).slide_right i i' hii' h₁ h₂ h₃ h₄)
  braid i i' c hb _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 :=
    pi_hom_ext fun X j => by
      exact congrArg (fun t => t.hom.app (X j))
        ((H j).braid i i' c hb e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12)
  braidQ i i' hii' _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ := pi_hom_ext_alg fun X j => by
    have h := congrArg (evalAlg (X j)) ((H j).braidQ i i' hii' h₁ h₂ h₃ h₄ h₅ h₆ h₇)
    rw [evalAlg_ncEval] at h
    erw [piEvalAlg_ncEval]
    refine h.trans ?_
    congr 1
    funext a
    fin_cases a <;> rfl

/-- Brundan's mixed inversion relation holds in a product when it holds in every factor. -/
theorem brundanMixedInversion_pi (M : ∀ j, BrundanMixedInversion (S j)) :
    BrundanMixedInversion (pi S) := by
  intro i i' hii' _ _ _ _ hj hi' hi hj'
  have hM : ∀ j, IsIso ((S j).mixedSigma i i' hj hi' hi hj') :=
    fun j => M j i i' hii' hj hi' hi hj'
  refine ⟨piTwo (fun X j => (inv ((S j).mixedSigma i i' hj hi' hi hj')).hom.app (X j))
    (fun _ _ f j => (inv ((S j).mixedSigma i i' hj hi' hi hj')).hom.naturality (f j)),
    pi_hom_ext fun X j => ?_, pi_hom_ext fun X j => ?_⟩
  · exact congrArg (fun t => t.hom.app (X j))
      (IsIso.hom_inv_id ((S j).mixedSigma i i' hj hi' hi hj'))
  · exact congrArg (fun t => t.hom.app (X j))
      (IsIso.inv_hom_id ((S j).mixedSigma i i' hj hi' hi hj'))

end RouqFamily

end Categorification.TwoRep
