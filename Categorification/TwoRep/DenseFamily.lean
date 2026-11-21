/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Idempotents.Basic

/-!
# Functors and natural transformations on a dense family of objects

Let `A` be a preadditive category and `P : T → A` a family of objects. The family is *dense*
(`IsDenseFamily P`) if every object `a` of `A` is a retract of a finite direct sum of members
of the family in the following explicit sense: there are `t : Fin n → T` and morphisms
`q i : a ⟶ P (t i)`, `p i : P (t i) ⟶ a` with `∑ i, q i ≫ p i = 𝟙 a`
(`RetractDecomposition`). No biproducts in `A` are needed.

This is the categorical input of B. Webster, *Knot invariants and higher representation
theory*, arXiv:1309.3796v2, Corollary 3.27: a functor given on a dense family extends to the
whole category, and natural transformations are determined by their components on the family.

## Main results

* `IsDenseFamily.natTrans_ext`: natural transformations between functors `F G : A ⥤ D`, with
  `F` additive, agreeing on every `P t` are equal.
* `IsDenseFamily.extendNatTrans`: a family of maps `F.obj (P t) ⟶ G.obj (P t)` natural with
  respect to all morphisms `P t ⟶ P t'` extends to a natural transformation `F ⟶ G`
  (`F`, `G` additive); `IsDenseFamily.extendNatIso` is the version for isomorphisms.
* `IsDenseFamily.extendFunctor`: if `D` has finite biproducts and is idempotent complete, an
  additive functor `Φ₀ : InducedCategory A P ⥤ D` extends to an additive functor `A ⥤ D`
  (`k`-linear when `Φ₀` is), with `IsDenseFamily.extendFunctorIso :
  inducedFunctor P ⋙ extendFunctor Φ₀ hP ≅ Φ₀`.
-/

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace Categorification.TwoRep

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] {T : Type w}

/-- A presentation of `a` as a retract of a finite direct sum of members of the family `P`,
given by its components: `∑ i, q i ≫ p i = 𝟙 a`. -/
structure RetractDecomposition (P : T → A) (a : A) where
  /-- The number of summands. -/
  n : ℕ
  /-- The indices of the summands. -/
  t : Fin n → T
  /-- The components of the inclusion of `a` into the sum. -/
  q : ∀ i, a ⟶ P (t i)
  /-- The components of the projection of the sum onto `a`. -/
  p : ∀ i, P (t i) ⟶ a
  sum_q_p : ∑ i, q i ≫ p i = 𝟙 a

/-- The family `P` is dense: every object is a retract of a finite direct sum of members of
the family. -/
structure IsDenseFamily (P : T → A) : Prop where
  nonempty_decomposition : ∀ a : A, Nonempty (RetractDecomposition P a)

namespace RetractDecomposition

variable {P : T → A}

/-- The decomposition of a member `P s` of the family with the single summand `P s`. -/
@[simps]
def single (s : T) : RetractDecomposition P (P s) where
  n := 1
  t _ := s
  q _ := 𝟙 _
  p _ := 𝟙 _
  sum_q_p := by simp

end RetractDecomposition

namespace IsDenseFamily

variable {P : T → A}

/-- A chosen decomposition of an object. -/
noncomputable def decomp (hP : IsDenseFamily P) (a : A) : RetractDecomposition P a :=
  Classical.choice (hP.nonempty_decomposition a)

section NatTrans

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] {F G : A ⥤ D}

/-- The component of a natural transformation at `a`, expanded along a decomposition. -/
lemma app_eq_sum [F.Additive] {a : A} (d : RetractDecomposition P a) (α : F ⟶ G) :
    α.app a = ∑ i, F.map (d.q i) ≫ α.app (P (d.t i)) ≫ G.map (d.p i) := by
  conv_lhs => rw [← Category.id_comp (α.app a), ← F.map_id, ← d.sum_q_p, F.map_sum, sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [F.map_comp, Category.assoc, α.naturality]

/-- Natural transformations out of an additive functor are determined by their components on
a dense family. -/
lemma natTrans_ext (hP : IsDenseFamily P) [F.Additive] {α β : F ⟶ G}
    (h : ∀ s, α.app (P s) = β.app (P s)) : α = β := by
  ext a
  rw [app_eq_sum (hP.decomp a) α, app_eq_sum (hP.decomp a) β]
  simp only [h]

/-- The candidate component at `a` of the extension of a family of maps on `P`. -/
def extensionComponent (η : ∀ s, F.obj (P s) ⟶ G.obj (P s)) {a : A}
    (d : RetractDecomposition P a) : F.obj a ⟶ G.obj a :=
  ∑ i, F.map (d.q i) ≫ η (d.t i) ≫ G.map (d.p i)

/-- Naturality of the candidate components, for arbitrary decompositions of source and target;
in particular the candidate component does not depend on the decomposition. -/
lemma map_comp_extensionComponent [F.Additive] [G.Additive]
    (η : ∀ s, F.obj (P s) ⟶ G.obj (P s))
    (hη : ∀ {s s' : T} (g : P s ⟶ P s'), F.map g ≫ η s' = η s ≫ G.map g)
    {a b : A} (d : RetractDecomposition P a) (d' : RetractDecomposition P b) (f : a ⟶ b) :
    F.map f ≫ extensionComponent η d' = extensionComponent η d ≫ G.map f := by
  have hF : F.map f = ∑ i, F.map (d.q i) ≫ F.map (d.p i ≫ f) := by
    conv_lhs => rw [← Category.id_comp f, ← d.sum_q_p, sum_comp, F.map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Category.assoc, F.map_comp]
  have hG : G.map f = ∑ j, G.map (f ≫ d'.q j) ≫ G.map (d'.p j) := by
    conv_lhs => rw [← Category.comp_id f, ← d'.sum_q_p, comp_sum, G.map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [← G.map_comp, Category.assoc]
  rw [hF, hG, extensionComponent, extensionComponent, sum_comp, sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [comp_sum, Category.assoc]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have := hη (d.p i ≫ f ≫ d'.q j)
  rw [← F.map_comp_assoc, ← G.map_comp_assoc, Category.assoc, reassoc_of% this]

/-- A family of maps `F.obj (P s) ⟶ G.obj (P s)`, natural with respect to all morphisms
`P s ⟶ P s'`, extends to a natural transformation `F ⟶ G` when `F`, `G` are additive and `P`
is dense. -/
noncomputable def extendNatTrans (hP : IsDenseFamily P) [F.Additive] [G.Additive]
    (η : ∀ s, F.obj (P s) ⟶ G.obj (P s))
    (hη : ∀ {s s' : T} (g : P s ⟶ P s'), F.map g ≫ η s' = η s ≫ G.map g) : F ⟶ G where
  app a := extensionComponent η (hP.decomp a)
  naturality _ _ f := map_comp_extensionComponent η hη _ _ f

/-- For the one-summand decomposition of `P s`, the candidate component is `η s`. -/
lemma extensionComponent_single (η : ∀ s, F.obj (P s) ⟶ G.obj (P s)) (s : T) :
    extensionComponent η (RetractDecomposition.single (P := P) s) = η s := by
  change ∑ _i : Fin 1, F.map (𝟙 _) ≫ η s ≫ G.map (𝟙 _) = η s
  simp

/-- The extended natural transformation has the prescribed components on the family. -/
@[simp]
lemma extendNatTrans_app (hP : IsDenseFamily P) [F.Additive] [G.Additive]
    (η : ∀ s, F.obj (P s) ⟶ G.obj (P s))
    (hη : ∀ {s s' : T} (g : P s ⟶ P s'), F.map g ≫ η s' = η s ≫ G.map g) (s : T) :
    (hP.extendNatTrans η hη).app (P s) = η s := by
  have := map_comp_extensionComponent η hη (RetractDecomposition.single s) (hP.decomp (P s))
    (𝟙 (P s))
  simp only [extensionComponent_single, F.map_id, G.map_id, Category.id_comp,
    Category.comp_id] at this
  exact this

/-- A family of isomorphisms `F.obj (P s) ≅ G.obj (P s)`, natural with respect to all
morphisms `P s ⟶ P s'`, extends to a natural isomorphism `F ≅ G` when `F`, `G` are additive
and `P` is dense. -/
noncomputable def extendNatIso (hP : IsDenseFamily P) [F.Additive] [G.Additive]
    (η : ∀ s, F.obj (P s) ≅ G.obj (P s))
    (hη : ∀ {s s' : T} (g : P s ⟶ P s'), F.map g ≫ (η s').hom = (η s).hom ≫ G.map g) :
    F ≅ G where
  hom := hP.extendNatTrans (fun s => (η s).hom) hη
  inv := hP.extendNatTrans (fun s => (η s).inv) fun g => by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hη, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  hom_inv_id := hP.natTrans_ext fun s => by simp
  inv_hom_id := hP.natTrans_ext fun s => by simp

/-- The extended natural isomorphism has the prescribed components on the family. -/
@[simp]
lemma extendNatIso_hom_app (hP : IsDenseFamily P) [F.Additive] [G.Additive]
    (η : ∀ s, F.obj (P s) ≅ G.obj (P s))
    (hη : ∀ {s s' : T} (g : P s ⟶ P s'), F.map g ≫ (η s').hom = (η s).hom ≫ G.map g)
    (s : T) : (hP.extendNatIso η hη).hom.app (P s) = (η s).hom := by
  simp [extendNatIso]

end NatTrans

section ExtendFunctor

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] (Φ₀ : InducedCategory A P ⥤ D)

/-- The value of `Φ₀` on a morphism `P s ⟶ P s'` of `A`. -/
def familyMap {s s' : T} (f : P s ⟶ P s') : Φ₀.obj s ⟶ Φ₀.obj s' :=
  Φ₀.map (InducedCategory.homMk (X := s) (Y := s') f)

omit [Preadditive A] [Preadditive D] in
/-- `familyMap` preserves identities. -/
@[simp]
lemma familyMap_id (s : T) : familyMap Φ₀ (𝟙 (P s)) = 𝟙 _ :=
  Φ₀.map_id s

omit [Preadditive A] [Preadditive D] in
/-- `familyMap` preserves composition. -/
lemma familyMap_comp {s s' s'' : T} (f : P s ⟶ P s') (g : P s' ⟶ P s'') :
    familyMap Φ₀ (f ≫ g) = familyMap Φ₀ f ≫ familyMap Φ₀ g :=
  Φ₀.map_comp (InducedCategory.homMk f) (InducedCategory.homMk g)

omit [Preadditive A] [Preadditive D] in
/-- `Φ₀.map` in terms of `familyMap`. -/
lemma map_eq_familyMap {s s' : InducedCategory A P} (g : s ⟶ s') :
    Φ₀.map g = familyMap Φ₀ g.hom := rfl

variable [Φ₀.Additive]

/-- `familyMap` is additive. -/
lemma familyMap_add {s s' : T} (f g : P s ⟶ P s') :
    familyMap Φ₀ (f + g) = familyMap Φ₀ f + familyMap Φ₀ g :=
  Φ₀.map_add (f := InducedCategory.homMk f) (g := InducedCategory.homMk g)

/-- `familyMap` preserves finite sums. -/
lemma familyMap_sum {s s' : T} {ι : Type*} (S : Finset ι) (f : ι → (P s ⟶ P s')) :
    familyMap Φ₀ (∑ i ∈ S, f i) = ∑ i ∈ S, familyMap Φ₀ (f i) :=
  map_sum ((Φ₀.mapAddHom (X := s) (Y := s')).comp
    (InducedCategory.homAddEquiv (F := P)).symm.toAddMonoidHom) f S

/-- The basic identity: inserting a decomposition of `a` between `x` and `y`. -/
lemma sum_familyMap_comp {a : A} (d : RetractDecomposition P a) {s s' : T} (x : P s ⟶ a)
    (y : a ⟶ P s') :
    ∑ j, familyMap Φ₀ (x ≫ d.q j) ≫ familyMap Φ₀ (d.p j ≫ y) = familyMap Φ₀ (x ≫ y) := by
  simp only [← familyMap_comp, ← familyMap_sum]
  congr 1
  conv_rhs => rw [← Category.id_comp y, ← d.sum_q_p, sum_comp, comp_sum]
  simp

variable [HasFiniteBiproducts D]

/-- The direct sum in `D` of the values of `Φ₀` on the summands of a decomposition. -/
noncomputable abbrev sumObj {a : A} (d : RetractDecomposition P a) : D :=
  ⨁ fun i => Φ₀.obj (d.t i)

/-- The matrix of a morphism `f : a ⟶ b` with respect to decompositions of `a` and `b`, with
entries `Φ₀ (p i ≫ f ≫ q' j)`. -/
noncomputable def matrix {a b : A} (d : RetractDecomposition P a) (d' : RetractDecomposition P b)
    (f : a ⟶ b) : sumObj Φ₀ d ⟶ sumObj Φ₀ d' :=
  biproduct.matrix fun i j => familyMap Φ₀ (d.p i ≫ f ≫ d'.q j)

/-- The column of a morphism `x : P s ⟶ a` with respect to a decomposition of `a`. -/
noncomputable def column {a : A} (d : RetractDecomposition P a) {s : T} (x : P s ⟶ a) :
    Φ₀.obj s ⟶ sumObj Φ₀ d :=
  biproduct.lift fun j => familyMap Φ₀ (x ≫ d.q j)

/-- The row of a morphism `y : a ⟶ P s` with respect to a decomposition of `a`. -/
noncomputable def row {a : A} (d : RetractDecomposition P a) {s : T} (y : a ⟶ P s) :
    sumObj Φ₀ d ⟶ Φ₀.obj s :=
  biproduct.desc fun i => familyMap Φ₀ (d.p i ≫ y)

/-- Matrices compose like the morphisms they represent. -/
@[reassoc]
lemma matrix_comp {a b c : A} (d : RetractDecomposition P a) (d' : RetractDecomposition P b)
    (d'' : RetractDecomposition P c) (f : a ⟶ b) (g : b ⟶ c) :
    matrix Φ₀ d d' f ≫ matrix Φ₀ d' d'' g = matrix Φ₀ d d'' (f ≫ g) := by
  ext i k
  simp only [matrix, Category.assoc, biproduct.ι_matrix_assoc, biproduct.lift_matrix_assoc,
    biproduct.lift_π]
  have := sum_familyMap_comp Φ₀ d' (d.p k ≫ f) (g ≫ d''.q i)
  simp only [Category.assoc] at this
  rw [this]

/-- A column followed by a matrix is the column of the composite. -/
@[reassoc]
lemma column_matrix {a b : A} (d : RetractDecomposition P a) (d' : RetractDecomposition P b)
    {s : T} (x : P s ⟶ a) (f : a ⟶ b) :
    column Φ₀ d x ≫ matrix Φ₀ d d' f = column Φ₀ d' (x ≫ f) := by
  ext k
  simp only [column, matrix, biproduct.lift_matrix, biproduct.lift_π]
  rw [sum_familyMap_comp Φ₀ d, Category.assoc]

/-- A matrix followed by a row is the row of the composite. -/
lemma matrix_row {a b : A} (d : RetractDecomposition P a) (d' : RetractDecomposition P b)
    (f : a ⟶ b) {s : T} (y : b ⟶ P s) :
    matrix Φ₀ d d' f ≫ row Φ₀ d' y = row Φ₀ d (f ≫ y) := by
  ext i
  simp only [row, matrix, biproduct.matrix_desc, biproduct.ι_desc]
  simp only [← Category.assoc]
  rw [sum_familyMap_comp Φ₀ d']

/-- A column followed by a row is `familyMap` of the composite. -/
lemma column_row {a : A} (d : RetractDecomposition P a) {s s' : T} (x : P s ⟶ a)
    (y : a ⟶ P s') : column Φ₀ d x ≫ row Φ₀ d y = familyMap Φ₀ (x ≫ y) := by
  simp only [column, row, biproduct.lift_desc]
  exact sum_familyMap_comp Φ₀ d x y

omit [Φ₀.Additive] in
/-- A row followed by a column is the matrix of the composite. -/
@[reassoc]
lemma row_column {a b : A} (d : RetractDecomposition P a) (d' : RetractDecomposition P b)
    {s : T} (y : a ⟶ P s) (x : P s ⟶ b) :
    row Φ₀ d y ≫ column Φ₀ d' x = matrix Φ₀ d d' (y ≫ x) := by
  ext i j
  simp [row, column, matrix, ← familyMap_comp]

omit [Φ₀.Additive] in
/-- A row followed by `familyMap g` is the row of the composite. -/
lemma row_familyMap {a : A} (d : RetractDecomposition P a) {s s' : T} (y : a ⟶ P s)
    (g : P s ⟶ P s') : row Φ₀ d y ≫ familyMap Φ₀ g = row Φ₀ d (y ≫ g) := by
  ext i
  simp [row, ← familyMap_comp]

/-- Matrices are additive in the morphism. -/
lemma matrix_add {a b : A} (d : RetractDecomposition P a) (d' : RetractDecomposition P b)
    (f g : a ⟶ b) : matrix Φ₀ d d' (f + g) = matrix Φ₀ d d' f + matrix Φ₀ d d' g := by
  ext i j
  simp [matrix, familyMap_add]

/-- The matrix of the identity is idempotent. -/
lemma matrix_id_idem {a : A} (d : RetractDecomposition P a) :
    matrix Φ₀ d d (𝟙 a) ≫ matrix Φ₀ d d (𝟙 a) = matrix Φ₀ d d (𝟙 a) := by
  rw [matrix_comp, Category.id_comp]

variable [IsIdempotentComplete D]

/-- The idempotent `matrix d d (𝟙 a)` splits in an idempotent complete category. -/
lemma exists_splitting {a : A} (d : RetractDecomposition P a) :
    ∃ (Y : D) (i : Y ⟶ sumObj Φ₀ d) (r : sumObj Φ₀ d ⟶ Y),
      i ≫ r = 𝟙 Y ∧ r ≫ i = matrix Φ₀ d d (𝟙 a) :=
  IsIdempotentComplete.idempotents_split _ _ (matrix_id_idem Φ₀ d)

/-- The value at `a` of the extension: the image of the idempotent `matrix d d (𝟙 a)` for the
chosen decomposition `d` of `a`. -/
noncomputable def extObj (hP : IsDenseFamily P) (a : A) : D :=
  (exists_splitting Φ₀ (hP.decomp a)).choose

/-- The inclusion of `extObj` into the direct sum. -/
noncomputable def extIncl (hP : IsDenseFamily P) (a : A) :
    extObj Φ₀ hP a ⟶ sumObj Φ₀ (hP.decomp a) :=
  (exists_splitting Φ₀ (hP.decomp a)).choose_spec.choose

/-- The projection of the direct sum onto `extObj`. -/
noncomputable def extProj (hP : IsDenseFamily P) (a : A) :
    sumObj Φ₀ (hP.decomp a) ⟶ extObj Φ₀ hP a :=
  (exists_splitting Φ₀ (hP.decomp a)).choose_spec.choose_spec.choose

/-- `extIncl` is a section of `extProj`. -/
@[reassoc (attr := simp)]
lemma extIncl_extProj (hP : IsDenseFamily P) (a : A) :
    extIncl Φ₀ hP a ≫ extProj Φ₀ hP a = 𝟙 _ :=
  (exists_splitting Φ₀ (hP.decomp a)).choose_spec.choose_spec.choose_spec.1

/-- `extProj ≫ extIncl` is the idempotent `matrix d d (𝟙 a)`. -/
@[reassoc]
lemma extProj_extIncl (hP : IsDenseFamily P) (a : A) :
    extProj Φ₀ hP a ≫ extIncl Φ₀ hP a = matrix Φ₀ (hP.decomp a) (hP.decomp a) (𝟙 a) :=
  (exists_splitting Φ₀ (hP.decomp a)).choose_spec.choose_spec.choose_spec.2

/-- The extension of an additive functor `Φ₀` on a dense family `P` to the whole category,
for an idempotent complete target with finite biproducts
(cf. Webster, arXiv:1309.3796v2, Corollary 3.27). -/
noncomputable def extendFunctor (hP : IsDenseFamily P) : A ⥤ D where
  obj a := extObj Φ₀ hP a
  map {a b} f := extIncl Φ₀ hP a ≫ matrix Φ₀ (hP.decomp a) (hP.decomp b) f ≫ extProj Φ₀ hP b
  map_id a := by
    rw [← extProj_extIncl, Category.assoc, extIncl_extProj_assoc, extIncl_extProj]
  map_comp {a b c} f g := by
    rw [Category.assoc, Category.assoc, extProj_extIncl_assoc, matrix_comp_assoc,
      Category.comp_id, matrix_comp_assoc]

/-- The extension on morphisms, as a compressed matrix. -/
lemma extendFunctor_map (hP : IsDenseFamily P) {a b : A} (f : a ⟶ b) :
    (extendFunctor Φ₀ hP).map f =
      extIncl Φ₀ hP a ≫ matrix Φ₀ (hP.decomp a) (hP.decomp b) f ≫ extProj Φ₀ hP b := rfl

/-- The extension of an additive functor is additive. -/
instance (hP : IsDenseFamily P) : (extendFunctor Φ₀ hP).Additive where
  map_add {a b f g} := by
    simp only [extendFunctor_map, matrix_add, add_comp, comp_add]
    rfl

/-- The isomorphism between the value of the extension at `P s` and `Φ₀.obj s`. -/
noncomputable def extendFunctorObjIso (hP : IsDenseFamily P) (s : T) :
    extObj Φ₀ hP (P s) ≅ Φ₀.obj s where
  hom := extIncl Φ₀ hP (P s) ≫ row Φ₀ (hP.decomp (P s)) (𝟙 (P s))
  inv := column Φ₀ (hP.decomp (P s)) (𝟙 (P s)) ≫ extProj Φ₀ hP (P s)
  hom_inv_id := by
    rw [Category.assoc, row_column_assoc, Category.comp_id, ← extProj_extIncl,
      Category.assoc, extIncl_extProj_assoc, extIncl_extProj]
  inv_hom_id := by
    rw [Category.assoc, extProj_extIncl_assoc, column_matrix_assoc, column_row,
      Category.id_comp, Category.id_comp, familyMap_id]

/-- The extension restricts to `Φ₀` on the family. -/
noncomputable def extendFunctorIso (hP : IsDenseFamily P) :
    inducedFunctor P ⋙ extendFunctor Φ₀ hP ≅ Φ₀ :=
  NatIso.ofComponents (fun s => extendFunctorObjIso Φ₀ hP s) fun {s s'} g => by
    change (extIncl Φ₀ hP (P s) ≫ matrix Φ₀ (hP.decomp (P s)) (hP.decomp (P s')) g.hom ≫
        extProj Φ₀ hP (P s')) ≫ extIncl Φ₀ hP (P s') ≫ row Φ₀ (hP.decomp (P s')) (𝟙 (P s')) =
      (extIncl Φ₀ hP (P s) ≫ row Φ₀ (hP.decomp (P s)) (𝟙 (P s))) ≫ familyMap Φ₀ g.hom
    simp only [Category.assoc, extProj_extIncl_assoc, matrix_row,
      row_familyMap, Category.comp_id, Category.id_comp]

/-- Naturality of `extendFunctorObjIso` with respect to morphisms of the family. -/
@[reassoc]
lemma extendFunctor_map_objIso_hom (hP : IsDenseFamily P) {s s' : T} (g : P s ⟶ P s') :
    (extendFunctor Φ₀ hP).map g ≫ (extendFunctorObjIso Φ₀ hP s').hom =
      (extendFunctorObjIso Φ₀ hP s).hom ≫ Φ₀.map (InducedCategory.homMk g) :=
  (extendFunctorIso Φ₀ hP).hom.naturality (InducedCategory.homMk g)

section Linear

variable {k : Type*} [CommRing k] [Linear k A] [Linear k D] [Φ₀.Linear k]

omit [HasFiniteBiproducts D] [IsIdempotentComplete D] [Φ₀.Additive] in
/-- `familyMap` is `k`-linear. -/
lemma familyMap_smul {s s' : T} (c : k) (f : P s ⟶ P s') :
    familyMap Φ₀ (c • f) = c • familyMap Φ₀ f :=
  Functor.map_smul Φ₀ c (InducedCategory.homMk (X := s) (Y := s') f)

omit [IsIdempotentComplete D] [Φ₀.Additive] in
/-- Matrices are `k`-linear in the morphism. -/
lemma matrix_smul {a b : A} (d : RetractDecomposition P a) (d' : RetractDecomposition P b)
    (c : k) (f : a ⟶ b) : matrix Φ₀ d d' (c • f) = c • matrix Φ₀ d d' f := by
  ext i j
  simp [matrix, familyMap_smul]

/-- The extension of a `k`-linear functor is `k`-linear. -/
instance (hP : IsDenseFamily P) : (extendFunctor Φ₀ hP).Linear k where
  map_smul {a b} f c := by
    simp only [extendFunctor_map, matrix_smul, Linear.smul_comp, Linear.comp_smul]
    rfl

end Linear

end ExtendFunctor

end IsDenseFamily

end Categorification.TwoRep
