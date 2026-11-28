/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Standardly stratified categories (Losev–Webster, Definition 2.1)

I. Losev, B. Webster, *On uniqueness of tensor products of irreducible categorifications*,
arXiv:1303.1336v3, §2.1.

## Standing assumptions (`IsFiniteBlockCategory`)

`C` is an abelian `k`-linear category whose blocks are each equivalent to the category of
finite-dimensional modules over a finite-dimensional `k`-algebra, and every simple object has
endomorphism algebra `k`. A block decomposition is encoded as a family of pairwise orthogonal
Serre subcategories, each equivalent to finitely generated modules over a finite-dimensional
algebra, such that every object is a finite direct sum of objects of the pieces; the pieces may
be coarser than the blocks (a finite-dimensional algebra is the product of its blocks), so this
is the same condition.

## Definition 2.1 (`StandardStratification`)

The data are a labelling `Λ` of the simple objects (`SimpleLabelling`), a poset `Ξ` with finite
upper and lower intervals and a map `ρ : Λ → Ξ` with finite fibres. For `ξ ∈ Ξ` the Serre
subcategories `C_{≤ξ}`, `C_{<ξ}` are spanned by the simples `L(λ)` with `ρ(λ) ≤ ξ`, resp.
`ρ(λ) < ξ` (`SimpleLabelling.le`, `SimpleLabelling.lt`): an object lies in them when each of
its simple subquotients does. The quotient `C_ξ = C_{≤ξ}/C_{<ξ}` is any localization
`π_ξ : C_{≤ξ} ⥤ C_ξ` at the morphisms that are isomorphisms modulo `C_{<ξ}` (Mathlib's
`ObjectProperty.isoModSerre`). The structure asks for an exact left adjoint `Δ_ξ` of `π_ξ`
(the standardization functor), and, for every label `λ`, an epimorphism from the projective
cover `P(λ)` onto the standard object `Δ(λ) = Δ_{ρ(λ)}(P_{ρ(λ)}(λ))` whose kernel has a finite
filtration with subquotients `Δ(μ)`, `ρ(μ) > ρ(λ)`.

Exactness of the left adjoint `Δ_ξ` (which is right exact) is stated as preservation of
monomorphisms. The Serre-class property of `C_{≤ξ}` and `C_{<ξ}` holds in every category of
finite length; it is a field (`le_isSerreClass`, `lt_isSerreClass`) so that the localization can
be stated.
-/

namespace Categorification.TensorProductCategorification

open CategoryTheory Limits

universe w v u v' u'

section Basic

variable {C : Type u} [Category.{v} C]

/-- A Serre class is closed under binary products (they are split extensions). -/
instance _root_.CategoryTheory.ObjectProperty.isClosedUnderBinaryProducts_of_isSerreClass
    [Abelian C] (P : ObjectProperty C) [P.IsSerreClass] : P.IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine P.prop_of_iso ?_ (P.prop_biprod (p.prop_diag_obj (.mk .left))
      (p.prop_diag_obj (.mk .right)))
    exact IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

/-- A Serre class is closed under finite products. -/
instance _root_.CategoryTheory.ObjectProperty.isClosedUnderFiniteProducts_of_isSerreClass
    [Abelian C] (P : ObjectProperty C) [P.IsSerreClass] : P.IsClosedUnderFiniteProducts :=
  .mk'

/-- A **projective cover** `p : P ⟶ X`: `P` is projective, `p` is an epimorphism, and `p` is
essential (a morphism `f` into `P` is an epimorphism as soon as `f ≫ p` is). -/
structure IsProjectiveCover {P X : C} (p : P ⟶ X) : Prop where
  projective : Projective P
  epi : Epi p
  essential : ∀ {Y : C} (f : Y ⟶ P), Epi (f ≫ p) → Epi f

variable [Abelian C]

/-- `L` is a **simple subquotient** of `X`: `L` is simple and isomorphic to `B/A` for
subobjects `A ≤ B` of `X`. -/
def IsSimpleSubquotient (L X : C) : Prop :=
  Simple L ∧ ∃ (A B : Subobject X) (h : A ≤ B), Nonempty (cokernel (Subobject.ofLE A B h) ≅ L)

/-- The objects all of whose simple subquotients satisfy `S`: in a category of finite length,
the Serre subcategory spanned by the simple objects satisfying `S`. -/
def spannedBy (S : ObjectProperty C) : ObjectProperty C :=
  fun X => ∀ L, IsSimpleSubquotient L X → S L

/-- `X` has a finite filtration whose successive subquotients satisfy `S`. -/
inductive HasFiltration (S : ObjectProperty C) : C → Prop
  | zero {X : C} : IsZero X → HasFiltration S X
  | extension {X : C} (T : ShortComplex C) : T.ShortExact → HasFiltration S T.X₁ → S T.X₃ →
      Nonempty (T.X₂ ≅ X) → HasFiltration S X

end Basic

section Blocks

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C] [Abelian C] [Linear k C]

/-- Finitely generated modules over `A`; for a finite-dimensional algebra these are the
finite-dimensional modules. -/
abbrev FGModuleCat (A : Type v) [Ring A] :=
  ObjectProperty.FullSubcategory (C := ModuleCat.{v} A) fun M => Module.Finite A M

/-- **The standing assumptions of Losev–Webster §2.1**: every block of `C` is equivalent to the
category of finite-dimensional modules over a finite-dimensional `k`-algebra, and every simple
object is absolutely simple (its endomorphisms are `k`). See the module docstring for the
encoding of the block decomposition. -/
structure IsFiniteBlockCategory : Prop where
  exists_blocks : ∃ (β : Type u) (P : β → ObjectProperty C),
    (∀ b, (P b).IsSerreClass) ∧
    (∀ b b', b ≠ b' → ∀ (X Y : C), P b X → P b' Y → ∀ f : X ⟶ Y, f = 0) ∧
    (∀ X : C, ∃ (s : Finset β) (Y : s → C), (∀ b, P b.1 (Y b)) ∧ Nonempty (X ≅ ∐ Y)) ∧
    ∀ b, ∃ (A : Type v) (_ : Ring A) (_ : Algebra k A), FiniteDimensional k A ∧
      Nonempty ((P b).FullSubcategory ≌ FGModuleCat A)
  finrank_end_simple : ∀ L : C, Simple L → Module.finrank k (L ⟶ L) = 1

end Blocks

section Stratification

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- **A labelling of the simple objects** by a set `Λ`, with a map `ρ` to a poset `Ξ` whose upper
and lower intervals are finite and whose fibres are finite (Losev–Webster §2.1). -/
structure SimpleLabelling (Ξ : Type w) [PartialOrder Ξ] where
  /-- The labels. -/
  Λ : Type w
  /-- The simple object `L(λ)`. -/
  simple : Λ → C
  isSimple : ∀ l, Simple (simple l)
  exists_iso : ∀ X : C, Simple X → ∃ l, Nonempty (X ≅ simple l)
  eq_of_iso : ∀ l l', Nonempty (simple l ≅ simple l') → l = l'
  /-- The map `ρ : Λ → Ξ`. -/
  ρ : Λ → Ξ
  finite_fibre : ∀ ξ : Ξ, (ρ ⁻¹' {ξ}).Finite
  finite_gt : ∀ ξ : Ξ, {ξ' | ξ < ξ'}.Finite
  finite_lt : ∀ ξ : Ξ, {ξ' | ξ' < ξ}.Finite

namespace SimpleLabelling

variable {C} {Ξ : Type w} [PartialOrder Ξ] (σ : SimpleLabelling C Ξ)

/-- The Serre subcategory `C_{≤ξ}` spanned by the `L(λ)` with `ρ(λ) ≤ ξ`. -/
def le (ξ : Ξ) : ObjectProperty C :=
  spannedBy fun L => ∃ l, σ.ρ l ≤ ξ ∧ Nonempty (L ≅ σ.simple l)

/-- The Serre subcategory `C_{<ξ}` spanned by the `L(λ)` with `ρ(λ) < ξ`. -/
def lt (ξ : Ξ) : ObjectProperty C :=
  spannedBy fun L => ∃ l, σ.ρ l < ξ ∧ Nonempty (L ≅ σ.simple l)

/-- `C_{<ξ}` as a property of objects of `C_{≤ξ}`. -/
def ltIn (ξ : Ξ) : ObjectProperty (σ.le ξ).FullSubcategory :=
  fun X => σ.lt ξ X.obj

/-- A simple subquotient of a simple object is isomorphic to it. -/
theorem _root_.Categorification.TensorProductCategorification.IsSimpleSubquotient.of_simple
    {L X : C} [Simple X] (h : IsSimpleSubquotient L X) : Nonempty (L ≅ X) := by
  obtain ⟨hL, A, B, hAB, ⟨e⟩⟩ := h
  have hord := (simple_iff_subobject_isSimpleOrder X).mp inferInstance
  have hz : ∀ (A B : Subobject X) (hAB : A ≤ B), A = B →
      IsZero (cokernel (Subobject.ofLE A B hAB)) := by
    rintro A B hAB rfl
    rw [Subobject.ofLE_refl]
    exact isZero_cokernel_of_epi _
  rcases hord.eq_bot_or_eq_top A with rfl | rfl
  · rcases hord.eq_bot_or_eq_top B with rfl | rfl
    · exact absurd (hz ⊥ ⊥ hAB rfl |>.of_iso e.symm) (Simple.not_isZero L)
    · have h0 : Subobject.ofLE ⊥ ⊤ hAB = 0 :=
        (IsZero.of_iso (isZero_zero C) Subobject.botCoeIsoZero).eq_of_src _ _
      exact ⟨e.symm ≪≫ (cokernelIsoOfEq h0) ≪≫ cokernelZeroIsoTarget ≪≫
        (Subobject.underlyingIso (𝟙 X))⟩
  · have hB : B = ⊤ := top_le_iff.mp hAB
    subst hB
    exact absurd (hz ⊤ ⊤ hAB rfl |>.of_iso e.symm) (Simple.not_isZero L)

/-- `L(λ)` lies in `C_{≤ρ(λ)}`. -/
theorem le_simple (l : σ.Λ) : σ.le (σ.ρ l) (σ.simple l) := by
  intro L hL
  have := σ.isSimple l
  exact ⟨l, le_rfl, hL.of_simple⟩

end SimpleLabelling

variable {C} {Ξ : Type w} [PartialOrder Ξ]

/-- **A standardly stratified structure** (Losev–Webster, arXiv:1303.1336v3, Definition 2.1) on
`C` for the labelling `σ`: localizations `π_ξ : C_{≤ξ} ⥤ C_ξ` at the morphisms that are
isomorphisms modulo `C_{<ξ}`, exact left adjoints `Δ_ξ` (standardization), projective covers
`P(λ)` in `C` and `P_ξ(λ)` of `π_ξ L(λ)` in `C_ξ`, and for every `λ` an epimorphism
`P(λ) ⟶ Δ(λ)` whose kernel is filtered by standard objects `Δ(μ)` with `ρ(λ) < ρ(μ)`.
The Serre-class instances of `C_{≤ξ}` and of `C_{<ξ} ⊆ C_{≤ξ}` (automatic in a category of
finite length) are parameters, so that the localization can be stated. -/
structure StandardStratification (σ : SimpleLabelling C Ξ) [∀ ξ, (σ.le ξ).IsSerreClass]
    [∀ ξ, (σ.ltIn ξ).IsSerreClass] where
  /-- The subquotient category `C_ξ`. -/
  Sub : Ξ → Type u'
  [cat : ∀ ξ, Category.{v'} (Sub ξ)]
  /-- The quotient functor `π_ξ : C_{≤ξ} ⥤ C_ξ`. -/
  π : ∀ ξ, (σ.le ξ).FullSubcategory ⥤ Sub ξ
  isLocalization : ∀ ξ, (π ξ).IsLocalization (σ.ltIn ξ).isoModSerre
  /-- The standardization functor `Δ_ξ`. -/
  Δ : ∀ ξ, Sub ξ ⥤ (σ.le ξ).FullSubcategory
  adj : ∀ ξ, Δ ξ ⊣ π ξ
  /-- `Δ_ξ` is exact (it is right exact as a left adjoint). -/
  preservesMono : ∀ ξ, (Δ ξ).PreservesMonomorphisms
  /-- The projective cover `P(λ) ⟶ L(λ)` in `C`. -/
  proj : σ.Λ → C
  projCover : ∀ l, proj l ⟶ σ.simple l
  isProjectiveCover : ∀ l, IsProjectiveCover (projCover l)
  /-- The projective cover `P_ξ(λ) ⟶ π_ξ L(λ)` in `C_ξ`, `ξ = ρ(λ)`. -/
  subProj : ∀ l, Sub (σ.ρ l)
  subProjCover : ∀ l, subProj l ⟶ (π (σ.ρ l)).obj ⟨σ.simple l, σ.le_simple l⟩
  isSubProjectiveCover : ∀ l, IsProjectiveCover (subProjCover l)
  /-- The condition on projectives: an epimorphism `P(λ) ⟶ Δ(λ)` with kernel filtered by
  standard objects of strictly larger labels. -/
  exists_epi : ∀ l, ∃ f : proj l ⟶ ((Δ (σ.ρ l)).obj (subProj l)).obj, Epi f ∧
    HasFiltration (fun X => ∃ l', σ.ρ l < σ.ρ l' ∧
      Nonempty (X ≅ ((Δ (σ.ρ l')).obj (subProj l')).obj)) (kernel f)

attribute [instance] StandardStratification.cat

namespace StandardStratification

variable {σ : SimpleLabelling C Ξ} [∀ ξ, (σ.le ξ).IsSerreClass] [∀ ξ, (σ.ltIn ξ).IsSerreClass]
  (S : StandardStratification.{w, v, u, v', u'} σ)

/-- The standard object `Δ(λ) = Δ_{ρ(λ)}(P_{ρ(λ)}(λ))`. -/
def standard (l : σ.Λ) : C := ((S.Δ (σ.ρ l)).obj (S.subProj l)).obj

/-- The proper standard object `Δ̄(λ) = Δ_{ρ(λ)}(L_{ρ(λ)}(λ))`. -/
def properStandard (l : σ.Λ) : C :=
  ((S.Δ (σ.ρ l)).obj ((S.π (σ.ρ l)).obj ⟨σ.simple l, σ.le_simple l⟩)).obj

end StandardStratification


end Stratification

end Categorification.TensorProductCategorification
