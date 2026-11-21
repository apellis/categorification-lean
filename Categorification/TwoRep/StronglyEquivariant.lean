/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
import Categorification.TwoRep.LinearCat

/-!
# Strongly equivariant functors between module categories

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §3.5,
**Definition 3.23**.

A module category over a 2-category `𝒰` is here a pseudofunctor `ℵ : 𝒰 ⥤ LinearCat k` (for the
Cautis–Lauda 2-category, `𝒰 = RevBicat (presCL RD k S).Bicat`, as for the actions of
`Categorification.KLR.CyclotomicAction.PresCL`). Webster defines a strongly equivariant functor
`β : ℵ₁ → ℵ₂` as a family of functors `β(λ) : ℵ₁(λ) → ℵ₂(λ)` with natural isomorphisms
`c_u : β ∘ ℵ₁(u) ≅ ℵ₂(u) ∘ β` for every 1-morphism `u`, such that
`c_v ∘ (id_β ⊗ ℵ₁(α)) = (ℵ₂(α) ⊗ id_β) ∘ c_u` for every 2-morphism `α : u → v`.

This is a strong transformation of pseudofunctors (`Pseudofunctor.StrongTrans`), whose fields
are `β(λ)` (`app`), `c_u` (`naturality`) and Webster's condition (`naturality_naturality`;
in components, `StronglyEquivariant.webster_condition`). Mathlib's strong transformations have
two further axioms, compatibility of `c` with the unit and composition constraints
(`naturality_id`, `naturality_comp`): `c_{𝟙} = id` and `c_{uv}` is the composite of `c_u` and
`c_v`. Webster's printed definition leaves these out; they are part of Rouquier's notion of a
morphism of 2-representations (arXiv:0812.5023, §5.1.2), which is the one Webster's universality
statement refers to (Corollary 3.27, "unique up to unique isomorphism"), and they are what makes
the strongly equivariant functors the 1-morphisms of a bicategory. We use the definition with
these axioms.

A morphism of strongly equivariant functors is a modification (`Pseudofunctor.StrongTrans.Modification`),
the 2-morphisms in "unique up to unique isomorphism".
-/

namespace Categorification.TwoRep

open CategoryTheory Bicategory

universe w v u w₁ v₁ u₁

variable {k : Type w} [CommRing k] {B : Type u₁} [Bicategory.{w₁, v₁} B]

/-- **Strongly equivariant functors** (Webster, arXiv:1309.3796v2, Definition 3.23, with the
unit and composition axioms of Rouquier, see the module docstring): strong transformations
between module categories `ℵ₁ ℵ₂ : B ⥤ LinearCat k`. -/
abbrev StronglyEquivariant (ℵ₁ ℵ₂ : Pseudofunctor B (LinearCat.{w, v, u} k)) :=
  Pseudofunctor.StrongTrans ℵ₁ ℵ₂

namespace StronglyEquivariant

variable {ℵ₁ ℵ₂ : Pseudofunctor B (LinearCat.{w, v, u} k)} (β : StronglyEquivariant ℵ₁ ℵ₂)

/-- The functor `β(λ) : ℵ₁(λ) → ℵ₂(λ)`. -/
def functor (a : B) : ℵ₁.obj a ⥤ ℵ₂.obj a := (β.app a).obj

/-- Webster's natural isomorphism `c_u : β ∘ ℵ₁(u) ≅ ℵ₂(u) ∘ β` (in diagrammatic order,
`ℵ₁(u) ⋙ β(b) ≅ β(a) ⋙ ℵ₂(u)`). -/
def iso {a b : B} (f : a ⟶ b) :
    (ℵ₁.map f).obj ⋙ β.functor b ≅ β.functor a ⋙ (ℵ₂.map f).obj :=
  (ObjectProperty.ι _).mapIso (β.naturality f)

/-- **Webster's condition** of Definition 3.23, in components: for a 2-morphism `α : u → v` and
an object `X` of `ℵ₁(a)`, `c_v ∘ β(ℵ₁(α)) = ℵ₂(α) ∘ c_u` at `X`. -/
theorem webster_condition {a b : B} {f g : a ⟶ b} (α : f ⟶ g) (X : ℵ₁.obj a) :
    (β.functor b).map ((ℵ₁.map₂ α).hom.app X) ≫ (β.iso g).hom.app X =
      (β.iso f).hom.app X ≫ (ℵ₂.map₂ α).hom.app ((β.functor a).obj X) := by
  have h := congrArg (fun θ => θ.hom.app X) (β.naturality_naturality α)
  exact h

end StronglyEquivariant

end Categorification.TwoRep
