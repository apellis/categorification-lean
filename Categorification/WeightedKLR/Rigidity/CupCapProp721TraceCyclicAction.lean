/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.StrictMate
import Categorification.TwoRep.CyclicTrace
import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
import Categorification.Diagrams.RevBicat
import StringDiagrams.Biadjunction.Basic

/-!
# Cyclic 2-morphisms under a strict pseudofunctor to `Cat`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Theorem 4.28
and Theorem 4.31, as used in §7.3, proof of Proposition 7.21. The action of the 2-morphisms of
`U` on the double tensor product algebras is a strict pseudofunctor to `Cat`; both halves of the
biadjunction `𝔈_i ⊣⊢ 𝔉_i` on modules come from the biadjunction of `U` through it. This file
records that the pseudofunctor carries a cyclic 2-morphism (`TwoRep.IsCyclic`: its conjugates
along the two adjunctions agree) to a natural transformation that is cyclic for the image
adjunctions of functors (`CupCap.isCyclic_map_ofCat`). This is the form of the hypothesis of
`KLR.Diagram.MatEnd.resIndTrace_cyclic`, the symmetry of the trace of Theorem 4.31.

## Main results

* `CupCap.map₂_conjugateEquiv`: a strict pseudofunctor commutes with conjugates.
* `CupCap.isCyclic_map_ofCat`: images of cyclic 2-morphisms are cyclic for the image
  adjunctions, in functor form.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open CategoryTheory CategoryTheory.Bicategory Categorification.Diagrams.BicatInterp

universe w₃ w₄ v₃ v u

variable {B : Type w₃} [Bicategory.{w₄, v₃} B] (Φ : StrictPseudofunctor B Cat.{v, u})

/-- **A strict pseudofunctor commutes with conjugates**: the image of the conjugate of `α` along
`adj₁`, `adj₂` is the conjugate of the image of `α` along the image adjunctions. -/
theorem map₂_conjugateEquiv {a b : B} {l₁ l₂ : a ⟶ b} {r₁ r₂ : b ⟶ a} (adj₁ : l₁ ⊣ r₁)
    (adj₂ : l₂ ⊣ r₂) (α : l₂ ⟶ l₁) :
    Φ.map₂ (conjugateEquiv adj₁ adj₂ α) =
      conjugateEquiv (Φ.mapAdjunction adj₁) (Φ.mapAdjunction adj₂) (Φ.map₂ α) := by
  have h := sp_map₂_conjugateEquiv_symm Φ adj₁ adj₂ (conjugateEquiv adj₁ adj₂ α)
  rw [Equiv.symm_apply_apply] at h
  rw [h, Equiv.apply_symm_apply]

/-- **Images of cyclic 2-morphisms are cyclic** (Webster, arXiv:1309.3796v3, Theorem 4.28): if
`α : l ⟶ l` is cyclic for `A : l ⊣ r` and `A' : r ⊣ l`, then the natural transformation
`Φ α` is cyclic for the adjunctions of functors `Φ l ⊣ Φ r` and `Φ r ⊣ Φ l`. -/
theorem isCyclic_map_ofCat {a b : B} {l : a ⟶ b} {r : b ⟶ a} (A : l ⊣ r) (A' : r ⊣ l)
    (α : l ⟶ l) (hα : TwoRep.IsCyclic A A' A A' α) :
    CategoryTheory.conjugateEquiv (Adjunction.ofCat (Φ.mapAdjunction A'))
        (Adjunction.ofCat (Φ.mapAdjunction A'))
        (CategoryTheory.conjugateEquiv (Adjunction.ofCat (Φ.mapAdjunction A))
          (Adjunction.ofCat (Φ.mapAdjunction A)) (Φ.map₂ α).toNatTrans) =
      (Φ.map₂ α).toNatTrans := by
  rw [← Bicategory.toNatTrans_conjugateEquiv, ← Bicategory.toNatTrans_conjugateEquiv,
    ← map₂_conjugateEquiv, ← map₂_conjugateEquiv]
  exact congrArg (fun x => (Φ.map₂ x).toNatTrans) hα

section Rev

variable {x y : B}

theorem conjugate_rev_aux {f₁ f₂ : x ⟶ y} {g₁ g₂ : y ⟶ x} (A₁ : f₁ ⊣ g₁) (A₂ : f₂ ⊣ g₂)
    (α : g₂ ⟶ g₁) :
    (λ_ f₁).inv ≫ A₂.unit ▷ f₁ ≫ (f₂ ◁ α) ▷ f₁ ≫ (α_ f₂ g₁ f₁).hom ≫ f₂ ◁ A₁.counit ≫
        (ρ_ f₂).hom =
      (λ_ f₁).inv ≫ A₂.unit ▷ f₁ ≫ (α_ f₂ g₂ f₁).hom ≫ f₂ ◁ α ▷ f₁ ≫ f₂ ◁ A₁.counit ≫
        (ρ_ f₂).hom := by
  bicategory

/-- **Conjugates in the 1-cell dual**: the conjugate along `RevBicat.adjunction A₁`,
`RevBicat.adjunction A₂` is the inverse conjugate along `A₂`, `A₁` in `B`. -/
theorem conjugateEquiv_revAdjunction {f₁ f₂ : x ⟶ y} {g₁ g₂ : y ⟶ x} (A₁ : f₁ ⊣ g₁)
    (A₂ : f₂ ⊣ g₂) (α : g₂ ⟶ g₁) :
    conjugateEquiv (RevBicat.adjunction A₁) (RevBicat.adjunction A₂) α =
      (conjugateEquiv A₂ A₁).symm α := by
  rw [conjugateEquiv_apply', conjugateEquiv_symm_apply']
  exact conjugate_rev_aux A₁ A₂ α

open StringDiagrams in
/-- **Cyclic 2-morphisms of a biadjunction are cyclic in the 1-cell dual**: if `α : f ⟶ f` is
cyclic for the biadjunction `P : f ⊣⊢ g` (its right and left mates agree), then it is cyclic in
`RevBicat B` for the adjunctions `f ⊣ g` and `g ⊣ f` read there from `P.right` and `P.left`. -/
theorem isCyclic_rev_of_biadjunction {f : x ⟶ y} {g : y ⟶ x} (P : Biadjunction f g) (α : f ⟶ f)
    (hα : Biadjunction.IsCyclic P P α) :
    TwoRep.IsCyclic (B := RevBicat B) (RevBicat.adjunction P.right) (RevBicat.adjunction P.left)
      (RevBicat.adjunction P.right) (RevBicat.adjunction P.left) α := by
  unfold TwoRep.IsCyclic
  rw [conjugateEquiv_revAdjunction, conjugateEquiv_revAdjunction, Equiv.symm_apply_eq]
  exact hα.symm

end Rev

end Categorification.Stendhal.CupCap
