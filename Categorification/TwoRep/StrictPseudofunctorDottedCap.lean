/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.AdjointPositive
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!
# Dotted caps and cups under strict pseudofunctors

The summands of Rouquier's maps (Brundan, arXiv:1501.00350v1, (1.8) and (1.9)) are a counit
after powers of an endomorphism of the right adjoint's partner (`R ◁ x^m ≫ ε`, a dotted cap)
and a unit followed by such powers (`η ≫ x^m ▷ R`, a dotted cup). A strict pseudofunctor sends
them to the dotted caps and cups built from the image adjunction, up to the equalities of the
images of composites and identities.

* `sp_map₂_powComp`: a strict pseudofunctor commutes with powers of an endomorphism.
* `sp_map₂_dottedCap`, `sp_map₂_dottedCup`: the images of the dotted cap and cup.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory Bicategory

universe w₁ w₂ w₃ w₄ v₂ v₃

variable {C' : Type w₃} [Bicategory.{w₄, v₃} C'] {C : Type w₁} [Bicategory.{w₂, v₂} C]
  (Φ : StrictPseudofunctor C' C) {a b : C'}

/-- A strict pseudofunctor sends powers of an endomorphism to powers of its image. -/
theorem sp_map₂_powComp {f : a ⟶ b} (x : f ⟶ f) (m : ℕ) :
    Φ.map₂ (powComp x m) = powComp (Φ.map₂ x) m := by
  induction m with
  | zero => exact Φ.map₂_id f
  | succ m ih => rw [powComp_succ, powComp_succ, Φ.map₂_comp, ih]

/-- **The image of a dotted cap** `R ◁ x^m ≫ ε` under a strict pseudofunctor is the dotted cap
of the image adjunction, framed by the equalities `map_comp` and `map_id`. -/
theorem sp_map₂_dottedCap {E : a ⟶ b} {R : b ⟶ a} (adj : E ⊣ R) (x : E ⟶ E) (m : ℕ) :
    Φ.map₂ (R ◁ powComp x m ≫ adj.counit) =
      eqToHom (Φ.map_comp R E) ≫
        (Φ.map R ◁ powComp (Φ.map₂ x) m ≫ (Φ.mapAdjunction adj).counit) ≫
          eqToHom (Φ.map_id b).symm := by
  rw [StrictPseudofunctor.mapAdjunction_counit', Φ.map₂_comp,
    Φ.toPseudofunctor.map₂_whisker_left, sp_map₂_powComp]
  have e₁ := Φ.mapComp_eq_eqToIso R E
  rw [e₁]
  simp

/-- **The image of a dotted cup** `η ≫ x^m ▷ R` under a strict pseudofunctor is the dotted cup
of the image adjunction, framed by the equalities `map_id` and `map_comp`. -/
theorem sp_map₂_dottedCup {E : a ⟶ b} {R : b ⟶ a} (adj : E ⊣ R) (x : E ⟶ E) (m : ℕ) :
    Φ.map₂ (adj.unit ≫ powComp x m ▷ R) =
      eqToHom (Φ.map_id a) ≫
        ((Φ.mapAdjunction adj).unit ≫ powComp (Φ.map₂ x) m ▷ Φ.map R) ≫
          eqToHom (Φ.map_comp E R).symm := by
  rw [StrictPseudofunctor.mapAdjunction_unit', Φ.map₂_comp,
    Φ.toPseudofunctor.map₂_whisker_right, sp_map₂_powComp]
  have e₁ := Φ.mapComp_eq_eqToIso E R
  rw [e₁]
  simp

end Categorification.TwoRep
