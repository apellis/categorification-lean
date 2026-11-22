/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShift
import Categorification.Diagrams.KL3.LocalizationShiftLemmas

/-!
# Relations for the weight shifts of `U′` (towards Webster, Proposition 3.30)

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. This file checks relations of the presentation `presLoc` of `U′` under the
weight shift `shiftImg RD k δ a b` of `Categorification.Diagrams.KL3.LocalizationShift`.

## Main results

* `shiftFunctorFree_map_invDotF`, `shiftFunctorFree_map_downDot`: the images of the inverse
  downward dot and of the downward dot are the same generators in the shifted region.
* `shift_rel_invLeft`, `shift_rel_invRight`: the relations `y⁻¹ y = 1`, `y y⁻¹ = 1` of `U′`
  hold for the images (for all `δ`, `a`, `b`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (δ : X) (a b : I → ℤ)

/-- The functor on the free 2-category of `U′` given by the weight shift. -/
abbrev shiftFree : Obj (lsig RD) ⥤ (presLoc RD k).Presented :=
  (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).functor

theorem shiftFree_obj_ob (μ : X) (t : List (Letter I)) :
    (shiftFree RD k δ a b).obj ((incl RD).obj (ob RD μ t)) = lob RD k (μ + δ) t :=
  congrArg (presLoc RD k).obj (shiftMap_ob RD δ μ t)

/-- The image of the inverse downward dot is the inverse downward dot in the shifted region. -/
theorem shiftFree_map_invDotF (i : I) (μ : X) :
    (shiftFree RD k δ a b).map (invDotF RD i μ) =
      eqToHom (shiftFree_obj_ob RD k δ a b μ [dn i]) ≫
        (presLoc RD k).diag (invDotF RD i (μ + δ)) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b μ [dn i]).symm := by
  refine (LocalMap.functor_map_single (shiftMap RD δ) (shiftImg RD k δ a b)
    (invDotLayer RD μ [] i []) _ rfl rfl (genDom_inv RD δ (i, μ) |>.trans
      (shiftMap_ob RD δ μ [dn i]).symm |>.symm) (genDom_inv RD δ (i, μ) |>.trans
      (shiftMap_ob RD δ μ [dn i]).symm |>.symm)).trans ?_
  show _ ≫ (eqToHom _ ≫ (presLoc RD k).diag (invDotF RD i (μ + δ)) ≫ eqToHom _) ≫ eqToHom _ = _
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- The image of the downward dot is the downward dot in the shifted region. -/
theorem shiftFree_map_downDot (i : I) (μ : X) :
    (shiftFree RD k δ a b).map (inclD RD (downDot RD i μ)) =
      eqToHom (shiftFree_obj_ob RD k δ a b μ [dn i]) ≫
        (presLoc RD k).diag (inclD RD (downDot RD i (μ + δ))) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b μ [dn i]).symm := by
  refine (LocalMap.functor_map_single (shiftMap RD δ) (shiftImg RD k δ a b)
    ((incl RD).layer (lay RD μ [] (.dot (dn i)) [])) _ rfl rfl
      (genDom_dot RD δ ⟨dn i, μ⟩ |>.trans (shiftMap_ob RD δ μ [dn i]).symm |>.symm)
      (genCod_dot RD δ ⟨dn i, μ⟩ |>.trans (shiftMap_ob RD δ μ [dn i]).symm |>.symm)).trans ?_
  show _ ≫ (eqToHom _ ≫ lgen RD k (μ + δ) (.dot (dn i)) ≫ eqToHom _) ≫ eqToHom _ = _
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

/-- **The relation `y⁻¹ y = 1`** holds for the images of the weight shift. -/
theorem shift_rel_invLeft (i : I) (μ : X) :
    (freeLift k (shiftFree RD k δ a b)).map (locRelation RD k (.invLeft i μ)) = 0 := by
  have e : locRelation RD k (.invLeft i μ) =
      (LinDiagram.of (invDotF RD i μ ≫ inclD RD (downDot RD i μ)) - 𝟙 _ :
        LinDiagram k ((incl RD).obj (ob RD μ [dn i])) ((incl RD).obj (ob RD μ [dn i]))) := rfl
  rw [e]
  simp only [Functor.map_sub, freeLift_map_of]
  rw [show (freeLift k (shiftFree RD k δ a b)).map (𝟙 (Free.of k ((incl RD).obj (ob RD μ [dn i])))) = 𝟙 _
    from (freeLift k _).map_id _]
  rw [(shiftFree RD k δ a b).map_comp,
    shiftFree_map_invDotF, shiftFree_map_downDot]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc ((presLoc RD k).diag _), invDot_comp_downDot]
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]
  exact sub_self _

/-- **The relation `y y⁻¹ = 1`** holds for the images of the weight shift. -/
theorem shift_rel_invRight (i : I) (μ : X) :
    (freeLift k (shiftFree RD k δ a b)).map (locRelation RD k (.invRight i μ)) = 0 := by
  have e : locRelation RD k (.invRight i μ) =
      (LinDiagram.of (inclD RD (downDot RD i μ) ≫ invDotF RD i μ) - 𝟙 _ :
        LinDiagram k ((incl RD).obj (ob RD μ [dn i])) ((incl RD).obj (ob RD μ [dn i]))) := rfl
  rw [e]
  simp only [Functor.map_sub, freeLift_map_of]
  rw [show (freeLift k (shiftFree RD k δ a b)).map (𝟙 (Free.of k ((incl RD).obj (ob RD μ [dn i])))) = 𝟙 _
    from (freeLift k _).map_id _]
  rw [(shiftFree RD k δ a b).map_comp,
    shiftFree_map_invDotF, shiftFree_map_downDot]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc ((presLoc RD k).diag _), downDot_comp_invDot]
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]
  exact sub_self _

end Categorification.KL3.Diagram
