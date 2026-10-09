/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.ModelSl2

/-!
# Homogeneity of interpretations in the graded-Hom bicategory

For an interpretation of a free 2-category (`Categorification.Diagrams.BicatInterp`) in the
graded-Hom bicategory `K^•` of a graded bicategory `B`, the image of a diagram is homogeneous of
degree the sum of the degrees of its generators, provided the image of each generator occurring
in it is homogeneous of the given degree. The structural 2-morphisms (images of 2-morphisms of the
free bicategory: associators, unitors and their whiskerings) are homogeneous of degree `0`.

## Main results

* `isHomogeneous_lift_map₂`: images of free 2-morphisms are homogeneous of degree `0`;
* `isHomogeneous_layerI`, `isHomogeneous_mapChain`, `isHomogeneous_interp_map`.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory StringDiagrams
open GradedHomBicat GradedHomCat Diagrams.BicatInterp

universe w v u u₀ u₁ u₂

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, HasShift (a ⟶ b) ℤ] [GradedBicategory B] [GradedBicategory.ShiftCoherence B]

theorem isHomogeneous_eqToHom {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] {X Y : GradedHomCat C} (h : X = Y) :
    IsHomogeneous (eqToHom h) 0 := by
  subst h; exact isHomogeneous_id _

/-- **Structural 2-morphisms are homogeneous of degree `0`**: the image of a 2-morphism of a free
bicategory under the lift of a prefunctor to the graded-Hom bicategory. -/
theorem isHomogeneous_lift_map₂ {Q : Type*} [Quiver Q] (F : Prefunctor Q (GradedHomBicat B))
    {a b : FreeBicategory Q} {f g : a ⟶ b} (η : f ⟶ g) :
    IsHomogeneous ((FreeBicategory.lift F).map₂ η) 0 := by
  induction η using Quot.ind with
  | mk η =>
    show IsHomogeneous (FreeBicategory.liftHom₂ F η) 0
    induction η with
    | id => exact isHomogeneous_id _
    | vcomp η θ ih₁ ih₂ => exact ih₁.comp ih₂ (by simp)
    | whisker_left f η ih => exact isHomogeneous_whiskerLeft _ ih
    | whisker_right h η ih => exact isHomogeneous_whiskerRight ih _
    | associator => exact isHomogeneous_associator_hom _ _ _
    | associator_inv => exact isHomogeneous_associator_inv _ _ _
    | right_unitor => exact isHomogeneous_rightUnitor_hom _
    | right_unitor_inv => exact isHomogeneous_rightUnitor_inv _
    | left_unitor => exact isHomogeneous_leftUnitor_hom _
    | left_unitor_inv => exact isHomogeneous_leftUnitor_inv _

variable [∀ a b : B, HasZeroObject (a ⟶ b)]
variable {S : Signature.{u₀, u₁, u₂}} {M : Model S (GradedHomBicat B)} (G : GenImg M)
  (δ : S.Gen → ℤ)

/-- The image of each generator `g` (at any regions) is homogeneous of degree `δ g`. -/
def GenHomogeneous (g : S.Gen) : Prop :=
  ∀ (a b : S.Region) (ha : S.left g = a) (hb : S.right g = b) (hd : S.ok a (S.dom g))
    (hde : S.endR a (S.dom g) = b) (hc : S.ok a (S.cod g)) (hce : S.endR a (S.cod g) = b),
    IsHomogeneous (G.gen g a b ha hb hd hde hc hce) (δ g)

variable {G δ}

omit [∀ a b : B, HasZeroObject (a ⟶ b)] in
theorem isHomogeneous_core {L : Layer S} (hv : L.Valid) (hL : GenHomogeneous G δ L.gen)
    (s m n t : S.Region) (hl : S.ok s L.left) (hm : S.endR s L.left = m) (ha : S.left L.gen = m)
    (hb : S.right L.gen = n) (ht : S.endR n L.right = t) :
    IsHomogeneous (core G hv s m n t hl hm ha hb ht) (δ L.gen) := by
  unfold core
  refine ((isHomogeneous_lift_map₂ _ _).comp
    ((isHomogeneous_whiskerLeft _ (isHomogeneous_whiskerRight (hL _ _ _ _ _ _ _ _) _)).comp
      (isHomogeneous_lift_map₂ _ _) rfl) (by simp))

variable (s₀ t₀ : S.Region)

theorem isHomogeneous_layerI (L : Layer S) (hv : L.Valid) (hL : GenHomogeneous G δ L.gen) :
    IsHomogeneous (layerI G s₀ t₀ L hv) (δ L.gen) := by
  unfold layerI
  split_ifs with h
  · exact (isHomogeneous_eqToHom _).comp ((isHomogeneous_core hv hL _ _ _ _ _ _ _ _ _).comp
      (isHomogeneous_eqToHom _) (zero_add _)) (add_zero _)
  · exact isHomogeneous_zero _

theorem isHomogeneous_mapChain :
    ∀ (a : Obj S) (ls : List (Layer S)) (b : Obj S) (h : Chain a ls b),
      (∀ L ∈ ls, GenHomogeneous G δ L.gen) →
      IsHomogeneous ((interp G s₀ t₀).mapChain a ls b h) (ls.map fun L => δ L.gen).sum
  | _, [], _, h, _ => isHomogeneous_eqToHom _
  | _, L :: ls, b, h, hls => by
    refine (isHomogeneous_eqToHom _).comp ((isHomogeneous_layerI s₀ t₀ L h.1
      (hls L List.mem_cons_self)).comp (isHomogeneous_mapChain L.cod ls b h.2.2
        (fun L' hL' => hls L' (List.mem_cons_of_mem _ hL'))) rfl) ?_
    simp [add_comm]

/-- **The image of a diagram is homogeneous** of degree the sum of the degrees of its
generators. -/
theorem isHomogeneous_interp_map {a b : Obj S} (d : a ⟶ b)
    (hd : ∀ L ∈ Diagram.layers d, GenHomogeneous G δ L.gen) :
    IsHomogeneous ((interp G s₀ t₀).functor.map d) ((Diagram.layers d).map fun L => δ L.gen).sum :=
  isHomogeneous_mapChain s₀ t₀ _ _ _ _ hd

end Categorification.TwoRep
