/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftRelations

/-!
# Dots, crossings and inverse dots under the weight shift of `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30: the weight shift fixes dots, crossings and inverse dots. This file makes this
precise for layers in any position: the weight shift `shiftImg RD k δ a b` sends a layer whose
generator is a dot, a crossing or an inverse dot to the one-layer diagram of the shifted layer
(`shiftLayer`), and hence a diagram all of whose layers are of this kind to the shifted diagram.

## Main results

* `shiftLayer_lay`: the shifted layer of `lay μ u g v` is `lay (μ + δ) u g v`.
* `shiftFree_layer`: the image of a dot, crossing or inverse-dot layer.
* `shiftFree_map_mk`: the image of a diagram all of whose generators are dots, crossings or
  inverse dots.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (δ : X) (a b : I → ℤ)

/-- The generators of `U′` with every region shifted by `δ`. -/
def shiftGen : (lsig RD).Gen → (lsig RD).Gen
  | .inl (.gen (.dot c)) => .inl (.gen (.dot ⟨c.l, c.r + δ⟩))
  | .inl (.gen (.cross ε i j ν)) => .inl (.gen (.cross ε i j (ν + δ)))
  | .inl (.cup c) => .inl (.cup ⟨c.l, c.r + δ⟩)
  | .inl (.cap c) => .inl (.cap ⟨c.l, c.r + δ⟩)
  | .inr p => .inr (p.1, p.2 + δ)

/-- A layer of `U′` with every region shifted by `δ`. -/
def shiftLayer (L : Layer (lsig RD)) : Layer (lsig RD) :=
  ⟨(shiftMap RD δ).region L.start, (shiftMap RD δ).word L.left, shiftGen RD δ L.gen,
    (shiftMap RD δ).word L.right⟩

/-- The generators fixed by the weight shift: dots, crossings and inverse dots. -/
def IsLocalGen : (lsig RD).Gen → Prop
  | .inl (.gen _) => True
  | .inl (.cup _) => False
  | .inl (.cap _) => False
  | .inr _ => True

theorem shiftLayer_lay (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    shiftLayer RD δ ((incl RD).layer (lay RD μ u g v)) = (incl RD).layer (lay RD (μ + δ) u g v) := by
  refine Layer.ext ?_ ?_ ?_ ?_
  · exact (wt_add_shift RD δ μ _).symm
  · show (wd RD (wt RD μ (g.dom ++ v)) u).map _ = wd RD (wt RD (μ + δ) (g.dom ++ v)) u
    rw [wd_shift, wt_add_shift]
  · show shiftGen RD δ (.inl (g.gen RD (wt RD μ v))) = .inl (g.gen RD (wt RD (μ + δ) v))
    rw [wt_add_shift]
    cases g with
    | dot l => rfl
    | cross ε i j => rfl
    | cup l =>
      simp only [Shape.gen, shiftGen, add_assoc]
    | cap l => rfl
  · exact wd_shift RD δ μ v

/-- The one-layer diagram of `U′` of shape `g` with rightmost region `ν`, as a diagram. -/
abbrev lgenD (ν : X) (g : Shape I) :
    (incl RD).obj (ob RD ν g.dom) ⟶ (incl RD).obj (ob RD ν g.cod) :=
  inclD RD (mkD RD ν [([], g, [])] ⟨by simp, by simp⟩)

/-- **The weight shift fixes dots, crossings and inverse dots** (Webster arXiv:1309.3796v2,
Proposition 3.30): the image of such a layer is the one-layer diagram of the shifted layer. -/
theorem shiftFree_layer : ∀ (L : Layer (lsig RD)) (hv : L.Valid), IsLocalGen RD L.gen →
    ∃ (hv' : (shiftLayer RD δ L).Valid) (e₁ : (shiftLayer RD δ L).dom = (shiftMap RD δ).obj L.dom)
      (e₂ : (shiftLayer RD δ L).cod = (shiftMap RD δ).obj L.cod),
      (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).layer L hv =
        (presLoc RD k).diag (Diagram.layer (shiftLayer RD δ L) hv' e₁ e₂)
  | ⟨s, l, .inl (.gen (.dot c)), r⟩, hv, _ =>
    LocalMap.ofGen_layer_eq_single _ _ _ hv (lgenD RD (c.r + δ) (.dot c.l))
      (genDom_dot RD δ c) (genCod_dot RD δ c) rfl _
      (by show [_] = [_]; congr 1; exact Layer.ext rfl (List.append_nil _) rfl rfl)
  | ⟨s, l, .inl (.gen (.cross ε i j ν)), r⟩, hv, _ =>
    LocalMap.ofGen_layer_eq_single _ _ _ hv (lgenD RD (ν + δ) (.cross ε i j))
      (genDom_cross RD δ ε i j ν) (genCod_cross RD δ ε i j ν) rfl _
      (by show [_] = [_]; congr 1; exact Layer.ext rfl (List.append_nil _) rfl rfl)
  | ⟨s, l, .inr p, r⟩, hv, _ =>
    LocalMap.ofGen_layer_eq_single _ _ _ hv (invDotF RD p.1 (p.2 + δ))
      (genDom_inv RD δ p) (genDom_inv RD δ p) rfl _
      (by show [_] = [_]; congr 1; exact Layer.ext rfl (List.append_nil _) rfl rfl)

/-- The image of a diagram of `R(ν)` placed on upward strands is the same diagram in the shifted
region (Webster arXiv:1309.3796v2, Proposition 3.30). -/
theorem shiftFree_map_upDiag (μ : X) {p q : Obj (KLR.Diagram.sig I)} (d : p ⟶ q) :
    (shiftFree RD k δ a b).map (inclD RD (upDiag RD μ d)) =
      eqToHom (shiftFree_obj_ob RD k δ a b μ _) ≫
        (presLoc RD k).diag (inclD RD (upDiag RD (μ + δ) d)) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b μ _).symm := by
  have hls : (Diagram.layers (inclD RD (upDiag RD μ d))).map (shiftLayer RD δ) =
      Diagram.layers (inclD RD (upDiag RD (μ + δ) d)) := by
    simp only [LayerMap.layers_map, layers_upDiag, List.map_map]
    refine List.map_congr_left fun L _ => ?_
    exact shiftLayer_lay RD δ μ _ _ _
  have hc' : Chain ((shiftMap RD δ).obj ((incl RD).obj (ob RD μ (ups p.word))))
      ((Diagram.layers (inclD RD (upDiag RD μ d))).map (shiftLayer RD δ))
      ((shiftMap RD δ).obj ((incl RD).obj (ob RD μ (ups q.word)))) := by
    rw [hls, shiftMap_ob, shiftMap_ob]; exact Diagram.chain _
  have hσ : ∀ L ∈ Diagram.layers (inclD RD (upDiag RD μ d)), ∀ (hv : L.Valid),
      ∃ (hv' : (shiftLayer RD δ L).Valid)
        (e₁ : (shiftLayer RD δ L).dom = (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).obj L.dom)
        (e₂ : (shiftLayer RD δ L).cod = (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).obj L.cod),
        (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).layer L hv =
          (presLoc RD k).diag (Diagram.layer (shiftLayer RD δ L) hv' e₁ e₂) := by
    intro L hL hv
    simp only [LayerMap.layers_map, layers_upDiag, List.map_map, List.mem_map] at hL
    obtain ⟨⟨s, l, g, r⟩, -, rfl⟩ := hL
    exact shiftFree_layer RD k δ a b _ hv (by cases g <;> trivial)
  refine (LocalMap.functor_map_mk_eq_diag _ (shiftLayer RD δ) _ hσ (Diagram.chain _) hc').trans ?_
  exact (presLoc RD k).diag_eq_of_layers_eq' _ _ (shiftMap_ob RD δ μ _) (shiftMap_ob RD δ μ _) hls

/-- The image of a multiple of a diagram of `R(ν)` on upward strands. -/
theorem shiftFree_freeLift_single (μ : X) {p q : Obj (KLR.Diagram.sig I)} (d : p ⟶ q) (r : k) :
    (freeLift k (shiftFree RD k δ a b)).map
        (inclLin RD k (upLin RD k μ (Finsupp.single d r : LinDiagram k p q))) =
      eqToHom (shiftFree_obj_ob RD k δ a b μ _) ≫
        (presLoc RD k).lin (inclLin RD k (upLin RD k (μ + δ) (Finsupp.single d r))) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b μ _).symm := by
  have e : ∀ ν : X, inclLin RD k (upLin RD k ν (Finsupp.single d r : LinDiagram k p q)) =
      (Finsupp.single (inclD RD (upDiag RD ν d)) r : LinDiagram k _ _) := fun ν => by
    rw [upLin, Finsupp.mapDomain_single]
    exact Finsupp.mapDomain_single
  rw [e, e, freeLift_map_single, Presentation.lin_single, shiftFree_map_upDiag]
  simp only [Linear.smul_comp, Linear.comp_smul]

/-- The image of a linear combination of diagrams of `R(ν)` on upward strands. -/
theorem shiftFree_freeLift_upLin (μ : X) {p q : Obj (KLR.Diagram.sig I)} (f : LinDiagram k p q) :
    (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k (upLin RD k μ f)) =
      eqToHom (shiftFree_obj_ob RD k δ a b μ _) ≫
        (presLoc RD k).lin (inclLin RD k (upLin RD k (μ + δ) f)) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b μ _).symm := by
  induction f using Finsupp.induction_linear with
  | zero =>
    simp only [upLin, Finsupp.mapDomain_zero, map_zero, Functor.map_zero, Presentation.lin_zero,
      Limits.zero_comp, Limits.comp_zero]
  | add f g hf hg =>
    simp only [upLin, Finsupp.mapDomain_add, map_add, Functor.map_add, Presentation.lin_add,
      Preadditive.add_comp, Preadditive.comp_add] at hf hg ⊢
    rw [hf, hg]
  | single d r => exact shiftFree_freeLift_single RD k δ a b μ d r

/-- **The KLR relations of `U′` hold for the images of the weight shift** (Webster
arXiv:1309.3796v2, Proposition 3.30). -/
theorem shift_rel_klr (μ : X) (r : KLR.Diagram.Rel I) :
    (freeLift k (shiftFree RD k δ a b)).map
      (inclLin RD k (relation (RD := RD) k (.klr μ r))) = 0 := by
  have h : (presLoc RD k).lin (inclLin RD k (upLin RD k (μ + δ)
      (KLR.Diagram.relation k (KLR.klQ2 k C) r))) = 0 :=
    (presLoc RD k).lin_rel_self (.inl (.inr (.klr (μ + δ) r)))
  refine (shiftFree_freeLift_upLin RD k δ a b μ _).trans ?_
  rw [h]
  simp only [Limits.zero_comp, Limits.comp_zero]

end Categorification.KL3.Diagram
