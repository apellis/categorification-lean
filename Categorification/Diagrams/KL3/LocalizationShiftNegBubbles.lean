/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftFakeBubbles
import Categorification.Diagrams.KL3.LocalizationShiftLayers

/-!
# Honest bubbles with negative dots under the weight shift of `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. The relations `LocRel.cw` and `LocRel.ccw` of `U′` (Webster,
Definition 3.28) identify the honest bubbles with `-(n+1)` dots, built from inverse dots, with
the fake bubbles. Under Webster's hypothesis `a i - b i = -⟨αᵢ^∨, δ⟩` both hold for the images
of the weight shift (`shift_rel_cw`, `shift_rel_ccw`).

The weight shift sends an inverse dot in any position to the inverse dot in the shifted region
(`shiftFree_map_invDot`), so the image of the honest clockwise bubble with `-n` dots is the
bubble `zcw` of `U′` with `-n + ⟨αᵢ^∨, δ⟩` dots (`shiftFree_map_cwNegHonest`); the fake
side is computed by `shiftEnd_cwL`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (δ : X) (a b : I → ℤ)

theorem shiftLayer_invDot (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    shiftLayer RD δ (invDotLayer RD μ u i v) = invDotLayer RD (μ + δ) u i v := by
  refine Layer.ext ?_ ?_ ?_ ?_
  · exact (wt_add_shift RD δ μ _).symm
  · show (wd RD (wt RD μ ([dn i] ++ v)) u).map _ = wd RD (wt RD (μ + δ) ([dn i] ++ v)) u
    rw [wd_shift, wt_add_shift]
  · show Sum.inr (i, wt RD μ v + δ) = Sum.inr (i, wt RD (μ + δ) v)
    rw [wt_add_shift]
  · exact wd_shift RD δ μ v

/-- The image of an inverse dot in any position is the inverse dot in the shifted region. -/
theorem shiftFree_map_invDot (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    (shiftFree RD k δ a b).map (invDot RD μ u i v) =
      eqToHom (shiftFree_obj_ob RD k δ a b μ _) ≫
        (presLoc RD k).diag (invDot RD (μ + δ) u i v) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b μ _).symm := by
  have hls : (Diagram.layers (invDot RD μ u i v)).map (shiftLayer RD δ) =
      Diagram.layers (invDot RD (μ + δ) u i v) := by
    show [shiftLayer RD δ (invDotLayer RD μ u i v)] = [invDotLayer RD (μ + δ) u i v]
    rw [shiftLayer_invDot]
  have hc' : Chain ((shiftMap RD δ).obj ((incl RD).obj (ob RD μ (u ++ [dn i] ++ v))))
      ((Diagram.layers (invDot RD μ u i v)).map (shiftLayer RD δ))
      ((shiftMap RD δ).obj ((incl RD).obj (ob RD μ (u ++ [dn i] ++ v)))) := by
    rw [hls, shiftMap_ob]; exact Diagram.chain _
  have hσ : ∀ L ∈ Diagram.layers (invDot RD μ u i v), ∀ (hv : L.Valid),
      ∃ (hv' : (shiftLayer RD δ L).Valid)
        (e₁ : (shiftLayer RD δ L).dom =
          (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).obj L.dom)
        (e₂ : (shiftLayer RD δ L).cod =
          (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).obj L.cod),
        (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).layer L hv =
          (presLoc RD k).diag (Diagram.layer (shiftLayer RD δ L) hv' e₁ e₂) := by
    intro L hL hv
    have hL' : L = invDotLayer RD μ u i v := List.mem_singleton.mp hL
    subst hL'
    exact shiftFree_layer RD k δ a b _ hv trivial
  refine (LocalMap.functor_map_mk_eq_diag _ (shiftLayer RD δ) _ hσ (Diagram.chain _) hc').trans ?_
  exact (presLoc RD k).diag_eq_of_layers_eq' _ _ (shiftMap_ob RD δ μ _) (shiftMap_ob RD δ μ _) hls

theorem functor_map_iterComp {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟) {x : 𝒞}
    (f : x ⟶ x) (n : ℕ) : F.map (iterComp f n) = iterComp (F.map f) n := by
  induction n with
  | zero => exact F.map_id x
  | succ n ih => rw [iterComp, iterComp, F.map_comp, ih]

theorem iterComp_conj {𝒞 : Type*} [Category 𝒞] {x y : 𝒞} (h : x = y) (g : y ⟶ y) (n : ℕ) :
    iterComp (eqToHom h ≫ g ≫ eqToHom h.symm) n = eqToHom h ≫ iterComp g n ≫ eqToHom h.symm := by
  subst h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The image of the honest clockwise bubble with `-n` dots. -/
theorem shiftFree_map_cwNegHonest (lam : X) (i : I) (n : ℕ) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam []).symm ≫
        (shiftFree RD k δ a b).map (cwNegHonest RD lam i n) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b lam []) =
      zcw (lam + δ) i (b i + (-(n : ℤ) + -a i)) := by
  rw [cwNegHonest, Functor.map_comp, Functor.map_comp, cupEF, capEF, shiftFree_map_mkD,
    shiftFree_map_mkD, functor_map_iterComp, shiftFree_map_invDot, iterComp_conj,
    imgList_eq_zg, imgList_eq_zg, ← zdot_neg_one, ← zdot_neg_nat]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  erw [Category.comp_id]
  rw [List.flatMap_singleton, List.flatMap_singleton]
  erw [zg_cons_self (lam + δ) _ (DStep.lay ([], .cup (up i), [])),
    zg_cons_self (lam + δ) _ (DStep.dot [up i] i [] (-a i)), zg_nil, Category.comp_id,
    zg_cons_self (lam + δ) _ (DStep.dot [up i] i [] (b i)),
    zg_cons_self (lam + δ) _ (DStep.lay ([], .cap (dn i), [])), zg_nil, Category.comp_id]
  simp only [Category.assoc]
  show ldg RD k (lam + δ) [] [up i, dn i] _ ≫ zdot RD k (lam + δ) [up i] i [] (-a i) ≫
    zdot RD k (lam + δ) [up i] i [] (-n) ≫ zdot RD k (lam + δ) [up i] i [] (b i) ≫
      ldg RD k (lam + δ) _ [] _ = _
  rw [← Category.assoc (zdot RD k (lam + δ) [up i] i [] (-a i)), ← zdot_add,
    ← Category.assoc (zdot RD k (lam + δ) [up i] i [] _), ← zdot_add]
  rfl

/-- The image of the honest counterclockwise bubble with `-n` dots. -/
theorem shiftFree_map_ccwNegHonest (lam : X) (i : I) (n : ℕ) :
    eqToHom (shiftFree_obj_ob RD k δ a b lam []).symm ≫
        (shiftFree RD k δ a b).map (ccwNegHonest RD lam i n) ≫
          eqToHom (shiftFree_obj_ob RD k δ a b lam []) =
      zccw (lam + δ) i (a i + (-(n : ℤ) + -b i)) := by
  rw [ccwNegHonest, Functor.map_comp, Functor.map_comp, cupFE, capFE, shiftFree_map_mkD,
    shiftFree_map_mkD, functor_map_iterComp, shiftFree_map_invDot, iterComp_conj,
    imgList_eq_zg, imgList_eq_zg, ← zdot_neg_one, ← zdot_neg_nat]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  erw [Category.comp_id]
  rw [List.flatMap_singleton, List.flatMap_singleton]
  erw [zg_cons_self (lam + δ) _ (DStep.lay ([], .cup (dn i), [])),
    zg_cons_self (lam + δ) _ (DStep.dot [] i [up i] (-b i)), zg_nil, Category.comp_id,
    zg_cons_self (lam + δ) _ (DStep.dot [] i [up i] (a i)),
    zg_cons_self (lam + δ) _ (DStep.lay ([], .cap (up i), [])), zg_nil, Category.comp_id]
  simp only [Category.assoc]
  show ldg RD k (lam + δ) [] [dn i, up i] _ ≫ zdot RD k (lam + δ) [] i [up i] (-b i) ≫
    zdot RD k (lam + δ) [] i [up i] (-n) ≫ zdot RD k (lam + δ) [] i [up i] (a i) ≫
      ldg RD k (lam + δ) _ [] _ = _
  rw [← Category.assoc (zdot RD k (lam + δ) [] i [up i] (-b i)), ← zdot_add,
    ← Category.assoc (zdot RD k (lam + δ) [] i [up i] _), ← zdot_add]
  rfl

theorem freeLift_eq_conj_shiftEnd (lam : X) (f : LEnd RD k (ob RD lam [])) :
    (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k f) =
      eqToHom (shiftFree_obj_ob RD k δ a b lam []) ≫ shiftEnd RD k δ a b lam f ≫
        eqToHom (shiftFree_obj_ob RD k δ a b lam []).symm := by
  rw [shiftEnd_apply]
  simp

theorem freeLift_of_eq_conj {lam : X}
    (f : (incl RD).obj (ob RD lam []) ⟶ (incl RD).obj (ob RD lam []))
    (g : lob RD k (lam + δ) [] ⟶ lob RD k (lam + δ) [])
    (h : eqToHom (shiftFree_obj_ob RD k δ a b lam []).symm ≫ (shiftFree RD k δ a b).map f ≫
          eqToHom (shiftFree_obj_ob RD k δ a b lam []) = g) :
    (freeLift k (shiftFree RD k δ a b)).map (LinDiagram.of f) =
      eqToHom (shiftFree_obj_ob RD k δ a b lam []) ≫ g ≫
        eqToHom (shiftFree_obj_ob RD k δ a b lam []).symm := by
  rw [freeLift_map_of, ← h]
  simp

/-- **The relation identifying honest clockwise bubbles with negative dots and fake bubbles**
holds for the images of the weight shift. -/
theorem shift_rel_cw (hab : ∀ i, a i - b i = -ip RD i δ) (lam : X) (i : I) (n : ℕ) :
    (freeLift k (shiftFree RD k δ a b)).map (locRelation RD k (.cw lam i n)) = 0 := by
  show (freeLift k (shiftFree RD k δ a b)).map (LinDiagram.of (cwNegHonest RD lam i (n + 1)) -
      inclLin RD k (cwL RD k lam i (-((n : ℤ) + 1)))) = 0
  rw [Functor.map_sub, freeLift_eq_conj_shiftEnd, freeLift_of_eq_conj RD k δ a b _ _
    (shiftFree_map_cwNegHonest RD k δ a b lam i (n + 1)), shiftEnd_cwL RD k δ a b hab,
    ← zcw_eq, sub_eq_zero]
  have := hab i
  congr 3
  push_cast
  omega

/-- **The relation identifying honest counterclockwise bubbles with negative dots and fake
bubbles** holds for the images of the weight shift. -/
theorem shift_rel_ccw (hab : ∀ i, a i - b i = -ip RD i δ) (lam : X) (i : I) (n : ℕ) :
    (freeLift k (shiftFree RD k δ a b)).map (locRelation RD k (.ccw lam i n)) = 0 := by
  show (freeLift k (shiftFree RD k δ a b)).map (LinDiagram.of (ccwNegHonest RD lam i (n + 1)) -
      inclLin RD k (ccwL RD k lam i (-((n : ℤ) + 1)))) = 0
  rw [Functor.map_sub, freeLift_eq_conj_shiftEnd, freeLift_of_eq_conj RD k δ a b _ _
    (shiftFree_map_ccwNegHonest RD k δ a b lam i (n + 1)), shiftEnd_ccwL RD k δ a b hab,
    ← zccw_eq, sub_eq_zero]
  have := hab i
  congr 3
  push_cast
  omega

end Categorification.KL3.Diagram
