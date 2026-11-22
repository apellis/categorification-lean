/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Diagrams.KL3.LocalizationCore

/-!
# Placement of 2-morphisms of `U′` between strands

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Lemma 3.29. A 2-morphism `E_s 1_ν ⟶ E_t 1_ν` of the localization `U′` (`ν = μ + v_X`) is placed
between the strands `u` and `v` by whiskering (`plcLoc`). Placement is compatible with
composition and identities, hence with inverses, and the localization functor intertwines it
with the placement `plcL` of `U`.

## Main results

* `plcLoc`: placement in `U′`.
* `plcLoc_comp`, `plcLoc_id`, `plcLoc_inv`: compatibility with composition, identities and
  inverses.
* `toLoc_plcL`: the localization of a placed 2-morphism of `U` is the placed localization.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

theorem incl_ob_whisker (μ : X) (u v s s' : List (Letter I))
    (h : wt RD (wt RD μ v) s' = wt RD (wt RD μ v) s) :
    (incl RD).obj (ob RD μ (u ++ s' ++ v)) =
      ((incl RD).obj (ob RD (wt RD μ v) s')).whisker
        ((incl RD).obj (ob RD (wt RD (wt RD μ v) s) u)) ((incl RD).word (wd RD μ v)) :=
  (congrArg (incl RD).obj (ob_whisker RD μ u v s s' h).symm).trans ((incl RD).obj_whisker _ _ _)

/-- **Placement in `U′`**: a 2-morphism `E_s 1_ν ⟶ E_t 1_ν` of `U′` (`ν = μ + v_X`) placed
between the strands `u` and `v`; the rightmost region becomes `μ`. -/
def plcLoc (μ : X) (u v : List (Letter I)) {s t : List (Letter I)}
    (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s)
    (f : (presLoc RD k).obj ((incl RD).obj (ob RD (wt RD μ v) s)) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD (wt RD μ v) t))) :
    (presLoc RD k).obj ((incl RD).obj (ob RD μ (u ++ s ++ v))) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD μ (u ++ t ++ v))) :=
  eqToHom (congrArg (presLoc RD k).obj (incl_ob_whisker RD μ u v s s rfl)) ≫
    (presLoc RD k).whisk f ((incl RD).obj (ob RD (wt RD (wt RD μ v) s) u))
      ((incl RD).word (wd RD μ v)) ≫
    eqToHom (congrArg (presLoc RD k).obj (incl_ob_whisker RD μ u v s t hst).symm)

theorem toLoc_plcL (μ : X) (u v s t : List (Letter I))
    (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s)
    (f : (pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t)) :
    (toLoc RD k).map (plcL RD k μ u v s t f) = plcLoc RD k μ u v hst ((toLoc RD k).map f) := by
  rw [plcL, dite_eq_left hst]
  simp only [plc, LinearMap.coe_mk, AddHom.coe_mk, Functor.map_comp, eqToHom_map]
  unfold toLoc
  rw [SigMap.lift_whisk _ _ _ _ (whiskerOK_ob RD μ u v s)]
  simp only [plcLoc, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

theorem locWhisk_congr_left {a b : Obj (lsig RD)}
    (f : (presLoc RD k).obj a ⟶ (presLoc RD k).obj b) {U U' : Obj (lsig RD)}
    (V : List (lsig RD).Colour) (h : U = U') :
    (presLoc RD k).whisk f U V =
      eqToHom (by rw [h]) ≫ (presLoc RD k).whisk f U' V ≫ eqToHom (by rw [h]) := by
  subst h; simp

/-- Placement in `U′` is compatible with composition. -/
theorem plcLoc_comp (μ : X) (u v : List (Letter I)) {s r t : List (Letter I)}
    (hsr : wt RD (wt RD μ v) r = wt RD (wt RD μ v) s)
    (hrt : wt RD (wt RD μ v) t = wt RD (wt RD μ v) r)
    (f : (presLoc RD k).obj ((incl RD).obj (ob RD (wt RD μ v) s)) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD (wt RD μ v) r)))
    (g : (presLoc RD k).obj ((incl RD).obj (ob RD (wt RD μ v) r)) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD (wt RD μ v) t))) :
    plcLoc RD k μ u v hsr f ≫ plcLoc RD k μ u v hrt g =
      plcLoc RD k μ u v (hrt.trans hsr) (f ≫ g) := by
  simp only [plcLoc, Presentation.whisk_comp]
  rw [locWhisk_congr_left RD k g ((incl RD).word (wd RD μ v))
    (show (incl RD).obj (ob RD (wt RD (wt RD μ v) r) u) =
      (incl RD).obj (ob RD (wt RD (wt RD μ v) s) u) by rw [hsr])]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans]

/-- Placement in `U′` preserves identities. -/
theorem plcLoc_id (μ : X) (u v s : List (Letter I)) :
    plcLoc RD k μ u v (s := s) (t := s) rfl (𝟙 _) = 𝟙 _ := by
  rw [plcLoc, Presentation.whisk_id _ _ _ _ ((incl RD).whiskerOK (whiskerOK_ob RD μ u v s))]
  simp

/-- Placement in `U′` preserves isomorphisms. -/
instance isIso_plcLoc (μ : X) (u v s : List (Letter I))
    (f : (presLoc RD k).obj ((incl RD).obj (ob RD (wt RD μ v) s)) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD (wt RD μ v) s))) [IsIso f] :
    IsIso (plcLoc RD k μ u v rfl f) :=
  ⟨⟨plcLoc RD k μ u v rfl (CategoryTheory.inv f), by
    rw [plcLoc_comp, IsIso.hom_inv_id]; exact plcLoc_id RD k μ u v s, by
    rw [plcLoc_comp, IsIso.inv_hom_id]; exact plcLoc_id RD k μ u v s⟩⟩

/-- Placement in `U′` preserves inverses of endomorphisms. -/
theorem plcLoc_inv (μ : X) (u v s : List (Letter I))
    (f : (presLoc RD k).obj ((incl RD).obj (ob RD (wt RD μ v) s)) ⟶
      (presLoc RD k).obj ((incl RD).obj (ob RD (wt RD μ v) s))) [IsIso f] :
    plcLoc RD k μ u v rfl (CategoryTheory.inv f) =
      CategoryTheory.inv (plcLoc RD k μ u v rfl f) := by
  refine (IsIso.eq_inv_of_hom_inv_id ?_)
  rw [plcLoc_comp, IsIso.hom_inv_id]; exact plcLoc_id RD k μ u v s

end Categorification.KL3.Diagram
