/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftLayers

/-!
# Images of normal-form diagrams under the weight shift of `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. The weight shift `shiftImg RD k δ a b` sends a dot or a crossing to the same
generator in the shifted region, and a cup or a cap to the shifted cup or cap with dots
`y^{∓a_i}`, `y^{∓b_i}` (integer powers, `zdot`) on its downward leg. This file computes the image
of a normal-form diagram `mkD μ ls` layer by layer.

## Main results

* `whisk_zdot`: placing integer powers of the downward dot between strands.
* `shiftFree_layer_cup`, `shiftFree_layer_cap`: the image of a cup or cap layer at any position.
* `shiftFree_map_mkD`: the image of `inclD (mkD μ ls h)` is the composite `imgList (μ + δ) ls h`
  of the images of its layers.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace StringDiagrams.Presentation

open CategoryTheory

variable {S : Signature} {R : Type*} [CommRing R] (Q : Presentation S R)

theorem whisk_eqToHom_of_ok {a b : Obj S} (h : a = b) (u : Obj S) (v : List S.Colour)
    (hw : a.WhiskerOK u v) :
    Q.whisk (eqToHom (congrArg Q.obj h)) u v =
      eqToHom (congrArg Q.obj (congrArg (fun x => Obj.whisker x u v) h)) := by
  subst h
  exact Q.whisk_id a u v hw

end StringDiagrams.Presentation

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

/-- Whiskering an endomorphism and transporting along an identification of the whiskered object
is multiplicative. -/
def whiskHom {a a' : Obj (lsig RD)} (U : Obj (lsig RD)) (V : List (lsig RD).Colour)
    (hw : a.WhiskerOK U V) (ho : a.whisker U V = a') :
    End ((presLoc RD k).obj a) →* End ((presLoc RD k).obj a') where
  toFun f := eqToHom (congrArg (presLoc RD k).obj ho).symm ≫ (presLoc RD k).whisk f U V ≫
    eqToHom (congrArg (presLoc RD k).obj ho)
  map_one' := by
    show _ ≫ (presLoc RD k).whisk (𝟙 _) U V ≫ _ = 𝟙 _
    rw [(presLoc RD k).whisk_id _ _ _ hw]; simp
  map_mul' f g := by
    simp only [End.mul_def, (presLoc RD k).whisk_comp, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]

/-- **Placing integer powers of the downward dot**: whiskering `n ∈ ℤ` dots on the strand `F_i`
is `n` dots on the corresponding strand of the whiskered object. -/
theorem whisk_zdot (ν : X) (u₀ : List (Letter I)) (i : I) (v₀ : List (Letter I)) (n : ℤ)
    (U : Obj (lsig RD)) (V : List (lsig RD).Colour)
    (hw : ((incl RD).obj (ob RD ν (u₀ ++ [dn i] ++ v₀))).WhiskerOK U V)
    (μ : X) (u v : List (Letter I))
    (ho : ((incl RD).obj (ob RD ν (u₀ ++ [dn i] ++ v₀))).whisker U V =
      (incl RD).obj (ob RD μ (u ++ [dn i] ++ v)))
    (hl : ((incl RD).layer (lay RD ν u₀ (.dot (dn i)) v₀)).whisker U V =
      (incl RD).layer (lay RD μ u (.dot (dn i)) v)) :
    (presLoc RD k).whisk (zdot RD k ν u₀ i v₀ n) U V =
      eqToHom (congrArg (presLoc RD k).obj ho) ≫ zdot RD k μ u i v n ≫
        eqToHom (congrArg (presLoc RD k).obj ho).symm := by
  let Φ := whiskHom RD k U V hw ho
  have h1 : Units.map Φ (dotUnit RD k ν u₀ i v₀) = dotUnit RD k μ u i v := by
    refine Units.ext ?_
    show eqToHom _ ≫ (presLoc RD k).whisk (ldot RD k ν u₀ i v₀) U V ≫ eqToHom _ = ldot RD k μ u i v
    rw [ldot, (presLoc RD k).whisk_diag _ _ _ hw,
      (presLoc RD k).diag_eq_of_layers_eq' _ (inclD RD (mkD RD μ [(u, .dot (dn i), v)] ⟨rfl, rfl⟩))
        ho ho]
    · simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        eqToHom_trans, Category.comp_id]
      rfl
    · show [((incl RD).layer (lay RD ν u₀ (.dot (dn i)) v₀)).whisker U V] =
        [(incl RD).layer (lay RD μ u (.dot (dn i)) v)]
      rw [hl]
  have h2 : Φ (zdot RD k ν u₀ i v₀ n) = zdot RD k μ u i v n := by
    rw [zdot, zdot, ← Units.coe_map, map_zpow, h1]
  have h3 := congrArg (fun f => eqToHom (congrArg (presLoc RD k).obj ho) ≫ f ≫
    eqToHom (congrArg (presLoc RD k).obj ho).symm) h2
  simp only [Φ, whiskHom, MonoidHom.coe_mk, OneHom.coe_mk, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id, eqToHom_trans_assoc, Category.id_comp] at h3
  exact h3

end Categorification.KL3.Diagram
