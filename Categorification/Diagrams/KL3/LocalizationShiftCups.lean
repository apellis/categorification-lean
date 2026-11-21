/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftImage

/-!
# Cup layers under the weight shift of `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. Supporting lemmas for the image of a cup layer under the weight shift
`shiftImg RD k δ a b`: the image of a cup layer in structural form (`ofGen_layer_cup`), the
shifted boundaries of a normal-form layer, and the dots `cupDecAt` on the downward leg of a cup
placed between strands.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (δ : X) (a b : I → ℤ)

theorem whisk_conj {a a' b b' : Obj (lsig RD)} (ha : a = a') (hb : b = b')
    (f : (presLoc RD k).obj a' ⟶ (presLoc RD k).obj b') (U : Obj (lsig RD))
    (V : List (lsig RD).Colour) :
    (presLoc RD k).whisk (eqToHom (congrArg (presLoc RD k).obj ha) ≫ f ≫
        eqToHom (congrArg (presLoc RD k).obj hb).symm) U V =
      eqToHom (congrArg (presLoc RD k).obj (congrArg (fun x => Obj.whisker x U V) ha)) ≫
        (presLoc RD k).whisk f U V ≫
          eqToHom (congrArg (presLoc RD k).obj (congrArg (fun x => Obj.whisker x U V) hb)).symm := by
  subst ha hb; simp

theorem genCod_whiskerOK {S S' : Signature} (κ : ColourMap S S') {L : Layer S} (hv : L.Valid) :
    (LocalMap.genCod κ L.gen).WhiskerOK (κ.obj ⟨L.start, L.left⟩) (κ.word L.right) := by
  refine ⟨κ.ok_map hv.left_ok, ?_, ?_⟩
  · show S'.endR (κ.region L.start) (κ.word L.left) = κ.region (S.left L.gen)
    rw [κ.endR_map, hv.left_end]
  · show S'.ok (S'.endR (κ.region (S.left L.gen)) (κ.word (S.cod L.gen))) _
    rw [κ.endR_map, hv.cod_end]; exact κ.ok_map hv.right_ok

/-- The dots `y^{-a_i}`, resp. `y^{-b_i}`, on the downward leg of a cup `l l*` placed between
the strands `u` and `v`. -/
def cupDecAt (ν : X) (u : List (Letter I)) :
    (l : Letter I) → (v : List (Letter I)) →
      (lob RD k ν (u ++ [l, l.dual] ++ v) ⟶ lob RD k ν (u ++ [l, l.dual] ++ v))
  | (true, i), v => eqToHom (congrArg (lob RD k ν) (by simp)) ≫
      zdot RD k ν (u ++ [up i]) i v (-a i) ≫ eqToHom (congrArg (lob RD k ν) (by simp))
  | (false, i), v => eqToHom (congrArg (lob RD k ν) (by simp)) ≫
      zdot RD k ν u i ([up i] ++ v) (-b i) ≫ eqToHom (congrArg (lob RD k ν) (by simp))

theorem shift_lay_dom (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    (shiftMap RD δ).obj ((incl RD).layer (lay RD μ u g v)).dom =
      (incl RD).obj (ob RD (μ + δ) (u ++ g.dom ++ v)) :=
  (congrArg (shiftMap RD δ).obj (((incl RD).toLayerMap.dom_eq (lay_valid RD μ u g v)).trans
    (congrArg (incl RD).obj (lay_dom RD μ u g v)))).trans (shiftMap_ob RD δ μ _)

theorem shift_lay_cod (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    (shiftMap RD δ).obj ((incl RD).layer (lay RD μ u g v)).cod =
      (incl RD).obj (ob RD (μ + δ) (u ++ g.cod ++ v)) :=
  (congrArg (shiftMap RD δ).obj (((incl RD).toLayerMap.cod_eq (lay_valid RD μ u g v)).trans
    (congrArg (incl RD).obj (lay_cod RD μ u g v)))).trans (shiftMap_ob RD δ μ _)

theorem ofGen_layer_cup (s : X) (l' : List (Col I X)) (c : Col I X) (r : List (Col I X))
    (hv : (⟨s, l', .inl (.cup c), r⟩ : Layer (lsig RD)).Valid) :
    (LocalMap.ofGen (shiftMap RD δ) (shiftImg RD k δ a b)).layer _ hv =
      eqToHom (congrArg (presLoc RD k).obj
          ((congrArg (fun x => Obj.whisker x _ _) (genDom_cup RD δ c)).symm.trans
            (LocalMap.whisker_genDom (shiftMap RD δ) ⟨s, l', .inl (.cup c), r⟩))).symm ≫
        (presLoc RD k).whisk (cupImg RD k a b c.l (sh RD c.l + c.r + δ))
          ((shiftMap RD δ).obj ⟨s, l'⟩) ((shiftMap RD δ).word r) ≫
        eqToHom (congrArg (presLoc RD k).obj
          ((congrArg (fun x => Obj.whisker x _ _) (genCod_cup RD δ c)).symm.trans
            (LocalMap.whisker_genCod (shiftMap RD δ) ⟨s, l', .inl (.cup c), r⟩))) := by
  rw [LocalMap.ofGen_layer]
  show _ ≫ (presLoc RD k).whisk (eqToHom _ ≫ _ ≫ eqToHom _) _ _ ≫ _ = _
  rw [whisk_conj RD k (genDom_cup RD δ c) (genCod_cup RD δ c)]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

theorem shift_lay_left (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    (shiftMap RD δ).obj ⟨((incl RD).layer (lay RD μ u g v)).start,
      ((incl RD).layer (lay RD μ u g v)).left⟩ =
      (incl RD).obj (ob RD (wt RD (wt RD (μ + δ) v) g.dom) u) := by
  refine Obj.ext ?_ ?_
  · show wt RD μ (u ++ g.dom ++ v) + δ = wt RD (wt RD (wt RD (μ + δ) v) g.dom) u
    simp only [List.append_assoc, wt_append, wt_add_shift]
  · show (wd RD (wt RD μ (g.dom ++ v)) u).map _ = wd RD (wt RD (wt RD (μ + δ) v) g.dom) u
    rw [wt_add_shift, wt_add_shift, ← wd_shift, wt_append]

theorem shift_lay_right (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    (shiftMap RD δ).word ((incl RD).layer (lay RD μ u g v)).right = wd RD (μ + δ) v :=
  wd_shift RD δ μ v

end Categorification.KL3.Diagram
