/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.CyclicDown

/-!
# Cyclicity of the same-colour crossings of `U_Q(g)`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Definition 1.1 (`eq_almost_cyclic`): the rotations of the upward crossing
`E_j E_i ⟶ E_i E_j` by cups on the right and caps on the left, and by cups on the left and caps
on the right, are `t_{ij}` and `t_{ji}` times the downward crossing. For `i = j` the two scalars
agree, so the same-colour crossings are cyclic for the biadjunctions given by the nested cups
and caps, as in KL III (M. Khovanov, A. Lauda, arXiv:0807.3250v1, eq. `eq_cyclic_cross-gen`,
`Categorification.Diagrams.KL3.Cyclic`). The downward crossing is `t_{ii}⁻¹` times the right
mate of the upward one.

The layer computations of the rotations are stated separately
(`CLQ.layers_rightRotate_upcross_same`, …); they do not depend on the relations.

## Main results

* `CLQ.diag_rotCrossR_same_eq_rotCrossL`, `CLQ.diag_rotCrossR_same_eq_smul`.
* `CLQ.upcross_same_isCyclic`, `CLQ.downcross_same_isCyclic`: the same-colour upward and
  downward crossings of `CLQ.pres RD k S` are cyclic.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Biadjunction

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (S : CL.CLScalars C k)

set_option hygiene false in
/-- The presentation `U_Q(g)` with `r = 1`. -/
local notation "PQ" => pres RD k S
set_option hygiene false in
local notation "piv" => (inv RD).toColourDuality.pivotal
set_option hygiene false in
local notation "Wup" => [⟨up i, sh RD (up i) + ν⟩, ⟨up i, ν⟩]
set_option hygiene false in
local notation "Wdn" => [⟨dn i, sh RD (dn i) + (sh RD (up i) + (sh RD (up i) + ν))⟩,
  ⟨dn i, sh RD (up i) + (sh RD (up i) + ν)⟩]
set_option hygiene false in
local notation "gUp" => PivotalGen.gen (Gen0.cross true i i ν)
set_option hygiene false in
local notation "gDn" => PivotalGen.gen (Gen0.cross false i i (sh RD (up i) + (sh RD (up i) + ν)))

/-- In `U_Q(g)` the two rotations of the same-colour upward crossing agree: both are `t_{ii}`
times the downward crossing (CL Definition 1.1, `eq_almost_cyclic`). -/
theorem diag_rotCrossR_same_eq_rotCrossL (i : I) (μ : X) :
    (PQ).diag (rotCrossR RD i i μ) = (PQ).diag (rotCrossL RD i i μ) := by
  have hR := (PQ).lin_rel_self (.inr (.cycCrossR i i μ))
  have hL := (PQ).lin_rel_self (.inr (.cycCrossL i i μ))
  change (PQ).lin ((((S.withRone.t i i)⁻¹ : kˣ) : k) •
    LinDiagram.of (rotCrossR RD i i μ) - LinDiagram.of (downCross RD i i μ)) = 0 at hR
  change (PQ).lin ((((S.withRone.t i i)⁻¹ : kˣ) : k) •
    LinDiagram.of (rotCrossL RD i i μ) - LinDiagram.of (downCross RD i i μ)) = 0 at hL
  rw [lin_sub, lin_smul, lin_of, lin_of, sub_eq_zero] at hR hL
  have h := congrArg (fun d => ((S.withRone.t i i : kˣ) : k) • d) (hR.trans hL.symm)
  simpa only [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul] using h

abbrev dualUpWordObj (i : I) (ν : X) : Obj (psig RD) :=
  ⟨ν, [⟨dn i, sh RD (up i) + ν⟩, ⟨dn i, sh RD (up i) + (sh RD (up i) + ν)⟩]⟩

theorem layers_rightRotate_upcross_same (i : I) (ν : X)
    (hg : (psig RD).GenValid (.gen (.cross true i i ν))) :
    List.map (fun x => Layer.wl (dualUpWordObj RD i ν) x)
          (cupLayers (E := (inv RD)) ((psig RD).left (gUp))
            Wup) ++
        List.map (fun x => Layer.wl (dualUpWordObj RD i ν) x)
          (List.map (fun x => x.wr (dualUpWordObj RD i ν).word)
            (Diagram.layers (genDiag (gUp) hg))) ++
      List.map (fun x => x.wr (dualUpWordObj RD i ν).word)
        (capLayers (E := (inv RD)) ((psig RD).right (gUp))
          Wup) =
    Diagram.layers (rotCrossR RD i i (sh RD (up i) + (sh RD (up i) + ν))) := by
  simp only [genDiag, cupLayers, capLayers, Diagram.layers_layer, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.append_nil, Layer.wl, Layer.wr,
    rotCrossR, layers_mkD, layList, lay]
  simp only [wt_cons, wt_nil, wd_cons, wd_nil, Shape.dom_cup, Shape.dom_cap, Shape.dom_cross,
    List.cons_append, List.nil_append, Letter.dual_mk, Bool.not_true,
    Shape.gen, inv_dual, Signature.ColourDuality.dualWord_cons,
    Signature.ColourDuality.dualWord_nil, Signature.ColourDuality.pivotal_dual,
    psig_right_cross]
  region_tac

theorem layers_leftRotate_upcross_same (i : I) (ν : X)
    (hg : (psig RD).GenValid (.gen (.cross true i i ν))) :
    List.map (fun x => x.wr (dualUpWordObj RD i ν).word)
          (cupRLayers (E := (inv RD)) ((psig RD).right (gUp))
            Wup) ++
        List.map (fun x => Layer.wl (dualUpWordObj RD i ν) x)
          (List.map (fun x => x.wr (dualUpWordObj RD i ν).word)
            (Diagram.layers (genDiag (gUp) hg))) ++
      List.map (fun x => Layer.wl (dualUpWordObj RD i ν) x)
        (capRLayers (E := (inv RD)) ((psig RD).left (gUp))
          Wup) =
    Diagram.layers (rotCrossL RD i i (sh RD (up i) + (sh RD (up i) + ν))) := by
  simp only [genDiag, cupRLayers, capRLayers, Diagram.layers_layer, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.append_nil, Layer.wl, Layer.wr,
    rotCrossL, layers_mkD, layList, lay]
  simp only [wt_cons, wt_nil, wd_cons, wd_nil, Shape.dom_cup, Shape.dom_cap, Shape.dom_cross,
    List.cons_append, List.nil_append, Letter.dual_mk, Bool.not_true,Bool.not_false,
    Shape.gen, inv_dual, Signature.ColourDuality.dualWord_cons,
    Signature.ColourDuality.dualWord_nil, Signature.ColourDuality.pivotal_dual,
    psig_right_cross]
  region_tac

/-- **The upward crossing is cyclic** (KL III eq. `eq_cyclic_cross-gen`): its two mates for the
biadjunctions of two-letter words (nested cups and caps) agree (both are the downward
crossing). -/
theorem upcross_same_isCyclic (i : I) (ν : X)
    (hg : (psig RD).GenValid (.gen (.cross true i i ν))) :
    IsCyclic (biadj (biadjColour RD k S) ((PQ).genDom _ hg))
      (biadj (biadjColour RD k S) ((PQ).genCod _ hg)) ((PQ).gen2 _ hg) := by
  obtain ⟨cup, hcup, hcupL⟩ := biadjW_left_unit_isDiag (zigzags RD k S) _ ((PQ).genDom _ hg) rfl
  obtain ⟨cap', hcap, hcapL⟩ :=
    biadjW_left_counit_isDiag (zigzags RD k S) _ ((PQ).genCod _ hg) rfl
  obtain ⟨cupR, hcupR, hcupRL⟩ :=
    biadjW_right_unit_isDiag (zigzags RD k S) _ ((PQ).genDom _ hg) rfl
  obtain ⟨capR', hcapR, hcapRL⟩ :=
    biadjW_right_counit_isDiag (zigzags RD k S) _ ((PQ).genCod _ hg) rfl
  refine (isCyclic_diag_iff _ _ cup hcup cap' hcap cupR hcupR capR' hcapR (genDiag _ hg)).2 ?_
  have h₁ : ((PQ).genDom _ hg).obj.word = Wup := rfl
  have h₂ : ((PQ).genCod _ hg).obj.word = Wup := rfl
  have h₃ : ((PQ).dualHom piv
      ((PQ).genCod _ hg)).obj = ⟨ν, [⟨dn i, sh RD (up i) + ν⟩,
        ⟨dn i, sh RD (up i) + (sh RD (up i) + ν)⟩]⟩ := rfl
  have h₄ : ((PQ).dualHom piv
      ((PQ).genDom _ hg)).obj = ⟨ν, [⟨dn i, sh RD (up i) + ν⟩,
        ⟨dn i, sh RD (up i) + (sh RD (up i) + ν)⟩]⟩ := rfl
  have e : ((PQ).dualHom piv ((PQ).genCod _ hg)).obj =
      ob RD (sh RD (up i) + (sh RD (up i) + ν)) [dn i, dn i] := by
    rw [h₃]; simp only [ob, wt_cons, wt_nil, wd_cons, wd_nil]; region_tac
  have e' : ((PQ).dualHom piv ((PQ).genDom _ hg)).obj =
      ob RD (sh RD (up i) + (sh RD (up i) + ν)) [dn i, dn i] := by
    rw [h₄]; simp only [ob, wt_cons, wt_nil, wd_cons, wd_nil]; region_tac
  refine diag_eq_transfer _ _ _ (rotCrossR RD i i _) (rotCrossL RD i i _) e e' ?_ ?_ ?_
  · rw [layers_rightRotateD, hcupL, hcapL, h₁, h₂, h₃, h₄]
    exact layers_rightRotate_upcross_same RD i ν hg
  · rw [layers_leftRotateD, hcupRL, hcapRL, h₁, h₂, h₃, h₄]
    exact layers_leftRotate_upcross_same RD i ν hg
  · exact diag_rotCrossR_same_eq_rotCrossL RD k S i _


theorem diag_rotCrossR_same_eq_smul (i : I) (μ : X) :
    (PQ).diag (rotCrossR RD i i μ) =
      ((S.withRone.t i i : kˣ) : k) • (PQ).diag (downCross RD i i μ) := by
  have hR := (PQ).lin_rel_self (.inr (.cycCrossR i i μ))
  change (PQ).lin ((((S.withRone.t i i)⁻¹ : kˣ) : k) •
    LinDiagram.of (rotCrossR RD i i μ) - LinDiagram.of (downCross RD i i μ)) = 0 at hR
  rw [lin_sub, lin_smul, lin_of, lin_of, sub_eq_zero] at hR
  rw [← hR, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

/-- The two-letter upward word `E_i E_i` on the left boundary of the upward crossing. -/
abbrev upWordObj (i : I) (ν : X) : Obj (psig RD) :=
  ⟨(psig RD).left (gUp), Wup⟩

theorem layers_rightRotate_downcross_same (i : I) (ν : X)
    (hg : (psig RD).GenValid (.gen (.cross false i i (sh RD (up i) + (sh RD (up i) + ν))))) :
    List.map (fun x => Layer.wl (upWordObj RD i ν) x)
          (cupLayers (E := (inv RD)) ((psig RD).left (gDn))
            Wdn) ++
        List.map (fun x => Layer.wl (upWordObj RD i ν) x)
          (List.map (fun x => x.wr Wup)
            (Diagram.layers (genDiag (gDn) hg))) ++
      List.map (fun x => x.wr Wup)
        (capLayers (E := (inv RD)) ((psig RD).right (gDn))
          Wdn) =
    List.map (fun x => Layer.wl (upWordObj RD i ν) x)
          (cupRLayers (E := (inv RD)) ((psig RD).right (gUp)) Wup) ++
        List.map (fun x => Layer.wl (upWordObj RD i ν) x)
          (List.map (fun x => x.wr Wup)
            (Diagram.layers (genDiag (gDn) hg))) ++
      List.map (fun x => x.wr Wup)
        (capRLayers (E := (inv RD)) ((psig RD).left (gUp)) Wup) := by
  simp only [genDiag, cupLayers, capLayers, cupRLayers, capRLayers, Diagram.layers_layer,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_nil, Layer.wl, Layer.wr]
  simp only [List.nil_append, Letter.dual_mk, Bool.not_true, Bool.not_false, inv_dual,
    Signature.ColourDuality.dualWord_cons, Signature.ColourDuality.dualWord_nil,
    Signature.ColourDuality.pivotal_dual, psig_right_cross, psig_left_cross]
  region_tac

theorem layers_leftRotate_downcross_same (i : I) (ν : X)
    (hg : (psig RD).GenValid (.gen (.cross false i i (sh RD (up i) + (sh RD (up i) + ν))))) :
    List.map (fun x => x.wr Wup)
          (cupRLayers (E := (inv RD)) ((psig RD).right (gDn))
            Wdn) ++
        List.map (fun x => Layer.wl (upWordObj RD i ν) x)
          (List.map (fun x => x.wr Wup)
            (Diagram.layers (genDiag (gDn) hg))) ++
      List.map (fun x => Layer.wl (upWordObj RD i ν) x)
        (capRLayers (E := (inv RD)) ((psig RD).left (gDn))
          Wdn) =
    List.map (fun x => x.wr Wup)
          (cupLayers (E := (inv RD)) ((psig RD).left (gUp)) Wup) ++
        List.map (fun x => Layer.wl (upWordObj RD i ν) x)
          (List.map (fun x => x.wr Wup)
            (Diagram.layers (genDiag (gDn) hg))) ++
      List.map (fun x => Layer.wl (upWordObj RD i ν) x)
        (capLayers (E := (inv RD)) ((psig RD).right (gUp)) Wup) := by
  simp only [genDiag, cupLayers, capLayers, cupRLayers, capRLayers, Diagram.layers_layer,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_nil, Layer.wl, Layer.wr]
  simp only [List.nil_append, Letter.dual_mk, Bool.not_true, Bool.not_false, inv_dual,
    Signature.ColourDuality.dualWord_cons, Signature.ColourDuality.dualWord_nil,
    Signature.ColourDuality.pivotal_dual, psig_right_cross, psig_left_cross]
  region_tac

/-- **The downward crossing is cyclic**: it is the mate of the upward crossing
(eq. `eq_cyclic_cross-gen`), and mates of cyclic 2-morphisms are cyclic. -/
theorem downcross_same_isCyclic (i : I) (μ : X)
    (hg : (psig RD).GenValid (.gen (.cross false i i μ))) :
    IsCyclic (biadj (biadjColour RD k S) ((PQ).genDom _ hg))
      (biadj (biadjColour RD k S) ((PQ).genCod _ hg)) ((PQ).gen2 _ hg) := by
  obtain ⟨ν, rfl⟩ : ∃ ν, μ = sh RD (up i) + (sh RD (up i) + ν) :=
    ⟨sh RD (dn i) + (sh RD (dn i) + μ), by simp⟩
  have hu := genValid_upcross RD i i ν
  have hβ := (upcross_same_isCyclic RD k S i ν hu).rightMate
  -- the up-crossing side
  have u₁ : ((PQ).genDom _ hu).obj.word = Wup := rfl
  have u₂ : ((PQ).genCod _ hu).obj.word = Wup := rfl
  have u₃ : ((PQ).dualHom piv
      ((PQ).genCod _ hu)).obj = ⟨ν, [⟨dn i, sh RD (up i) + ν⟩,
        ⟨dn i, sh RD (up i) + (sh RD (up i) + ν)⟩]⟩ := rfl
  have u₄ : ((PQ).dualHom piv
      ((PQ).genDom _ hu)).obj = ⟨ν, [⟨dn i, sh RD (up i) + ν⟩,
        ⟨dn i, sh RD (up i) + (sh RD (up i) + ν)⟩]⟩ := rfl
  obtain ⟨cup, hcup, hcupL⟩ := biadjW_left_unit_isDiag (zigzags RD k S) _ ((PQ).genDom _ hu) rfl
  obtain ⟨cap', hcap, hcapL⟩ :=
    biadjW_left_counit_isDiag (zigzags RD k S) _ ((PQ).genCod _ hu) rfl
  replace hcup : (biadj (biadjColour RD k S) ((PQ).genDom _ hu)).left.unit =
      (PQ).diag cup := hcup
  replace hcap : (biadj (biadjColour RD k S) ((PQ).genCod _ hu)).left.counit =
      (PQ).diag cap' := hcap
  rw [show (PQ).gen2 _ hu = (PQ).diag (genDiag _ hu) from rfl,
    rightMate_diag _ _ cup hcup cap' hcap] at hβ
  have e : ((PQ).dualHom piv ((PQ).genCod _ hu)).obj =
      ob RD (sh RD (up i) + (sh RD (up i) + ν)) [dn i, dn i] := by
    rw [u₃]; simp only [ob, wt_cons, wt_nil, wd_cons, wd_nil]; region_tac
  have e' : ((PQ).dualHom piv ((PQ).genDom _ hu)).obj =
      ob RD (sh RD (up i) + (sh RD (up i) + ν)) [dn i, dn i] := by
    rw [u₄]; simp only [ob, wt_cons, wt_nil, wd_cons, wd_nil]; region_tac
  have hb : ((PQ).genDom _ hg).obj = ((PQ).dualHom piv
      ((PQ).genCod _ hu)).obj := by
    rw [u₃]; show (⟨_, _⟩ : Obj (psig RD)) = _
    simp only [wd_cons, wd_nil, wt_cons, wt_nil, psig_left_cross, psig_dom_cross]
    region_tac
  have hb' : ((PQ).genCod _ hg).obj = ((PQ).dualHom piv
      ((PQ).genDom _ hu)).obj := by
    rw [u₄]; show (⟨_, _⟩ : Obj (psig RD)) = _
    simp only [wd_cons, wd_nil, wt_cons, wt_nil, psig_left_cross, psig_cod_cross]
    region_tac
  rw [(PQ).diag_eq_of_layers_eq' _ (rotCrossR RD i i _) e e' ?_,
    diag_rotCrossR_same_eq_smul RD k S i _, Linear.smul_comp, Linear.comp_smul,
    ← (PQ).diag_eq_of_layers_eq' (Diagram.cast (genDiag _ hg) hb hb')
      (downCross RD i i _) e e' rfl] at hβ
  swap
  · rw [layers_rightRotateD, hcupL, hcapL, u₁, u₂, u₃, u₄]
    exact layers_rightRotate_upcross_same RD i ν hu
  replace hβ := hβ.smul ((((S.withRone.t i i)⁻¹ : kˣ) : k))
  rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at hβ
  obtain ⟨cupR', hcupR', hcupRL'⟩ :=
    biadjW_right_unit_isDiag (zigzags RD k S) _ ((PQ).genCod _ hu) rfl
  obtain ⟨capR, hcapR, hcapRL⟩ :=
    biadjW_right_counit_isDiag (zigzags RD k S) _ ((PQ).genDom _ hu) rfl
  obtain ⟨cup'', hcup'', hcupL''⟩ :=
    biadjW_left_unit_isDiag (zigzags RD k S) _ ((PQ).genCod _ hu) rfl
  obtain ⟨cap'', hcap'', hcapL''⟩ :=
    biadjW_left_counit_isDiag (zigzags RD k S) _ ((PQ).genDom _ hu) rfl
  rw [isCyclic_diag_iff _ _ cupR' hcupR' capR hcapR cup'' hcup'' cap'' hcap''] at hβ
  obtain ⟨dcup, hdcup, hdcupL⟩ :=
    biadjW_left_unit_isDiag (zigzags RD k S) _ ((PQ).genDom _ hg) rfl
  obtain ⟨dcap', hdcap', hdcapL⟩ :=
    biadjW_left_counit_isDiag (zigzags RD k S) _ ((PQ).genCod _ hg) rfl
  obtain ⟨dcupR, hdcupR, hdcupRL⟩ :=
    biadjW_right_unit_isDiag (zigzags RD k S) _ ((PQ).genDom _ hg) rfl
  obtain ⟨dcapR', hdcapR', hdcapRL⟩ :=
    biadjW_right_counit_isDiag (zigzags RD k S) _ ((PQ).genCod _ hg) rfl
  refine (isCyclic_diag_iff _ _ dcup hdcup dcap' hdcap' dcupR hdcupR dcapR' hdcapR'
    (genDiag _ hg)).2 ?_
  have d₁ : ((PQ).genDom _ hg).obj.word =
      Wdn := rfl
  have d₂ : ((PQ).genCod _ hg).obj.word =
      Wdn := rfl
  have d₃ : ((PQ).dualHom piv
      ((PQ).genCod _ hg)).obj = ((PQ).genDom _ hu).obj := by
    show (⟨_, _⟩ : Obj (psig RD)) = ⟨_, _⟩
    rw [d₂]
    simp only [psig_right_cross, psig_left_cross, psig_dom_cross, wd_cons, wd_nil,
      wt_cons, wt_nil, Signature.ColourDuality.dualWord_cons, Signature.ColourDuality.dualWord_nil,
      Signature.ColourDuality.pivotal_dual, inv_dual, List.nil_append, List.cons_append,
      Letter.dual_mk, Bool.not_false]
    region_tac
  have d₄ : ((PQ).dualHom piv
      ((PQ).genDom _ hg)).obj = ((PQ).genCod _ hu).obj := by
    show (⟨_, _⟩ : Obj (psig RD)) = ⟨_, _⟩
    rw [d₁]
    simp only [psig_right_cross, psig_left_cross, psig_cod_cross, wd_cons, wd_nil,
      wt_cons, wt_nil, Signature.ColourDuality.dualWord_cons, Signature.ColourDuality.dualWord_nil,
      Signature.ColourDuality.pivotal_dual, inv_dual, List.nil_append, List.cons_append,
      Letter.dual_mk, Bool.not_false]
    region_tac
  refine diag_eq_transfer _ _ _ _ _ d₃ d₄ ?_ ?_ hβ
  all_goals
    simp only [layers_rightRotateD, layers_leftRotateD, hdcupL, hdcapL, hcupRL', hcapRL, hdcupRL,
      hdcapRL, hcupL'', hcapL'', d₁, d₂, u₁, u₂, d₃, d₄]
    simp only [Diagram.layers_cast]
  · exact layers_rightRotate_downcross_same RD i ν hg
  · exact layers_leftRotate_downcross_same RD i ν hg

end Categorification.KL3.Diagram.CLQ
