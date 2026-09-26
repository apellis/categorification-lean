/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Presentation
import Categorification.Diagrams.KL3.NestedCups

/-!
# Cyclicity: all 2-morphisms of `U` are cyclic

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1,
Definition 3.1: "All 2-morphisms are cyclic with respect to the above biadjoint structure. This
is ensured by the relations (3.3) and (`eq_cyclic_cross-gen`)."

We prove this statement for the presentation `pres RD k`, with the biadjunctions `x ⊣⊢ x*` of
all words given by the (nested) cups and caps (`biadjWord`):

* `updot_isCyclic`, `downdot_isCyclic`: the upward dot is cyclic because both of its rotations
  equal the downward dot (relations `cycDotR`, `cycDotL`); the downward dot is then cyclic as a
  mate of a cyclic 2-morphism;
* `upcross_isCyclic`, `downcross_isCyclic`: the same for the crossings (relations `cycCrossR`,
  `cycCrossL`), using that the units and counits of the biadjunctions of two-letter words are the
  nested cup and cap diagrams (`Categorification.Diagrams.KL3.NestedCups`);
* `isCyclic`: every 2-morphism of `U` is cyclic, by the rotation invariance theorem of the
  pivotal extension (`Presentation.pivotal_isCyclic`); `pivotal` is the resulting pivotal
  structure on `U`.

These proofs also certify the transcription of the rotated diagrams in `Relations.lean`: the
diagrams `rotDotR`, `rotDotL`, `rotCrossR`, `rotCrossL` have exactly the layers of the mates
computed from the library's biadjunctions.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Biadjunction

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

@[simp] theorem sh_dn_add_sh_up (i : I) (ν : X) : sh RD (dn i) + (sh RD (up i) + ν) = ν := by
  rw [← add_assoc, show dn i = (up i).dual from rfl, sh_dual_add_sh, zero_add]

@[simp] theorem sh_up_add_sh_dn (i : I) (ν : X) : sh RD (up i) + (sh RD (dn i) + ν) = ν := by
  rw [← add_assoc, show dn i = (up i).dual from rfl, sh_add_sh_dual, zero_add]

theorem sh_false (i : I) : sh RD (false, i) = -sh RD (true, i) := sh_dual RD (true, i)

theorem sh_dn (i : I) : sh RD (dn i) = -sh RD (up i) := sh_dual RD (true, i)

@[simp] theorem psig_right_cross (ε : Bool) (i j : I) (ν : X) :
    (psig RD).right (.gen (.cross ε i j ν)) = ν := rfl

@[simp] theorem sig0_colourTgt (c : Col I X) : (sig0 RD).colourTgt c = c.r := rfl

@[simp] theorem sig0_colourSrc (c : Col I X) : (sig0 RD).colourSrc c = sh RD c.l + c.r := rfl

@[simp] theorem psig_dom_cross (ε : Bool) (i j : I) (ν : X) :
    (psig RD).dom (.gen (.cross ε i j ν)) = wd RD ν [(ε, i), (ε, j)] := rfl

@[simp] theorem psig_cod_cross (ε : Bool) (i j : I) (ν : X) :
    (psig RD).cod (.gen (.cross ε i j ν)) = wd RD ν [(ε, j), (ε, i)] := rfl

@[simp] theorem psig_left_cross (ε : Bool) (i j : I) (ν : X) :
    (psig RD).left (.gen (.cross ε i j ν)) = sh RD (ε, i) + (sh RD (ε, j) + ν) := rfl

/-- Transport an equality of classes of diagrams along equalities of boundary objects and of
lists of layers. -/
theorem diag_eq_transfer {S : Signature} {R : Type*} [CommRing R] (P : Presentation S R)
    {a b a' b' : Obj S} (A B : a ⟶ b) (A' B' : a' ⟶ b') (e₁ : a = a') (e₂ : b = b')
    (hA : Diagram.layers A = Diagram.layers A') (hB : Diagram.layers B = Diagram.layers B')
    (h : P.diag A' = P.diag B') : P.diag A = P.diag B := by
  rw [P.diag_eq_of_layers_eq' A A' e₁ e₂ hA, P.diag_eq_of_layers_eq' B B' e₁ e₂ hB, h]

/-- The upward dot on the strand `⟨E_i, ν⟩` is a valid generator. -/
theorem genValid_updot (i : I) (ν : X) : (psig RD).GenValid (.gen (.dot ⟨up i, ν⟩)) :=
  ⟨⟨rfl, trivial⟩, rfl, ⟨rfl, trivial⟩, rfl⟩

/-- **The upward dot is cyclic** (KL III eq. (3.3)): its two mates for the biadjunction
`E_{+i} 1_ν ⊣⊢ E_{-i} 1_{ν+i_X}` agree (both are the downward dot). -/
theorem updot_isCyclic (i : I) (ν : X) (hg : (psig RD).GenValid (.gen (.dot ⟨up i, ν⟩))) :
    IsCyclic (biadj (biadjColour RD k) ((pres RD k).genDom _ hg))
      (biadj (biadjColour RD k) ((pres RD k).genCod _ hg)) ((pres RD k).gen2 _ hg) := by
  rw [isCyclic_biadj_iff_single (biadjColour RD k) (c := ⟨up i, ν⟩) (c' := ⟨up i, ν⟩) rfl rfl]
  refine (isCyclic_diag_iff (biadjColour RD k ((pres RD k).genDom _ hg) ⟨up i, ν⟩ rfl)
    (biadjColour RD k ((pres RD k).genCod _ hg) ⟨up i, ν⟩ rfl) _ rfl _ rfl _ rfl _ rfl
    (genDiag _ hg)).2 ?_
  have ha : (⟨ν, [(inv RD).dual ⟨up i, ν⟩]⟩ : Obj (psig RD)) = ob RD (sh RD (up i) + ν) [dn i] :=
    Obj.ext (by simp [ob]) rfl
  rw [(pres RD k).diag_eq_of_layers_eq' _ (rotDotR RD i (sh RD (up i) + ν)) ha ha ?_,
    (pres RD k).diag_eq_of_layers_eq' _ (rotDotL RD i (sh RD (up i) + ν)) ha ha ?_]
  · congr 2
    exact ((pres RD k).diag_eq_of_rel (.inr (.cycDotR i _)) rfl).trans
      ((pres RD k).diag_eq_of_rel (.inr (.cycDotL i _)) rfl).symm
  · simp [rotDotL, genDiag, layList, lay, Layer.wl, Layer.wr, Pivotal.cupD, Pivotal.capD,
      pivotalCupsCaps, genDom, genCod, inv_dual, Shape.gen, Signature.pivotal, sig0,
      Signature.ColourDuality.dualWord, Letter.dual]
  · simp [rotDotR, genDiag, layList, lay, Layer.wl, Layer.wr, Pivotal.cupD, Pivotal.capD,
      pivotalCupsCaps, genDom, genCod, inv_dual, Shape.gen, Signature.pivotal, sig0,
      Signature.ColourDuality.dualWord, Letter.dual]

/-- The downward dot on the strand `⟨F_i, μ⟩` is a valid generator. -/
theorem genValid_downdot (i : I) (μ : X) : (psig RD).GenValid (.gen (.dot ⟨dn i, μ⟩)) :=
  ⟨⟨rfl, trivial⟩, rfl, ⟨rfl, trivial⟩, rfl⟩

/-- **The downward dot is cyclic**: it is the mate of the upward dot (eq. (3.3)), and mates of
cyclic 2-morphisms are cyclic. -/
theorem downdot_isCyclic (i : I) (μ : X) (hg : (psig RD).GenValid (.gen (.dot ⟨dn i, μ⟩))) :
    IsCyclic (biadj (biadjColour RD k) ((pres RD k).genDom _ hg))
      (biadj (biadjColour RD k) ((pres RD k).genCod _ hg)) ((pres RD k).gen2 _ hg) := by
  obtain ⟨ν, rfl⟩ : ∃ ν, μ = sh RD (up i) + ν := ⟨sh RD (dn i) + μ, by simp⟩
  have hu := genValid_updot RD i ν
  have hα := (isCyclic_biadj_iff_single (biadjColour RD k) (c := ⟨up i, ν⟩) (c' := ⟨up i, ν⟩)
    rfl rfl _).1 (updot_isCyclic RD k i ν hu)
  have hβ := hα.rightMate
  have ha : (⟨ν, [(inv RD).dual ⟨up i, ν⟩]⟩ : Obj (psig RD)) = ob RD (sh RD (up i) + ν) [dn i] :=
    Obj.ext (by simp [ob]) rfl
  have hb : (⟨sh RD (dn i) + (sh RD (up i) + ν), [⟨dn i, sh RD (up i) + ν⟩]⟩ : Obj (psig RD)) =
      ⟨ν, [(inv RD).dual ⟨up i, ν⟩]⟩ := Obj.ext (by simp) rfl
  rw [show (pres RD k).gen2 _ hu = (pres RD k).diag (genDiag _ hu) from rfl,
    rightMate_diag _ _ _ rfl _ rfl] at hβ
  rw [(pres RD k).diag_eq_of_layers_eq' _ (rotDotR RD i (sh RD (up i) + ν)) ha ha ?_,
    (pres RD k).diag_eq_of_rel (.inr (.cycDotR i _)) rfl,
    ← (pres RD k).diag_eq_of_layers_eq' (Diagram.cast (genDiag _ hg) hb hb)
        (downDot RD i (sh RD (up i) + ν)) ha ha rfl] at hβ
  swap
  · simp [rotDotR, genDiag, layList, lay, Layer.wl, Layer.wr, Pivotal.cupD, Pivotal.capD,
      pivotalCupsCaps, genDom, genCod, inv_dual, Shape.gen, Signature.pivotal, sig0,
      Signature.ColourDuality.dualWord, Letter.dual]
  rw [isCyclic_diag_iff _ _ _ rfl _ rfl _ rfl _ rfl] at hβ
  rw [isCyclic_biadj_iff_single (biadjColour RD k) (c := ⟨dn i, sh RD (up i) + ν⟩)
    (c' := ⟨dn i, sh RD (up i) + ν⟩) rfl rfl]
  refine (isCyclic_diag_iff
    (biadjColour RD k ((pres RD k).genDom _ hg) ⟨dn i, sh RD (up i) + ν⟩ rfl)
    (biadjColour RD k ((pres RD k).genCod _ hg) ⟨dn i, sh RD (up i) + ν⟩ rfl) _ rfl _ rfl _ rfl _ rfl
    (genDiag _ hg)).2 ?_
  have e : (⟨sh RD (up i) + ν, [(inv RD).dual ⟨dn i, sh RD (up i) + ν⟩]⟩ : Obj (psig RD)) =
      ⟨sh RD (up i) + ν, [⟨up i, ν⟩]⟩ := Obj.ext rfl (by simp [inv_dual, Letter.dual])
  have hdd : (inv RD).dual ⟨dn i, sh RD (up i) + ν⟩ = ⟨up i, ν⟩ := by
    rw [inv_dual]; simp [Letter.dual]
  have hd₁ : (inv RD).toColourDuality.pivotal.dualWord
      ((psig RD).cod (.gen (.dot ⟨dn i, sh RD (up i) + ν⟩))) = [⟨up i, ν⟩] := by
    show [(inv RD).dual ⟨dn i, sh RD (up i) + ν⟩] = _
    rw [hdd]
  have hd₂ : (inv RD).toColourDuality.pivotal.dualWord
      ((psig RD).dom (.gen (.dot ⟨dn i, sh RD (up i) + ν⟩))) = [⟨up i, ν⟩] := hd₁
  refine diag_eq_transfer _ _ _ _ _ e e ?_ ?_ hβ
  all_goals
    simp only [layers_rightRotateD, layers_leftRotateD, Diagram.layers_cast, pivotalCupsCaps,
      Pivotal.cupD, Pivotal.capD, Diagram.layers_layer, genDiag, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Layer.wl, Layer.wr, dualHom_obj, genDom, genCod]
    refine List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_,
      List.cons_eq_cons.2 ⟨Layer.ext ?_ ?_ ?_ ?_, rfl⟩⟩⟩
    all_goals (try simp only [hd₁, hd₂, hdd, List.append_nil]); try rfl

/-- Closes equalities of lists of layers of `psig` that differ only by the arithmetic of
weights. -/
macro "region_tac" : tactic => `(tactic| (
  simp only [List.cons.injEq, Layer.mk.injEq, Col.mk.injEq, Obj.mk.injEq, and_true, true_and,
    and_self]
  repeat' constructor
  all_goals (try simp only [sh_false, sh_dn, sig0_colourTgt, sig0_colourSrc])
  all_goals first | rfl | abel1 | (congr 1; abel1) | (congr 2; abel1) | (congr 3; abel1)))

/-- The upward crossing `E_j E_i 1_ν ⟶ E_i E_j 1_ν` is a valid generator. -/
theorem genValid_upcross (j i : I) (ν : X) :
    (psig RD).GenValid (.gen (.cross true j i ν)) :=
  ⟨⟨rfl, rfl, trivial⟩, rfl,
    ⟨show sh RD (true, i) + (sh RD (true, j) + ν) = sh RD (true, j) + (sh RD (true, i) + ν) from
      add_left_comm _ _ _, rfl, trivial⟩, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **The upward crossing is cyclic** (KL III eq. `eq_cyclic_cross-gen`): its two mates for the
biadjunctions of two-letter words (nested cups and caps) agree (both are the downward
crossing). -/
theorem upcross_isCyclic (j i : I) (ν : X) (hg : (psig RD).GenValid (.gen (.cross true j i ν))) :
    IsCyclic (biadj (biadjColour RD k) ((pres RD k).genDom _ hg))
      (biadj (biadjColour RD k) ((pres RD k).genCod _ hg)) ((pres RD k).gen2 _ hg) := by
  obtain ⟨cup, hcup, hcupL⟩ := biadjW_left_unit_isDiag (zigzags RD k) _ ((pres RD k).genDom _ hg) rfl
  obtain ⟨cap', hcap, hcapL⟩ :=
    biadjW_left_counit_isDiag (zigzags RD k) _ ((pres RD k).genCod _ hg) rfl
  obtain ⟨cupR, hcupR, hcupRL⟩ :=
    biadjW_right_unit_isDiag (zigzags RD k) _ ((pres RD k).genDom _ hg) rfl
  obtain ⟨capR', hcapR, hcapRL⟩ :=
    biadjW_right_counit_isDiag (zigzags RD k) _ ((pres RD k).genCod _ hg) rfl
  refine (isCyclic_diag_iff _ _ cup hcup cap' hcap cupR hcupR capR' hcapR (genDiag _ hg)).2 ?_
  have h₁ : ((pres RD k).genDom _ hg).obj.word = [⟨up j, sh RD (up i) + ν⟩, ⟨up i, ν⟩] := rfl
  have h₂ : ((pres RD k).genCod _ hg).obj.word = [⟨up i, sh RD (up j) + ν⟩, ⟨up j, ν⟩] := rfl
  have h₃ : ((pres RD k).dualHom (inv RD).toColourDuality.pivotal
      ((pres RD k).genCod _ hg)).obj = ⟨ν, [⟨dn j, sh RD (up j) + ν⟩,
        ⟨dn i, sh RD (up i) + (sh RD (up j) + ν)⟩]⟩ := rfl
  have h₄ : ((pres RD k).dualHom (inv RD).toColourDuality.pivotal
      ((pres RD k).genDom _ hg)).obj = ⟨ν, [⟨dn i, sh RD (up i) + ν⟩,
        ⟨dn j, sh RD (up j) + (sh RD (up i) + ν)⟩]⟩ := rfl
  have e : ((pres RD k).dualHom (inv RD).toColourDuality.pivotal ((pres RD k).genCod _ hg)).obj =
      ob RD (sh RD (up i) + (sh RD (up j) + ν)) [dn j, dn i] := by
    rw [h₃]; simp only [ob, wt_cons, wt_nil, wd_cons, wd_nil]; region_tac
  have e' : ((pres RD k).dualHom (inv RD).toColourDuality.pivotal ((pres RD k).genDom _ hg)).obj =
      ob RD (sh RD (up i) + (sh RD (up j) + ν)) [dn i, dn j] := by
    rw [h₄]; simp only [ob, wt_cons, wt_nil, wd_cons, wd_nil]; region_tac
  refine diag_eq_transfer _ _ _ (rotCrossR RD j i _) (rotCrossL RD j i _) e e' ?_ ?_ ?_
  · rw [layers_rightRotateD, hcupL, hcapL, h₁, h₂, h₃, h₄]
    simp only [genDiag, cupLayers, capLayers, Diagram.layers_layer, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.map_append, List.append_nil, Layer.wl, Layer.wr,
      rotCrossR, layers_mkD, layList, lay]
    simp only [wt_cons, wt_nil, wd_cons, wd_nil, Shape.dom_cup, Shape.dom_cap, Shape.dom_cross,
      List.cons_append, List.nil_append, Letter.dual_mk, Bool.not_true, Bool.not_false,
      Shape.gen, inv_dual, Signature.ColourDuality.dualWord_cons,
      Signature.ColourDuality.dualWord_nil, Signature.ColourDuality.pivotal_dual,
      psig_right_cross, psig_left_cross]
    region_tac
  · rw [layers_leftRotateD, hcupRL, hcapRL, h₁, h₂, h₃, h₄]
    simp only [genDiag, cupRLayers, capRLayers, Diagram.layers_layer, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.map_append, List.append_nil, Layer.wl, Layer.wr,
      rotCrossL, layers_mkD, layList, lay]
    simp only [wt_cons, wt_nil, wd_cons, wd_nil, Shape.dom_cup, Shape.dom_cap, Shape.dom_cross,
      List.cons_append, List.nil_append, Letter.dual_mk, Bool.not_true, Bool.not_false,
      Shape.gen, inv_dual, Signature.ColourDuality.dualWord_cons,
      Signature.ColourDuality.dualWord_nil, Signature.ColourDuality.pivotal_dual,
      psig_right_cross, psig_left_cross]
    region_tac
  · exact ((pres RD k).diag_eq_of_rel (.inr (.cycCrossR j i _)) rfl).trans
      ((pres RD k).diag_eq_of_rel (.inr (.cycCrossL j i _)) rfl).symm

/-- The downward crossing `F_j F_i 1_μ ⟶ F_i F_j 1_μ` is a valid generator. -/
theorem genValid_downcross (j i : I) (μ : X) :
    (psig RD).GenValid (.gen (.cross false j i μ)) :=
  ⟨⟨rfl, rfl, trivial⟩, rfl,
    ⟨show sh RD (false, i) + (sh RD (false, j) + μ) = sh RD (false, j) + (sh RD (false, i) + μ) from
      add_left_comm _ _ _, rfl, trivial⟩, rfl⟩

set_option maxHeartbeats 2000000 in
/-- **The downward crossing is cyclic**: it is the mate of the upward crossing
(eq. `eq_cyclic_cross-gen`), and mates of cyclic 2-morphisms are cyclic. -/
theorem downcross_isCyclic (j i : I) (μ : X)
    (hg : (psig RD).GenValid (.gen (.cross false j i μ))) :
    IsCyclic (biadj (biadjColour RD k) ((pres RD k).genDom _ hg))
      (biadj (biadjColour RD k) ((pres RD k).genCod _ hg)) ((pres RD k).gen2 _ hg) := by
  obtain ⟨ν, rfl⟩ : ∃ ν, μ = sh RD (up i) + (sh RD (up j) + ν) :=
    ⟨sh RD (dn j) + (sh RD (dn i) + μ), by simp⟩
  have hu := genValid_upcross RD j i ν
  have hβ := (upcross_isCyclic RD k j i ν hu).rightMate
  -- the up-crossing side
  have u₁ : ((pres RD k).genDom _ hu).obj.word = [⟨up j, sh RD (up i) + ν⟩, ⟨up i, ν⟩] := rfl
  have u₂ : ((pres RD k).genCod _ hu).obj.word = [⟨up i, sh RD (up j) + ν⟩, ⟨up j, ν⟩] := rfl
  have u₃ : ((pres RD k).dualHom (inv RD).toColourDuality.pivotal
      ((pres RD k).genCod _ hu)).obj = ⟨ν, [⟨dn j, sh RD (up j) + ν⟩,
        ⟨dn i, sh RD (up i) + (sh RD (up j) + ν)⟩]⟩ := rfl
  have u₄ : ((pres RD k).dualHom (inv RD).toColourDuality.pivotal
      ((pres RD k).genDom _ hu)).obj = ⟨ν, [⟨dn i, sh RD (up i) + ν⟩,
        ⟨dn j, sh RD (up j) + (sh RD (up i) + ν)⟩]⟩ := rfl
  obtain ⟨cup, hcup, hcupL⟩ := biadjW_left_unit_isDiag (zigzags RD k) _ ((pres RD k).genDom _ hu) rfl
  obtain ⟨cap', hcap, hcapL⟩ :=
    biadjW_left_counit_isDiag (zigzags RD k) _ ((pres RD k).genCod _ hu) rfl
  replace hcup : (biadj (biadjColour RD k) ((pres RD k).genDom _ hu)).left.unit =
      (pres RD k).diag cup := hcup
  replace hcap : (biadj (biadjColour RD k) ((pres RD k).genCod _ hu)).left.counit =
      (pres RD k).diag cap' := hcap
  rw [show (pres RD k).gen2 _ hu = (pres RD k).diag (genDiag _ hu) from rfl,
    rightMate_diag _ _ cup hcup cap' hcap] at hβ
  have e : ((pres RD k).dualHom (inv RD).toColourDuality.pivotal ((pres RD k).genCod _ hu)).obj =
      ob RD (sh RD (up i) + (sh RD (up j) + ν)) [dn j, dn i] := by
    rw [u₃]; simp only [ob, wt_cons, wt_nil, wd_cons, wd_nil]; region_tac
  have e' : ((pres RD k).dualHom (inv RD).toColourDuality.pivotal ((pres RD k).genDom _ hu)).obj =
      ob RD (sh RD (up i) + (sh RD (up j) + ν)) [dn i, dn j] := by
    rw [u₄]; simp only [ob, wt_cons, wt_nil, wd_cons, wd_nil]; region_tac
  have hb : ((pres RD k).genDom _ hg).obj = ((pres RD k).dualHom (inv RD).toColourDuality.pivotal
      ((pres RD k).genCod _ hu)).obj := by
    rw [u₃]; show (⟨_, _⟩ : Obj (psig RD)) = _
    simp only [wd_cons, wd_nil, wt_cons, wt_nil, psig_left_cross, psig_dom_cross, psig_cod_cross]
    region_tac
  have hb' : ((pres RD k).genCod _ hg).obj = ((pres RD k).dualHom (inv RD).toColourDuality.pivotal
      ((pres RD k).genDom _ hu)).obj := by
    rw [u₄]; show (⟨_, _⟩ : Obj (psig RD)) = _
    simp only [wd_cons, wd_nil, wt_cons, wt_nil, psig_left_cross, psig_dom_cross, psig_cod_cross]
    region_tac
  rw [(pres RD k).diag_eq_of_layers_eq' _ (rotCrossR RD j i _) e e' ?_,
    (pres RD k).diag_eq_of_rel (.inr (.cycCrossR j i _)) rfl,
    ← (pres RD k).diag_eq_of_layers_eq' (Diagram.cast (genDiag _ hg) hb hb')
      (downCross RD j i _) e e' rfl] at hβ
  swap
  · rw [layers_rightRotateD, hcupL, hcapL, u₁, u₂, u₃, u₄]
    simp only [genDiag, cupLayers, capLayers, Diagram.layers_layer, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.map_append, List.append_nil, Layer.wl, Layer.wr,
      rotCrossR, layers_mkD, layList, lay]
    simp only [wt_cons, wt_nil, wd_cons, wd_nil, Shape.dom_cup, Shape.dom_cap, Shape.dom_cross,
      List.cons_append, List.nil_append, Letter.dual_mk, Bool.not_true, Bool.not_false,
      Shape.gen, inv_dual, Signature.ColourDuality.dualWord_cons,
      Signature.ColourDuality.dualWord_nil, Signature.ColourDuality.pivotal_dual,
      psig_right_cross, psig_left_cross]
    region_tac
  obtain ⟨cupR', hcupR', hcupRL'⟩ :=
    biadjW_right_unit_isDiag (zigzags RD k) _ ((pres RD k).genCod _ hu) rfl
  obtain ⟨capR, hcapR, hcapRL⟩ :=
    biadjW_right_counit_isDiag (zigzags RD k) _ ((pres RD k).genDom _ hu) rfl
  obtain ⟨cup'', hcup'', hcupL''⟩ :=
    biadjW_left_unit_isDiag (zigzags RD k) _ ((pres RD k).genCod _ hu) rfl
  obtain ⟨cap'', hcap'', hcapL''⟩ :=
    biadjW_left_counit_isDiag (zigzags RD k) _ ((pres RD k).genDom _ hu) rfl
  rw [isCyclic_diag_iff _ _ cupR' hcupR' capR hcapR cup'' hcup'' cap'' hcap''] at hβ
  obtain ⟨dcup, hdcup, hdcupL⟩ :=
    biadjW_left_unit_isDiag (zigzags RD k) _ ((pres RD k).genDom _ hg) rfl
  obtain ⟨dcap', hdcap', hdcapL⟩ :=
    biadjW_left_counit_isDiag (zigzags RD k) _ ((pres RD k).genCod _ hg) rfl
  obtain ⟨dcupR, hdcupR, hdcupRL⟩ :=
    biadjW_right_unit_isDiag (zigzags RD k) _ ((pres RD k).genDom _ hg) rfl
  obtain ⟨dcapR', hdcapR', hdcapRL⟩ :=
    biadjW_right_counit_isDiag (zigzags RD k) _ ((pres RD k).genCod _ hg) rfl
  refine (isCyclic_diag_iff _ _ dcup hdcup dcap' hdcap' dcupR hdcupR dcapR' hdcapR'
    (genDiag _ hg)).2 ?_
  have d₁ : ((pres RD k).genDom _ hg).obj.word =
      [⟨dn j, sh RD (dn i) + (sh RD (up i) + (sh RD (up j) + ν))⟩,
        ⟨dn i, sh RD (up i) + (sh RD (up j) + ν)⟩] := rfl
  have d₂ : ((pres RD k).genCod _ hg).obj.word =
      [⟨dn i, sh RD (dn j) + (sh RD (up i) + (sh RD (up j) + ν))⟩,
        ⟨dn j, sh RD (up i) + (sh RD (up j) + ν)⟩] := rfl
  have d₃ : ((pres RD k).dualHom (inv RD).toColourDuality.pivotal
      ((pres RD k).genCod _ hg)).obj = ((pres RD k).genDom _ hu).obj := by
    show (⟨_, _⟩ : Obj (psig RD)) = ⟨_, _⟩
    rw [d₂]
    simp only [psig_right_cross, psig_left_cross, psig_cod_cross, psig_dom_cross, wd_cons, wd_nil,
      wt_cons, wt_nil, Signature.ColourDuality.dualWord_cons, Signature.ColourDuality.dualWord_nil,
      Signature.ColourDuality.pivotal_dual, inv_dual, List.nil_append, List.cons_append,
      Letter.dual_mk, Bool.not_false]
    region_tac
  have d₄ : ((pres RD k).dualHom (inv RD).toColourDuality.pivotal
      ((pres RD k).genDom _ hg)).obj = ((pres RD k).genCod _ hu).obj := by
    show (⟨_, _⟩ : Obj (psig RD)) = ⟨_, _⟩
    rw [d₁]
    simp only [psig_right_cross, psig_left_cross, psig_cod_cross, psig_dom_cross, wd_cons, wd_nil,
      wt_cons, wt_nil, Signature.ColourDuality.dualWord_cons, Signature.ColourDuality.dualWord_nil,
      Signature.ColourDuality.pivotal_dual, inv_dual, List.nil_append, List.cons_append,
      Letter.dual_mk, Bool.not_false]
    region_tac
  refine diag_eq_transfer _ _ _ _ _ d₃ d₄ ?_ ?_ hβ
  all_goals
    simp only [layers_rightRotateD, layers_leftRotateD, hdcupL, hdcapL, hcupRL', hcapRL, hdcupRL,
      hdcapRL, hcupL'', hcapL'', d₁, d₂, u₁, u₂, d₃, d₄]
    simp only [genDiag, cupLayers, capLayers, cupRLayers, capRLayers, Diagram.layers_layer,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.map_append,
      List.append_nil, Layer.wl, Layer.wr, Diagram.layers_cast, genDom, genCod]
    simp only [wt_cons, wt_nil, wd_cons, wd_nil, List.cons_append, List.nil_append,
      Letter.dual_mk, Bool.not_true, Bool.not_false, inv_dual,
      Signature.ColourDuality.dualWord_cons, Signature.ColourDuality.dualWord_nil,
      Signature.ColourDuality.pivotal_dual, psig_right_cross, psig_left_cross, psig_dom_cross,
      psig_cod_cross]
    region_tac

/-- Every generator of the base signature (dots and crossings, upward and downward) is cyclic
for the biadjunctions of its boundary words. -/
theorem gen_isCyclic (g : (sig0 RD).Gen) (hg : (psig RD).GenValid (.gen g)) :
    IsCyclic (biadj (biadjColour RD k) ((pres RD k).genDom (.gen g) hg))
      (biadj (biadjColour RD k) ((pres RD k).genCod (.gen g) hg)) ((pres RD k).gen2 (.gen g) hg) := by
  rcases g with ⟨⟨⟨_ | _, i⟩, r⟩⟩ | ⟨_ | _, i, j, ν⟩
  · exact downdot_isCyclic RD k i r hg
  · exact updot_isCyclic RD k i r hg
  · exact downcross_isCyclic RD k i j ν hg
  · exact upcross_isCyclic RD k i j ν hg

/-- **All 2-morphisms of `U` are cyclic** (KL III Definition 3.1, "All 2-morphisms are cyclic
with respect to the above biadjoint structure. This is ensured by the relations (3.3) and
(`eq_cyclic_cross-gen`)"): for every 2-morphism `θ : x ⟶ x'` of `U`, its right mate and its
left mate (the rotations of `θ` by the nested cups and caps on the right and on the left) agree.
This is derived from the cyclicity of the generators (`gen_isCyclic`) by the rotation invariance
theorem of the pivotal extension. -/
theorem isCyclic {l m : U RD k} {x x' : l ⟶ m} (θ : x ⟶ x') :
    IsCyclic (biadjWord RD k x) (biadjWord RD k x') θ :=
  pivotal_isCyclic (inv RD) (pres RD k) (zigzags RD k) (gen_isCyclic RD k) θ

/-- The pivotal structure on `U`: duals are the dual words, and every 2-morphism is cyclic. -/
abbrev pivotal : StringDiagrams.Pivotal (U RD k) :=
  pivotalStructure (inv RD) (pres RD k) (zigzags RD k) (gen_isCyclic RD k)

end Categorification.KL3.Diagram
