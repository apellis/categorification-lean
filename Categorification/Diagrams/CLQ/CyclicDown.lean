/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.Presentation
import Categorification.Diagrams.KL3.Cyclic

/-!
# Cyclicity of the dots of `U_Q(g)`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Definition 1.1 (`eq_cyclic_dot`): the dot relations of `U_Q(g)` are those of
KL III (arXiv:0807.3250v1, eq. (3.3)), so the dots are cyclic for the biadjunctions given by the
cups and caps, as in `Categorification.Diagrams.KL3.Cyclic`.

## Main results

* `CLQ.updot_isCyclic`, `CLQ.downdot_isCyclic`: the upward and downward dots of
  `CLQ.pres RD k S` are cyclic.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Biadjunction

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (S : CL.CLScalars C k)

/-- **The upward dot of `U_Q(g)` is cyclic** (CL Definition 1.1, `eq_cyclic_dot`): its two
mates for the biadjunction `E_{+i} 1_ν ⊣⊢ E_{-i} 1_{ν+i_X}` agree (both are the downward dot). -/
theorem updot_isCyclic (i : I) (ν : X) (hg : (psig RD).GenValid (.gen (.dot ⟨up i, ν⟩))) :
    IsCyclic (biadj (biadjColour RD k S) ((pres RD k S).genDom _ hg))
      (biadj (biadjColour RD k S) ((pres RD k S).genCod _ hg)) ((pres RD k S).gen2 _ hg) := by
  rw [isCyclic_biadj_iff_single (biadjColour RD k S) (c := ⟨up i, ν⟩) (c' := ⟨up i, ν⟩) rfl rfl]
  refine (isCyclic_diag_iff (biadjColour RD k S ((pres RD k S).genDom _ hg) ⟨up i, ν⟩ rfl)
    (biadjColour RD k S ((pres RD k S).genCod _ hg) ⟨up i, ν⟩ rfl) _ rfl _ rfl _ rfl _ rfl
    (genDiag _ hg)).2 ?_
  have ha : (⟨ν, [(inv RD).dual ⟨up i, ν⟩]⟩ : Obj (psig RD)) = ob RD (sh RD (up i) + ν) [dn i] :=
    Obj.ext (by simp [ob]) rfl
  rw [(pres RD k S).diag_eq_of_layers_eq' _ (rotDotR RD i (sh RD (up i) + ν)) ha ha ?_,
    (pres RD k S).diag_eq_of_layers_eq' _ (rotDotL RD i (sh RD (up i) + ν)) ha ha ?_]
  · congr 2
    exact ((pres RD k S).diag_eq_of_rel (.inr (.cycDotR i _)) rfl).trans
      ((pres RD k S).diag_eq_of_rel (.inr (.cycDotL i _)) rfl).symm
  · simp [rotDotL, genDiag, layList, lay, Layer.wl, Layer.wr, Pivotal.cupD, Pivotal.capD,
      pivotalCupsCaps, genDom, genCod, inv_dual, Shape.gen, psig, Signature.pivotal, sig0,
      Signature.ColourDuality.dualWord, Letter.dual]
  · simp [rotDotR, genDiag, layList, lay, Layer.wl, Layer.wr, Pivotal.cupD, Pivotal.capD,
      pivotalCupsCaps, genDom, genCod, inv_dual, Shape.gen, psig, Signature.pivotal, sig0,
      Signature.ColourDuality.dualWord, Letter.dual]

/-- **The downward dot of `U_Q(g)` is cyclic**: it is the mate of the upward dot
(`eq_cyclic_dot`), and mates of cyclic 2-morphisms are cyclic. -/
theorem downdot_isCyclic (i : I) (μ : X) (hg : (psig RD).GenValid (.gen (.dot ⟨dn i, μ⟩))) :
    IsCyclic (biadj (biadjColour RD k S) ((pres RD k S).genDom _ hg))
      (biadj (biadjColour RD k S) ((pres RD k S).genCod _ hg)) ((pres RD k S).gen2 _ hg) := by
  obtain ⟨ν, rfl⟩ : ∃ ν, μ = sh RD (up i) + ν := ⟨sh RD (dn i) + μ, by simp⟩
  have hu := genValid_updot RD i ν
  have hα := (isCyclic_biadj_iff_single (biadjColour RD k S) (c := ⟨up i, ν⟩) (c' := ⟨up i, ν⟩)
    rfl rfl _).1 (updot_isCyclic RD k S i ν hu)
  have hβ := hα.rightMate
  have ha : (⟨ν, [(inv RD).dual ⟨up i, ν⟩]⟩ : Obj (psig RD)) = ob RD (sh RD (up i) + ν) [dn i] :=
    Obj.ext (by simp [ob]) rfl
  have hb : (⟨sh RD (dn i) + (sh RD (up i) + ν), [⟨dn i, sh RD (up i) + ν⟩]⟩ : Obj (psig RD)) =
      ⟨ν, [(inv RD).dual ⟨up i, ν⟩]⟩ := Obj.ext (by simp) rfl
  rw [show (pres RD k S).gen2 _ hu = (pres RD k S).diag (genDiag _ hu) from rfl,
    rightMate_diag _ _ _ rfl _ rfl] at hβ
  rw [(pres RD k S).diag_eq_of_layers_eq' _ (rotDotR RD i (sh RD (up i) + ν)) ha ha ?_,
    (pres RD k S).diag_eq_of_rel (.inr (.cycDotR i _)) rfl,
    ← (pres RD k S).diag_eq_of_layers_eq' (Diagram.cast (genDiag _ hg) hb hb)
        (downDot RD i (sh RD (up i) + ν)) ha ha rfl] at hβ
  swap
  · simp [rotDotR, genDiag, layList, lay, Layer.wl, Layer.wr, Pivotal.cupD, Pivotal.capD,
      pivotalCupsCaps, genDom, genCod, inv_dual, Shape.gen, psig, Signature.pivotal, sig0,
      Signature.ColourDuality.dualWord, Letter.dual]
  rw [isCyclic_diag_iff _ _ _ rfl _ rfl _ rfl _ rfl] at hβ
  rw [isCyclic_biadj_iff_single (biadjColour RD k S) (c := ⟨dn i, sh RD (up i) + ν⟩)
    (c' := ⟨dn i, sh RD (up i) + ν⟩) rfl rfl]
  refine (isCyclic_diag_iff
    (biadjColour RD k S ((pres RD k S).genDom _ hg) ⟨dn i, sh RD (up i) + ν⟩ rfl)
    (biadjColour RD k S ((pres RD k S).genCod _ hg) ⟨dn i, sh RD (up i) + ν⟩ rfl) _ rfl _ rfl
    _ rfl _ rfl (genDiag _ hg)).2 ?_
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

end Categorification.KL3.Diagram.CLQ
