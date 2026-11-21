/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.RescaleR

/-!
# `U_Q(g)` with `r_i = 1`, as the base of the spanning argument for general scalars

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, Definition 1.1. The files in `Categorification.Diagrams.CLQ` carry out the
spanning argument of M. Khovanov, A. D. Lauda, arXiv:0807.3250v1, Propositions 3.6 and 3.10
(`Categorification.Diagrams.KL3.Lemma39`) for `U_Q(g)` with arbitrary scalars `t`, `s`; the
scalars `r` are normalized to `1` (`CL.equivWithRone`, CL's Remark after `eq_r3_hard-gen`,
item 1). They follow the files of `Categorification.Diagrams.KL3` with the same names; where a
relation of `U_Q(g)` differs from KL III's (the mixed relations carry `t_{ij}`, the
`Q`-cyclicity of crossings carries `t_{ij}`, and `ψ^2 = Q_{ij}(x, y)` has the general
polynomial `qCL S`), the statements are those of `U_Q(g)`.

## Main definitions

* `pres RD k S`: `U_Q(g)` for the scalars `S.withRone`, with `U`, `zigzags`, `biadjColour`,
  `strandE`, `strandF`, `biadjEF`, `biadjWord` as in `Categorification.Diagrams.KL3.Presentation`.
* `lin_relation`: the relations of `pres RD k S` that are KL III's relations.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Biadjunction

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (S : CL.CLScalars C k)

/-- `U_Q(g)` for the scalars `S` with `r` normalized to `1`. -/
def pres : Presentation.{w, max u v} (psig RD) k := CL.presCL RD k S.withRone

/-- The strict bicategory of `pres RD k S`. -/
abbrev U : Type v := (pres RD k S).Bicat

theorem zigzags : (pres RD k S).PivotalZigzags (inv RD).toColourDuality :=
  CL.zigzags RD k S.withRone

/-- The biadjunctions of all strands, given by the cups and caps. -/
abbrev biadjColour : ColourBiadjunctions (pres RD k S) (inv RD).toColourDuality.pivotal :=
  Presentation.pivotalBiadj (inv RD) (pres RD k S) (zigzags RD k S)

/-- The object `λ`. -/
abbrev wtObj (lam : X) : U RD k S := ⟨lam⟩

/-- The 1-morphism `E_{+i} 1_λ`. -/
abbrev strandE (i : I) (lam : X) : (⟨sh RD (up i) + lam⟩ : U RD k S) ⟶ ⟨lam⟩ :=
  (pres RD k S).colourHom (⟨up i, lam⟩ : Col I X)

/-- The 1-morphism `E_{-i} 1_{λ+i_X}`: the dual of `strandE`. -/
abbrev strandF (i : I) (lam : X) : (⟨lam⟩ : U RD k S) ⟶ ⟨sh RD (up i) + lam⟩ :=
  (pres RD k S).dualHom (inv RD).toColourDuality.pivotal (strandE RD k S i lam)

theorem strandF_obj (i : I) (lam : X) :
    (strandF RD k S i lam).obj = ⟨lam, [⟨dn i, sh RD (up i) + lam⟩]⟩ := rfl

/-- `1_{λ+i_X} E_{+i} 1_λ` and `1_λ E_{-i} 1_{λ+i_X}` are biadjoint. -/
abbrev biadjEF (i : I) (lam : X) : strandE RD k S i lam ⊣⊢ strandF RD k S i lam :=
  biadjColour RD k S (strandE RD k S i lam) ⟨up i, lam⟩ rfl

theorem biadjEF_left_unit (i : I) (lam : X) :
    (biadjEF RD k S i lam).left.unit =
      (pres RD k S).diag (Pivotal.cupD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X)) := rfl

theorem biadjEF_left_counit (i : I) (lam : X) :
    (biadjEF RD k S i lam).left.counit =
      (pres RD k S).diag (Pivotal.capD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X)) := rfl

/-- Every 1-morphism is biadjoint to its dual word, by nested cups and caps. -/
abbrev biadjWord {l m : U RD k S} (x : l ⟶ m) :
    x ⊣⊢ (pres RD k S).dualHom (inv RD).toColourDuality.pivotal x :=
  biadj (biadjColour RD k S) x

/-- The relations of `pres RD k S`. -/
theorem lin_relationCL (r : Rel RD) : (pres RD k S).lin (CL.relationCL RD k S.withRone r) = 0 :=
  (pres RD k S).lin_rel_self (.inr r)

/-- The polynomials `Q` do not involve the scalars `r`. -/
theorem qCL_withRone : CL.qCL S.withRone = CL.qCL S := rfl

/-- A relation of `pres RD k S` whose `U_Q(g)` form with `r = 1` is the KL III relation. -/
theorem lin_relation_of (r : Rel RD) (h : CL.relationCL RD k S.withRone r = relation k r) :
    (pres RD k S).lin (relation k r) = 0 :=
  h ▸ lin_relationCL RD k S r

theorem relationCL_curlR (i : I) (lam : X) :
    CL.relationCL RD k S.withRone (.curlR i lam) = relation k (.curlR i lam) := by
  show LinDiagram.of (curlR RD i lam) - ((S.withRone.r i : kˣ) : k) • curlRHS RD k i lam =
    LinDiagram.of (curlR RD i lam) - curlRHS RD k i lam
  rw [CL.CLScalars.withRone_r, Units.val_one, one_smul]

theorem relationCL_curlL (i : I) (μ : X) :
    CL.relationCL RD k S.withRone (.curlL i μ) = relation k (.curlL i μ) := by
  show LinDiagram.of (curlL RD i μ) - ((S.withRone.r i : kˣ) : k) • curlLHS RD k i μ =
    LinDiagram.of (curlL RD i μ) - curlLHS RD k i μ
  rw [CL.CLScalars.withRone_r, Units.val_one, one_smul]

theorem relationCL_decompEF (i : I) (lam : X) :
    CL.relationCL RD k S.withRone (.decompEF i lam) = relation k (.decompEF i lam) := by
  show LinDiagram.of (𝟙 _) + (((S.withRone.r i)⁻¹ : kˣ) : k) ^ 2 •
      LinDiagram.of (crossl RD i i lam ≫ crossr RD i i lam) - decompEFSum RD k i lam =
    LinDiagram.of (𝟙 _) + LinDiagram.of (crossl RD i i lam ≫ crossr RD i i lam) -
      decompEFSum RD k i lam
  rw [CL.CLScalars.withRone_r, inv_one, Units.val_one, one_pow, one_smul]

theorem relationCL_decompFE (i : I) (lam : X) :
    CL.relationCL RD k S.withRone (.decompFE i lam) = relation k (.decompFE i lam) := by
  show LinDiagram.of (𝟙 _) + (((S.withRone.r i)⁻¹ : kˣ) : k) ^ 2 •
      LinDiagram.of (crossr RD i i lam ≫ crossl RD i i lam) - decompFESum RD k i lam =
    LinDiagram.of (𝟙 _) + LinDiagram.of (crossr RD i i lam ≫ crossl RD i i lam) -
      decompFESum RD k i lam
  rw [CL.CLScalars.withRone_r, inv_one, Units.val_one, one_pow, one_smul]

/-- The KLR relations of `pres RD k S` on upward strands are those for the polynomials
`qCL S`. -/
theorem rel_klr (μ : X) (r : KLR.Diagram.Rel I) :
    (pres RD k S).rel (.inr (.klr μ r)) = upLin RD k μ (KLR.Diagram.relation k (CL.qCL S) r) := by
  show upLin RD k μ (CL.relationR k (CL.qCL S) (fun c => ((S.withRone.r c : kˣ) : k)) r) = _
  have e : (fun c => ((S.withRone.r c : kˣ) : k)) = fun _ => 1 := by
    funext c; rw [CL.CLScalars.withRone_r, Units.val_one]
  rw [e, CL.relationR_one]

theorem lin_relation_klr (μ : X) (r : KLR.Diagram.Rel I) :
    (pres RD k S).lin (upLin RD k μ (KLR.Diagram.relation k (CL.qCL S) r)) = 0 := by
  rw [← rel_klr]; exact (pres RD k S).lin_rel_self _

end Categorification.KL3.Diagram.CLQ
