/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqZig
import Categorification.Diagrams.CL.NoMix

/-!
# Single-colour cyclicity in the admissible Rouquier interpretation

Brundan, arXiv:1501.00350v1, Theorem 5.3, equations (5.6), (5.8), and its final
cyclicity deduction. Both rotated dot diagrams and both rotated same-colour
crossing diagrams have the prescribed downward-generator image. The left
adjunction and cyclicity are derived from Rouquier's inverses, not additional data.

The headline results `cycDotR_rel`, `cycDotL_rel`, `cycCrossR_rel`, and
`cycCrossL_rel` kill the actual linear relations used by `presNM`. These particular
relations do not involve `Sc.r`; this is not a soundness assertion for the other
relations at arbitrary scalars. There is no zero-object, grading, or finiteness
hypothesis. Mixed upward KLR equations, the other non-mixed relation families,
presentation descent, and horizontal coherence are separate from these results.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp
universe w v u u₁
variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [AdditiveWhiskering B]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y}
namespace RouqFamily
variable (S : RouqFamily (B := B) RD) (Sc : CL.CLScalars C k)
attribute [local irreducible] KL3.Diagram.sh

theorem adjL_counit_congr (i : I) {a b b' : X} (h : b = b')
    (p : a + RD.iX i = b) (p' : a + RD.iX i = b')
    (e : S.E i p' ≫ S.F i p' = S.E i p ≫ S.F i p) :
    eqToHom e ≫ (S.adjL i p).counit = (S.adjL i p').counit := by
  subst h; simp

/-- The right rotation of the dot acts by the actual downward dot. -/
theorem cycDotR (i : I) (μ : X) :
    (S.interp Sc (sh RD (dn i) + μ) μ).map
      (ObjectProperty.homMk (X := colourAdmissible ⟨dn i, μ⟩)
        (Y := colourAdmissible ⟨dn i, μ⟩) (rotDotR RD i μ)) =
    (S.interp Sc (sh RD (dn i) + μ) μ).map
      (ObjectProperty.homMk (X := colourAdmissible ⟨dn i, μ⟩)
        (Y := colourAdmissible ⟨dn i, μ⟩) (downDot RD i μ)) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ =
    admissibleChain (S.genImg Sc) _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk, colourAdmissible, rotDotR, downDot, mkD,
    Diagram.layers_mk, layList_cons, layList_nil, lay, Shape.gen, wd_cons, wd_nil,
    wt_cons, wt_nil, List.nil_append, List.cons_append, Shape.dom, Letter.dual, up, dn,
    Bool.not_false, Bool.not_true]
  generalize_proofs
  generalize hx : sh RD (up i) + (sh RD (dn i) + μ) = x at *
  have hxμ : x = μ := by rw [← hx]; exact sh_up_add_sh_dn i μ
  subst hxμ
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ =
    eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _
  erw [eqToHom_word ?w0 _, eqToHom_word ?w1 _, eqToHom_word ?w2 _]
  · unfold coreC core
    dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
      Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen, inv_dual, Letter.dual, up, dn]
    refine rot_key S.model
      (a := fo (S := psig RD) x) (b := fo (S := psig RD) (sh RD (dn i) + x))
      (r := FreeBicategory.Hom.of (⟨⟨dn i, x⟩, rfl, rfl⟩ :
        rq (S := psig RD) x ⟶ rq (sh RD (dn i) + x)))
      (e := FreeBicategory.Hom.of (⟨⟨up i, sh RD (dn i) + x⟩, rfl,
        sh_up_add_sh_dn i x⟩ : rq (S := psig RD) (sh RD (dn i) + x) ⟶ rq x))
      (S.adjL i (dn_reg i rfl rfl)) (S.dot i (dn_reg i rfl rfl))
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (whiskerRightIso (eqToIso (hom_of_congr (congrArg (Col.mk (dn i)) hx))) _) _ ?_
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?_
      (Iso.refl _) (Iso.refl _)
        (eqToIso (by refine comp_of_congr hx rfl ?_; exact congrArg (Col.mk (dn i)) hx))
        (Iso.refl _) _ ?_
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?_
      _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [whiskerRightIso_hom, eqToIso.hom, lift_map₂_whiskerRight,
        lift_map₂_eqToHom, eqToHom_refl, id_whiskerRight, Category.comp_id]
      rfl
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      rfl
    · simp only [Iso.refl_hom, PrelaxFunctor.map₂_id]
      erw [Category.comp_id]
      erw [eqToIso.inv, lift_map₂_eqToHom]
      exact S.adjL_counit_congr i hx _ _ _
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      rfl
  case w2 =>
    change ([⟨dn i, x⟩, ⟨up i, sh RD (dn i) + x⟩, ⟨dn i, x⟩] : List (Col I X)) =
      [⟨dn i, sh RD (up i) + (sh RD (dn i) + x)⟩,
        ⟨up i, sh RD (dn i) + x⟩, ⟨dn i, x⟩]
    rw [hx]
  case w1 =>
    change ([⟨dn i, x⟩, ⟨up i, sh RD (dn i) + x⟩,
      ⟨dn i, sh RD (up i) + (sh RD (dn i) + x)⟩] : List (Col I X)) =
        [⟨dn i, x⟩, ⟨up i, sh RD (dn i) + x⟩, ⟨dn i, x⟩]
    rw [hx]
  case w0 => rfl

/-- The left rotation agrees with the right mate, by Rouquier dot cyclicity. -/
theorem cycDotL (i : I) (μ : X) :
    (S.interp Sc (sh RD (dn i) + μ) μ).map
      (ObjectProperty.homMk (X := colourAdmissible ⟨dn i, μ⟩)
        (Y := colourAdmissible ⟨dn i, μ⟩) (rotDotL RD i μ)) =
    (S.interp Sc (sh RD (dn i) + μ) μ).map
      (ObjectProperty.homMk (X := colourAdmissible ⟨dn i, μ⟩)
        (Y := colourAdmissible ⟨dn i, μ⟩) (downDot RD i μ)) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ =
    admissibleChain (S.genImg Sc) _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk, colourAdmissible, rotDotL, downDot, mkD,
    Diagram.layers_mk, layList_cons, layList_nil, lay, Shape.gen, wd_cons, wd_nil,
    wt_cons, wt_nil, List.nil_append, List.cons_append, Shape.dom, Letter.dual, up, dn,
    Bool.not_false, Bool.not_true]
  change admissibleChain (S.genImg Sc) _
    [⟨sh RD (dn i) + μ, [], .cup ⟨dn i, sh RD (up i) + (sh RD (dn i) + μ)⟩,
        [⟨dn i, μ⟩]⟩,
      ⟨sh RD (dn i) + (sh RD (up i) + (sh RD (dn i) + μ)),
        [⟨dn i, sh RD (up i) + (sh RD (dn i) + μ)⟩],
        .gen (.dot ⟨up i, sh RD (dn i) + μ⟩), [⟨dn i, μ⟩]⟩,
      ⟨sh RD (dn i) + (sh RD (up i) + (sh RD (dn i) + μ)),
        [⟨dn i, sh RD (up i) + (sh RD (dn i) + μ)⟩], .cap ⟨dn i, μ⟩, []⟩]
    _ _ _ _ = _
  generalize_proofs
  generalize hx : sh RD (up i) + (sh RD (dn i) + μ) = x at *
  have hxμ : x = μ := by rw [← hx]; exact sh_up_add_sh_dn i μ
  subst hxμ
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ =
    eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _
  erw [eqToHom_word ?w0 _, eqToHom_word ?w1 _]
  · unfold coreC core
    dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
      Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen, inv_dual, Letter.dual, up, dn]
    refine rotL_key S.model
      (a := fo (S := psig RD) x) (b := fo (S := psig RD) (sh RD (dn i) + x))
      (r := FreeBicategory.Hom.of (⟨⟨dn i, x⟩, rfl, rfl⟩ :
        rq (S := psig RD) x ⟶ rq (sh RD (dn i) + x)))
      (e := FreeBicategory.Hom.of (⟨⟨up i, sh RD (dn i) + x⟩, rfl,
        sh_up_add_sh_dn i x⟩ : rq (S := psig RD) (sh RD (dn i) + x) ⟶ rq x))
      (S.adj i (dn_reg i rfl rfl)) (S.dot i (dn_reg i rfl rfl))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?_
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?_
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?_
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?_
      _ _ _ _ _ _ _ _ _ _ _ _ _ _
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      rfl
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      rfl
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      rfl
    · simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      exact S.dotDn_eq_rightMate i _
  all_goals rfl

/-- The actual right dot-cyclicity relation of `presNM` vanishes. -/
theorem cycDotR_rel (i : I) (μ : X) :
    admissibleMap (S.genImg Sc) (colourAdmissible ⟨dn i, μ⟩).property
      (colourAdmissible ⟨dn i, μ⟩).property
      (CL.relationCL RD k Sc (.cycDotR i μ)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _
    (LinDiagram.of (rotDotR RD i μ) - LinDiagram.of (downDot RD i μ)) = 0
  erw [map_sub, admissibleMap_of, admissibleMap_of]
  exact sub_eq_zero.mpr (S.cycDotR Sc i μ)

/-- The actual left dot-cyclicity relation of `presNM` vanishes. -/
theorem cycDotL_rel (i : I) (μ : X) :
    admissibleMap (S.genImg Sc) (colourAdmissible ⟨dn i, μ⟩).property
      (colourAdmissible ⟨dn i, μ⟩).property
      (CL.relationCL RD k Sc (.cycDotL i μ)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _
    (LinDiagram.of (rotDotL RD i μ) - LinDiagram.of (downDot RD i μ)) = 0
  erw [map_sub, admissibleMap_of, admissibleMap_of]
  exact sub_eq_zero.mpr (S.cycDotL Sc i μ)

/-- The admissible word at its actual left and right boundary regions. -/
abbrev obAdmissible (μ : X) (ls : List (Letter I)) :
    Admissible (S := psig RD) (KL3.Diagram.wt RD μ ls : X) μ :=
  ⟨ob RD μ ls, ⟨ob_wf RD μ ls, ob_endR RD μ ls, rfl⟩⟩

private theorem dual_up (i : I) : Letter.dual (up i) = dn i := rfl
private theorem dual_dn (i : I) : Letter.dual (dn i) = up i := rfl
private theorem sig0_colourSrc (c : Col I X) : (sig0 RD).colourSrc c = sh RD c.l + c.r := rfl
private theorem sig0_colourTgt (c : Col I X) : (sig0 RD).colourTgt c = c.r := rfl
private theorem sig0_dom_cross (e : Bool) (i j : I) (ν : X) :
    (sig0 RD).dom (.cross e i j ν) = wd RD ν [(e, i), (e, j)] := rfl
private theorem sig0_cod_cross (e : Bool) (i j : I) (ν : X) :
    (sig0 RD).cod (.cross e i j ν) = wd RD ν [(e, j), (e, i)] := rfl

omit [AdditiveWhiskering B] in
private theorem cross_congr (i : I) {a b b' c : X} (h : b = b')
    (p : a + RD.iX i = b) (q : b + RD.iX i = c)
    (p' : a + RD.iX i = b') (q' : b' + RD.iX i = c)
    (e : S.E i p' ≫ S.E i q' = S.E i p ≫ S.E i q)
    (e' : S.E i p ≫ S.E i q = S.E i p' ≫ S.E i q') :
    eqToHom e ≫ S.cross i i p q p q ≫ eqToHom e' = S.cross i i p' q' p' q' := by
  subst h; simp

/-- The same-colour left crossing rotation has the prescribed downward image. -/
theorem cycCrossL (i : I) (μ : X) :
    (S.interp Sc (KL3.Diagram.wt RD μ [dn i, dn i]) μ).map
      (ObjectProperty.homMk (X := obAdmissible μ [dn i, dn i])
        (Y := obAdmissible μ [dn i, dn i]) (rotCrossL RD i i μ)) =
    (S.interp Sc (KL3.Diagram.wt RD μ [dn i, dn i]) μ).map
      (ObjectProperty.homMk (X := obAdmissible μ [dn i, dn i])
        (Y := obAdmissible μ [dn i, dn i]) (downCross RD i i μ)) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ =
    admissibleChain (S.genImg Sc) _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk, obAdmissible, rotCrossL, downCross, mkD,
    Diagram.layers_mk, layList_cons, layList_nil, lay, Shape.gen, wd_cons, wd_nil,
    wt_cons, wt_nil, List.nil_append, List.cons_append, Shape.dom, dual_dn]
  generalize_proofs
  generalize hy : sh RD (up i) +
    (sh RD (dn i) + (sh RD (dn i) + μ)) = y at *
  have hyμ : y = sh RD (dn i) + μ := by rw [← hy]; exact sh_up_add_sh_dn i _
  subst hyμ
  generalize hx : sh RD (up i) + (sh RD (dn i) + μ) = x at *
  have hxμ : x = μ := by rw [← hx]; exact sh_up_add_sh_dn i μ
  subst hxμ
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ =
    eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _
  erw [eqToHom_word ?w0 _]
  try erw [eqToHom_word ?w1 _]
  try erw [eqToHom_word ?w2 _]
  try erw [eqToHom_word ?w3 _]
  try erw [eqToHom_word ?w4 _]
  try erw [eqToHom_word ?w5 _]
  · unfold coreC core
    dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
      Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen, sig0_dom_cross, sig0_cod_cross,
      wd_cons, wd_nil, wt_cons, wt_nil, inv_dual, dual_up, sig0_colourTgt, sig0_colourSrc]
    refine rot2L_key S.model
      (a := fo (S := psig RD) x) (b := fo (S := psig RD) (sh RD (dn i) + x))
      (c := fo (S := psig RD) (sh RD (dn i) + (sh RD (dn i) + x)))
      (r₁ := FreeBicategory.Hom.of (⟨⟨dn i, x⟩, rfl, rfl⟩ :
        rq (S := psig RD) x ⟶ rq (sh RD (dn i) + x)))
      (e₁ := FreeBicategory.Hom.of (⟨⟨up i, sh RD (dn i) + x⟩, rfl,
          sh_up_add_sh_dn i x⟩ :
        rq (S := psig RD) (sh RD (dn i) + x) ⟶ rq x))
      (r₂ := FreeBicategory.Hom.of (⟨⟨dn i, sh RD (dn i) + x⟩, rfl, rfl⟩ :
        rq (S := psig RD) (sh RD (dn i) + x) ⟶
          rq (sh RD (dn i) + (sh RD (dn i) + x))))
      (e₂ := FreeBicategory.Hom.of (⟨⟨up i, sh RD (dn i) +
          (sh RD (dn i) + x)⟩, rfl, sh_up_add_sh_dn (RD := RD) i (sh RD (dn i) + x)⟩ :
        rq (S := psig RD) (sh RD (dn i) + (sh RD (dn i) + x)) ⟶
          rq (sh RD (dn i) + x)))
      (S.adj i (dn_reg i rfl rfl)) (S.adj i (dn_reg i rfl rfl))
      (S.cross i i (dn_reg i rfl rfl) (dn_reg i rfl rfl)
        (dn_reg i rfl rfl) (dn_reg i rfl rfl))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg1
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg2
      (Iso.refl _) (Iso.refl _)
      (eqToIso (by refine comp_of_congr hy rfl ?_; exact congrArg (Col.mk (up i)) hy))
      (eqToIso (by refine comp_of_congr hy rfl ?_; exact congrArg (Col.mk (up i)) hy)) _ ?hg3
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg4
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg5
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg6
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    case hg1 | hg2 | hg4 | hg5 =>
      simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      rfl
    case hg3 =>
      erw [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom, lift_map₂_eqToHom]
      exact S.cross_congr i hy _ _ _ _ _ _
    case hg6 =>
      simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      exact S.crossDn_self Sc i _ _
  case w0 | w1 | w4 => rfl
  case w2 =>
    change ([⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩, ⟨up i, sh RD (dn i) + x⟩,
      ⟨up i, sh RD (dn i) + (sh RD (dn i) + x)⟩,
      ⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩] : List (Col I X)) =
        [⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩,
          ⟨up i, sh RD (up i) + (sh RD (dn i) + (sh RD (dn i) + x))⟩,
          ⟨up i, sh RD (dn i) + (sh RD (dn i) + x)⟩,
          ⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩]
    rw [hy]
  case w3 =>
    change ([⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩,
      ⟨up i, sh RD (up i) + (sh RD (dn i) + (sh RD (dn i) + x))⟩,
      ⟨up i, sh RD (dn i) + (sh RD (dn i) + x)⟩,
      ⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩] : List (Col I X)) =
        [⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩, ⟨up i, sh RD (dn i) + x⟩,
          ⟨up i, sh RD (dn i) + (sh RD (dn i) + x)⟩,
          ⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩]
    rw [hy]

/-- The same-colour right crossing rotation has the prescribed downward image. -/
theorem cycCrossR (i : I) (μ : X) :
    (S.interp Sc (KL3.Diagram.wt RD μ [dn i, dn i]) μ).map
      (ObjectProperty.homMk (X := obAdmissible μ [dn i, dn i])
        (Y := obAdmissible μ [dn i, dn i]) (rotCrossR RD i i μ)) =
    (S.interp Sc (KL3.Diagram.wt RD μ [dn i, dn i]) μ).map
      (ObjectProperty.homMk (X := obAdmissible μ [dn i, dn i])
        (Y := obAdmissible μ [dn i, dn i]) (downCross RD i i μ)) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ =
    admissibleChain (S.genImg Sc) _ _ _ _ _ _
  dsimp only [ObjectProperty.homMk, obAdmissible, rotCrossR, downCross, mkD,
    Diagram.layers_mk, layList_cons, layList_nil, lay, Shape.gen, wd_cons, wd_nil,
    wt_cons, wt_nil, List.nil_append, List.cons_append, Shape.dom, dual_up]
  generalize_proofs
  generalize hy : sh RD (up i) +
    (sh RD (dn i) + (sh RD (dn i) + μ)) = y at *
  have hyμ : y = sh RD (dn i) + μ := by rw [← hy]; exact sh_up_add_sh_dn i _
  subst hyμ
  generalize hx : sh RD (up i) + (sh RD (dn i) + μ) = x at *
  have hxμ : x = μ := by rw [← hx]; exact sh_up_add_sh_dn i μ
  subst hxμ
  change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
    coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ =
    eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _
  erw [eqToHom_word ?w0 _]
  try erw [eqToHom_word ?w1 _]
  try erw [eqToHom_word ?w2 _]
  try erw [eqToHom_word ?w3 _]
  try erw [eqToHom_word ?w4 _]
  try erw [eqToHom_word ?w5 _]
  · unfold coreC core
    dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
      Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen, sig0_dom_cross, sig0_cod_cross,
      wd_cons, wd_nil, wt_cons, wt_nil, inv_dual, dual_up, sig0_colourTgt, sig0_colourSrc]
    refine rot2_key S.model
      (a := fo (S := psig RD) x) (b := fo (S := psig RD) (sh RD (dn i) + x))
      (c := fo (S := psig RD) (sh RD (dn i) + (sh RD (dn i) + x)))
      (r₁ := FreeBicategory.Hom.of (⟨⟨dn i, x⟩, rfl, rfl⟩ :
        rq (S := psig RD) x ⟶ rq (sh RD (dn i) + x)))
      (e₁ := FreeBicategory.Hom.of (⟨⟨up i, sh RD (dn i) + x⟩, rfl,
          sh_up_add_sh_dn i x⟩ :
        rq (S := psig RD) (sh RD (dn i) + x) ⟶ rq x))
      (r₂ := FreeBicategory.Hom.of (⟨⟨dn i, sh RD (dn i) + x⟩, rfl, rfl⟩ :
        rq (S := psig RD) (sh RD (dn i) + x) ⟶
          rq (sh RD (dn i) + (sh RD (dn i) + x))))
      (e₂ := FreeBicategory.Hom.of (⟨⟨up i, sh RD (dn i) +
          (sh RD (dn i) + x)⟩, rfl, sh_up_add_sh_dn (RD := RD) i (sh RD (dn i) + x)⟩ :
        rq (S := psig RD) (sh RD (dn i) + (sh RD (dn i) + x)) ⟶
          rq (sh RD (dn i) + x)))
      (S.adjL i (dn_reg i rfl rfl)) (S.adjL i (dn_reg i rfl rfl))
      (S.cross i i (dn_reg i rfl rfl) (dn_reg i rfl rfl)
        (dn_reg i rfl rfl) (dn_reg i rfl rfl))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (whiskerRightIso (eqToIso (hom_of_congr ?hc1)) _)
      _ ?hg1
      (Iso.refl _) (α_ _ _ _) (Iso.refl _) (whiskerRightIso (eqToIso (hom_of_congr ?hc2)) _)
      _ ?hg2
      (Iso.refl _) (Iso.refl _)
      (eqToIso (by refine comp_of_congr hy rfl ?_; exact congrArg (Col.mk (up i)) hy))
      (eqToIso (by refine comp_of_congr hy rfl ?_; exact congrArg (Col.mk (up i)) hy)) _ ?hg3
      (Iso.refl _) (Iso.refl _)
      (eqToIso (by refine comp_of_congr hx rfl ?_; exact congrArg (Col.mk (dn i)) hx))
      (Iso.refl _) _ ?hg4
      (Iso.refl _) (Iso.refl _)
      (eqToIso (by refine comp_of_congr hy rfl ?_; exact congrArg (Col.mk (dn i)) hy))
      (Iso.refl _) _ ?hg5
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) _ ?hg6
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    case hc1 => exact congrArg (Col.mk (dn i)) hx
    case hc2 => exact congrArg (Col.mk (dn i)) hy
    case hg1 | hg2 =>
      simp only [Iso.refl_inv, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [whiskerRightIso_hom, eqToIso.hom, lift_map₂_whiskerRight,
        lift_map₂_eqToHom, eqToHom_refl, id_whiskerRight, Category.comp_id]
      rfl
    case hg3 =>
      erw [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom, lift_map₂_eqToHom]
      exact S.cross_congr i hy _ _ _ _ _ _
    case hg4 =>
      simp only [Iso.refl_hom, PrelaxFunctor.map₂_id]
      erw [Category.comp_id, eqToIso.inv, lift_map₂_eqToHom]
      exact S.adjL_counit_congr i hx _ _ _
    case hg5 =>
      simp only [Iso.refl_hom, PrelaxFunctor.map₂_id]
      erw [Category.comp_id, eqToIso.inv, lift_map₂_eqToHom]
      exact S.adjL_counit_congr i hy _ _ _
    case hg6 =>
      simp only [Iso.refl_inv, Iso.refl_hom, PrelaxFunctor.map₂_id, Category.id_comp]
      erw [Category.comp_id]
      change S.crossDn Sc i i _ _ _ _ = _
      rw [crossDn, Sc.t_self, inv_one, Units.val_one, one_smul]
      rfl
  case w0 => rfl
  case w1 =>
    change ([⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩, ⟨up i, sh RD (dn i) + x⟩,
      ⟨dn i, sh RD (up i) + (sh RD (dn i) + x)⟩] : List (Col I X)) =
        [⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩, ⟨up i, sh RD (dn i) + x⟩, ⟨dn i, x⟩]
    rw [hx]
  case w2 =>
    change ([⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩, ⟨up i, sh RD (dn i) + x⟩,
      ⟨up i, sh RD (dn i) + (sh RD (dn i) + x)⟩,
      ⟨dn i, sh RD (up i) + (sh RD (dn i) + (sh RD (dn i) + x))⟩, ⟨dn i, x⟩] :
      List (Col I X)) =
        [⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩,
          ⟨up i, sh RD (up i) + (sh RD (dn i) + (sh RD (dn i) + x))⟩,
          ⟨up i, sh RD (dn i) + (sh RD (dn i) + x)⟩,
          ⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩]
    rw [hy]
  case w3 =>
    change ([⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩,
      ⟨up i, sh RD (up i) + (sh RD (dn i) + (sh RD (dn i) + x))⟩,
      ⟨up i, sh RD (dn i) + (sh RD (dn i) + x)⟩,
      ⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩] : List (Col I X)) =
        [⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, sh RD (up i) + (sh RD (dn i) + x)⟩,
          ⟨up i, sh RD (dn i) + x⟩, ⟨up i, sh RD (dn i) + (sh RD (dn i) + x)⟩,
          ⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩]
    rw [hx, hy]
  case w4 =>
    change ([⟨dn i, sh RD (dn i) + x⟩, ⟨up i, sh RD (dn i) + (sh RD (dn i) + x)⟩,
      ⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩] : List (Col I X)) =
        [⟨dn i, sh RD (up i) + (sh RD (dn i) + (sh RD (dn i) + x))⟩,
          ⟨up i, sh RD (dn i) + (sh RD (dn i) + x)⟩,
          ⟨dn i, sh RD (dn i) + x⟩, ⟨dn i, x⟩]
    rw [hy]

/-- The actual same-colour left crossing-cyclicity relation vanishes. -/
theorem cycCrossL_rel (i : I) (μ : X) :
    admissibleMap (S.genImg Sc) (obAdmissible μ [dn i, dn i]).property
      (obAdmissible μ [dn i, dn i]).property
      (CL.relationCL RD k Sc (.cycCrossL i i μ)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _
    ((((Sc.t i i)⁻¹ : kˣ) : k) • LinDiagram.of (rotCrossL RD i i μ) -
      LinDiagram.of (downCross RD i i μ)) = 0
  rw [Sc.t_self, inv_one, Units.val_one, one_smul]
  erw [map_sub, admissibleMap_of, admissibleMap_of]
  exact sub_eq_zero.mpr (S.cycCrossL Sc i μ)

/-- The actual same-colour right crossing-cyclicity relation vanishes. -/
theorem cycCrossR_rel (i : I) (μ : X) :
    admissibleMap (S.genImg Sc) (obAdmissible μ [dn i, dn i]).property
      (obAdmissible μ [dn i, dn i]).property
      (CL.relationCL RD k Sc (.cycCrossR i i μ)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _
    ((((Sc.t i i)⁻¹ : kˣ) : k) • LinDiagram.of (rotCrossR RD i i μ) -
      LinDiagram.of (downCross RD i i μ)) = 0
  rw [Sc.t_self, inv_one, Units.val_one, one_smul]
  erw [map_sub, admissibleMap_of, admissibleMap_of]
  exact sub_eq_zero.mpr (S.cycCrossR Sc i μ)


end RouqFamily
end Categorification.TwoRep
