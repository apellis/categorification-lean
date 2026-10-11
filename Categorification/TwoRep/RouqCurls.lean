/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqFakeBubbles
import Categorification.TwoRep.RouqCurlSums

/-!
# Actual normalized CL curl consumers

The original ungraded `RouqFamily.genImg` kills both actual CL curl relations, with
**local normalization `(Sc.r i : k) = 1`**. All other scalar data remain arbitrary.
The upward crossing and both derived adjunctions are unchanged. In particular this is
not unrestricted-scalar soundness: rescaling the source generators is a separate theorem.

Both right-hand sides are the original finite sums of recursive fake bubbles.
Only preadditive, linear Hom categories and linear whiskering are used; no grading,
zero objects, finiteness, mixed inversion, or presentation relations are assumed.
Decompositions and aggregate presentation soundness are separate.

Cautis–Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §2.6, the extended single-colour curl relations.
-/

noncomputable section
namespace Categorification.Diagrams.BicatInterp
open CategoryTheory Bicategory StringDiagrams
universe w₁ w₂ u₀ u₁ u₂ v₂
variable {S : Signature.{u₀, u₁, u₂}} {C : Type w₁} [Bicategory.{w₂, v₂} C]
  {M : Model S C} (G : GenImg M) {s t : S.Region} {u : Obj S} {v : List S.Colour}
  (hu : S.ok u.start u.word) (hue : S.endR u.start u.word = s) (hvv : S.ok t v)

private theorem curl_admissibleChain_whisker (ls : List (Layer S)) :
    ∀ (lw : List (Layer S)) (_hl : lw = ls.map (·.whisker u v)) (a a' b : Obj S)
      (_e : a' = a.whisker u v) (hc : Chain a ls b)
      (hcw : Chain a' lw (b.whisker u v)) (ha : Cond s t a)
      (hb : Cond s t b) (hwa : Cond u.start (S.endR t v) a')
      (hwb : Cond u.start (S.endR t v) (b.whisker u v))
      (φ : fw u.start a'.word (S.endR t v) hwa.1 hwa.2.1 ⟶
        fw t v (S.endR t v) hvv rfl ≫ (fw s a.word t ha.1 ha.2.1 ≫ fw u.start u.word s hu hue))
      (ψ : fw t v (S.endR t v) hvv rfl ≫ (fw s b.word t hb.1 hb.2.1 ≫ fw u.start u.word s hu hue) ⟶
        fw u.start (b.whisker u v).word (S.endR t v) hwb.1 hwb.2.1),
      admissibleChain G a' lw (b.whisker u v) hcw hwa hwb =
        M.lift.map₂ φ ≫
          midK M (fw t v (S.endR t v) hvv rfl) (fw u.start u.word s hu hue)
            (admissibleChain G a ls b hc ha hb) ≫ M.lift.map₂ ψ := by
  induction ls with
  | nil =>
    intro lw hl a a' b e hc hcw ha hb hwa hwb φ ψ
    simp only [List.map_nil] at hl
    subst hl
    obtain rfl : a = b := hc
    obtain rfl : a' = a.whisker u v := hcw
    simp only [admissibleChain, eqToHom_refl, midK_id, Category.id_comp,
      ← PrelaxFunctor.map₂_comp]
    rw [lift_map₂_eq M (φ ≫ ψ) (𝟙 _), PrelaxFunctor.map₂_id]
  | cons L ls ih =>
    intro lw hl a a' b e hc hcw ha hb hwa hwb φ ψ
    cases lw with
    | nil => simp at hl
    | cons Lw lsw => ?_
    simp only [List.map_cons, List.cons.injEq] at hl
    obtain ⟨rfl, hls⟩ := hl
    obtain ⟨hv, rfl, hc'⟩ := hc
    obtain ⟨hvw, hwd, hcw'⟩ := hcw
    have hLw : Cond u.start (S.endR t v) (L.whisker u v).dom := hwd ▸ hwa
    have hcod : Cond s t L.cod := ha.cod hv
    have ec : (L.whisker u v).cod = L.cod.whisker u v := Layer.whisker_cod L u v
    have ed : (L.whisker u v).dom = L.dom.whisker u v := Layer.whisker_dom L u v
    dsimp only [admissibleChain]
    rw [ih lsw hls L.cod (L.whisker u v).cod b ec hc' hcw' hcod hb (hLw.cod hvw) hwb
      (eqToHom (fw_eq (congrArg Obj.word ec) _ _ _ _) ≫ (splitW hu hue hvv L.cod hcod).hom) ψ,
      coreC_whisker G hu hue hvv hv ha hvw hLw
        (eqToHom (fw_eq (congrArg Obj.word ed) _ _ _ _) ≫ (splitW hu hue hvv L.dom ha).hom)
        ((splitW hu hue hvv L.cod hcod).inv ≫ eqToHom (fw_eq (congrArg Obj.word ec).symm _ _ _ _))]
    erw [eqToHom_lift M (fw_eq (congrArg Obj.word hwd.symm) _ _ _ _)]
    simp only [eqToHom_refl, Category.id_comp, midK_comp, Category.assoc]
    rw [← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp_assoc,
      lift_map₂_eq M (_ ≫ _) φ, lift_map₂_eq M (_ ≫ _) (𝟙 _), PrelaxFunctor.map₂_id,
      Category.id_comp]
section Linear
variable {k : Type*} [CommRing k] [∀ a b : C, Preadditive (a ⟶ b)]
  [∀ a b : C, Linear k (a ⟶ b)]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear k]

omit [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear k] in
private theorem curl_map_single {s t : S.Region} {a b : Obj S}
    (ha : Cond s t a) (hb : Cond s t b) (d : a ⟶ b) (r : k) :
    admissibleMap G ha hb (Finsupp.single d r) =
      r • admissibleChain G a d.1 b d.2 ha hb := by
  exact Finsupp.linearCombination_single _ _ _

private theorem curl_map_whisker {a b : Obj S}
    (hw : a.WhiskerOK u v) (ha : Cond s t a) (hb : Cond s t b)
    (hwa : Cond u.start (S.endR t v) (a.whisker u v))
    (hwb : Cond u.start (S.endR t v) (b.whisker u v)) (f : LinDiagram k a b) :
    admissibleMap G hwa hwb (LinDiagram.whisker f u v hw) =
      M.lift.map₂ (splitW hu hue hvv a ha).hom ≫
        midK M (fw t v (S.endR t v) hvv rfl) (fw u.start u.word s hu hue)
          (admissibleMap G ha hb f) ≫ M.lift.map₂ (splitW hu hue hvv b hb).inv := by
  induction f using (Finsupp.induction_linear (ι := a ⟶ b) (M := k)) with
  | zero =>
    erw [LinDiagram.whisker_zero, map_zero, map_zero]
    simp only [Limits.zero_comp, Limits.comp_zero, midK_zero]
  | add f g hf hg =>
    erw [LinDiagram.whisker_add, map_add, map_add]
    simp only [Preadditive.add_comp, Preadditive.comp_add, midK_add, hf, hg]
  | single d r =>
    erw [LinDiagram.whisker_single, curl_map_single, curl_map_single]
    simp only [Linear.smul_comp, Linear.comp_smul, midK_smul]
    congr 1
    exact curl_admissibleChain_whisker G hu hue hvv d.1 _ rfl a (a.whisker u v) b rfl d.2
      (Diagram.whisker d u v hw).2 ha hb hwa hwb _ _

omit [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear k] in
private theorem curl_map_cast {s t : S.Region} {a b a' b' : Obj S}
    (f : LinDiagram k a b) (ea : a = a') (eb : b = b')
    (ha : Cond s t a) (hb : Cond s t b) (ha' : Cond s t a') (hb' : Cond s t b') :
    admissibleMap G ha' hb' (LinDiagram.cast f ea eb) =
      eqToHom (admissibleWord_eq ea.symm ha' ha) ≫ admissibleMap G ha hb f ≫
        eqToHom (admissibleWord_eq eb hb hb') := by
  subst ea eb
  simp only [LinDiagram.cast_rfl, eqToHom_refl, Category.id_comp, Category.comp_id]
end Linear
end Categorification.Diagrams.BicatInterp


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

/-- The admissible upward strand, with its original outer regions. -/
abbrev curlUp (i : I) (μ : X) : Admissible (S := psig RD) (sh RD (up i) + μ) μ :=
  ⟨ob RD μ [up i], ⟨⟨rfl, trivial⟩, rfl, rfl⟩⟩

private abbrev curlE (i : I) (μ : X) : fo (S := psig RD) μ ⟶ fo (sh RD (up i) + μ) :=
  FreeBicategory.Hom.of (⟨⟨up i, μ⟩, rfl, rfl⟩ :
    rq (S := psig RD) μ ⟶ rq (sh RD (up i) + μ))
private abbrev curlF (i : I) (μ : X) : fo (S := psig RD) (sh RD (up i) + μ) ⟶ fo μ :=
  FreeBicategory.Hom.of (⟨⟨dn i, sh RD (up i) + μ⟩, rfl, sh_dn_add_sh_up i μ⟩ :
    rq (S := psig RD) (sh RD (up i) + μ) ⟶ rq μ)

/-- The actual left-curl diagram uses the unchanged upward crossing. -/
theorem curl_left_image (i : I) (μ : X) :
    (S.interp Sc (sh RD (up i) + μ) μ).map
      (ObjectProperty.homMk (X := curlUp i μ) (Y := curlUp i μ)
        (KL3.Diagram.curlL RD i μ)) =
    curlEG (S.adj i (cross_up_reg i (sh RD (up i) + μ))).unit
      (S.adjL i (cross_up_reg i (sh RD (up i) + μ))).counit
      (S.cross i i (cross_up_reg i μ) (cross_up_reg i (sh RD (up i) + μ))
        (cross_up_reg i μ) (cross_up_reg i (sh RD (up i) + μ))) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, curlUp, KL3.Diagram.curlL, mkD,
    Diagram.layers_mk, layList_cons, layList_nil, lay, Shape.gen, wd_cons, wd_nil,
    wt_cons, wt_nil, List.nil_append, List.cons_append, Shape.dom]
  simp only [show ∀ j : I, (dn j).dual = up j from fun _ => rfl]
  dsimp only [up, dn] at *
  generalize_proofs
  generalize hy : sh RD ((false, i) : Letter I) +
    (sh RD ((true, i) : Letter I) + (sh RD ((true, i) : Letter I) + μ)) = y at *
  obtain rfl : y = sh RD ((true, i) : Letter I) + μ := by
    rw [← hy]; exact sh_dn_add_sh_up i _
  conv_lhs =>
    change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
      coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _
  erw [eqToHom_word (M := S.model) ?w0 _]
  erw [eqToHom_word (M := S.model) ?w1 _]
  erw [eqToHom_word (M := S.model) ?w2 _]
  · unfold coreC core
    dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
      Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen,
      wd_cons, wd_nil, wt_cons, wt_nil, inv_dual]
    dsimp only [fw]
    refine (curlL_key S.model (em := curlE i μ) (ep := curlE i (sh RD (up i) + μ))
      (rp := curlF i (sh RD (up i) + μ))
      (S.adj i (cross_up_reg i (sh RD (up i) + μ))).unit
      (S.adjL i (cross_up_reg i (sh RD (up i) + μ))).counit
      (S.cross i i (cross_up_reg i μ) (cross_up_reg i (sh RD (up i) + μ))
        (cross_up_reg i μ) (cross_up_reg i (sh RD (up i) + μ)))
      (eqToIso ?e1) (eqToIso ?e2) (eqToIso ?e3) (eqToIso ?e4) _ ?hg1
      (eqToIso ?e5) (eqToIso ?e6) (eqToIso ?e7) (eqToIso ?e8) _ ?hg2
      (eqToIso ?e9) (eqToIso ?e10) (eqToIso ?e11) (eqToIso ?e12) _ ?hg3
      _ _ _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _)).trans ?fin
    case e4 => exact comp_of_congr rfl (congrArg (Col.mk (up i)) (sh_dn_add_sh_up i _)) rfl
    case e1 | e2 | e3 | e5 | e6 | e7 | e8 | e9 | e10 | e11 | e12 => rfl
    case hg1 | hg3 =>
      erw [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom, lift_map₂_eqToHom]
      erw [eqToHom_refl, Category.id_comp, eqToHom_refl, Category.comp_id]
      rfl
    case hg2 =>
      erw [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom]
      erw [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    case fin =>
      erw [PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
      rfl
  all_goals
    change (_ : List (Col I X)) = _
    dsimp [Layer.cod, Layer.dom, ob, psig, Signature.pivotal, sig0, KL3.Diagram.inv,
      Letter.dual, wd, KL3.Diagram.wt]
    all_goals first | rfl | (simp only [hy]; rfl)
private abbrev curlRm (i : I) (μ : X) : fo (S := psig RD) μ ⟶ fo (sh RD (dn i) + μ) :=
  FreeBicategory.Hom.of (⟨⟨dn i, μ⟩, rfl, rfl⟩ :
    rq (S := psig RD) μ ⟶ rq (sh RD (dn i) + μ))
private abbrev curlEm (i : I) (μ : X) : fo (S := psig RD) (sh RD (dn i) + μ) ⟶ fo μ :=
  FreeBicategory.Hom.of (⟨⟨up i, sh RD (dn i) + μ⟩, rfl, sh_up_add_sh_dn i μ⟩ :
    rq (S := psig RD) (sh RD (dn i) + μ) ⟶ rq μ)

omit [AdditiveWhiskering B] in
private lemma curl_cross_congr (i : I) {l n m n₂ : X} (hn : n = n₂)
    (h₁ : l + RD.iX i = n) (h₂ : n + RD.iX i = m)
    (h₁' : l + RD.iX i = n₂) (h₂' : n₂ + RD.iX i = m)
    (e₁ : S.E i h₁' ≫ S.E i h₂' = S.E i h₁ ≫ S.E i h₂)
    (e₂ : S.E i h₁ ≫ S.E i h₂ = S.E i h₁' ≫ S.E i h₂') :
    eqToHom e₁ ≫ S.cross i i h₁ h₂ h₁ h₂ ≫ eqToHom e₂ =
      S.cross i i h₁' h₂' h₁' h₂' := by
  subst hn
  simp

/-- The actual right-curl diagram uses the unchanged upward crossing. -/
theorem curl_right_image (i : I) (μ : X) :
    (S.interp Sc (sh RD (up i) + μ) μ).map
      (ObjectProperty.homMk (X := curlUp i μ) (Y := curlUp i μ)
        (KL3.Diagram.curlR RD i μ)) =
    curlG (S.adjL i (cross_dn_reg i μ)).unit (S.adj i (cross_dn_reg i μ)).counit
      (S.cross i i (cross_dn_reg i μ) (cross_up_reg i μ)
        (cross_dn_reg i μ) (cross_up_reg i μ)) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [ObjectProperty.homMk, curlUp, KL3.Diagram.curlR, mkD,
    Diagram.layers_mk, layList_cons, layList_nil, lay, Shape.gen, wd_cons, wd_nil,
    wt_cons, wt_nil, List.nil_append, List.cons_append, Shape.dom]
  simp only [show ∀ j : I, (up j).dual = dn j from fun _ => rfl,
    show ∀ j : I, (dn j).dual = up j from fun _ => rfl]
  dsimp only [up, dn] at *
  generalize_proofs
  generalize hx : sh RD ((true, i) : Letter I) + (sh RD ((false, i) : Letter I) + μ) = x at *
  obtain rfl : μ = x := by rw [← hx]; exact (sh_up_add_sh_dn i _).symm
  conv_lhs =>
    change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫
      coreC (S.genImg Sc) _ _ ≫ eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _
  erw [eqToHom_word (M := S.model) ?w0 _]
  erw [eqToHom_word (M := S.model) ?w1 _]
  erw [eqToHom_word (M := S.model) ?w2 _]
  · unfold coreC core
    dsimp only [Signature.endR, psig_colourTgt, psig_colourSrc, Signature.pivotal_dom_cup,
      Signature.pivotal_cod_cup, Signature.pivotal_dom_cap, Signature.pivotal_cod_cap,
      Signature.pivotal_dom_gen, Signature.pivotal_cod_gen, Signature.pivotal_left_cup,
      Signature.pivotal_right_cup, Signature.pivotal_left_cap, Signature.pivotal_right_cap,
      Signature.pivotal_left_gen, Signature.pivotal_right_gen,
      wd_cons, wd_nil, wt_cons, wt_nil, inv_dual]
    dsimp only [fw]
    refine (curl_key S.model (r := curlRm i μ) (e := curlEm i μ) (e' := curlE i μ)
      (S.adjL i (cross_dn_reg i μ)).unit (S.adj i (cross_dn_reg i μ)).counit
      (S.cross i i (cross_dn_reg i μ) (cross_up_reg i μ)
        (cross_dn_reg i μ) (cross_up_reg i μ))
      (eqToIso ?e1) (eqToIso ?e2) (eqToIso ?e3) (eqToIso ?e4) _ ?hg1
      (eqToIso ?e5) (eqToIso ?e6) (eqToIso ?e7) (eqToIso ?e8) _ ?hg2
      (eqToIso ?e9) (eqToIso ?e10) (eqToIso ?e11) (eqToIso ?e12) _ ?hg3
      _ _ _ _ _ _ _ _ _ _ (𝟙 _) (𝟙 _)).trans ?fin
    case e4 => exact comp_of_congr rfl (congrArg (Col.mk (dn i)) hx) rfl
    case e7 | e8 => exact comp_of_congr hx rfl (congrArg (Col.mk (up i)) hx)
    case e1 | e2 | e3 | e5 | e6 | e9 | e10 | e11 | e12 => rfl
    case hg1 | hg3 =>
      erw [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom, lift_map₂_eqToHom]
      erw [eqToHom_refl, Category.id_comp, eqToHom_refl, Category.comp_id]
      rfl
    case hg2 =>
      erw [eqToIso.inv, eqToIso.hom, lift_map₂_eqToHom, lift_map₂_eqToHom]
      dsimp only [genImg]
      exact S.curl_cross_congr i hx _ _ _ _ _ _
    case fin =>
      erw [PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
      rfl
  all_goals
    change (_ : List (Col I X)) = _
    dsimp [Layer.cod, Layer.dom, ob, psig, Signature.pivotal, sig0, KL3.Diagram.inv,
      Letter.dual, wd, KL3.Diagram.wt]
    all_goals first | rfl | (simp only [hx]; rfl)

private theorem curl_dot (i : I) (μ : X) :
    (S.interp Sc (sh RD (up i) + μ) μ).map
      (ObjectProperty.homMk (X := curlUp i μ) (Y := curlUp i μ)
        (mkD RD μ [([], .dot (up i), [])] ⟨rfl, rfl⟩)) = S.dot i (cross_up_reg i μ) := by
  change admissibleChain (S.genImg Sc) _ _ _ _ _ _ = _
  dsimp only [mkD, Diagram.layers_mk, layList_cons, layList_nil, lay, Shape.gen,
    wd_cons, wd_nil, wt_cons, wt_nil, List.nil_append, List.cons_append, Shape.dom,
    ObjectProperty.homMk, curlUp]
  conv_lhs => change eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _
  erw [eqToHom_word (M := S.model) (by rfl) _]
  unfold coreC core
  refine (chain1_key S.model ((λ_ _) ≪≫ (ρ_ _)) ((λ_ _) ≪≫ (ρ_ _))
    _ _ _ _ _ (𝟙 _) (𝟙 _)).trans ?_
  erw [layerAt_whole, PrelaxFunctor.map₂_id, Category.id_comp, Category.comp_id]
  rfl

private theorem curl_dots (i : I) (μ : X) (n : ℕ) :
    (S.interp Sc (sh RD (up i) + μ) μ).map
      (ObjectProperty.homMk (X := curlUp i μ) (Y := curlUp i μ)
        (dots RD μ [] (up i) [] n)) = powComp (S.dot i (cross_up_reg i μ)) n := by
  induction n with
  | zero => exact (S.interp Sc _ _).map_id _
  | succ n ih =>
    have hd : dots RD μ [] (up i) [] (n + 1) =
        dots RD μ [] (up i) [] n ≫ mkD RD μ [([], .dot (up i), [])] ⟨rfl, rfl⟩ := by
      unfold dots
      erw [mkD_comp]
      congr 1
      exact List.replicate_succ'
    rw [hd]
    change (S.interp Sc _ _).map
      ((ObjectProperty.homMk (X := curlUp i μ) (Y := curlUp i μ) (dots RD μ [] (up i) [] n)) ≫
        ObjectProperty.homMk (X := curlUp i μ) (Y := curlUp i μ)
          (mkD RD μ [([], .dot (up i), [])] ⟨rfl, rfl⟩)) = _
    rw [Functor.map_comp, ih, S.curl_dot, powComp_succ]
    rfl

variable [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]

private theorem curl_bubR (i : I) (μ : X) (b : LEnd RD k (ob RD μ [])) :
    admissibleMap (S.genImg Sc) (curlUp i μ).property (curlUp i μ).property
      (bubR RD k μ [up i] b) =
    (λ_ (S.E i (cross_up_reg i μ))).inv ≫ S.bubbleHom Sc μ b ▷ S.E i (cross_up_reg i μ) ≫
      (λ_ (S.E i (cross_up_reg i μ))).hom := by
  have hw := whiskerOK_right RD μ [up i]
  have hwa := (bubbleNil (RD := RD) μ).property.whisker
    (u := ob RD μ [up i]) (curlUp i μ).property.1 rfl (v := []) trivial
  unfold bubR
  erw [curl_map_cast (S.genImg Sc) _ _ _ hwa hwa]
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  erw [curl_map_whisker (S.genImg Sc) (u := ob RD μ [up i]) (v := []) (s := μ) (t := μ)
    (curlUp i μ).property.1 rfl trivial hw
    (bubbleNil μ).property (bubbleNil μ).property hwa hwa b]
  erw [lift_map₂_eq S.model (splitW _ _ _ _ _).hom ((λ_ _).inv ≫ (λ_ _).inv),
    lift_map₂_eq S.model (splitW _ _ _ _ _).inv ((λ_ _).hom ≫ (λ_ _).hom)]
  erw [PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_comp,
    lift_map₂_leftUnitor_inv, lift_map₂_leftUnitor_inv,
    lift_map₂_leftUnitor_hom, lift_map₂_leftUnitor_hom]
  change ((λ_ (S.E i (cross_up_reg i μ))).inv ≫ (λ_ _).inv) ≫
    (𝟙 _ ◁ S.bubbleHom Sc μ b ▷ S.E i (cross_up_reg i μ)) ≫
      (λ_ _).hom ≫ (λ_ _).hom = _
  simpa only [Category.assoc] using StrongSl2.bubL_aux (S.E i (cross_up_reg i μ)) (S.bubbleHom Sc μ b)

private theorem curl_bubL (i : I) (μ : X)
    (b : LEnd RD k (ob RD (KL3.Diagram.wt RD μ [up i]) [])) :
    admissibleMap (S.genImg Sc) (curlUp i μ).property (curlUp i μ).property
      (bubL RD k μ [up i] b) =
    (ρ_ (S.E i (cross_up_reg i μ))).inv ≫ S.E i (cross_up_reg i μ) ◁
      S.bubbleHom Sc (sh RD (up i) + μ) b ≫ (ρ_ (S.E i (cross_up_reg i μ))).hom := by
  have hw := whiskerOK_left RD μ [up i]
  have hwa := (bubbleNil (RD := RD) (sh RD (up i) + μ)).property.whisker
    (u := ob RD (sh RD (up i) + μ) []) trivial rfl (v := wd RD μ [up i]) (curlUp i μ).property.1
  unfold bubL
  erw [curl_map_cast (S.genImg Sc) _ _ _ hwa hwa]
  erw [eqToHom_refl, Category.id_comp, Category.comp_id]
  erw [curl_map_whisker (S.genImg Sc) (u := ob RD (sh RD (up i) + μ) [])
    (v := wd RD μ [up i]) (s := sh RD (up i) + μ) (t := sh RD (up i) + μ)
    trivial rfl (curlUp i μ).property.1 hw
    (bubbleNil (RD := RD) _).property (bubbleNil (RD := RD) _).property hwa hwa b]
  erw [lift_map₂_eq S.model (splitW _ _ _ _ _).hom ((ρ_ _).inv ≫ _ ◁ (λ_ _).inv),
    lift_map₂_eq S.model (splitW _ _ _ _ _).inv (_ ◁ (λ_ _).hom ≫ (ρ_ _).hom)]
  erw [PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_comp,
    lift_map₂_rightUnitor_inv, lift_map₂_rightUnitor_hom,
    lift_map₂_whiskerLeft, lift_map₂_whiskerLeft,
    lift_map₂_leftUnitor_inv, lift_map₂_leftUnitor_hom]
  change ((ρ_ (S.E i (cross_up_reg i μ))).inv ≫ _ ◁ (λ_ _).inv) ≫
    (S.E i (cross_up_reg i μ) ◁ S.bubbleHom Sc (sh RD (up i) + μ) b ▷ 𝟙 _) ≫
      _ ◁ (λ_ _).hom ≫ (ρ_ _).hom = _
  simpa only [Category.assoc] using StrongSl2.bubR_aux (S.E i (cross_up_reg i μ))
    (S.bubbleHom Sc (sh RD (up i) + μ) b)

private theorem curlR_interpreted (i : I) (μ : X) :
    admissibleMap (k := k) (S.genImg Sc) (curlUp i μ).property (curlUp i μ).property
      (LinDiagram.of (KL3.Diagram.curlR RD i μ)) =
    admissibleMap (S.genImg Sc) (curlUp i μ).property (curlUp i μ).property
      (curlRHS RD k i μ) := by
  erw [admissibleMap_of]
  erw [S.curl_right_image]
  rw [S.adjL_eq i (sub_add_cancel (sh RD (dn i) + μ) (RD.iX i))
    (cross_dn_reg i μ) (cross_up_reg i μ)]
  change curlG (S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).cupL _ _ = _
  rw [(S.loc i (cross_dn_reg i μ) (cross_up_reg i μ)).curlG_bubble_sum]
  unfold curlRHS
  rw [map_neg, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [admissibleMap_comp (S.genImg Sc) (curlUp i μ).property
    (curlUp i μ).property (curlUp i μ).property]
  erw [admissibleMap_of, S.curl_dots, S.curl_bubR]
  rw [S.bubble_cwL Sc i (cross_dn_reg i μ) (cross_up_reg i μ)]
  rfl

private theorem curlL_interpreted (i : I) (μ : X) :
    admissibleMap (k := k) (S.genImg Sc) (curlUp i μ).property (curlUp i μ).property
      (LinDiagram.of (KL3.Diagram.curlL RD i μ)) =
    admissibleMap (S.genImg Sc) (curlUp i μ).property (curlUp i μ).property
      (curlLHS RD k i μ) := by
  erw [admissibleMap_of]
  erw [S.curl_left_image]
  rw [S.adjL_eq i (cross_up_reg i μ) (cross_up_reg i (sh RD (up i) + μ)) rfl]
  change curlEG _ (S.loc i (cross_up_reg i μ) (cross_up_reg i (sh RD (up i) + μ))).capL _ = _
  rw [(S.loc i (cross_up_reg i μ) (cross_up_reg i (sh RD (up i) + μ))).curlEG_bubble_sum]
  unfold curlLHS
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [admissibleMap_comp (S.genImg Sc) (curlUp i μ).property
    (curlUp i μ).property (curlUp i μ).property]
  erw [admissibleMap_of, S.curl_dots, S.curl_bubL]
  erw [S.bubble_ccwL Sc i (cross_up_reg i μ) (cross_up_reg i (sh RD (up i) + μ))]
  exact (StrongSl2.rbub_comm _ _).symm

/-- The original right-curl CL relation vanishes when this colour has `rᵢ = 1`. -/
theorem curlR_rel (i : I) (μ : X) (hr : (Sc.r i : k) = 1) :
    admissibleMap (S.genImg Sc) (curlUp i μ).property (curlUp i μ).property
      (CL.relationCL RD k Sc (.curlR i μ)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _
    (LinDiagram.of (KL3.Diagram.curlR RD i μ) - (Sc.r i : k) • curlRHS RD k i μ) = 0
  rw [hr, one_smul, map_sub, S.curlR_interpreted, sub_self]

/-- The original left-curl CL relation vanishes when this colour has `rᵢ = 1`. -/
theorem curlL_rel (i : I) (μ : X) (hr : (Sc.r i : k) = 1) :
    admissibleMap (S.genImg Sc) (curlUp i μ).property (curlUp i μ).property
      (CL.relationCL RD k Sc (.curlL i μ)) = 0 := by
  change admissibleMap (S.genImg Sc) _ _
    (LinDiagram.of (KL3.Diagram.curlL RD i μ) - (Sc.r i : k) • curlLHS RD k i μ) = 0
  rw [hr, one_smul, map_sub, S.curlL_interpreted, sub_self]

end RouqFamily
end Categorification.TwoRep
