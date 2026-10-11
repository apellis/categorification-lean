/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterpAdmissible

/-!
# Admissible horizontal soundness

The original admissible interpreter preserves two-sided whiskering and even
interchange. Its linear extension therefore annihilates the actual presentation
ideal, by induction over its span generators, including arbitrary pre- and
postcomposition. Inadmissible intermediate boundaries are handled by emptiness
of the source diagram Hom, not by adding zero objects to the target.

The context formula uses `splitW` and `midK`: the right word acts on the left
in the target bicategory, and the left word acts on the right. Free bicategory
coherence accounts for all associators and dependent outer-region transports.
-/

noncomputable section
namespace Categorification.Diagrams.BicatInterp
open CategoryTheory Bicategory StringDiagrams
universe w₁ w₂ u₀ u₁ u₂ v₂
variable {S : Signature.{u₀, u₁, u₂}} {C : Type w₁} [Bicategory.{w₂, v₂} C]
  {M : Model S C}

section Whisker
variable (G : GenImg M) {s t : S.Region} {u : Obj S} {v : List S.Colour}
  (hu : S.ok u.start u.word) (hue : S.endR u.start u.word = s) (hvv : S.ok t v)

/-- Admissible chain interpretation preserves two-sided horizontal contexts. -/
theorem admissibleChain_whisker (ls : List (Layer S)) :
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
    simp only [admissibleChain, eqToHom_refl, Category.id_comp]
    rw [ih lsw hls L.cod (L.whisker u v).cod b ec hc' hcw' hcod hb (hLw.cod hvw) hwb
      (eqToHom (fw_eq (congrArg Obj.word ec) _ _ _ _) ≫ (splitW hu hue hvv L.cod hcod).hom) ψ,
      coreC_whisker G hu hue hvv hv ha hvw hLw
        (eqToHom (fw_eq (congrArg Obj.word ed) _ _ _ _) ≫ (splitW hu hue hvv L.dom ha).hom)
        ((splitW hu hue hvv L.cod hcod).inv ≫ eqToHom (fw_eq (congrArg Obj.word ec).symm _ _ _ _)),
      eqToHom_word (congrArg Obj.word hwd.symm) _]
    simp only [midK_comp, Category.assoc]
    rw [← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp_assoc,
      lift_map₂_eq M (_ ≫ _) φ, lift_map₂_eq M (_ ≫ _) (𝟙 _), PrelaxFunctor.map₂_id,
      Category.id_comp]
end Whisker

/-- The actual two orders of disjoint generators agree on admissible words. -/
theorem admissibleInterp_interchange (G : GenImg M) (x : InterchangeData S) (hx : x.Valid)
    {s t : S.Region} (hc : Cond s t x.dom) (hcod : Cond s t x.cod) :
    (admissibleInterp G s t).map (ObjectProperty.homMk
      (X := ⟨x.dom, hc⟩) (Y := ⟨x.cod, hcod⟩) (InterchangeData.ghDiagram hx)) =
    (admissibleInterp G s t).map (ObjectProperty.homMk
      (X := ⟨x.dom, hc⟩) (Y := ⟨x.cod, hcod⟩) (InterchangeData.hgDiagram hx)) := by
  have hgh := (InterchangeData.ghDiagram hx).2
  have hhg := (InterchangeData.hgDiagram hx).2
  have c1 : Cond s t x.gh₁.dom := by rw [hgh.2.1]; exact hc
  have c2 : Cond s t x.gh₂.dom := by rw [hgh.2.2.2.1]; exact c1.cod hx.gh₁
  have c3 : Cond s t x.hg₁.dom := by rw [hhg.2.1]; exact hc
  have c4 : Cond s t x.hg₂.dom := by rw [hhg.2.2.2.1]; exact c3.cod hx.hg₁
  change admissibleChain G x.dom [x.gh₁, x.gh₂] x.cod hgh hc hcod =
    admissibleChain G x.dom [x.hg₁, x.hg₂] x.cod hhg hc hcod
  simp only [admissibleChain, coreC_eq]
  rw [eqToHom_word ?e0 _, eqToHom_word ?e1 _, eqToHom_word ?e2 _, eqToHom_word ?e3 _,
    eqToHom_word ?e4 _, eqToHom_word ?e5 _]
  · obtain ⟨start, g, mid, h⟩ := x
    have hs : start = S.left g := hx.gh₁.left_end
    subst hs
    have hst : S.left g = s := hc.2.2
    subst hst
    have ht : S.right h = t := Cond.right_end hx.hg₁ c3
    subst ht
    have m_ok : S.ok (S.right g) mid := ((Signature.ok_append _ _ _).1 hx.gh₁.right_ok).1
    have m_end : S.endR (S.right g) mid = S.left h := by
      have := hx.hg₁.left_end
      change S.endR (S.left g) (S.dom g ++ mid) = S.left h at this
      have hde : S.endR (S.left g) (S.dom g) = S.right g := hx.gh₁.dom_end
      rw [Signature.endR_append, hde] at this
      exact this
    exact exch_key M (G.gen h (S.left h) (S.right h) rfl rfl hx.hg₁.dom_ok hx.hg₁.dom_end hx.hg₁.cod_ok hx.hg₁.cod_end)
      (G.gen g (S.left g) (S.right g) rfl rfl hx.gh₁.dom_ok hx.gh₁.dom_end hx.gh₁.cod_ok hx.gh₁.cod_end)
      (splitIso (S.right g) mid (S.dom h) (S.left h) (S.right h) m_ok m_end hx.hg₁.dom_ok
        hx.hg₁.dom_end)
      (eqToIso (fw_nil (S.left g) trivial))
      (eqToIso (fw_nil (S.right h) trivial))
      (splitIso (S.left g) (S.cod g) mid (S.right g) (S.left h) hx.gh₁.cod_ok hx.gh₁.cod_end
        m_ok m_end)
      (eqToIso (fw_nil (S.right h) trivial))
      (splitIso (S.left g) (S.dom g) mid (S.right g) (S.left h) hx.gh₁.dom_ok hx.gh₁.dom_end
        m_ok m_end)
      (splitIso (S.right g) mid (S.cod h) (S.left h) (S.right h) m_ok m_end hx.hg₁.cod_ok
        hx.hg₁.cod_end)
      (eqToIso (fw_nil (S.left g) trivial)) _ _ _ _ _ _ _ _ _ _ _ _ _ _
  all_goals simp [InterchangeData.gh₁, InterchangeData.gh₂, InterchangeData.hg₁,
    InterchangeData.hg₂, InterchangeData.dom, InterchangeData.cod, Layer.dom, Layer.cod]
section Linear
variable {k : Type*} [CommRing k] [∀ a b : C, Preadditive (a ⟶ b)]
  [∀ a b : C, Linear k (a ⟶ b)]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear k]

/-- Horizontal contexts act by the actual target whiskerings and free coherence maps. -/
theorem admissibleMap_whisker (G : GenImg M) {s t : S.Region}
    {a b u : Obj S} {v : List S.Colour} (ha : Cond s t a) (hb : Cond s t b)
    (hu : S.ok u.start u.word) (hue : S.endR u.start u.word = s) (hvv : S.ok t v)
    (hw : a.WhiskerOK u v) (f : LinDiagram k a b) :
    admissibleMap G (ha.whisker hu hue hvv) (hb.whisker hu hue hvv)
      (LinDiagram.whisker f u v hw) =
    M.lift.map₂ (splitW hu hue hvv a ha).hom ≫
      midK M (fw t v (S.endR t v) hvv rfl) (fw u.start u.word s hu hue)
        (admissibleMap G ha hb f) ≫ M.lift.map₂ (splitW hu hue hvv b hb).inv := by
  induction f using (Finsupp.induction_linear (ι := a ⟶ b) (M := k)) with
  | zero =>
    erw [LinDiagram.whisker_zero, map_zero, map_zero, midK_zero,
      Limits.zero_comp, Limits.comp_zero]
  | add f g hf hg =>
    erw [LinDiagram.whisker_add, map_add, hf, hg, map_add, midK_add,
      Preadditive.add_comp, Preadditive.comp_add]
  | single d r =>
    erw [LinDiagram.whisker_single]
    dsimp only [admissibleMap]
    erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, midK_smul,
      Linear.smul_comp, Linear.comp_smul]
    congr 1
    exact admissibleChain_whisker G hu hue hvv d.1 _ rfl a (a.whisker u v) b rfl d.2
      (Diagram.whisker d u v hw).2 ha hb _ _ _ _

omit [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear k] in
/-- Even interchange is annihilated without zero objects. -/
theorem admissibleMap_interchange (G : GenImg M) (x : InterchangeData S) (hx : x.Valid)
    (hsign : x.sign = 1) {s t : S.Region} (ha : Cond s t x.dom) (hb : Cond s t x.cod) :
    admissibleMap (k := k) G ha hb (InterchangeData.rel k hx) = 0 := by
  rw [InterchangeData.rel, hsign, Int.cast_one, one_smul, map_sub,
    admissibleMap_of, admissibleMap_of, admissibleInterp_interchange]
  exact sub_self _

/-- No formal diagrams connect an admissible source to an inadmissible target. -/
theorem linDiagram_eq_zero_of_not_cond {s t : S.Region} {a b : Obj S}
    (ha : Cond s t a) (hb : ¬ Cond s t b) (f : LinDiagram k a b) : f = 0 := by
  apply Finsupp.ext
  intro d
  exact (hb (ha.chain d.2)).elim

/-- A killed relation remains killed in every admissible horizontal context. -/
theorem admissibleMap_whisker_eq_zero (G : GenImg M) {a b : Obj S}
    (f : LinDiagram k a b) (u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v)
    (hf : ∀ (ha : Cond a.start a.endR a) (hb : Cond a.start a.endR b),
      admissibleMap G ha hb f = 0) {s t : S.Region}
    (hwa : Cond s t (a.whisker u v)) (hwb : Cond s t (b.whisker u v)) :
    admissibleMap G hwa hwb (LinDiagram.whisker f u v hw) = 0 := by
  obtain ⟨hok, hend, hst⟩ := hwa
  change u.start = s at hst
  subst s
  have hue : S.endR u.start u.word = a.start := hw.2.1
  have hokA : S.ok a.start a.word := by
    simp only [Obj.whisker_word, Signature.ok_append, hue] at hok
    exact hok.1.2
  have ha : Cond a.start a.endR a := ⟨hokA, rfl, rfl⟩
  have ht : t = S.endR a.endR v := by
    rw [← hend]
    simp only [Obj.whisker_word, Signature.endR_append, hue]
    rfl
  subst ht
  by_cases hb : Cond a.start a.endR b
  · rw [admissibleMap_whisker G ha hb hw.1 hue hw.2.2 hw f, hf ha hb,
      midK_zero, Limits.zero_comp, Limits.comp_zero]
  · rw [linDiagram_eq_zero_of_not_cond ha hb f, LinDiagram.whisker_zero, map_zero]

omit [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear k] in
/-- Every actual imposed relation, including interchange, is annihilated. -/
theorem admissibleMap_allRel (G : GenImg M) (P : Presentation S k)
    (hrel : ∀ (i : P.Rel) {s t : S.Region} (ha : Cond s t (P.dom i))
      (hb : Cond s t (P.cod i)), admissibleMap G ha hb (P.rel i) = 0)
    (heven : ∀ g, S.odd g = false) (i : P.AllRel) {s t : S.Region}
    (ha : Cond s t i.dom) (hb : Cond s t i.cod) :
    admissibleMap G ha hb i.rel = 0 := by
  cases i with
  | user i => exact hrel i ha hb
  | interchange x hx =>
    exact admissibleMap_interchange G x hx (by simp [InterchangeData.sign, heven]) ha hb

/-- The original horizontally generated ideal lies in the admissible interpreter's kernel. -/
theorem admissibleMap_ideal (G : GenImg M) (P : Presentation S k)
    (hrel : ∀ (i : P.Rel) {s t : S.Region} (ha : Cond s t (P.dom i))
      (hb : Cond s t (P.cod i)), admissibleMap G ha hb (P.rel i) = 0)
    (heven : ∀ g, S.odd g = false) {s t : S.Region} {a b : Obj S}
    (ha : Cond s t a) (hb : Cond s t b) (f : LinDiagram k a b)
    (hf : f ∈ P.ideal a b) : admissibleMap G ha hb f = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, u, v, hw, pre, post⟩ := hf
    by_cases hd : Cond s t (i.dom.whisker u v)
    · by_cases hc : Cond s t (i.cod.whisker u v)
      · rw [admissibleMap_comp G ha hd hb, admissibleMap_comp G hd hc hb,
          admissibleMap_whisker_eq_zero G i.rel u v hw
            (fun hi hj => admissibleMap_allRel G P hrel heven i hi hj) hd hc,
          Limits.zero_comp, Limits.comp_zero]
      · rw [linDiagram_eq_zero_of_not_cond hd hc (LinDiagram.whisker i.rel u v hw),
          Limits.zero_comp, Limits.comp_zero, map_zero]
    · rw [linDiagram_eq_zero_of_not_cond ha hd pre, Limits.zero_comp, map_zero]
  | zero => exact map_zero _
  | add f g _ _ hf hg => rw [map_add, hf, hg, add_zero]
  | smul r f _ hf => rw [map_smul, hf, smul_zero]

end Linear
end Categorification.Diagrams.BicatInterp
