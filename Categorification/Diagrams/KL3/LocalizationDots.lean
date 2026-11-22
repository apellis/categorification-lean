/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Localization
import Categorification.Diagrams.KL3.Cyclic

/-!
# Inverse dots in `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, Definition 3.28
and the proof of Lemma 3.29. `U′` (`presLoc`) is `U` with the downward dot inverted and honest
bubbles with negative dots identified with fake bubbles. This file proves the local relations used
in the proof of Lemma 3.29.

* `adjLoc`: the adjunction `E_i ⊣ F_i` in `U′`; the upward and downward dots are mates
  (`conj_locUpDot`).
* `locUpInvDot`, `locUpDot_comp_locUpInvDot`, `locUpInvDot_comp_locUpDot`: the upward dot is
  invertible in `U′`, its inverse being the mate of the inverse downward dot.
* `isIso_toLoc_dg_dot`: every single-dot layer of the KL calculus, upward or downward and at any
  position, becomes invertible in `U′`.
* `inv_slide`: a slide relation `a ψ = ψ b + c` with `a`, `b` invertible gives the slide of the
  inverses.
* `toLoc_cross_comp_inv_dot_right_eq`, `toLoc_cross_comp_inv_dot_left_eq` (same colour) and
  `toLoc_cross_comp_inv_dot_right_eq_of_ne`, `toLoc_cross_comp_inv_dot_left_eq_of_ne` (distinct
  colours): inverse dots slide through upward crossings, KL III (2.5c–d) multiplied by the
  inverse dots as in the proof of Lemma 3.29.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Biadjunction Bicategory

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

instance : (lsig RD).IsEven := ⟨fun _ => rfl⟩

/-- The localization functor on classes of diagrams. -/
theorem toLoc_diag {a b : Obj (psig RD)} (d : a ⟶ b) :
    (toLoc RD k).map ((pres RD k).diag d) = (presLoc RD k).diag (inclD RD d) := by
  have h := toLoc_lin RD k (LinDiagram.of d)
  rwa [lin_of, inclLin_of, lin_of] at h

/-- A unit and counit given by diagrams satisfy the left zigzag identity as diagrams. -/
theorem diag_leftZigzagD_of_adj {S : Signature} {R : Type*} [CommRing R]
    {P : Presentation S R} [S.IsEven] {l m : P.Bicat} {x : l ⟶ m} {y : m ⟶ l} (A : x ⊣ y)
    (cup : Obj.nil l.region ⟶ x.obj.tensor y.obj) (cap : y.obj.tensor x.obj ⟶ Obj.nil m.region)
    (hu : A.unit = P.diag cup) (hc : A.counit = P.diag cap) :
    P.diag (P.leftZigzagD x y cup cap) = 𝟙 _ := by
  have h := A.left_triangle
  rw [hu, hc, leftZigzag_diag] at h
  have h' : (P.diag (P.leftZigzagD x y cup cap) : x ⟶ x) = 𝟙 x := by
    rw [← cancel_mono (ρ_ x).inv]; simpa using h
  exact h'

/-- A unit and counit given by diagrams satisfy the right zigzag identity as diagrams. -/
theorem diag_rightZigzagD_of_adj {S : Signature} {R : Type*} [CommRing R]
    {P : Presentation S R} [S.IsEven] {l m : P.Bicat} {x : l ⟶ m} {y : m ⟶ l} (A : x ⊣ y)
    (cup : Obj.nil l.region ⟶ x.obj.tensor y.obj) (cap : y.obj.tensor x.obj ⟶ Obj.nil m.region)
    (hu : A.unit = P.diag cup) (hc : A.counit = P.diag cap) :
    P.diag (P.rightZigzagD x y cup cap) = 𝟙 _ := by
  have h := A.right_triangle
  rw [hu, hc, rightZigzag_diag] at h
  have h' : (P.diag (P.rightZigzagD x y cup cap) : y ⟶ y) = 𝟙 y := by
    rw [← cancel_mono (λ_ y).inv]; simpa using h
  exact h'

/-- The strand `E_{+i} 1_λ` as a 1-morphism of `U′`. -/
abbrev locE (i : I) (lam : X) : (⟨sh RD (up i) + lam⟩ : (presLoc RD k).Bicat) ⟶ ⟨lam⟩ :=
  (presLoc RD k).colourHom (⟨up i, lam⟩ : Col I X)

/-- The strand `E_{-i} 1_{λ+i_X}` as a 1-morphism of `U′`. -/
def locF (i : I) (lam : X) : (⟨lam⟩ : (presLoc RD k).Bicat) ⟶ ⟨sh RD (up i) + lam⟩ :=
  ⟨(incl RD).obj (strandF RD k i lam).obj, (strandF RD k i lam).start_eq, (strandF RD k i lam).wf,
    (strandF RD k i lam).endR_eq⟩

/-- The conjugate (right mate) of the class of a diagram, for adjunctions whose unit and counit
are classes of diagrams, is the class of the rotated diagram. -/
theorem conjugateEquiv_diag {S : Signature} {R : Type*} [CommRing R]
    {P : Presentation S R} [S.IsEven] {l m : P.Bicat} {x x' : l ⟶ m} {y y' : m ⟶ l}
    (A : x ⊣ y) (A' : x' ⊣ y')
    (cup : Obj.nil l.region ⟶ x.obj.tensor y.obj) (hcup : A.unit = P.diag cup)
    (cap' : y'.obj.tensor x'.obj ⟶ Obj.nil m.region) (hcap : A'.counit = P.diag cap')
    (d : x.obj ⟶ x'.obj) :
    conjugateEquiv A' A (P.diag d : x ⟶ x') = P.diag (rightRotateD x x' y y' cup cap' d) := by
  rw [conjugateEquiv_apply', hcup, hcap]
  change eqToHom (congrArg P.obj (Obj.tensor_nil y'.obj l.region).symm) ≫
      P.wL y'.obj (P.diag cup) ≫
        P.wL y'.obj (P.wRAt l.region (P.diag d) y.obj x.start_eq x'.start_eq) ≫
          eqToHom (congrArg P.obj (Obj.tensor_assoc y'.obj x'.obj y.obj).symm) ≫
            P.wRAt m.region (P.diag cap') y.obj (y' ≫ x').start_eq rfl ≫
              eqToHom (congrArg P.obj (Obj.nil_tensor y.start_eq)) = _
  rw [P.wRAt_diag d _ (Bicat.Hom.composable x y),
    P.wRAt_diag cap' _ (Bicat.Hom.composable (y' ≫ x') y),
    P.wL_diag_of_composable _ cup (Bicat.Hom.composable y' (𝟙 l)),
    P.wL_diag_of_composable _ _ (Bicat.Hom.composable y' (x ≫ y))]
  simp [rightRotateD, Diagram.cast_eq, P.diag_eqToHom]

/-- The cup `1 ⟶ E_i F_i` of `U` in `U′`. -/
abbrev locCup (i : I) (lam : X) :
    Obj.nil (sh RD (up i) + lam) ⟶ (locE RD k i lam).obj.tensor (locF RD k i lam).obj :=
  inclD RD (Pivotal.cupD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X))

/-- The cap `F_i E_i ⟶ 1` of `U` in `U′`. -/
abbrev locCap (i : I) (lam : X) :
    (locF RD k i lam).obj.tensor (locE RD k i lam).obj ⟶ Obj.nil lam :=
  inclD RD (Pivotal.capD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X))

/-- **The adjunction `E_{+i} 1_λ ⊣ E_{-i} 1_{λ+i_X}` in `U′`**, with unit the cup and counit
the cap of `U` (the zigzag relations hold in `U′` because they hold in `U`). -/
def adjLoc (i : I) (lam : X) : locE RD k i lam ⊣ locF RD k i lam :=
  adjunctionOfZigzag _ _ (locCup RD k i lam) (locCap RD k i lam)
    (by
      calc (presLoc RD k).diag ((presLoc RD k).leftZigzagD _ _ (locCup RD k i lam)
              (locCap RD k i lam))
          = (presLoc RD k).diag (inclD RD ((pres RD k).leftZigzagD (strandE RD k i lam)
              (strandF RD k i lam) (Pivotal.cupD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X))
              (Pivotal.capD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X)))) :=
            (presLoc RD k).diag_eq_of_layers_eq (by
              simp [Diagram.layers_leftZigzag, LayerMap.layers_map, List.map_append,
                List.map_map]
              constructor)
        _ = 𝟙 _ := by
            rw [← toLoc_diag, diag_leftZigzagD_of_adj (biadjEF RD k i lam).left
              (Pivotal.cupD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X))
              (Pivotal.capD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X)) rfl rfl]
            exact (toLoc RD k).map_id _)
    (by
      calc (presLoc RD k).diag ((presLoc RD k).rightZigzagD _ _ (locCup RD k i lam)
              (locCap RD k i lam))
          = (presLoc RD k).diag (inclD RD ((pres RD k).rightZigzagD (strandE RD k i lam)
              (strandF RD k i lam) (Pivotal.cupD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X))
              (Pivotal.capD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X)))) :=
            (presLoc RD k).diag_eq_of_layers_eq (by
              simp [Diagram.layers_rightZigzag, LayerMap.layers_map, List.map_append,
                List.map_map]
              constructor)
        _ = 𝟙 _ := by
            rw [← toLoc_diag, diag_rightZigzagD_of_adj (biadjEF RD k i lam).left
              (Pivotal.cupD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X))
              (Pivotal.capD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X)) rfl rfl]
            exact (toLoc RD k).map_id _)


/-- The upward dot on `E_{+i} 1_λ` of `U`, as a diagram. -/
def upDot (i : I) (lam : X) : ob RD lam [up i] ⟶ ob RD lam [up i] :=
  mkD RD lam [([], .dot (up i), [])] ⟨rfl, rfl⟩

theorem locF_obj (i : I) (lam : X) :
    (incl RD).obj (ob RD (sh RD (up i) + lam) [dn i]) = (locF RD k i lam).obj :=
  Obj.ext (by simp [ob, incl, locF]) rfl

/-- The upward dot of `E_{+i} 1_λ` as a 2-morphism of `U′`. -/
abbrev locUpDot (i : I) (lam : X) : locE RD k i lam ⟶ locE RD k i lam :=
  (presLoc RD k).diag (inclD RD (upDot RD i lam))

/-- The downward dot of `E_{-i} 1_{λ+i_X}` as a 2-morphism of `U′`. -/
abbrev locDownDot (i : I) (lam : X) : locF RD k i lam ⟶ locF RD k i lam :=
  (presLoc RD k).diag (Diagram.cast (inclD RD (downDot RD i (sh RD (up i) + lam)))
    (locF_obj RD k i lam) (locF_obj RD k i lam))

/-- The inverse downward dot of `E_{-i} 1_{λ+i_X}` as a 2-morphism of `U′`. -/
abbrev locInvDot (i : I) (lam : X) : locF RD k i lam ⟶ locF RD k i lam :=
  (presLoc RD k).diag (Diagram.cast (invDotF RD i (sh RD (up i) + lam))
    (locF_obj RD k i lam) (locF_obj RD k i lam))

theorem conj_locUpDot (i : I) (lam : X) :
    conjugateEquiv (adjLoc RD k i lam) (adjLoc RD k i lam) (locUpDot RD k i lam) =
      locDownDot RD k i lam := by
  rw [conjugateEquiv_diag _ _ (locCup RD k i lam) rfl (locCap RD k i lam) rfl]
  have hU : (presLoc RD k).diag (rightRotateD _ _ _ _ (locCup RD k i lam) (locCap RD k i lam)
      (inclD RD (upDot RD i lam))) =
      (presLoc RD k).diag (inclD RD (rightRotateD (strandE RD k i lam) (strandE RD k i lam)
        (strandF RD k i lam) (strandF RD k i lam)
        (Pivotal.cupD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X))
        (Pivotal.capD (inv RD).toColourDuality (⟨up i, lam⟩ : Col I X)) (upDot RD i lam))) :=
    (presLoc RD k).diag_eq_of_layers_eq (by
      simp [layers_rightRotateD, LayerMap.layers_map, List.map_append, List.map_map]
      constructor)
  rw [hU, ← toLoc_diag]
  have ha : (strandF RD k i lam).obj = ob RD (sh RD (up i) + lam) [dn i] :=
    Obj.ext (by simp [ob]) rfl
  rw [(pres RD k).diag_eq_of_layers_eq' _ (rotDotR RD i (sh RD (up i) + lam)) ha ha ?_,
    (pres RD k).diag_eq_of_rel (.inr (.cycDotR i _)) rfl]
  · simp only [Functor.map_comp, eqToHom_map, toLoc_diag, locDownDot, diag_cast]
  · simp [rotDotR, upDot, layList, lay, Layer.wl, Layer.wr, Pivotal.cupD, Pivotal.capD,
      inv_dual, Shape.gen, psig, Signature.pivotal, sig0, Letter.dual]
    rfl

/-- Transport of the identity `f ≫ g = 1` along an equality of boundary objects. -/
theorem diag_cast_comp_diag_cast {S : Signature} {R : Type*} [CommRing R] (P : Presentation S R)
    {a a' : Obj S} (f g : a ⟶ a) (h : a = a') (hfg : P.diag f ≫ P.diag g = 𝟙 _) :
    P.diag (Diagram.cast f h h) ≫ P.diag (Diagram.cast g h h) = 𝟙 _ := by
  subst h; simpa using hfg

theorem locInvDot_comp_locDownDot (i : I) (lam : X) :
    locInvDot RD k i lam ≫ locDownDot RD k i lam = 𝟙 _ :=
  diag_cast_comp_diag_cast _ _ _ _ (invDot_comp_downDot RD k i (sh RD (up i) + lam))

theorem locDownDot_comp_locInvDot (i : I) (lam : X) :
    locDownDot RD k i lam ≫ locInvDot RD k i lam = 𝟙 _ :=
  diag_cast_comp_diag_cast _ _ _ _ (downDot_comp_invDot RD k i (sh RD (up i) + lam))

/-- The inverse of the upward dot of `E_{+i} 1_λ` in `U′`: the mate of the inverse downward dot
for the adjunction `E ⊣ F`. -/
def locUpInvDot (i : I) (lam : X) : locE RD k i lam ⟶ locE RD k i lam :=
  (conjugateEquiv (adjLoc RD k i lam) (adjLoc RD k i lam)).symm (locInvDot RD k i lam)

theorem conj_locUpInvDot (i : I) (lam : X) :
    conjugateEquiv (adjLoc RD k i lam) (adjLoc RD k i lam) (locUpInvDot RD k i lam) =
      locInvDot RD k i lam :=
  Equiv.apply_symm_apply _ _

theorem locUpDot_comp_locUpInvDot (i : I) (lam : X) :
    locUpDot RD k i lam ≫ locUpInvDot RD k i lam = 𝟙 _ := by
  apply (conjugateEquiv (adjLoc RD k i lam) (adjLoc RD k i lam)).injective
  rw [← Bicategory.conjugateEquiv_comp _ (adjLoc RD k i lam), conj_locUpInvDot, conj_locUpDot,
    Bicategory.conjugateEquiv_id,
    locInvDot_comp_locDownDot]

theorem locUpInvDot_comp_locUpDot (i : I) (lam : X) :
    locUpInvDot RD k i lam ≫ locUpDot RD k i lam = 𝟙 _ := by
  apply (conjugateEquiv (adjLoc RD k i lam) (adjLoc RD k i lam)).injective
  rw [← Bicategory.conjugateEquiv_comp _ (adjLoc RD k i lam), conj_locUpInvDot, conj_locUpDot,
    Bicategory.conjugateEquiv_id,
    locDownDot_comp_locInvDot]

/-! ## Dots at arbitrary positions -/

/-- Whiskering preserves isomorphisms. -/
theorem isIso_whisk {S : Signature} {R : Type*} [CommRing R] (P : Presentation S R) {a b : Obj S}
    (f : P.obj a ⟶ P.obj b) [IsIso f] (u : Obj S) (v : List S.Colour) (ha : a.WhiskerOK u v)
    (hb : b.WhiskerOK u v) : IsIso (P.whisk f u v) :=
  ⟨⟨P.whisk (CategoryTheory.inv f) u v, by rw [← Presentation.whisk_comp, IsIso.hom_inv_id, P.whisk_id _ _ _ ha],
    by rw [← Presentation.whisk_comp, IsIso.inv_hom_id, P.whisk_id _ _ _ hb]⟩⟩

/-- In `U′` the localization of a 2-morphism placed between strands is invertible if the
localization of the 2-morphism is. -/
theorem isIso_toLoc_plcL (μ : X) (u v s t : List (Letter I))
    (hst : wt RD (wt RD μ v) t = wt RD (wt RD μ v) s)
    (f : (pres RD k).obj (ob RD (wt RD μ v) s) ⟶ (pres RD k).obj (ob RD (wt RD μ v) t))
    [IsIso ((toLoc RD k).map f)] : IsIso ((toLoc RD k).map (plcL RD k μ u v s t f)) := by
  rw [plcL, dite_eq_left hst]
  simp only [plc, LinearMap.coe_mk, AddHom.coe_mk, Functor.map_comp, eqToHom_map]
  rw [toLoc, SigMap.lift_whisk _ _ _ _ (whiskerOK_ob RD μ u v s)]
  have := isIso_whisk (presLoc RD k) ((toLoc RD k).map f) ((incl RD).obj (ob RD _ u))
    ((incl RD).word (wd RD μ v)) ((incl RD).whiskerOK (whiskerOK_ob RD μ u v s))
    ((incl RD).whiskerOK (by rw [← hst]; exact whiskerOK_ob RD μ u v t))
  unfold toLoc at this
  infer_instance

/-- The dot on a single strand is invertible in `U′`: the downward dot by Definition 3.28, the
upward dot by `locUpInvDot`. -/
instance isIso_toLoc_dot (ν : X) (l : Letter I) :
    IsIso ((toLoc RD k).map (dg RD k ν [l] [l] [([], .dot l, [])])) := by
  obtain ⟨b, i⟩ := l
  rw [dg_of (show SChain [(b, i)] [([], .dot (b, i), [])] [(b, i)] from ⟨rfl, rfl⟩)]
  cases b with
  | false =>
    rw [show mkD RD ν [([], .dot (false, i), [])] ⟨rfl, rfl⟩ = downDot RD i ν from rfl, toLoc_diag]
    exact ⟨⟨(presLoc RD k).diag (invDotF RD i ν), downDot_comp_invDot RD k i ν,
      invDot_comp_downDot RD k i ν⟩⟩
  | true =>
    rw [show mkD RD ν [([], .dot (true, i), [])] ⟨rfl, rfl⟩ = upDot RD i ν from rfl, toLoc_diag]
    exact ⟨⟨locUpInvDot RD k i ν, locUpDot_comp_locUpInvDot RD k i ν,
      locUpInvDot_comp_locUpDot RD k i ν⟩⟩

/-- **Every dot is invertible in `U′`**: the dot on the strand `l` between the strands `u` and
`v`, with rightmost region `μ`. -/
instance isIso_toLoc_dg_dot (μ : X) (u : List (Letter I)) (l : Letter I) (v : List (Letter I)) :
    IsIso ((toLoc RD k).map (dg RD k μ (u ++ [l] ++ v) (u ++ [l] ++ v) [(u, .dot l, v)])) := by
  have h := plcL_dg RD k μ u v [l] [l] [([], .dot l, [])]
  simp only [List.map_cons, List.map_nil, whL, List.nil_append, List.append_nil] at h
  rw [← h]
  exact isIso_toLoc_plcL RD k μ u v [l] [l] rfl _

/-! ## Sliding inverse dots -/

/-- **Inverting a slide relation.** If `a ≫ ψ = ψ ≫ b + c` with `a`, `b` invertible, then
`ψ ≫ b⁻¹ = a⁻¹ ≫ ψ + a⁻¹ ≫ c ≫ b⁻¹`. (Composition is left to right: `a ≫ ψ` is `a` followed
by `ψ`.) -/
theorem inv_slide {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {A B : 𝒞} (ψ c : A ⟶ B) (a : A ⟶ A)
    (b : B ⟶ B) [IsIso a] [IsIso b] (h : a ≫ ψ = ψ ≫ b + c) :
    ψ ≫ CategoryTheory.inv b = CategoryTheory.inv a ≫ ψ +
      CategoryTheory.inv a ≫ c ≫ CategoryTheory.inv b := by
  have h' : CategoryTheory.inv a ≫ (a ≫ ψ) ≫ CategoryTheory.inv b =
      CategoryTheory.inv a ≫ (ψ ≫ b + c) ≫ CategoryTheory.inv b := by rw [h]
  simpa [Preadditive.add_comp, Preadditive.comp_add] using h'


/-! ### Sliding inverse dots through upward crossings

In `U′` the relations (2.5c–d) of KL III, multiplied on both sides by the inverses of the dots,
give the slides of the inverse dots through upward crossings (proof of Webster
arXiv:1309.3796v2, Lemma 3.29). Below `ψ` is the upward crossing on two strands, `x₀`, `x₁` are
the dots on the left and right strand, and all maps are images under `U → U′`. -/

section InverseSlides

/-- In `U′`, `ψ x₁⁻¹ = x₀⁻¹ ψ + x₀⁻¹ x₁⁻¹` for an upward crossing of two strands of colour `c`
(composition is diagrammatic, bottom to top). This is (2.5c) of KL III multiplied by the inverse
dots (Webster arXiv:1309.3796v2, proof of Lemma 3.29). -/
theorem toLoc_cross_comp_inv_dot_right_eq (μ : X) (c : I) :
    haveI : IsIso ((toLoc RD k).map
        (dg RD k μ [up c, up c] [up c, up c] [([], .dot (up c), [up c])])) :=
      isIso_toLoc_dg_dot RD k μ [] (up c) [up c]
    haveI : IsIso ((toLoc RD k).map
        (dg RD k μ [up c, up c] [up c, up c] [([up c], .dot (up c), [])])) :=
      isIso_toLoc_dg_dot RD k μ [up c] (up c) []
    (toLoc RD k).map (dg RD k μ [up c, up c] [up c, up c] [([], .cross true c c, [])]) ≫
        CategoryTheory.inv ((toLoc RD k).map
          (dg RD k μ [up c, up c] [up c, up c] [([up c], .dot (up c), [])])) =
      CategoryTheory.inv ((toLoc RD k).map
          (dg RD k μ [up c, up c] [up c, up c] [([], .dot (up c), [up c])])) ≫
          (toLoc RD k).map (dg RD k μ [up c, up c] [up c, up c] [([], .cross true c c, [])]) +
        CategoryTheory.inv ((toLoc RD k).map
          (dg RD k μ [up c, up c] [up c, up c] [([], .dot (up c), [up c])])) ≫
          CategoryTheory.inv ((toLoc RD k).map
            (dg RD k μ [up c, up c] [up c, up c] [([up c], .dot (up c), [])])) := by
  have : IsIso ((toLoc RD k).map
      (dg RD k μ [up c, up c] [up c, up c] [([], .dot (up c), [up c])])) :=
    isIso_toLoc_dg_dot RD k μ [] (up c) [up c]
  have : IsIso ((toLoc RD k).map
      (dg RD k μ [up c, up c] [up c, up c] [([up c], .dot (up c), [])])) :=
    isIso_toLoc_dg_dot RD k μ [up c] (up c) []
  have h := dg_slideREq (RD := RD) (k := k) μ c
  have e1 : dg RD k μ [up c, up c] [up c, up c]
      [([], .dot (up c), [up c]), ([], .cross true c c, [])] =
      dg RD k μ [up c, up c] [up c, up c] [([], .dot (up c), [up c])] ≫
        dg RD k μ [up c, up c] [up c, up c] [([], .cross true c c, [])] :=
    (dg_comp (show SChain [up c, up c] [([], .dot (up c), [up c])] [up c, up c] from ⟨rfl, rfl⟩)
      (show SChain [up c, up c] [([], .cross true c c, [])] [up c, up c] from ⟨rfl, rfl⟩)).symm
  have e2 : dg RD k μ [up c, up c] [up c, up c]
      [([], .cross true c c, []), ([up c], .dot (up c), [])] =
      dg RD k μ [up c, up c] [up c, up c] [([], .cross true c c, [])] ≫
        dg RD k μ [up c, up c] [up c, up c] [([up c], .dot (up c), [])] :=
    (dg_comp (show SChain [up c, up c] [([], .cross true c c, [])] [up c, up c] from ⟨rfl, rfl⟩)
      (show SChain [up c, up c] [([up c], .dot (up c), [])] [up c, up c] from ⟨rfl, rfl⟩)).symm
  rw [e1, e2, dg_nil] at h
  have h' := congrArg (toLoc RD k).map h
  rw [Functor.map_add, Functor.map_comp, Functor.map_comp, CategoryTheory.Functor.map_id] at h'
  have := inv_slide _ _ _ _ h'
  rwa [Category.id_comp] at this


/-- In `U′`, `ψ x₀⁻¹ = x₁⁻¹ ψ - x₁⁻¹ x₀⁻¹` for an upward crossing of two strands of colour `c`
(composition is diagrammatic, bottom to top). This is (2.5d) of KL III multiplied by the inverse
dots (Webster arXiv:1309.3796v2, proof of Lemma 3.29). -/
theorem toLoc_cross_comp_inv_dot_left_eq (μ : X) (c : I) :
    haveI : IsIso ((toLoc RD k).map (dg RD k μ [up c, up c] [up c, up c] [([], .dot (up c), [up c])])) :=
      isIso_toLoc_dg_dot RD k μ [] (up c) [up c]
    haveI : IsIso ((toLoc RD k).map (dg RD k μ [up c, up c] [up c, up c] [([up c], .dot (up c), [])])) :=
      isIso_toLoc_dg_dot RD k μ [up c] (up c) []
    (toLoc RD k).map (dg RD k μ [up c, up c] [up c, up c] [([], .cross true c c, [])]) ≫ CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [up c, up c] [up c, up c] [([], .dot (up c), [up c])])) =
      CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [up c, up c] [up c, up c] [([up c], .dot (up c), [])])) ≫ (toLoc RD k).map (dg RD k μ [up c, up c] [up c, up c] [([], .cross true c c, [])]) -
        CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [up c, up c] [up c, up c] [([up c], .dot (up c), [])])) ≫ CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [up c, up c] [up c, up c] [([], .dot (up c), [up c])])) := by
  have : IsIso ((toLoc RD k).map (dg RD k μ [up c, up c] [up c, up c] [([], .dot (up c), [up c])])) :=
    isIso_toLoc_dg_dot RD k μ [] (up c) [up c]
  have : IsIso ((toLoc RD k).map (dg RD k μ [up c, up c] [up c, up c] [([up c], .dot (up c), [])])) :=
    isIso_toLoc_dg_dot RD k μ [up c] (up c) []
  have h := dg_slideLEq (RD := RD) (k := k) μ c
  have e1 : dg RD k μ [up c, up c] [up c, up c] [([], .cross true c c, []), ([], .dot (up c), [up c])] = (dg RD k μ [up c, up c] [up c, up c] [([], .cross true c c, [])]) ≫ (dg RD k μ [up c, up c] [up c, up c] [([], .dot (up c), [up c])]) :=
    (dg_comp (show SChain [up c, up c] [([], .cross true c c, [])] [up c, up c] from ⟨rfl, rfl⟩) (show SChain [up c, up c] [([], .dot (up c), [up c])] [up c, up c] from ⟨rfl, rfl⟩)).symm
  have e2 : dg RD k μ [up c, up c] [up c, up c] [([up c], .dot (up c), []), ([], .cross true c c, [])] = (dg RD k μ [up c, up c] [up c, up c] [([up c], .dot (up c), [])]) ≫ (dg RD k μ [up c, up c] [up c, up c] [([], .cross true c c, [])]) :=
    (dg_comp (show SChain [up c, up c] [([up c], .dot (up c), [])] [up c, up c] from ⟨rfl, rfl⟩) (show SChain [up c, up c] [([], .cross true c c, [])] [up c, up c] from ⟨rfl, rfl⟩)).symm
  rw [e1, e2, dg_nil] at h
  have h' := congrArg (toLoc RD k).map h
  rw [Functor.map_add, Functor.map_comp, Functor.map_comp, CategoryTheory.Functor.map_id] at h'
  have h'' := eq_sub_of_add_eq h'.symm
  rw [sub_eq_add_neg] at h''
  have := inv_slide _ _ _ _ h''
  rwa [Preadditive.neg_comp, Category.id_comp, Preadditive.comp_neg, ← sub_eq_add_neg] at this

/-- In `U′`, `ψ x₁⁻¹ = x₀⁻¹ ψ` for an upward crossing of strands of colours `c ≠ d`, the inverse dot
being on the strand of colour `c` (Webster arXiv:1309.3796v2, proof of Lemma 3.29). -/
theorem toLoc_cross_comp_inv_dot_right_eq_of_ne (μ : X) (c d : I) (h : c ≠ d) :
    haveI : IsIso ((toLoc RD k).map (dg RD k μ [up c, up d] [up c, up d] [([], .dot (up c), [up d])])) :=
      isIso_toLoc_dg_dot RD k μ [] (up c) [up d]
    haveI : IsIso ((toLoc RD k).map (dg RD k μ [up d, up c] [up d, up c] [([up d], .dot (up c), [])])) :=
      isIso_toLoc_dg_dot RD k μ [up d] (up c) []
    (toLoc RD k).map (dg RD k μ [up c, up d] [up d, up c] [([], .cross true c d, [])]) ≫ CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [up d, up c] [up d, up c] [([up d], .dot (up c), [])])) =
      CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [up c, up d] [up c, up d] [([], .dot (up c), [up d])])) ≫ (toLoc RD k).map (dg RD k μ [up c, up d] [up d, up c] [([], .cross true c d, [])]) := by
  have : IsIso ((toLoc RD k).map (dg RD k μ [up c, up d] [up c, up d] [([], .dot (up c), [up d])])) :=
    isIso_toLoc_dg_dot RD k μ [] (up c) [up d]
  have : IsIso ((toLoc RD k).map (dg RD k μ [up d, up c] [up d, up c] [([up d], .dot (up c), [])])) :=
    isIso_toLoc_dg_dot RD k μ [up d] (up c) []
  have h := dg_slideRNe (RD := RD) (k := k) μ c d h
  have e1 : dg RD k μ [up c, up d] [up d, up c] [([], .dot (up c), [up d]), ([], .cross true c d, [])] = (dg RD k μ [up c, up d] [up c, up d] [([], .dot (up c), [up d])]) ≫ (dg RD k μ [up c, up d] [up d, up c] [([], .cross true c d, [])]) :=
    (dg_comp (show SChain [up c, up d] [([], .dot (up c), [up d])] [up c, up d] from ⟨rfl, rfl⟩) (show SChain [up c, up d] [([], .cross true c d, [])] [up d, up c] from ⟨rfl, rfl⟩)).symm
  have e2 : dg RD k μ [up c, up d] [up d, up c] [([], .cross true c d, []), ([up d], .dot (up c), [])] = (dg RD k μ [up c, up d] [up d, up c] [([], .cross true c d, [])]) ≫ (dg RD k μ [up d, up c] [up d, up c] [([up d], .dot (up c), [])]) :=
    (dg_comp (show SChain [up c, up d] [([], .cross true c d, [])] [up d, up c] from ⟨rfl, rfl⟩) (show SChain [up d, up c] [([up d], .dot (up c), [])] [up d, up c] from ⟨rfl, rfl⟩)).symm
  rw [e1, e2] at h
  have h' := congrArg (toLoc RD k).map h
  rw [Functor.map_comp, Functor.map_comp] at h'
  have := inv_slide _ 0 _ _ (h'.trans (add_zero _).symm)
  rwa [Limits.zero_comp, Limits.comp_zero, add_zero] at this

/-- In `U′`, `ψ x₀⁻¹ = x₁⁻¹ ψ` for an upward crossing of strands of colours `c ≠ d`, the inverse dot
being on the strand of colour `d` (Webster arXiv:1309.3796v2, proof of Lemma 3.29). -/
theorem toLoc_cross_comp_inv_dot_left_eq_of_ne (μ : X) (c d : I) (h : c ≠ d) :
    haveI : IsIso ((toLoc RD k).map (dg RD k μ [up d, up c] [up d, up c] [([], .dot (up d), [up c])])) :=
      isIso_toLoc_dg_dot RD k μ [] (up d) [up c]
    haveI : IsIso ((toLoc RD k).map (dg RD k μ [up c, up d] [up c, up d] [([up c], .dot (up d), [])])) :=
      isIso_toLoc_dg_dot RD k μ [up c] (up d) []
    (toLoc RD k).map (dg RD k μ [up c, up d] [up d, up c] [([], .cross true c d, [])]) ≫ CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [up d, up c] [up d, up c] [([], .dot (up d), [up c])])) =
      CategoryTheory.inv ((toLoc RD k).map (dg RD k μ [up c, up d] [up c, up d] [([up c], .dot (up d), [])])) ≫ (toLoc RD k).map (dg RD k μ [up c, up d] [up d, up c] [([], .cross true c d, [])]) := by
  have : IsIso ((toLoc RD k).map (dg RD k μ [up d, up c] [up d, up c] [([], .dot (up d), [up c])])) :=
    isIso_toLoc_dg_dot RD k μ [] (up d) [up c]
  have : IsIso ((toLoc RD k).map (dg RD k μ [up c, up d] [up c, up d] [([up c], .dot (up d), [])])) :=
    isIso_toLoc_dg_dot RD k μ [up c] (up d) []
  have h := dg_slideLNe (RD := RD) (k := k) μ c d h
  have e1 : dg RD k μ [up c, up d] [up d, up c] [([], .cross true c d, []), ([], .dot (up d), [up c])] = (dg RD k μ [up c, up d] [up d, up c] [([], .cross true c d, [])]) ≫ (dg RD k μ [up d, up c] [up d, up c] [([], .dot (up d), [up c])]) :=
    (dg_comp (show SChain [up c, up d] [([], .cross true c d, [])] [up d, up c] from ⟨rfl, rfl⟩) (show SChain [up d, up c] [([], .dot (up d), [up c])] [up d, up c] from ⟨rfl, rfl⟩)).symm
  have e2 : dg RD k μ [up c, up d] [up d, up c] [([up c], .dot (up d), []), ([], .cross true c d, [])] = (dg RD k μ [up c, up d] [up c, up d] [([up c], .dot (up d), [])]) ≫ (dg RD k μ [up c, up d] [up d, up c] [([], .cross true c d, [])]) :=
    (dg_comp (show SChain [up c, up d] [([up c], .dot (up d), [])] [up c, up d] from ⟨rfl, rfl⟩) (show SChain [up c, up d] [([], .cross true c d, [])] [up d, up c] from ⟨rfl, rfl⟩)).symm
  rw [e1, e2] at h
  have h' := congrArg (toLoc RD k).map h.symm
  rw [Functor.map_comp, Functor.map_comp] at h'
  have := inv_slide _ 0 _ _ (h'.trans (add_zero _).symm)
  rwa [Limits.zero_comp, Limits.comp_zero, add_zero] at this

end InverseSlides

end Categorification.KL3.Diagram
