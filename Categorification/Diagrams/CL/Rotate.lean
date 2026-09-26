/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Rotation
import Categorification.Diagrams.CL.RescaleBasic

/-!
# Rotation of upward diagrams in a presentation on the signature of `U`

S. Cautis, A. D. Lauda, *Implicit structure in 2-representations of quantum groups*,
arXiv:1111.1431v3, §2.2 (`sec:cycbiadjoint`, eq. `eq_almost_cyclic`, p. 6, and the sentence
after it).

In `U_Q(g)` the 2-morphisms are cyclic only up to the scalars `t_{ij}`, so the rotation calculus of
KL III (`Categorification.Diagrams.KL3.Rotation`, which uses that every 2-morphism of `U` is
cyclic) does not apply as it stands. This file develops the part of it that does not need
cyclicity, for an arbitrary presentation `P` on the signature `psig RD` of `U` in which the zigzag
relations hold (`hz : P.PivotalZigzags _`):

* `rotC P hz μ ν s t s' t' hs ht es et`: **the rotation by `180°`** of a 2-morphism
  `E_s 1_μ ⟶ E_t 1_μ` of `P`, i.e. its right mate `E_{t*} 1_ν ⟶ E_{s*} 1_ν` for the biadjunctions
  given by nested cups and caps (the boundaries are given as `s'`, `t'` with `rd s = s'`,
  `rd t = t'`, to avoid transport). It is `k`-linear and contravariant (`rotC_comp`, `rotC_id`);
  nothing else about it needs cyclicity.
* `dgC P μ s t ls`: the class in `P` of the normal-form diagram with layers `ls`.
* `rotC_dg`: **the rotation of a normal-form diagram all of whose generators are upward dots and
  upward crossings is the diagram of the rotated layers in reversed order** (`rotLs`), times the
  product of the scalars `τ j i` of its crossings `E_j E_i ⟶ E_i E_j`, provided that
  (`hDot`) the rotated upward dot is the downward dot, and (`hCross`) the rotated upward crossing
  `rotCrossR j i` is `τ j i` times the downward crossing. For `U_Q(g)` these are CL's dot
  cyclicity `eq_cyclic_dot` and `Q`-cyclicity `eq_almost_cyclic` with `τ j i = t_{ij}`.

The proof follows `Categorification.Diagrams.KL3.Rotation` (mates of whiskered generators via
`Categorification.Diagrams.KL3.MateCalculus`), with the scalar of the crossing carried through
the linearity of mates and of whiskering.

For KLR diagrams:

* `rotKD D`: the rotation of a KLR diagram `D : a ⟶ b` by `180°`, a diagram
  `kobjR b ⟶ kobjR a` between the reversed sequences: layers in reversed order, each layer
  `(u, g, v)` becoming `(v.reverse, g, u.reverse)`; `rotKD_comp`, `rotKD_id`;
* `rotKLin τ`: its `k`-linear extension, weighted by the product `wK τ D` of the scalars of the
  crossings; it is contravariant (`rotKLin_comp`, `rotKLin_id`), so it sends a polynomial in dots
  to the reversed polynomial in the rotated dots (`ncEval_antihom`);
* `rotC_upDiag`, `rotC_upLin`: **the rotation of a linear combination of KLR diagrams on upward
  strands is `rotKLin τ` of it on downward strands**.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Bicategory

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

section Rot

variable (P : Presentation.{w, max u v} (psig RD) k)

/-! ## Objects as 1-morphisms of `P.Bicat` -/

/-- The 1-morphism `E_t 1_μ` of `P.Bicat`, from its left region `ν = μ + t_X` to `μ`. -/
def obC (μ ν : X) (t : List (Letter I)) (h : wt RD μ t = ν) : (⟨ν⟩ : P.Bicat) ⟶ ⟨μ⟩ :=
  ⟨ob RD μ t, h, ob_wf RD μ t, ob_endR RD μ t⟩

@[simp] theorem obC_obj (μ ν : X) (t : List (Letter I)) (h : wt RD μ t = ν) :
    (obC P μ ν t h).obj = ob RD μ t := rfl

/-- The dual of `E_t 1_μ` is `E_{t*} 1_ν`. -/
theorem dual_obC (μ ν : X) (t : List (Letter I)) (h : wt RD μ t = ν) :
    P.dualHom (inv RD).toColourDuality.pivotal (obC P μ ν t h) =
      obC P ν μ (rd t) (wt_rd_of RD μ ν t h) := by
  subst h
  exact Bicat.Hom.ext (Obj.ext (wt_rd RD μ t).symm (dualWord_wd RD μ t))

variable (hz : P.PivotalZigzags (inv RD).toColourDuality)

/-- The biadjunctions `x ⊣⊢ x*` of all 1-morphisms of `P.Bicat`, by nested cups and caps. -/
local notation "BBC" => biadj (pivotalBiadj (inv RD) P hz)

/-- The right mate for the nested cups and caps, as a `k`-linear map. -/
def mateC {l m : P.Bicat} (x x' : l ⟶ m) :
    (P.obj x.obj ⟶ P.obj x'.obj) →ₗ[k]
      (P.obj (P.dualHom (inv RD).toColourDuality.pivotal x').obj ⟶
        P.obj (P.dualHom (inv RD).toColourDuality.pivotal x).obj) where
  toFun f := Biadjunction.rightMate (BBC x) (BBC x') (show x ⟶ x' from f)
  map_add' f g := Biadjunction.rightMate_add (BBC x) (BBC x') (show x ⟶ x' from f) g
  map_smul' r f := Biadjunction.rightMate_smul (BBC x) (BBC x') r (show x ⟶ x' from f)

theorem mateC_apply {l m : P.Bicat} (x x' : l ⟶ m) (f : P.obj x.obj ⟶ P.obj x'.obj) :
    mateC P hz x x' f = Biadjunction.rightMate (BBC x) (BBC x') (show x ⟶ x' from f) := rfl

theorem objEqC {l m : P.Bicat} {x y : l ⟶ m} (h : x = y) :
    P.obj (Bicat.Hom.obj x) = P.obj (Bicat.Hom.obj y) :=
  congrArg (fun z => P.obj (Bicat.Hom.obj z)) h

theorem rotC_e₁ (μ ν : X) (t t' : List (Letter I)) (ht : wt RD μ t = ν) (et : rd t = t') :
    P.obj (ob RD ν t') =
      P.obj (P.dualHom (inv RD).toColourDuality.pivotal (obC P μ ν t ht)).obj := by
  rw [dual_obC]; subst et; rfl

/-- **The rotation by `180°`** of a 2-morphism `f : E_s 1_μ ⟶ E_t 1_μ` of `P`, where
`ν = μ + s_X = μ + t_X`: its right mate `E_{t*} 1_ν ⟶ E_{s*} 1_ν` for the biadjunctions given by
the nested cups and caps, with the boundaries written as `t' = t*`, `s' = s*`. -/
def rotC (μ ν : X) (s t s' t' : List (Letter I)) (hs : wt RD μ s = ν) (ht : wt RD μ t = ν)
    (es : rd s = s') (et : rd t = t') :
    (P.obj (ob RD μ s) ⟶ P.obj (ob RD μ t)) →ₗ[k] (P.obj (ob RD ν t') ⟶ P.obj (ob RD ν s')) where
  toFun f := eqToHom (rotC_e₁ P μ ν t t' ht et) ≫ mateC P hz (obC P μ ν s hs) (obC P μ ν t ht) f ≫
      eqToHom (rotC_e₁ P μ ν s s' hs es).symm
  map_add' f g := by
    rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    rw [map_smul, Linear.smul_comp, Linear.comp_smul]
    rfl

theorem rotC_apply (μ ν : X) (s t s' t' : List (Letter I)) (hs : wt RD μ s = ν)
    (ht : wt RD μ t = ν) (es : rd s = s') (et : rd t = t')
    (f : P.obj (ob RD μ s) ⟶ P.obj (ob RD μ t)) :
    rotC P hz μ ν s t s' t' hs ht es et f = eqToHom (rotC_e₁ P μ ν t t' ht et) ≫
      mateC P hz (obC P μ ν s hs) (obC P μ ν t ht) f ≫ eqToHom (rotC_e₁ P μ ν s s' hs es).symm :=
  rfl

/-- The rotation is contravariant. -/
theorem rotC_comp (μ ν : X) (s r t s' r' t' : List (Letter I)) (hs : wt RD μ s = ν)
    (hr : wt RD μ r = ν) (ht : wt RD μ t = ν) (es : rd s = s') (er : rd r = r') (et : rd t = t')
    (f : P.obj (ob RD μ s) ⟶ P.obj (ob RD μ r)) (g : P.obj (ob RD μ r) ⟶ P.obj (ob RD μ t)) :
    rotC P hz μ ν s t s' t' hs ht es et (f ≫ g) =
      rotC P hz μ ν r t r' t' hr ht er et g ≫ rotC P hz μ ν s r s' r' hs hr es er f := by
  have h := Biadjunction.rightMate_comp (BBC (obC P μ ν s hs)) (BBC (obC P μ ν r hr))
    (BBC (obC P μ ν t ht)) (show obC P μ ν s hs ⟶ obC P μ ν r hr from f)
    (show obC P μ ν r hr ⟶ obC P μ ν t ht from g)
  simp only [rotC_apply, mateC_apply]
  erw [h]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact congrArg (eqToHom _ ≫ ·) (@Category.assoc P.Presented _ _ _ _ _ _ _ _)

theorem rotC_id (μ ν : X) (s s' : List (Letter I)) (hs : wt RD μ s = ν) (es : rd s = s') :
    rotC P hz μ ν s s s' s' hs hs es es (𝟙 _) = 𝟙 _ := by
  have h := Biadjunction.rightMate_id (BBC (obC P μ ν s hs))
  rw [rotC_apply, mateC_apply]
  erw [h]
  erw [@Category.id_comp P.Presented]
  simp

/-! ## Classes of normal-form diagrams -/

open Classical in
/-- The class in `P` of the normal-form diagram with layers `ls` from `E_s 1_μ` to `E_t 1_μ`,
or `0` if the layers do not form such a diagram. -/
def dgC (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    P.obj (ob RD μ s) ⟶ P.obj (ob RD μ t) :=
  if h : SChain s ls t then P.diag (mkD RD μ ls h) else 0

variable {P}

theorem dgC_of {μ : X} {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    dgC P μ s t ls = P.diag (mkD RD μ ls h) := dif_pos h

theorem dgC_of_not {μ : X} {s t : List (Letter I)} {ls : List (LayerData I)}
    (h : ¬ SChain s ls t) : dgC P μ s t ls = 0 := dif_neg h

theorem dgC_nil (μ : X) (s : List (Letter I)) : dgC P μ s s [] = 𝟙 _ := by
  rw [dgC_of (show SChain s [] s from rfl)]
  exact (P.diag_eq_of_layers_eq rfl).trans (P.diag_id _)

theorem dgC_comp {μ : X} {s t r : List (Letter I)} {A B : List (LayerData I)} (hA : SChain s A t)
    (hB : SChain t B r) : dgC P μ s t A ≫ dgC P μ t r B = dgC P μ s r (A ++ B) := by
  rw [dgC_of hA, dgC_of hB, dgC_of (hA.append hB), ← Presentation.diag_comp, mkD_comp]

variable (P) in
/-- The morphism `θ` of the presented category is the class of a diagram with the layers
`ls`. -/
def IsDgC {a b : Obj (psig RD)} (θ : P.obj a ⟶ P.obj b) (ls : List (Layer (psig RD))) : Prop :=
  ∃ D : a ⟶ b, θ = P.diag D ∧ Diagram.layers D = ls

theorem isDgC_dg (μ : X) {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    IsDgC P (dgC P μ s t ls) (layList RD μ ls) :=
  ⟨mkD RD μ ls h, dgC_of h, rfl⟩

theorem IsDgC.eqToHom_comp {a a' b : Obj (psig RD)} (e : P.obj a' = P.obj a)
    {θ : P.obj a ⟶ P.obj b} {ls : List (Layer (psig RD))} (h : IsDgC P θ ls) :
    IsDgC P (eqToHom e ≫ θ) ls := by
  obtain rfl := P.obj_injective e
  simpa using h

theorem IsDgC.comp_eqToHom {a b b' : Obj (psig RD)} (e : P.obj b = P.obj b')
    {θ : P.obj a ⟶ P.obj b} {ls : List (Layer (psig RD))} (h : IsDgC P θ ls) :
    IsDgC P (θ ≫ eqToHom e) ls := by
  obtain rfl := P.obj_injective e
  simpa using h

/-- Two classes of diagrams with the same layers are equal, up to the identification of their
boundaries. -/
theorem IsDgC.eq_eqToHom {a b a' b' : Obj (psig RD)} {θ : P.obj a ⟶ P.obj b}
    {θ' : P.obj a' ⟶ P.obj b'} {ls : List (Layer (psig RD))}
    (h : IsDgC P θ ls) (h' : IsDgC P θ' ls) (ea : a = a') (eb : b = b') :
    θ = eqToHom (congrArg P.obj ea) ≫ θ' ≫ eqToHom (congrArg P.obj eb.symm) := by
  subst ea eb
  obtain ⟨D, rfl, hD⟩ := h
  obtain ⟨D', rfl, hD'⟩ := h'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact P.diag_eq_of_layers_eq (hD.trans hD'.symm)

/-- A morphism which is the class of a diagram with the layers of a normal-form diagram is that
normal-form diagram. -/
theorem IsDgC.eq_dgC {a b : Obj (psig RD)} {θ : P.obj a ⟶ P.obj b} {ν : X}
    {s t : List (Letter I)} {L : List (LayerData I)} (hθ : IsDgC P θ (layList RD ν L))
    (ea : a = ob RD ν s) (eb : b = ob RD ν t) (hL : SChain s L t) :
    θ = eqToHom (congrArg P.obj ea) ≫ dgC P ν s t L ≫ eqToHom (congrArg P.obj eb.symm) :=
  hθ.eq_eqToHom (isDgC_dg ν hL) ea eb

/-! ## The mate of a normal-form diagram -/

/-- The mate of a normal-form diagram, as a list of layers: nested cups of `a` to the right of
`b*`, the layers of the diagram between `b*` and `a*`, nested caps of `b` to the left of `a*`. -/
theorem isDgC_mate_raw (ν μ : X) (a b : List (Letter I)) (ha : wt RD ν a = μ)
    (hb : wt RD ν b = μ) (ls : List (LayerData I)) (h : SChain a ls b) :
    IsDgC P (mateC P hz (obC P ν μ a ha) (obC P ν μ b hb) (dgC P ν a b ls))
      ((cupLayers (E := inv RD) μ (wd RD ν a)).map (·.wl (ob RD μ (rd b))) ++
        ((layList RD ν ls).map (·.wr (wd RD μ (rd a)))).map (·.wl (ob RD μ (rd b))) ++
        (capLayers (E := inv RD) ν (wd RD ν b)).map (·.wr (wd RD μ (rd a)))) := by
  have H := IsDiag.rightMate (BBC (obC P ν μ a ha)) (BBC (obC P ν μ b hb))
    (isDiag_biadj_left_unit hz _) (isDiag_biadj_left_counit hz _)
    (show IsDiag P (show obC P ν μ a ha ⟶ obC P ν μ b hb from dgC P ν a b ls) _ from
      isDgC_dg ν h)
  have e₁ := congrArg Bicat.Hom.obj (dual_obC P ν μ b hb)
  have e₂ : (P.dualHom (inv RD).toColourDuality.pivotal
      (obC P ν μ a ha)).obj.word = wd RD μ (rd a) := by
    rw [dual_obC]; rfl
  simp only [obC_obj] at e₁
  rw [e₁, e₂] at H
  exact H

/-- **The mate of a normal-form diagram, in normal form** (before straightening). -/
theorem isDgC_mate_nf (ν μ : X) (a b : List (Letter I)) (ha : wt RD ν a = μ)
    (hb : wt RD ν b = μ) (ls : List (LayerData I)) (h : SChain a ls b) :
    IsDgC P (mateC P hz (obC P ν μ a ha) (obC P ν μ b hb) (dgC P ν a b ls))
      (layList RD μ (rotRaw a b ls)) := by
  have H := isDgC_mate_raw hz ν μ a b ha hb ls h
  convert H using 1
  subst ha
  have hμ : wt RD (wt RD ν a) (rd a) = ν := wt_rd RD ν a
  simp only [rotRaw, layList_append]
  congr 1
  congr 1
  · rw [cupLayers_wd]
    have hm := (sChain_nCups a).wt_mem RD (wt RD ν a)
    simp only [layList, List.map_map]
    refine List.map_congr_left fun x hx => ?_
    simp only [Function.comp_apply, whL]
    rw [lay_wl_eq RD _ (wt RD ν a) _ _ _ _
      (show wt RD (wt RD ν a) (x.1 ++ x.2.1.dom ++ x.2.2) = wt RD ν a from hm x hx),
      List.append_nil]
  · have hm := h.wt_mem RD ν
    simp only [layList, List.map_map]
    refine List.map_congr_left fun x hx => ?_
    simp only [Function.comp_apply, whL]
    rw [lay_wr_eq RD _ _ _ _ _ _ hμ, lay_wl_eq RD _ _ _ _ _ _ ?_]
    rw [← List.append_assoc, wt_append, hμ, hm x hx]
  · rw [capLayers_wd]
    simp only [layList, List.map_map]
    refine List.map_congr_left fun x _ => ?_
    simp only [Function.comp_apply, whL, List.nil_append]
    rw [lay_wr_eq RD _ _ _ _ _ _ hμ]

/-- The mate of a normal-form diagram is the (unstraightened) normal-form diagram `rotRaw`. -/
theorem mateC_dgC (ν μ : X) (a b : List (Letter I)) (ha : wt RD ν a = μ)
    (hb : wt RD ν b = μ) {ls : List (LayerData I)} (h : SChain a ls b) :
    mateC P hz (obC P ν μ a ha) (obC P ν μ b hb) (dgC P ν a b ls) =
      eqToHom (congrArg P.obj (congrArg Bicat.Hom.obj (dual_obC P ν μ b hb))) ≫
        dgC P μ (rd b) (rd a) (rotRaw a b ls) ≫
          eqToHom (congrArg P.obj (congrArg Bicat.Hom.obj (dual_obC P ν μ a ha)).symm) :=
  (isDgC_mate_nf hz ν μ a b ha hb ls h).eq_dgC
    (congrArg Bicat.Hom.obj (dual_obC P ν μ b hb)) (congrArg Bicat.Hom.obj (dual_obC P ν μ a ha))
    (sChain_rotRaw h)

/-! ## The rotations of the upward generators -/

/-- The upward generators: dots on upward strands and crossings of upward strands. -/
def IsUpSh (g : Shape I) : Prop := (∃ i, g = .dot (up i)) ∨ ∃ j i, g = .cross true j i

/-- The scalar acquired by an upward generator under rotation: `τ j i` for the crossing
`E_j E_i ⟶ E_i E_j`, `1` for a dot (and for the other shapes, which do not occur). -/
def shSc (τ : I → I → k) : Shape I → k
  | .cross true j i => τ j i
  | _ => 1

@[simp] theorem shSc_dot (τ : I → I → k) (l : Letter I) : shSc τ (.dot l) = 1 := rfl
@[simp] theorem shSc_upcross (τ : I → I → k) (j i : I) : shSc τ (.cross true j i) = τ j i := rfl

variable {hz}
variable (τ : I → I → k)
  (hDot : ∀ (i : I) (μ : X), P.diag (rotDotR RD i μ) = P.diag (downDot RD i μ))
  (hCross : ∀ (j i : I) (μ : X),
    P.diag (rotCrossR RD j i μ) = τ j i • P.diag (downCross RD j i μ))

include hDot hCross in
/-- **The rotations of the upward generators**: the mate of an upward dot is the downward dot,
the mate of the upward crossing `E_j E_i ⟶ E_i E_j` is `τ j i` times the downward crossing. -/
theorem mateC_gen (ν μ : X) (g : Shape I) (hg : IsUpSh g) (h₁ : wt RD ν g.dom = μ)
    (h₂ : wt RD ν g.cod = μ) :
    ∃ Z, mateC P hz (obC P ν μ g.dom h₁) (obC P ν μ g.cod h₂)
        (dgC P ν g.dom g.cod [([], g, [])]) = shSc τ g • Z ∧
      IsDgC P Z (layList RD μ [([], rotSh g, [])]) := by
  have hg₀ : SChain g.dom [([], g, [])] g.cod := by simp
  have hc : SChain (rd g.cod) [([], rotSh g, [])] (rd g.dom) := by
    simp [rotSh_dom, rotSh_cod]
  refine ⟨eqToHom (congrArg P.obj (congrArg Bicat.Hom.obj (dual_obC P ν μ g.cod h₂))) ≫
      dgC P μ (rd g.cod) (rd g.dom) [([], rotSh g, [])] ≫
        eqToHom (congrArg P.obj (congrArg Bicat.Hom.obj (dual_obC P ν μ g.dom h₁)).symm),
    ?_, ((isDgC_dg μ hc).comp_eqToHom _).eqToHom_comp _⟩
  rw [mateC_dgC hz ν μ _ _ h₁ h₂ hg₀, ← Linear.comp_smul, ← Linear.smul_comp]
  congr 2
  rw [dgC_of (sChain_rotRaw hg₀), dgC_of hc]
  rcases hg with ⟨i, rfl⟩ | ⟨j, i, rfl⟩
  · rw [shSc_dot, one_smul]
    exact hDot i μ
  · exact hCross j i μ

include hDot hCross in
/-- **The rotation of a whiskered upward generator is the whiskered rotated generator**, times the
scalar of the generator: `(u ⊗ g ⊗ v)^* = shSc τ g · (v* ⊗ g^rot ⊗ u*)`. -/
theorem mateC_layer (μ ν : X) (u v : List (Letter I)) (g : Shape I) (hg : IsUpSh g)
    (hs : wt RD μ (u ++ g.dom ++ v) = ν) (ht : wt RD μ (u ++ g.cod ++ v) = ν) :
    ∃ Z, mateC P hz (obC P μ ν _ hs) (obC P μ ν _ ht)
        (dgC P μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)]) = shSc τ g • Z ∧
      IsDgC P Z (layList RD ν [(rd v, rotSh g, rd u)]) := by
  have h₂ : wt RD (wt RD μ v) g.cod = wt RD (wt RD μ v) g.dom :=
    (Shape.wt_dom_eq_wt_cod (wt RD μ v) g).symm
  have hu : wt RD (wt RD (wt RD μ v) g.dom) u = ν := by
    rw [← hs, List.append_assoc, wt_append, wt_append]
  let V := obC P μ (wt RD μ v) v rfl
  let G₁ := obC P (wt RD μ v) (wt RD (wt RD μ v) g.dom) g.dom rfl
  let G₂ := obC P (wt RD μ v) (wt RD (wt RD μ v) g.dom) g.cod h₂
  let Uh := obC P (wt RD (wt RD μ v) g.dom) ν u hu
  let θ : G₁ ⟶ G₂ := dgC P (wt RD μ v) g.dom g.cod [([], g, [])]
  have hθ : IsDiag P θ (layList RD (wt RD μ v) [([], g, [])]) :=
    isDgC_dg (wt RD μ v) (show SChain g.dom [([], g, [])] g.cod by simp)
  obtain ⟨Z₀, hZ₀, hZ₀l⟩ := mateC_gen (hz := hz) τ hDot hCross (wt RD μ v) _ g hg rfl h₂
  let θ' : G₁ ⟶ G₂ := (Biadjunction.rightMateLinearEquiv k (BBC G₁) (BBC G₂)).symm Z₀
  have hθ'm : Biadjunction.rightMate (BBC G₁) (BBC G₂) θ' = Z₀ :=
    (Biadjunction.rightMateLinearEquiv k (BBC G₁) (BBC G₂)).apply_symm_apply Z₀
  have hθθ' : θ = shSc τ g • θ' := by
    apply (Biadjunction.rightMateLinearEquiv k (BBC G₁) (BBC G₂)).injective
    rw [map_smul]
    exact hZ₀.trans (congrArg (shSc τ g • ·) hθ'm.symm)
  have hbase : IsDiag P (Biadjunction.rightMate (BBC G₁) (BBC G₂) θ')
      (layList RD (wt RD (wt RD μ v) g.dom) [([], rotSh g, [])]) := by
    rw [hθ'm]; exact hZ₀l
  have hW := (IsDiag.rightMate_whiskerRight hz V hbase).rightMate_whiskerLeft hz Uh
  have hX : IsDiag P (Uh ◁ (θ ▷ V))
      (((layList RD (wt RD μ v) [([], g, [])]).map (·.wr V.obj.word)).map (·.wl Uh.obj)) :=
    (hθ.whiskerRight V).whiskerLeft Uh
  have e : obC P μ ν (u ++ g.dom ++ v) hs = Uh ≫ (G₁ ≫ V) := by
    refine Bicat.Hom.ext (Obj.ext ?_ ?_)
    · show wt RD μ (u ++ g.dom ++ v) = wt RD (wt RD (wt RD μ v) g.dom) u
      rw [hu, hs]
    · show wd RD μ (u ++ g.dom ++ v) =
        wd RD (wt RD (wt RD μ v) g.dom) u ++ (wd RD (wt RD μ v) g.dom ++ wd RD μ v)
      simp [wd_append, wt_append, List.append_assoc]
  have e' : obC P μ ν (u ++ g.cod ++ v) ht = Uh ≫ (G₂ ≫ V) := by
    refine Bicat.Hom.ext (Obj.ext ?_ ?_)
    · show wt RD μ (u ++ g.cod ++ v) = wt RD (wt RD (wt RD μ v) g.dom) u
      rw [hu, ht]
    · show wd RD μ (u ++ g.cod ++ v) =
        wd RD (wt RD (wt RD μ v) g.dom) u ++ (wd RD (wt RD μ v) g.cod ++ wd RD μ v)
      simp [wd_append, wt_append, List.append_assoc, h₂]
  have hdg : IsDiag P (show obC P μ ν _ hs ⟶ obC P μ ν _ ht from
      dgC P μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)])
      (((layList RD (wt RD μ v) [([], g, [])]).map (·.wr V.obj.word)).map (·.wl Uh.obj)) := by
    refine IsDiag.congr (P := P) (θ := (show obC P μ ν _ hs ⟶ obC P μ ν _ ht from
      dgC P μ (u ++ g.dom ++ v) (u ++ g.cod ++ v) [(u, g, v)]))
      (isDgC_dg μ (show SChain (u ++ g.dom ++ v) [(u, g, v)] (u ++ g.cod ++ v) from
        ⟨rfl, rfl⟩)) ?_
    simp only [layList_cons, layList_nil, List.map_cons, List.map_nil]
    congr 1
    rw [show V.obj.word = wd RD μ v from rfl, lay_wr_eq RD μ (wt RD μ v) v [] [] g rfl,
      show Uh.obj = ob RD (wt RD (wt RD μ v) g.dom) u from rfl,
      lay_wl_eq RD μ (wt RD (wt RD μ v) g.dom) u [] ([] ++ v) g ?_]
    · simp
    · simp [wt_append]
  have heq := hdg.eq_eqToHom hX e e'
  have H := rightMate_eqToHom_conj hz e e' (Uh ◁ (θ ▷ V))
  have hsm : Uh ◁ (θ ▷ V) = shSc τ g • (Uh ◁ (θ' ▷ V)) := by
    rw [hθθ', LocallyLinear.smul_whiskerRight, LocallyLinear.whiskerLeft_smul]
  refine ⟨show P.dualHom (inv RD).toColourDuality.pivotal (obC P μ ν _ ht) ⟶
      P.dualHom (inv RD).toColourDuality.pivotal (obC P μ ν _ hs) from
    eqToHom (congrArg (P.dualHom (inv RD).toColourDuality.pivotal) e') ≫
      Biadjunction.rightMate (BBC (Uh ≫ (G₁ ≫ V))) (BBC (Uh ≫ (G₂ ≫ V))) (Uh ◁ (θ' ▷ V)) ≫
        eqToHom (congrArg (P.dualHom (inv RD).toColourDuality.pivotal) e).symm, ?_, ?_⟩
  · rw [mateC_apply]
    refine (congrArg (Biadjunction.rightMate (BBC (obC P μ ν _ hs)) (BBC (obC P μ ν _ ht)))
      heq).trans ?_
    rw [H, hsm, Biadjunction.rightMate_smul, Linear.smul_comp, Linear.comp_smul]
  · have hfin : IsDiag P (eqToHom (congrArg (P.dualHom (inv RD).toColourDuality.pivotal) e') ≫
        Biadjunction.rightMate (BBC (Uh ≫ (G₁ ≫ V))) (BBC (Uh ≫ (G₂ ≫ V))) (Uh ◁ (θ' ▷ V)) ≫
          eqToHom (congrArg (P.dualHom (inv RD).toColourDuality.pivotal) e).symm)
        (((layList RD (wt RD (wt RD μ v) g.dom) [([], rotSh g, [])]).map
          (·.wl (P.dualHom (inv RD).toColourDuality.pivotal V).obj)).map
            (·.wr (P.dualHom (inv RD).toColourDuality.pivotal Uh).obj.word)) :=
      (hW.comp_eqToHom _).eqToHom_comp _
    refine hfin.congr ?_
    have eV := congrArg Bicat.Hom.obj (dual_obC P μ (wt RD μ v) v rfl)
    have eU := congrArg (fun x => (Bicat.Hom.obj x).word)
      (dual_obC P (wt RD (wt RD μ v) g.dom) ν u hu)
    simp only [obC_obj, ob_word] at eV eU
    simp only [layList_cons, layList_nil, List.map_cons, List.map_nil]
    rw [show V = obC P μ (wt RD μ v) v rfl from rfl, eV,
      show Uh = obC P (wt RD (wt RD μ v) g.dom) ν u hu from rfl, eU,
      lay_wl_eq RD _ (wt RD μ v) (rd v) [] [] (rotSh g)
        (by simp [rotSh_dom, wt_rd_of RD _ _ g.cod h₂]),
      lay_wr_eq RD ν _ (rd u) _ [] (rotSh g) (wt_rd_of RD _ _ u hu)]
    simp

/-! ## The rotation of upward normal-form diagrams -/

include hDot hCross in
/-- The rotation of a single upward layer. -/
theorem rotC_dg_single (μ ν : X) (x : LayerData I) (hx : IsUpSh x.2.1)
    (hs : wt RD μ (x.1 ++ x.2.1.dom ++ x.2.2) = ν) (ht : wt RD μ (x.1 ++ x.2.1.cod ++ x.2.2) = ν) :
    rotC P hz μ ν _ _ _ _ hs ht rfl rfl (dgC P μ _ _ [x]) =
      shSc τ x.2.1 • dgC P ν (rd (x.1 ++ x.2.1.cod ++ x.2.2)) (rd (x.1 ++ x.2.1.dom ++ x.2.2))
        [rotLD x] := by
  obtain ⟨u, g, v⟩ := x
  obtain ⟨Z, hZ, hZl⟩ := mateC_layer (hz := hz) τ hDot hCross μ ν u v g hx hs ht
  rw [rotC_apply, hZ, Linear.smul_comp, Linear.comp_smul]
  congr 1
  have H := (hZl.eqToHom_comp (rotC_e₁ P μ ν _ _ ht rfl)).comp_eqToHom
    (rotC_e₁ P μ ν _ _ hs rfl).symm
  have H' := isDgC_dg (P := P) ν (sChain_rotLs
    (show SChain (u ++ g.dom ++ v) [(u, g, v)] (u ++ g.cod ++ v) from ⟨rfl, rfl⟩))
  simpa using H.eq_eqToHom H' rfl rfl

include hDot hCross in
/-- **The rotation of an upward normal-form diagram is the diagram of the rotated layers in
reversed order**, times the product of the scalars `τ j i` of its crossings
`E_j E_i ⟶ E_i E_j`. -/
theorem rotC_dg (μ ν : X) {s t : List (Letter I)} (ls : List (LayerData I)) (h : SChain s ls t)
    (hup : ∀ x ∈ ls, IsUpSh x.2.1) (hs : wt RD μ s = ν) (ht : wt RD μ t = ν) :
    rotC P hz μ ν s t (rd s) (rd t) hs ht rfl rfl (dgC P μ s t ls) =
      (ls.map fun x => shSc τ x.2.1).prod • dgC P ν (rd t) (rd s) (rotLs ls) := by
  induction ls generalizing s with
  | nil =>
    obtain rfl : s = t := h
    rw [dgC_nil, rotC_id, rotLs_nil, dgC_nil, List.map_nil, List.prod_nil, one_smul]
  | cons x ls ih =>
    obtain ⟨rfl, h'⟩ := h
    have hr : wt RD μ (x.1 ++ x.2.1.cod ++ x.2.2) = ν := by
      rw [← ht, SChain.wt_eq RD μ h']
    rw [show x :: ls = [x] ++ ls from rfl, ← dgC_comp (show SChain _ [x] _ from ⟨rfl, rfl⟩) h',
      rotC_comp P hz μ ν _ _ _ _ _ _ hs hr ht rfl rfl rfl,
      ih h' (fun y hy => hup y (List.mem_cons_of_mem x hy)) hr,
      rotC_dg_single τ hDot hCross μ ν x (hup x List.mem_cons_self) hs hr,
      Linear.smul_comp, Linear.comp_smul, smul_smul, rotLs_append,
      show rotLs [x] = [rotLD x] from rfl,
      dgC_comp (sChain_rotLs h') (show SChain (rd (x.1 ++ x.2.1.cod ++ x.2.2)) [rotLD x]
        (rd (x.1 ++ x.2.1.dom ++ x.2.2)) from
          sChain_rotLs (show SChain _ [x] _ from ⟨rfl, rfl⟩)),
      List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, mul_comm]

include hDot hCross in
/-- `rotC_dg` with the boundaries of the rotation given as `s'`, `t'`. -/
theorem rotC_dg' (μ ν : X) {s t s' t' : List (Letter I)} (ls : List (LayerData I))
    (h : SChain s ls t) (hup : ∀ x ∈ ls, IsUpSh x.2.1) (hs : wt RD μ s = ν) (ht : wt RD μ t = ν)
    (es : rd s = s') (et : rd t = t') :
    rotC P hz μ ν s t s' t' hs ht es et (dgC P μ s t ls) =
      (ls.map fun x => shSc τ x.2.1).prod • dgC P ν t' s' (rotLs ls) := by
  subst es et
  exact rotC_dg τ hDot hCross μ ν ls h hup hs ht

end Rot

/-! ## Rotation of KLR diagrams -/

section KLRRot

/-- The rotation of a KLR layer by `180°`: the strands to its left and right are exchanged and
reversed, the generator is unchanged (a crossing `c d ⟶ d c` rotates to a crossing `c d ⟶ d c`,
a dot to a dot). -/
def rotKL (L : Layer (KLR.Diagram.sig I)) : Layer (KLR.Diagram.sig I) :=
  ⟨(), L.right.reverse, L.gen, L.left.reverse⟩

/-- The reversed sequence. -/
def kobjR (a : Obj (KLR.Diagram.sig I)) : Obj (KLR.Diagram.sig I) := ⟨(), a.word.reverse⟩

@[simp] theorem kobjR_word (a : Obj (KLR.Diagram.sig I)) : (kobjR a).word = a.word.reverse := rfl

theorem gen_cod_reverse (g : KLR.Diagram.Gen I) : g.cod.reverse = g.dom := by cases g <;> rfl

theorem gen_dom_reverse (g : KLR.Diagram.Gen I) : g.dom.reverse = g.cod := by cases g <;> rfl

theorem rotKL_dom (L : Layer (KLR.Diagram.sig I)) : (rotKL L).dom = kobjR L.cod :=
  KLR.Diagram.obj_ext (by simp [rotKL, kobjR, gen_cod_reverse])

theorem rotKL_cod (L : Layer (KLR.Diagram.sig I)) : (rotKL L).cod = kobjR L.dom :=
  KLR.Diagram.obj_ext (by simp [rotKL, kobjR, gen_dom_reverse])

theorem chain_rotKL {a b : Obj (KLR.Diagram.sig I)} {ls : List (Layer (KLR.Diagram.sig I))}
    (h : Chain a ls b) : Chain (kobjR b) (ls.map rotKL).reverse (kobjR a) := by
  induction ls generalizing a with
  | nil => exact congrArg kobjR (show a = b from h).symm
  | cons L ls ih =>
    obtain ⟨-, rfl, hc⟩ := h
    rw [List.map_cons, List.reverse_cons]
    exact (ih hc).append ⟨Layer.valid_of_subsingleton _, rotKL_dom L, rotKL_cod L⟩

/-- **The rotation of a KLR diagram by `180°`**: the rotated layers in reversed order. -/
def rotKD {a b : Obj (KLR.Diagram.sig I)} (D : a ⟶ b) : kobjR b ⟶ kobjR a :=
  Diagram.mk ((Diagram.layers D).map rotKL).reverse (chain_rotKL (Diagram.chain D))

@[simp] theorem layers_rotKD {a b : Obj (KLR.Diagram.sig I)} (D : a ⟶ b) :
    Diagram.layers (rotKD D) = ((Diagram.layers D).map rotKL).reverse := rfl

/-- The scalar acquired by a KLR diagram placed on upward strands under rotation: the product of
`τ c d` over its crossings `c d ⟶ d c`. -/
def wK (τ : I → I → k) {a b : Obj (KLR.Diagram.sig I)} (D : a ⟶ b) : k :=
  ((Diagram.layers D).map fun L => shSc τ (upShape L.gen)).prod

/-- A KLR layer as a normal-form layer on downward strands. -/
def dnLDC (L : Layer (KLR.Diagram.sig I)) : LayerData I := (dns L.left, dnShape L.gen, dns L.right)

theorem sChain_dnLDC {a b : Obj (KLR.Diagram.sig I)} {ls : List (Layer (KLR.Diagram.sig I))}
    (h : Chain a ls b) : SChain (dns a.word) (ls.map dnLDC) (dns b.word) := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih =>
    obtain ⟨-, rfl, hc⟩ := h
    refine ⟨?_, ?_⟩
    · simp [dnLDC, dnShape_dom]
    · have := ih hc
      simpa [dnLDC, dnShape_cod] using this

theorem rd_ups (l : List I) : rd (ups l) = dns l.reverse := by
  simp [rd, ups, dns, List.map_map, Function.comp_def, List.map_reverse, Letter.dual]

theorem rotLD_upLD (L : Layer (KLR.Diagram.sig I)) : rotLD (upLD L) = dnLDC (rotKL L) := by
  obtain ⟨_, l, g, r⟩ := L
  simp only [rotLD, upLD, dnLDC, rotKL, rd_ups]
  congr 2
  cases g <;> rfl

theorem rotLs_map_upLD (ls : List (Layer (KLR.Diagram.sig I))) :
    rotLs (ls.map upLD) = ((ls.map rotKL).reverse).map dnLDC := by
  simp [rotLs, List.map_reverse, List.map_map, Function.comp_def, rotLD_upLD]

theorem isUpSh_upShape (g : KLR.Diagram.Gen I) : IsUpSh (upShape g) := by
  cases g with
  | dot c => exact Or.inl ⟨c, rfl⟩
  | cross c d => exact Or.inr ⟨c, d, rfl⟩

variable {P : Presentation.{w, max u v} (psig RD) k}

theorem diag_upDiag (μ : X) {a b : Obj (KLR.Diagram.sig I)} (D : a ⟶ b) :
    P.diag (upDiag RD μ D) = dgC P μ (ups a.word) (ups b.word) ((Diagram.layers D).map upLD) := by
  rw [dgC_of (sChain_upLD (Diagram.chain D))]
  exact P.diag_eq_of_layers_eq (by simp [layList, upLay, upLD, List.map_map])

theorem diag_dnDiag (ν : X) {a b : Obj (KLR.Diagram.sig I)} (D : a ⟶ b) :
    P.diag (dnDiag RD ν D) = dgC P ν (dns a.word) (dns b.word) ((Diagram.layers D).map dnLDC) := by
  rw [dgC_of (sChain_dnLDC (Diagram.chain D))]
  exact P.diag_eq_of_layers_eq (by simp [layList, dnLay, dnLDC, List.map_map])

variable {hz : P.PivotalZigzags (inv RD).toColourDuality} (τ : I → I → k)
  (hDot : ∀ (i : I) (μ : X), P.diag (rotDotR RD i μ) = P.diag (downDot RD i μ))
  (hCross : ∀ (j i : I) (μ : X),
    P.diag (rotCrossR RD j i μ) = τ j i • P.diag (downCross RD j i μ))

include hDot hCross in
/-- **The rotation of a KLR diagram on upward strands is the rotated KLR diagram on downward
strands**, times the product `wK τ D` of the scalars of its crossings. -/
theorem rotC_upDiag (μ ν : X) {a b : Obj (KLR.Diagram.sig I)} (D : a ⟶ b)
    (hs : wt RD μ (ups a.word) = ν) (ht : wt RD μ (ups b.word) = ν) :
    rotC P hz μ ν (ups a.word) (ups b.word) (dns (kobjR a).word) (dns (kobjR b).word) hs ht
        (rd_ups a.word) (rd_ups b.word) (P.diag (upDiag RD μ D)) =
      wK τ D • P.diag (dnDiag RD ν (rotKD D)) := by
  rw [diag_upDiag, rotC_dg' τ hDot hCross μ ν _ (sChain_upLD (Diagram.chain D))
    (fun x hx => by
      obtain ⟨L, -, rfl⟩ := List.mem_map.1 hx
      exact isUpSh_upShape L.gen) hs ht, diag_dnDiag, rotLs_map_upLD]
  congr 1
  simp [wK, List.map_map, Function.comp_def, upLD]

end KLRRot

/-! ## Rotation of linear combinations of KLR diagrams -/

section KLRLin

theorem rotKD_comp {a b c : Obj (KLR.Diagram.sig I)} (D : a ⟶ b) (E : b ⟶ c) :
    rotKD (D ≫ E) = rotKD E ≫ rotKD D :=
  Diagram.ext (by simp [List.map_append, List.reverse_append])

theorem rotKD_id (a : Obj (KLR.Diagram.sig I)) : rotKD (𝟙 a) = 𝟙 (kobjR a) :=
  Diagram.ext (by simp)

theorem wK_comp (τ : I → I → k) {a b c : Obj (KLR.Diagram.sig I)} (D : a ⟶ b) (E : b ⟶ c) :
    wK τ (D ≫ E) = wK τ D * wK τ E := by
  simp [wK, List.map_append, List.prod_append]

theorem wK_id (τ : I → I → k) (a : Obj (KLR.Diagram.sig I)) : wK τ (𝟙 a) = 1 := by
  simp [wK]

/-- **The rotation of linear combinations of KLR diagrams**, with the scalars `wK τ`: the
`k`-linear map sending a diagram `D` to `wK τ D • rotKD D`. -/
def rotKLin (τ : I → I → k) {a b : Obj (KLR.Diagram.sig I)} :
    LinDiagram k a b →ₗ[k] LinDiagram k (kobjR b) (kobjR a) :=
  Finsupp.lsum k fun D => LinearMap.toSpanSingleton k _ (wK τ D • LinDiagram.of (rotKD D))

theorem rotKLin_single (τ : I → I → k) {a b : Obj (KLR.Diagram.sig I)} (D : a ⟶ b) (r : k) :
    rotKLin τ (Finsupp.single D r : LinDiagram k a b) = r • wK τ D • LinDiagram.of (rotKD D) := by
  erw [rotKLin, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

theorem rotKLin_of (τ : I → I → k) {a b : Obj (KLR.Diagram.sig I)} (D : a ⟶ b) :
    rotKLin τ (LinDiagram.of D : LinDiagram k a b) = wK τ D • LinDiagram.of (rotKD D) := by
  rw [rotKLin_single, one_smul]

theorem rotKLin_id (τ : I → I → k) (a : Obj (KLR.Diagram.sig I)) :
    rotKLin τ (𝟙 (Free.of k a)) = 𝟙 (Free.of k (kobjR a)) := by
  rw [show (𝟙 (Free.of k a)) = LinDiagram.of (𝟙 a) from rfl, rotKLin_of, rotKD_id, wK_id, one_smul]
  rfl

/-- The rotation is contravariant. -/
theorem rotKLin_comp (τ : I → I → k) {a b c : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b)
    (g : LinDiagram k b c) : rotKLin τ (f ≫ g) = rotKLin τ g ≫ rotKLin τ f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [Limits.zero_comp, map_zero, map_zero, Limits.comp_zero]
  | add f f' hf hf' => rw [Preadditive.add_comp, map_add, hf, hf', map_add, Preadditive.comp_add]
  | single D r =>
    induction g using Finsupp.induction_linear with
    | zero => rw [Limits.comp_zero, map_zero, map_zero, Limits.zero_comp]
    | add g g' hg hg' =>
      rw [Preadditive.comp_add, map_add, hg, hg', map_add, Preadditive.add_comp]
    | single E s =>
      rw [← Finsupp.smul_single_one D r, ← Finsupp.smul_single_one E s]
      change rotKLin τ ((r • LinDiagram.of D) ≫ (s • LinDiagram.of E)) =
        rotKLin τ (s • LinDiagram.of E) ≫ rotKLin τ (r • LinDiagram.of D)
      rw [Linear.smul_comp, Linear.comp_smul, ← LinDiagram.of_comp, map_smul, map_smul, map_smul,
        map_smul, rotKLin_of, rotKLin_of, rotKLin_of, rotKD_comp, wK_comp, Linear.smul_comp,
        Linear.smul_comp, Linear.comp_smul, Linear.comp_smul, ← LinDiagram.of_comp]
      simp only [smul_smul]
      congr 1
      ring

theorem ofFn_reverse' {α : Type*} {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).reverse = List.ofFn fun a => f (Fin.rev a) := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map, ← List.map_reverse, List.finRange_reverse, List.map_map]
  rfl

/-- A `k`-linear, unital, antimultiplicative map sends `ncEval y p` to the evaluation of the
reversed polynomial on the images of the reversed variables. -/
theorem ncEval_antihom {A B : Type*} [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (φ : A →ₗ[k] B) (h1 : φ 1 = 1) (hmul : ∀ x y, φ (x * y) = φ y * φ x) {n : ℕ}
    (y : Fin n → A) (p : MvPolynomial (Fin n) k) :
    φ (KLR.ncEval y p) =
      KLR.ncEval (fun a => φ (y (Fin.rev a))) (MvPolynomial.rename Fin.rev p) := by
  have hpow : ∀ (x : A) (m : ℕ), φ (x ^ m) = φ x ^ m := by
    intro x m
    induction m with
    | zero => rw [pow_zero, pow_zero, h1]
    | succ m ih => rw [pow_succ, hmul, ih, pow_succ']
  have hlist : ∀ l : List A, φ l.prod = (l.map φ).reverse.prod := by
    intro l
    induction l with
    | nil => simp [h1]
    | cons x l ih =>
      rw [List.prod_cons, hmul, ih, List.map_cons, List.reverse_cons, List.prod_append,
        List.prod_singleton]
  have halg : ∀ c : k, φ (algebraMap k A c) = algebraMap k B c := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, Algebra.algebraMap_eq_smul_one]
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [Rescale.ncEval_add, map_add, hp, hq, map_add, Rescale.ncEval_add]
  | monomial s c =>
    rw [Rescale.ncEval_monomial, MvPolynomial.rename_monomial, Rescale.ncEval_monomial, hmul,
      halg, hlist, ← Algebra.commutes]
    congr 1
    rw [List.map_ofFn, ofFn_reverse']
    congr 1
    refine congrArg List.ofFn (funext fun a => ?_)
    simp only [Function.comp_apply, hpow]
    congr 1
    have := Finsupp.mapDomain_apply Fin.rev_injective s (Fin.rev a)
    rw [Fin.rev_rev] at this
    rw [this]

end KLRLin

/-! ## The rotation of KLR relations on upward strands -/

section Bridge

variable {P : Presentation.{w, max u v} (psig RD) k}
  {hz : P.PivotalZigzags (inv RD).toColourDuality} (τ : I → I → k)
  (hDot : ∀ (i : I) (μ : X), P.diag (rotDotR RD i μ) = P.diag (downDot RD i μ))
  (hCross : ∀ (j i : I) (μ : X),
    P.diag (rotCrossR RD j i μ) = τ j i • P.diag (downCross RD j i μ))

theorem dnLin_single (ν : X) {a b : Obj (KLR.Diagram.sig I)} (D : a ⟶ b) (r : k) :
    dnLin RD k ν (Finsupp.single D r : LinDiagram k a b) =
      r • LinDiagram.of (dnDiag RD ν D) := by
  rw [dnLin, Finsupp.mapDomain_single, Finsupp.smul_single_one]

theorem dnLin_smul (ν : X) {a b : Obj (KLR.Diagram.sig I)} (r : k) (f : LinDiagram k a b) :
    dnLin RD k ν (r • f) = r • dnLin RD k ν f :=
  Finsupp.mapDomain_smul _ _

theorem dnLin_add (ν : X) {a b : Obj (KLR.Diagram.sig I)} (f g : LinDiagram k a b) :
    dnLin RD k ν (f + g) = dnLin RD k ν f + dnLin RD k ν g :=
  Finsupp.mapDomain_add

theorem upLin_single (μ : X) {a b : Obj (KLR.Diagram.sig I)} (D : a ⟶ b) (r : k) :
    upLin RD k μ (Finsupp.single D r : LinDiagram k a b) =
      r • LinDiagram.of (upDiag RD μ D) := by
  rw [upLin, Finsupp.mapDomain_single, Finsupp.smul_single_one]

include hDot hCross in
/-- **The rotation of a linear combination of KLR diagrams on upward strands** is the rotated
linear combination (`rotKLin τ`) on downward strands. -/
theorem rotC_upLin (μ ν : X) {a b : Obj (KLR.Diagram.sig I)} (f : LinDiagram k a b)
    (hs : wt RD μ (ups a.word) = ν) (ht : wt RD μ (ups b.word) = ν) :
    rotC P hz μ ν (ups a.word) (ups b.word) (dns (kobjR a).word) (dns (kobjR b).word) hs ht
        (rd_ups a.word) (rd_ups b.word) (P.lin (upLin RD k μ f)) =
      P.lin (dnLin RD k ν (rotKLin τ f)) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [show upLin RD k μ (0 : LinDiagram k a b) = 0 from Finsupp.mapDomain_zero, lin_zero,
      map_zero, map_zero, show dnLin RD k ν (0 : LinDiagram k (kobjR b) (kobjR a)) = 0 from
        Finsupp.mapDomain_zero, lin_zero]
  | add f g hf hg =>
    rw [show upLin RD k μ (f + g) = upLin RD k μ f + upLin RD k μ g from Finsupp.mapDomain_add,
      lin_add, map_add, hf, hg, map_add, dnLin_add, lin_add]
  | single D r =>
    rw [upLin_single, lin_smul, lin_of, map_smul, rotC_upDiag τ hDot hCross, rotKLin_single,
      dnLin_smul, dnLin_smul, dnLin, Finsupp.mapDomain_single, lin_smul, lin_smul, lin_of]

end Bridge

end Categorification.KL3.Diagram.CL
