/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.NestedCups

/-!
# Mates of whiskered 2-morphisms in pivotal extensions

For a presentation `Q` of a pivotal extension `S.pivotal E` (with the zigzag relations) every
1-morphism `x` of `Q.Bicat` is biadjoint to its dual word `x*` by nested cups and caps
(`Presentation.biadj`). This file computes the mates (rotations) of whiskered 2-morphisms and
of mates, at the level of lists of layers (`IsDiag`):

* `IsDiag.comp_left_unit`, `IsDiag.comp_left_counit`: the unit and counit of a composite of
  biadjunctions are classes of the evident nested diagrams;
* `cupLayers_append`, `capLayers_append`: the nested cups and caps of a concatenated word are
  those of the composite biadjunction;
* `rightMate_id_eq_eqToHom`: two biadjunctions `x ⊣⊢ y` with the same unit and counit
  layers give the trivial comparison;
* `rightMate_biadj_comp`: the mate for the biadjunction of a concatenated word is the mate for
  the composite biadjunction;
* `IsDiag.rightMate_whiskerLeft`, `IsDiag.rightMate_whiskerRight`: **the mate of a whiskered
  2-morphism is the whiskered mate** (`(u ◁ θ ▷ v)^* = v* ◁ θ^* ▷ u*` in string diagrams);
* `cupLayers_dualWord`, `capLayers_dualWord`: the nested cups and caps of a dual word are the
  nested cups and caps of the exchanged biadjunction;
* `rightMate_rightMate`: **rotating twice is the identity** (up to `x** = x`), using that all
  2-morphisms are cyclic.

This is generic (it does not depend on KL III).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory Bicategory StringDiagrams Presentation Biadjunction

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R]

/-! ## Units and counits of composite biadjunctions -/

section Comp

variable {P : Presentation.{w, v} S R} [S.IsEven] {l m n : P.Bicat}

theorem IsDiag.comp_left_unit {f₁ : l ⟶ m} {g₁ : m ⟶ l} {f₂ : m ⟶ n} {g₂ : n ⟶ m}
    (P₁ : f₁ ⊣⊢ g₁) (P₂ : f₂ ⊣⊢ g₂) {ls ms : List (Layer S)}
    (h₁ : IsDiag P P₁.left.unit ls) (h₂ : IsDiag P P₂.left.unit ms) :
    IsDiag P (P₁.comp P₂).left.unit
      (ls ++ (ms.map (·.wr g₁.obj.word)).map (·.wl f₁.obj)) := by
  simp only [Biadjunction.comp_left, Bicategory.Adjunction.comp_unit,
    Bicategory.Adjunction.compUnit, bicategoricalComp]
  refine IsDiag.congr (IsDiag.comp h₁ (IsDiag.comp (ls := []) ?_
      (IsDiag.comp (IsDiag.whiskerLeft _ (IsDiag.whiskerRight _ h₂)) (IsDiag.comp (ls := []) ?_
      (isDiag_id _))))) ?_
  · isdiag_triv
  · isdiag_triv
  · simp

theorem IsDiag.comp_left_counit {f₁ : l ⟶ m} {g₁ : m ⟶ l} {f₂ : m ⟶ n} {g₂ : n ⟶ m}
    (P₁ : f₁ ⊣⊢ g₁) (P₂ : f₂ ⊣⊢ g₂) {ls ms : List (Layer S)}
    (h₁ : IsDiag P P₁.left.counit ls) (h₂ : IsDiag P P₂.left.counit ms) :
    IsDiag P (P₁.comp P₂).left.counit
      ((ls.map (·.wr f₂.obj.word)).map (·.wl g₂.obj) ++ ms) := by
  simp only [Biadjunction.comp_left, Bicategory.Adjunction.comp_counit,
    Bicategory.Adjunction.compCounit, bicategoricalComp]
  refine IsDiag.congr (IsDiag.comp (isDiag_id _) (IsDiag.comp (ls := []) ?_
      (IsDiag.comp (IsDiag.whiskerLeft _ (IsDiag.whiskerRight _ h₁)) (IsDiag.comp (ls := []) ?_
      h₂)))) ?_
  · isdiag_triv
  · isdiag_triv
  · simp

theorem IsDiag.eqToHom_comp {x y z : l ⟶ m} (h : x = y) {θ : y ⟶ z} {ls : List (Layer S)}
    (hθ : IsDiag P θ ls) : IsDiag P (eqToHom h ≫ θ) ls :=
  ((isDiag_eqToHom h).comp hθ).congr rfl

theorem IsDiag.comp_eqToHom {x y z : l ⟶ m} {θ : x ⟶ y} (h : y = z) {ls : List (Layer S)}
    (hθ : IsDiag P θ ls) : IsDiag P (θ ≫ eqToHom h) ls :=
  (hθ.comp (isDiag_eqToHom h)).congr (List.append_nil _)

/-- Two 2-morphisms that are classes of diagrams with the same layers agree, up to the
identification of their boundaries. -/
theorem IsDiag.eq_eqToHom {x y x' y' : l ⟶ m} {θ : x ⟶ y} {θ' : x' ⟶ y'} {ls : List (Layer S)}
    (h : IsDiag P θ ls) (h' : IsDiag P θ' ls) (e : x = x') (e' : y = y') :
    θ = eqToHom e ≫ θ' ≫ eqToHom e'.symm := by
  subst e e'
  obtain ⟨D, rfl, hD⟩ := h
  obtain ⟨D', rfl, hD'⟩ := h'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact P.diag_eq_of_layers_eq (hD.trans hD'.symm)

theorem IsDiag.eq {x y : l ⟶ m} {θ θ' : x ⟶ y} {ls : List (Layer S)}
    (h : IsDiag P θ ls) (h' : IsDiag P θ' ls) : θ = θ' := by
  simpa using h.eq_eqToHom h' rfl rfl

/-- The right mate of a class of a diagram, for biadjunctions whose units and counits are
classes of diagrams with given layers. -/
theorem IsDiag.rightMate {x x' : l ⟶ m} {y y' : m ⟶ l} (Q₁ : x ⊣⊢ y) (Q₂ : x' ⊣⊢ y')
    {cl al ls : List (Layer S)} (hcup : IsDiag P Q₁.left.unit cl)
    (hcap : IsDiag P Q₂.left.counit al) {θ : x ⟶ x'} (hθ : IsDiag P θ ls) :
    IsDiag P (Biadjunction.rightMate Q₁ Q₂ θ)
      (cl.map (·.wl y'.obj) ++ (ls.map (·.wr y.obj.word)).map (·.wl y'.obj) ++
        al.map (·.wr y.obj.word)) := by
  obtain ⟨cup, hcup, rfl⟩ := hcup
  obtain ⟨cap', hcap, rfl⟩ := hcap
  obtain ⟨d, rfl, rfl⟩ := hθ
  exact ⟨_, rightMate_diag Q₁ Q₂ cup hcup cap' hcap d, layers_rightRotateD _ _ _ _ _ _ _⟩

/-- **Comparison of biadjunctions.** Two biadjunctions `x ⊣⊢ y` and `x ⊣⊢ y'` (with `y = y'`)
whose counits are classes of diagrams with the same layers, the first with a unit that is a
class of a diagram, induce the trivial comparison `y' ⟶ y`. -/
theorem rightMate_id_eq_eqToHom {x : l ⟶ m} {y y' : m ⟶ l} (Q₁ : x ⊣⊢ y) (Q₂ : x ⊣⊢ y')
    (h : y = y') {cl al : List (Layer S)} (hcup : IsDiag P Q₁.left.unit cl)
    (hcap : IsDiag P Q₁.left.counit al) (hcap' : IsDiag P Q₂.left.counit al) :
    Biadjunction.rightMate Q₁ Q₂ (𝟙 x) = eqToHom h.symm := by
  subst h
  obtain ⟨D, hD, hDl⟩ := IsDiag.rightMate Q₁ Q₂ hcup hcap' (isDiag_id x)
  obtain ⟨D', hD', hD'l⟩ := IsDiag.rightMate Q₁ Q₁ hcup hcap (isDiag_id x)
  rw [hD, eqToHom_refl, ← Biadjunction.rightMate_id Q₁, hD']
  exact P.diag_eq_of_layers_eq (hDl.trans hD'l.symm)

end Comp

/-! ## Nested cups and caps of concatenated and dual words -/

section Nested

variable {E : S.ColourInvolution} [S.IsEven]

omit [S.IsEven] in
theorem cupLayers_start : ∀ (r : S.Region) (w : List S.Colour), S.ok r w →
    ∀ L ∈ cupLayers (E := E) r w, L.start = r
  | _, [], _ => by simp [cupLayers]
  | r, c :: w, h => by
    intro L hL
    simp only [cupLayers, List.mem_cons, List.mem_map] at hL
    rcases hL with rfl | ⟨L', -, rfl⟩
    · exact h.1
    · rfl

omit [S.IsEven] in
theorem cupLayers_append : ∀ (r : S.Region) (w w' : List S.Colour), S.ok r (w ++ w') →
    cupLayers (E := E) r (w ++ w') = cupLayers (E := E) r w ++
      ((cupLayers (E := E) (S.endR r w) w').map
        (·.wr (E.toColourDuality.pivotal.dualWord w))).map
          (·.wl (⟨r, w⟩ : Obj (S.pivotal E.toColourDuality)))
  | r, [], w', h => by
    simp only [List.nil_append, Signature.endR_nil, cupLayers, List.map_map]
    conv_lhs => rw [← List.map_id (cupLayers r w')]
    refine List.map_congr_left fun L hL => ?_
    have := cupLayers_start (E := E) r w' h L hL
    obtain ⟨st, lf, g, rt⟩ := L
    simp only [Function.comp_apply, Layer.wr, Layer.wl, Signature.ColourDuality.dualWord_nil,
      List.append_nil, List.nil_append]
    rw [← this]; rfl
  | r, c :: w, w', h => by
    have ih := cupLayers_append (S.colourTgt c) w w' h.2
    simp only [List.cons_append, cupLayers, ih, List.map_append, List.map_map,
      Signature.endR_cons, List.cons_append]
    congr 2
    refine List.map_congr_left fun L _ => ?_
    simp [Layer.wr, Layer.wl, List.append_assoc]

omit [S.IsEven] in
theorem capLayers_append (r r' : S.Region) : ∀ (w w' : List S.Colour),
    capLayers (E := E) r (w ++ w') =
      ((capLayers (E := E) r' w).map (·.wr w')).map
        (·.wl (⟨r, E.toColourDuality.pivotal.dualWord w'⟩ : Obj (S.pivotal E.toColourDuality))) ++
        capLayers (E := E) r w'
  | [], w' => by simp [capLayers]
  | c :: w, w' => by
    have ih := capLayers_append r r' w w'
    simp only [List.cons_append, capLayers, ih, List.map_cons, List.cons_append, List.map_map]
    congr 1
    simp [Layer.wr, Layer.wl, List.append_assoc]

end Nested

/-! ## Mates for the biadjunctions of concatenated words -/

section Words

variable {E : S.ColourInvolution} [S.IsEven]
  {Q : Presentation.{w, v} (S.pivotal E.toColourDuality) R}
  (hz : Q.PivotalZigzags E.toColourDuality)

/-- The biadjunctions `x ⊣⊢ x*` of all 1-morphisms, by nested cups and caps. -/
local notation "BB" => biadj (pivotalBiadj E Q hz)

variable {l m n : Q.Bicat}

theorem isDiag_biadj_left_unit (x : l ⟶ m) :
    IsDiag Q (BB x).left.unit (cupLayers (E := E) l.region x.obj.word) :=
  biadjW_left_unit_isDiag hz x.obj.word x rfl

theorem isDiag_biadj_left_counit (x : l ⟶ m) :
    IsDiag Q (BB x).left.counit (capLayers (E := E) m.region x.obj.word) :=
  biadjW_left_counit_isDiag hz x.obj.word x rfl

theorem isDiag_biadj_right_unit (x : l ⟶ m) :
    IsDiag Q (BB x).right.unit (cupRLayers (E := E) m.region x.obj.word) :=
  biadjW_right_unit_isDiag hz x.obj.word x rfl

theorem isDiag_biadj_right_counit (x : l ⟶ m) :
    IsDiag Q (BB x).right.counit (capRLayers (E := E) l.region x.obj.word) :=
  biadjW_right_counit_isDiag hz x.obj.word x rfl

theorem isDiag_biadj_comp_left_unit (x : l ⟶ m) (y : m ⟶ n) :
    IsDiag Q ((BB x).comp (BB y)).left.unit (cupLayers (E := E) l.region (x ≫ y).obj.word) := by
  refine (IsDiag.comp_left_unit _ _ (isDiag_biadj_left_unit hz x)
    (isDiag_biadj_left_unit hz y)).congr ?_
  have hok : S.ok l.region (x.obj.word ++ y.obj.word) := by
    have := (x ≫ y).wf
    rw [Obj.WF, (x ≫ y).start_eq, Signature.pivotal_ok] at this
    exact this
  have hm : S.endR l.region x.obj.word = m.region := by
    have := x.endR_eq
    rw [Obj.endR, x.start_eq, Signature.pivotal_endR] at this
    exact this
  rw [show (x ≫ y).obj.word = x.obj.word ++ y.obj.word from rfl,
    cupLayers_append (S := S) (E := E) l.region _ _ hok, hm]
  have hx : (⟨l.region, x.obj.word⟩ : Obj (S.pivotal E.toColourDuality)) = x.obj :=
    Obj.ext x.start_eq.symm rfl
  rw [hx]
  rfl

theorem isDiag_biadj_comp_left_counit (x : l ⟶ m) (y : m ⟶ n) :
    IsDiag Q ((BB x).comp (BB y)).left.counit
      (capLayers (E := E) n.region (x ≫ y).obj.word) := by
  refine (IsDiag.comp_left_counit _ _ (isDiag_biadj_left_counit hz x)
    (isDiag_biadj_left_counit hz y)).congr ?_
  rw [show (x ≫ y).obj.word = x.obj.word ++ y.obj.word from rfl,
    capLayers_append (S := S) (E := E) n.region m.region]
  rfl

/-- **The mate for the biadjunction of a concatenated word is the mate for the composite
biadjunction**, up to the identifications `(x y)* = y* x*`. -/
theorem rightMate_biadj_comp {x x' : l ⟶ m} {y y' : m ⟶ n} (α : x ≫ y ⟶ x' ≫ y') :
    Biadjunction.rightMate (BB (x ≫ y)) (BB (x' ≫ y')) α =
      eqToHom (Q.dualHom_comp _ x' y') ≫
        Biadjunction.rightMate ((BB x).comp (BB y)) ((BB x').comp (BB y')) α ≫
          eqToHom (Q.dualHom_comp _ x y).symm := by
  rw [rightMate_eq_comp' _ ((BB x).comp (BB y)) _ ((BB x').comp (BB y'))]
  congr 1
  · refine rightMate_id_eq_eqToHom _ _ (Q.dualHom_comp _ x' y').symm
      (isDiag_biadj_comp_left_unit hz x' y') (isDiag_biadj_comp_left_counit hz x' y') ?_
    exact isDiag_biadj_left_counit hz (x' ≫ y')
  · congr 1
    refine rightMate_id_eq_eqToHom _ _ (Q.dualHom_comp _ x y) (isDiag_biadj_left_unit hz (x ≫ y))
      (isDiag_biadj_left_counit hz (x ≫ y)) ?_
    exact isDiag_biadj_comp_left_counit hz x y

/-- **The mate of a left-whiskered 2-morphism is the right-whiskered mate**:
`(h ◁ θ)^* = θ^* ▷ h*`, at the level of layers. -/
theorem IsDiag.rightMate_whiskerLeft (h : n ⟶ l) {x x' : l ⟶ m} {θ : x ⟶ x'}
    {ms : List (Layer (S.pivotal E.toColourDuality))}
    (hθ : IsDiag Q (Biadjunction.rightMate (BB x) (BB x') θ) ms) :
    IsDiag Q (Biadjunction.rightMate (BB (h ≫ x)) (BB (h ≫ x')) (h ◁ θ))
      (ms.map (·.wr (Q.dualHom E.toColourDuality.pivotal h).obj.word)) := by
  rw [rightMate_biadj_comp hz, Biadjunction.rightMate_whiskerLeft]
  exact ((hθ.whiskerRight _).comp_eqToHom _).eqToHom_comp _

/-- **The mate of a right-whiskered 2-morphism is the left-whiskered mate**:
`(θ ▷ h)^* = h* ◁ θ^*`, at the level of layers. -/
theorem IsDiag.rightMate_whiskerRight (h : m ⟶ n) {x x' : l ⟶ m} {θ : x ⟶ x'}
    {ms : List (Layer (S.pivotal E.toColourDuality))}
    (hθ : IsDiag Q (Biadjunction.rightMate (BB x) (BB x') θ) ms) :
    IsDiag Q (Biadjunction.rightMate (BB (x ≫ h)) (BB (x' ≫ h)) (θ ▷ h))
      (ms.map (·.wl (Q.dualHom E.toColourDuality.pivotal h).obj)) := by
  rw [rightMate_biadj_comp hz, Biadjunction.rightMate_whiskerRight]
  exact ((hθ.whiskerLeft _).comp_eqToHom _).eqToHom_comp _

end Words

/-! ## Rotating twice -/

section Double

variable {E : S.ColourInvolution}

omit [CommRing R] in
theorem dualWord_dualWord (w : List S.Colour) :
    E.toColourDuality.pivotal.dualWord (E.toColourDuality.pivotal.dualWord w) = w := by
  simp [Signature.ColourDuality.dualWord_eq, List.map_reverse, List.map_map, Function.comp_def,
    E.dual_dual]

omit [CommRing R] in
theorem capLayers_dualWord : ∀ (r : S.Region) (w : List S.Colour), S.ok r w →
    capLayers (E := E) r (E.toColourDuality.pivotal.dualWord w) = capRLayers (E := E) r w
  | _, [], _ => rfl
  | r, c :: w, h => by
    have ih := capLayers_dualWord (S.colourTgt c) w h.2
    rw [Signature.ColourDuality.dualWord_cons,
      capLayers_append (S := S) (E := E) r (S.colourTgt c), ih]
    simp only [capRLayers, capLayers, Signature.ColourDuality.dualWord_cons,
      Signature.ColourDuality.dualWord_nil, List.nil_append, Signature.ColourDuality.pivotal_dual,
      E.dual_dual, List.map_map]
    congr 1
    simp only [Layer.wr, Layer.wl, List.append_nil, List.cons.injEq, and_true]
    refine Layer.ext ?_ rfl rfl rfl
    show r = S.colourTgt (E.dual c)
    rw [E.tgt_dual]; exact h.1.symm

variable [S.IsEven] {Q : Presentation.{w, v} (S.pivotal E.toColourDuality) R}
  (hz : Q.PivotalZigzags E.toColourDuality)

local notation "BB" => biadj (pivotalBiadj E Q hz)

variable {l m : Q.Bicat}

omit [S.IsEven] in
theorem dualHom_dualHom (x : l ⟶ m) :
    Q.dualHom E.toColourDuality.pivotal (Q.dualHom E.toColourDuality.pivotal x) = x :=
  Bicat.Hom.ext (Obj.ext x.start_eq.symm (dualWord_dualWord (E := E) _))

theorem isDiag_biadj_dual_left_counit (x : l ⟶ m) :
    IsDiag Q (BB (Q.dualHom E.toColourDuality.pivotal x)).left.counit
      (capRLayers (E := E) l.region x.obj.word) := by
  refine (isDiag_biadj_left_counit hz _).congr ?_
  have hok : S.ok l.region x.obj.word := by
    have := x.wf
    rw [Obj.WF, x.start_eq, Signature.pivotal_ok] at this
    exact this
  exact capLayers_dualWord (S := S) (E := E) l.region x.obj.word hok

/-- Mates along equalities of 1-morphisms. -/
theorem rightMate_eqToHom_conj {A A₁ A' A₁' : l ⟶ m} (e : A = A₁) (e' : A' = A₁')
    (θ : A₁ ⟶ A₁') :
    Biadjunction.rightMate (BB A) (BB A') (eqToHom e ≫ θ ≫ eqToHom e'.symm) =
      eqToHom (congrArg (Q.dualHom E.toColourDuality.pivotal) e') ≫
        Biadjunction.rightMate (BB A₁) (BB A₁') θ ≫
          eqToHom (congrArg (Q.dualHom E.toColourDuality.pivotal) e).symm := by
  subst e e'; simp

/-- **Rotating a cyclic 2-morphism twice gives it back**, up to the identification `x** = x`. -/
theorem rightMate_rightMate {x x' : l ⟶ m} (α : x ⟶ x')
    (hα : Biadjunction.IsCyclic (BB x) (BB x') α) :
    Biadjunction.rightMate (BB (Q.dualHom E.toColourDuality.pivotal x'))
        (BB (Q.dualHom E.toColourDuality.pivotal x))
        (Biadjunction.rightMate (BB x) (BB x') α) =
      eqToHom (dualHom_dualHom x) ≫ α ≫ eqToHom (dualHom_dualHom x').symm := by
  rw [rightMate_eq_comp' _ (BB x').symm _ (BB x).symm, show
    Biadjunction.rightMate (BB x) (BB x') α = Biadjunction.leftMate (BB x) (BB x') α from hα,
    rightMate_symm_leftMate]
  congr 1
  · exact rightMate_id_eq_eqToHom _ _ (dualHom_dualHom x).symm
      (isDiag_biadj_right_unit hz x) (isDiag_biadj_right_counit hz x)
      (isDiag_biadj_dual_left_counit hz x)
  · congr 1
    exact rightMate_id_eq_eqToHom _ _ (dualHom_dualHom x')
      (isDiag_biadj_left_unit hz _) (isDiag_biadj_dual_left_counit hz x')
      (isDiag_biadj_right_counit hz x')

/-- Rotating back: if `β` is the rotation of a cyclic `α`, the rotation of `β` has the layers
of `α`. -/
theorem IsDiag.rightMate_rotate_back {A A' : l ⟶ m} {B B' : m ⟶ l}
    (eB : B = Q.dualHom E.toColourDuality.pivotal A')
    (eB' : B' = Q.dualHom E.toColourDuality.pivotal A) {α : A ⟶ A'} {β : B ⟶ B'}
    (hα : Biadjunction.IsCyclic (BB A) (BB A') α)
    (hβ : β = eqToHom eB ≫ Biadjunction.rightMate (BB A) (BB A') α ≫ eqToHom eB'.symm)
    {ls : List (Layer (S.pivotal E.toColourDuality))} (hl : IsDiag Q α ls) :
    IsDiag Q (Biadjunction.rightMate (BB B) (BB B') β) ls := by
  subst eB eB' hβ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [rightMate_rightMate hz α hα]
  exact (hl.comp_eqToHom _).eqToHom_comp _

end Double

end Categorification.KL3.Diagram
