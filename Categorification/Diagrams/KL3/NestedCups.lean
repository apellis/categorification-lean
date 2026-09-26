/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Biadjunction.PivotalExtension

/-!
# Nested cups and caps as diagrams

For a presentation `Q` of a pivotal extension `S.pivotal E` (with the zigzag relations), the
library builds biadjunctions `x ⊣⊢ x*` for all words `x` (`Presentation.biadj`) from the cups
and caps of single colours, via Mathlib's composite adjunctions. This file shows that their units
and counits are classes of explicit diagrams of nested cups and caps, with explicitly given lists
of layers (`IsDiag`):

* `biadj_left_unit_isDiag`: the unit of `x ⊣ x*` has the layers `cupLayers`: the cup of the
  first colour, then (recursively) the nested cups of the rest of the word inserted between the
  first colour and its dual;
* `biadj_left_counit_isDiag`: the counit of `x ⊣ x*` has the layers `capLayers`;
* `biadj_right_unit_isDiag`, `biadj_right_counit_isDiag`: the same for `x* ⊣ x`.

This is generic (it does not depend on KL III); it fills, for pivotal extensions, the gap
"no explicit nested cup/cap diagram for multi-letter words" of the diagrammatics library.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory Bicategory StringDiagrams Presentation Biadjunction

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R]

section IsDiag

variable (P : Presentation.{w, v} S R) [S.IsEven] {l m n : P.Bicat}

/-- The 2-morphism `θ` of `P.Bicat` is the class of a diagram with the layers `ls`. -/
def IsDiag {x y : l ⟶ m} (θ : x ⟶ y) (ls : List (Layer S)) : Prop :=
  ∃ D : x.obj ⟶ y.obj, θ = P.diag D ∧ Diagram.layers D = ls

variable {P}

theorem IsDiag.congr {x y : l ⟶ m} {θ : x ⟶ y} {ls ls' : List (Layer S)} (h : IsDiag P θ ls)
    (e : ls = ls') : IsDiag P θ ls' := e ▸ h

theorem IsDiag.comp {x y z : l ⟶ m} {θ : x ⟶ y} {θ' : y ⟶ z} {ls ls' : List (Layer S)}
    (h : IsDiag P θ ls) (h' : IsDiag P θ' ls') : IsDiag P (θ ≫ θ') (ls ++ ls') := by
  obtain ⟨D, rfl, rfl⟩ := h
  obtain ⟨D', rfl, rfl⟩ := h'
  exact ⟨D ≫ D', (P.diag_comp D D').symm, rfl⟩

theorem isDiag_id (x : l ⟶ m) : IsDiag P (𝟙 x) [] := ⟨𝟙 x.obj, (P.diag_id _).symm, rfl⟩

theorem isDiag_eqToHom {x y : l ⟶ m} (h : x = y) : IsDiag P (eqToHom h) [] := by
  subst h; exact isDiag_id x

theorem IsDiag.whiskerLeft (f : l ⟶ m) {x y : m ⟶ n} {θ : x ⟶ y} {ls : List (Layer S)}
    (h : IsDiag P θ ls) : IsDiag P (f ◁ θ) (ls.map (·.wl f.obj)) := by
  obtain ⟨D, rfl, rfl⟩ := h
  exact ⟨Diagram.lwhisker f.obj D (Bicat.Hom.composable f x),
    P.wL_diag_of_composable _ _ (Bicat.Hom.composable f x), rfl⟩

theorem IsDiag.whiskerRight {x y : l ⟶ m} (g : m ⟶ n) {θ : x ⟶ y} {ls : List (Layer S)}
    (h : IsDiag P θ ls) : IsDiag P (θ ▷ g) (ls.map (·.wr g.obj.word)) := by
  obtain ⟨D, rfl, rfl⟩ := h
  exact ⟨Diagram.rwhisker D g.obj (Bicat.Hom.composable x g),
    P.wRAt_diag D _ (Bicat.Hom.composable x g) _ _, rfl⟩

theorem isDiag_associator_hom {k : P.Bicat} (f : l ⟶ m) (g : m ⟶ n) (h : n ⟶ k) :
    IsDiag P (α_ f g h).hom [] := by
  rw [Strict.associator_eqToIso, eqToIso.hom]; exact isDiag_eqToHom _

theorem isDiag_associator_inv {k : P.Bicat} (f : l ⟶ m) (g : m ⟶ n) (h : n ⟶ k) :
    IsDiag P (α_ f g h).inv [] := by
  rw [Strict.associator_eqToIso, eqToIso.inv]; exact isDiag_eqToHom _

theorem isDiag_leftUnitor_hom (f : l ⟶ m) : IsDiag P (λ_ f).hom [] := by
  rw [Strict.leftUnitor_eqToIso, eqToIso.hom]; exact isDiag_eqToHom _

theorem isDiag_leftUnitor_inv (f : l ⟶ m) : IsDiag P (λ_ f).inv [] := by
  rw [Strict.leftUnitor_eqToIso, eqToIso.inv]; exact isDiag_eqToHom _

theorem isDiag_rightUnitor_hom (f : l ⟶ m) : IsDiag P (ρ_ f).hom [] := by
  rw [Strict.rightUnitor_eqToIso, eqToIso.hom]; exact isDiag_eqToHom _

theorem isDiag_rightUnitor_inv (f : l ⟶ m) : IsDiag P (ρ_ f).inv [] := by
  rw [Strict.rightUnitor_eqToIso, eqToIso.inv]; exact isDiag_eqToHom _

theorem isDiag_comp_triv {x y z : l ⟶ m} {θ : x ⟶ y} {θ' : y ⟶ z}
    (h : IsDiag P θ []) (h' : IsDiag P θ' []) : IsDiag P (θ ≫ θ') [] :=
  (h.comp h').congr rfl

theorem isDiag_whiskerLeft_triv (f : l ⟶ m) {x y : m ⟶ n} {θ : x ⟶ y}
    (h : IsDiag P θ []) : IsDiag P (f ◁ θ) [] :=
  (h.whiskerLeft f).congr rfl

theorem isDiag_whiskerRight_triv {x y : l ⟶ m} (g : m ⟶ n) {θ : x ⟶ y}
    (h : IsDiag P θ []) : IsDiag P (θ ▷ g) [] :=
  (h.whiskerRight g).congr rfl

end IsDiag

/-- Proves `IsDiag P θ []` for composites and whiskerings of identities, associators and
unitors. -/
macro "isdiag_triv" : tactic => `(tactic| (
  simp only [BicategoricalCoherence.refl_iso, BicategoricalCoherence.whiskerLeft_iso,
    BicategoricalCoherence.whiskerRight_iso, BicategoricalCoherence.tensorRight_iso,
    BicategoricalCoherence.tensorRight'_iso, BicategoricalCoherence.left_iso,
    BicategoricalCoherence.left'_iso, BicategoricalCoherence.right_iso,
    BicategoricalCoherence.right'_iso, BicategoricalCoherence.assoc_iso,
    BicategoricalCoherence.assoc'_iso, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom]
  repeat (first
    | exact isDiag_id _
    | exact isDiag_eqToHom _
    | exact isDiag_associator_hom _ _ _
    | exact isDiag_associator_inv _ _ _
    | exact isDiag_leftUnitor_hom _
    | exact isDiag_leftUnitor_inv _
    | exact isDiag_rightUnitor_hom _
    | exact isDiag_rightUnitor_inv _
    | apply isDiag_comp_triv
    | apply isDiag_whiskerLeft_triv
    | apply isDiag_whiskerRight_triv)))

section Nested

variable {E : S.ColourInvolution} [S.IsEven]
  {Q : Presentation.{w, v} (S.pivotal E.toColourDuality) R}
  (hz : Q.PivotalZigzags E.toColourDuality)

/-- The layers of the nested cups `1 ⟶ w w*` of a word `w` read from the region `r`: the cup of
the first colour `c`, then the nested cups of the rest of `w` between `c` and `c*`. -/
def cupLayers : S.Region → List S.Colour → List (Layer (S.pivotal E.toColourDuality))
  | _, [] => []
  | r, c :: w => ⟨S.colourSrc c, [], .cup c, []⟩ ::
      (cupLayers (S.colourTgt c) w).map fun L => (L.wr [E.dual c]).wl ⟨r, [c]⟩

theorem biadjW_left_unit_isDiag : ∀ (w : List S.Colour) {l m : Q.Bicat} (x : l ⟶ m)
    (hx : x.obj.word = w),
    IsDiag Q (biadjW (pivotalBiadj E Q hz) w x hx).left.unit (cupLayers (E := E) l.region w)
  | [], l, m, x, hx => ⟨_, rfl, Diagram.layers_eqToHom _⟩
  | c :: w, l, m, x, hx => by
    rw [biadjW_cons_left_unit]
    have ih := biadjW_left_unit_isDiag w (Q.tailHom x c w hx) rfl
    have h₀ : IsDiag Q (pivotalBiadj E Q hz (Q.headHom x c w hx) c rfl).left.unit
        [⟨S.colourSrc c, [], .cup c, []⟩] := ⟨_, rfl, rfl⟩
    simp only [bicategoricalComp]
    refine IsDiag.congr (IsDiag.comp (IsDiag.comp h₀ (IsDiag.comp (ls := []) ?_
      (IsDiag.comp (IsDiag.whiskerLeft _ (IsDiag.whiskerRight _ ih)) (IsDiag.comp (ls := []) ?_
      (isDiag_id _))))) (isDiag_eqToHom _)) ?_
    · isdiag_triv
    · isdiag_triv
    · simp only [cupLayers, List.map_map, List.nil_append, List.append_nil, List.cons_append]
      rfl

/-- The layers of the nested caps `w* w ⟶ 1` of a word `w` whose dual starts in the region `r`:
the nested caps of the tail inside, after the cap of the first colour. -/
def capLayers (r : S.Region) : List S.Colour → List (Layer (S.pivotal E.toColourDuality))
  | [] => []
  | c :: w => ((⟨S.colourTgt c, [], .cap c, []⟩ : Layer (S.pivotal E.toColourDuality)).wr w).wl
      ⟨r, E.toColourDuality.pivotal.dualWord w⟩ :: capLayers r w

theorem biadjW_left_counit_isDiag : ∀ (w : List S.Colour) {l m : Q.Bicat} (x : l ⟶ m)
    (hx : x.obj.word = w),
    IsDiag Q (biadjW (pivotalBiadj E Q hz) w x hx).left.counit (capLayers (E := E) m.region w)
  | [], l, m, x, hx => ⟨_, rfl, Diagram.layers_eqToHom _⟩
  | c :: w, l, m, x, hx => by
    rw [biadjW_cons_left_counit]
    have ih := biadjW_left_counit_isDiag w (Q.tailHom x c w hx) rfl
    have h₀ : IsDiag Q (pivotalBiadj E Q hz (Q.headHom x c w hx) c rfl).left.counit
        [⟨S.colourTgt c, [], .cap c, []⟩] := ⟨_, rfl, rfl⟩
    simp only [bicategoricalComp]
    refine IsDiag.congr (IsDiag.comp (isDiag_eqToHom _) (IsDiag.comp (isDiag_id _)
      (IsDiag.comp (ls := []) ?_ (IsDiag.comp (IsDiag.whiskerLeft _ (IsDiag.whiskerRight _ h₀))
      (IsDiag.comp (ls := []) ?_ ih))))) ?_
    · isdiag_triv
    · isdiag_triv
    · simp only [capLayers, List.map_cons, List.map_nil, List.nil_append, List.cons_append]
      rfl

/-- The right unit of a transported biadjunction. -/
theorem biadjCongr_right_unit {B : Type*} [Bicategory B] {a b : B}
    {f f' : a ⟶ b} {g g' : b ⟶ a} (P : f ⊣⊢ g) (hf : f = f') (hg : g = g') :
    (P.congr hf hg).right.unit = P.right.unit ≫ eqToHom (by rw [hf, hg]) := by
  subst hf hg; simp

/-- The right counit of a transported biadjunction. -/
theorem biadjCongr_right_counit {B : Type*} [Bicategory B] {a b : B}
    {f f' : a ⟶ b} {g g' : b ⟶ a} (P : f ⊣⊢ g) (hf : f = f') (hg : g = g') :
    (P.congr hf hg).right.counit = eqToHom (by rw [hf, hg]) ≫ P.right.counit := by
  subst hf hg; simp

/-- The layers of the nested cups `1 ⟶ w* w` of a word `w`, starting in the region `r` where
`w*` starts: the nested cups of the tail first, then the cup `1 ⟶ c* c` of the first colour
inside. -/
def cupRLayers (r : S.Region) : List S.Colour → List (Layer (S.pivotal E.toColourDuality))
  | [] => []
  | c :: w => cupRLayers r w ++
      [((⟨S.colourSrc (E.dual c), [], .cup (E.dual c), []⟩ :
        Layer (S.pivotal E.toColourDuality)).wr w).wl
        (⟨r, E.toColourDuality.pivotal.dualWord w⟩ : Obj (S.pivotal E.toColourDuality))]

theorem biadjW_right_unit_isDiag : ∀ (w : List S.Colour) {l m : Q.Bicat} (x : l ⟶ m)
    (hx : x.obj.word = w),
    IsDiag Q (biadjW (pivotalBiadj E Q hz) w x hx).right.unit (cupRLayers (E := E) m.region w)
  | [], l, m, x, hx => ⟨_, rfl, Diagram.layers_eqToHom _⟩
  | c :: w, l, m, x, hx => by
    have ih := biadjW_right_unit_isDiag w (Q.tailHom x c w hx) rfl
    have h₀ : IsDiag Q (pivotalBiadj E Q hz (Q.headHom x c w hx) c rfl).right.unit
        [⟨S.colourSrc (E.dual c), [], .cup (E.dual c), []⟩] := ⟨_, rfl, rfl⟩
    simp only [biadjW, biadjCongr_right_unit, Biadjunction.comp_right,
      Bicategory.Adjunction.comp_unit, Bicategory.Adjunction.compUnit, bicategoricalComp]
    refine IsDiag.congr (IsDiag.comp (IsDiag.comp ih (IsDiag.comp (ls := []) ?_
      (IsDiag.comp (IsDiag.whiskerLeft _ (IsDiag.whiskerRight _ h₀)) (IsDiag.comp (ls := []) ?_
      (isDiag_id _))))) (isDiag_eqToHom _)) ?_
    · isdiag_triv
    · isdiag_triv
    · simp only [cupRLayers, List.map_cons, List.map_nil, List.nil_append, List.append_nil]
      rfl

/-- The layers of the nested caps `w w* ⟶ 1` of a word `w` read from the region `r`: the nested
caps of the tail between `c` and `c*` first, then the cap `c c* ⟶ 1` of the first colour. -/
def capRLayers : S.Region → List S.Colour → List (Layer (S.pivotal E.toColourDuality))
  | _, [] => []
  | r, c :: w => (capRLayers (S.colourTgt c) w).map (fun L =>
      (L.wr [E.dual c]).wl (⟨r, [c]⟩ : Obj (S.pivotal E.toColourDuality))) ++
      [(⟨S.colourTgt (E.dual c), [], .cap (E.dual c), []⟩ : Layer (S.pivotal E.toColourDuality))]

theorem biadjW_right_counit_isDiag : ∀ (w : List S.Colour) {l m : Q.Bicat} (x : l ⟶ m)
    (hx : x.obj.word = w),
    IsDiag Q (biadjW (pivotalBiadj E Q hz) w x hx).right.counit (capRLayers (E := E) l.region w)
  | [], l, m, x, hx => ⟨_, rfl, Diagram.layers_eqToHom _⟩
  | c :: w, l, m, x, hx => by
    have ih := biadjW_right_counit_isDiag w (Q.tailHom x c w hx) rfl
    have h₀ : IsDiag Q (pivotalBiadj E Q hz (Q.headHom x c w hx) c rfl).right.counit
        [⟨S.colourTgt (E.dual c), [], .cap (E.dual c), []⟩] := ⟨_, rfl, rfl⟩
    simp only [biadjW, biadjCongr_right_counit, Biadjunction.comp_right,
      Bicategory.Adjunction.comp_counit, Bicategory.Adjunction.compCounit, bicategoricalComp]
    refine IsDiag.congr (IsDiag.comp (isDiag_eqToHom _) (IsDiag.comp (isDiag_id _)
      (IsDiag.comp (ls := []) ?_ (IsDiag.comp (IsDiag.whiskerLeft _ (IsDiag.whiskerRight _ ih))
      (IsDiag.comp (ls := []) ?_ h₀))))) ?_
    · isdiag_triv
    · isdiag_triv
    · simp only [capRLayers, List.map_cons, List.map_nil, List.nil_append, List.append_nil,
        List.map_map]
      rfl

end Nested

end Categorification.KL3.Diagram
