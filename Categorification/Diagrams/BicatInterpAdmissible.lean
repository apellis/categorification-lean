/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.BicatInterp
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Interpreting admissible words without zero objects

The fixed-boundary interpretation is defined directly on admissible words. Unlike `interp`,
this construction never assigns an image to an inadmissible word, so it requires no zero
objects in the target Hom categories. Its values use the same `Model.word` and `coreC` as
the total interpretation. When zero objects exist, `admissibleInterp_map` compares the two.

This file constructs the functor on free diagrams. Descent through a presentation and
pseudofunctorial assembly require further soundness and coherence statements.
-/

noncomputable section

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams

universe w₁ w₂ u₀ u₁ u₂ v₂

variable {S : Signature.{u₀, u₁, u₂}} {C : Type w₁} [Bicategory.{w₂, v₂} C]
  {M : Model S C}

/-- The full subcategory of words with the specified outer regions. -/
abbrev Admissible (s t : S.Region) :=
  ObjectProperty.FullSubcategory (Cond s t : ObjectProperty (Obj S))

/-- Transport of word images along equality of admissible objects. -/
theorem admissibleWord_eq {s t : S.Region} {a b : Obj S} (h : a = b)
    (ha : Cond s t a) (hb : Cond s t b) :
    M.word s a.word t ha.1 ha.2.1 = M.word s b.word t hb.1 hb.2.1 := by
  cases h
  rfl

/-- The image of a chain between admissible words, with no fallback object. -/
def admissibleChain (G : GenImg M) {s t : S.Region} :
    (a : Obj S) → (ls : List (Layer S)) → (b : Obj S) → Chain a ls b →
    (ha : Cond s t a) → (hb : Cond s t b) →
    (M.word s a.word t ha.1 ha.2.1 ⟶ M.word s b.word t hb.1 hb.2.1)
  | _, [], _, h, ha, hb => eqToHom (admissibleWord_eq h ha hb)
  | _, L :: ls, b, h, ha, hb =>
    eqToHom (admissibleWord_eq h.2.1.symm ha (h.2.1 ▸ ha)) ≫
      coreC G h.1 (h.2.1 ▸ ha) ≫
        admissibleChain G L.cod ls b h.2.2 ((h.2.1 ▸ ha).cod h.1) hb

/-- Composition of admissible chains is concatenation. -/
theorem admissibleChain_append (G : GenImg M) {s t : S.Region}
    {a b c : Obj S} {ls ms : List (Layer S)} (h₁ : Chain a ls b) (h₂ : Chain b ms c)
    (ha : Cond s t a) (hb : Cond s t b) (hc : Cond s t c) :
    admissibleChain G a (ls ++ ms) c (h₁.append h₂) ha hc =
      admissibleChain G a ls b h₁ ha hb ≫ admissibleChain G b ms c h₂ hb hc := by
  induction ls generalizing a with
  | nil => cases h₁; simp [admissibleChain]
  | cons L ls ih =>
    rcases h₁ with ⟨hv, rfl, h₁⟩
    simpa only [List.cons_append, admissibleChain, eqToHom_refl, Category.id_comp,
      Category.assoc] using congrArg (coreC G hv ha ≫ ·) (ih h₁ (ha.cod hv))

/-- The free-diagram interpretation on admissible words in the original target bicategory. -/
def admissibleInterp (G : GenImg M) (s t : S.Region) :
    Admissible s t ⥤ (M.obj t ⟶ M.obj s) where
  obj a := M.word s a.obj.word t a.property.1 a.property.2.1
  map {a b} f := admissibleChain G a.obj (Diagram.layers f.hom) b.obj
    (Diagram.chain f.hom) a.property b.property
  map_id a := by
    change eqToHom (admissibleWord_eq (M := M) rfl a.property a.property) = 𝟙 _
    rfl
  map_comp {a b c} f g := admissibleChain_append G (Diagram.chain f.hom)
    (Diagram.chain g.hom) a.property b.property c.property

/-- A single layer has its original `coreC` image. -/
theorem admissibleInterp_layer (G : GenImg M) {s t : S.Region} (L : Layer S)
    (hv : L.Valid) (ha : Cond s t L.dom) :
    (admissibleInterp G s t).map (ObjectProperty.homMk
      (X := ⟨L.dom, ha⟩) (Y := ⟨L.cod, ha.cod hv⟩) (Diagram.ofLayer L hv)) =
      coreC G hv ha := by
  change (𝟙 _ ≫ coreC G hv ha ≫ 𝟙 _) = _
  simp only [Category.id_comp, Category.comp_id]

section Linear

variable {k : Type*} [CommRing k] [∀ a b : C, Preadditive (a ⟶ b)]
  [∀ a b : C, Linear k (a ⟶ b)]

/-- The linear image of a diagram with admissible endpoints. -/
def admissibleMap (G : GenImg M) {s t : S.Region} {a b : Obj S}
    (ha : Cond s t a) (hb : Cond s t b) :
    LinDiagram k a b →ₗ[k] (M.word s a.word t ha.1 ha.2.1 ⟶
      M.word s b.word t hb.1 hb.2.1) :=
  Finsupp.linearCombination k fun f : a ⟶ b =>
    (admissibleInterp G s t).map (ObjectProperty.homMk (X := ⟨a, ha⟩) (Y := ⟨b, hb⟩) f)

@[simp]
theorem admissibleMap_of (G : GenImg M) {s t : S.Region} {a b : Obj S}
    (ha : Cond s t a) (hb : Cond s t b) (f : a ⟶ b) :
    admissibleMap (k := k) G ha hb (LinDiagram.of f) =
      (admissibleInterp G s t).map (ObjectProperty.homMk (X := ⟨a, ha⟩) (Y := ⟨b, hb⟩) f) := by
  change (Finsupp.linearCombination k fun f : a ⟶ b =>
    (admissibleInterp G s t).map (ObjectProperty.homMk (X := ⟨a, ha⟩) (Y := ⟨b, hb⟩) f))
      (Finsupp.single f 1) = _
  rw [Finsupp.linearCombination_single, one_smul]

/-- Linear interpretation preserves vertical composition on the admissible component. -/
theorem admissibleMap_comp (G : GenImg M) {s t : S.Region} {a b c : Obj S}
    (ha : Cond s t a) (hb : Cond s t b) (hc : Cond s t c)
    (f : LinDiagram k a b) (g : LinDiagram k b c) :
    admissibleMap G ha hc (f ≫ g) = admissibleMap G ha hb f ≫ admissibleMap G hb hc g := by
  induction f using (Finsupp.induction_linear (ι := a ⟶ b) (M := k)) with
  | zero =>
    erw [Limits.zero_comp, map_zero, map_zero, Limits.zero_comp]
  | add f₁ f₂ h₁ h₂ =>
    erw [Preadditive.add_comp, map_add, h₁, h₂, map_add, Preadditive.add_comp]
  | single f r =>
    induction g using (Finsupp.induction_linear (ι := b ⟶ c) (M := k)) with
    | zero =>
      erw [Limits.comp_zero, map_zero, map_zero, Limits.comp_zero]
    | add g₁ g₂ h₁ h₂ =>
      erw [Preadditive.comp_add, map_add, h₁, h₂, map_add, Preadditive.comp_add]
    | single g q =>
      erw [Free.single_comp_single]
      dsimp only [admissibleMap]
      erw [Finsupp.linearCombination_single, Finsupp.linearCombination_single,
        Finsupp.linearCombination_single]
      erw [Linear.smul_comp, Linear.comp_smul, smul_smul]
      congr 1
      exact (admissibleInterp G s t).map_comp
        (ObjectProperty.homMk (X := ⟨a, ha⟩) (Y := ⟨b, hb⟩) f)
        (ObjectProperty.homMk (X := ⟨b, hb⟩) (Y := ⟨c, hc⟩) g)

/-- The admissible component of the free linear category. -/
abbrev LinearAdmissible (k : Type*) [CommRing k] (s t : S.Region) :=
  ObjectProperty.FullSubcategory (fun a : Free k (Obj S) => Cond s t (show Obj S from a))

/-- Linear combinations of admissible diagrams act in the original Hom category. -/
def admissibleLinearInterp (G : GenImg M) (s t : S.Region) :
    LinearAdmissible k s t ⥤ (M.obj t ⟶ M.obj s) where
  obj a := M.word s (Obj.word a.obj) t a.property.1 a.property.2.1
  map {a b} f := admissibleMap G a.property b.property f.hom
  map_id a := by
    change admissibleMap G a.property a.property (LinDiagram.of (𝟙 (show Obj S from a.obj))) = _
    rw [admissibleMap_of]
    exact (admissibleInterp G s t).map_id ⟨a.obj, a.property⟩
  map_comp {a b c} f g := admissibleMap_comp G a.property b.property c.property f.hom g.hom

instance admissibleLinearInterp_additive (G : GenImg M) (s t : S.Region) :
    (admissibleLinearInterp (k := k) G s t).Additive where
  map_add := by
    intro a b f g
    exact (admissibleMap G a.property b.property).map_add f.hom g.hom

instance admissibleLinearInterp_linear (G : GenImg M) (s t : S.Region) :
    (admissibleLinearInterp (k := k) G s t).Linear k where
  map_smul := by
    intro a b f r
    exact (admissibleMap G a.property b.property).map_smul r f.hom

end Linear

section Comparison

variable [∀ a b : C, Limits.HasZeroObject (a ⟶ b)] [∀ a b : C, Preadditive (a ⟶ b)]

/-- The restricted chain map agrees with the total interpretation on its admissible component. -/
theorem admissibleChain_eq (G : GenImg M) {s t : S.Region} (a : Obj S)
    (ls : List (Layer S)) (b : Obj S) (h : Chain a ls b)
    (ha : Cond s t a) (hb : Cond s t b) :
    (interp G s t).mapChain a ls b h =
      eqToHom (objI_pos s t ha) ≫ admissibleChain G a ls b h ha hb ≫
        eqToHom (objI_pos s t hb).symm := by
  induction ls generalizing a with
  | nil => cases h; simp [Interpretation.mapChain, admissibleChain]
  | cons L ls ih =>
    rcases h with ⟨hv, rfl, hc⟩
    simp only [Interpretation.mapChain, eqToHom_refl, Category.id_comp,
      layerI_pos G s t hv ha, admissibleChain, ih _ hc (ha.cod hv), Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl]

/-- Comparison with the existing total interpretation, when the latter is available. -/
theorem admissibleInterp_map (G : GenImg M) {s t : S.Region}
    {a b : Admissible s t} (f : a ⟶ b) :
    (interp G s t).functor.map f.hom =
      eqToHom (objI_pos s t a.property) ≫ (admissibleInterp G s t).map f ≫
        eqToHom (objI_pos s t b.property).symm :=
  admissibleChain_eq G _ _ _ (Diagram.chain f.hom) a.property b.property

end Comparison
end Categorification.Diagrams.BicatInterp
