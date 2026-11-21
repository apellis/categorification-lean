/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Biadjunction.Words
import Categorification.Diagrams.RevBicat
import Categorification.TwoRep.SubPseudofunctor

/-!
# Closure of object properties under the action of a presented 2-category

For a pseudofunctor `F : RevBicat P.Bicat ⥤ LinearCat k` out of a presented 2-category and
properties `Pr a` of the objects of `F(a)` closed under isomorphisms, if every `F(x)` with `x` a
one-letter word preserves the properties, then so does `F(x)` for every 1-morphism `x`: every
1-morphism is a composite of one-letter words, and `F` preserves composites up to isomorphism.
This is the closure hypothesis of `LinearCat.fullSub`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Bicategory StringDiagrams

namespace Categorification.TwoRep.LinearCat

universe w v u w₀ v₀ u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} [S.IsEven] {R : Type w₀} [CommRing R]
  {P : Presentation.{w₀, v₀} S R} {k : Type w} [CommRing k]
  (F : Pseudofunctor (RevBicat P.Bicat) (LinearCat.{w, v, u} k))
  (Pr : ∀ a, ObjectProperty (F.obj a)) [∀ a, (Pr a).IsClosedUnderIsomorphisms]

/-- The 1-morphism `x` of `RevBicat P.Bicat` as a 1-morphism of `P.Bicat`. -/
abbrev revHom {a b : RevBicat P.Bicat} (x : a ⟶ b) : b.as ⟶ a.as := x

theorem map_closed_of_letters
    (h : ∀ {a b : RevBicat P.Bicat} (x : a ⟶ b) (c : S.Colour), (revHom x).obj.word = [c] →
      ∀ X, Pr a X → Pr b ((F.map x).obj.obj X)) :
    ∀ (w : List S.Colour) {a b : RevBicat P.Bicat} (x : a ⟶ b), (revHom x).obj.word = w →
      ∀ X, Pr a X → Pr b ((F.map x).obj.obj X) := by
  intro w
  induction w with
  | nil =>
    intro a b x hx X hX
    have hab : a = b := by
      obtain ⟨⟨ra⟩⟩ := a
      obtain ⟨⟨rb⟩⟩ := b
      have h1 := x.start_eq
      have h2 := x.endR_eq
      change S.endR x.obj.start x.obj.word = ra at h2
      rw [hx, h1] at h2
      simp only [Signature.endR_nil] at h2
      rw [h2]
    subst hab
    have hx1 : x = 𝟙 a := Presentation.Bicat.Hom.ext (Obj.ext x.start_eq hx)
    subst hx1
    exact (Pr a).prop_of_iso (isoApp (F.mapId a) X).symm hX
  | cons c w ih =>
    intro a b x hx X hX
    let y : b.as ⟶ a.as := x
    let t : a ⟶ ⟨⟨S.colourTgt c⟩⟩ := P.tailHom y c w hx
    let hd : (⟨⟨S.colourTgt c⟩⟩ : RevBicat P.Bicat) ⟶ b := P.headHom y c w hx
    have hxy : x = t ≫ hd := (P.headHom_comp_tailHom y c w hx).symm
    rw [hxy]
    exact (Pr b).prop_of_iso (isoApp (F.mapComp t hd) X).symm
      (h hd c rfl _ (ih t rfl X hX))

end Categorification.TwoRep.LinearCat
