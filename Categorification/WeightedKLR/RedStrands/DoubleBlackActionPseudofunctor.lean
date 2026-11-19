/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionWhisker
import Categorification.Diagrams.RevBicat
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import Mathlib.CategoryTheory.Category.Cat

/-!
# The black action as a strict pseudofunctor

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28. The Khovanov–Lauda 2-category acts on the
violating quotients: a word `s` acts by right whiskering with its mirror word, and a diagram
acts by the mirror diagram. Since reflection reverses the order of 1-morphisms, the action is
a strict pseudofunctor from the reverse of the Khovanov–Lauda bicategory to `Cat`.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

theorem inducedCategory_eqToHom_hom {𝒞 : Type*} {𝒟 : Type*} [Category 𝒟] {F : 𝒞 → 𝒟}
    {x y : InducedCategory 𝒟 F} (h : x = y) :
    (eqToHom h).hom = eqToHom (congrArg F h) := by
  subst h; rfl

theorem inducedCategory_eq_eqToHom {𝒞 : Type*} {𝒟 : Type*} [Category 𝒟] {F : 𝒞 → 𝒟}
    {x y : InducedCategory 𝒟 F} (f : x ⟶ y) (h : x = y)
    (hf : f.hom = eqToHom (congrArg F h)) : f = eqToHom h := by
  subst h; ext; exact hf

/-- A morphism conjugated twice by transports is conjugated once. -/
theorem eqToHom_conj_conj {D : Type*} [Category D] {a a₁ b c c₁ d : D} (g : b ⟶ c)
    (h₁ : a = a₁) (h₂ : a₁ = b) (h₃ : c = c₁) (h₄ : c₁ = d) (h₅ : a = b) (h₆ : c = d) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ g ≫ eqToHom h₃) ≫ eqToHom h₄ = eqToHom h₅ ≫ g ≫ eqToHom h₆ := by
  subst h₁ h₂ h₃ h₄; simp

section Append

variable {μ ν₁ ν₂ : X} {v₁ v₂ : List (DoubleStrand I ℓ)} (hv₁ : RedFree v₁)
  (hv₂ : RedFree v₂) (h₁ : endWeight RD (fun r => (Λ r).val) μ v₁ = ν₁)
  (h₂ : endWeight RD (fun r => (Λ r).val) ν₁ v₂ = ν₂)

/-- Right whiskering by a concatenation is the composite of the two whiskerings, as an
equality of functors. -/
theorem whiskerRight_append_eq :
    whiskerRight P (v₁ ++ v₂) (redFree_append hv₁ hv₂) (endWeight_append_of_eq h₁ h₂) =
      whiskerRight P v₁ hv₁ h₁ ⋙ whiskerRight P v₂ hv₂ h₂ :=
  CategoryTheory.Functor.ext_of_iso (whiskerRightAppend P hv₁ hv₂ h₁ h₂)
    (fun x => appendRight_append hv₁ hv₂ h₁ h₂ x) fun x => by
      ext
      rw [whiskerRightAppend_hom_app_hom]
      exact (inducedCategory_eqToHom_hom _).symm

/-- Right whiskering by a concatenation on the violating quotients, as an equality of
functors. -/
theorem violatingWhiskerRight_append_eq :
    violatingWhiskerRight P (v₁ ++ v₂) (redFree_append hv₁ hv₂)
        (endWeight_append_of_eq h₁ h₂) =
      violatingWhiskerRight P v₁ hv₁ h₁ ⋙ violatingWhiskerRight P v₂ hv₂ h₂ := by
  apply CategoryTheory.Quotient.lift_unique'
  show whiskerRight P (v₁ ++ v₂) (redFree_append hv₁ hv₂) (endWeight_append_of_eq h₁ h₂) ⋙
      violatingFunctor P ν₂ =
    (whiskerRight P v₁ hv₁ h₁ ⋙ whiskerRight P v₂ hv₂ h₂) ⋙ violatingFunctor P ν₂
  rw [whiskerRight_append_eq]

end Append

section Nil

variable {μ : X} (hv : RedFree ([] : List (DoubleStrand I ℓ)))
  (h : endWeight RD (fun r => (Λ r).val) μ [] = μ)

theorem appendRight_nil (x : DoubleStendhalTriple RD Λ 0 μ) : appendRight [] hv h x = x := by
  apply Subtype.ext; apply DoubleBoundary.ext
  exact List.append_nil _

/-- Right whiskering by the empty word is the identity. -/
theorem whiskerRight_nil_eq : whiskerRight P [] hv h = 𝟭 (BoundaryCategory P μ) := by
  refine CategoryTheory.Functor.ext (h_obj := fun b => appendRight_nil hv h b)
    (h_map := fun x y f => ?_)
  ext
  have hx : (obj RD (fun r => (Λ r).val) 0 x.val.word).endR = μ :=
    (colours_endR ..).trans (endWeight_word x)
  simp only [whiskerRight, whiskerRightHom, InducedCategory.homMk_hom, InducedCategory.comp_hom,
    inducedCategory_eqToHom_hom, Functor.id_map]
  erw [P.wRAt_nil f.hom (colours_ok ..) hx rfl rfl, inducedCategory_eqToHom_hom]
  exact eqToHom_conj_conj (D := P.Presented) _ _ _ _ _ _ _

/-- Right whiskering by the empty word on the violating quotient is the identity. -/
theorem violatingWhiskerRight_nil_eq :
    violatingWhiskerRight P [] hv h = 𝟭 (ViolatingCategory P μ) := by
  apply CategoryTheory.Quotient.lift_unique'
  show whiskerRight P [] hv h ⋙ violatingFunctor P μ = violatingFunctor P μ ⋙ 𝟭 _
  rw [whiskerRight_nil_eq]; rfl

end Nil

section Words

/-- The action of a word depends only on the word. -/
theorem blackAct_congr {μ ν : X} {s s' : List (Letter I)} (h : s = s') (hs : wt RD μ s = ν)
    (hs' : wt RD μ s' = ν) : blackAct P s hs = blackAct P s' hs' := by
  subst h; rfl

/-- The empty word acts by the identity functor. -/
theorem blackAct_nil {μ : X} (h : wt RD μ [] = μ) :
    blackAct P [] h = 𝟭 (ViolatingCategory P μ) :=
  violatingWhiskerRight_nil_eq P _ _

variable {μ ν₁ ν₂ : X} (s t : List (Letter I)) (ht : wt RD μ t = ν₁)
  (hs : wt RD ν₁ s = ν₂) (hst : wt RD μ (s ++ t) = ν₂)

/-- The action of `s ++ t` is the action of `t` followed by the action of `s`, as an equality
of functors. -/
theorem blackAct_append_eq :
    blackAct P (s ++ t) hst = blackAct P t ht ⋙ blackAct P s hs :=
  (violatingWhiskerRight_congr P (blackWord_append' s t) _
      (redFree_append (blackWord_redFree t) (blackWord_redFree s)) _
      (endWeight_append_of_eq ((endWeight_blackWord RD _ μ t).trans ht)
        ((endWeight_blackWord RD _ ν₁ s).trans hs))).trans
    (violatingWhiskerRight_append_eq P _ _ _ _)

theorem blackActAppend_hom_eq :
    (blackActAppend P s t ht hs hst).hom = eqToHom (blackAct_append_eq P s t ht hs hst) := by
  ext ⟨x⟩
  rw [eqToHom_app]
  simp only [blackActAppend, violatingWhiskerRightAppend, Quotient.natIsoLift]
  erw [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  erw [Quotient.natTransLift_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  have hx := whiskerRightAppend_hom_app_hom P (blackWord_redFree t) (blackWord_redFree s)
    ((endWeight_blackWord RD _ μ t).trans ht) ((endWeight_blackWord RD _ ν₁ s).trans hs) x
  erw [inducedCategory_eq_eqToHom _ (appendRight_append _ _ _ _ x) hx, eqToHom_map,
    eqToHom_trans]

theorem blackActAppend_inv_eq :
    (blackActAppend P s t ht hs hst).inv =
      eqToHom (blackAct_append_eq P s t ht hs hst).symm := by
  have : blackActAppend P s t ht hs hst = eqToIso (blackAct_append_eq P s t ht hs hst) :=
    Iso.ext (blackActAppend_hom_eq P s t ht hs hst)
  rw [this]; rfl

end Words

end Categorification.Stendhal.DoubleDiagram
