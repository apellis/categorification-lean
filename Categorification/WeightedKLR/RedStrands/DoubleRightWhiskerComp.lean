/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleRightWhisker

/-!
# Composition of right whiskerings

Webster, arXiv:1309.3796v3, §4.5, before Theorem 4.28. Appending `v₁ ++ v₂` on the right of a
double Stendhal boundary is appending `v₁` and then `v₂`. This file identifies the right
whiskering by a concatenation with the composite of the two right whiskerings, on the
boundary categories and on the violating quotients. This is the compatibility of the action
of `𝒰` with composition of 1-morphisms.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

variable {I : Type*} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type*}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

omit [AddCommGroup Y] in
theorem redFree_append {v₁ v₂ : List (DoubleStrand I ℓ)} (h₁ : RedFree v₁)
    (h₂ : RedFree v₂) : RedFree (v₁ ++ v₂) := by
  simp only [RedFree, List.filterMap_append] at h₁ h₂ ⊢
  rw [h₁, h₂]; rfl

theorem endWeight_append_of_eq {μ ν₁ ν₂ : X} {v₁ v₂ : List (DoubleStrand I ℓ)}
    (h₁ : endWeight RD (fun r => (Λ r).val) μ v₁ = ν₁)
    (h₂ : endWeight RD (fun r => (Λ r).val) ν₁ v₂ = ν₂) :
    endWeight RD (fun r => (Λ r).val) μ (v₁ ++ v₂) = ν₂ := by
  subst h₁ h₂
  simp [endWeight, List.map_append, List.sum_append, add_assoc]

/-- Right whiskering by a diagram along an equality of the whiskering objects. -/
theorem wRAt_congr_obj {a a' b b' : Obj (signature RD (fun r => (Λ r).val))} {r : X}
    (f : P.obj a ⟶ P.obj a') (h : b = b') (ha : a.start = r) (ha' : a'.start = r) :
    P.wRAt r f b ha ha' =
      eqToHom (by rw [h]) ≫ P.wRAt r f b' ha ha' ≫ eqToHom (by rw [h]) := by
  subst h; simp

theorem composable_append {μ ν₁ : X} (v₁ v₂ : List (DoubleStrand I ℓ))
    (h₁ : endWeight RD (fun r => (Λ r).val) μ v₁ = ν₁) :
    (obj RD (fun r => (Λ r).val) μ v₁).Composable (obj RD (fun r => (Λ r).val) ν₁ v₂) :=
  ⟨colours_ok .., (colours_endR ..).trans h₁, colours_ok ..⟩

theorem appendRight_append {μ ν₁ ν₂ : X} {v₁ v₂ : List (DoubleStrand I ℓ)}
    (hv₁ : RedFree v₁) (hv₂ : RedFree v₂)
    (h₁ : endWeight RD (fun r => (Λ r).val) μ v₁ = ν₁)
    (h₂ : endWeight RD (fun r => (Λ r).val) ν₁ v₂ = ν₂) (x : DoubleStendhalTriple RD Λ 0 μ) :
    appendRight (v₁ ++ v₂) (redFree_append hv₁ hv₂) (endWeight_append_of_eq h₁ h₂) x =
      appendRight v₂ hv₂ h₂ (appendRight v₁ hv₁ h₁ x) := by
  apply Subtype.ext; apply DoubleBoundary.ext
  exact (List.append_assoc _ _ _).symm

/-- Two composites of a morphism with transports agree. -/
theorem eqToHom_sandwich {D : Type*} [Category D] {a b₁ b₂ b c c₁ c₂ c₃ c₄ d₁ d₂ e₁ : D}
    (g : b ⟶ c) (h₁ : a = b₁) (h₂ : b₁ = b₂) (h₃ : b₂ = b) (h₄ : c = c₁) (h₅ : c₁ = c₂)
    (h₆ : c₂ = c₃) (h₀ : c₃ = c₄) (h₇ : a = d₁) (h₈ : d₁ = d₂) (h₉ : d₂ = b)
    (h₁₀ : c = e₁) (h₁₁ : e₁ = c₄) :
    (eqToHom h₁ ≫ (eqToHom h₂ ≫ (eqToHom h₃ ≫ g ≫ eqToHom h₄) ≫ eqToHom h₅) ≫
        eqToHom h₆) ≫ eqToHom h₀ =
      eqToHom h₇ ≫ eqToHom h₈ ≫ (eqToHom h₉ ≫ g ≫ eqToHom h₁₀) ≫ eqToHom h₁₁ := by
  subst h₁ h₂ h₃ h₄ h₅ h₆ h₀ h₇ h₈ h₁₀; simp

section Comp

variable {μ ν₁ ν₂ : X} {v₁ v₂ : List (DoubleStrand I ℓ)} (hv₁ : RedFree v₁)
  (hv₂ : RedFree v₂) (h₁ : endWeight RD (fun r => (Λ r).val) μ v₁ = ν₁)
  (h₂ : endWeight RD (fun r => (Λ r).val) ν₁ v₂ = ν₂)

/-- The component of the comparison at a boundary: the identity of the common boundary. -/
def whiskerRightAppendApp (x : BoundaryCategory P μ) :
    (whiskerRight P (v₁ ++ v₂) (redFree_append hv₁ hv₂) (endWeight_append_of_eq h₁ h₂)).obj x ≅
      (whiskerRight P v₁ hv₁ h₁ ⋙ whiskerRight P v₂ hv₂ h₂).obj x :=
  InducedCategory.isoMk (eqToIso (congrArg (tripleObj P) (appendRight_append hv₁ hv₂ h₁ h₂ x)))

/-- Whiskering on the right by a concatenation is the composite of the two whiskerings
(Webster, arXiv:1309.3796v3, §4.5, before Theorem 4.28). -/
def whiskerRightAppend :
    whiskerRight P (v₁ ++ v₂) (redFree_append hv₁ hv₂) (endWeight_append_of_eq h₁ h₂) ≅
      whiskerRight P v₁ hv₁ h₁ ⋙ whiskerRight P v₂ hv₂ h₂ :=
  NatIso.ofComponents (whiskerRightAppendApp P hv₁ hv₂ h₁ h₂) fun {x y} f => by
    ext
    have hbc := composable_append (Λ := Λ) v₁ v₂ h₁
    have hT := P.wRAt_tensor (r := (0 : X)) (composable P x v₁) hbc f.hom rfl rfl
    have hC := wRAt_congr_obj P f.hom
      (obj_tensor_obj_of_eq (Λ := Λ) h₁ v₂).symm (r := (0 : X)) rfl rfl
    simp only [InducedCategory.comp_hom, whiskerRight, whiskerRightHom, Functor.comp_map,
      InducedCategory.homMk_hom, whiskerRightAppendApp, InducedCategory.isoMk_hom]
    erw [P.wRAt_comp (r := (0 : X)) rfl rfl rfl, P.wRAt_comp (r := (0 : X)) rfl rfl rfl,
      P.wRAt_eqToHom _ _ (ok_endR P (appendRight v₁ hv₁ h₁ x) v₂),
      P.wRAt_eqToHom _ _ ((composable P y v₁).tensor_left hbc).ok_endR, hC, hT, eqToIso.hom, eqToIso.hom]
    apply eqToHom_sandwich (D := P.Presented)

@[simp] theorem whiskerRightAppend_hom_app_hom (x : BoundaryCategory P μ) :
    ((whiskerRightAppend P hv₁ hv₂ h₁ h₂).hom.app x).hom =
      eqToHom (congrArg (tripleObj P) (appendRight_append hv₁ hv₂ h₁ h₂ x)) :=
  rfl

/-- Whiskering on the right by a concatenation is the composite of the two whiskerings, on
the violating quotients (Webster, arXiv:1309.3796v3, §4.5, before Theorem 4.28). -/
def violatingWhiskerRightAppend :
    violatingWhiskerRight P (v₁ ++ v₂) (redFree_append hv₁ hv₂)
        (endWeight_append_of_eq h₁ h₂) ≅
      violatingWhiskerRight P v₁ hv₁ h₁ ⋙ violatingWhiskerRight P v₂ hv₂ h₂ :=
  CategoryTheory.Quotient.natIsoLift _
    (Functor.isoWhiskerRight (whiskerRightAppend P hv₁ hv₂ h₁ h₂) (violatingFunctor P ν₂))

end Comp

end Categorification.Stendhal.DoubleDiagram
