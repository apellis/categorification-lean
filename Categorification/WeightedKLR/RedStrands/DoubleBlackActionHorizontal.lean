/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleBlackActionComp

/-!
# Horizontal composition and the black action

Webster, arXiv:1309.3796v3, §4.5, Theorem 4.28. Reflection reverses the order of
1-morphisms: a Khovanov–Lauda diagram whiskered on the right by `c` reflects to the reflected
diagram whiskered on the left by the reflection of `c`, and conversely. This file records these
two identities for the reflection functor into a signed presentation.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory QuantumGroup QuantumGroup.UDot KL3.Diagram StringDiagrams

universe u v

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {X Y : Type v}
  [AddCommGroup X] [AddCommGroup Y] {RD : WeightDatum C X Y}
  {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}} {k : Type*} [CommRing k]
  (P : Presentation (signature RD (fun r => (Λ r).val)) k)

/-- Whiskering along an equality of the left whiskering objects. -/
theorem whisk_congr_left {S : Signature} {R : Type*} [CommRing R] (Q : Presentation S R)
    {a b u u' : Obj S} (f : Q.obj a ⟶ Q.obj b) (h : u = u') (v : List S.Colour) :
    Q.whisk f u v = eqToHom (by rw [h]) ≫ Q.whisk f u' v ≫ eqToHom (by rw [h]) := by
  subst h; simp

variable (hP : ∀ r : (pres RD k).Rel,
  P.lin (blackMirrorLinear RD (fun r => (Λ r).val) ((pres RD k).rel r)) = 0)

/-- Reflection reverses the tensor product of composable objects. -/
theorem mirror_tensor {a c : Obj (psig RD)} (h : a.endR = c.start) :
    (blackMirror RD (fun r => (Λ r).val)).obj (a.tensor c) =
      ((blackMirror RD (fun r => (Λ r).val)).obj c).tensor
        ((blackMirror RD (fun r => (Λ r).val)).obj a) := by
  apply Obj.ext
  · show (blackMirror RD (fun r => (Λ r).val)).region (Obj.endR (a.tensor c)) =
      (blackMirror RD (fun r => (Λ r).val)).region c.endR
    simp [Obj.endR, Obj.tensor, Signature.endR_append]
    rw [show (psig RD).endR a.start a.word = c.start from h]
  · simp [Obj.tensor, MirrorColourMap.word_append]

/-- Generic transport lemma for composites with `eqToHom`. -/
theorem eqToHom_sandwich_three {D : Type*} [Category D] {a a₁ a₂ b c c₁ c₂ d c' e : D}
    (g : b ⟶ c) (h₁ : a = a₁) (h₂ : a₁ = a₂) (h₃ : a₂ = b) (h₄ : c = c₁)
    (h₅ : c₁ = c₂) (h₆ : c₂ = d) (h₇ : a = e) (h₈ : e = b) (h₉ : c = c')
    (h₁₀ : c' = d) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ (eqToHom h₃ ≫ g ≫ eqToHom h₄) ≫ eqToHom h₅) ≫
        eqToHom h₆ =
      eqToHom h₇ ≫ (eqToHom h₈ ≫ g ≫ eqToHom h₉) ≫ eqToHom h₁₀ := by
  subst h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₉; simp

/-- Two composites of a morphism with transports agree. -/
theorem eqToHom_sandwich_two {D : Type*} [Category D] {a a₁ b c c₁ d a₂' c₁' : D}
    (g : b ⟶ c) (h₁ : a = a₁) (h₂ : a₁ = b) (h₃ : c = c₁) (h₄ : c₁ = d) (h₅ : a = a₂')
    (h₆ : a₂' = b) (h₇ : c = c₁') (h₈ : c₁' = d) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ g ≫ eqToHom h₃) ≫ eqToHom h₄ =
      eqToHom h₅ ≫ (eqToHom h₆ ≫ g ≫ eqToHom h₇) ≫ eqToHom h₈ := by
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

theorem linDiagram_eq_zero_of_isEmpty {S : Signature} {R : Type*} [CommRing R] {a b : Obj S}
    [IsEmpty (a ⟶ b)] (f : LinDiagram R a b) : f = 0 :=
  Subsingleton.elim (α := (a ⟶ b) →₀ R) _ _

/-- Reflection sends right whiskering of black Khovanov–Lauda diagrams to left whiskering. -/
theorem blackMirrorInto_wRAt {a b c : Obj (psig RD)} {r : X}
    (hac : a.Composable c) (hbc : b.Composable c)
    (ψ : (pres RD k).obj a ⟶ (pres RD k).obj b) (ha : a.start = r) (hb : b.start = r) :
    (blackMirrorInto RD (fun r => (Λ r).val) P hP).map ((pres RD k).wRAt r ψ c ha hb) =
      eqToHom (congrArg P.obj (mirror_tensor hac.endR_eq)) ≫
        P.wL ((blackMirror RD (fun r => (Λ r).val)).obj c)
          ((blackMirrorInto RD (fun r => (Λ r).val) P hP).map ψ) ≫
          eqToHom (congrArg P.obj (mirror_tensor hbc.endR_eq)).symm := by
  by_cases hne : Nonempty (a ⟶ b)
  · have hw : a.WhiskerOK (Obj.nil r) c.word :=
      ⟨trivial, ha.symm, hac.endR_eq ▸ hac.right_wf⟩
    have hl : (blackMirror RD (fun r => (Λ r).val)).leftObj a c.word =
        (blackMirror RD (fun r => (Λ r).val)).obj c := by
      apply Obj.ext
      · show (blackMirror RD (fun r => (Λ r).val)).region ((psig RD).endR a.endR c.word) =
          (blackMirror RD (fun r => (Λ r).val)).region c.endR
        rw [hac.endR_eq]; rfl
      · rfl
    simp only [Presentation.wRAt, Presentation.wL, Functor.map_comp, eqToHom_map]
    unfold blackMirrorInto
    erw [SigMirror.lift_whisk _ _ _ _ _ hac.left_wf hw hne, whisk_congr_left P _ hl]
    exact eqToHom_sandwich_three (D := P.Presented) _ _ _ _ _ _ _ _ _ _ _
  · obtain ⟨f, rfl⟩ := (pres RD k).lin_surjective ψ
    have : IsEmpty (a ⟶ b) := not_nonempty_iff.mp hne
    rw [linDiagram_eq_zero_of_isEmpty f]
    erw [Presentation.lin_zero, Presentation.wRAt_zero, Functor.map_zero, Functor.map_zero,
      Presentation.wL_zero]
    simp only [Limits.zero_comp, Limits.comp_zero]
    rfl

/-- Reflection sends left whiskering of black Khovanov–Lauda diagrams to right whiskering. -/
theorem blackMirrorInto_wL {a b c : Obj (psig RD)}
    (hca : c.Composable a) (hcb : c.Composable b) (hab : a.endR = b.endR)
    (ψ : (pres RD k).obj a ⟶ (pres RD k).obj b) :
    (blackMirrorInto RD (fun r => (Λ r).val) P hP).map ((pres RD k).wL c ψ) =
      eqToHom (congrArg P.obj (mirror_tensor hca.endR_eq)) ≫
        P.wRAt ((blackMirror RD (fun r => (Λ r).val)).obj a).start
          ((blackMirrorInto RD (fun r => (Λ r).val) P hP).map ψ)
          ((blackMirror RD (fun r => (Λ r).val)).obj c) rfl
          (by show (blackMirror RD (fun r => (Λ r).val)).region b.endR = _; rw [← hab]; rfl) ≫
          eqToHom (congrArg P.obj (mirror_tensor hcb.endR_eq)).symm := by
  by_cases hne : Nonempty (a ⟶ b)
  · have hw : a.WhiskerOK c [] := ⟨hca.left_wf, hca.endR_eq, trivial⟩
    simp only [Presentation.wRAt, Presentation.wL, Functor.map_comp, eqToHom_map]
    unfold blackMirrorInto
    erw [SigMirror.lift_whisk _ _ _ _ _ hca.right_wf hw hne]
    exact eqToHom_sandwich_two (D := P.Presented) _ _ _ _ _ _ _ _ _
  · obtain ⟨f, rfl⟩ := (pres RD k).lin_surjective ψ
    have : IsEmpty (a ⟶ b) := not_nonempty_iff.mp hne
    rw [linDiagram_eq_zero_of_isEmpty f]
    erw [Presentation.lin_zero, Presentation.wL_zero, Functor.map_zero, Functor.map_zero,
      Presentation.wRAt_zero]
    erw [Limits.zero_comp, Limits.comp_zero]
    rfl

end Categorification.Stendhal.DoubleDiagram
